#!/usr/bin/env python3
"""A standalone GitHub-compatible git forge in one file, standard library only.

Serves git smart HTTP (upload-pack v2 + v0, receive-pack v0), the REST v3 API,
the GraphQL v4 API and an MCP endpoint from one in-memory git object store.
Lifecycle: bind an ephemeral port, POST it to $MAKEFUN_ENV_URL/register, poll
$MAKEFUN_ENV_URL/done, exit 0 when the env says done.
"""

import base64
import difflib
import hashlib
import json
import os
import socket
import sys
import threading
import time
import urllib.request
import zlib
from datetime import datetime, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

# --------------------------------------------------------------------------
# Environment and the logical clock (deterministic: never the wall clock)

ENV_URL = os.environ.get("MAKEFUN_ENV_URL", "").rstrip("/")
TOKEN = os.environ.get("MAKEFUN_SHOP_TOKEN", "")


def _base_epoch():
    raw = os.environ.get("MAKEFUN_TRIAL_NOW", "")
    if raw:
        try:
            dt = datetime.fromisoformat(raw.replace("Z", "+00:00"))
            return int(dt.timestamp())
        except Exception:
            pass
    return 1760000000  # a fixed instant when the trial does not name one


BASE_EPOCH = _base_epoch()
_tick = [0]
_tick_lock = threading.Lock()


def tick():
    with _tick_lock:
        _tick[0] += 1
        return _tick[0]


def now_epoch():
    return BASE_EPOCH + tick()


def now_iso():
    return datetime.fromtimestamp(now_epoch(), tz=timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


# --------------------------------------------------------------------------
# The store: one git object database plus the forge's own records.

LOCK = threading.RLock()
OBJECTS = {}  # sha hex -> (type name, raw bytes)
TYPE_CODE = {"commit": 1, "tree": 2, "blob": 3, "tag": 4}
CODE_TYPE = {v: k for k, v in TYPE_CODE.items()}
ZERO = "0" * 40

_repo_seq = [0]
_issue_seq = [0]
_comment_seq = [0]


class Repo:
    def __init__(self, name, private, description):
        _repo_seq[0] += 1
        self.id = _repo_seq[0]
        self.name = name
        self.private = bool(private)
        self.description = description or ""
        self.default_branch = "main"
        self.refs = {}  # full ref name -> sha hex
        self.issues = {}  # number -> issue dict
        self.pulls = {}  # number -> pull dict
        self.labels = {}  # name -> label dict
        self.next_number = 1  # issues and pull requests share one sequence
        self.created_tick = tick()
        self.updated_tick = self.created_tick


REPOS = {}  # name -> Repo
VIEWER = {"login": None}  # learned from the first owner-addressed request


def viewer_login():
    return VIEWER["login"] or "viewer"


def learn_viewer(owner):
    if owner and VIEWER["login"] is None:
        VIEWER["login"] = owner


# --------------------------------------------------------------------------
# Git objects

def hash_object(otype, data):
    head = ("%s %d\0" % (otype, len(data))).encode()
    return hashlib.sha1(head + data).hexdigest()


def store_object(otype, data):
    sha = hash_object(otype, data)
    OBJECTS[sha] = (otype, data)
    return sha


def get_object(sha):
    return OBJECTS.get(sha)


def parse_commit(data):
    head, _, message = data.partition(b"\n\n")
    info = {"tree": None, "parents": [], "message": message.decode("utf-8", "replace")}
    for line in head.split(b"\n"):
        if line.startswith(b"tree "):
            info["tree"] = line[5:].decode()
        elif line.startswith(b"parent "):
            info["parents"].append(line[7:].decode())
    return info


def make_commit(tree_sha, parents, message):
    ts = now_epoch()
    ident = "Forge <%s@example.invalid> %d +0000" % (viewer_login(), ts)
    lines = ["tree %s" % tree_sha]
    for p in parents:
        lines.append("parent %s" % p)
    lines.append("author %s" % ident)
    lines.append("committer %s" % ident)
    data = ("\n".join(lines) + "\n\n" + (message or "")).encode()
    return store_object("commit", data)


def parse_tree(data):
    entries = []
    i = 0
    while i < len(data):
        sp = data.index(b" ", i)
        mode = data[i:sp].decode()
        nul = data.index(b"\0", sp)
        name = data[sp + 1:nul].decode("utf-8", "surrogateescape")
        sha = data[nul + 1:nul + 21].hex()
        entries.append((mode, name, sha))
        i = nul + 21
    return entries


def build_tree(entries):
    # entries: list of (mode, name, sha); git sorts trees by name, dirs as name/
    def key(e):
        mode, name, _ = e
        return name + "/" if mode == "40000" else name

    out = bytearray()
    for mode, name, sha in sorted(entries, key=key):
        out += mode.encode() + b" " + name.encode("utf-8", "surrogateescape") + b"\0" + bytes.fromhex(sha)
    return store_object("tree", bytes(out))


def tree_flat(tree_sha, prefix=""):
    """Flatten a tree into {path: (mode, sha)} for blobs, recursing into subtrees."""
    out = {}
    if not tree_sha:
        return out
    obj = get_object(tree_sha)
    if not obj or obj[0] != "tree":
        return out
    for mode, name, sha in parse_tree(obj[1]):
        path = prefix + name
        if mode == "40000":
            out.update(tree_flat(sha, path + "/"))
        else:
            out[path] = (mode, sha)
    return out


def tree_set(tree_sha, path, blob_sha):
    """Return a new tree sha with path set to blob_sha (or removed when None)."""
    parts = path.split("/")
    entries = {}
    if tree_sha:
        obj = get_object(tree_sha)
        if obj and obj[0] == "tree":
            for mode, name, sha in parse_tree(obj[1]):
                entries[name] = (mode, sha)
    head = parts[0]
    if len(parts) == 1:
        if blob_sha is None:
            entries.pop(head, None)
        else:
            entries[head] = ("100644", blob_sha)
    else:
        sub_mode, sub_sha = entries.get(head, ("40000", None))
        new_sub = tree_set(sub_sha, "/".join(parts[1:]), blob_sha)
        if new_sub is None:
            entries.pop(head, None)
        else:
            entries[head] = ("40000", new_sub)
    if not entries:
        return None
    return build_tree([(mode, name, sha) for name, (mode, sha) in entries.items()])


EMPTY_TREE = None  # computed lazily: sha of the empty tree


def empty_tree():
    global EMPTY_TREE
    if EMPTY_TREE is None:
        EMPTY_TREE = store_object("tree", b"")
    return EMPTY_TREE


def commit_tree_of(commit_sha):
    obj = get_object(commit_sha)
    if not obj or obj[0] != "commit":
        return None
    return parse_commit(obj[1])["tree"]


def ancestors(start, limit=None):
    """All commit shas reachable from start (inclusive), parents walked BFS."""
    seen = {}
    queue = [start]
    while queue:
        nxt = []
        for sha in queue:
            if sha in seen or sha not in OBJECTS:
                continue
            seen[sha] = True
            obj = get_object(sha)
            if obj and obj[0] == "commit":
                nxt.extend(parse_commit(obj[1])["parents"])
        if limit is not None and len(seen) >= limit:
            break
        queue = nxt
    return seen


def is_ancestor(old, new):
    if old == new:
        return True
    return old in ancestors(new)


def merge_base(a, b):
    anc_a = ancestors(a)
    queue = [b]
    seen = set()
    while queue:
        nxt = []
        for sha in queue:
            if sha in anc_a:
                return sha
            if sha in seen:
                continue
            seen.add(sha)
            obj = get_object(sha)
            if obj and obj[0] == "commit":
                nxt.extend(parse_commit(obj[1])["parents"])
        queue = nxt
    return None


def closure(tips, exclude_tips=(), depth=None, client_shallow=()):
    """Objects to send for the given tips.

    Returns (object shas in send order, shallow boundary commit shas,
    unshallowed commit shas). Haves exclude their whole object closure;
    client-shallow commits exclude only themselves and their trees, but
    traversal continues through them so a deepen can deliver their parents.
    depth=None means the full history; otherwise commits deeper than depth
    steps from a tip are cut and the boundary commits are reported shallow.
    """
    shallow_have = set(client_shallow)
    have_deep = set()
    for tip in exclude_tips:
        # A have the client holds only shallowly does not imply its ancestors:
        # stop the descent at shallow commits (they are covered separately).
        stack = [tip]
        seen = set()
        while stack:
            sha = stack.pop()
            if sha in seen or sha in shallow_have:
                continue
            seen.add(sha)
            have_deep.add(sha)
            obj = get_object(sha)
            if obj and obj[0] == "commit":
                stack.extend(parse_commit(obj[1])["parents"])
    excluded_objs = set()

    def exclude_tree(tree_sha):
        if not tree_sha:
            return
        excluded_objs.add(tree_sha)
        obj = get_object(tree_sha)
        if obj and obj[0] == "tree":
            for mode, name, sha in parse_tree(obj[1]):
                if mode == "40000":
                    exclude_tree(sha)
                else:
                    excluded_objs.add(sha)

    for c in have_deep | shallow_have:
        excluded_objs.add(c)
        obj = get_object(c)
        if obj and obj[0] == "commit":
            exclude_tree(parse_commit(obj[1])["tree"])

    dist = {}
    queue = []
    for tip in tips:
        if tip in OBJECTS and tip not in dist:
            dist[tip] = 1
            queue.append(tip)
    send = []
    boundary = set()
    i = 0
    while i < len(queue):
        sha = queue[i]
        i += 1
        d = dist[sha]
        if sha not in have_deep and sha not in shallow_have:
            send.append(sha)
        obj = get_object(sha)
        if not obj or obj[0] != "commit":
            continue
        parents = parse_commit(obj[1])["parents"]
        if depth is not None and d >= depth:
            if parents and sha not in have_deep:
                boundary.add(sha)
            continue
        for p in parents:
            if p in have_deep:
                continue
            if p not in dist or dist[p] > d + 1:
                dist[p] = d + 1
                queue.append(p)
    wanted = []
    seen = set()

    def add(sha):
        if sha not in seen and sha in OBJECTS and sha not in excluded_objs:
            seen.add(sha)
            wanted.append(sha)

    def add_tree(tree_sha):
        if not tree_sha:
            return
        add(tree_sha)
        obj = get_object(tree_sha)
        if obj and obj[0] == "tree":
            for mode, name, sha in parse_tree(obj[1]):
                if mode == "40000":
                    add_tree(sha)
                else:
                    add(sha)

    for sha in send:
        add(sha)
        obj = get_object(sha)
        if obj and obj[0] == "commit":
            add_tree(parse_commit(obj[1])["tree"])
    # annotated tags pointing at wanted commits ride along
    for sha, (otype, data) in list(OBJECTS.items()):
        if otype == "tag" and sha not in excluded_objs:
            target = tag_target(data)
            if target in seen:
                add(sha)
    unshallow = {s for s in shallow_have if s in dist and s not in boundary}
    return wanted, boundary, unshallow


def tag_target(data):
    for line in data.split(b"\n"):
        if line.startswith(b"object "):
            return line[7:].decode()
    return None


# --------------------------------------------------------------------------
# Packfiles

def _pack_entry_header(otype, size):
    code = TYPE_CODE[otype]
    first = (code << 4) | (size & 0x0F)
    size >>= 4
    out = bytearray()
    while size:
        out.append(first | 0x80)
        first = size & 0x7F
        size >>= 7
    out.append(first)
    return bytes(out)


_PACK_CACHE = {}


def build_pack(shas):
    key = tuple(shas)
    cached = _PACK_CACHE.get(key)
    if cached is not None:
        return cached
    out = bytearray()
    out += b"PACK" + (2).to_bytes(4, "big") + len(shas).to_bytes(4, "big")
    for sha in shas:
        otype, data = OBJECTS[sha]
        out += _pack_entry_header(otype, len(data))
        out += zlib.compress(data)
    out += hashlib.sha1(bytes(out)).digest()
    pack = bytes(out)
    if len(_PACK_CACHE) > 64:
        _PACK_CACHE.clear()
    _PACK_CACHE[key] = pack
    return pack


def _delta_varint(data, pos):
    val = 0
    shift = 0
    while True:
        b = data[pos]
        pos += 1
        val |= (b & 0x7F) << shift
        shift += 7
        if not (b & 0x80):
            return val, pos


def apply_delta(base, delta):
    src, pos = _delta_varint(delta, 0)
    if src != len(base):
        raise ValueError("delta base size mismatch")
    tgt, pos = _delta_varint(delta, pos)
    out = bytearray()
    while pos < len(delta):
        op = delta[pos]
        pos += 1
        if op & 0x80:
            cp_off = 0
            cp_size = 0
            for i in range(4):
                if op & (1 << i):
                    cp_off |= delta[pos] << (8 * i)
                    pos += 1
            for i in range(3):
                if op & (0x10 << i):
                    cp_size |= delta[pos] << (8 * i)
                    pos += 1
            if cp_size == 0:
                cp_size = 0x10000
            out += base[cp_off:cp_off + cp_size]
        elif op:
            out += delta[pos:pos + op]
            pos += op
        else:
            raise ValueError("delta opcode 0")
    if len(out) != tgt:
        raise ValueError("delta size mismatch")
    return bytes(out)


def parse_pack(data):
    """Store every object in a packfile; returns the number of objects."""
    if len(data) < 12 or data[:4] != b"PACK":
        raise ValueError("not a pack")
    count = int.from_bytes(data[8:12], "big")
    pos = 12
    pending = []  # (sha or None, type, data or delta bytes, base ref)
    by_offset = {}
    for _ in range(count):
        start = pos
        c = data[pos]
        pos += 1
        code = (c >> 4) & 7
        size = c & 0x0F
        shift = 4
        while c & 0x80:
            c = data[pos]
            pos += 1
            size |= (c & 0x7F) << shift
            shift += 7
        base = None
        if code == 6:  # ofs-delta
            c = data[pos]
            pos += 1
            ofs = c & 0x7F
            while c & 0x80:
                c = data[pos]
                pos += 1
                ofs = ((ofs + 1) << 7) | (c & 0x7F)
            base = ("ofs", start - ofs)
        elif code == 7:  # ref-delta
            base = ("ref", data[pos:pos + 20].hex())
            pos += 20
        d = zlib.decompressobj()
        raw = d.decompress(data[pos:])
        pos += len(data[pos:]) - len(d.unused_data)
        if code in (6, 7):
            pending.append((start, code, raw, base))
            by_offset[start] = None
        else:
            otype = CODE_TYPE[code]
            sha = store_object(otype, raw)
            by_offset[start] = sha
    # resolve deltas (possibly chained)
    def resolve(item):
        start, code, raw, base = item
        if by_offset.get(start):
            return by_offset[start]
        if base[0] == "ofs":
            base_item = next(p for p in pending if p[0] == base[1]) if any(p[0] == base[1] for p in pending) else None
            if base_item is not None:
                base_sha = resolve(base_item)
            else:
                base_sha = by_offset[base[1]]
        else:
            base_sha = base[1]
        bobj = get_object(base_sha)
        if bobj is None:
            raise ValueError("delta base missing")
        full = apply_delta(bobj[1], raw)
        sha = store_object(bobj[0], full)
        by_offset[start] = sha
        return sha

    for item in pending:
        resolve(item)
    return count


# --------------------------------------------------------------------------
# pkt-lines (git wire framing)

def pkt(payload):
    if isinstance(payload, str):
        payload = payload.encode()
    return ("%04x" % (len(payload) + 4)).encode() + payload


FLUSH = b"0000"
DELIM = b"0001"


def read_pkt_lines(data, pos=0):
    """Parse pkt-lines from data starting at pos.

    Returns (lines, new_pos, kind) where kind is 'flush', 'delim' or 'end'
    for the terminator that stopped the parse; plain lines are bytes without
    their trailing newline stripped of nothing (raw payloads).
    """
    lines = []
    while pos + 4 <= len(data):
        try:
            n = int(data[pos:pos + 4], 16)
        except ValueError:
            break
        if n == 0:
            return lines, pos + 4, "flush"
        if n == 1:
            return lines, pos + 4, "delim"
        if n == 2:
            return lines, pos + 4, "end"
        if n < 4 or pos + n > len(data):
            break
        lines.append(data[pos + 4:pos + n])
        pos += n
    return lines, pos, "end"


# --------------------------------------------------------------------------
# JSON views of the store

def iso_of(tick_value):
    return datetime.fromtimestamp(BASE_EPOCH + tick_value, tz=timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def user_view():
    return {"login": viewer_login(), "id": 1, "type": "User", "site_admin": False}


def repo_view(repo):
    owner = viewer_login()
    return {
        "id": repo.id,
        "node_id": gid("Repository", repo.id),
        "name": repo.name,
        "full_name": "%s/%s" % (owner, repo.name),
        "private": repo.private,
        "owner": user_view(),
        "html_url": "https://forge.invalid/%s/%s" % (owner, repo.name),
        "description": repo.description,
        "fork": False,
        "url": "/api/v3/repos/%s/%s" % (owner, repo.name),
        "created_at": iso_of(repo.created_tick),
        "updated_at": iso_of(repo.updated_tick),
        "pushed_at": iso_of(repo.updated_tick),
        "size": 0,
        "stargazers_count": 0,
        "watchers_count": 0,
        "language": None,
        "has_issues": True,
        "has_projects": True,
        "has_downloads": True,
        "has_wiki": True,
        "has_pages": False,
        "forks_count": 0,
        "open_issues_count": sum(1 for i in list(repo.issues.values()) + list(repo.pulls.values()) if i["state"] == "open"),
        "license": None,
        "topics": [],
        "visibility": "private" if repo.private else "public",
        "default_branch": repo.default_branch,
    }


def label_view(label):
    return {
        "id": label["id"],
        "node_id": gid("Label", label["id"]),
        "name": label["name"],
        "color": label.get("color", "ededed"),
        "default": False,
        "description": label.get("description"),
        "url": "",
    }


def issue_view(repo, issue):
    return {
        "id": issue["id"],
        "node_id": gid("Issue", issue["id"]),
        "url": "/api/v3/repos/%s/%s/issues/%d" % (viewer_login(), repo.name, issue["number"]),
        "repository_url": "/api/v3/repos/%s/%s" % (viewer_login(), repo.name),
        "number": issue["number"],
        "title": issue["title"],
        "body": issue["body"],
        "user": user_view(),
        "labels": [label_view(repo.labels[name]) for name in issue["labels"] if name in repo.labels],
        "state": issue["state"],
        "locked": False,
        "assignees": [],
        "comments": len(issue["comments"]),
        "created_at": iso_of(issue["created_tick"]),
        "updated_at": iso_of(issue["updated_tick"]),
        "closed_at": iso_of(issue["closed_tick"]) if issue.get("closed_tick") else None,
    }


def comment_view(repo, issue, comment):
    return {
        "id": comment["id"],
        "node_id": gid("IssueComment", comment["id"]),
        "url": "/api/v3/repos/%s/%s/issues/comments/%d" % (viewer_login(), repo.name, comment["id"]),
        "body": comment["body"],
        "user": user_view(),
        "created_at": iso_of(comment["created_tick"]),
        "updated_at": iso_of(comment["created_tick"]),
    }


def branch_tip(repo, branch):
    return repo.refs.get("refs/heads/" + branch)


def pull_view(repo, pull):
    owner = viewer_login()
    head_sha = branch_tip(repo, pull["head"]) or ZERO
    base_sha = branch_tip(repo, pull["base"]) or ZERO
    base_ref = {
        "label": "%s:%s" % (owner, pull["base"]),
        "ref": pull["base"],
        "sha": base_sha,
        "user": user_view(),
        "repo": repo_view(repo),
    }
    head_ref = {
        "label": "%s:%s" % (owner, pull["head"]),
        "ref": pull["head"],
        "sha": head_sha,
        "user": user_view(),
        "repo": repo_view(repo),
    }
    files = pull_files(repo, pull)
    return {
        "id": pull["id"],
        "node_id": gid("PullRequest", pull["id"]),
        "url": "/api/v3/repos/%s/%s/pulls/%d" % (owner, repo.name, pull["number"]),
        "html_url": "https://forge.invalid/%s/%s/pull/%d" % (owner, repo.name, pull["number"]),
        "diff_url": "https://forge.invalid/%s/%s/pull/%d.diff" % (owner, repo.name, pull["number"]),
        "patch_url": "https://forge.invalid/%s/%s/pull/%d.patch" % (owner, repo.name, pull["number"]),
        "number": pull["number"],
        "state": pull["state"],
        "title": pull["title"],
        "body": pull["body"],
        "user": user_view(),
        "labels": [],
        "locked": False,
        "head": head_ref,
        "base": base_ref,
        "created_at": iso_of(pull["created_tick"]),
        "updated_at": iso_of(pull["updated_tick"]),
        "closed_at": iso_of(pull["closed_tick"]) if pull.get("closed_tick") else None,
        "merged_at": iso_of(pull["merged_tick"]) if pull.get("merged_tick") else None,
        "merged": bool(pull.get("merged")),
        "mergeable": pull_mergeable(repo, pull),
        "mergeable_state": "clean" if pull_mergeable(repo, pull) else "dirty",
        "merge_commit_sha": pull.get("merge_commit_sha"),
        "comments": 0,
        "review_comments": 0,
        "commits": len(pull_commits(repo, pull)),
        "additions": sum(f["additions"] for f in files),
        "deletions": sum(f["deletions"] for f in files),
        "changed_files": len(files),
    }


def pull_commits(repo, pull):
    head = branch_tip(repo, pull["head"])
    base = branch_tip(repo, pull["base"])
    if not head:
        return []
    base_anc = ancestors(base) if base else set()
    out = []
    for sha in ancestors(head):
        if sha not in base_anc:
            out.append(sha)
    return out


def tree_map_at(repo, refname):
    sha = repo.refs.get(refname)
    if not sha:
        return {}
    tree = commit_tree_of(sha)
    return tree_flat(tree) if tree else {}


def pull_files(repo, pull):
    base_map = tree_map_at(repo, "refs/heads/" + pull["base"])
    head_map = tree_map_at(repo, "refs/heads/" + pull["head"])
    # changes are measured from the merge base, not the (possibly moved) base tip
    mb = merge_base(branch_tip(repo, pull["base"]) or "", branch_tip(repo, pull["head"]) or "")
    if mb:
        base_map = tree_flat(commit_tree_of(mb)) if commit_tree_of(mb) else {}
    out = []
    for path in sorted(set(base_map) | set(head_map)):
        b = base_map.get(path)
        h = head_map.get(path)
        if b == h:
            continue
        if b is None:
            status = "added"
        elif h is None:
            status = "removed"
        else:
            status = "modified"
        old_text = ""
        new_text = ""
        if b:
            obj = get_object(b[1])
            if obj:
                old_text = obj[1].decode("utf-8", "replace")
        if h:
            obj = get_object(h[1])
            if obj:
                new_text = obj[1].decode("utf-8", "replace")
        adds = dels = 0
        for line in difflib.unified_diff(old_text.splitlines(), new_text.splitlines(), lineterm=""):
            if line.startswith("+") and not line.startswith("+++"):
                adds += 1
            elif line.startswith("-") and not line.startswith("---"):
                dels += 1
        out.append({
            "sha": h[1] if h else ZERO,
            "filename": path,
            "status": status,
            "additions": adds,
            "deletions": dels,
            "changes": adds + dels,
            "patch": "",
        })
    return out


def pull_mergeable(repo, pull):
    if pull["state"] != "open":
        return None
    head = branch_tip(repo, pull["head"])
    base = branch_tip(repo, pull["base"])
    if not head or not base:
        return None
    if is_ancestor(head, base):
        return True
    mb = merge_base(base, head)
    if not mb:
        return False
    base_map = tree_flat(commit_tree_of(mb)) if commit_tree_of(mb) else {}
    base_now = tree_flat(commit_tree_of(base)) if commit_tree_of(base) else {}
    head_map = tree_flat(commit_tree_of(head)) if commit_tree_of(head) else {}
    for path in set(base_map) | set(base_now) | set(head_map):
        base_changed = base_map.get(path) != base_now.get(path)
        head_changed = base_map.get(path) != head_map.get(path)
        if base_changed and head_changed and base_now.get(path) != head_map.get(path):
            return False
    return True


def gid(kind, ident):
    return base64.b64encode(("%s:%s" % (kind, ident)).encode()).decode()


# --------------------------------------------------------------------------
# Small helpers shared by the HTTP surfaces

class ApiError(Exception):
    def __init__(self, status, message):
        super().__init__(message)
        self.status = status
        self.message = message


def get_repo(owner, name):
    learn_viewer(owner)
    repo = REPOS.get(name)
    if repo is None or (VIEWER["login"] is not None and owner != VIEWER["login"]):
        raise ApiError(404, "Not Found")
    return repo


def new_issue(repo, title, body, labels=()):
    _issue_seq[0] += 1
    number = repo.next_number
    repo.next_number += 1
    t = tick()
    issue = {
        "id": _issue_seq[0],
        "number": number,
        "title": title or "",
        "body": body or "",
        "state": "open",
        "labels": list(labels),
        "comments": [],
        "created_tick": t,
        "updated_tick": t,
        "closed_tick": None,
    }
    repo.issues[number] = issue
    return issue


def new_pull(repo, title, body, head, base):
    _issue_seq[0] += 1
    number = repo.next_number
    repo.next_number += 1
    t = tick()
    pull = {
        "id": _issue_seq[0],
        "number": number,
        "title": title or "",
        "body": body or "",
        "state": "open",
        "head": head,
        "base": base,
        "merged": False,
        "merged_tick": None,
        "closed_tick": None,
        "merge_commit_sha": None,
        "created_tick": t,
        "updated_tick": t,
    }
    repo.pulls[number] = pull
    return pull


def merge_pull(repo, pull, method="squash"):
    """Merge pull into its base branch; returns the merge commit sha."""
    head = branch_tip(repo, pull["head"])
    base = branch_tip(repo, pull["base"])
    mb = merge_base(base, head) if (base and head) else None
    base_tree_map = tree_flat(commit_tree_of(base)) if base and commit_tree_of(base) else {}
    mb_map = tree_flat(commit_tree_of(mb)) if mb and commit_tree_of(mb) else {}
    head_map = tree_flat(commit_tree_of(head)) if head and commit_tree_of(head) else {}
    merged_map = dict(base_tree_map)
    for path, val in head_map.items():
        if mb_map.get(path) != val:
            merged_map[path] = val
    for path in mb_map:
        if path not in head_map and path in merged_map and merged_map[path] == mb_map[path]:
            del merged_map[path]
    tree_sha = build_tree_from_map(merged_map)
    if method == "merge":
        parents = [p for p in (base, head) if p]
        message = "Merge pull request #%d" % pull["number"]
    else:
        parents = [base] if base else []
        message = "%s (#%d)" % (pull["title"], pull["number"])
    sha = make_commit(tree_sha, parents, message)
    repo.refs["refs/heads/" + pull["base"]] = sha
    pull["state"] = "closed"
    pull["merged"] = True
    pull["merged_tick"] = tick()
    pull["closed_tick"] = pull["merged_tick"]
    pull["merge_commit_sha"] = sha
    pull["updated_tick"] = pull["merged_tick"]
    repo.updated_tick = pull["merged_tick"]
    return sha


def build_tree_from_map(flat):
    """Build nested trees from a flat {path: (mode, sha)} map; returns tree sha."""
    root = {}
    for path, (mode, sha) in flat.items():
        parts = path.split("/")
        node = root
        for part in parts[:-1]:
            node = node.setdefault(part, {})
        node[parts[-1]] = (mode, sha)

    def emit(node):
        entries = []
        for name, val in node.items():
            if isinstance(val, dict):
                entries.append(("40000", name, emit(val)))
            else:
                entries.append((val[0], name, val[1]))
        return build_tree(entries)

    if not root:
        return empty_tree()
    return emit(root)


# --------------------------------------------------------------------------
# HTTP plumbing

_req_seq = [0]


def request_id():
    _req_seq[0] += 1
    return "FORGE-%06d" % _req_seq[0]


class Handler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    server_version = "Forge/1.0"

    def log_message(self, fmt, *args):
        pass

    def setup(self):
        super().setup()
        try:
            # Responses go out as a header block plus a body write; without
            # NODELAY the body can sit in Nagle's algorithm waiting for an
            # ACK the client is delaying, adding ~20-40 ms per request.
            self.connection.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        except Exception:
            pass

    def do_GET(self):
        self.handle_all()

    def do_POST(self):
        self.handle_all()

    def do_PUT(self):
        self.handle_all()

    def do_PATCH(self):
        self.handle_all()

    def do_DELETE(self):
        self.handle_all()

    def do_HEAD(self):
        self.handle_all()

    # -- plumbing ------------------------------------------------------
    def read_body(self):
        length = self.headers.get("Content-Length")
        if length is not None:
            n = int(length)
            return self.rfile.read(n) if n > 0 else b""
        if (self.headers.get("Transfer-Encoding") or "").lower() == "chunked":
            out = bytearray()
            while True:
                line = self.rfile.readline(65536).strip()
                try:
                    n = int(line.split(b";")[0], 16)
                except ValueError:
                    break
                if n == 0:
                    while True:
                        trailer = self.rfile.readline(65536)
                        if trailer in (b"\r\n", b"\n", b""):
                            break
                    break
                out += self.rfile.read(n)
                self.rfile.readline(65536)
            return bytes(out)
        return b""

    def send_bytes(self, status, data, content_type, extra=None):
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(data)))
        self.send_header("X-GitHub-Request-Id", request_id())
        if extra:
            for k, v in extra.items():
                self.send_header(k, v)
        self.end_headers()
        if self.command != "HEAD":
            self.wfile.write(data)

    def send_json(self, status, obj, extra=None):
        data = (json.dumps(obj) + "\n").encode()
        self.send_bytes(status, data, "application/json; charset=utf-8", extra)

    def authed(self):
        if not TOKEN:
            return True
        return self.headers.get("Authorization") == "Bearer " + TOKEN

    def handle_all(self):
        try:
            self._dispatch()
        except ApiError as e:
            self.send_json(e.status, {"message": e.message})
        except BrokenPipeError:
            pass
        except Exception as e:  # never hang a check on an internal error
            try:
                self.send_json(500, {"message": "Internal error: %s" % e})
            except Exception:
                pass

    def _dispatch(self):
        from urllib.parse import urlparse, parse_qs, unquote

        parsed = urlparse(self.path)
        path = unquote(parsed.path)
        query = {k: v[0] for k, v in parse_qs(parsed.query).items()}
        body = self.read_body() if self.command in ("POST", "PUT", "PATCH", "DELETE") else b""

        if path == "/healthz" and self.command == "GET":
            self.send_json(200, {"ok": True})
            return
        if not self.authed():
            self.send_json(401, {"message": "Bad credentials"})
            return
        if path == "/api/graphql" and self.command == "POST":
            self.handle_graphql(body)
            return
        if path == "/mcp" and self.command == "POST":
            self.handle_mcp(body)
            return
        if path == "/api/v3" or path.startswith("/api/v3/"):
            with LOCK:
                self.handle_rest(path, query, body)
            return
        git_seg = _segments(path)
        if len(git_seg) >= 3 and git_seg[1].endswith(".git"):
            with LOCK:
                self.handle_git(path, query, body)
            return
        self.send_json(404, {"message": "Not Found"})

    # -- REST helpers ---------------------------------------------------
    def json_body(self, body):
        if not body:
            return {}
        try:
            data = json.loads(body.decode("utf-8"))
        except Exception:
            raise ApiError(400, "Problems parsing JSON")
        if not isinstance(data, dict):
            raise ApiError(400, "Problems parsing JSON")
        return data

    def paginate(self, items, query, path):
        try:
            per_page = min(100, max(1, int(query.get("per_page", 30))))
        except ValueError:
            per_page = 30
        try:
            page = max(1, int(query.get("page", 1)))
        except ValueError:
            page = 1
        total = len(items)
        start = (page - 1) * per_page
        chunk = items[start:start + per_page]
        headers = {}
        if start + per_page < total:
            host = self.headers.get("Host", "127.0.0.1")
            params = dict(query)
            params["page"] = str(page + 1)
            params["per_page"] = str(per_page)
            qs = "&".join("%s=%s" % (k, v) for k, v in sorted(params.items()))
            last_page = (total + per_page - 1) // per_page
            params["page"] = str(last_page)
            qs_last = "&".join("%s=%s" % (k, v) for k, v in sorted(params.items()))
            headers["Link"] = '<http://%s%s?%s>; rel="next", <http://%s%s?%s>; rel="last"' % (
                host, path, qs, host, path, qs_last)
        return chunk, headers


# --------------------------------------------------------------------------
# REST v3

def _segments(path):
    return [s for s in path.split("/") if s != ""]


def commit_view(sha):
    obj = get_object(sha)
    data = obj[1] if obj else b""
    info = parse_commit(data) if obj else {"tree": None, "parents": [], "message": ""}
    author = {"name": viewer_login(), "email": "%s@example.invalid" % viewer_login(), "date": now_iso()}
    committer = dict(author)
    for line in (obj[1].split(b"\n\n")[0].decode("utf-8", "replace") if obj else "").split("\n"):
        for role in ("author", "committer"):
            if line.startswith(role + " "):
                rest = line[len(role) + 1:]
                try:
                    ident, ts, _tz = rest.rsplit(" ", 2)
                    name, email = ident.rsplit(" <", 1)
                    view = {"name": name, "email": email.rstrip(">"),
                            "date": datetime.fromtimestamp(int(ts), tz=timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")}
                    if role == "author":
                        author = view
                    else:
                        committer = view
                except Exception:
                    pass
    return {
        "sha": sha,
        "node_id": gid("Commit", sha),
        "commit": {
            "author": author,
            "committer": committer,
            "message": info["message"],
            "tree": {"sha": info["tree"], "url": ""},
            "comment_count": 0,
        },
        "url": "",
        "html_url": "",
        "parents": [{"sha": p, "url": ""} for p in info["parents"]],
    }


def handle_rest(self, path, query, body):
    seg = _segments(path)  # ['api', 'v3', ...]
    rest = seg[2:]
    method = self.command

    if not rest:
        if method == "GET":
            self.send_json(200, {
                "current_user_url": "/api/v3/user",
                "current_user_repositories_url": "/api/v3/user/repos",
                "repository_url": "/api/v3/repos/{owner}/{repo}",
                "rate_limit_url": "/api/v3/rate_limit",
                "emojis_url": "/api/v3/emojis",
                "issue_search_url": "/api/v3/search/issues",
            }, {"X-OAuth-Scopes": "repo, read:org"})
            return
        raise ApiError(404, "Not Found")

    if rest == ["meta"] and method == "GET":
        self.send_json(200, {
            "verifiable_password_authentication": False,
            "installed_version": "1.0.0-forge",
            "github_services_sha": "forge",
            "api": ["v3"],
        })
        return

    if rest == ["user"] and method == "GET":
        self.send_json(200, user_view())
        return

    if rest == ["user", "repos"]:
        if method == "GET":
            items = [repo_view(r) for r in REPOS.values()]
            chunk, headers = self.paginate(items, query, "/api/v3/user/repos")
            self.send_json(200, chunk, headers)
            return
        if method == "POST":
            data = self.json_body(body)
            name = data.get("name")
            if not name or not isinstance(name, str):
                raise ApiError(422, "Repository creation failed.")
            if name in REPOS:
                raise ApiError(422, "Repository creation failed: name already exists on this account")
            repo = Repo(name, data.get("private", False), data.get("description", ""))
            REPOS[name] = repo
            if data.get("auto_init"):
                blob = store_object("blob", ("# %s\n" % name).encode())
                tree = build_tree([("100644", "README.md", blob)])
                sha = make_commit(tree, [], "Initial commit")
                repo.refs["refs/heads/" + repo.default_branch] = sha
            self.send_json(201, repo_view(repo))
            return

    if len(rest) >= 3 and rest[0] == "repos":
        owner, name = rest[1], rest[2]
        repo = get_repo(owner, name)
        tail = rest[3:]
        base = "/api/v3/repos/%s/%s" % (owner, name)

        if not tail:
            if method == "GET":
                self.send_json(200, repo_view(repo))
                return
            if method == "PATCH":
                data = self.json_body(body)
                if "description" in data:
                    repo.description = data["description"] or ""
                if "private" in data:
                    repo.private = bool(data["private"])
                if "default_branch" in data and data["default_branch"]:
                    repo.default_branch = data["default_branch"]
                if "name" in data and data["name"] and data["name"] != repo.name:
                    REPOS[data["name"]] = repo
                    del REPOS[repo.name]
                    repo.name = data["name"]
                repo.updated_tick = tick()
                self.send_json(200, repo_view(repo))
                return
            if method == "DELETE":
                del REPOS[repo.name]
                self.send_bytes(204, b"", "application/json; charset=utf-8")
                return
            raise ApiError(404, "Not Found")

        if tail == ["branches"] and method == "GET":
            out = []
            for ref in sorted(repo.refs):
                if ref.startswith("refs/heads/"):
                    out.append({"name": ref[len("refs/heads/"):],
                                "commit": {"sha": repo.refs[ref], "url": ""},
                                "protected": False})
            self.send_json(200, out)
            return

        if len(tail) == 2 and tail[0] == "branches" and method == "GET":
            ref = "refs/heads/" + tail[1]
            if ref not in repo.refs:
                raise ApiError(404, "Not Found")
            self.send_json(200, {"name": tail[1], "commit": {"sha": repo.refs[ref], "url": ""}, "protected": False})
            return

        if tail == ["commits"] and method == "GET":
            ref = query.get("sha") or repo.default_branch
            tip = repo.refs.get("refs/heads/" + ref) or repo.refs.get(ref) or (ref if ref in OBJECTS else None)
            if tip is None:
                self.send_json(200, [])
                return
            order = []
            seen = set()
            queue = [tip]
            while queue:
                nxt = []
                for sha in queue:
                    if sha in seen:
                        continue
                    seen.add(sha)
                    order.append(sha)
                    obj = get_object(sha)
                    if obj and obj[0] == "commit":
                        nxt.extend(parse_commit(obj[1])["parents"])
                queue = nxt
            items = [commit_view(s) for s in order]
            chunk, headers = self.paginate(items, query, base + "/commits")
            self.send_json(200, chunk, headers)
            return

        if tail == ["git", "refs"] and method == "POST":
            data = self.json_body(body)
            ref = data.get("ref", "")
            sha = data.get("sha", "")
            obj = get_object(sha)
            if not ref.startswith("refs/") or obj is None or obj[0] != "commit":
                raise ApiError(422, "Object is not a commit or ref is invalid")
            repo.refs[ref] = sha
            repo.updated_tick = tick()
            self.send_json(201, {"ref": ref, "node_id": gid("Ref", ref), "url": "",
                                 "object": {"type": "commit", "sha": sha, "url": ""}})
            return

        if tail[:2] == ["git", "ref"] and method == "GET":
            ref = "refs/" + "/".join(tail[2:])
            if ref not in repo.refs:
                raise ApiError(404, "Not Found")
            self.send_json(200, {"ref": ref, "node_id": gid("Ref", ref), "url": "",
                                 "object": {"type": "commit", "sha": repo.refs[ref], "url": ""}})
            return

        if tail and tail[0] == "contents":
            sub = "/".join(tail[1:])
            rest_contents(self, repo, sub, query, body)
            return

        if tail == ["labels"]:
            if method == "GET":
                self.send_json(200, [label_view(l) for l in repo.labels.values()])
                return
            if method == "POST":
                data = self.json_body(body)
                lname = data.get("name")
                if not lname:
                    raise ApiError(422, "Validation Failed")
                if lname in repo.labels:
                    raise ApiError(422, "Validation Failed")
                _issue_seq[0] += 1
                label = {"id": _issue_seq[0], "name": lname,
                         "color": data.get("color", "ededed"), "description": data.get("description")}
                repo.labels[lname] = label
                self.send_json(201, label_view(label))
                return

        if len(tail) == 2 and tail[0] == "labels" and method == "GET":
            label = repo.labels.get(tail[1])
            if label is None:
                raise ApiError(404, "Not Found")
            self.send_json(200, label_view(label))
            return

        if tail == ["issues"]:
            if method == "GET":
                state = query.get("state", "open")
                items = [i for i in repo.issues.values() if state == "all" or i["state"] == state]
                direction = query.get("direction", "desc")
                items.sort(key=lambda i: i["created_tick"], reverse=(direction != "asc"))
                views = [issue_view(repo, i) for i in items]
                chunk, headers = self.paginate(views, query, base + "/issues")
                self.send_json(200, chunk, headers)
                return
            if method == "POST":
                data = self.json_body(body)
                labels = data.get("labels") or []
                names = []
                for lab in labels:
                    lname = lab["name"] if isinstance(lab, dict) else lab
                    if lname not in repo.labels:
                        raise ApiError(422, "Validation Failed")
                    names.append(lname)
                issue = new_issue(repo, data.get("title"), data.get("body"), names)
                self.send_json(201, issue_view(repo, issue))
                return

        if len(tail) >= 2 and tail[0] == "issues":
            try:
                number = int(tail[1])
            except ValueError:
                raise ApiError(404, "Not Found")
            issue = repo.issues.get(number)
            if issue is None:
                raise ApiError(404, "Not Found")
            if len(tail) == 2:
                if method == "GET":
                    self.send_json(200, issue_view(repo, issue))
                    return
                if method == "PATCH":
                    data = self.json_body(body)
                    if "title" in data:
                        issue["title"] = data["title"] or ""
                    if "body" in data:
                        issue["body"] = data["body"] or ""
                    if "state" in data:
                        issue["state"] = data["state"]
                        if data["state"] == "closed":
                            issue["closed_tick"] = tick()
                    if "labels" in data:
                        names = []
                        for lab in data["labels"] or []:
                            lname = lab["name"] if isinstance(lab, dict) else lab
                            if lname not in repo.labels:
                                raise ApiError(422, "Validation Failed")
                            names.append(lname)
                        issue["labels"] = names
                    issue["updated_tick"] = tick()
                    self.send_json(200, issue_view(repo, issue))
                    return
            if len(tail) == 3 and tail[2] == "comments":
                if method == "GET":
                    views = [comment_view(repo, issue, c) for c in issue["comments"]]
                    chunk, headers = self.paginate(views, query, base + "/issues/%d/comments" % number)
                    self.send_json(200, chunk, headers)
                    return
                if method == "POST":
                    data = self.json_body(body)
                    _comment_seq[0] += 1
                    comment = {"id": _comment_seq[0], "body": data.get("body") or "", "created_tick": tick()}
                    issue["comments"].append(comment)
                    issue["updated_tick"] = tick()
                    self.send_json(201, comment_view(repo, issue, comment))
                    return
            raise ApiError(404, "Not Found")

        if tail == ["pulls"]:
            if method == "GET":
                state = query.get("state", "open")
                items = [p for p in repo.pulls.values() if state == "all" or p["state"] == state]
                items.sort(key=lambda p: p["created_tick"], reverse=True)
                views = [pull_view(repo, p) for p in items]
                chunk, headers = self.paginate(views, query, base + "/pulls")
                self.send_json(200, chunk, headers)
                return
            if method == "POST":
                data = self.json_body(body)
                head = (data.get("head") or "").split(":")[-1]
                base_name = (data.get("base") or repo.default_branch).split(":")[-1]
                if "refs/heads/" + head not in repo.refs:
                    raise ApiError(422, "Validation Failed")
                if "refs/heads/" + base_name not in repo.refs:
                    raise ApiError(422, "Validation Failed")
                for p in repo.pulls.values():
                    if p["head"] == head and p["base"] == base_name and p["state"] == "open":
                        raise ApiError(422, "A pull request already exists for this branch.")
                pull = new_pull(repo, data.get("title"), data.get("body"), head, base_name)
                self.send_json(201, pull_view(repo, pull))
                return

        if len(tail) >= 2 and tail[0] == "pulls":
            try:
                number = int(tail[1])
            except ValueError:
                raise ApiError(404, "Not Found")
            pull = repo.pulls.get(number)
            if len(tail) == 2:
                if pull is None:
                    raise ApiError(404, "Not Found")
                if method == "GET":
                    self.send_json(200, pull_view(repo, pull))
                    return
                if method == "PATCH":
                    data = self.json_body(body)
                    if "title" in data:
                        pull["title"] = data["title"] or ""
                    if "body" in data:
                        pull["body"] = data["body"] or ""
                    if "state" in data:
                        pull["state"] = data["state"]
                        if data["state"] == "closed":
                            pull["closed_tick"] = tick()
                    pull["updated_tick"] = tick()
                    self.send_json(200, pull_view(repo, pull))
                    return
            if pull is None:
                raise ApiError(404, "Not Found")
            if len(tail) == 3 and tail[2] == "files" and method == "GET":
                files = pull_files(repo, pull)
                chunk, headers = self.paginate(files, query, base + "/pulls/%d/files" % number)
                self.send_json(200, chunk, headers)
                return
            if len(tail) == 3 and tail[2] == "commits" and method == "GET":
                views = [commit_view(s) for s in pull_commits(repo, pull)]
                chunk, headers = self.paginate(views, query, base + "/pulls/%d/commits" % number)
                self.send_json(200, chunk, headers)
                return
            if len(tail) == 3 and tail[2] == "merge" and method == "PUT":
                data = self.json_body(body) if body else {}
                if pull["state"] != "open":
                    raise ApiError(405, "Pull Request is not mergeable")
                if not pull_mergeable(repo, pull):
                    raise ApiError(405, "Pull Request is not mergeable")
                sha = merge_pull(repo, pull, (data.get("merge_method") or "squash"))
                self.send_json(200, {"sha": sha, "merged": True,
                                     "message": "Pull Request successfully merged"})
                return
            raise ApiError(404, "Not Found")

    raise ApiError(404, "Not Found")


def _subtree_sha(tree_sha, path):
    cur = tree_sha
    for part in path.split("/"):
        if not part:
            continue
        obj = get_object(cur) if cur else None
        nxt = None
        if obj and obj[0] == "tree":
            for mode, name, sha in parse_tree(obj[1]):
                if name == part and mode == "40000":
                    nxt = sha
                    break
        if nxt is None:
            return None
        cur = nxt
    return cur


def rest_contents(self, repo, sub, query, body):
    method = self.command
    ref = query.get("ref") or repo.default_branch
    branch = (self.json_body(body).get("branch") if method in ("PUT", "DELETE") and body else None) or ref

    def tip_for(branch_name):
        return repo.refs.get("refs/heads/" + branch_name)

    if method == "GET":
        tip = tip_for(ref) or (ref if ref in OBJECTS else None)
        if tip is None:
            raise ApiError(404, "Not Found")
        tree_sha = commit_tree_of(tip)
        flat = tree_flat(tree_sha) if tree_sha else {}
        if sub == "":
            entries = {}
            for p, (mode, sha) in flat.items():
                head = p.split("/")[0]
                if "/" in p:
                    entries[head] = ("dir", head, None)
                else:
                    entries[head] = ("file", p, (mode, sha))
            out = []
            for name in sorted(entries):
                kind, p, ms = entries[name]
                if kind == "dir":
                    out.append({"name": name, "path": name, "sha": _subtree_sha(tree_sha, name) or ZERO, "size": 0,
                                "url": "", "html_url": "", "git_url": "", "download_url": None, "type": "dir"})
                else:
                    mode, sha = ms
                    obj = get_object(sha)
                    out.append({"name": name, "path": p, "sha": sha, "size": len(obj[1]) if obj else 0,
                                "url": "", "html_url": "", "git_url": "", "download_url": "", "type": "file"})
            self.send_json(200, out)
            return
        if sub in flat:
            mode, sha = flat[sub]
            obj = get_object(sha)
            content = obj[1] if obj else b""
            name = sub.split("/")[-1]
            self.send_json(200, {
                "name": name, "path": sub, "sha": sha, "size": len(content),
                "url": "", "html_url": "", "git_url": "", "download_url": "",
                "type": "file", "encoding": "base64",
                "content": base64.b64encode(content).decode(),
            })
            return
        prefix = sub.rstrip("/") + "/"
        children = {}
        for p, (mode, sha) in flat.items():
            if p.startswith(prefix):
                rest = p[len(prefix):]
                head = rest.split("/")[0]
                if "/" in rest:
                    children[head] = ("dir", prefix + head, None)
                else:
                    children[head] = ("file", p, (mode, sha))
        if children:
            out = []
            for name in sorted(children):
                kind, p, ms = children[name]
                if kind == "dir":
                    out.append({"name": name, "path": p, "sha": _subtree_sha(tree_sha, p) or ZERO, "size": 0,
                                "url": "", "html_url": "", "git_url": "", "download_url": None, "type": "dir"})
                else:
                    mode, sha = ms
                    obj = get_object(sha)
                    out.append({"name": name, "path": p, "sha": sha, "size": len(obj[1]) if obj else 0,
                                "url": "", "html_url": "", "git_url": "", "download_url": "", "type": "file"})
            self.send_json(200, out)
            return
        raise ApiError(404, "Not Found")

    if method == "PUT":
        data = self.json_body(body)
        content_b64 = data.get("content")
        if content_b64 is None or "message" not in data:
            raise ApiError(422, "Validation Failed")
        try:
            raw = base64.b64decode(content_b64)
        except Exception:
            raise ApiError(422, "Validation Failed")
        branch_name = data.get("branch") or repo.default_branch
        tip = tip_for(branch_name)
        tree_sha = commit_tree_of(tip) if tip else None
        flat = tree_flat(tree_sha) if tree_sha else {}
        exists = sub in flat
        if exists:
            cur_sha = flat[sub][1]
            given = data.get("sha")
            if given is not None and given != cur_sha:
                raise ApiError(409, "Conflict: sha does not match")
            status = 200
        else:
            status = 201
        blob_sha = store_object("blob", raw)
        new_tree = tree_set(tree_sha, sub, blob_sha)
        commit_sha = make_commit(new_tree, [tip] if tip else [], data.get("message") or "")
        repo.refs["refs/heads/" + branch_name] = commit_sha
        repo.updated_tick = tick()
        name = sub.split("/")[-1]
        self.send_json(status, {
            "content": {"name": name, "path": sub, "sha": blob_sha, "size": len(raw),
                        "url": "", "html_url": "", "git_url": "", "download_url": "",
                        "type": "file", "encoding": "base64"},
            "commit": commit_view(commit_sha)["commit"] | {"sha": commit_sha},
        })
        return

    if method == "DELETE":
        data = self.json_body(body)
        branch_name = data.get("branch") or repo.default_branch
        tip = tip_for(branch_name)
        if tip is None:
            raise ApiError(404, "Not Found")
        tree_sha = commit_tree_of(tip)
        flat = tree_flat(tree_sha) if tree_sha else {}
        if sub not in flat:
            raise ApiError(404, "Not Found")
        given = data.get("sha")
        if given is not None and given != flat[sub][1]:
            raise ApiError(409, "Conflict: sha does not match")
        new_tree = tree_set(tree_sha, sub, None)
        commit_sha = make_commit(new_tree or empty_tree(), [tip], data.get("message") or "")
        repo.refs["refs/heads/" + branch_name] = commit_sha
        repo.updated_tick = tick()
        self.send_json(200, {"content": None, "commit": {"sha": commit_sha}})
        return

    raise ApiError(404, "Not Found")


Handler.handle_rest = handle_rest
Handler.rest_contents = rest_contents


# --------------------------------------------------------------------------
# Git smart HTTP

UPLOAD_CAPS_V0 = "side-band-64k ofs-delta agent=forge/1.0"
RECEIVE_CAPS_V0 = "report-status side-band-64k delete-refs ofs-delta agent=forge/1.0"


def _sideband_pack(pack_bytes):
    out = bytearray()
    chunk = 65500
    for i in range(0, len(pack_bytes), chunk):
        out += pkt(b"\x01" + pack_bytes[i:i + chunk])
    out += FLUSH
    return bytes(out)


def _refs_advertisement(repo, caps):
    lines = []
    if not repo.refs:
        lines.append(pkt("%s capabilities^{}\0%s\n" % (ZERO, caps)))
        return b"".join(lines)
    head_ref = "refs/heads/" + repo.default_branch
    head_sha = repo.refs.get(head_ref)
    first = True
    if head_sha:
        lines.append(pkt("%s HEAD\0%s\n" % (head_sha, caps)))
        first = False
    for ref in sorted(repo.refs):
        sha = repo.refs[ref]
        if first:
            lines.append(pkt("%s %s\0%s\n" % (sha, ref, caps)))
            first = False
        else:
            lines.append(pkt("%s %s\n" % (sha, ref)))
        obj = get_object(sha)
        if obj and obj[0] == "tag":
            target = tag_target(obj[1])
            if target:
                lines.append(pkt("%s %s^{}\n" % (target, ref)))
    if first:
        lines.append(pkt("%s capabilities^{}\0%s\n" % (ZERO, caps)))
    return b"".join(lines)


def handle_git(self, path, query, body):
    seg = _segments(path)
    if len(seg) < 3 or not seg[1].endswith(".git"):
        raise ApiError(404, "Not Found")
    owner = seg[0]
    name = seg[1][:-4]
    learn_viewer(owner)
    repo = REPOS.get(name)
    rest = seg[2:]
    method = self.command
    version2 = "version=2" in (self.headers.get("Git-Protocol") or "")

    if rest == ["info", "refs"] and method == "GET":
        service = query.get("service", "")
        if service not in ("git-upload-pack", "git-receive-pack"):
            raise ApiError(400, "Service not found")
        if repo is None:
            raise ApiError(404, "Not Found")
        if service == "git-upload-pack" and version2:
            out = b"".join([
                pkt("version 2\n"),
                pkt("agent=forge/1.0\n"),
                pkt("ls-refs=unborn\n"),
                pkt("fetch=shallow wait-for-done\n"),
                pkt("object-format=sha1\n"),
                FLUSH,
            ])
            self.send_bytes(200, out, "application/x-git-upload-pack-advertisement")
            return
        caps = UPLOAD_CAPS_V0 if service == "git-upload-pack" else RECEIVE_CAPS_V0
        preamble = "# service=%s\n" % service
        out = pkt(preamble) + FLUSH + _refs_advertisement(repo, caps) + FLUSH
        ctype = "application/x-%s-advertisement" % service
        self.send_bytes(200, out, ctype)
        return

    if repo is None:
        raise ApiError(404, "Not Found")

    if rest == ["git-upload-pack"] and method == "POST":
        if version2:
            out = _upload_pack_v2(repo, body)
        else:
            out = _upload_pack_v0(repo, body)
        self.send_bytes(200, out, "application/x-git-upload-pack-result")
        return

    if rest == ["git-receive-pack"] and method == "POST":
        out = _receive_pack(repo, body)
        self.send_bytes(200, out, "application/x-git-receive-pack-result")
        return

    raise ApiError(404, "Not Found")


def _upload_pack_v0(repo, body):
    wants = []
    haves = []
    done = False
    pos = 0
    while pos < len(body):
        lines, pos, kind = read_pkt_lines(body, pos)
        for raw in lines:
            line = raw.decode("utf-8", "replace").rstrip("\n")
            parts = line.split(" ")
            if parts[0] == "want" and len(parts) >= 2:
                wants.append(parts[1])
            elif parts[0] == "have" and len(parts) >= 2:
                haves.append(parts[1])
            elif parts[0] == "done":
                done = True
        if kind == "end":
            break
    common = [h for h in haves if h in OBJECTS]
    out = bytearray()
    if common:
        out += pkt("ACK %s\n" % common[-1])
    else:
        out += pkt("NAK\n")
    shas, _boundary, _unshallow = closure(wants, exclude_tips=haves)
    pack = build_pack(shas)
    out += _sideband_pack(pack)
    return bytes(out)


def _upload_pack_v2(repo, body):
    lines, pos, kind = read_pkt_lines(body, 0)
    command = None
    for raw in lines:
        line = raw.decode("utf-8", "replace").rstrip("\n")
        if line.startswith("command="):
            command = line[len("command="):]
    args = []
    if kind == "delim":
        arg_lines, pos, _ = read_pkt_lines(body, pos)
        for raw in arg_lines:
            args.append(raw.decode("utf-8", "replace").rstrip("\n"))

    if command == "ls-refs":
        return _ls_refs(repo, args)
    if command == "fetch":
        return _fetch_v2(repo, args)
    return pkt("ERR unknown command\n") + FLUSH


def _ls_refs(repo, args):
    prefixes = []
    peel = False
    symrefs = False
    unborn = False
    for a in args:
        if a.startswith("ref-prefix "):
            prefixes.append(a[len("ref-prefix "):])
        elif a == "peel":
            peel = True
        elif a == "symrefs":
            symrefs = True
        elif a == "unborn":
            unborn = True

    def matches(name):
        if not prefixes:
            return True
        return any(name.startswith(p) for p in prefixes)

    out = bytearray()
    head_ref = "refs/heads/" + repo.default_branch
    head_sha = repo.refs.get(head_ref)
    if matches("HEAD"):
        if head_sha:
            line = "%s HEAD" % head_sha
            if symrefs:
                line += " symref-target:%s" % head_ref
            out += pkt(line + "\n")
        elif unborn:
            line = "%s HEAD" % ZERO
            if symrefs:
                line += " symref-target:%s" % head_ref
            line += " unborn"
            out += pkt(line + "\n")
    for ref in sorted(repo.refs):
        if not matches(ref):
            continue
        sha = repo.refs[ref]
        line = "%s %s" % (sha, ref)
        if peel:
            obj = get_object(sha)
            if obj and obj[0] == "tag":
                target = tag_target(obj[1])
                while target:
                    tobj = get_object(target)
                    if tobj and tobj[0] == "tag":
                        target = tag_target(tobj[1])
                    else:
                        break
                if target:
                    line += " peeled:%s" % target
        out += pkt(line + "\n")
    out += FLUSH
    return bytes(out)


def _fetch_v2(repo, args):
    wants = []
    haves = []
    client_shallow = []
    want_refs = []
    depth = None
    wait_for_done = False
    done = False
    for a in args:
        if a.startswith("want "):
            wants.append(a[5:].strip())
        elif a.startswith("have "):
            haves.append(a[5:].strip())
        elif a.startswith("shallow "):
            client_shallow.append(a[8:].strip())
        elif a.startswith("deepen "):
            try:
                depth = int(a[7:].strip())
            except ValueError:
                depth = None
        elif a.startswith("want-ref "):
            want_refs.append(a[9:].strip())
        elif a == "wait-for-done":
            wait_for_done = True
        elif a == "done":
            done = True

    if wait_for_done and not done:
        out = bytearray()
        out += pkt("acknowledgments\n")
        common = [h for h in haves if h in OBJECTS]
        if common:
            for h in common:
                out += pkt("ACK %s\n" % h)
            out += pkt("ready\n")
        else:
            out += pkt("NAK\n")
        out += FLUSH
        return bytes(out)

    sections = []
    shas, boundary, unshallow = closure(wants, exclude_tips=haves, depth=depth,
                                        client_shallow=client_shallow)
    if depth is not None or client_shallow:
        sec = bytearray()
        sec += pkt("shallow-info\n")
        for sha in sorted(boundary):
            sec += pkt("shallow %s\n" % sha)
        for sha in sorted(unshallow):
            sec += pkt("unshallow %s\n" % sha)
        sections.append(bytes(sec))
    if want_refs:
        sec = bytearray()
        sec += pkt("wanted-refs\n")
        for ref in want_refs:
            sha = repo.refs.get(ref)
            if sha:
                sec += pkt("%s %s\n" % (sha, ref))
        sections.append(bytes(sec))
    pack = build_pack(shas)
    sec = bytearray()
    sec += pkt("packfile\n")
    sec += _sideband_pack(pack)[:-4]  # sideband chunks without their flush
    sections.append(bytes(sec))

    out = bytearray()
    for i, sec in enumerate(sections):
        out += sec
        out += DELIM if i < len(sections) - 1 else FLUSH
    return bytes(out)


def _receive_pack(repo, body):
    lines, pos, kind = read_pkt_lines(body, 0)
    commands = []
    caps = ""
    for i, raw in enumerate(lines):
        line = raw.decode("utf-8", "replace").rstrip("\n")
        if i == 0 and "\0" in line:
            line, caps = line.split("\0", 1)
        parts = line.split(" ")
        if len(parts) >= 3:
            commands.append((parts[0], parts[1], parts[2]))
    pack_data = body[pos:] if kind == "flush" else b""
    unpack_ok = True
    unpack_msg = "ok"
    if pack_data:
        try:
            parse_pack(pack_data)
        except Exception as e:
            unpack_ok = False
            unpack_msg = "error: %s" % e
    results = []
    for old, new, ref in commands:
        if not unpack_ok:
            results.append((ref, False, "unpack failed"))
            continue
        current = repo.refs.get(ref)
        if new == ZERO:
            if current is None:
                results.append((ref, False, "reference not found"))
            else:
                del repo.refs[ref]
                results.append((ref, True, ""))
            continue
        obj = get_object(new)
        if obj is None:
            results.append((ref, False, "not our ref"))
            continue
        if old == ZERO:
            repo.refs[ref] = new
            results.append((ref, True, ""))
            continue
        if current != old:
            results.append((ref, False, "stale info"))
            continue
        if obj[0] == "commit" and not is_ancestor(old, new):
            results.append((ref, False, "non-fast-forward"))
            continue
        repo.refs[ref] = new
        results.append((ref, True, ""))
    repo.updated_tick = tick()

    if "report-status" not in caps:
        return b""
    report = []
    report.append("unpack %s\n" % unpack_msg)
    for ref, ok, why in results:
        if ok:
            report.append("ok %s\n" % ref)
        else:
            report.append("ng %s %s\n" % (ref, why))
    out = bytearray()
    if "side-band-64k" in caps:
        for line in report:
            out += pkt(b"\x01" + line.encode())
        out += FLUSH
    else:
        for line in report:
            out += pkt(line)
        out += FLUSH
    return bytes(out)


Handler.handle_git = handle_git


# --------------------------------------------------------------------------
# MCP (JSON-RPC 2.0 over Streamable HTTP)

MCP_VERSIONS = ["2026-07-28", "2025-11-25", "2025-06-18", "2025-03-26", "2024-11-05"]

MCP_TOOLS = [
    {"name": "create_repo", "description": "Create a new repository for the authenticated user.",
     "inputSchema": {"type": "object", "properties": {
         "name": {"type": "string", "description": "Repository name"},
         "description": {"type": "string", "description": "Repository description"},
         "private": {"type": "boolean", "description": "Whether the repository is private"}},
         "required": ["name"]}},
    {"name": "get_repo", "description": "Get details of a repository.",
     "inputSchema": {"type": "object", "properties": {
         "owner": {"type": "string", "description": "Repository owner login"},
         "repo": {"type": "string", "description": "Repository name"}},
         "required": ["owner", "repo"]}},
    {"name": "create_issue", "description": "Create a new issue in a repository.",
     "inputSchema": {"type": "object", "properties": {
         "owner": {"type": "string"}, "repo": {"type": "string"},
         "title": {"type": "string"}, "body": {"type": "string"}},
         "required": ["owner", "repo", "title"]}},
    {"name": "list_issues", "description": "List issues in a repository.",
     "inputSchema": {"type": "object", "properties": {
         "owner": {"type": "string"}, "repo": {"type": "string"},
         "state": {"type": "string", "description": "open, closed or all"}},
         "required": ["owner", "repo"]}},
    {"name": "create_pull_request", "description": "Create a new pull request in a repository.",
     "inputSchema": {"type": "object", "properties": {
         "owner": {"type": "string"}, "repo": {"type": "string"},
         "title": {"type": "string"}, "body": {"type": "string"},
         "head": {"type": "string"}, "base": {"type": "string"}},
         "required": ["owner", "repo", "title", "head", "base"]}},
    {"name": "merge_pull_request", "description": "Merge a pull request.",
     "inputSchema": {"type": "object", "properties": {
         "owner": {"type": "string"}, "repo": {"type": "string"},
         "pull_number": {"type": "integer"}},
         "required": ["owner", "repo", "pull_number"]}},
]
MCP_TOOL_MAP = {t["name"]: t for t in MCP_TOOLS}


def _mcp_result_text(obj):
    return {"content": [{"type": "text", "text": json.dumps(obj)}],
            "structuredContent": obj, "isError": False}


def _mcp_error_result(message):
    return {"content": [{"type": "text", "text": message}], "isError": True}


def _mcp_call_tool(name, args):
    lname = name.lower()
    tool = None
    for t in MCP_TOOLS:
        if lname == t["name"] or lname.endswith(t["name"]):
            tool = t
            break
    if tool is None:
        return None, {"code": -32602, "message": "Unknown tool: %s" % name}
    args = args or {}
    if "repo" not in args and isinstance(args.get("full_name"), str) and "/" in args["full_name"]:
        owner_part, repo_part = args["full_name"].split("/", 1)
        args.setdefault("owner", owner_part)
        args["repo"] = repo_part
    for req in tool["inputSchema"].get("required", []):
        if args.get(req) is None:
            return _mcp_error_result("missing required argument: %s" % req), None
    try:
        if tool["name"] == "create_repo":
            rname = args["name"]
            if rname in REPOS:
                return _mcp_error_result("repository already exists"), None
            repo = Repo(rname, args.get("private", False), args.get("description", ""))
            REPOS[rname] = repo
            return _mcp_result_text(repo_view(repo)), None
        repo = get_repo(args.get("owner", ""), args.get("repo", ""))
        if tool["name"] == "get_repo":
            return _mcp_result_text(repo_view(repo)), None
        if tool["name"] == "create_issue":
            issue = new_issue(repo, args.get("title"), args.get("body"))
            return _mcp_result_text(issue_view(repo, issue)), None
        if tool["name"] == "list_issues":
            state = (args.get("state") or "open").lower()
            items = [issue_view(repo, i) for i in repo.issues.values()
                     if state == "all" or i["state"] == state]
            items.sort(key=lambda v: v["number"])
            return _mcp_result_text(items), None
        if tool["name"] == "create_pull_request":
            head = (args.get("head") or "").split(":")[-1]
            base_name = (args.get("base") or repo.default_branch).split(":")[-1]
            if "refs/heads/" + head not in repo.refs or "refs/heads/" + base_name not in repo.refs:
                return _mcp_error_result("head or base branch not found"), None
            pull = new_pull(repo, args.get("title"), args.get("body"), head, base_name)
            return _mcp_result_text(pull_view(repo, pull)), None
        if tool["name"] == "merge_pull_request":
            pull = repo.pulls.get(int(args["pull_number"]))
            if pull is None:
                return _mcp_error_result("pull request not found"), None
            if pull["state"] != "open" or not pull_mergeable(repo, pull):
                return _mcp_error_result("pull request is not mergeable"), None
            sha = merge_pull(repo, pull, "squash")
            return _mcp_result_text({"sha": sha, "merged": True,
                                     "message": "Pull Request successfully merged"}), None
    except ApiError as e:
        return _mcp_error_result(e.message), None
    return _mcp_error_result("unsupported tool"), None


def handle_mcp(self, body):
    try:
        payload = json.loads(body.decode("utf-8")) if body else None
    except Exception:
        self.send_json(400, {"jsonrpc": "2.0", "id": None,
                             "error": {"code": -32700, "message": "Parse error"}})
        return
    if isinstance(payload, list):
        responses = []
        for item in payload:
            resp = _mcp_one(item)
            if resp is not None:
                responses.append(resp)
        self.send_json(200, responses)
        return
    if not isinstance(payload, dict):
        self.send_json(400, {"jsonrpc": "2.0", "id": None,
                             "error": {"code": -32700, "message": "Parse error"}})
        return
    resp = _mcp_one(payload)
    if resp is None:
        self.send_bytes(202, b"", "application/json; charset=utf-8")
        return
    self.send_json(200, resp, {"Mcp-Session-Id": "forge-session"})


def _mcp_one(req):
    if not isinstance(req, dict):
        return {"jsonrpc": "2.0", "id": None, "error": {"code": -32600, "message": "Invalid Request"}}
    method = req.get("method", "")
    rid = req.get("id")
    params = req.get("params") or {}
    if rid is None:  # notification
        return None
    if method == "server/discover":
        result = {
            "protocolVersion": "2026-07-28",
            "supportedVersions": MCP_VERSIONS,
            "capabilities": {"tools": {"listChanged": False}},
            "serverInfo": {"name": "forge", "version": "1.0.0"},
        }
        return {"jsonrpc": "2.0", "id": rid, "result": result}
    if method == "initialize":
        want = params.get("protocolVersion")
        result = {
            "protocolVersion": want if want in MCP_VERSIONS else "2025-11-25",
            "capabilities": {"tools": {"listChanged": False}},
            "serverInfo": {"name": "forge", "version": "1.0.0"},
        }
        return {"jsonrpc": "2.0", "id": rid, "result": result}
    if method == "ping":
        return {"jsonrpc": "2.0", "id": rid, "result": {}}
    if method == "tools/list":
        return {"jsonrpc": "2.0", "id": rid, "result": {"tools": MCP_TOOLS}}
    if method == "tools/call":
        with LOCK:
            result, error = _mcp_call_tool(params.get("name", ""), params.get("arguments") or {})
        if error is not None:
            return {"jsonrpc": "2.0", "id": rid, "error": error}
        return {"jsonrpc": "2.0", "id": rid, "result": result}
    if method == "resources/list":
        return {"jsonrpc": "2.0", "id": rid, "result": {"resources": []}}
    if method == "prompts/list":
        return {"jsonrpc": "2.0", "id": rid, "result": {"prompts": []}}
    return {"jsonrpc": "2.0", "id": rid,
            "error": {"code": -32601, "message": "Method not found: %s" % method}}


Handler.handle_mcp = handle_mcp


# --------------------------------------------------------------------------
# GraphQL: a small parser and executor over the same store

class GqlError(Exception):
    pass


class UnknownField(Exception):
    def __init__(self, type_name, field):
        super().__init__(field)
        self.type_name = type_name
        self.field = field


def _gql_tokens(text):
    toks = []
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c in " \t\r\n,":
            i += 1
            continue
        if c == "#":
            while i < n and text[i] != "\n":
                i += 1
            continue
        if text.startswith("...", i):
            toks.append(("...", "..."))
            i += 3
            continue
        if c in "!$():=@[]{}|&":
            toks.append((c, c))
            i += 1
            continue
        if c == '"':
            if text.startswith('"""', i):
                j = text.find('"""', i + 3)
                if j < 0:
                    raise GqlError("unterminated block string")
                toks.append(("str", text[i + 3:j]))
                i = j + 3
                continue
            j = i + 1
            buf = []
            while j < n and text[j] != '"':
                if text[j] == "\\" and j + 1 < n:
                    esc = text[j + 1]
                    buf.append({"n": "\n", "t": "\t", "r": "\r", '"': '"', "\\": "\\", "/": "/"}.get(esc, esc))
                    j += 2
                else:
                    buf.append(text[j])
                    j += 1
            if j >= n:
                raise GqlError("unterminated string")
            toks.append(("str", "".join(buf)))
            i = j + 1
            continue
        if c.isdigit() or (c == "-" and i + 1 < n and text[i + 1].isdigit()):
            j = i + 1
            while j < n and (text[j].isdigit() or text[j] in ".eE+-"):
                j += 1
            num = text[i:j]
            toks.append(("float" if ("." in num or "e" in num or "E" in num) else "int", num))
            i = j
            continue
        if c.isalpha() or c == "_":
            j = i + 1
            while j < n and (text[j].isalnum() or text[j] == "_"):
                j += 1
            toks.append(("name", text[i:j]))
            i = j
            continue
        raise GqlError("unexpected character %r" % c)
    toks.append(("eof", ""))
    return toks


class _Parser:
    def __init__(self, text):
        self.toks = _gql_tokens(text)
        self.i = 0

    def peek(self):
        return self.toks[self.i]

    def next(self):
        t = self.toks[self.i]
        self.i += 1
        return t

    def expect(self, kind):
        t = self.next()
        if t[0] != kind:
            raise GqlError("expected %s, got %s" % (kind, t[0]))
        return t[1]

    def parse_document(self):
        ops = []
        frags = {}
        while self.peek()[0] != "eof":
            if self.peek()[0] == "{":
                ops.append({"kind": "query", "name": None, "selections": self.parse_selection_set()})
            elif self.peek() == ("name", "fragment"):
                self.next()
                fname = self.expect("name")
                if self.expect("name") != "on":
                    raise GqlError("fragment without on")
                cond = self.expect("name")
                self.parse_directives()
                frags[fname] = (cond, self.parse_selection_set())
            elif self.peek()[0] == "name" and self.peek()[1] in ("query", "mutation", "subscription"):
                kind = self.next()[1]
                name = None
                if self.peek()[0] == "name":
                    name = self.next()[1]
                if self.peek()[0] == "(":
                    self.parse_var_defs()
                self.parse_directives()
                ops.append({"kind": kind, "name": name, "selections": self.parse_selection_set()})
            else:
                raise GqlError("unexpected token %r" % (self.peek(),))
        return ops, frags

    def parse_var_defs(self):
        self.expect("(")
        while self.peek()[0] != ")":
            self.expect("$")
            self.expect("name")
            self.expect(":")
            self.parse_type()
            if self.peek()[0] == "=":
                self.next()
                self.parse_value()
            self.parse_directives()
        self.expect(")")

    def parse_type(self):
        if self.peek()[0] == "[":
            self.next()
            self.parse_type()
            self.expect("]")
        else:
            self.expect("name")
        if self.peek()[0] == "!":
            self.next()

    def parse_directives(self):
        dirs = []
        while self.peek()[0] == "@":
            self.next()
            dname = self.expect("name")
            dargs = {}
            if self.peek()[0] == "(":
                dargs = self.parse_args()
            dirs.append((dname, dargs))
        return dirs

    def parse_args(self):
        args = {}
        self.expect("(")
        while self.peek()[0] != ")":
            aname = self.expect("name")
            self.expect(":")
            args[aname] = self.parse_value()
        self.expect(")")
        return args

    def parse_value(self):
        kind, val = self.peek()
        if kind == "$":
            self.next()
            return ("var", self.expect("name"))
        if kind == "int":
            self.next()
            return ("int", int(val))
        if kind == "float":
            self.next()
            return ("float", float(val))
        if kind == "str":
            self.next()
            return ("str", val)
        if kind == "[":
            self.next()
            items = []
            while self.peek()[0] != "]":
                items.append(self.parse_value())
            self.expect("]")
            return ("list", items)
        if kind == "{":
            self.next()
            obj = {}
            while self.peek()[0] != "}":
                k = self.expect("name")
                self.expect(":")
                obj[k] = self.parse_value()
            self.expect("}")
            return ("obj", obj)
        if kind == "name":
            self.next()
            if val == "true":
                return ("bool", True)
            if val == "false":
                return ("bool", False)
            if val == "null":
                return ("null", None)
            return ("enum", val)
        raise GqlError("bad value")

    def parse_selection_set(self):
        self.expect("{")
        sels = []
        while self.peek()[0] != "}":
            sels.append(self.parse_selection())
        self.expect("}")
        return sels

    def parse_selection(self):
        if self.peek()[0] == "...":
            self.next()
            if self.peek()[0] == "name" and self.peek()[1] == "on":
                self.next()
                cond = self.expect("name")
                dirs = self.parse_directives()
                return ("inline", cond, dirs, self.parse_selection_set())
            if self.peek()[0] == "name":
                fname = self.next()[1]
                dirs = self.parse_directives()
                return ("spread", fname, dirs)
            return ("inline", None, [], self.parse_selection_set())
        first = self.expect("name")
        alias = None
        name = first
        if self.peek()[0] == ":":
            self.next()
            alias = first
            name = self.expect("name")
        args = {}
        if self.peek()[0] == "(":
            args = self.parse_args()
        dirs = self.parse_directives()
        sels = []
        if self.peek()[0] == "{":
            sels = self.parse_selection_set()
        return ("field", alias, name, args, dirs, sels)


def _eval_value(v, variables):
    kind = v[0]
    if kind == "var":
        return variables.get(v[1])
    if kind in ("int", "float", "str", "bool", "enum"):
        return v[1]
    if kind == "null":
        return None
    if kind == "list":
        return [_eval_value(x, variables) for x in v[1]]
    if kind == "obj":
        return {k: _eval_value(x, variables) for k, x in v[1].items()}
    return None


def _cursor(i):
    return base64.b64encode(("cursor:%d" % i).encode()).decode()


def _uncursor(c):
    try:
        raw = base64.b64decode(c).decode()
        return int(raw.split(":")[1])
    except Exception:
        return -1


def make_conn(type_name, items, args):
    args = args or {}
    start = 0
    if args.get("after"):
        start = _uncursor(args["after"]) + 1
    end = len(items)
    if args.get("first") is not None:
        end = min(len(items), start + int(args["first"]))
    elif args.get("last") is not None:
        start = max(start, len(items) - int(args["last"]))
    sliced = items[start:end]
    page_info = {
        "__type": "PageInfo",
        "hasNextPage": end < len(items),
        "hasPreviousPage": start > 0,
        "startCursor": _cursor(start) if sliced else None,
        "endCursor": _cursor(start + len(sliced) - 1) if sliced else None,
    }
    return {"__type": type_name, "__items": sliced, "__start": start,
            "totalCount": len(items), "pageInfo": page_info}


# -- node constructors ------------------------------------------------------

def user_node(login=None):
    login = login or viewer_login()
    return {"__type": "User", "id": gid("User", 1), "login": login, "name": login,
            "url": "https://forge.invalid/" + login, "email": "", "isViewer": True,
            "avatarUrl": ""}


def repo_node(repo):
    return {"__type": "Repository", "__repo": repo, "id": gid("Repository", repo.id),
            "databaseId": repo.id, "name": repo.name,
            "nameWithOwner": "%s/%s" % (viewer_login(), repo.name),
            "isPrivate": repo.private, "description": repo.description,
            "viewerPermission": "ADMIN", "hasIssuesEnabled": True,
            "hasProjectsEnabled": True, "hasWikiEnabled": True, "isFork": False,
            "isArchived": False, "isEmpty": not bool(repo.refs), "forkCount": 0,
            "stargazerCount": 0, "createdAt": iso_of(repo.created_tick),
            "updatedAt": iso_of(repo.updated_tick), "pushedAt": iso_of(repo.updated_tick),
            "url": "https://forge.invalid/%s/%s" % (viewer_login(), repo.name)}


def issue_node(repo, issue):
    return {"__type": "Issue", "__repo": repo, "__issue": issue,
            "id": gid("Issue", issue["id"]), "number": issue["number"],
            "title": issue["title"], "body": issue["body"],
            "state": issue["state"].upper(),
            "url": "https://forge.invalid/%s/%s/issues/%d" % (viewer_login(), repo.name, issue["number"]),
            "createdAt": iso_of(issue["created_tick"]), "updatedAt": iso_of(issue["updated_tick"]),
            "closedAt": iso_of(issue["closed_tick"]) if issue.get("closed_tick") else None}


def comment_node(repo, comment):
    return {"__type": "IssueComment", "__repo": repo, "id": gid("IssueComment", comment["id"]),
            "body": comment["body"], "createdAt": iso_of(comment["created_tick"]),
            "updatedAt": iso_of(comment["created_tick"]), "url": ""}


def label_node(label):
    return {"__type": "Label", "id": gid("Label", label["id"]), "name": label["name"],
            "color": label.get("color", "ededed"), "description": label.get("description") or ""}


def ref_node(repo, refname):
    sha = repo.refs.get(refname)
    if sha is None:
        return None
    prefix = "refs/heads/" if refname.startswith("refs/heads/") else "refs/tags/"
    return {"__type": "Ref", "__repo": repo, "__ref": refname, "__sha": sha,
            "name": refname[len(prefix):], "prefix": prefix, "qualifiedName": refname}


def commit_node(sha):
    obj = get_object(sha)
    info = {"tree": None, "parents": [], "message": ""}
    author = {"__type": "GitActor", "name": viewer_login(),
              "email": "%s@example.invalid" % viewer_login(), "date": now_iso()}
    if obj and obj[0] == "commit":
        info = parse_commit(obj[1])
        head = obj[1].split(b"\n\n")[0].decode("utf-8", "replace")
        for line in head.split("\n"):
            if line.startswith("author "):
                rest = line[7:]
                try:
                    ident, ts, _tz = rest.rsplit(" ", 2)
                    nm, em = ident.rsplit(" <", 1)
                    author = {"__type": "GitActor", "name": nm, "email": em.rstrip(">"),
                              "date": datetime.fromtimestamp(int(ts), tz=timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")}
                except Exception:
                    pass
    return {"__type": "Commit", "__sha": sha, "__info": info, "oid": sha,
            "message": info["message"],
            "messageHeadline": info["message"].split("\n")[0] if info["message"] else "",
            "committedDate": author["date"], "authoredDate": author["date"],
            "url": "", "__author": author}


def pull_node(repo, pull):
    state = "MERGED" if pull.get("merged") else pull["state"].upper()
    if pull["state"] != "open":
        mergeable = "UNKNOWN"
    else:
        mergeable = "MERGEABLE" if pull_mergeable(repo, pull) else "CONFLICTING"
    return {"__type": "PullRequest", "__repo": repo, "__pull": pull,
            "id": gid("PullRequest", pull["id"]), "number": pull["number"],
            "title": pull["title"], "body": pull["body"], "state": state,
            "merged": bool(pull.get("merged")), "mergeable": mergeable,
            "isDraft": False, "headRefName": pull["head"], "baseRefName": pull["base"],
            "headRefOid": branch_tip(repo, pull["head"]) or ZERO,
            "baseRefOid": branch_tip(repo, pull["base"]) or ZERO,
            "url": "https://forge.invalid/%s/%s/pull/%d" % (viewer_login(), repo.name, pull["number"]),
            "createdAt": iso_of(pull["created_tick"]), "updatedAt": iso_of(pull["updated_tick"]),
            "closedAt": iso_of(pull["closed_tick"]) if pull.get("closed_tick") else None,
            "mergedAt": iso_of(pull["merged_tick"]) if pull.get("merged_tick") else None,
            "additions": 0, "deletions": 0, "changedFiles": 0}


def _find_repo_by_dbid(dbid):
    for repo in REPOS.values():
        if repo.id == dbid:
            return repo
    return None


def _decode_gid(raw):
    try:
        decoded = base64.b64decode(raw).decode()
        kind, ident = decoded.split(":", 1)
        return kind, ident
    except Exception:
        return None, None


def _find_issue(gid_raw):
    kind, ident = _decode_gid(gid_raw)
    if kind != "Issue":
        return None, None
    for repo in REPOS.values():
        for issue in repo.issues.values():
            if issue["id"] == int(ident):
                return repo, issue
    return None, None


def _find_pull(gid_raw):
    kind, ident = _decode_gid(gid_raw)
    if kind != "PullRequest":
        return None, None
    for repo in REPOS.values():
        for pull in repo.pulls.values():
            if pull["id"] == int(ident):
                return repo, pull
    return None, None


def _node_by_id(raw):
    kind, ident = _decode_gid(raw)
    if kind == "Repository":
        repo = _find_repo_by_dbid(int(ident))
        return repo_node(repo) if repo else None
    if kind == "Issue":
        repo, issue = _find_issue(raw)
        return issue_node(repo, issue) if issue else None
    if kind == "PullRequest":
        repo, pull = _find_pull(raw)
        return pull_node(repo, pull) if pull else None
    if kind == "User":
        return user_node()
    if kind == "Label":
        for repo in REPOS.values():
            for label in repo.labels.values():
                if label["id"] == int(ident):
                    return label_node(label)
    if kind == "IssueComment":
        for repo in REPOS.values():
            for issue in repo.issues.values():
                for c in issue["comments"]:
                    if c["id"] == int(ident):
                        return comment_node(repo, c)
    return None


# -- field handlers -----------------------------------------------------------

def _h_query_viewer(node, args, ctx):
    return user_node()


def _h_query_repository(node, args, ctx):
    owner = args.get("owner") or ""
    name = args.get("name") or ""
    learn_viewer(owner)
    if VIEWER["login"] is not None and owner != VIEWER["login"]:
        return None
    repo = REPOS.get(name)
    return repo_node(repo) if repo else None


def _h_query_node(node, args, ctx):
    return _node_by_id(args.get("id") or "")


def _h_query_search(node, args, ctx):
    conn = make_conn("SearchResultItemConnection", [], args)
    conn["issueCount"] = 0
    conn["repositoryCount"] = 0
    conn["userCount"] = 0
    return conn


def _h_query_ratelimit(node, args, ctx):
    return {"__type": "RateLimit", "limit": 5000, "cost": 1, "remaining": 4999,
            "used": 1, "nodeCount": 0, "resetAt": now_iso()}


def _h_repo_owner(node, args, ctx):
    return user_node()


def _h_repo_default_branch_ref(node, args, ctx):
    repo = node["__repo"]
    return ref_node(repo, "refs/heads/" + repo.default_branch)


def _sorted_issues(repo, args):
    items = list(repo.issues.values())
    states = args.get("states")
    if states:
        wanted = {s.upper() for s in states}
        items = [i for i in items if i["state"].upper() in wanted]
    order = args.get("orderBy") or {}
    direction = (order.get("direction") or "DESC").upper()
    items.sort(key=lambda i: (i["created_tick"], i["number"]), reverse=(direction != "ASC"))
    return items


def _h_repo_issue(node, args, ctx):
    repo = node["__repo"]
    issue = repo.issues.get(int(args.get("number") or 0))
    return issue_node(repo, issue) if issue else None


def _h_repo_issues(node, args, ctx):
    repo = node["__repo"]
    items = [issue_node(repo, i) for i in _sorted_issues(repo, args)]
    labels = args.get("labels")
    if labels:
        wanted = set(labels)
        items = [n for n in items if wanted & {l for l in n["__issue"]["labels"]}]
    return make_conn("IssueConnection", items, args)


def _h_repo_pull_request(node, args, ctx):
    repo = node["__repo"]
    pull = repo.pulls.get(int(args.get("number") or 0))
    return pull_node(repo, pull) if pull else None


def _h_repo_pull_requests(node, args, ctx):
    repo = node["__repo"]
    items = list(repo.pulls.values())
    states = args.get("states")
    if states:
        wanted = {s.upper() for s in states}
        def state_of(p):
            return "MERGED" if p.get("merged") else p["state"].upper()
        items = [p for p in items if state_of(p) in wanted]
    items.sort(key=lambda p: (p["created_tick"], p["number"]), reverse=True)
    return make_conn("PullRequestConnection", [pull_node(repo, p) for p in items], args)


def _h_repo_ref(node, args, ctx):
    repo = node["__repo"]
    qn = args.get("qualifiedName") or ""
    if not qn.startswith("refs/"):
        qn = "refs/heads/" + qn
    return ref_node(repo, qn)


def _h_issue_author(node, args, ctx):
    return user_node()


def _h_issue_repository(node, args, ctx):
    return repo_node(node["__repo"])


def _h_issue_labels(node, args, ctx):
    repo = node["__repo"]
    items = [label_node(repo.labels[n]) for n in node["__issue"]["labels"] if n in repo.labels]
    return make_conn("LabelConnection", items, args)


def _h_issue_comments(node, args, ctx):
    repo = node["__repo"]
    items = [comment_node(repo, c) for c in node["__issue"]["comments"]]
    return make_conn("IssueCommentConnection", items, args)


def _h_pull_files(node, args, ctx):
    repo = node["__repo"]
    change = {"added": "ADDED", "modified": "MODIFIED", "removed": "DELETED"}
    items = []
    for f in pull_files(repo, node["__pull"]):
        items.append({"__type": "PullRequestChangedFile", "path": f["filename"],
                      "additions": f["additions"], "deletions": f["deletions"],
                      "changeType": change.get(f["status"], "MODIFIED")})
    return make_conn("PullRequestChangedFileConnection", items, args)


def _h_pull_merge_commit(node, args, ctx):
    sha = node["__pull"].get("merge_commit_sha")
    return commit_node(sha) if sha else None


def _h_pull_commits(node, args, ctx):
    repo = node["__repo"]
    items = [commit_node(s) for s in pull_commits(repo, node["__pull"])]
    return make_conn("PullRequestCommitConnection", items, args)


def _h_pull_head_ref(node, args, ctx):
    return ref_node(node["__repo"], "refs/heads/" + node["__pull"]["head"])


def _h_pull_base_ref(node, args, ctx):
    return ref_node(node["__repo"], "refs/heads/" + node["__pull"]["base"])


def _h_ref_target(node, args, ctx):
    return commit_node(node["__sha"])


def _h_ref_repository(node, args, ctx):
    return repo_node(node["__repo"])


def _h_commit_author(node, args, ctx):
    return node["__author"]


def _h_commit_tree(node, args, ctx):
    tree = node["__info"]["tree"]
    return {"__type": "Tree", "oid": tree} if tree else None


def _h_commit_parents(node, args, ctx):
    items = [commit_node(p) for p in node["__info"]["parents"]]
    return make_conn("CommitConnection", items, args)


def _h_conn_edges(node, args, ctx):
    start = node["__start"]
    return [{"__type": "Edge", "node": item, "cursor": _cursor(start + i)}
            for i, item in enumerate(node["__items"])]


def _h_conn_nodes(node, args, ctx):
    return node["__items"]


def _h_mut_create_issue(node, args, ctx):
    inp = args.get("input") or args
    repo = _find_repo_by_dbid(int(_decode_gid(inp.get("repositoryId") or "")[1] or 0))
    if repo is None:
        raise GqlError("repository not found")
    issue = new_issue(repo, inp.get("title"), inp.get("body"))
    return {"__type": "CreateIssuePayload", "issue": issue_node(repo, issue),
            "clientMutationId": inp.get("clientMutationId")}


def _h_mut_close_issue(node, args, ctx):
    inp = args.get("input") or args
    repo, issue = _find_issue(inp.get("issueId") or "")
    if issue is None:
        raise GqlError("issue not found")
    issue["state"] = "closed"
    issue["closed_tick"] = tick()
    issue["updated_tick"] = issue["closed_tick"]
    return {"__type": "CloseIssuePayload", "issue": issue_node(repo, issue),
            "clientMutationId": inp.get("clientMutationId")}


def _h_mut_reopen_issue(node, args, ctx):
    inp = args.get("input") or args
    repo, issue = _find_issue(inp.get("issueId") or "")
    if issue is None:
        raise GqlError("issue not found")
    issue["state"] = "open"
    issue["closed_tick"] = None
    issue["updated_tick"] = tick()
    return {"__type": "ReopenIssuePayload", "issue": issue_node(repo, issue),
            "clientMutationId": inp.get("clientMutationId")}


def _h_mut_create_pull(node, args, ctx):
    inp = args.get("input") or args
    repo = _find_repo_by_dbid(int(_decode_gid(inp.get("repositoryId") or "")[1] or 0))
    if repo is None:
        raise GqlError("repository not found")
    head = (inp.get("headRefName") or "").replace("refs/heads/", "")
    base_name = (inp.get("baseRefName") or repo.default_branch).replace("refs/heads/", "")
    pull = new_pull(repo, inp.get("title"), inp.get("body"), head, base_name)
    return {"__type": "CreatePullRequestPayload", "pullRequest": pull_node(repo, pull),
            "clientMutationId": inp.get("clientMutationId")}


def _h_mut_merge_pull(node, args, ctx):
    inp = args.get("input") or args
    repo, pull = _find_pull(inp.get("pullRequestId") or "")
    if pull is None:
        raise GqlError("pull request not found")
    method = (inp.get("mergeMethod") or "SQUASH").lower()
    if pull["state"] == "open" and pull_mergeable(repo, pull):
        merge_pull(repo, pull, "merge" if method == "merge" else "squash")
    return {"__type": "MergePullRequestPayload", "pullRequest": pull_node(repo, pull),
            "clientMutationId": inp.get("clientMutationId")}


def _h_mut_add_comment(node, args, ctx):
    inp = args.get("input") or args
    subject = inp.get("subjectId") or ""
    repo, issue = _find_issue(subject)
    target = None
    if issue is not None:
        target = issue
    else:
        repo, pull = _find_pull(subject)
        if pull is not None:
            target = pull
            target.setdefault("comments", [])
    if target is None:
        raise GqlError("subject not found")
    _comment_seq[0] += 1
    comment = {"id": _comment_seq[0], "body": inp.get("body") or "", "created_tick": tick()}
    target["comments"].append(comment)
    edge = {"__type": "IssueCommentEdge", "node": comment_node(repo, comment), "cursor": _cursor(0)}
    return {"__type": "AddCommentPayload", "commentEdge": edge,
            "clientMutationId": inp.get("clientMutationId")}


FIELD_HANDLERS = {
    ("Query", "viewer"): _h_query_viewer,
    ("Query", "repository"): _h_query_repository,
    ("Query", "node"): _h_query_node,
    ("Query", "search"): _h_query_search,
    ("Query", "rateLimit"): _h_query_ratelimit,
    ("Repository", "owner"): _h_repo_owner,
    ("Repository", "defaultBranchRef"): _h_repo_default_branch_ref,
    ("Repository", "issue"): _h_repo_issue,
    ("Repository", "issues"): _h_repo_issues,
    ("Repository", "pullRequest"): _h_repo_pull_request,
    ("Repository", "pullRequests"): _h_repo_pull_requests,
    ("Repository", "ref"): _h_repo_ref,
    ("Issue", "author"): _h_issue_author,
    ("Issue", "repository"): _h_issue_repository,
    ("Issue", "labels"): _h_issue_labels,
    ("Issue", "comments"): _h_issue_comments,
    ("PullRequest", "author"): _h_issue_author,
    ("PullRequest", "repository"): _h_issue_repository,
    ("PullRequest", "files"): _h_pull_files,
    ("PullRequest", "mergeCommit"): _h_pull_merge_commit,
    ("PullRequest", "commits"): _h_pull_commits,
    ("PullRequest", "headRef"): _h_pull_head_ref,
    ("PullRequest", "baseRef"): _h_pull_base_ref,
    ("IssueComment", "author"): _h_issue_author,
    ("Ref", "target"): _h_ref_target,
    ("Ref", "repository"): _h_ref_repository,
    ("Commit", "author"): _h_commit_author,
    ("Commit", "tree"): _h_commit_tree,
    ("Commit", "parents"): _h_commit_parents,
    ("Mutation", "createIssue"): _h_mut_create_issue,
    ("Mutation", "closeIssue"): _h_mut_close_issue,
    ("Mutation", "reopenIssue"): _h_mut_reopen_issue,
    ("Mutation", "createPullRequest"): _h_mut_create_pull,
    ("Mutation", "mergePullRequest"): _h_mut_merge_pull,
    ("Mutation", "addComment"): _h_mut_add_comment,
}
for _conn in ("IssueConnection", "PullRequestConnection", "LabelConnection",
              "IssueCommentConnection", "PullRequestChangedFileConnection",
              "CommitConnection", "PullRequestCommitConnection", "SearchResultItemConnection"):
    FIELD_HANDLERS[(_conn, "edges")] = _h_conn_edges
    FIELD_HANDLERS[(_conn, "nodes")] = _h_conn_nodes


# -- introspection ------------------------------------------------------------

_SCALARS = {"ID", "String", "Int", "Float", "Boolean", "DateTime", "URI", "GitObjectID", "GitTimestamp", "HTML"}
_ENUMS = {"IssueState", "PullRequestState", "MergeableState", "RepositoryPermission",
          "PatchType", "IssueOrderField", "OrderDirection", "SearchType", "PullRequestReviewState"}


def _type_kind(name):
    if name in GQL_TYPES:
        return GQL_TYPES[name][0]
    if name in _SCALARS:
        return "SCALAR"
    if name in _ENUMS:
        return "ENUM"
    return "OBJECT"


def _fields(*pairs):
    return list(pairs)


GQL_TYPES = {
    "Query": ("OBJECT", _fields(("viewer", "User"), ("repository", "Repository"), ("node", "Node"),
                                ("search", "SearchResultItemConnection"), ("rateLimit", "RateLimit"))),
    "Mutation": ("OBJECT", _fields(("createIssue", "CreateIssuePayload"), ("closeIssue", "CloseIssuePayload"),
                                   ("reopenIssue", "ReopenIssuePayload"),
                                   ("createPullRequest", "CreatePullRequestPayload"),
                                   ("mergePullRequest", "MergePullRequestPayload"),
                                   ("addComment", "AddCommentPayload"))),
    "User": ("OBJECT", _fields(("id", "ID"), ("login", "String"), ("name", "String"),
                               ("url", "URI"), ("email", "String"), ("isViewer", "Boolean"))),
    "Repository": ("OBJECT", _fields(("id", "ID"), ("databaseId", "Int"), ("name", "String"),
                                     ("nameWithOwner", "String"), ("owner", "RepositoryOwner"),
                                     ("defaultBranchRef", "Ref"), ("viewerPermission", "RepositoryPermission"),
                                     ("hasIssuesEnabled", "Boolean"), ("issue", "Issue"),
                                     ("issues", "IssueConnection"), ("pullRequest", "PullRequest"),
                                     ("pullRequests", "PullRequestConnection"), ("url", "URI"),
                                     ("createdAt", "DateTime"), ("updatedAt", "DateTime"),
                                     ("isPrivate", "Boolean"), ("description", "String"))),
    "Issue": ("OBJECT", _fields(("id", "ID"), ("number", "Int"), ("title", "String"),
                                ("state", "IssueState"), ("body", "String"), ("url", "URI"),
                                ("createdAt", "DateTime"), ("updatedAt", "DateTime"),
                                ("closedAt", "DateTime"), ("author", "Actor"),
                                ("labels", "LabelConnection"), ("comments", "IssueCommentConnection"),
                                ("repository", "Repository"))),
    "PullRequest": ("OBJECT", _fields(("id", "ID"), ("number", "Int"), ("title", "String"),
                                      ("body", "String"), ("state", "PullRequestState"),
                                      ("merged", "Boolean"), ("mergeable", "MergeableState"),
                                      ("headRefName", "String"), ("baseRefName", "String"),
                                      ("headRefOid", "GitObjectID"), ("baseRefOid", "GitObjectID"),
                                      ("url", "URI"), ("createdAt", "DateTime"), ("updatedAt", "DateTime"),
                                      ("mergedAt", "DateTime"), ("closedAt", "DateTime"),
                                      ("author", "Actor"), ("repository", "Repository"),
                                      ("files", "PullRequestChangedFileConnection"),
                                      ("mergeCommit", "Commit"), ("commits", "PullRequestCommitConnection"),
                                      ("isDraft", "Boolean"), ("additions", "Int"), ("deletions", "Int"))),
    "Label": ("OBJECT", _fields(("id", "ID"), ("name", "String"), ("color", "String"), ("description", "String"))),
    "IssueComment": ("OBJECT", _fields(("id", "ID"), ("body", "String"), ("author", "Actor"),
                                       ("createdAt", "DateTime"), ("updatedAt", "DateTime"), ("url", "URI"))),
    "Ref": ("OBJECT", _fields(("name", "String"), ("prefix", "String"), ("qualifiedName", "String"),
                              ("target", "GitObject"), ("repository", "Repository"))),
    "Commit": ("OBJECT", _fields(("oid", "GitObjectID"), ("message", "String"),
                                 ("messageHeadline", "String"), ("committedDate", "DateTime"),
                                 ("authoredDate", "DateTime"), ("author", "GitActor"),
                                 ("tree", "Tree"), ("url", "URI"))),
    "Tree": ("OBJECT", _fields(("oid", "GitObjectID"))),
    "GitActor": ("OBJECT", _fields(("name", "String"), ("email", "String"), ("date", "DateTime"))),
    "PageInfo": ("OBJECT", _fields(("hasNextPage", "Boolean"), ("hasPreviousPage", "Boolean"),
                                   ("startCursor", "String"), ("endCursor", "String"))),
    "PullRequestChangedFile": ("OBJECT", _fields(("path", "String"), ("additions", "Int"),
                                                 ("deletions", "Int"), ("changeType", "PatchType"))),
    "RateLimit": ("OBJECT", _fields(("limit", "Int"), ("cost", "Int"), ("remaining", "Int"),
                                    ("used", "Int"), ("nodeCount", "Int"), ("resetAt", "DateTime"))),
    "CreateIssuePayload": ("OBJECT", _fields(("issue", "Issue"), ("clientMutationId", "String"))),
    "CloseIssuePayload": ("OBJECT", _fields(("issue", "Issue"), ("clientMutationId", "String"))),
    "ReopenIssuePayload": ("OBJECT", _fields(("issue", "Issue"), ("clientMutationId", "String"))),
    "CreatePullRequestPayload": ("OBJECT", _fields(("pullRequest", "PullRequest"), ("clientMutationId", "String"))),
    "MergePullRequestPayload": ("OBJECT", _fields(("pullRequest", "PullRequest"), ("clientMutationId", "String"))),
    "AddCommentPayload": ("OBJECT", _fields(("commentEdge", "IssueCommentEdge"), ("clientMutationId", "String"))),
    "IssueCommentEdge": ("OBJECT", _fields(("node", "IssueComment"), ("cursor", "String"))),
    "SearchType": ("ENUM", None),
}
for _c, _item in (("IssueConnection", "Issue"), ("PullRequestConnection", "PullRequest"),
                  ("LabelConnection", "Label"), ("IssueCommentConnection", "IssueComment"),
                  ("PullRequestChangedFileConnection", "PullRequestChangedFile"),
                  ("CommitConnection", "Commit"), ("PullRequestCommitConnection", "Commit"),
                  ("SearchResultItemConnection", "SearchResultItem")):
    GQL_TYPES[_c] = ("OBJECT", _fields(("totalCount", "Int"), ("nodes", _item),
                                       ("edges", _item + "Edge"), ("pageInfo", "PageInfo")))
    GQL_TYPES[_item + "Edge"] = ("OBJECT", _fields(("node", _item), ("cursor", "String")))
GQL_TYPES["SearchResultItemConnection"] = ("OBJECT", _fields(
    ("totalCount", "Int"), ("issueCount", "Int"), ("repositoryCount", "Int"), ("userCount", "Int"),
    ("nodes", "SearchResultItem"), ("edges", "SearchResultItemEdge"), ("pageInfo", "PageInfo")))


def _type_node(name):
    kind, fields = GQL_TYPES.get(name, ("OBJECT", []))
    node = {"__type": "__Type", "name": name, "kind": kind, "description": None,
            "__gql_fields": fields, "__gql_enums": None}
    if kind == "ENUM":
        values = ["ISSUE", "REPOSITORY", "USER", "DISCUSSION"] if name == "SearchType" else ["OPEN", "CLOSED"]
        node["__gql_enums"] = values
    return node


def _h_type_fields(node, args, ctx):
    out = []
    for fname, tname in node.get("__gql_fields") or []:
        out.append({"__type": "__Field", "name": fname, "description": None, "args": [],
                    "type": _type_node(tname), "isDeprecated": False, "deprecationReason": None})
    return out


def _h_type_enum_values(node, args, ctx):
    return [{"__type": "__EnumValue", "name": v, "description": None,
             "isDeprecated": False, "deprecationReason": None}
            for v in (node.get("__gql_enums") or [])]


FIELD_HANDLERS[("__Type", "fields")] = _h_type_fields
FIELD_HANDLERS[("__Type", "enumValues")] = _h_type_enum_values
FIELD_HANDLERS[("__Type", "possibleTypes")] = lambda n, a, c: None
FIELD_HANDLERS[("__Type", "inputFields")] = lambda n, a, c: None
FIELD_HANDLERS[("__Type", "ofType")] = lambda n, a, c: None
FIELD_HANDLERS[("__Type", "specifiedByURL")] = lambda n, a, c: None
FIELD_HANDLERS[("__Type", "isOneOf")] = lambda n, a, c: False


def _h_query_type(node, args, ctx):
    name = args.get("name") or ""
    if name in GQL_TYPES or name in _SCALARS or name in _ENUMS:
        return _type_node(name)
    return None


def _h_query_schema(node, args, ctx):
    return {"__type": "__Schema"}


FIELD_HANDLERS[("Query", "__type")] = _h_query_type
FIELD_HANDLERS[("Query", "__schema")] = _h_query_schema
FIELD_HANDLERS[("__Schema", "queryType")] = lambda n, a, c: _type_node("Query")
FIELD_HANDLERS[("__Schema", "mutationType")] = lambda n, a, c: _type_node("Mutation")
FIELD_HANDLERS[("__Schema", "subscriptionType")] = lambda n, a, c: None
FIELD_HANDLERS[("__Schema", "types")] = lambda n, a, c: [_type_node(t) for t in GQL_TYPES]
FIELD_HANDLERS[("__Schema", "directives")] = lambda n, a, c: []


# -- executor -----------------------------------------------------------------

_INTERFACES = {"Node", "Actor", "RepositoryOwner", "GitObject", "UniformResourceLocatable", "Comment"}


def _directives_ok(dirs, variables):
    for dname, dargs in dirs:
        if dname == "skip" and _eval_value(dargs.get("if", ("bool", False)), variables) is True:
            return False
        if dname == "include" and _eval_value(dargs.get("if", ("bool", True)), variables) is False:
            return False
    return True


def _resolve_field(node, type_name, field, args, ctx):
    if field == "__typename":
        return type_name
    handler = FIELD_HANDLERS.get((type_name, field))
    if handler is not None:
        return handler(node, args, ctx)
    if not field.startswith("__") and field in node:
        return node[field]
    raise UnknownField(type_name, field)


def _exec_set(node, type_name, selections, ctx, frags):
    out = {}
    for sel in selections:
        if sel[0] == "field":
            _, alias, name, arg_asts, dirs, subsels = sel
            if not _directives_ok(dirs, ctx["variables"]):
                continue
            key = alias or name
            args = {k: _eval_value(v, ctx["variables"]) for k, v in arg_asts.items()}
            try:
                value = _resolve_field(node, type_name, name, args, ctx)
            except UnknownField:
                ctx["errors"].append({
                    "message": "Field '%s' doesn't exist on type '%s'" % (name, type_name),
                    "locations": [], "path": [key]})
                out[key] = None
                continue
            except GqlError as e:
                ctx["errors"].append({"message": str(e), "path": [key]})
                out[key] = None
                continue
            out[key] = _complete(value, subsels, ctx, frags)
        elif sel[0] == "spread":
            _, fname, dirs = sel
            if not _directives_ok(dirs, ctx["variables"]):
                continue
            frag = frags.get(fname)
            if frag is None:
                continue
            cond, fsel = frag
            if cond == type_name or cond in _INTERFACES:
                out.update(_exec_set(node, type_name, fsel, ctx, frags))
        elif sel[0] == "inline":
            _, cond, dirs, fsel = sel
            if not _directives_ok(dirs, ctx["variables"]):
                continue
            if cond is None or cond == type_name or cond in _INTERFACES:
                out.update(_exec_set(node, type_name, fsel, ctx, frags))
    return out


def _complete(value, subsels, ctx, frags):
    if value is None:
        return None
    if isinstance(value, list):
        return [_complete(v, subsels, ctx, frags) for v in value]
    if isinstance(value, dict) and "__type" in value:
        if not subsels:
            return value.get("id") or value.get("oid") or ""
        return _exec_set(value, value["__type"], subsels, ctx, frags)
    return value


def _gql_run_one(payload):
    query = payload.get("query")
    if not isinstance(query, str):
        return {"errors": [{"message": "query is required"}]}
    variables = payload.get("variables") or {}
    try:
        ops, frags = _Parser(query).parse_document()
    except GqlError as e:
        return {"errors": [{"message": str(e)}]}
    if not ops:
        return {"errors": [{"message": "no operation"}]}
    opname = payload.get("operationName")
    chosen = None
    if opname:
        chosen = [op for op in ops if op["name"] == opname]
    elif len(ops) == 1:
        chosen = ops
    if chosen is None:
        # several operations and no name: answer each in order
        return [_gql_run_op(op, variables, frags) for op in ops]
    return _gql_run_op(chosen[0], variables, frags)


def _gql_run_op(op, variables, frags):
    ctx = {"variables": variables, "errors": []}
    root_type = "Mutation" if op["kind"] == "mutation" else "Query"
    root = {"__type": root_type}
    with LOCK:
        data = _exec_set(root, root_type, op["selections"], ctx, frags)
    result = {"data": data}
    if ctx["errors"]:
        result["errors"] = ctx["errors"]
    return result


def handle_graphql(self, body):
    try:
        payload = json.loads(body.decode("utf-8")) if body else None
    except Exception:
        self.send_json(400, {"errors": [{"message": "Problems parsing JSON"}]})
        return
    if isinstance(payload, list):
        self.send_json(200, [_gql_run_one(item) for item in payload])
        return
    if not isinstance(payload, dict):
        self.send_json(400, {"errors": [{"message": "Problems parsing JSON"}]})
        return
    result = _gql_run_one(payload)
    if isinstance(result, list):
        self.send_json(200, result)
        return
    self.send_json(200, result)


Handler.handle_graphql = handle_graphql


# --------------------------------------------------------------------------
# Lifecycle

class Server(ThreadingHTTPServer):
    daemon_threads = True
    request_queue_size = 256
    allow_reuse_address = True

    def handle_error(self, request, client_address):
        pass


def main():
    if not ENV_URL:
        print("MAKEFUN_ENV_URL is not set", file=sys.stderr)
        return 1
    server = Server(("0.0.0.0", 0), Handler)
    port = server.server_address[1]
    print("[entry] listening on port %d" % port, flush=True)
    thread = threading.Thread(target=server.serve_forever, kwargs={"poll_interval": 0.05})
    thread.daemon = True
    thread.start()

    deadline = time.time() + 120
    while True:
        try:
            req = urllib.request.Request(
                ENV_URL + "/register",
                data=json.dumps({"port": port}).encode(),
                headers={"Content-Type": "application/json"},
                method="POST")
            with urllib.request.urlopen(req, timeout=10) as resp:
                resp.read()
            break
        except Exception:
            if time.time() > deadline:
                print("could not register with the env", file=sys.stderr)
                return 1
            time.sleep(0.25)
    print("[entry] registered; waiting for the env to say done", flush=True)

    while True:
        try:
            with urllib.request.urlopen(ENV_URL + "/done", timeout=10) as resp:
                data = json.loads(resp.read().decode("utf-8"))
            if isinstance(data, dict) and data.get("done"):
                break
        except Exception:
            pass
        time.sleep(0.2)

    server.shutdown()
    server.server_close()
    return 0


if __name__ == "__main__":
    sys.exit(main())
