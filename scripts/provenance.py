#!/usr/bin/env python3
"""scripts/provenance.py — which twin code each piece of our L code stands for.

Every L `FunDecl` under `ConAgua/**` (and, by choice, a Lean model of ours
that mirrors a twin function) carries a citation line in its declaration
block (doc comment, attributes, `--` comments directly above the `def`):

    /-- con-ron: ConRon/Arena/Core.lean:3685-3688 ConRon.Arena.flushCaches -/
    -- con-ron: ConRon/Arena/Core.lean:3685-3688 ConRon.Arena.flushCaches
    /-- con-leche: ConLeche/Frontend/Scan/Fast.lean:40-61 ConLeche.Frontend.strClose -/
    /-- con-ron: none — the memo library's own probe loop -/

i.e. the twin's file, the line range of the declaration's block (its doc
comment and attributes included, up to the next column-0 declaration), and its
fully qualified name; optionally followed by ` — <prose>`.  A bare
`con-ron: …` line inside a doc comment counts too, and an item may carry
several (an L function that merges several twin functions).  A `con-ron:`
line whose text starts with anything but `ConRon/`, `ConLeche/` or `none` is
prose, not a citation, and is not checked.

Paths and ranges are UPSTREAM's at the revisions in `vendor/UPSTREAM`: the
con-ron path is relative to its `proof/` directory (the same path as under
`vendor/con-ron/`), the con-leche path relative to its root (as under
`vendor/con-leche/`).  The text is read from the reference clones
`_tmp/ref/<repo>` with `git cat-file` (so `update --old` is a diff of two
upstream revisions, untouched by our patches); without them, `check` falls
back to `vendor/` (the patches do not move lines of cited code).

Modes (pure python, no build, a second or so):

  check            every FunDecl has a citation; every `@[l_impl T]` target T
                   has one naming T; every citation's range is exactly the
                   block of the named declaration at the current revision.
                   `CHANGED` markers are listed (the bump's work queue);
                   `--strict` fails on them too.
  update [--old R] after a bump: R is the OLD con-ron revision (default:
                   vendor/UPSTREAM at HEAD, when the working tree's differs);
                   the old con-leche revision is the one con-ron pins at R.
                   For every citation: the cited text at the old revision vs
                   the declaration's block at the new one.  Identical →
                   the range is rewritten (MOVED).  Equal up to comments →
                   rewritten, reported DOC.  Otherwise (CHANGED, GONE) a
                   marker line is inserted right below the citation:
                       -- con-ron: CHANGED since <old> — …, then delete this line
                   and the diff is printed.  Then the CALLEE pass: every
                   twin declaration whose code changed between the two
                   revisions and that no L code cites, reached from a cited
                   declaration through uncited ones (identifiers resolved
                   textually, namespaces and `open`s respected) at most
                   `--depth` calls down (default 1: the helpers an L function
                   inlines), puts a `CHANGED` marker on the citing items.  Structures
                   and inductives are reported (TYPE) but not followed: a
                   changed type is a question for the relations.  `--json F`
                   writes the findings for the dashboard; `--dry-run`
                   writes no marker.
  annotate         insert the citations `@[l_impl T]` implies, where missing
                   (the doc line for new code, mechanically).
  locate NAME…     print the citation body of each twin declaration.
  coverage         per twin file: definitions cited / all definitions.

Exit codes: 0 clean, 1 findings, 2 usage or IO error.
DESIGN.md, "Provenance: citations instead of fingerprints"; PLAN.md, "Bumping the twin".
"""

from __future__ import annotations

import argparse
import difflib
import json
import os
import re
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ROOTS = ["ConAgua"]
# Not scanned: throwaway experiments.
EXEMPT = ("ConAgua/Spike/",)

# Per upstream: path prefix in the upstream repository, the directories whose
# declarations are indexed (for name resolution and the callee pass), and the
# root namespace (a twin name `ConRon.…` belongs to con-ron).
UPSTREAMS = {
    "con-ron": {"prefix": "proof/", "dirs": ["ConRon/Arena"], "ns": "ConRon"},
    "con-leche": {"prefix": "", "dirs": ["ConLeche/Frontend", "ConLeche/Kernel",
                                          "ConLeche/Cached"], "ns": "ConLeche"},
}
COVERAGE_DIRS = {"con-ron": ["ConRon/Arena"], "con-leche": ["ConLeche/Frontend"]}


def rel(p):
    return os.path.relpath(p, REPO)


# ------------------------------------------------------------- upstream trees

def upstream_revs(text=None):
    if text is None:
        with open(os.path.join(REPO, "vendor/UPSTREAM"), encoding="utf-8") as f:
            text = f.read()
    revs = {}
    for line in text.splitlines():
        if line.startswith("#") or not line.strip():
            continue
        parts = line.split()
        revs[parts[0]] = parts[1]
    return revs


def ref_dir(repo):
    return os.path.join(REPO, "_tmp", "ref", repo)


def git(repo, *args):
    r = subprocess.run(["git", "-C", ref_dir(repo)] + list(args),
                       capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None


def has_rev(repo, rev):
    return os.path.isdir(ref_dir(repo)) and git(repo, "cat-file", "-e", rev + "^{commit}") is not None


class Tree:
    """One upstream at one revision (from the reference clone), or the
    vendored copy (`rev=None`)."""

    def __init__(self, repo, rev):
        self.repo, self.rev = repo, rev
        self.prefix = UPSTREAMS[repo]["prefix"]
        self.cache = {}
        self.proc = None
        self._index = None

    def _batch(self, spec):
        if self.proc is None:
            self.proc = subprocess.Popen(
                ["git", "-C", ref_dir(self.repo), "cat-file", "--batch"],
                stdin=subprocess.PIPE, stdout=subprocess.PIPE)
        self.proc.stdin.write((spec + "\n").encode())
        self.proc.stdin.flush()
        head = self.proc.stdout.readline().decode().split()
        if len(head) < 3 or head[1] != "blob":
            return None
        data = self.proc.stdout.read(int(head[2]))
        self.proc.stdout.read(1)
        return data.decode("utf-8")

    def read(self, path):
        if path not in self.cache:
            if self.rev is None:
                full = os.path.join(REPO, "vendor", self.repo, path)
                text = open(full, encoding="utf-8").read() if os.path.isfile(full) else None
            else:
                text = self._batch("%s:%s%s" % (self.rev, self.prefix, path))
            self.cache[path] = None if text is None else text.split("\n")
        return self.cache[path]

    def paths(self, dirs):
        out = []
        if self.rev is None:
            base = os.path.join(REPO, "vendor", self.repo)
            for d in dirs:
                for dp, dn, fns in os.walk(os.path.join(base, d)):
                    out += [os.path.relpath(os.path.join(dp, f), base)
                            for f in fns if f.endswith(".lean")]
        else:
            ls = git(self.repo, "ls-tree", "-r", "--name-only", self.rev, "--",
                     *[self.prefix + d for d in dirs]) or ""
            out = [p[len(self.prefix):] for p in ls.split() if p.endswith(".lean")]
        return sorted(out)

    def index(self):
        """{qualified name: [(path, 0-based line)]} over the indexed dirs."""
        if self._index is None:
            self._index = {}
            for p in self.paths(UPSTREAMS[self.repo]["dirs"]):
                for i, q, _kw in qualified_decls(self.read(p)):
                    self._index.setdefault(q, []).append((p, i))
        return self._index

    def label(self):
        return (self.rev or "vendor")[:8]


def current_trees(quiet=False):
    revs = upstream_revs()
    trees = {}
    for repo in UPSTREAMS:
        rev = revs[repo]
        if has_rev(repo, rev):
            trees[repo] = Tree(repo, rev)
        else:
            if not quiet:
                print("note: _tmp/ref/%s lacks %s; reading vendor/%s (patched) instead"
                      % (repo, rev[:8], repo), file=sys.stderr)
            trees[repo] = Tree(repo, None)
    return trees


# --------------------------------------------------------------- Lean parsing

DECL_KW = ("def|theorem|abbrev|inductive|structure|class|instance|opaque|axiom"
           "|lemma|example")
MODIFIERS = (r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+"
             r"|public\s+|meta\s+|scoped\s+|local\s+|nonrec\s+)*")
DECL_RE = re.compile(r"^(?:@\[[^\]]*\]\s*)*" + MODIFIERS + r"(?P<kw>" + DECL_KW + r")\s+"
                     r"(?P<name>[^\s:({\[⟨]+)")
STOPPER_RE = re.compile(
    r"^(?:/--|/-!|@\[|end\b|namespace\b|section\b|mutual\b|open\b|variable\b"
    r"|attribute\b|#|" + MODIFIERS + r"(?:" + DECL_KW + r")\s)")
SCOPE_RE = re.compile(
    r"^(?:(?:noncomputable|public|private)\s+)*(?P<kw>namespace|section)\b[ \t]*(?P<name>\S*)")
TYPE_KW = ("structure", "inductive", "class")
DEF_KW = ("def", "abbrev", "instance", "opaque")


def comment_lines(lines):
    """Indices of lines inside a `/- … -/` block comment (doc comments included)."""
    inside, depth = set(), 0
    for i, line in enumerate(lines):
        started = depth > 0
        j, n = 0, len(line)
        while j < n - 1:
            two = line[j:j + 2]
            if depth == 0 and two == "--":
                break
            if two == "/-":
                depth += 1
                j += 2
                continue
            if two == "-/":
                if depth:
                    depth -= 1
                j += 2
                continue
            j += 1
        if started or depth > 0:
            inside.add(i)
    return inside


def decl_at(lines, i, skip):
    if not lines[i] or lines[i][:1].isspace() or i in skip:
        return None
    m = DECL_RE.match(lines[i])
    return (m.group("kw"), m.group("name")) if m else None


_QD = {}


def qualified_decls(lines):
    """[(0-based line, qualified name, keyword)] for every column-0 declaration
    (memoized per list object: the trees keep their files' lines)."""
    key = id(lines)
    if key not in _QD:
        _QD[key] = (lines, _qualified_decls(lines))
    return _QD[key][1]


def _qualified_decls(lines):
    skip = comment_lines(lines)
    stack, out = [], []
    for i, line in enumerate(lines):
        if i in skip or not line or line[:1].isspace():
            continue
        m = SCOPE_RE.match(line)
        if m:
            stack.append((m.group("kw"), m.group("name")))
            continue
        if re.match(r"^mutual\b", line):
            stack.append(("mutual", ""))
            continue
        if re.match(r"^end\b", line):
            if stack:
                stack.pop()
            continue
        got = decl_at(lines, i, skip)
        if not got:
            continue
        nm = got[1]
        q = nm[len("_root_."):] if nm.startswith("_root_.") else \
            ".".join([s for k, s in stack if k == "namespace" and s] + [nm])
        out.append((i, q, got[0]))
    return out


def extend_block(lines, i):
    """1-based (a, b): the block of the declaration at 0-based line `i`, from
    its attributes and doc comment to the line before the next column-0 line
    that starts something new (trailing blanks dropped)."""
    a, j = i, i - 1
    while j >= 0:
        s = lines[j]
        if s.startswith("@[") or s.startswith("/--"):
            a, j = j, j - 1
            continue
        if s.rstrip().endswith("-/") and not s.startswith("/-!"):
            k = j
            while k >= 0 and not (lines[k].startswith("/--") or lines[k].startswith("/-!")):
                k -= 1
            if k >= 0 and lines[k].startswith("/--"):
                a, j = k, k - 1
                continue
        break
    b, k = i, i + 1
    while k < len(lines):
        s = lines[k]
        if s and not s[:1].isspace() and STOPPER_RE.match(s):
            break
        b, k = k, k + 1
    while b > i and lines[b].strip() == "":
        b -= 1
    return a + 1, b + 1


def strip_comments(lines):
    """A block's code: comments removed, strings kept, blank lines dropped."""
    text = "\n".join(lines)
    out, i, n, depth = [], 0, len(text), 0
    while i < n:
        two = text[i:i + 2]
        if depth:
            if two == "/-":
                depth, i = depth + 1, i + 2
            elif two == "-/":
                depth, i = depth - 1, i + 2
            else:
                if text[i] == "\n":
                    out.append("\n")
                i += 1
            continue
        if two == "/-":
            depth, i = 1, i + 2
            continue
        if two == "--":
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        if text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append(text[i:j + 1])
            i = j + 1
            continue
        out.append(text[i])
        i += 1
    return [l.rstrip() for l in "".join(out).split("\n") if l.strip()]


def names_compatible(q, cited):
    """Does the declaration with qualified name `q` answer to `cited`? Exact,
    `cited` a namespace-suffix of `q`, or `cited` a `where` child of `q`."""
    if q == cited:
        return True
    xs, ys = q.split("."), cited.split(".")
    if len(ys) < len(xs) and xs[-len(ys):] == ys:
        return True
    if len(xs) < len(ys) and ys[:len(xs)] == xs:
        return True
    return False


def locate(tree, name):
    """(path, a, b, qualified) of the twin declaration `name`, or None. A
    `where` child (`f.go`) resolves to its parent's block."""
    idx = tree.index()
    parts = name.split(".")
    for k in range(len(parts), 0, -1):
        hits = idx.get(".".join(parts[:k]))
        if hits:
            # a `private` declaration is not the one a qualified name means (CoreTest.lean's
            # private `internExprList` beside Intern.lean's): prefer a public hit
            pub = [(p, i) for p, i in hits
                   if not re.match(r"^(?:@\[[^\]]*\]\s*)*private\b", tree.read(p)[i])]
            p, i = (pub or hits)[0]
            a, b = extend_block(tree.read(p), i)
            return p, a, b, ".".join(parts[:k])
    return None


def decl_in_range(lines, a, b):
    """(qualified name, 0-based line) of the first declaration in a..b."""
    for i, q, _kw in qualified_decls(lines):
        if a - 1 <= i <= b - 1:
            return q, i
        if i > b - 1:
            break
    return None


def find_block(lines, block, near):
    if not block:
        return None
    n = len(block)
    hits = [i for i in range(len(lines) - n + 1)
            if lines[i].rstrip() == block[0]
            and [l.rstrip() for l in lines[i:i + n]] == block]
    if not hits:
        return None
    i = min(hits, key=lambda i: abs(i + 1 - near))
    return i + 1, i + n


def repo_of(name):
    for repo, u in UPSTREAMS.items():
        if name.split(".")[0] == u["ns"]:
            return repo
    return None


# ------------------------------------------------------------- our L sources

CITE_LINE_RE = re.compile(
    r"^(?P<indent>[ \t]*)(?P<head>(?:/--|--)?[ \t]*)con-(?P<repo>ron|leche):[ \t]*"
    r"(?P<body>.*?)(?P<tail>[ \t]*-/)?[ \t]*$")
CITE_BODY_RE = re.compile(
    r"^(?P<path>[^\s:]+\.lean):(?P<a>\d+)(?:-(?P<b>\d+))?\s+(?P<decl>\S+)"
    r"(?P<prose>\s+(?:—|--)(?:\s.*)?)?$")
MARKER_RE = re.compile(r"^\s*--\s*con-(?:ron|leche):\s*CHANGED\b")
L_IMPL_RE = re.compile(r"@\[([^\]]*)\]", re.S)
FUNDECL_RE = re.compile(r":\s*(?:L\.)?FunDecl\s*:=")


class Cite:
    def __init__(self, file, lineno, repo, path, a, b, decl, m):
        self.file, self.lineno, self.repo = file, lineno, repo
        self.path, self.a, self.b, self.decl = path, a, b, decl
        self.m = m  # the CITE_LINE_RE match (for re-rendering)
        self.prose = CITE_BODY_RE.match(m.group("body")).group("prose") or ""

    def body(self, path=None, a=None, b=None):
        a = self.a if a is None else a
        b = self.b if b is None else b
        return "%s:%s %s" % (path or self.path, a if a == b else "%d-%d" % (a, b), self.decl)

    def render(self, path, a, b):
        m = self.m
        return "%s%scon-%s: %s%s%s" % (m.group("indent"), m.group("head"), m.group("repo"),
                                      self.body(path, a, b), self.prose, m.group("tail") or "")

    def where(self):
        return "%s:%d" % (rel(self.file), self.lineno)


class Item:
    def __init__(self, file, lineno, kw, name, is_fun, l_impl, cites, nones, bad):
        self.file, self.lineno, self.kw, self.name = file, lineno, kw, name
        self.is_fun, self.l_impl, self.cites, self.nones, self.bad = is_fun, l_impl, cites, nones, bad

    def where(self):
        return "%s:%d" % (rel(self.file), self.lineno)


def our_files():
    out = []
    for r in ROOTS:
        for dp, dn, fns in os.walk(os.path.join(REPO, r)):
            dn.sort()
            for f in sorted(fns):
                p = os.path.join(dp, f)
                if f.endswith(".lean") and not rel(p).startswith(EXEMPT):
                    out.append(p)
    return out


def block_start(lines, i):
    """0-based first line of the declaration block above line `i`: attributes
    (multi-line ones too), doc comment, `--` lines; no blank lines."""
    j = i - 1
    while j >= 0:
        s = lines[j]
        if s.startswith("@[") or s.lstrip().startswith("--"):
            j -= 1
            continue
        if s and s[:1].isspace():  # an attribute's continuation line?
            k = j
            while k >= 0 and lines[k][:1].isspace() and lines[k].strip():
                k -= 1
            if k >= 0 and lines[k].startswith("@["):
                j = k - 1
                continue
            break
        if s.rstrip().endswith("-/"):
            k = j
            while k >= 0 and not lines[k].startswith("/-"):
                k -= 1
            if k >= 0 and lines[k].startswith("/--"):
                j = k - 1
                continue
        break
    return j + 1


def is_fundecl(lines, i):
    """Is the declaration at line `i` of type `FunDecl` (`… : FunDecl :=`)?
    Its header runs to the first `:=`; a pattern-matching `|` or a blank
    line first means it is not."""
    head = []
    for j in range(i, min(i + 15, len(lines))):
        s = lines[j]
        if j > i and (not s.strip() or s.lstrip().startswith("|")):
            return False
        head.append(s)
        k = s.find(":=")
        if k >= 0:
            return bool(FUNDECL_RE.search("\n".join(head[:-1] + [s[:k + 2]])))
    return False


def scan(path):
    """(items, markers) of one of our files."""
    with open(path, encoding="utf-8") as f:
        lines = f.read().split("\n")
    skip = comment_lines(lines)
    items, markers = [], []
    for i, line in enumerate(lines):
        if MARKER_RE.match(line):
            markers.append((path, i + 1, line.strip()))
    for i in range(len(lines)):
        got = decl_at(lines, i, skip)
        if not got:
            continue
        kw, name = got
        s = block_start(lines, i)
        is_fun = kw in ("def", "abbrev") and is_fundecl(lines, i)
        attrs = "\n".join(lines[s:i + 1])
        l_impl = []
        for a in L_IMPL_RE.findall(attrs):
            for part in a.split(","):
                ws = part.split()
                if ws and ws[0] == "l_impl":
                    l_impl += ws[1:]
        cites, nones, bad = [], [], []
        for j in range(s, i):
            m = CITE_LINE_RE.match(lines[j])
            if not m or MARKER_RE.match(lines[j]):
                continue
            body, repo = m.group("body"), "con-" + m.group("repo")
            if not re.match(r"^(?:none\b|Con(?:Ron|Leche)/)", body):
                continue  # prose that mentions the twin (`con-leche: \`Core.lean:1-2\` f`)
            if re.match(r"^none\b", body):
                nones.append(j + 1)
                continue
            c = CITE_BODY_RE.match(body)
            if not c:
                bad.append((j + 1, body))
                continue
            cites.append(Cite(path, j + 1, repo, c.group("path"), int(c.group("a")),
                              int(c.group("b") or c.group("a")), c.group("decl"), m))
        items.append(Item(path, i + 1, kw, name, is_fun, l_impl, cites, nones, bad))
    return items, markers


def collect():
    items, markers = [], []
    for p in our_files():
        it, mk = scan(p)
        items += it
        markers += mk
    return items, markers


def item_label(it):
    return "%s.%s" % (os.path.basename(it.file)[:-5], it.name)


# ---------------------------------------------------------------------- check

def verify_cite(trees, c):
    """None if the citation is exact at the current revision, else a finding."""
    tree = trees[c.repo]
    lines = tree.read(c.path)
    if lines is None:
        return "MISSING %s — %s not in %s at %s" % (c.where(), c.path, c.repo, tree.label())
    if not (1 <= c.a <= c.b <= len(lines)):
        return "RANGE %s — %s:%d-%d outside the file (%d lines)" % (
            c.where(), c.path, c.a, c.b, len(lines))
    got = decl_in_range(lines, c.a, c.b)
    if got is None or not names_compatible(got[0], c.decl):
        return "NAME %s — %s:%d-%d declares `%s`, cited as `%s`" % (
            c.where(), c.path, c.a, c.b, got[0] if got else "nothing", c.decl)
    a, b = extend_block(lines, got[1])
    if (a, b) != (c.a, c.b):
        return "RANGE %s — `%s`'s block is %s:%d-%d, cited as %d-%d" % (
            c.where(), c.decl, c.path, a, b, c.a, c.b)
    return None


def cites_target(trees, it, t):
    for c in it.cites:
        if c.decl == t:
            return True
        lines = trees[c.repo].read(c.path)
        got = lines and decl_in_range(lines, c.a, c.b)
        if got and (got[0] == t or t.startswith(got[0] + ".")) and names_compatible(got[0], c.decl):
            return True
    return False


def cmd_check(args):
    trees = current_trees()
    items, markers = collect()
    n = 0

    def out(s):
        nonlocal n
        n += 1
        print(s)

    for path, ln, text in markers:
        if args.strict:
            out("UNRECONCILED %s:%d — %s" % (rel(path), ln, text))
        else:
            print("queue: %s:%d — %s" % (rel(path), ln, text))
    for it in items:
        for ln, body in it.bad:
            out("MALFORMED %s:%d — %s" % (rel(it.file), ln, body))
        for c in it.cites:
            f = verify_cite(trees, c)
            if f:
                out(f)
        if it.is_fun and not it.cites and not it.nones and not it.bad:
            out("UNCITED %s — FunDecl `%s` has no `con-ron:`/`con-leche:` line%s" % (
                it.where(), it.name,
                " (run `scripts/provenance.py annotate`)" if it.l_impl else ""))
        elif it.l_impl:
            for t in it.l_impl:
                if not cites_target(trees, it, t):
                    out("LIMPL %s — `@[l_impl %s]` but no citation of it (run "
                        "`scripts/provenance.py annotate`)" % (it.where(), t))
    if n:
        print("%d finding(s)." % n)
        return 1
    funs = [it for it in items if it.is_fun]
    print("provenance: %d FunDecl(s) (%d cite twin code, %d `none`), %d other cited "
          "declaration(s), %d citation(s); all exact at con-ron %s, con-leche %s%s." % (
              len(funs), sum(1 for it in funs if it.cites), sum(1 for it in funs if not it.cites),
              sum(1 for it in items if it.cites and not it.is_fun),
              sum(len(it.cites) for it in items),
              trees["con-ron"].label(), trees["con-leche"].label(),
              "; %d CHANGED marker(s) queued" % len(markers) if markers else ""))
    return 0


# ------------------------------------------------------------------- annotate

def cmd_annotate(args):
    trees = current_trees()
    items, _ = collect()
    edits, n, missing = {}, 0, 0
    for it in items:
        if not it.l_impl:
            continue
        new = []
        for t in it.l_impl:
            if cites_target(trees, it, t):
                continue
            repo = repo_of(t)
            loc = locate(trees[repo], t) if repo else None
            if loc is None:
                print("NOTFOUND %s — `@[l_impl %s]`: no such twin declaration" % (it.where(), t))
                missing += 1
                continue
            p, a, b, _q = loc
            new.append("%s: %s:%d-%d %s" % (repo, p, a, b, t))
        if new:
            edits.setdefault(it.file, []).append((it.lineno, new))
            n += len(new)
    for path, es in edits.items():
        with open(path, encoding="utf-8") as f:
            lines = f.read().split("\n")
        for lineno, new in sorted(es, key=lambda e: -e[0]):
            i = lineno - 1
            s = block_start(lines, i)
            has_doc = any(lines[j].startswith("/--") for j in range(s, i))
            if has_doc:
                # after the doc comment, before the attributes: `--` lines
                k = s
                while k < i and not lines[k].rstrip().endswith("-/"):
                    k += 1
                ins = ["-- " + x for x in new]
                lines[k + 1:k + 1] = ins
            else:
                ins = ["/-- " + new[0]] + new[1:]
                ins[-1] += " -/"
                lines[s:s] = ins
        with open(path, "w", encoding="utf-8") as f:
            f.write("\n".join(lines))
    print("annotate: %d citation(s) inserted in %d file(s)%s." % (
        n, len(edits), ", %d target(s) not found" % missing if missing else ""))
    return 1 if missing else 0


def cmd_locate(args):
    trees = current_trees()
    rc = 0
    for name in args.names:
        repo = repo_of(name)
        loc = locate(trees[repo], name) if repo else None
        if loc is None:
            print("NOTFOUND %s" % name)
            rc = 1
        else:
            print("%s: %s:%d-%d %s" % (repo, loc[0], loc[1], loc[2], name))
    return rc


# --------------------------------------------------------------------- update

def old_revs(args):
    cur = upstream_revs()
    if args.old:
        cr = git("con-ron", "rev-parse", "--verify", args.old + "^{commit}")
        if cr is None:
            sys.exit("unknown con-ron revision %s (in _tmp/ref/con-ron)" % args.old)
        cr = cr.strip()
        man = git("con-ron", "show", cr + ":proof/lake-manifest.json")
        cl = next(p["rev"] for p in json.loads(man)["packages"] if "con-leche" in p["name"])
        return {"con-ron": cr, "con-leche": args.old_leche or cl}
    r = subprocess.run(["git", "-C", REPO, "show", "HEAD:vendor/UPSTREAM"],
                       capture_output=True, text=True)
    old = upstream_revs(r.stdout) if r.returncode == 0 else {}
    if not old or old == cur:
        sys.exit("vendor/UPSTREAM matches HEAD's; pass --old <con-ron rev>")
    return old


def changed_decls(old, new):
    """{qualified name: kind} of the twin declarations whose code changed
    (comment-stripped block differs) or that are new, over the indexed dirs."""
    out = {}
    for repo in UPSTREAMS:
        o, n = old[repo], new[repo]
        if o.rev == n.rev:
            continue
        dirs = [UPSTREAMS[repo]["prefix"] + d for d in UPSTREAMS[repo]["dirs"]]
        names = (git(repo, "diff", "--name-only", o.rev, n.rev, "--", *dirs) or "").split()
        files = [p[len(UPSTREAMS[repo]["prefix"]):] for p in names if p.endswith(".lean")]
        for p in files:
            nl, ol = n.read(p), o.read(p)
            olds = {}
            if ol:
                for i, q, kw in qualified_decls(ol):
                    a, b = extend_block(ol, i)
                    olds[q] = strip_comments(ol[a - 1:b])
            if nl:
                for i, q, kw in qualified_decls(nl):
                    a, b = extend_block(nl, i)
                    if olds.get(q) != strip_comments(nl[a - 1:b]):
                        out[(repo, q)] = (kw, p, q not in olds)
    return out


IDENT_RE = re.compile(r"(?<![\w.'?!])[A-Za-z_][\w'!?]*(?:\.[A-Za-z_][\w'!?]*)*")


class Calls:
    """Textual call graph over one tree's indexed declarations."""

    def __init__(self, tree):
        self.tree = tree
        self.idx = tree.index()
        self.memo = {}
        self.opens = {}

    def file_opens(self, p):
        if p not in self.opens:
            self.opens[p] = [w for l in self.tree.read(p) if l.startswith("open ")
                             for w in l.split()[1:] if w[:1].isupper()]
        return self.opens[p]

    def resolve(self, ns, opens, tok):
        parts = tok.split(".")
        for k in range(len(parts), 0, -1):
            t = ".".join(parts[:k])
            for pre in [ns[:j] for j in range(len(ns), -1, -1)] + [o.split(".") for o in opens]:
                q = ".".join(pre + [t])
                if q in self.idx:
                    return q
        return None

    def callees(self, q):
        if q not in self.memo:
            p, i = self.idx[q][0]
            lines = self.tree.read(p)
            a, b = extend_block(lines, i)
            code = "\n".join(strip_comments(lines[a - 1:b]))
            code = re.sub(r'"(?:[^"\\]|\\.)*"', '""', code)
            ns = q.split(".")[:-1]
            opens = self.file_opens(p)
            out = set()
            for tok in set(IDENT_RE.findall(code)):
                r = self.resolve(ns, opens, tok)
                if r and r != q:
                    out.add(r)
            self.memo[q] = out
        return self.memo[q]


def marker_line(indent, repo, old, what):
    return "%s-- %s: CHANGED since %s — %s; re-check the L code and its proofs, then delete this line" % (
        indent, repo, old[:8], what)


def cmd_update(args):
    olds = old_revs(args)
    new = current_trees()
    for repo in UPSTREAMS:
        if new[repo].rev is None:
            sys.exit("update needs _tmp/ref/%s at the current revision" % repo)
        if not has_rev(repo, olds[repo]):
            sys.exit("_tmp/ref/%s lacks the old revision %s" % (repo, olds[repo][:8]))
    old = {repo: Tree(repo, olds[repo]) for repo in UPSTREAMS}
    items, markers = collect()
    for path, ln, text in markers:
        print("UNRECONCILED %s:%d — %s" % (rel(path), ln, text))
    rewrites, inserts = {}, {}
    counts = {"moved": 0, "doc": 0, "changed": 0, "gone": 0, "callee": 0}
    cited = {}  # (repo, qualified) -> [items]
    records = []

    def record(kind, c, it, note=""):
        records.append({"kind": kind, "where": c.where(), "item": item_label(it),
                        "cites": c.body(), "note": note})
    for it in items:
        for c in it.cites:
            nt, ot = new[c.repo], old[c.repo]
            ol = ot.read(c.path)
            old_text = [l.rstrip() for l in ol[c.a - 1:c.b]] if ol and c.b <= len(ol) else None
            # the old block: the cited range if it declares the name, else by name
            # (a second run, or citations written at the new revision)
            got = ol and decl_in_range(ol, c.a, c.b)
            if not (got and names_compatible(got[0], c.decl)):
                lo = locate(ot, c.decl)
                old_text = None
                if lo:
                    ol2 = ot.read(lo[0])
                    old_text = [l.rstrip() for l in ol2[lo[1] - 1:lo[2]]]
            nl = nt.read(c.path)
            loc = None
            if nl and old_text:
                fb = find_block(nl, old_text, c.a)
                if fb:
                    loc = (c.path, fb[0], fb[1])
            if loc is None:
                lo = locate(nt, c.decl)
                if lo:
                    loc = lo[:3]
            mi = c.m.group("indent")
            if loc is None:
                print("GONE %s — `%s` not found at %s → re-port %s" % (
                    c.where(), c.decl, nt.label(), item_label(it)))
                inserts.setdefault(c.file, []).append(
                    (c.lineno, marker_line(mi, c.repo, ot.rev, "`%s` is gone upstream" % c.decl)))
                counts["gone"] += 1
                record("gone", c, it)
                continue
            p, a, b = loc
            nlines = nt.read(p)
            new_text = [l.rstrip() for l in nlines[a - 1:b]]
            q = decl_in_range(nlines, a, b)
            if q:
                cited.setdefault((c.repo, q[0]), []).append(it)
            if (p, a, b) != (c.path, c.a, c.b):
                rewrites.setdefault(c.file, {})[c.lineno] = c.render(p, a, b)
            if old_text == new_text:
                if (p, a, b) != (c.path, c.a, c.b):
                    print("MOVED %s — %s → %s" % (c.where(), c.body(), c.body(p, a, b)))
                    counts["moved"] += 1
                continue
            if old_text is not None and strip_comments(old_text) == strip_comments(new_text):
                print("DOC %s — %s: comments only" % (c.where(), c.body(p, a, b)))
                counts["doc"] += 1
                continue
            print("CHANGED %s — %s → re-check %s" % (c.where(), c.body(p, a, b), item_label(it)))
            for dl in difflib.unified_diff(old_text or [], new_text,
                                           fromfile="%s@%s" % (c.path, ot.label()),
                                           tofile="%s@%s" % (p, nt.label()), lineterm=""):
                print("    " + dl)
            inserts.setdefault(c.file, []).append(
                (c.lineno, marker_line(mi, c.repo, ot.rev, "`%s` changed" % c.decl)))
            counts["changed"] += 1
            record("changed", c, it)

    # the callee pass
    changed = changed_decls(old, new)
    types = sorted((r, q) for (r, q), (kw, _p, _a) in changed.items() if kw in TYPE_KW)
    for r, q in types:
        users = sorted({item_label(it) for it in cited.get((r, q), [])})
        print("TYPE %s %s changed (%s)%s — check the relations that mention it" % (
            r, q, changed[(r, q)][1], "; cited by " + ", ".join(users) if users else ""))
    # helpers below a cited declaration, `--depth` calls deep, through uncited ones
    for repo in UPSTREAMS:
        calls = Calls(new[repo])
        for (r, q0), its in sorted(cited.items()):
            if r != repo or q0 not in calls.idx:
                continue
            frontier, seen, hits = [(q0, [q0])], {q0}, []
            for _ in range(args.depth):
                nxt = []
                for q, path in frontier:
                    for d in sorted(calls.callees(q)):
                        if d in seen or (repo, d) in cited:
                            continue
                        seen.add(d)
                        ch = changed.get((repo, d))
                        if ch and ch[0] in TYPE_KW:
                            continue
                        if ch:
                            hits.append((d, path + [d]))
                        nxt.append((d, path + [d]))
                frontier = nxt
            if not hits:
                continue
            for it in its:
                c = next(c for c in it.cites if c.repo == repo)
                print("CALLEE %s — %s: below `%s`, changed: %s" % (
                    c.where(), item_label(it), q0,
                    "; ".join("`%s` (%s, via %s)" % (d, changed[(repo, d)][1], " → ".join(pth[1:-1]) or "direct")
                              for d, pth in hits)))
                inserts.setdefault(c.file, []).append(
                    (c.lineno, marker_line(c.m.group("indent"), repo, old[repo].rev,
                                           "below `%s`, %s changed" % (
                                               q0, ", ".join("`%s`" % d for d, _ in hits)))))
                record("callee", c, it, ", ".join(d for d, _ in hits))
                counts["callee"] += 1

    if args.json:
        with open(args.json, "w", encoding="utf-8") as f:
            json.dump({"old": {r: t.rev for r, t in old.items()},
                       "new": {r: t.rev for r, t in new.items()},
                       "counts": counts, "findings": records,
                       "types": [{"repo": r, "decl": q, "file": changed[(r, q)][1]} for r, q in types]},
                      f, indent=1)
            f.write("\n")

    if not args.dry_run:
        for path in set(rewrites) | set(inserts):
            with open(path, encoding="utf-8") as f:
                lines = f.read().split("\n")
            for ln, text in rewrites.get(path, {}).items():
                lines[ln - 1] = text
            for ln, text in sorted(set(inserts.get(path, [])), key=lambda e: -e[0]):
                if not any(l.strip() == text.strip() for l in lines[ln:ln + 8]):
                    lines.insert(ln, text)
            with open(path, "w", encoding="utf-8") as f:
                f.write("\n".join(lines))
    print("update %s → %s: %d moved, %d comment-only, %d changed, %d gone, %d callee "
          "finding(s)%s." % (old["con-ron"].label(), new["con-ron"].label(), counts["moved"],
                             counts["doc"], counts["changed"], counts["gone"], counts["callee"],
                             " (dry run, nothing written)" if args.dry_run else
                             "; markers inserted: reconcile, then delete them"))
    return 1 if counts["changed"] + counts["gone"] + counts["callee"] else 0


# ------------------------------------------------------------------- coverage

def cmd_coverage(args):
    trees = current_trees(quiet=True)
    items, _ = collect()
    cited = set()
    for it in items:
        for c in it.cites:
            lines = trees[c.repo].read(c.path)
            got = lines and decl_in_range(lines, c.a, c.b)
            if got:
                cited.add((c.repo, got[0]))
    for repo, dirs in COVERAGE_DIRS.items():
        tot = cov = 0
        print("%s (%s):" % (repo, trees[repo].label()))
        for p in trees[repo].paths(dirs):
            ds = [q for _i, q, kw in qualified_decls(trees[repo].read(p)) if kw in DEF_KW]
            k = sum(1 for q in ds if (repo, q) in cited)
            tot, cov = tot + len(ds), cov + k
            if ds and (k or args.all):
                print("  %4d / %4d  %s" % (k, len(ds), p))
        print("  %4d / %4d  total definitions cited" % (cov, tot))
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    ck = sub.add_parser("check")
    ck.add_argument("--strict", action="store_true",
                    help="also fail on CHANGED markers (they are only listed otherwise)")
    sub.add_parser("annotate")
    u = sub.add_parser("update")
    u.add_argument("--old", help="the old con-ron revision")
    u.add_argument("--old-leche", help="the old con-leche revision (default: con-ron's pin at --old)")
    u.add_argument("--dry-run", action="store_true")
    u.add_argument("--depth", type=int, default=1,
                   help="how many calls deep the callee pass looks below a cited declaration (1)")
    u.add_argument("--json", metavar="FILE", help="also write the findings as JSON")
    lo = sub.add_parser("locate")
    lo.add_argument("names", nargs="+")
    cv = sub.add_parser("coverage")
    cv.add_argument("--all", action="store_true", help="also list files with nothing cited")
    args = ap.parse_args()
    return {"check": cmd_check, "annotate": cmd_annotate, "update": cmd_update,
            "locate": cmd_locate, "coverage": cmd_coverage}[args.cmd](args)


if __name__ == "__main__":
    sys.exit(main())
