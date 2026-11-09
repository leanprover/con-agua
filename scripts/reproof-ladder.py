#!/usr/bin/env python3
"""The re-proof ladder: after a twin sync has changed the statements, re-prove what the base's
proofs still prove, mechanically (PLAN.md, "Bumping the twin"; lane journal docs/design/syncproc.md).

    scripts/reproof-ladder.py [options] [FILE...]

For every theorem of the given files that fails to elaborate or uses `sorry` (the *failing* ones),
it tries, in order, and keeps the first candidate that elaborates:
  (i)   master    the base revision's proof text verbatim under the new statement;
  (ii)  codemod   the same after the sync's regex rules (`[codemod]` of the rules file);
  (iii) vocab     the same with the sync's vocabulary added (`[vocab NAME]` sections, tried in
                  order; or a hook module, `--vocab-hook`, see VOCAB HOOK below);
  (iv)  otherwise the theorem is left at `sorry` (with --write) and gets a ticket line: file,
        declaration, the last rung tried, the first error.
A base declaration is found by qualified name: in the same file, else anywhere in the base tree
(files that moved or split), else through a `rename OLD NEW` line of the rules file, else by its last
name component if that is unique. Only the proof (the text after the statement's `:=`) is taken
from the base; the statement is the current one.

It only ever proposes text that elaborates: each rung elaborates the whole module with the candidates
in place (a copy under the run directory: the worktree is not touched), a theorem counts as closed
when no error and no `sorry` warning falls inside it, and with --write the final text (closed
theorems at their candidate, the rest at `sorry`) is elaborated once more before it replaces the
file; a theorem that breaks there goes back to `sorry`, and a file that still does not check is left
as it was.

Files: the FILE arguments, else `--changed` (default): the .lean files under ConAgua/ that differ
from the base. A file whose imports are not built (a partial tree) is reported as `blocked` and
skipped; build them (`scripts/lake build <module>`) and run the ladder again: it only looks at what
fails now, so reruns are cheap and idempotent.

Options:
  --base REV        where the old proofs come from (default: merge-base of HEAD and master)
  --rules FILE      the sync's rules, scripts/sync-rules/<sync>.txt (format: class Rules below)
  --steps LIST      rungs to run, a subset of master,codemod,vocab (default: all three)
  --failing MODE    elab (default): elaborate each file first, failing = an error or a `sorry` warning
                    inside the theorem; sorry: only theorems whose proof text contains `sorry`
                    (no first elaboration; for a tree that builds)
  --decls FILE      replay mode: exactly the theorems listed (`path name` per line, or
                    `path:name1,name2`), whatever state they are in (to measure the ladder on a
                    finished sync: put back the base's proof and see which rung closes it)
  --write           write the verified result into the worktree (default: report only); a
                    failing proof that no rung closes becomes `sorry` (the base's text stays in
                    git, the current one in the ticket's file at HEAD)
  --out DIR         report directory (default _tmp/ladder/<worktree name>)
  --jobs N          lean processes at a time (default 2); --threads N each (LEAN_NUM_THREADS, 1)
  --timeout S       per lean run (default 900); --mem-gb G per lean process tree (default 15)
  --worktree DIR    the checkout to work on (default: the current one)

Report: <out>/report.md (closed per rung, the remaining list by file, blocked files), report.json,
tickets.tsv (file, line, declaration, rung, first error), and the candidate texts of the closed
theorems in closed/ (also without --write, to apply by hand).

VOCAB HOOK: `--vocab-hook FILE.py` (or `vocab_hook FILE.py` in the rules file) is a Python file that
defines `candidates(proof, ctx) -> [(label, text), ...]`: the vocabulary rung's variants of a codemod
proof text, tried in order. `ctx` has `file` (the path), `name`, `stmt` (the new statement text),
`text` (the whole current file) and `rules`. It replaces the `[vocab]` sections.
"""
import argparse
import collections
import concurrent.futures
import fcntl
import importlib.util
import json
import os
import re
import signal
import subprocess
import sys
import threading
import time
import tomllib

# ---------------------------------------------------------------------------------------------------
# Lean source structure: top-level items, namespaces, the statement/proof split


DECL_KW = ("theorem", "lemma", "def", "abbrev", "instance", "example", "structure", "inductive",
           "class", "opaque", "axiom", "l_model", "l_spec", "elab", "macro", "syntax")
PROOF_KW = ("theorem", "lemma")
MODIFIERS = ("private", "protected", "noncomputable", "public", "nonrec", "unsafe", "partial",
             "meta", "scoped", "local")
HEAD = re.compile(r"^(?:@\[[^\]]*(?:\][^\]]*)*?\]\s*)*((?:(?:%s)\s+)*)(%s)\b\s*([^\s:({\[⦃]+)?"
                  % ("|".join(MODIFIERS), "|".join(DECL_KW)))
CONT = ("|", ")", "]", "}", "⟩", "termination_by", "decreasing_by", "where", "deriving", "·")
PREFIX_IN = re.compile(r"^(set_option|include|omit|open|variable)\b.*\bin\s*$")


def lex(text):
    """Per character: is it code (not in a comment or string)? And the bracket depth before it.
    Returns (code mask, depth, line start offsets, offsets where an outermost comment starts)."""
    n = len(text)
    code = [True] * n
    depth = [0] * n
    cstart = set()  # offsets where an outermost comment begins
    i, d, cdepth = 0, 0, 0
    while i < n:
        c = text[i]
        if cdepth:
            if text.startswith("/-", i):
                cdepth += 1; code[i] = code[i + 1] = False; i += 2; continue
            if text.startswith("-/", i):
                cdepth -= 1; code[i] = code[i + 1] = False; i += 2; continue
            code[i] = False; depth[i] = d; i += 1; continue
        if text.startswith("/-", i):
            cstart.add(i)
            cdepth = 1; code[i] = code[i + 1] = False; depth[i] = depth[i + 1] = d; i += 2; continue
        if text.startswith("--", i):
            cstart.add(i)
            j = text.find("\n", i)
            j = n if j < 0 else j
            for k in range(i, j):
                code[k] = False; depth[k] = d
            i = j; continue
        if c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            for k in range(i, min(j + 1, n)):
                code[k] = False; depth[k] = d
            i = j + 1; continue
        depth[i] = d
        if c in "([{⟨⦃":
            d += 1
        elif c in ")]}⟩⦄":
            d = max(0, d - 1)
        i += 1
    starts = [0] + [m.end() for m in re.finditer("\n", text)]
    return code, depth, starts, cstart


class Decl:
    __slots__ = ("name", "kind", "l0", "l1", "a", "b", "assign", "ns")

    def __repr__(self):
        return f"Decl({self.kind} {self.name} {self.l0 + 1}-{self.l1})"


def parse(text):
    """Top-level items of a Lean file. Each Decl: qualified `name`, `kind`, lines [l0, l1) (0-based,
    trailing blank lines excluded), character span [a, b), `assign` = offset of the statement's
    `:=` at bracket depth 0, or of the line of the first `|` arm of an equation-style body (None if
    there is neither)."""
    code, depth, starts, cstart = lex(text)
    lines = text.split("\n")
    nl = len(lines)
    # boundaries: lines that start a new top-level item (code or a comment, at column 0, outside
    # every bracket and comment)
    bounds = []
    for li in range(nl):
        if not lines[li] or lines[li][0].isspace():
            continue
        o = starts[li]
        if depth[o]:
            continue
        if code[o] and not lines[li].startswith(CONT):
            bounds.append(li)
        elif o in cstart:
            # a comment at column 0 is an item unless the code after it is indented (a comment
            # line inside a proof)
            j = o
            while j < len(text) and (not code[j] or text[j].isspace()):
                j += 1
            ls = text.rfind("\n", 0, j) + 1
            if j >= len(text) or j == ls:
                bounds.append(li)
    out, ns = [], []
    k = 0
    while k < len(bounds):
        li = bounds[k]
        # prefixes: doc comments, attribute-only lines, `... in` lines attach to the next item
        j = k
        while j + 1 < len(bounds):
            l = lines[bounds[j]]
            if l.startswith("/--") or PREFIX_IN.match(l) or re.match(r"^@\[[^\]]*\]\s*$", l):
                j += 1
                continue
            break
        hl = bounds[j]
        end = bounds[j + 1] if j + 1 < len(bounds) else nl
        e = end
        while e > hl + 1 and not lines[e - 1].strip():
            e -= 1
        head = lines[hl]
        # an attribute line followed by the declaration on the next line
        m = HEAD.match(head)
        w = head.split()
        kw0 = w[0] if w else ""
        if kw0 in ("namespace",) and len(w) > 1:
            ns.append(w[1])
        elif kw0 in ("section", "mutual") or head.startswith(("public section", "noncomputable section",
                                                              "@[expose] public section")):
            ns.append(None)
        elif kw0 == "end":
            if ns:
                ns.pop()
        elif m:
            d = Decl()
            d.kind = m.group(2)
            raw = m.group(3) or ""
            if raw.startswith("_root_."):
                qual = raw[len("_root_."):]
            else:
                qual = ".".join([x for x in ns if x] + ([raw] if raw else []))
            d.name = qual if raw else None
            d.ns = ".".join(x for x in ns if x)
            d.l0, d.l1 = li, e
            d.a = starts[li]
            d.b = starts[e - 1] + len(lines[e - 1])
            d.assign = None
            ho = starts[hl] + m.end(2)
            for o in range(ho, d.b - 1):
                if code[o] and depth[o] == 0 and text[o] == ":" and text[o + 1] == "=":
                    d.assign = o
                    break
                if code[o] and depth[o] == 0 and text[o] == "|" and text[o - 1] in "\n ":
                    ls = text.rfind("\n", 0, o) + 1
                    if not text[ls:o].strip():
                        d.assign = ls  # equation style: the arms are the proof
                        break
            out.append(d)
        k = j + 1
    return out


def proof_text(text, d):
    return None if d.assign is None else text[d.assign:d.b]


def stmt_text(text, d):
    return text[d.a:d.assign]


SORRY = re.compile(r"\bsorry\b")


def has_sorry_token(text, d):
    if d.assign is None:
        return False
    code = LEXCACHE.get(text)[0]
    seg = text[d.assign:d.b]
    for m in SORRY.finditer(seg):
        if code[d.assign + m.start()]:
            return True
    return False


class _LexCache(threading.local):
    """The last text lexed, per thread."""

    def __init__(self):
        self.k, self.v = None, None

    def get(self, text):
        if self.k is not text:
            self.k, self.v = text, lex(text)
        return self.v


LEXCACHE = _LexCache()


def keyed(decls):
    """name -> Decl for named declarations; a name that occurs twice gets `#2`, `#3`."""
    seen = collections.Counter()
    out = {}
    for d in decls:
        if not d.name:
            continue
        seen[d.name] += 1
        out[d.name if seen[d.name] == 1 else f"{d.name}#{seen[d.name]}"] = d
    return out


# ---------------------------------------------------------------------------------------------------
# The rules file


class Rules:
    """Rules file, one rule per line, `#` comments:
        [codemod]                         rules of rung (ii), applied to the base proof in order
        sub REGEX ==> REPLACEMENT          Python `re.sub` (multiline mode); either side may be
                                           written in double quotes (taken literally, no escapes
                                           of their own) to keep spaces at its ends
        [vocab NAME]                       a variant of rung (iii), applied after the codemod;
                                           several sections are tried in order
        use NAME                           (in a vocab section) the rules of an earlier section first
        sub REGEX ==> REPLACEMENT          as above
        sub-if IDENT REGEX ==> REPL        only if IDENT occurs in the file being re-proved
        [names]
        rename OLD NEW                     the base declaration OLD is the current NEW
        vocab_hook FILE.py                 see VOCAB HOOK in the script's docstring
    """

    def __init__(self, path=None):
        self.codemod, self.vocab, self.renames, self.hook = [], collections.OrderedDict(), {}, None
        if not path:
            return
        sec, cur = None, None
        for n, raw in enumerate(open(path), 1):
            line = raw.rstrip("\n")
            if not line.strip() or line.lstrip().startswith("#"):
                continue
            s = line.strip()
            m = re.match(r"^\[(codemod|names|vocab)(?:\s+(\S+))?\]$", s)
            if m:
                sec = m.group(1)
                if sec == "vocab":
                    cur = self.vocab.setdefault(m.group(2) or f"v{len(self.vocab) + 1}", [])
                continue
            try:
                if s.startswith("rename "):
                    _, old, new = s.split()
                    self.renames[new] = old
                elif s.startswith("vocab_hook "):
                    self.hook = os.path.join(os.path.dirname(os.path.abspath(path)), s.split(None, 1)[1])
                elif s.startswith("use ") and sec == "vocab":
                    cur.extend(self.vocab[s.split()[1]])
                elif s.startswith(("sub ", "sub-if ")):
                    guard = None
                    body = s[4:] if s.startswith("sub ") else s[7:]
                    if s.startswith("sub-if "):
                        guard, body = body.split(None, 1)
                    pat, rep = body.split(" ==> ", 1) if " ==> " in body else (body.rstrip(" =>"), "")
                    rule = (guard, re.compile(_unq(pat.strip()), re.M), _unq(rep.strip()))
                    (self.codemod if sec in (None, "codemod") else cur).append(rule)
                else:
                    raise ValueError("unknown rule")
            except (ValueError, KeyError, re.error) as e:
                sys.exit(f"{path}:{n}: {e}: {line}")

    @staticmethod
    def apply(rules, txt, scope):
        for guard, pat, rep in rules:
            if guard is None or guard in scope:
                txt = pat.sub(rep, txt)
        return txt


def _unq(s):
    return s[1:-1] if len(s) >= 2 and s[0] == s[-1] == '"' else s


# ---------------------------------------------------------------------------------------------------
# Running Lean


def tree_pids(pid):
    kids = collections.defaultdict(list)
    for p in os.listdir("/proc"):
        if p.isdigit():
            try:
                with open(f"/proc/{p}/stat") as fh:
                    st = fh.read()
                kids[int(st[st.rfind(")") + 2:].split()[1])].append(int(p))
            except (OSError, ValueError, IndexError):
                pass
    out, todo = [], [pid]
    while todo:
        p = todo.pop()
        out.append(p)
        todo.extend(kids.get(p, []))
    return out


def rss_max(pids):
    best = 0
    for p in pids:
        try:
            with open(f"/proc/{p}/status") as fh:
                best = max(best, next((int(l.split()[1]) * 1024 for l in fh if l.startswith("VmRSS:")), 0))
        except (OSError, ValueError):
            pass
    return best


LIVE = set()  # process groups of the running lean processes (killed when the ladder is stopped)


def _stop(signum, frame):
    for g in list(LIVE):
        try:
            os.killpg(g, signal.SIGKILL)
        except OSError:
            pass
    sys.exit(f"stopped by signal {signum}")


MSG = re.compile(r"^(.*?):(\d+):(\d+): (error|warning|info)(?:\([^)]*\))?: (.*)$")
BLOCKED = re.compile(r"unknown module prefix|object file .* does not exist|failed to read file|"
                     r"could not find (native implementation|module)|\.olean.* (not found|invalid)")


class Lean:
    def __init__(self, wt, threads, timeout, mem_gb):
        self.wt, self.timeout, self.mem = wt, timeout, mem_gb * 2**30
        self.env = dict(os.environ, LEAN_NUM_THREADS=str(threads))
        self.opts = []
        try:
            lo = tomllib.load(open(os.path.join(wt, "lakefile.toml"), "rb")).get("leanOptions", {})
            for k, v in lo.items():
                self.opts.append(f"-D{k}={str(v).lower() if isinstance(v, bool) else v}")
        except OSError:
            pass
        self.peak = 0
        self.runs = 0
        self.secs = 0.0
        self.lock = threading.Lock()

    def run(self, path):
        """Elaborate `path` -> (status, [(line, col, sev, msg)], seconds). status: ok, killed-mem,
        timeout, blocked."""
        cmd = [os.path.join(self.wt, "scripts", "lake"), "env", "lean"] + self.opts + [path]
        t0 = time.time()
        p = subprocess.Popen(cmd, cwd=self.wt, env=self.env, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, start_new_session=True)
        LIVE.add(p.pid)
        chunks = []
        rd = threading.Thread(target=lambda: chunks.append(p.stdout.read()))
        rd.start()
        why, peak = None, 0
        while p.poll() is None:
            pids = tree_pids(p.pid)
            peak = max(peak, rss_max(pids))
            if peak > self.mem:
                why = "killed-mem"
            elif time.time() - t0 > self.timeout:
                why = "timeout"
            if why:
                for q in pids:
                    try:
                        os.kill(q, signal.SIGKILL)
                    except OSError:
                        pass
                p.wait()
                break
            time.sleep(0.25)
        rd.join()
        LIVE.discard(p.pid)
        dt = time.time() - t0
        with self.lock:
            self.peak = max(self.peak, peak)
            self.runs += 1
            self.secs += dt
        out = (b"".join(chunks)).decode(errors="replace")
        msgs, cur = [], None
        for line in out.split("\n"):
            m = MSG.match(line)
            if m and os.path.abspath(os.path.join(self.wt, m.group(1))) == os.path.abspath(path):
                cur = [int(m.group(2)), int(m.group(3)), m.group(4), m.group(5)]
                msgs.append(cur)
            elif cur is not None and line and len(cur[3]) < 2000:
                cur[3] += "\n" + line
        if why:
            return why, msgs, dt
        if any(s == "error" and l == 1 and BLOCKED.search(t) for l, c, s, t in msgs):
            return "blocked", msgs, dt
        return "ok", msgs, dt


# ---------------------------------------------------------------------------------------------------
# The ladder on one file


def git(wt, *a):
    return subprocess.run(["git", "-C", wt] + list(a), capture_output=True, text=True)


class BaseTree:
    """The base revision's declarations: by file, and by qualified name over the whole tree."""

    def __init__(self, wt, rev):
        self.wt, self.rev = wt, rev
        self.files = {}
        self._index = None
        self.lock = threading.Lock()

    def file(self, path):
        with self.lock:
            if path not in self.files:
                r = git(self.wt, "show", f"{self.rev}:{path}")
                t = r.stdout if r.returncode == 0 else None
                self.files[path] = (t, keyed(parse(t)) if t else {})
            return self.files[path]

    def index(self):
        with self.lock:
            if self._index is None:
                ls = git(self.wt, "ls-tree", "-r", "--name-only", self.rev, "ConAgua").stdout.split()
                self._index = {"name": collections.defaultdict(list), "last": collections.defaultdict(list)}
                self._paths = [f for f in ls if f.endswith(".lean")]
        if not self._index["name"]:
            for f in self._paths:
                t, ds = self.file(f)
                for k, d in ds.items():
                    if d.kind in PROOF_KW and d.assign is not None:
                        self._index["name"][k].append((f, k))
                        self._index["last"][k.rsplit(".", 1)[-1]].append((f, k))
        return self._index

    def find(self, path, name, renames):
        """-> (path, base text, Decl, how) or None."""
        old = renames.get(name, renames.get(name.rsplit(".", 1)[-1], name))
        t, ds = self.file(path)
        if t is not None and old in ds and ds[old].assign is not None:
            return path, t, ds[old], "same file" + (" (renamed)" if old != name else "")
        ix = self.index()
        for key, how in ((old, "moved"), (old.rsplit(".", 1)[-1], "by last name")):
            hits = ix["name" if how == "moved" else "last"].get(key, [])
            if len(hits) == 1:
                f, k = hits[0]
                t, ds = self.file(f)
                return f, t, ds[k], f"{how} from {f}"
        return None


def assemble(text, decls, repl):
    """`text` with the spans of `decls` named in `repl` (name -> new text) replaced.
    -> (new text, {name: (first line, last line + 1)} 1-based of every decl in the new text)."""
    out, pos, line, spans = [], 0, 1, {}
    for k, d in decls:
        new = repl.get(k)
        pre = text[pos:d.a]
        out.append(pre)
        line += pre.count("\n")
        body = new if new is not None else text[d.a:d.b]
        spans[k] = (line, line + body.count("\n") + 1)
        out.append(body)
        line += body.count("\n")
        pos = d.b
    out.append(text[pos:])
    return "".join(out), spans


def faults(msgs, span, also_info=False):
    """Errors and `sorry` warnings within the 1-based line span."""
    a, b = span
    return [m for m in msgs if a <= m[0] < b and
            (m[2] == "error" or (m[2] == "warning" and "declaration uses 'sorry'" in m[3]))]


def first_line(m):
    return f"{m[0]}:{m[1]}: {m[3].splitlines()[0][:300]}" if m else ""


class Ladder:
    def __init__(self, a):
        self.a = a
        self.wt = a.worktree
        self.rules = Rules(a.rules)
        self.base = BaseTree(self.wt, a.base)
        self.lean = Lean(self.wt, a.threads, a.timeout, a.mem_gb)
        self.lock = threading.Lock()
        hook = a.vocab_hook or self.rules.hook
        self.hook = None
        if hook:
            spec = importlib.util.spec_from_file_location("vocab_hook", hook)
            mod = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(mod)
            self.hook = mod.candidates
        self.labels = []  # every variant label in ladder order, as rungs() emits them
        self.work = os.path.join(a.out, "work")
        os.makedirs(self.work, exist_ok=True)

    def rungs(self, proof, ctx):
        """[(rung, label, text)] in ladder order (duplicates are dropped by the caller)."""
        out = []
        if "master" in self.a.steps:
            out.append(("master", "master", proof))
        cm = Rules.apply(self.rules.codemod, proof, ctx["text"])
        if "codemod" in self.a.steps:
            out.append(("codemod", "codemod", cm))
        if "vocab" in self.a.steps:
            if self.hook:
                for lab, t in self.hook(cm, ctx):
                    out.append(("vocab", f"vocab:{lab}", t))
            else:
                for lab, rs in self.rules.vocab.items():
                    out.append(("vocab", f"vocab:{lab}", Rules.apply(rs, cm, ctx["text"])))
        with self.lock:
            for _, lab, _ in out:
                if lab not in self.labels:
                    self.labels.append(lab)
        return out

    def elab(self, path, txt, tag):
        p = os.path.join(self.work, path.replace("/", "__")[:-5] + f".{tag}.lean")
        with open(p, "w") as fh:
            fh.write(txt)
        st, msgs, dt = self.lean.run(p)
        if not self.a.keep_work:
            os.unlink(p)
        return st, msgs, dt

    def file(self, path, forced):
        R = {"file": path, "status": "ok", "closed": {}, "left": [], "runs": [], "secs": 0.0,
             "notes": []}
        full = os.path.join(self.wt, path)
        text = open(full).read()
        decls = parse(text)
        byname = keyed(decls)
        order = [(k, d) for k, d in byname.items()]
        order.sort(key=lambda kd: kd[1].a)
        named = {k for k, _ in order}
        # which theorems fail
        fail_err = {}
        if forced is not None:
            failing = []
            for k in forced:
                hits = [k] if k in named else [n for n in named if n.endswith("." + k)]
                if len(hits) == 1:
                    failing.append(hits[0])
                else:
                    R["notes"].append(f"{k}: {'ambiguous' if hits else 'not found'} in the file")
        elif self.a.failing == "sorry":
            failing = [k for k, d in order if d.kind in PROOF_KW and has_sorry_token(text, d)]
        else:
            st, msgs, dt = self.elab(path, text, "base")
            R["runs"].append(("base", st, round(dt, 1))); R["secs"] += dt
            if st != "ok":
                R["status"] = st
                R["notes"].append(first_line(next((m for m in msgs if m[2] == "error"), None)))
                return R
            _, spans = assemble(text, order, {})
            failing = []
            for k, d in order:
                f = faults(msgs, spans[k])
                if f:
                    failing.append(k)
                    fail_err[k] = f
            placed = {id(m) for k in fail_err for m in fail_err[k]}
            for m in msgs:
                if m[2] == "error" and id(m) not in placed:
                    R["notes"].append("outside any declaration: " + first_line(m))
        if not failing:
            return R
        cands = {}  # name -> [(rung, label, text)]
        stmt_bad = set()
        for k in failing:
            d = byname[k]
            line = d.l0 + 1
            if d.kind not in PROOF_KW:
                R["left"].append((k, line, "not a theorem", first_line((fail_err.get(k) or [None])[0])))
                continue
            if d.assign is None:
                R["left"].append((k, line, "no := proof", first_line((fail_err.get(k) or [None])[0])))
                continue
            errs = fail_err.get(k, [])
            stmt_err = [m for m in errs if m[2] == "error" and
                        _offset(text, m[0], m[1]) < d.assign]
            if stmt_err:
                R["left"].append((k, line, "statement", first_line(stmt_err[0])))
                stmt_bad.add(k)
                continue
            hit = self.base.find(path, k.split("#")[0], self.rules.renames)
            if hit is None:
                R["left"].append((k, line, "no base proof", first_line((errs or [None])[0])))
                continue
            bpath, btext, bd, how = hit
            proof = proof_text(btext, bd)
            stmt = stmt_text(text, d)
            ctx = {"file": path, "name": k, "stmt": stmt, "text": text, "rules": self.rules}
            seen = {text[d.a:d.b]} if forced is None else set()
            lst = []
            for rung, lab, t in self.rungs(proof, ctx):
                cand = stmt + t
                if cand in seen:
                    continue
                seen.add(cand)
                lst.append((rung, lab, cand))
            if not lst:
                R["left"].append((k, line, "no new candidate (the base proof is the current one)",
                                  first_line((errs or [None])[0])))
                continue
            cands[k] = (lst, how)
        accepted = {}  # name -> (label, text)
        last_err = {k: (fail_err.get(k) or [None])[0] for k in cands}
        tried = collections.defaultdict(list)
        labels = sorted({lab for lst, _ in cands.values() for _, lab, _ in lst},
                        key=self.labels.index)
        dead = False
        for lab in labels:
            todo = {k: next(t for _, l, t in cands[k][0] if l == lab)
                    for k in cands if k not in accepted and any(l == lab for _, l, _ in cands[k][0])}
            if not todo:
                continue
            repl = {k: t for k, (_, t) in accepted.items()}
            repl.update(todo)
            txt, spans = assemble(text, order, repl)
            st, msgs, dt = self.elab(path, txt, lab.replace(":", "-"))
            R["runs"].append((lab, st, round(dt, 1))); R["secs"] += dt
            if st != "ok":
                R["notes"].append(f"rung {lab}: {st}")
                if st == "blocked":
                    R["status"] = st
                    dead = True
                    break
                continue
            for k in todo:
                tried[k].append(lab)
                f = faults(msgs, spans[k])
                if f:
                    last_err[k] = f[0]
                else:
                    accepted[k] = (lab, todo[k])
        if dead:
            return R
        # verify the final text (with --write: the rest at sorry) and write it
        if accepted or self.a.write:
            for _ in range(3):
                repl = {k: t for k, (_, t) in accepted.items()}
                if self.a.write:
                    for k in failing:
                        d = byname[k]
                        if k not in accepted and d.kind in PROOF_KW and d.assign is not None \
                                and not has_sorry_token(text, d) and k not in stmt_bad:
                            repl[k] = stmt_text(text, d).rstrip() + " := by\n  sorry"
                txt, spans = assemble(text, order, repl)
                if not self.a.write and forced is not None:
                    break  # replay mode: the rung runs already checked them together
                st, msgs, dt = self.elab(path, txt, "final")
                R["runs"].append(("final", st, round(dt, 1))); R["secs"] += dt
                if st != "ok":
                    R["notes"].append(f"final check: {st}; nothing written")
                    accepted = {}
                    break
                bad = [k for k in accepted if faults(msgs, spans[k])]
                if not bad:
                    others = [m for m in msgs if m[2] == "error" and
                              not any(spans[k][0] <= m[0] < spans[k][1] for k in failing)]
                    if self.a.write and not others:
                        if txt != text:
                            tmp = full + ".ladder-tmp"
                            with open(tmp, "w") as fh:
                                fh.write(txt)
                            os.replace(tmp, full)
                            R["written"] = True
                    elif others:
                        R["notes"].append("final check: errors outside the re-proved theorems; "
                                          "nothing written: " + first_line(others[0]))
                    break
                for k in bad:
                    last_err[k] = faults(msgs, spans[k])[0]
                    del accepted[k]
                    R["notes"].append(f"{k}: closed alone, broke in the final check")
        for k, (lab, t) in accepted.items():
            R["closed"][k] = {"rung": lab, "how": cands[k][1], "line": byname[k].l0 + 1}
            cdir = os.path.join(self.a.out, "closed", path.replace("/", "__")[:-5])
            os.makedirs(cdir, exist_ok=True)
            with open(os.path.join(cdir, k.replace("/", "_") + ".lean"), "w") as fh:
                fh.write(t + "\n")
        for k in cands:
            if k not in accepted:
                R["left"].append((k, byname[k].l0 + 1, tried[k][-1] if tried[k] else "not run",
                                  first_line(last_err.get(k))))
        R["left"].sort(key=lambda x: x[1])
        return R


def _offset(text, line, col):
    starts = LEXCACHE.get(text)[2]
    return starts[line - 1] + col if line - 1 < len(starts) else len(text)


# ---------------------------------------------------------------------------------------------------
# Driver and report


RUNG_ORDER = ["master", "codemod", "vocab"]


def report(a, results, t0, lean):
    closed = collections.Counter()
    by_label = collections.Counter()
    tot_fail = 0
    for r in results:
        for k, c in r["closed"].items():
            closed[c["rung"].split(":")[0]] += 1
            by_label[c["rung"]] += 1
        tot_fail += len(r["closed"]) + len(r["left"])
    cum, lines = 0, []
    for rung in RUNG_ORDER:
        cum += closed[rung]
        lines.append(f"| ({'i' * (RUNG_ORDER.index(rung) + 1) if rung != 'vocab' else 'iii'}) {rung} "
                     f"| {closed[rung]} | {cum} |")
    blocked = [r for r in results if r["status"] != "ok"]
    md = [f"# Re-proof ladder: {os.path.basename(a.worktree)}", "",
          f"Base `{a.base}`, HEAD `{git(a.worktree, 'rev-parse', '--short', 'HEAD').stdout.strip()}`, "
          f"rules `{a.rules or '-'}`, rungs {','.join(a.steps)}, failing={a.failing}"
          f"{' (replay of ' + a.decls + ')' if a.decls else ''}, {'written' if a.write else 'report only'}.",
          f"{len(results)} files, {tot_fail} failing theorems; {lean.runs} lean runs, "
          f"{lean.secs / 60:.1f} CPU-min of lean, {(time.time() - t0) / 60:.1f} min wall, "
          f"peak {lean.peak / 2**30:.1f} GB per run, jobs {a.jobs}.", "",
          "| rung | closed | cumulative |", "|---|---:|---:|"] + lines + \
         [f"| left | {tot_fail - cum} | |", "", "By variant: " +
          ", ".join(f"{k} {v}" for k, v in sorted(by_label.items())), ""]
    if blocked:
        md += ["## Not processed", ""] + [f"* `{r['file']}`: {r['status']} {'; '.join(r['notes'][:1])}"
                                          for r in blocked] + [""]
    md += ["## Left (tickets), by file", ""]
    tickets = []
    for r in sorted(results, key=lambda r: r["file"]):
        if not r["left"] and not r["notes"]:
            continue
        md.append(f"### `{r['file']}` ({len(r['closed'])} closed, {len(r['left'])} left)")
        for k, line, step, err in r["left"]:
            md.append(f"* `{k}` (l. {line}) — {step} — {err.splitlines()[0][:200] if err else ''}")
            tickets.append("\t".join([r["file"], str(line), k, step, err.replace("\t", " ")]))
        for n in r["notes"]:
            md.append(f"* note: {n}")
        md.append("")
    os.makedirs(a.out, exist_ok=True)
    open(os.path.join(a.out, "report.md"), "w").write("\n".join(md) + "\n")
    open(os.path.join(a.out, "tickets.tsv"), "w").write("\n".join(tickets) + ("\n" if tickets else ""))
    json.dump({"args": {k: v for k, v in vars(a).items()}, "results": results,
               "closed": dict(closed), "by_variant": dict(by_label), "failing": tot_fail},
              open(os.path.join(a.out, "report.json"), "w"), indent=1)
    print("\n".join(md[:12 + len(lines)]))
    print(f"report: {os.path.join(a.out, 'report.md')}")


def read_decls(path):
    out = collections.OrderedDict()
    for raw in open(path):
        s = raw.split("#", 1)[0].strip() if not raw.lstrip().startswith("#") else ""
        if not s:
            continue
        if ":" in s.split()[0] and len(s.split()) == 1:
            f, names = s.split(":", 1)
            out.setdefault(f, []).extend(n for n in names.split(",") if n)
        else:
            f, n = s.split()
            out.setdefault(f, []).append(n)
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0],
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("files", nargs="*")
    ap.add_argument("--worktree", default=None)
    ap.add_argument("--base", default=None)
    ap.add_argument("--rules", default=None)
    ap.add_argument("--vocab-hook", default=None)
    ap.add_argument("--steps", default="master,codemod,vocab")
    ap.add_argument("--failing", choices=("elab", "sorry"), default="elab")
    ap.add_argument("--decls", default=None)
    ap.add_argument("--write", action="store_true")
    ap.add_argument("--out", default=None)
    ap.add_argument("--jobs", type=int, default=2)
    ap.add_argument("--threads", type=int, default=1)
    ap.add_argument("--timeout", type=int, default=900)
    ap.add_argument("--mem-gb", type=float, default=15)
    ap.add_argument("--keep-work", action="store_true", help="keep the elaborated candidate files")
    a = ap.parse_args()
    a.worktree = os.path.abspath(a.worktree or git(os.getcwd(), "rev-parse", "--show-toplevel").stdout.strip())
    a.steps = [s for s in a.steps.split(",") if s]
    if set(a.steps) - set(RUNG_ORDER):
        sys.exit(f"--steps: unknown {set(a.steps) - set(RUNG_ORDER)}")
    if a.base is None:
        a.base = git(a.worktree, "merge-base", "HEAD", "master").stdout.strip()
    a.base = git(a.worktree, "rev-parse", "--short", a.base).stdout.strip() or sys.exit("bad --base")
    root = os.path.realpath(os.path.join(a.worktree, "_tmp"))
    a.out = os.path.abspath(a.out or os.path.join(root, "ladder", os.path.basename(a.worktree)))
    forced = None
    if a.decls:
        forced = read_decls(a.decls)
        files = list(forced)
    elif a.files:
        files = [os.path.relpath(os.path.abspath(f), a.worktree) for f in a.files]
    else:
        d = git(a.worktree, "diff", "--name-only", "--diff-filter=AM", a.base, "--", "ConAgua").stdout.split()
        files = [f for f in d if f.endswith(".lean")]
    gen = re.compile(r"generated by|Generated by|DO NOT EDIT")
    files = [f for f in files if os.path.exists(os.path.join(a.worktree, f)) and
             not gen.search(open(os.path.join(a.worktree, f)).read(600))]
    # no build in this worktree while we read oleans and (with --write) edit sources
    lockf = open(os.path.join(a.worktree, ".lake", "scripts-lake.lock"), "w")
    try:
        fcntl.flock(lockf, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        sys.exit("a scripts/lake build is running in this worktree; run the ladder after it")
    signal.signal(signal.SIGTERM, _stop)
    signal.signal(signal.SIGINT, _stop)
    lad = Ladder(a)
    t0 = time.time()
    print(f"ladder: {len(files)} files, base {a.base}, jobs {a.jobs}, out {a.out}", flush=True)
    sizes = {f: os.path.getsize(os.path.join(a.worktree, f)) for f in files}
    results = []

    def one(f):
        try:
            r = lad.file(f, forced.get(f) if forced is not None else None)
        except Exception as e:  # a parse problem in one file must not stop the others
            r = {"file": f, "status": f"crashed: {type(e).__name__}: {e}", "closed": {}, "left": [],
                 "runs": [], "secs": 0.0, "notes": [repr(e)]}
        print(f"  {f}: {r['status']}, {len(r['closed'])} closed, {len(r['left'])} left, "
              f"{r['secs']:.0f} s", flush=True)
        return r

    with concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs) as ex:
        for r in ex.map(one, sorted(files, key=lambda f: -sizes[f])):
            results.append(r)
    report(a, results, t0, lad.lean)


if __name__ == "__main__":
    main()
