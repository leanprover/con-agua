#!/usr/bin/env python3
"""End-to-end differential testing of the L checker (lane `e2e`, DESIGN.md "End-to-end runs").

Steps (all in _tmp/e2e/<checkout name>/):

1. **Assemble.** Every `ConAgua` module (except executables and the spike) is imported, in as few
   import closures as the modules allow (some clash on declaration names; each clash is reported),
   and `ConAgua/E2E/Dump.lean` dumps every binding of an L function name to a FunDecl it finds
   (`Prog` lists and `p.lookup "f" = some d` hypotheses). The bindings are merged; the program is
   everything reachable from `check` and `check_np` (`ConAgua/E2E/Check.lean`). A called function
   with no L code (no binding, or only `abort` stubs) gets an e2e stub with its own code.
2. **Compile.** `e2e-l asm` (checks `Prog.wf`) and `cc harness/e2e.c` for each entry.
3. **Run** every fixture (con-leche's e2e fixtures and the arena tests) through the compiled
   `check` and `check_np`, the reference `e2e-ref` (the twin at the program's pin list; with and
   without the prelude), and `L.run` (`e2e-l run`) on small fixtures; classify.
4. **Report** `docs/e2e.md` (and `--csv` appends a line to `docs/e2e.csv`).

Never a merge gate. Niced; every run has a timeout; a monitor kills any run above PER_RUN_GB and the
largest run while all together are above TOTAL_GB.

Usage: scripts/e2e.py [--no-build] [--jobs N] [--only REGEX] [--write] [--csv]
"""
import argparse
import collections
import concurrent.futures as cf
import datetime
import glob
import gzip
import hashlib
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import tarfile
import threading
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REF = os.path.join(ROOT, "_tmp", "ref", "con-leche", "tests")
WORK = os.path.join(ROOT, "_tmp", "e2e", os.path.basename(ROOT))
BIN = os.path.join(ROOT, ".lake", "build", "bin")

PER_RUN_GB = 6
TOTAL_GB = 20
T_COMPILED = 60      # seconds per compiled L run
T_REF = 120          # seconds per reference run
T_INTERP = 400       # seconds per L.run (interpreter) run (the pin stage alone is ~2 min under L.run)
T_DIFF = 600         # seconds per e2e-diff run
DIFF_N = 200         # expression handles per fixture in e2e-diff
DIFF_WORDS = 1 << 18       # words per array in e2e-diff (L.run holds every array in full)
DIFF_BIG_WORDS = 1 << 19   # words per array on e2e-diff's retry
INTERP_MAX_BYTES = 20000   # L.run only on fixtures up to this size
INTERP_WORDS = 1 << 18     # words per array under L.run
ACCEPT = "accept"
BIG_WORDS = 1 << 25        # words per array on the retry after an error
TRACE_MAX_BYTES = 1 << 20  # the tracing interpreter on l-error fixtures up to this size
TRACE_WORDS = 1 << 18

ENTRIES = ["check", "check_np"]
# further roots of the assembled program (test entries and the functions `e2e-diff` runs)
ROOTS = ENTRIES + ["e2e_front", "whnf", "whnf_core", "infer"]
E2E_SOURCE = "L.E2E.e2eProg"
# modules never imported by the dump: executables (a `main`), the spike, the census exe
SKIP_MODS = re.compile(r"^ConAgua\.(Spike\.|Census\.Main$|E2E\.(Main|Ref|Explore.*)$)")


def log(*a):
    print(*a, file=sys.stderr, flush=True)


def lake(*args, check=True):
    cmd = [os.path.join(ROOT, "scripts", "lake")] + list(args)
    r = subprocess.run(["nice", "-n", "10"] + cmd, cwd=ROOT, capture_output=True, text=True)
    if check and r.returncode != 0:
        sys.exit(f"{' '.join(cmd)} failed:\n{r.stdout[-4000:]}\n{r.stderr[-4000:]}")
    return r


# ---------------------------------------------------------------- process guard

class Guard:
    """Tracks live child processes; kills one above PER_RUN_GB, and the largest while the total is
    above TOTAL_GB."""

    def __init__(self):
        self.live = {}
        self.killed = {}
        self.lock = threading.Lock()
        threading.Thread(target=self.loop, daemon=True).start()

    @staticmethod
    def tree(pid):
        out, todo = [], [pid]
        while todo:
            p = todo.pop()
            out.append(p)
            try:
                for tid in os.listdir(f"/proc/{p}/task"):
                    with open(f"/proc/{p}/task/{tid}/children") as fh:
                        todo += [int(x) for x in fh.read().split()]
            except (OSError, ValueError):
                pass
        return out

    @classmethod
    def rss(cls, pid):
        total = 0
        for p in cls.tree(pid):
            try:
                with open(f"/proc/{p}/status") as fh:
                    total += next((int(l.split()[1]) * 1024 for l in fh if l.startswith("VmRSS:")), 0)
            except (OSError, ValueError):
                pass
        return total

    def kill(self, pid, why):
        self.killed[pid] = why
        for q in self.tree(pid):
            try:
                os.kill(q, signal.SIGKILL)
            except OSError:
                pass

    def loop(self):
        while True:
            time.sleep(0.25)
            with self.lock:
                pids = list(self.live)
            sizes = {p: self.rss(p) for p in pids}
            for p, m in sizes.items():
                if m > PER_RUN_GB * 2**30:
                    self.kill(p, "memout")
            while sum(sizes.values()) > TOTAL_GB * 2**30 and sizes:
                p = max(sizes, key=sizes.get)
                self.kill(p, "memout")
                del sizes[p]

    def run(self, cmd, timeout, env=None):
        """Returns (status, stdout): status is 'ok', 'timeout' or 'memout'."""
        p = subprocess.Popen(["nice", "-n", "10"] + cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                             text=True, start_new_session=True, env=env)
        with self.lock:
            self.live[p.pid] = True
        try:
            out, _ = p.communicate(timeout=timeout)
            st = "ok"
        except subprocess.TimeoutExpired:
            self.kill(p.pid, "timeout")
            out, _ = p.communicate()
            st = "timeout"
        with self.lock:
            del self.live[p.pid]
        if p.pid in self.killed:
            st = self.killed.pop(p.pid)
        return st, (out or "").strip()


# ---------------------------------------------------------------- 1. assemble

def all_modules():
    mods = []
    for f in sorted(glob.glob(os.path.join(ROOT, "ConAgua", "**", "*.lean"), recursive=True)):
        m = os.path.relpath(f, ROOT)[:-5].replace("/", ".")
        if SKIP_MODS.match(m):
            continue
        with open(f, encoding="utf-8") as fh:
            if re.search(r"^def main\b", fh.read(), re.M):
                continue
        if not os.path.exists(os.path.join(ROOT, ".lake", "build", "lib", "lean", *m.split(".")) + ".olean"):
            continue
        mods.append(m)
    return mods


def imports_of(m, cache={}):
    if m not in cache:
        p = os.path.join(ROOT, *m.split(".")) + ".lean"
        out = []
        if os.path.exists(p):
            for l in open(p, encoding="utf-8"):
                mm = re.match(r"\s*(?:public\s+|meta\s+)*import\s+(\S+)", l)
                if mm and mm.group(1).startswith("ConAgua"):
                    out.append(mm.group(1))
        cache[m] = out
    return cache[m]


def closure(m, memo={}):
    if m not in memo:
        memo[m] = {m}
        s = {m}
        for i in imports_of(m):
            s |= closure(i)
        memo[m] = s
    return memo[m]


def dump_sets(mods):
    """Dump the bindings of `mods`, split into import-compatible sets. Returns (dump files, clashes)."""
    os.makedirs(WORK, exist_ok=True)
    todo, k, dumps, clashes = list(mods), 0, [], []
    while todo:
        cur, rest = list(todo), []
        while True:
            src = os.path.join(ROOT, "ConAgua", "E2E", f"DumpRun{k}.lean")
            out = os.path.join(WORK, f"dump{k}.txt")
            with open(src, "w") as fh:
                fh.write("".join(f"import {m}\n" for m in cur))
                fh.write(f"import ConAgua.E2E.Dump\n#eval L.E2E.dumpBindings \"{out}\"\n")
            r = lake("env", "lean", src, check=False)
            os.remove(src)
            msg = r.stdout + r.stderr
            mm = re.search(r"import (\S+) failed, environment already contains '([^']+)' from (\S+)", msg)
            if mm:
                bad, decl, other = mm.groups()
                clashes.append((bad, other, decl))
                drop = [m for m in cur if bad in closure(m)]
                if not drop:
                    sys.exit(f"cannot drop {bad}:\n{msg[-3000:]}")
                cur = [m for m in cur if m not in drop]
                rest += drop
                continue
            if r.returncode != 0:
                sys.exit(f"dump {k} failed:\n{msg[-4000:]}")
            break
        dumps.append(out)
        log(f"dump {k}: {len(cur)} modules")
        todo, k = rest, k + 1
    return dumps, clashes


def read_dumps(dumps):
    """bindings: name -> list of (source, body key, stub); bodies: key -> (nparams, nlocals, text)."""
    data_idx, data_list = {}, []
    bodies, binds, errs = {}, collections.defaultdict(list), []
    for d in dumps:
        local_data, local_fn = {}, {}
        for line in open(d, encoding="utf-8"):
            w = line.rstrip("\n").split(" ")
            if w[0] == "data":
                h = w[2] if len(w) > 2 else ""
                if h not in data_idx:
                    data_idx[h] = len(data_list)
                    data_list.append(h)
                local_data[w[1]] = data_idx[h]
            elif w[0] == "fn":
                np_, nl = int(w[2]), int(w[3])
                text = " ".join(w[4:])
                text = re.sub(r"\(ldc (\d+) ", lambda m: f"(ldc {local_data[m.group(1)]} ", text)
                key = hashlib.sha1(f"{np_} {nl} {text}".encode()).hexdigest()[:16]
                bodies[key] = (np_, nl, text)
                local_fn[w[1]] = key
            elif w[0] == "bind":
                _, src, name, h, stub = w
                binds[name].append((src, local_fn[h], stub == "1"))
            elif w[0] == "err":
                errs.append(" ".join(w[1:]))
    return binds, bodies, data_list, errs


CALL = re.compile(r"\(call \(([\d ]*)\) (\S+) \(")


def arg_count(text, start):
    """The number of argument expressions of the list that opens at `text[start]`."""
    i, depth, n = start, 0, 0
    while True:
        c = text[i]
        if c == "(":
            depth += 1
            if depth == 2:
                n += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                return n
        i += 1


def calls_of(text):
    """(callee, number of arguments, number of results) of every call in a body."""
    return [(m.group(2), arg_count(text, m.end() - 1), len(m.group(1).split())) for m in CALL.finditer(text)]


def rename_calls(text, f):
    """`text` with each callee `g` (called with `n` arguments) renamed to `f(g, n)`."""
    return CALL.sub(lambda m: f"(call ({m.group(1)}) {f(m.group(2), arg_count(text, m.end() - 1))} (", text)


def assemble(dumps):
    binds, bodies, data_list, errs = read_dumps(dumps)
    chosen, conflicts = {}, []
    patched = sorted(n for n, bs in binds.items() if n not in ROOTS and any(s == E2E_SOURCE for s, _, _ in bs))
    for name, bs in binds.items():
        mine = [k for s, k, st in bs if s == E2E_SOURCE]
        real = collections.Counter(k for s, k, st in bs if not st)
        if mine:
            chosen[name] = mine[0]
        elif len(real) == 1:
            chosen[name] = next(iter(real))
        elif len(real) > 1:
            # a closed binding (a `Prog`, a lookup) wins over a ROM instance Dump.lean derived
            closed = collections.Counter(k for s, k, st in bs if not st and not s.endswith("@rom"))
            best = (closed or real).most_common(1)[0][0]
            if len(closed) == 1:
                chosen[name] = best
                continue
            chosen[name] = best
            conflicts.append({"name": name, "bodies": [
                {"key": k, "count": c, "sources": sorted({s for s, kk, _ in bs if kk == k})[:4]}
                for k, c in real.most_common()], "chosen": best})
    # reachability
    reach, todo, missing, arity = set(), list(ROOTS), {}, []
    callers = collections.defaultdict(set)
    while todo:
        f = todo.pop()
        if f in reach:
            continue
        reach.add(f)
        if f not in chosen:
            continue
        np_, nl, text = bodies[chosen[f]]
        for g, nargs, nres in calls_of(text):
            callers[g].add(f)
            if g in chosen:
                gp = bodies[chosen[g]][0]
                if gp != nargs:
                    arity.append({"caller": f, "callee": g, "args": nargs, "params": gp})
                    missing.setdefault(f"__arity_{g}_{nargs}", set()).add(nargs)
                    callers[f"__arity_{g}_{nargs}"].add(f)
                    continue
            else:
                missing.setdefault(g, set()).add(nargs)
            todo.append(g)
    stubs = {}
    for code, g in enumerate(sorted(missing), start=1):
        stub_np = {bodies[k][0] for s, k, st in binds.get(g, [])}
        np_ = max(missing[g] | stub_np)
        if len(missing[g] | stub_np) > 1:
            arity.append({"caller": ",".join(sorted(callers[g])), "callee": g,
                          "args": sorted(missing[g]), "params": sorted(stub_np)})
        stubs[g] = (code, np_, sorted({s for s, k, st in binds.get(g, [])})[:3])
    return {
        "chosen": chosen, "bodies": bodies, "data": data_list, "reach": reach, "stubs": stubs,
        "callers": callers, "conflicts": [c for c in conflicts if c["name"] in reach],
        "conflicts_unreached": len([c for c in conflicts if c["name"] not in reach]),
        "arity": arity, "errs": errs, "nbind": len(binds), "patched": patched,
    }


def write_prog(asm, path):
    with open(path, "w") as fh:
        for i, h in enumerate(asm["data"]):
            fh.write(f"data {i} {h}\n")
        for f in sorted(asm["reach"]):
            if f in asm["chosen"]:
                np_, nl, text = asm["bodies"][asm["chosen"][f]]
                text = rename_calls(text, lambda g, n: g if g not in asm["chosen"] or asm["bodies"][asm["chosen"][g]][0] == n else f"__arity_{g}_{n}")
                fh.write(f"fn {f} {np_} {nl} {text}\n")
        for g, (code, np_, _) in sorted(asm["stubs"].items()):
            fh.write(f"stub {g} {np_} {code}\n")


# ---------------------------------------------------------------- 2. compile

def compile_entry(prog, entry):
    s = os.path.join(WORK, f"{entry}.s")
    exe = os.path.join(WORK, f"{entry}.bin")
    r = subprocess.run([os.path.join(BIN, "e2e-l"), "asm", prog, entry, s], capture_output=True, text=True)
    if r.returncode != 0:
        return None, (r.stdout + r.stderr).strip()
    c = subprocess.run(["cc", "-O2", "-o", exe, os.path.join(ROOT, "harness", "e2e.c"), s],
                       capture_output=True, text=True)
    if c.returncode != 0:
        return None, c.stderr[-2000:]
    return exe, r.stdout.strip()


# ---------------------------------------------------------------- 3. fixtures and runs

def fixtures():
    """(id, path, con-leche's expected exit code or None)."""
    fx = os.path.join(WORK, "fixtures")
    os.makedirs(fx, exist_ok=True)
    out = []
    exp = {}
    for line in open(os.path.join(REF, "e2e-expected.txt"), encoding="utf-8"):
        w = line.split()
        if len(w) >= 2 and not line.startswith("#") and w[0].isdigit():
            exp["e2e/" + w[1]] = int(w[0])
    for line in open(os.path.join(REF, "arena-expected.txt"), encoding="utf-8"):
        w = line.split()
        if len(w) >= 2 and not line.startswith("#") and w[0].isdigit():
            exp["arena/" + w[1]] = int(w[0])
    for f in sorted(glob.glob(os.path.join(REF, "e2e", "*.ndjson*"))):
        name = os.path.basename(f)
        if name.endswith(".gz"):
            name = name[:-3]
            dst = os.path.join(fx, name)
            if not os.path.exists(dst):
                with gzip.open(f) as src, open(dst + ".part", "wb") as o:
                    shutil.copyfileobj(src, o)
                os.rename(dst + ".part", dst)
            f = dst
        out.append(("e2e/" + name, f, exp.get("e2e/" + name)))
    arena = os.path.join(WORK, "arena-tests")
    if not os.path.isdir(arena):
        with tarfile.open(os.path.join(REF, "arena", "lean-arena-tests.tar.gz")) as t:
            t.extractall(arena, filter="data")
    for f in sorted(glob.glob(os.path.join(arena, "**", "*.ndjson"), recursive=True)):
        rel = os.path.relpath(f, arena)
        out.append(("arena/" + rel, f, exp.get("arena/" + rel)))
    return out


def sha(path):
    h = hashlib.sha1()
    with open(path, "rb") as fh:
        for b in iter(lambda: fh.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()


def ref_key():
    h = hashlib.sha1()
    for p in [os.path.join(ROOT, "vendor", "UPSTREAM"), os.path.join(ROOT, "ConAgua", "E2E", "Ref.lean")]:
        h.update(open(p, "rb").read())
    for p in sorted(glob.glob(os.path.join(ROOT, "vendor", "patches", "**", "*.patch"), recursive=True)):
        h.update(open(p, "rb").read())
    return h.hexdigest()[:12]


def ref_verdict(out, st):
    """(verdict, where): where is `line` (the frontend's verdict), `decl` (the fold's) or ``."""
    if st != "ok":
        return st, ""
    m = re.match(r"verdict (\d+)(.*)", out)
    if not m:
        return "crash", ""
    v = {"0": "accept", "1": "reject", "2": "decline", "3": "error"}.get(m.group(1), "?")
    where = "line" if re.search(r"\(line \d+\)", m.group(2)) else ("decl" if "(declaration" in m.group(2) else "")
    return v, where


def l_outcome(out, st, stubs_by_code):
    if st != "ok":
        return st
    if out == "accept":
        return "accept"
    if out == "ok 1":
        return "reject-front"
    if out.startswith("ok "):
        return "ok-other " + out[3:]
    if out == "exhausted":
        return "exhausted"
    if out.startswith("missing "):
        return "missing " + stubs_by_code.get(int(out.split()[1]), "?")
    if out == "error":
        return "error"
    return "crash"


def interp_outcome(out, st):
    if st != "ok":
        return st
    if out.startswith("ok "):
        return "accept" if out == "ok 71757147230292" else ("reject-front" if out == "ok 1" else "ok-other " + out[3:])
    if out in ("abort", "oob"):
        return "error"
    return out  # missing NAME, exhausted, nofun NAME


def classify(lo, ref, where=""):
    """The class of one L outcome against the reference verdict (`where`: the reference's stage)."""
    if lo.startswith("missing "):
        return "missing"
    if lo in ("timeout", "memout", "exhausted", "crash"):
        return "l-" + lo
    racc = ref == "accept"
    if ref in ("timeout", "memout", "crash"):
        return "ref-" + ref
    if lo == "accept":
        return "agree-accept" if racc else "DISAGREE-accept"
    if lo == "reject-front":
        if racc:
            return "DISAGREE-reject"
        return "agree-reject" if where == "line" else "agree-reject, stage differs"
    if lo == "error":
        return "l-error" if racc else "agree-reject (L aborts)"
    return "DISAGREE-other"


# ---------------------------------------------------------------- 4. report

def report(res, asm, compiled, clashes, args, t0):
    lines = []
    now = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    rev = subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    lines += ["# End-to-end runs of the L checker (generated by `scripts/e2e.py`)", "",
              f"{now}, `{rev}`, {len(res)} fixtures, {time.time() - t0:.0f} s. Never a merge gate. "
              "How it works and how to read it: DESIGN.md, \"End-to-end runs (lane `e2e`)\".", ""]
    lines += ["## Assembly", "",
              f"* {asm['nbind']} function names bound in the lanes' modules; the program reachable from "
              f"`check`/`check_np` has {len(asm['reach']) - len(asm['stubs'])} functions with L code and "
              f"**{len(asm['stubs'])} without** (e2e stubs, below).",
              f"* Compiled: " + "; ".join(f"`{e}`: {('ok, ' + c[1]) if c[0] else 'FAILED: ' + c[1][:300]}" for e, c in compiled.items()), ""]
    if asm["patched"]:
        lines += ["* Bound by `ConAgua/E2E/Check.lean` (ROM instances and e2e patches, see there): "
                  + ", ".join(f"`{n}`" for n in asm["patched"]), ""]
    if clashes:
        lines += ["* **Modules that cannot be imported together** (a declaration defined twice; the "
                  "dump imports them in separate closures, a Lean assembly of the whole program cannot):", ""]
        seen = set()
        for a, b, d in clashes:
            if (frozenset((a, b)), d) not in seen:
                seen.add((frozenset((a, b)), d))
                lines.append(f"  * `{a}` vs `{b}`: both define `{d}`")
        lines += [""]
    if asm["conflicts"]:
        lines += ["* **Names bound to different L code** (the most common binding is used):", ""]
        for c in asm["conflicts"]:
            lines.append(f"  * `{c['name']}`: " + "; ".join(
                f"{b['count']}× from {', '.join('`' + s + '`' for s in b['sources'])}" for b in c["bodies"]))
        lines += [""]
    if asm["arity"]:
        lines += ["* **Arity mismatches** (caller's argument count vs the callee's parameters):", ""]
        lines += [f"  * `{a['caller']}` → `{a['callee']}`: {a['args']} arguments, {a['params']} parameters" for a in asm["arity"]]
        lines += [""]
    # classes
    for entry in ENTRIES:
        cnt = collections.Counter(r[entry]["class"] for r in res)
        lines += [f"## `{entry}` against `e2e-ref{' --no-prelude' if entry == 'check_np' else ''}`", "",
                  "| class | fixtures |", "|---|---:|"]
        lines += [f"| {k} | {v} |" for k, v in sorted(cnt.items())]
        miss = collections.Counter(r[entry]["l"][len("missing "):] for r in res if r[entry]["class"] == "missing")
        if miss:
            lines += ["", "Missing functions, by the fixtures each one blocks (the first stub a run reaches):", "",
                      "| function | fixtures | code | called from |", "|---|---:|---:|---|"]
            for g, n in miss.most_common():
                code = asm["stubs"].get(g, (0,))[0]
                lines.append(f"| `{g}` | {n} | {code} | {', '.join('`' + c + '`' for c in sorted(asm['callers'].get(g, []))[:4])} |")
        errs = [r for r in res if r[entry]["class"] in ("l-error", "DISAGREE-accept", "DISAGREE-reject", "DISAGREE-other", "l-crash", "agree-reject, stage differs")]
        if errs:
            lines += ["", "Disagreements, L errors where the reference accepts, and rejects at different stages "
                      "(smallest first; *where* is the tracing interpreter's stop: `abort #k` is the k-th `abort` "
                      "of the function's body in pre-order, from 0):", "",
                      "| fixture | bytes | class | L | `L.run` | reference | where |", "|---|---:|---|---|---|---|---|"]
            for r in sorted(errs, key=lambda r: r["size"])[:80]:
                lines.append(f"| `{r['id']}` | {r['size']} | {r[entry]['class']} | {r[entry]['l']} | {r[entry].get('interp', '–')} | "
                             f"{r[entry]['ref']} | {r[entry].get('trace', '–')} |")
        ab = collections.Counter((r[entry].get("stop", "?"), r[entry]["ref"]) for r in res
                                 if r[entry]["class"] == "agree-reject (L aborts)")
        if ab:
            lines += ["", "Where L aborts when both reject (the reference's stage: `line` = frontend, `decl` = the fold):", "",
                      "| L stops at | reference | fixtures |", "|---|---|---:|"]
            lines += [f"| {a} | {b} | {n} |" for (a, b), n in sorted(ab.items(), key=lambda x: -x[1])]
        capn = [r for r in res if r[entry].get("small")]
        if capn:
            lines += ["", f"{len(capn)} fixtures got further with the larger capacity ({BIG_WORDS} words per array): "
                      + ", ".join(f"`{r['id']}`" for r in capn[:20])]
        cmp_bugs = [r for r in res if r[entry].get("interp") not in (None, "timeout", "memout") and
                    not r[entry].get("small") and not same_outcome(r[entry]["interp"], r[entry]["l"])]
        if cmp_bugs:
            lines += ["", "**Compiled vs `L.run` differ** (a compiler or harness bug, or a capacity difference):", "",
                      "| fixture | compiled | `L.run` |", "|---|---|---|"]
            lines += [f"| `{r['id']}` | {r[entry]['l']} | {r[entry]['interp']} |" for r in cmp_bugs[:40]]
        lines += [""]
    if any("diff" in r for r in res):
        lines += diff_report(res)
    lines += ["## Stubs (called, no L code)", "",
              "| code | function | stub bindings in |", "|---:|---|---|"]
    for g, (code, np_, srcs) in sorted(asm["stubs"].items(), key=lambda x: x[1][0]):
        lines.append(f"| {code} | `{g}` ({np_}) | {', '.join('`' + s + '`' for s in srcs) or '– (no binding at all)'} |")
    lines += [""]
    return "\n".join(lines) + "\n"


def max_id(path):
    """The largest export id (`in`, `il`, `ie`) in a fixture (the dense id tables are sized for it, up
    to `DIFF_BIG_WORDS`; larger ids go to the tables' sparse overflow)."""
    best = 0
    with open(path, "rb") as fh:
        for m in re.finditer(rb'"i[nle]":(\d+)', fh.read()):
            best = max(best, int(m.group(1)))
    return best


def parse_diff(out, st):
    """`e2e-diff`'s output: front, store, and per function the tallies and examples."""
    d = {"status": st, "front": None, "store": None, "fns": {}}
    if st != "ok":
        return d
    cur = None
    for line in out.splitlines():
        if line.startswith("front "):
            d["front"] = line[6:]
        elif line.startswith("store "):
            d["store"] = line[6:]
        elif line.startswith("fn "):
            w = line.split()
            cur = w[1]
            t = {w[i]: int(w[i + 1]) for i in range(2, 14, 2) if i + 1 < len(w) and w[i + 1].isdigit()}
            m = re.search(r"missing \[(.*)\]", line)
            t["missing"] = dict((x.split(":")[0], int(x.split(":")[1])) for x in m.group(1).split(", ") if x) if m else {}
            t["examples"] = []
            d["fns"][cur] = t
        elif line.startswith("  ") and cur:
            d["fns"][cur]["examples"].append(line.strip())
    return d


def diff_report(res):
    lines = ["## Per-function differential tests (`e2e-diff`)", "",
             "From each fixture, the twin's state and L's memory after the stages before the fold "
             "(`internReservedPins`, `parseBytes`, `internAllPins`; L: `e2e_front()`); the stores' node "
             f"counts compared; then up to {DIFF_N} persistent expression handles per fixture through "
             "`whnf`, `whnf_core`, `infer` on both sides (verified mode, the empty environment). "
             "`both err`: the twin throws and L aborts.", ""]
    ds = [r for r in res if "diff" in r]
    front = collections.Counter("both ok" if (r["diff"]["front"] or "").startswith("L ok 0 twin ok") else
                                (r["diff"]["front"] or r["diff"]["status"]) for r in ds)
    store = collections.Counter((r["diff"]["store"] or "–").split(" ")[0] for r in ds if r["diff"]["store"])
    lines += [f"* Front: {front.get('both ok', 0)} fixtures where both succeed; stores agree on "
              f"{store.get('agree', 0)}, **differ on {store.get('DIFFER', 0)}**."]
    for r in ds:
        if (r["diff"]["store"] or "").startswith("DIFFER"):
            lines.append(f"  * `{r['id']}`: {r['diff']['store'][7:][:300]}")
    other = [(r["id"], r["diff"]["front"]) for r in ds if r["diff"]["front"] and not r["diff"]["front"].startswith("L ok 0 twin ok")
             and not re.match(r"L (ok [1-9]|error .*) twin (reject|error)", r["diff"]["front"])]
    if other:
        lines.append(f"* Front outcomes differ (L vs twin) on {len(other)}:")
        lines += [f"  * `{i}`: {f[:200]}" for i, f in other[:20]]
    lines += ["", "| function | handles | agree | disagree | L error, twin ok | L ok, twin error | both err | missing |",
              "|---|---:|---:|---:|---:|---:|---:|---|"]
    names = sorted({f for r in ds for f in r["diff"]["fns"]})
    ex = []
    for f in names:
        tot = collections.Counter()
        miss = collections.Counter()
        for r in ds:
            t = r["diff"]["fns"].get(f)
            if not t:
                continue
            for k in ("n", "agree", "disagree", "lerr", "twinerr", "botherr"):
                tot[k] += t.get(k, 0)
            miss.update(t["missing"])
            ex += [(r["id"], e) for e in t["examples"]]
        lines.append(f"| `{f}` | {tot['n']} | {tot['agree']} | {tot['disagree']} | {tot['lerr']} | {tot['twinerr']} | "
                     f"{tot['botherr']} | {', '.join(f'`{k}` {v}' for k, v in miss.most_common(5))} |")
    if ex:
        lines += ["", "Examples (handle words; `e2e-diff PROG FIXTURE` reproduces):", ""]
        lines += [f"* `{i}`: {e[:300]}" for i, e in ex[:40]]
    return lines + [""]


def same_outcome(a, b):
    return a == b or (a.startswith("missing") and b.startswith("missing") and a == b)


# ---------------------------------------------------------------- main

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--no-build", action="store_true")
    ap.add_argument("--jobs", type=int, default=max(1, min(16, (os.cpu_count() or 4) // 4)))
    ap.add_argument("--only", default=None, help="regex on fixture ids")
    ap.add_argument("--no-interp", action="store_true")
    ap.add_argument("--no-diff", action="store_true", help="skip the per-function differential tests")
    ap.add_argument("--diff-sample", type=int, default=24, help="fixtures for e2e-diff (L.run is slow: ~3 min each)")
    ap.add_argument("--interp-sample", type=int, default=12, help="fixtures for L.run of check_np")
    ap.add_argument("--assemble-only", action="store_true", help="assemble and compile, run nothing")
    ap.add_argument("--write", action="store_true", help="write docs/e2e.md")
    ap.add_argument("--csv", action="store_true", help="append to docs/e2e.csv")
    args = ap.parse_args()
    t0 = time.time()
    os.makedirs(WORK, exist_ok=True)
    if not args.no_build:
        log("building")
        lake("build")
        lake("build", "ConAgua.E2E.Check", "ConAgua.E2E.Dump", "e2e-l", "e2e-ref", "e2e-diff")
    log("dumping")
    dumps, clashes = dump_sets(all_modules())
    asm = assemble(dumps)
    prog = os.path.join(WORK, "checker.prog")
    write_prog(asm, prog)
    log(f"program: {len(asm['reach'])} functions, {len(asm['stubs'])} stubs")
    compiled = {e: compile_entry(prog, e) for e in ENTRIES}
    for e, (exe, msg) in compiled.items():
        log(f"compile {e}: {msg[:300] if msg else ''}")
    if args.assemble_only:
        return
    stubs_by_code = {code: g for g, (code, _, _) in asm["stubs"].items()}
    # the pin-data buffer (byte array 1, DESIGN.md lane `romload`), once the program reads it
    reads_pins = any(c[0] and re.search(r"\bnb ([2-9]|\d\d)", c[1]) for c in compiled.values())
    env = dict(os.environ)
    npins = 0
    if reads_pins:
        pins = os.path.join(WORK, "pins.bin")
        if not os.path.exists(pins):
            lake("exe", "romgen", pins, "1")
        env["CA_PINS"] = pins
        npins = 1
    fx = fixtures()
    if args.only:
        fx = [f for f in fx if re.search(args.only, f[0])]
    cache_path = os.path.join(WORK, "refcache.json")
    cache = json.load(open(cache_path)) if os.path.exists(cache_path) else {}
    rk = ref_key()
    guard = Guard()
    # the samples for the slow L.run-based checks: evenly spread over the fixtures up to INTERP_MAX_BYTES
    small = [f[0] for f in fx if os.path.getsize(f[1]) <= INTERP_MAX_BYTES]
    def spread(k):
        return set(small[i * len(small) // k] for i in range(k)) if k and small else set()
    diff_set, interp_set = spread(args.diff_sample), spread(args.interp_sample)

    def one(f):
        fid, path, exp = f
        size = os.path.getsize(path)
        r = {"id": fid, "size": size, "expected": exp}
        h = sha(path)
        for entry in ENTRIES:
            ck = f"{rk}:{h}:{entry}:{npins}"
            if ck in cache:
                ref, where = cache[ck]
            else:
                st, out = guard.run([os.path.join(BIN, "e2e-ref"), path] + (["--no-prelude"] if entry == "check_np" else []) + [f"--pins={npins}"], T_REF)
                ref, where = ref_verdict(out, st)
                if st == "ok":
                    cache[ck] = [ref, where]
            exe = compiled[entry][0]
            cap = None
            if exe:
                st, out = guard.run([exe, path], T_COMPILED, env=env)
                lo = l_outcome(out, st, stubs_by_code)
                if lo == "error":
                    # capacities: once more with every array 8 times larger
                    st, out = guard.run([exe, path], T_COMPILED, env=dict(env, CA_WORDS=str(BIG_WORDS)))
                    lo2 = l_outcome(out, st, stubs_by_code)
                    if lo2 != lo:
                        cap, lo = lo, lo2
            else:
                lo = "crash"
            d = {"ref": ref + (f" ({where})" if where else ""), "l": lo, "class": classify(lo, ref, where)}
            if cap:
                d["small"] = cap
            if lo == "error" and size <= TRACE_MAX_BYTES:
                st, out = guard.run([os.path.join(BIN, "e2e-l"), "trace", prog, entry, path, str(TRACE_WORDS)], T_INTERP, env=env) if entry == "check_np" else ("skip", "")
                ls = out.splitlines()
                if st == "ok" and len(ls) >= 2:
                    d["trace"] = ls[0] + " in " + ls[1][len("stack "):].split(" > ")[-1] + " (" + ls[1][len("stack "):] + ")"
                    d["stop"] = ls[0] + " in " + ls[1][len("stack "):].split(" > ")[-1]
            if not args.no_interp and entry == "check_np" and fid in interp_set:
                st, out = guard.run([os.path.join(BIN, "e2e-l"), "run", prog, entry, path, str(INTERP_WORDS)], T_INTERP, env=env)
                d["interp"] = interp_outcome(out, st)
            r[entry] = d
        if not args.no_diff and fid in diff_set:
            st, out = guard.run([os.path.join(BIN, "e2e-diff"), prog, path, str(DIFF_N), str(DIFF_WORDS),
                                 str(min(max_id(path) + 2, DIFF_BIG_WORDS))], T_DIFF, env=env)
            r["diff"] = parse_diff(out, st)
            if (r["diff"]["front"] or "").startswith("L error") and (r["diff"]["front"] or "").endswith("twin ok"):
                # capacities: once more with larger arrays (`L.run` holds every array in full)
                st, out = guard.run([os.path.join(BIN, "e2e-diff"), prog, path, str(DIFF_N), str(DIFF_BIG_WORDS),
                                     str(min(max_id(path) + 2, DIFF_BIG_WORDS))], T_DIFF, env=env)
                r["diff"] = parse_diff(out, st)
        return r

    res = []
    with cf.ThreadPoolExecutor(args.jobs) as ex:
        for i, r in enumerate(ex.map(one, fx)):
            res.append(r)
            if i % 50 == 0:
                log(f"{i}/{len(fx)}")
    with open(cache_path + ".tmp", "w") as fh:
        json.dump(cache, fh)
    os.replace(cache_path + ".tmp", cache_path)
    with open(os.path.join(WORK, "results.json"), "w") as fh:
        json.dump({"results": res, "stubs": {g: v[0] for g, v in asm["stubs"].items()}}, fh, indent=1)
    md = report(res, asm, compiled, clashes, args, t0)
    out_md = os.path.join(ROOT, "docs", "e2e.md") if args.write else os.path.join(WORK, "e2e.md")
    with open(out_md, "w") as fh:
        fh.write(md)
    log(f"wrote {out_md}")
    if args.csv:
        p = os.path.join(ROOT, "docs", "e2e.csv")
        new = not os.path.exists(p)
        rev = subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=ROOT, capture_output=True, text=True).stdout.strip()
        with open(p, "a") as fh:
            if new:
                fh.write("date,rev,entry,fixtures,functions,stubs,agree_accept,agree_reject,missing,l_error,disagree,other,top_missing\n")
            for entry in ENTRIES:
                cnt = collections.Counter(r[entry]["class"] for r in res)
                miss = collections.Counter(r[entry]["l"][8:] for r in res if r[entry]["class"] == "missing")
                dis = sum(v for k, v in cnt.items() if k.startswith("DISAGREE"))
                arej = sum(v for k, v in cnt.items() if k.startswith("agree-reject"))
                known = cnt["agree-accept"] + arej + cnt["missing"] + cnt["l-error"] + dis
                fh.write(",".join(map(str, [
                    datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M"), rev, entry, len(res),
                    len(asm["reach"]) - len(asm["stubs"]), len(asm["stubs"]), cnt["agree-accept"], arej,
                    cnt["missing"], cnt["l-error"], dis, len(res) - known,
                    (miss.most_common(1)[0][0] if miss else "")])) + "\n")
    print(md)


if __name__ == "__main__":
    main()
