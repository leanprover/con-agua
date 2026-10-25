#!/usr/bin/env python3
"""End-to-end differential testing of the L checker (lane `e2e`, DESIGN.md "End-to-end runs").

Steps (all in _tmp/e2e/<checkout name>/):

1. **Assemble.** Every `ConAgua` module (except executables and the spike) is imported, in as few
   import closures as the modules allow (some clash on declaration names; each clash is reported),
   and `ConAgua/E2E/Dump.lean` dumps every binding of an L function name to a FunDecl it finds
   (`Prog` lists and `p.lookup "f" = some d` hypotheses). The bindings are merged; the program is
   everything reachable from `check` and `check_np` (`ConAgua/E2E/Check.lean`). A called function
   with no L code (no binding, or only `abort` stubs) gets an e2e stub with its own code.
2. **Compile.** `check`: the shipped code, printed by `checker.s`'s generator
   (`ConAgua/Checker/AsmEmit.lean`; the report says whether the committed file is up to date);
   `check_np`: `e2e-l asm` (checks `Prog.wf`). Each linked with `cc main.c` (the entry stub
   lays out a fixed partition of one region, lane `abi`: no capacity retries).
3. **Run** every fixture (con-leche's e2e fixtures and the arena tests) through the compiled
   `check` and `check_np`, the reference `e2e-ref` (the twin at the program's pin list; with and
   without the prelude), and `L.run` (`e2e-l run`) on small fixtures; classify.
4. **Report** `docs/e2e.md` (and `--csv` appends a line to `docs/e2e.csv`).

Never a merge gate. Every run has a timeout; a monitor kills any run above PER_RUN_GB and the
largest run while all together are above TOTAL_GB.

Usage: scripts/e2e.py [--no-build] [--jobs N] [--only REGEX] [--rerun-failing [RESULTS]]
                     [--trace {disagree,all,none}] [--trace-sample N] [--write] [--csv]

Speed (lane `e2efix`): the tracing interpreter (`e2e-l trace`, up to T_INTERP s per run) runs by default
only where L and the reference disagree (L errors where the reference accepts, `DISAGREE-*`), plus
`--trace-sample` of the fixtures where L aborts and the reference rejects; `--trace all` traces every L
error. Traces are cached per (program, fixture, entry) in `tracecache.json`, so a second `--trace all`
on the same program costs nothing. `--rerun-failing` reruns only the fixtures that were not
`agree-accept`/`agree-reject*` in both entries of a previous `results.json` (default: this checkout's)
and merges them into it. Fixtures are started largest first (the long runs do not form the tail).
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
TRACE_MAX_BYTES = 1 << 20  # the tracing interpreter on l-error fixtures up to this size
TRACE_WORDS = 1 << 18
DEFAULT_JOBS = 8           # shared machine: at most ~8 runs at a time (each well under PER_RUN_GB)
# classes that count as passing for `--rerun-failing`
PASSING = ("agree-accept", "agree-reject", "agree-reject (L aborts)", "agree-timeout", "agree-memout")

# the real con-ron binary (the Rust checker, built from the vendored revision: DESIGN.md, lane
# `integrate`, "A second reference"); `$CON_RON` overrides
CON_RON = os.environ.get("CON_RON", os.path.join(ROOT, "_tmp", "ref", "con-ron-integrate", "target", "release", "con-ron"))
T_CONRON = 120      # seconds per con-ron run
T_PERF = 120        # seconds per `perf stat` run

ENTRIES = ["check", "check_np"]
PIN_VARIANTS = 3  # the variants in `pins.bin` (`romgen pins.bin 3`: all of `natOpPinSets`)
# further roots of the assembled program (test entries and the functions `e2e-diff` runs)
ROOTS = ENTRIES + ["e2e_front", "whnf", "whnf_core", "infer"]
E2E_SOURCE = "L.E2E.e2eProg"
# modules never imported by the dump: executables (a `main`), the spike, the census exe
SKIP_MODS = re.compile(r"^ConAgua\.(Census\.Main$|E2E\.(Main|Ref|Explore.*)$)")


def log(*a):
    print(*a, file=sys.stderr, flush=True)


def lake(*args, check=True):
    cmd = [os.path.join(ROOT, "scripts", "lake")] + list(args)
    r = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
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
        st, out, _ = self.run3(cmd, timeout, env)
        return st, out

    def run3(self, cmd, timeout, env=None, stderr=False):
        """Returns (status, stdout, exit code)."""
        p = subprocess.Popen(cmd, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT if stderr else subprocess.DEVNULL,
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
        return st, (out or "").strip(), p.returncode


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
        if not cur:
            sys.exit(f"dump {k}: no module left to import after dropping clashes {clashes[-3:]}; "
                     "usually stale oleans: run a full scripts/lake build first")
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


def write_checker(path):
    """The checker `L.Checker.checkerProg` (`ConAgua/Checker/Prog.lean`) and the test entries of
    `ConAgua/E2E/Check.lean`, as a program file (`L.E2E.writeChecker`)."""
    src = os.path.join(ROOT, "ConAgua", "E2E", "WriteRun.lean")
    with open(src, "w") as fh:
        fh.write(f"import ConAgua.E2E.Check\n#eval L.E2E.writeChecker \"{path}\"\n")
    r = lake("env", "lean", src, check=False)
    os.remove(src)
    if r.returncode != 0:
        sys.exit(f"writeChecker failed:\n{(r.stdout + r.stderr)[-4000:]}")


def write_conron_pins(path, n):
    """`natOpPinSets.take n` in con-ron's `con-ron-pins/1` format (`ConRon.Dump.dumpPins`), for
    `con-ron --pins FILE`: the three references run at one pin list."""
    src = os.path.join(ROOT, "ConAgua", "E2E", "PinsRun.lean")
    with open(src, "w") as fh:
        fh.write("import ConRon.Dump.Pins\n"
                 f"#eval IO.FS.writeFile \"{path}\" (ConRon.Dump.dumpPins (ConLeche.natOpPinSets.take {n}))\n")
    r = lake("env", "lean", src, check=False)
    os.remove(src)
    if r.returncode != 0:
        sys.exit(f"writing the con-ron pins failed:\n{(r.stdout + r.stderr)[-4000:]}")


def asm_of_prog(path):
    """The report's view of a program file: its functions, its stubs (code, parameters), callers."""
    fns, stubs, callers = {}, {}, collections.defaultdict(set)
    for line in open(path, encoding="utf-8"):
        w = line.rstrip("\n").split(" ", 4)
        if w[0] == "fn":
            fns[w[1]] = w[4]
        elif w[0] == "stub":
            stubs[w[1]] = (int(w[3]), int(w[2]), [])
    for f, text in fns.items():
        for g, _, _ in calls_of(text):
            callers[g].add(f)
    return {"reach": set(fns) | set(stubs), "stubs": stubs, "callers": callers, "conflicts": [],
            "conflicts_unreached": 0, "arity": [], "patched": [], "nbind": len(fns) + len(stubs)}


# ---------------------------------------------------------------- 2. compile

def checker_asm(s):
    """Write the shipped checker's assembler text to `s`, with the generator of `checker.s`
    (`ConAgua/Checker/AsmEmit.lean`, as `scripts/asm_file.py` runs it). Returns (ok, message); the
    message says whether the committed `checker.s` is up to date with it."""
    r = lake("env", "lean", "--run", "ConAgua/Checker/AsmEmit.lean", s, check=False)
    if r.returncode != 0:
        return False, (r.stdout + r.stderr).strip()[-2000:]
    with open(s, "rb") as a, open(os.path.join(ROOT, "checker.s"), "rb") as b:
        same = a.read() == b.read()
    return True, r.stdout.strip() + ("; checker.s is up to date" if same else
                                     "; **checker.s is STALE** (run scripts/asm_file.py)")


def compile_entry(prog, entry):
    """`check` is the shipped code (`checker_asm`); other entries are compiled by `e2e-l asm`."""
    s = os.path.join(WORK, f"{entry}.s")
    exe = os.path.join(WORK, f"{entry}.bin")
    if entry == "check":
        ok, msg = checker_asm(s)
        if not ok:
            return None, msg
    else:
        r = subprocess.run([os.path.join(BIN, "e2e-l"), "asm", prog, entry, s], capture_output=True, text=True)
        if r.returncode != 0:
            return None, (r.stdout + r.stderr).strip()
        msg = r.stdout.strip()
    c = subprocess.run(["cc", "-std=gnu23", "-O2", "-pthread", "-o", exe, os.path.join(ROOT, "main.c"), s],
                       capture_output=True, text=True)
    if c.returncode != 0:
        return None, c.stderr[-2000:]
    return exe, msg


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
    if lo == "timeout" and ref == "timeout":
        return "agree-timeout"
    if lo == "memout" and ref == "memout":
        # both run into PER_RUN_GB (e.g. `stack_fuel_offset`: with 2^32-word arrays L stops only at
        # its own record limits, lane abi; con-ron aborts on it, con-leche expects an abort)
        return "agree-memout"
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
              (f"* `L.Checker.checkerProg` (`ConAgua/Checker/Prog.lean`, `scripts/checker_prog.py`) and the "
               f"test entries of `ConAgua/E2E/Check.lean`: {len(asm['reach']) - len(asm['stubs'])} functions "
               f"with L code, **{len(asm['stubs'])} stubs** (`checkerStubs`: they abort; below)."
               if not args.text_dump else
               f"* {asm['nbind']} function names bound in the lanes' modules; the program reachable from "
               f"`check`/`check_np` has {len(asm['reach']) - len(asm['stubs'])} functions with L code and "
               f"**{len(asm['stubs'])} without** (e2e stubs, below)."),
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
        aborts = [r for r in res if r[entry]["class"] == "agree-reject (L aborts)"]
        ab = collections.Counter((r[entry]["stop"], r[entry]["ref"]) for r in aborts if "stop" in r[entry])
        if ab:
            lines += ["", "Where L aborts when both reject (the reference's stage: `line` = frontend, `decl` = the fold; "
                      f"{sum(ab.values())} of {len(aborts)} traced, `--trace all` traces all):", "",
                      "| L stops at | reference | fixtures |", "|---|---|---:|"]
            lines += [f"| {a} | {b} | {n} |" for (a, b), n in sorted(ab.items(), key=lambda x: -x[1])]
        cmp_bugs = [r for r in res if r[entry].get("interp") not in (None, "timeout", "memout") and
                    not same_outcome(r[entry]["interp"], r[entry]["l"])]
        if cmp_bugs:
            lines += ["", "**Compiled vs `L.run` differ** (a compiler or harness bug, or a capacity difference):", "",
                      "| fixture | compiled | `L.run` |", "|---|---|---|"]
            lines += [f"| `{r['id']}` | {r[entry]['l']} | {r[entry]['interp']} |" for r in cmp_bugs[:40]]
        lines += [""]
    lines += conron_report(res)
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


def perf_instr(guard, cmd, env=None):
    """`instructions:u` of one run (`perf stat`), or None."""
    st, out, rc = guard.run3(["perf", "stat", "-x,", "-e", "instructions:u", "--"] + cmd, T_PERF, env=env, stderr=True)
    if st != "ok":
        return None
    for line in out.splitlines():
        w = line.split(",")
        if len(w) > 2 and w[2].startswith("instructions") and w[0].isdigit():
            return int(w[0])
    return None


def conron_report(res):
    """The three references side by side (`check`), and instructions:u where both accept."""
    rs = [r for r in res if "conron" in r]
    if not rs:
        return []
    lines = ["## `check` against both references: `e2e-ref` (the twin, compiled by Lean) and `con-ron` (the Rust binary)", "",
             "`con-ron --jobs=1 --pins P FILE` at the vendored revision (exit codes: 0 accept, 1 reject, 2 decline, "
             "3 error; `P`: the same pin list as the others, `natOpPinSets.take 3` (all of it, as `pins.bin`) in its `con-ron-pins/1` format), `e2e-ref FILE --pins=3`, and the compiled `check`. Accept is the "
             "verdict compared.", "",
             "| con-ron | e2e-ref | L `check` | fixtures |", "|---|---|---|---:|"]
    def acc(v):
        return "accept" if v == "accept" else ("–" if v in ("timeout", "memout", "crash") or v.startswith("missing") else "no")
    cnt = collections.Counter((r["conron"], r["check"]["ref"].split(" ")[0], acc(r["check"]["l"])) for r in rs)
    lines += [f"| {a} | {b} | {c} | {n} |" for (a, b, c), n in sorted(cnt.items(), key=lambda x: -x[1])]
    three = sum(1 for r in rs if acc(r["conron"]) == acc(r["check"]["ref"].split(" ")[0]) == acc(r["check"]["l"]) != "–")
    bad = [r for r in rs if acc(r["conron"]) != acc(r["check"]["ref"].split(" ")[0]) and "–" not in (acc(r["conron"]), acc(r["check"]["ref"].split(" ")[0]))]
    lines += ["", f"* All three agree on accept/not on **{three}** of {len(rs)} fixtures; con-ron and `e2e-ref` "
              f"disagree on **{len(bad)}**" + (":" if bad else ".")]
    lines += [f"  * `{r['id']}`: con-ron {r['conron']}, e2e-ref {r['check']['ref']}" for r in bad[:30]]
    ps = [r for r in rs if r.get("perf") and r["perf"]["L"] and r["perf"]["con-ron"]]
    if ps:
        import math
        gm = math.exp(sum(math.log(r["perf"]["L"] / r["perf"]["con-ron"]) for r in ps) / len(ps))
        lines += ["", f"### `instructions:u`, compiled `check` vs `con-ron --jobs=1` (fixtures both accept; one run each)", "",
                  f"Geometric mean of the ratio L / con-ron over {len(ps)} fixtures: **{gm:.2f}**.", "",
                  "| fixture | bytes | L | con-ron | ratio |", "|---|---:|---:|---:|---:|"]
        for r in sorted(ps, key=lambda r: -r["size"])[:40]:
            lines.append(f"| `{r['id']}` | {r['size']} | {r['perf']['L']:,} | {r['perf']['con-ron']:,} | "
                         f"{r['perf']['L'] / r['perf']['con-ron']:.2f} |")
    return lines + [""]


def same_outcome(a, b):
    return a == b or (a.startswith("missing") and b.startswith("missing") and a == b)


# ---------------------------------------------------------------- main

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--no-build", action="store_true")
    ap.add_argument("--jobs", type=int, default=DEFAULT_JOBS)
    ap.add_argument("--only", default=None, help="regex on fixture ids")
    ap.add_argument("--rerun-failing", nargs="?", const=os.path.join(WORK, "results.json"), default=None,
                    metavar="RESULTS", help="rerun only the fixtures not passing in RESULTS (a previous "
                    "results.json; default this checkout's) and merge them into it")
    ap.add_argument("--trace", choices=["disagree", "all", "none"], default="disagree",
                    help="which L errors get the tracing interpreter (default: where L and the reference disagree)")
    ap.add_argument("--trace-sample", type=int, default=0,
                    help="also trace this many (evenly spread) fixtures where L aborts and the reference rejects")
    ap.add_argument("--no-interp", action="store_true")
    ap.add_argument("--no-diff", action="store_true", help="skip the per-function differential tests")
    ap.add_argument("--diff-sample", type=int, default=24, help="fixtures for e2e-diff (L.run is slow: ~3 min each)")
    ap.add_argument("--interp-sample", type=int, default=12, help="fixtures for L.run of check_np")
    ap.add_argument("--assemble-only", action="store_true", help="assemble and compile, run nothing")
    ap.add_argument("--text-dump", action="store_true",
                    help="assemble from the lanes' modules through text (the fallback; default: checkerProg)")
    ap.add_argument("--no-conron", action="store_true", help="skip the con-ron binary reference")
    ap.add_argument("--no-perf", action="store_true", help="skip instructions:u on fixtures both accept")
    ap.add_argument("--perf-only", action="store_true",
                    help="cheap perf rerun: no tracing, interpreter or differential checks (implies the perf runs); "
                    "(the verdict columns still come from the caches)")
    ap.add_argument("--latest", default=os.path.join(ROOT, "_tmp", "e2e", "latest", "results.json"),
                    help="machine-readable per-fixture perf table (written after every "
                    "full run that measured perf; '' to skip)")
    ap.add_argument("--write", action="store_true", help="write docs/e2e.md")
    ap.add_argument("--csv", action="store_true", help="append to docs/e2e.csv")
    args = ap.parse_args()
    t0 = time.time()
    if args.perf_only:
        args.no_diff = args.no_interp = True
        args.trace = "none"
    os.makedirs(WORK, exist_ok=True)
    if not args.no_build:
        log("building")
        # only what e2e needs (not the whole proof tree)
        lake("build", "ConAgua.E2E.Check", "ConAgua.Checker.Prog", "ConAgua.Compiler.Abi", "ConRon.Dump.Pins",
             "e2e-l", "e2e-ref", "e2e-diff")
    prog = os.path.join(WORK, "checker.prog")
    if args.text_dump:
        # the old path: every binding of the lanes' modules, through text (no `checkerProg` needed)
        log("dumping")
        dumps, clashes = dump_sets(all_modules())
        asm = assemble(dumps)
        write_prog(asm, prog)
    else:
        log("writing checkerProg")
        write_checker(prog)
        asm, clashes = asm_of_prog(prog), []
    log(f"program: {len(asm['reach'])} functions, {len(asm['stubs'])} stubs")
    compiled = {e: compile_entry(prog, e) for e in ENTRIES}
    for e, (exe, msg) in compiled.items():
        log(f"compile {e}: {msg[:300] if msg else ''}")
    if args.assemble_only:
        return
    stubs_by_code = {code: g for g, (code, _, _) in asm["stubs"].items()}
    # the pin data (byte array 1, DESIGN.md lane `romload`): the committed `pins.bin`, which main.c
    # embeds in the compiled binaries (all of con-leche's pin variants, scripts/asm_file.py); the
    # references run at the same pin list
    env = dict(os.environ, CA_PINS=os.path.join(ROOT, "pins.bin"))   # for `e2e-l run`/`trace`, `e2e-diff`
    npins = PIN_VARIANTS
    fx = fixtures()
    if args.only:
        fx = [f for f in fx if re.search(args.only, f[0])]
    prev = None
    if args.rerun_failing:
        prev = json.load(open(args.rerun_failing))["results"]
        failing = {r["id"] for r in prev if any(r[e]["class"] not in PASSING for e in ENTRIES)}
        fx = [f for f in fx if f[0] in failing]
        log(f"rerunning {len(fx)} previously failing fixtures (of {len(prev)}) from {args.rerun_failing}")
    with open(prog, "rb") as fh:
        prog_key = hashlib.sha1(fh.read()).hexdigest()[:16]
    tcache_path = os.path.join(WORK, "tracecache.json")
    tcache = json.load(open(tcache_path)) if os.path.exists(tcache_path) else {}
    cache_path = os.path.join(WORK, "refcache.json")
    cache = json.load(open(cache_path)) if os.path.exists(cache_path) else {}
    rk = ref_key()
    guard = Guard()
    # the samples for the slow L.run-based checks: evenly spread over the fixtures up to INTERP_MAX_BYTES
    small = [f[0] for f in fx if os.path.getsize(f[1]) <= INTERP_MAX_BYTES]
    def spread(k):
        return set(small[i * len(small) // k] for i in range(k)) if k and small else set()
    diff_set, interp_set = spread(args.diff_sample), spread(args.interp_sample)
    fids = [f[0] for f in fx]
    k = args.trace_sample
    trace_sample = set(fids[i * len(fids) // k] for i in range(k)) if k and fids else set()

    conron_key = None
    conron_pins = os.path.join(WORK, f"pins{npins}.con-ron-pins")
    if not args.no_conron and os.path.exists(CON_RON):
        st_ = os.stat(CON_RON)
        conron_key = f"{st_.st_size}-{int(st_.st_mtime)}-{npins}"
        if not os.path.exists(conron_pins):
            write_conron_pins(conron_pins, npins)
    elif not args.no_conron:
        log(f"no con-ron binary at {CON_RON}: skipping that reference")

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
                st, out, rc = guard.run3([os.path.join(BIN, "e2e-ref"), path] + (["--no-prelude"] if entry == "check_np" else []) + [f"--pins={npins}"], T_REF, stderr=True)
                ref, where = ref_verdict(next((l for l in out.splitlines() if l.startswith("verdict ")), ""), st)
                if ref == "crash":
                    # never cached: a transient failure must not outlive the binary that caused it
                    log(f"e2e-ref crashed on {fid} (exit {rc}): {out[-300:]!r}")
                elif st == "ok":
                    cache[ck] = [ref, where]
            exe = compiled[entry][0]
            if exe:
                st, out = guard.run([exe, path], T_COMPILED, env=env)
                lo = l_outcome(out, st, stubs_by_code)
            else:
                lo = "crash"
            d = {"ref": ref + (f" ({where})" if where else ""), "l": lo, "class": classify(lo, ref, where)}
            want = (args.trace == "all" or
                    (args.trace == "disagree" and (d["class"] == "l-error" or d["class"].startswith("DISAGREE")
                                                   or fid in trace_sample)))
            if lo == "error" and size <= TRACE_MAX_BYTES and want:
                tk = f"{prog_key}:{h}:{entry}:{TRACE_WORDS}"
                if tk in tcache:
                    ls = tcache[tk]
                else:
                    st, out = guard.run([os.path.join(BIN, "e2e-l"), "trace", prog, entry, path, str(TRACE_WORDS)], T_INTERP, env=env)
                    ls = out.splitlines()[:2] if st == "ok" else [st]
                    tcache[tk] = ls
                if len(ls) >= 2:
                    d["trace"] = ls[0] + " in " + ls[1][len("stack "):].split(" > ")[-1] + " (" + ls[1][len("stack "):] + ")"
                    d["stop"] = ls[0] + " in " + ls[1][len("stack "):].split(" > ")[-1]
                else:
                    d["trace"] = f"untraced ({ls[0] if ls else 'no output'})"
            if not args.no_interp and entry == "check_np" and fid in interp_set:
                st, out = guard.run([os.path.join(BIN, "e2e-l"), "run", prog, entry, path, str(INTERP_WORDS)], T_INTERP, env=env)
                d["interp"] = interp_outcome(out, st)
            r[entry] = d
        if conron_key:
            ck = f"conron:{conron_key}:{h}"
            if ck in cache:
                cr = cache[ck]
            else:
                st, out, rc = guard.run3([CON_RON, "--jobs=1", "--pins", conron_pins, path], T_CONRON)
                cr = {0: "accept", 1: "reject", 2: "decline", 3: "error"}.get(rc, f"exit {rc}") if st == "ok" else st
                if st == "ok":
                    cache[ck] = cr
            r["conron"] = cr
            if not args.no_perf and cr == "accept" and r["check"]["l"] == "accept":
                r["perf"] = {"L": perf_instr(guard, [compiled["check"][0], path], env),
                             "con-ron": perf_instr(guard, [CON_RON, "--jobs=1", "--pins", conron_pins, path]),
                             "e2e-ref": perf_instr(guard, [os.path.join(BIN, "e2e-ref"), path, f"--pins={npins}"])}
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
    order = {f[0]: i for i, f in enumerate(fx)}
    with cf.ThreadPoolExecutor(args.jobs) as ex:
        futs = [ex.submit(one, f) for f in sorted(fx, key=lambda f: -os.path.getsize(f[1]))]
        for i, fu in enumerate(cf.as_completed(futs)):
            res.append(fu.result())
            if i % 50 == 0:
                log(f"{i}/{len(fx)} ({time.time() - t0:.0f} s)")
    res.sort(key=lambda r: order[r["id"]])
    if prev is not None:
        new = {r["id"]: r for r in res}
        res = [new.get(r["id"], r) for r in prev]
    for path_, obj in ((cache_path, cache), (tcache_path, tcache)):
        with open(path_ + ".tmp", "w") as fh:
            json.dump(obj, fh)
        os.replace(path_ + ".tmp", path_)
    with open(os.path.join(WORK, "results.json"), "w") as fh:
        json.dump({"results": res, "stubs": {g: v[0] for g, v in asm["stubs"].items()}}, fh, indent=1)
    if args.latest and not args.no_perf and not args.only and args.rerun_failing is None and not args.no_conron:
        rows = [{"id": r["id"], "size": r["size"], "class": r["check"]["class"], "perf": r["perf"]}
                for r in res if r.get("perf") and r["perf"].get("L") and r["perf"].get("con-ron")]
        os.makedirs(os.path.dirname(args.latest), exist_ok=True)
        rev = subprocess.run(["git", "-C", ROOT, "rev-parse", "--short", "HEAD"], capture_output=True, text=True).stdout.strip()
        with open(args.latest + ".tmp", "w") as fh:
            json.dump({"date": time.strftime("%Y-%m-%d %H:%M", time.gmtime()) + " UTC", "rev": rev,
                       "fixtures": len(res), "seconds": round(time.time() - t0), "rows": rows}, fh, indent=1)
        os.replace(args.latest + ".tmp", args.latest)
        log(f"wrote {args.latest} ({len(rows)} perf rows)")
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
