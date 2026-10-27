#!/usr/bin/env python3
"""Generate `ConAgua/Checker/Prog.lean`: the whole checker as one `Prog` (lane `integrate`).

DESIGN.md, "The checker as one program (lane `integrate`)". Steps:

1. Dump every binding of an L function name to a `FunDecl` in the `ConAgua` modules
   (`ConAgua/E2E/Dump.lean`, through `scripts/e2e.py`'s `dump_sets`).
2. From `check`, follow the calls. A name bound in `L.Checker.entryProg` (`ConAgua/Checker/Entry.lean`)
   takes that binding; otherwise the name must have exactly one body among its non-stub bindings
   (closed bindings first, ROM-parametric lookups instantiated at `romData` second) — several
   bodies, or a call whose argument count differs from the callee's parameters, is an error.
   A name with no L code becomes `abortStub n` (listed in the file and in DESIGN.md).
3. Ask `ConAgua/Checker/Sources.lean` for each chosen binding's Lean term and modules, and write
   the file: the imports, `checkerProg`, `checkerStubs`; `ProgTab.lean`, `ProgNrt.lean`,
   `ProgSkt.lean`: the literals the compiled code reads; and `ProgWf.lean`: `Prog.wf` by `prog_wf`
   (`WFSplit.lean`).
4. Write `ConAgua/Checker/Asm.lean` and `AsmPart<k>.lean`: the compiled checker as a kernel-checked
   literal (`asm_lit`, DESIGN.md "Kernel-checked compiler output"). Then regenerate the committed
   file `checker.s` with `scripts/asm_file.py` (it needs `Checker/Prog.lean` built).

Usage: scripts/checker_prog.py [--no-build] [--check]   (`--check`: fail if the file would change)
"""
import argparse
import collections
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import e2e  # noqa: E402

ROOT = e2e.ROOT
OUT = os.path.join(ROOT, "ConAgua", "Checker", "Prog.lean")
ASM_OUT = os.path.join(ROOT, "ConAgua", "Checker", "Asm.lean")
WF_OUT = os.path.join(ROOT, "ConAgua", "Checker", "ProgWf.lean")
TAB_OUT = os.path.join(ROOT, "ConAgua", "Checker", "ProgTab.lean")
NRT_OUT = os.path.join(ROOT, "ConAgua", "Checker", "ProgNrt.lean")
SKT_OUT = os.path.join(ROOT, "ConAgua", "Checker", "ProgSkt.lean")
# `checkerAsm`'s per-function kernel checks, spread over this many modules (built in parallel;
# each loads `Checker/Prog.lean`, about 3 GB): ASM_PARTS for the functions before the prelude's
# copies, one kernel check per function; PRE_PARTS for the copies (`pre_*`, and the stubs after
# them), one kernel check per part (`asmLitBatch`): every copy reads the prelude's 15 700 bytes
# (`ldc`), whose `romIdx` the kernel then evaluates once per part instead of once per function
# (~5 s each; 110 copies: 350 s in one part before)
ASM_PARTS = 6
PRE_PARTS = 4
ENTRY_SOURCES = ["L.Checker.entryProg", "L.Checker.preludeProg"]
PRE = "pre_"
# the frontend's input (`ConAgua/Checker/Prelude.lean`, `preFn`: byte array 0)
TOUCH = re.compile(r"\((?:l8|s8) 0 |\(n8 0\)")
ENTRY = "check"
# every module that imports the generated file (the asm parts, the write-set decisions, ...): its
# olean may be stale or missing while the file is regenerated
OUT_MOD = "ConAgua.Checker.Prog"
# modules never imported: the benchmarks (they clash with `NatBits` on `L.Arena.bv`), the generated
# file itself and what imports it
SKIP = re.compile(r"^ConAgua\.(Arena\.(LiftBench|Inst1Bench|WalkBench)\w*|Compiler\.WFAllBench|Checker\.(Prog|ProgTab|ProgNrt|ProgSkt|Wf|CoreErec)|E2E\.Check)$")


def assemble(dumps):
    binds, bodies, data_list, errs = e2e.read_dumps(dumps)
    chosen, src_of, problems = {}, {}, []

    def choose(name):
        bs = binds.get(name, [])
        mine = [(s, k) for s, k, st in bs if s in ENTRY_SOURCES]
        if mine:
            return mine[0]
        real = [(s, k) for s, k, st in bs if not st]
        if not real:
            return None
        closed = [(s, k) for s, k in real if not s.endswith("@rom")]
        pool = closed or real
        keys = collections.OrderedDict()
        for s, k in pool:
            keys.setdefault(k, []).append(s)
        if len(keys) > 1:
            problems.append(f"several bodies for `{name}`: " + "; ".join(
                f"{k}: {', '.join(sorted(ss)[:3])}" for k, ss in keys.items()))
        k, ss = next(iter(keys.items()))
        # prefer a `Prog` constant or a lookup in a plain constant over a structure's recursor
        ss = sorted(ss, key=lambda s: (bool(re.search(r"\.(rec|recOn|casesOn|mk)$", s)), len(s), s))
        return ss[0], k

    reach, todo, stubs = [], [ENTRY], {}
    seen = set()
    while todo:
        f = todo.pop()
        if f in seen:
            continue
        seen.add(f)
        c = choose(f)
        if c is None:
            np_ = {n for _, n in stubs.get(f, set())}
            stubs[f] = None
            continue
        src_of[f], chosen[f] = c
        reach.append(f)
        for g, nargs, nres in e2e.calls_of(bodies[c[1]][2]):
            todo.append(g[len(PRE):] if g.startswith(PRE) else g)
    # the frontend copied onto the prelude's bytes: from `front_run`, every function that reads
    # the input, or calls one that does
    calls = {f: [g for g, _, _ in e2e.calls_of(bodies[chosen[f]][2])] for f in reach}
    fr, todo2 = set(), ["front_run"]
    while todo2:
        f = todo2.pop()
        if f in fr or f not in chosen:
            continue
        fr.add(f)
        todo2 += calls[f]
    pre = {f for f in fr if TOUCH.search(bodies[chosen[f]][2])}
    while True:
        more = {f for f in fr if f not in pre and any(g in pre for g in calls[f])}
        if not more:
            break
        pre |= more
    for f in reach:
        for g in calls[f]:
            if g.startswith(PRE) and g[len(PRE):] not in pre:
                problems.append(f"`{f}` calls `{g}`, but `{g[len(PRE):]}` is not a copied frontend function")
    # arities
    want = collections.defaultdict(set)
    for f in reach:
        for g, nargs, _ in e2e.calls_of(bodies[chosen[f]][2]):
            if g.startswith(PRE):
                g = g[len(PRE):]
            want[g].add(nargs)
            if g in chosen and bodies[chosen[g]][0] != nargs:
                problems.append(f"`{f}` calls `{g}` with {nargs} arguments, `{g}` takes {bodies[chosen[g]][0]}")
    for g in stubs:
        if len(want[g]) != 1:
            problems.append(f"stub `{g}` called with {sorted(want[g])} arguments")
        stubs[g] = min(want[g])
    return sorted(reach), src_of, stubs, sorted(pre), sorted(fr - pre), problems, errs


def sources(src_of):
    work = os.path.join(e2e.WORK, "checker")
    os.makedirs(work, exist_ok=True)
    inp, out = os.path.join(work, "sources.in"), os.path.join(work, "sources.out")
    with open(inp, "w") as fh:
        for f, s in sorted(src_of.items()):
            fh.write(f"{s} {f}\n")
    mods = [m for m in e2e.all_modules() if not SKIP.match(m) and OUT_MOD not in e2e.closure(m)]
    src = os.path.join(ROOT, "ConAgua", "Checker", "SourcesRun.lean")
    with open(src, "w") as fh:
        fh.write("".join(f"import {m}\n" for m in mods))
        fh.write(f"import ConAgua.Checker.Sources\n#eval L.Checker.writeSources \"{inp}\" \"{out}\"\n")
    r = e2e.lake("env", "lean", src, check=False)
    os.remove(src)
    if r.returncode != 0:
        sys.exit(f"sources failed:\n{(r.stdout + r.stderr)[-4000:]}")
    res, errs = {}, []
    for line in open(out, encoding="utf-8"):
        w = line.rstrip("\n").split(" ", 3)
        if w[0] == "ok":
            res[w[1]] = (w[2].split(",") if w[2] else [], w[3])
        else:
            errs.append(line.strip())
    return res, errs


HEADER = '''import ConAgua.Compiler.WFSplit
import ConAgua.Checker.Entry
import ConAgua.Checker.Prelude
{imports}

/-!
# The checker: one program (generated by `scripts/checker_prog.py`; do not edit)

`checkerProg` is every L function reachable from `check` (`ConAgua/Checker/Entry.lean`), each bound
to the `FunDecl` of the lanes' modules: the one body every non-stub binding of the name agrees on
(`L.Checker.entryProg` first). `checkerStubs` are the called functions with no L code yet: they
abort (the checker declines). DESIGN.md, "The checker as one program (lane `integrate`)".

{nfun} functions, {nstub} of them stubs.
-/

namespace L.Checker

open L L.Compiler

/-- The called functions with no L code yet (each aborts). -/
def checkerStubs : List String := [{stub_names}]

/-- The frontend functions `builtin_prelude` runs on the prelude's bytes ({npre}; `preFn`,
`ConAgua/Checker/Prelude.lean`), each bound as `pre_<name>`. -/
def preNames : List String := [
  {pre_names}]

def preTree : NTree := nameTree preNames

/-- The functions reachable from `front_run` that are not copied ({nshared}): the copies call them
unrenamed (`PreSimProg`, `ConAgua/Checker/PreludeSim.lean`). -/
def preShared : List String := [
  {shared_names}]

/-- **The checker.** -/
def checkerProg : Prog := [
{entries}]

end L.Checker
'''

# The literals the compiled code and the static check read, each in its own module after
# `Prog.lean` (built in parallel; `checkerSkt_eq` alone is a 45 s kernel check): the modules that
# import the program do not wait for them.
TAB = '''import ConAgua.Checker.Prog
import ConAgua.Compiler.WFSplit

/-! `checkerProg`'s array table (generated by `scripts/checker_prog.py`, do not edit), apart from
`Prog.lean` so that the modules importing the program do not wait for it. -/

namespace L.Checker

open L L.Compiler

set_option maxRecDepth 100000 in
/-- The table for the arrays the program names (`Prog.wfAuto`'s), as a literal (`tab_lit%`: every
per-chunk check of `checkerProg_wf` unfolds it). -/
def checkerTab : Tab := tab_lit% (Prog.tab checkerProg (Prog.arrs checkerProg).1 (Prog.arrs checkerProg).2)

#guard checkerTab == Prog.tab checkerProg (Prog.arrs checkerProg).1 (Prog.arrs checkerProg).2

-- the word arrays are the ones `cap_check` checks
#guard (Prog.arrs checkerProg).2 == wordArrays

end L.Checker
'''

NRT = '''import ConAgua.Checker.Prog
import ConAgua.Compiler.WFSplit

/-! `checkerProg`'s result counts (generated by `scripts/checker_prog.py`, do not edit), apart from
`Prog.lean` so that the modules importing the program do not wait for them. -/

namespace L.Checker

open L L.Compiler

-- The result counts of `checkerProg`'s functions (`Prog.nrt`), as a literal, with
-- `checkerNrt_eq : Prog.nrt checkerProg = checkerNrt` (`nrt_lit`): every call site of the compiled
-- code looks its callee's count up in it (`asm_lit`).
nrt_lit checkerNrt : checkerProg

end L.Checker
'''

SKT = '''import ConAgua.Checker.Prog
import ConAgua.Compiler.WFSplit

/-! `checkerProg`'s leaf frames (generated by `scripts/checker_prog.py`, do not edit), apart from
`Prog.lean` so that the modules importing the program do not wait for them. -/

namespace L.Checker

open L L.Compiler

-- The frames of `checkerProg`'s leaves without a stack check (`Prog.skt`), as a literal, with
-- `checkerSkt_eq : Prog.skt checkerProg "check" = checkerSkt` (`skt_lit`): every function's stack
-- check of the compiled code looks its callees' frames up in it (`asm_lit`).
skt_lit checkerSkt : checkerProg "check"

end L.Checker
'''

WF = '''import ConAgua.Checker.ProgTab
import ConAgua.Compiler.WFSplit

/-! `checkerProg`'s static check (generated by `scripts/checker_prog.py`, do not edit), apart from
`Prog.lean` so that the modules importing the program (the asm parts, ...) do not wait for it. -/

namespace L.Checker

open L L.Compiler

/-- **`checkerProg` passes the compiler's static check** (every call resolves, with the callee's
parameter count; the names are distinct; the frames fit). -/
prog_wf checkerProg_wf : checkerTab checkerProg

end L.Checker
'''


ASM_PART = '''import ConAgua.Compiler.AsmLit
import ConAgua.Checker.ProgTab
import ConAgua.Checker.ProgNrt
import ConAgua.Checker.ProgSkt

/-! Part {k} of `checkerAsm` (`ConAgua/Checker/Asm.lean`; generated by `scripts/checker_prog.py`, do
not edit): the literals and kernel-checked equations of functions {lo} … {hi_1} of `checkerProg`. -/

namespace L.Checker

open L L.Compiler

set_option asmLitBatch {batch} in
asm_lit_fns checkerAsm : checkerTab checkerNrt checkerSkt checkerProg {lo} {hi}

end L.Checker
'''

ASM = '''{imports}

/-!
# The checker's machine code, as a kernel-checked literal (generated by `scripts/checker_prog.py`; do not edit)

`checkerAsm : Program` is the compiled checker as a literal term, and
`checkerAsm_eq : compileProg checkerTab checkerProg "check" = checkerAsm` is checked by the kernel,
one function at a time (`asm_lit`, `ConAgua/Compiler/AsmLit.lean`; the functions' checks are in
`AsmPart0` … `AsmPart{last}`), so running the compiler as compiled Lean code is not trusted.
`checkerFile_eq` (`ConAgua/Checker/AsmFileEq.lean`) compares it with the committed file
`checker.s` (`scripts/asm_file.py`). DESIGN.md, "Kernel-checked compiler output".
-/

namespace L.Checker

open L L.Compiler

/-- **The checker's code**: `compileProg checkerTab checkerProg "check"`, as a literal. -/
asm_lit checkerAsm : checkerTab checkerNrt checkerSkt checkerProg "check"

end L.Checker
'''


def lean_str(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--no-build", action="store_true")
    ap.add_argument("--check", action="store_true")
    a = ap.parse_args()
    if not a.no_build:
        e2e.log("building")
        # the whole library: the dump only sees modules with an olean (`e2e.all_modules`), so a
        # partial build silently drops lanes' modules (e.g. the frontend's, then `front_run` is
        # missing: "`builtin_prelude` calls `pre_front_run`, but `front_run` is not a copied
        # frontend function")
        # the generated file itself (and what imports it) may fail to build while it is stale:
        # that is what this script fixes, so only the modules it reads must build
        r = e2e.lake("build", "ConAgua", "ConAgua.Checker.Sources", "ConAgua.Checker.Entry",
                     "ConAgua.Checker.Prelude", "ConAgua.E2E.Dump", check=False)
        if r.returncode != 0:
            e2e.log("the full build failed (a stale generated file?); building the inputs only")
            e2e.lake("build", "ConAgua.Checker.Sources", "ConAgua.Checker.Entry",
                     "ConAgua.Checker.Prelude", "ConAgua.E2E.Dump")
    e2e.log("dumping")
    mods = [m for m in e2e.all_modules() if not SKIP.match(m) and OUT_MOD not in e2e.closure(m)]
    dumps, clashes = e2e.dump_sets(mods)
    if clashes:
        for bad, other, decl in clashes:
            e2e.log(f"CLASH: {bad} vs {other}: {decl}")
        sys.exit("modules clash on import (fix them first)")
    reach, src_of, stubs, pre, shared, problems, derrs = assemble(dumps)
    if problems:
        for p in problems:
            e2e.log("PROBLEM: " + p)
        sys.exit(f"{len(problems)} problems")
    e2e.log(f"{len(reach)} functions, {len(stubs)} stubs; asking for the sources")
    res, serrs = sources(src_of)
    if serrs:
        for e in serrs:
            e2e.log(e)
        sys.exit("sources failed")
    imports = sorted({m for f in reach for m in res[f][0]} - {"ConAgua.Checker.Entry", "ConAgua.Checker.Prelude"})
    imports = [m for m in imports if m.startswith("ConAgua.")]
    entries = [f"  ({lean_str(f)}, {res[f][1]})" for f in reach]
    entries += [f"  ({lean_str(PRE + f)}, preFn preTree ({res[f][1]}))" for f in pre]
    entries += [f"  ({lean_str(g)}, abortStub {n})" for g, n in sorted(stubs.items())]
    txt = HEADER.format(imports="\n".join(f"import {m}" for m in imports), nfun=len(entries),
                        nstub=len(stubs), stub_names=", ".join(lean_str(g) for g in sorted(stubs)),
                        pre_names=",\n  ".join(lean_str(f) for f in pre), npre=len(pre),
                        shared_names=",\n  ".join(lean_str(f) for f in shared), nshared=len(shared),
                        entries=",\n".join(entries))
    n = len(entries)
    s0 = len(reach)  # the first copy
    bounds = [s0 * k // ASM_PARTS for k in range(ASM_PARTS)] + \
        [s0 + (n - s0) * k // PRE_PARTS for k in range(PRE_PARTS + 1)]
    nparts = ASM_PARTS + PRE_PARTS
    outs = [(OUT, txt), (TAB_OUT, TAB), (NRT_OUT, NRT), (SKT_OUT, SKT), (WF_OUT, WF)]
    for k in range(nparts):
        lo, hi = bounds[k], bounds[k + 1]
        outs.append((os.path.join(ROOT, "ConAgua", "Checker", f"AsmPart{k}.lean"),
                     ASM_PART.format(k=k, lo=lo, hi=hi, hi_1=hi - 1,
                                     batch=1 if k < ASM_PARTS else max(1, hi - lo))))
    outs.append((ASM_OUT, ASM.format(imports="\n".join(f"import ConAgua.Checker.AsmPart{k}" for k in range(nparts)),
                                     last=nparts - 1)))
    stale = [os.path.join(ROOT, "ConAgua", "Checker", f"AsmPart{k}.lean") for k in range(nparts, nparts + 16)]
    stale = [p for p in stale if os.path.exists(p)]
    if stale and a.check:
        sys.exit(f"{stale[0]} is stale: run scripts/checker_prog.py")
    for p in stale:
        if not a.check:
            os.remove(p)
    for path, t in outs:
        old = open(path, encoding="utf-8").read() if os.path.exists(path) else None
        if a.check:
            if old != t:
                sys.exit(f"{path} is out of date: run scripts/checker_prog.py")
            continue
        with open(path, "w", encoding="utf-8") as fh:
            fh.write(t)
    if a.check:
        return
    e2e.log(f"wrote {OUT}: {len(entries)} functions ({len(stubs)} stubs), {len(imports)} imports")
    e2e.log("checker.s is now stale: build, then run scripts/asm_file.py and commit the file")


if __name__ == "__main__":
    main()
