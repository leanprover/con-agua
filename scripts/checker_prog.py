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
   the file: the imports, `checkerProg`, `checkerStubs`; `ProgTab.lean`; `ProgTree.lean` (the name
   tree, for the proofs about `checkerProg`); `ProgIdx.lean`, `ProgIPart<k>.lean`, `ProgI.lean`: the
   program the compiler compiles, `checkerProgI` (`checkerProg` with its small leaves inlined,
   `ConAgua/Compiler/Inline.lean`), as kernel-checked literals; and over `checkerProgI`:
   `ProgNrt.lean`, `ProgSkt.lean` (parts `ProgSktPart<k>.lean`): the literals the compiled code
   reads, and `ProgWf.lean`: `Prog.wf` by `prog_wf` (`WFSplit.lean`; the name tree in
   `ProgTreeI.lean`, the chunk checks in `ProgWfPart<k>.lean`).
4. Write `ConAgua/Checker/Asm.lean` and `AsmPart<k>.lean`: the compiled checker as a kernel-checked
   literal (`asm_lit`, DESIGN.md "Kernel-checked compiler output"). Then regenerate the committed
   file `checker.s` with `scripts/asm_file.py` (it needs `Checker/ProgI.lean` built).
5. Build `ConAgua.Checker.Prog` and regenerate the call-closure lists the proofs about
   `checkerProg` check (`CLOSURES`: `core_fns.py`, `loop_fns.py`, `leaf_fns.py`, `phaseb_fns.py`,
   `preloop_ws.py`, in that order, each after building the modules its Lean script imports).
   Skipped with `--no-build` or `--no-closures`.

Usage: scripts/checker_prog.py [--no-build] [--no-closures] [--check]   (`--check`: fail if the file would change)
"""
import argparse
import collections
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import e2e  # noqa: E402
import arr_names  # noqa: E402
import lean_module  # noqa: E402

ROOT = e2e.ROOT
OUT = os.path.join(ROOT, "ConAgua", "Checker", "Prog.lean")
ASM_OUT = os.path.join(ROOT, "ConAgua", "Checker", "Asm.lean")
WF_OUT = os.path.join(ROOT, "ConAgua", "Checker", "ProgWf.lean")
TAB_OUT = os.path.join(ROOT, "ConAgua", "Checker", "ProgTab.lean")
NRT_OUT = os.path.join(ROOT, "ConAgua", "Checker", "ProgNrt.lean")
SKT_OUT = os.path.join(ROOT, "ConAgua", "Checker", "ProgSkt.lean")
TREE_OUT = os.path.join(ROOT, "ConAgua", "Checker", "ProgTree.lean")
TREE_I_OUT = os.path.join(ROOT, "ConAgua", "Checker", "ProgTreeI.lean")
IDX_OUT = os.path.join(ROOT, "ConAgua", "Checker", "ProgIdx.lean")
INL_OUT = os.path.join(ROOT, "ConAgua", "Checker", "ProgI.lean")
# The inliner (`ConAgua/Compiler/Inline.lean`): leaves of at most INLINE_SIZE nodes, one round
# (docs/design/inline.md §1). Its per-function literals (`inl_round_fns`) in INL_PARTS modules
# before the prelude's copies and INL_PRE_PARTS for the copies (the slowest to check).
INLINE_SIZE = 80
# The cut points (function indices, for a `checkerProg` of CUT_REF functions; scaled to the actual
# count) are balanced by measured kernel time, not by function count: a function's check costs
# anywhere from 1 ms to 4.5 s, and the heavy ones cluster (docs/design/lnext3.md, "Balanced
# parts"). To retune, profile each part (`set_option profiler true`, `profiler.threshold 1` before
# `inl_round_fns` / `asm_lit_fns`; one `type checking took` line per batch or function, in order),
# and cut the cumulative cost into equal shares.
CUT_REF = 1721
INL_CUTS = [0, 173, 316, 608, 805, 924, 1126, 1251, 1418, 1578, 1721]
ASM_CUTS = [0, 175, 314, 503, 645, 758, 906, 966, 1086, 1222, 1238, 1372, 1489, 1597, 1721]
INL_PARTS = len(INL_CUTS) - 1
INL_PRE_PARTS = 2
# `checkerAsm`'s per-function kernel checks, spread over this many modules (built in parallel;
# each loads `Checker/Prog.lean`, about 3 GB): ASM_PARTS for the functions before the prelude's
# copies, one kernel check per function; PRE_PARTS for the copies (`pre_*`, and the stubs after
# them), one kernel check per part (`asmLitBatch`): every copy reads the prelude's 15 700 bytes
# (`ldc`), whose `romIdx` the kernel then evaluates once per part instead of once per function
# (~5 s each; 110 copies: 350 s in one part before)
ASM_PARTS = len(ASM_CUTS) - 1
PRE_PARTS = 4
# `checkerSkt_eq` (one kernel check of every leaf's frame: 55 s) in SKT_PARTS modules, by function
# ranges; `checkerProg_wf`'s chunk checks (`progWfChunk` functions each; 50 s) in WF_PARTS
# modules, by chunk ranges (the last, the prelude's copies, reads the most constant data). The
# parts run in parallel, so an L change's rebuild does not wait for one long module (lnext2 §3).
SKT_PARTS = 6
WF_PARTS = 4
WF_CHUNK = 32
ENTRY_SOURCES = ["L.Checker.entryProg", "L.Checker.preludeProg"]
PRE = "pre_"
# the frontend's input (`ConAgua/Checker/Prelude.lean`, `preFn`: byte array 0)
# a read or write of the input byte array (`IN`'s number in `ConAgua/Layout.lean`)
IN_ID = next(n for n, name in arr_names.byte_names().items() if name == "IN")
TOUCH = re.compile(rf"\((?:l8|s8) {IN_ID} |\(n8 {IN_ID}\)")
ENTRY = "check"
# every module that imports the generated file (the asm parts, the write-set decisions, ...): its
# olean may be stale or missing while the file is regenerated
OUT_MOD = "ConAgua.Checker.Prog"
# modules never imported: the benchmarks (they clash with `NatBits` on `L.Arena.bv`), the generated
# file itself and what imports it
SKIP = re.compile(r"^ConAgua\.(Arena\.(LiftBench|Inst1Bench|WalkBench)\w*|Compiler\.WFAllBench|Checker\.(Prog|ProgTab|ProgNrt|ProgSkt\w*|ProgWf\w*|ProgTree|ProgTreeI|ProgIdx|ProgI|ProgIPart\d+|ProgIRef|Wf|CoreErec)|E2E\.Check)$")


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

set_option maxRecDepth 100000 in
/-- **The checker.** (The code generator recurses once per list cell: `maxRecDepth`.) -/
def checkerProg : Prog := [
{entries}]

end L.Checker
'''

# The literals the compiled code and the static check read, each in its own module after
# `Prog.lean` (built in parallel; `checkerSkt_eq` alone is a 45 s kernel check): the modules that
# import the program do not wait for them.
TAB = '''import ConAgua.Checker.Prog
import ConAgua.Compiler.WFSplit
import ConAgua.Layout

/-! `checkerProg`'s array table (generated by `scripts/checker_prog.py`, do not edit), apart from
`Prog.lean` so that the modules importing the program do not wait for it. -/

namespace L.Checker

open L L.Compiler

/-- The checker's word arrays in layout order: the table's rows, the table-relative one last (its
position gets no slot, `L.Compiler.Tab.nslot`). -/
def checkerWordRows : List ArrDecl :=
  checkerArrays.filter (fun d => d.kind == .word && !d.atTable) ++ checkerArrays.filter (·.atTable)

/-- The checker's table: the layout of `checkerArrays` (the byte arrays first, in table order: the
input, the pin data; then the word arrays, `checkerWordRows`), the program's constant data, result
and global counts (`t`), `checkerArrays`' minimum lengths and table-relative array
(`Tab.tblBase`). -/
def checkerTabOf (t : Tab) : Tab :=
  let l := Tab.ofArrs (checkerArrays.ids .byte) (checkerWordRows.map fun d => (d.id, d.tiered)) t.rom t.nres t.ng
  { l with mins := checkerArrays.mins, tbl := checkerArrays.tblArr.map fun x => (x.1, l.tblBase) }

set_option maxRecDepth 100000 in
/-- The checker's table (`checkerTabOf`), as a literal (`tab_lit%`: every per-chunk check of
`checkerProg_wf` unfolds it). -/
def checkerTab : Tab :=
  tab_lit% (checkerTabOf (Prog.tab checkerProg))

#guard checkerTab == checkerTabOf (Prog.tab checkerProg)

end L.Checker
'''

NRT = '''import ConAgua.Checker.ProgI
import ConAgua.Compiler.WFSplit

/-! The result counts of the compiled program `checkerProgI` (generated by `scripts/checker_prog.py`,
do not edit), apart from `ProgI.lean` so that the modules importing the program do not wait for
them. -/

namespace L.Checker

open L L.Compiler

-- The result counts of `checkerProgI`'s functions (`Prog.nrt`), as a literal, with
-- `checkerNrt_eq : Prog.nrt checkerProgI = checkerNrt` (`nrt_lit`): every call site of the compiled
-- code looks its callee's count up in it (`asm_lit`).
nrt_lit checkerNrt : checkerProgI

end L.Checker
'''

SKT = '''{imports}

/-! The leaf frames of the compiled program `checkerProgI` (generated by `scripts/checker_prog.py`, do
not edit), apart from `ProgI.lean` so that the modules importing the program do not wait for them. -/

namespace L.Checker

open L L.Compiler

-- The frames of `checkerProgI`'s leaves without a stack check (`Prog.skt`), as a literal, with
-- `checkerSkt_eq : Prog.skt checkerProgI "check" = checkerSkt` (`skt_lit`, from the parts'
-- `checkerSkt.part<i>`, `ProgSktPart<k>`): every function's stack check of the compiled code looks
-- its callees' frames up in it (`asm_lit`).
skt_lit checkerSkt : checkerProgI "check"

end L.Checker
'''

SKT_PART = '''import ConAgua.Checker.ProgI

/-! Part {k} of `checkerSkt_eq` (`ConAgua/Checker/ProgSkt.lean`; generated by
`scripts/checker_prog.py`, do not edit): the leaf frames of functions {lo} … {hi_1} of
`checkerProgI`, one kernel check (`skt_part`). -/

namespace L.Checker

open L L.Compiler

-- the kernel's whnf of a long body (`par_compact`'s calls, lane compare2) recurses deeply
set_option maxRecDepth 100000 in
skt_part checkerSkt : checkerProgI "check" {lo} {hi}

end L.Checker
'''

TREE = '''import ConAgua.Checker.Prog

/-! `checkerProg`'s name tree (generated by `scripts/checker_prog.py`, do not edit):
`checkerProg_wf.tree_eq : progTree checkerProg = some checkerProg_wf.tree` (the names are
distinct), apart from `ProgWf.lean` so that the modules that need only the names
(`PreludeSimProg.lean`) do not wait for the table and the static check. -/

namespace L.Checker

open L L.Compiler

prog_tree checkerProg_wf : checkerProg

end L.Checker
'''

TREE_I = '''import ConAgua.Checker.ProgI

/-! The compiled program's name tree (generated by `scripts/checker_prog.py`, do not edit):
`checkerProgI_wf.tree_eq : progTree checkerProgI = some checkerProgI_wf.tree`, for the static check
(`ProgWf.lean`). -/

namespace L.Checker

open L L.Compiler

prog_tree checkerProgI_wf : checkerProgI

end L.Checker
'''

WF_PART = '''import ConAgua.Checker.ProgTab
import ConAgua.Checker.ProgTreeI

/-! Part {k} of `checkerProgI_wf` (`ConAgua/Checker/ProgWf.lean`; generated by
`scripts/checker_prog.py`, do not edit): the per-chunk kernel checks `checkerProgI_wf.c<j>` of
chunks {lo} … {hi_1} (`prog_wf_part`). -/

namespace L.Checker

open L L.Compiler

prog_wf_part checkerProgI_wf : checkerTab checkerProgI {lo} {hi}

end L.Checker
'''

WF = '''{imports}

/-! The static check of the compiled program `checkerProgI` (generated by `scripts/checker_prog.py`,
do not edit), apart from `ProgI.lean` so that the modules importing the program (the asm parts, ...)
do not wait for it. The per-chunk checks are in `ProgWfPart<k>` (built in parallel), the name tree
in `ProgTreeI`. -/

namespace L.Checker

open L L.Compiler

/-- **The compiled program `checkerProgI` passes the compiler's static check** (every call
resolves, with the callee's parameter count; the names are distinct; the frames fit). -/
prog_wf checkerProgI_wf : checkerTab checkerProgI

end L.Checker
'''


IDX = '''import ConAgua.Checker.Prog
import ConAgua.Compiler.InlineLit

/-! `checkerProg`'s name tree for the inliner (generated by `scripts/checker_prog.py`, do not edit), a
literal (`idx_lit`): the inliner (`ConAgua/Compiler/Inline.lean`) finds its callees through it. That
it is `Prog.idxTree checkerProg` (`checkerIdx_eq`) is checked in `ProgIRef.lean`, off the path to the
compiled code. -/

namespace L.Checker

open L L.Compiler

set_option maxRecDepth 100000 in
idx_lit checkerIdx : checkerProg

end L.Checker
'''

INL_PART = '''import ConAgua.Checker.ProgIdx
import ConAgua.Checker.AsmKeys

/-! Part {k} of `checkerProgI` (`ConAgua/Checker/ProgI.lean`; generated by `scripts/checker_prog.py`,
do not edit): functions {lo} … {hi_1} of `checkerProg` with their small leaves inlined, as
literals, each with its kernel-checked equation (`inl_round_fns`, `ConAgua/Compiler/InlineLit.lean`). -/

namespace L.Checker

open L L.Compiler

inl_round_fns checkerProgI : {size} checkerXKeys checkerIdx checkerProg {lo} {hi}

end L.Checker
'''

INL = '''{imports}

/-!
# The program the compiler compiles (generated by `scripts/checker_prog.py`; do not edit)

`checkerProgI`: `checkerProg` with its leaves of at most {size} nodes inlined (one round of
`inlRound`, `ConAgua/Compiler/Inline.lean`), except the functions with a hand-written body
(`checkerXKeys`, `ConAgua/Checker/AsmKeys.lean`), as a literal whose functions the kernel checked one
at a time (`ProgIPart0` … `ProgIPart{last}`). The whole-program checks of the compiled code
(`ProgNrt`, `ProgSkt`, `ProgWf`, the asm parts) read the literal. That it is the inliner's output
and that it refines `checkerProg` (`checkerProgI_refines`) is `Checker/ProgIRef.lean`.
-/

namespace L.Checker

open L L.Compiler

/-- **The program the compiler compiles**: `checkerProg` with its small leaves inlined. -/
inl_round checkerProgI : {size} checkerXKeys checkerIdx checkerProg

end L.Checker
'''

ASM_PART = '''import ConAgua.Compiler.AsmLit
import ConAgua.Checker.AsmX
import ConAgua.Checker.ProgTab
import ConAgua.Checker.ProgNrt
import ConAgua.Checker.ProgSkt

/-! Part {k} of `checkerAsm` (`ConAgua/Checker/Asm.lean`; generated by `scripts/checker_prog.py`, do
not edit): the literals and kernel-checked equations of functions {lo} … {hi_1} of `checkerProgI`. -/

namespace L.Checker

open L L.Compiler

set_option maxRecDepth 100000 in
set_option asmLitBatch {batch} in
asm_lit_fns checkerAsm : checkerTab checkerNrt checkerSkt checkerProgI {lo} {hi} asm checkerX

end L.Checker
'''

ASM = '''{imports}

/-!
# The checker's machine code, as a kernel-checked literal (generated by `scripts/checker_prog.py`; do not edit)

`checkerAsm : Program` is the compiled checker as a literal term, and
`checkerAsm_eq : compileProgX checkerX checkerTab checkerProgI "check" = checkerAsm` is checked by the
kernel, one function at a time (`asm_lit`, `ConAgua/Compiler/AsmLit.lean`; the functions' checks are in
`AsmPart0` … `AsmPart{last}`), so running the compiler as compiled Lean code is not trusted.
`checkerFile_eq` (`ConAgua/Checker/AsmFileEq.lean`) compares it with the committed file
`checker.s` (`scripts/asm_file.py`). DESIGN.md, "Kernel-checked compiler output".
-/

namespace L.Checker

open L L.Compiler

/-- **The checker's code**: `compileProgX checkerX checkerTab checkerProgI "check"` (`checkerProgI`:
the checker with its small leaves inlined, `ConAgua/Checker/ProgI.lean`; `checkerX`: the hand-written
bodies, `ConAgua/Checker/AsmX.lean`), as a literal. -/
asm_lit checkerAsm : checkerTab checkerNrt checkerSkt checkerProgI "check" asm checkerX

end L.Checker
'''


def lean_str(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


# The closure-list generators, in dependency order (`leaf_fns.lean` reads `loopFns`), with the
# modules each one's Lean script imports besides the program (built before it runs).
CLOSURES = [("core_fns.py", ["ConAgua.Arena.CoreErec"]), ("loop_fns.py", ["ConAgua.Arena.LoopFns"]),
            ("leaf_fns.py", ["ConAgua.Arena.LeafFns"]), ("phaseb_fns.py", []), ("preloop_ws.py", [])]


def closures():
    """Step 5: the program's olean, then each closure list regenerated from it."""
    e2e.log("building ConAgua.Checker.Prog for the closure lists")
    e2e.lake("build", "ConAgua.Checker.Prog")
    for script, mods in CLOSURES:
        if mods:
            e2e.lake("build", *mods)
        e2e.log(f"regenerating with {script}")
        r = subprocess.run([sys.executable, os.path.join(ROOT, "scripts", script)], cwd=ROOT,
                           capture_output=True, text=True)
        if r.returncode != 0:
            sys.exit(f"scripts/{script} failed:\n{(r.stdout + r.stderr)[-3000:]}")
        e2e.log(f"  {r.stdout.strip().splitlines()[-1] if r.stdout.strip() else 'ok'}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--no-build", action="store_true")
    ap.add_argument("--no-closures", action="store_true",
                    help="do not build the program and regenerate the closure lists (step 5)")
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
    if os.environ.get("CHECKER_PROG_BUILT_ONLY"):
        def built(m):
            o = os.path.join(ROOT, ".lake", "build", "lib", "lean", *m.split(".")) + ".olean"
            return os.path.exists(o) and all(built_c.setdefault(d, os.path.exists(os.path.join(ROOT, ".lake", "build", "lib", "lean", *d.split(".")) + ".olean")) for d in e2e.closure(m) if d.startswith("ConAgua"))
        built_c = {}
        mods = [m for m in mods if built(m)]
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
    bounds = [s0 * c // CUT_REF for c in ASM_CUTS[:-1]] + \
        [s0 + (n - s0) * k // PRE_PARTS for k in range(PRE_PARTS + 1)]
    nparts = ASM_PARTS + PRE_PARTS
    chk = os.path.join(ROOT, "ConAgua", "Checker")
    skt_b = [n * k // SKT_PARTS for k in range(SKT_PARTS + 1)]
    nch = (n + WF_CHUNK - 1) // WF_CHUNK
    wf_b = [nch * k // WF_PARTS for k in range(WF_PARTS + 1)]
    inl_b = [s0 * c // CUT_REF for c in INL_CUTS[:-1]] + \
        [s0 + (n - s0) * k // INL_PRE_PARTS for k in range(INL_PRE_PARTS + 1)]
    ninl = INL_PARTS + INL_PRE_PARTS
    outs = [(OUT, txt), (TAB_OUT, TAB), (NRT_OUT, NRT), (TREE_OUT, TREE), (TREE_I_OUT, TREE_I),
            (IDX_OUT, IDX),
            (INL_OUT, INL.format(imports="\n".join(f"import ConAgua.Checker.ProgIPart{k}" for k in range(ninl)),
                                 size=INLINE_SIZE, last=ninl - 1)),
            (SKT_OUT, SKT.format(imports="\n".join(f"import ConAgua.Checker.ProgSktPart{k}" for k in range(SKT_PARTS))
                                 + "\nimport ConAgua.Compiler.WFSplit")),
            (WF_OUT, WF.format(imports="\n".join(f"import ConAgua.Checker.ProgWfPart{k}" for k in range(WF_PARTS))
                               + "\nimport ConAgua.Compiler.WFSplit"))]
    for k in range(ninl):
        outs.append((os.path.join(chk, f"ProgIPart{k}.lean"),
                     INL_PART.format(k=k, lo=inl_b[k], hi=inl_b[k + 1], hi_1=inl_b[k + 1] - 1, size=INLINE_SIZE)))
    for k in range(SKT_PARTS):
        outs.append((os.path.join(chk, f"ProgSktPart{k}.lean"),
                     SKT_PART.format(k=k, lo=skt_b[k], hi=skt_b[k + 1], hi_1=skt_b[k + 1] - 1)))
    for k in range(WF_PARTS):
        outs.append((os.path.join(chk, f"ProgWfPart{k}.lean"),
                     WF_PART.format(k=k, lo=wf_b[k], hi=wf_b[k + 1], hi_1=wf_b[k + 1] - 1)))
    for k in range(nparts):
        lo, hi = bounds[k], bounds[k + 1]
        outs.append((os.path.join(ROOT, "ConAgua", "Checker", f"AsmPart{k}.lean"),
                     ASM_PART.format(k=k, lo=lo, hi=hi, hi_1=hi - 1,
                                     batch=1 if k < ASM_PARTS else max(1, hi - lo))))
    outs.append((ASM_OUT, ASM.format(imports="\n".join(f"import ConAgua.Checker.AsmPart{k}" for k in range(nparts)),
                                     last=nparts - 1)))
    stale = [os.path.join(ROOT, "ConAgua", "Checker", f"AsmPart{k}.lean") for k in range(nparts, nparts + 16)]
    stale += [os.path.join(chk, f"ProgSktPart{k}.lean") for k in range(SKT_PARTS, SKT_PARTS + 16)]
    stale += [os.path.join(chk, f"ProgWfPart{k}.lean") for k in range(WF_PARTS, WF_PARTS + 16)]
    stale += [os.path.join(chk, f"ProgIPart{k}.lean") for k in range(ninl, ninl + 16)]
    stale = [p for p in stale if os.path.exists(p)]
    if stale and a.check:
        sys.exit(f"{stale[0]} is stale: run scripts/checker_prog.py")
    for p in stale:
        if not a.check:
            os.remove(p)
    # modules: every file but the program literal runs an elaborator over the imported program
    # (`meta import`); the inliner's parts' kernel checks unfold `toString` on function names
    # (`Nat.repr`, which `Init.Data.Repr` does not expose); they and the name tree's (`progTree`
    # reads each function's parameter count) unfold the L functions, which are `@[no_expose]`
    # (`import all` of their modules, `lean_module.body_modules`)
    inl_parts = {os.path.join(chk, f"ProgIPart{k}.lean") for k in range(ninl)}
    bodies = lean_module.body_modules(imports + ["ConAgua.Checker.Entry", "ConAgua.Checker.Prelude"])
    outs = [(path, lean_module.modularize(t, meta=path != OUT,
                                          import_all=(["Init.Data.Repr"] if path in inl_parts else [])
                                          + (bodies if path in inl_parts or path == TREE_OUT else [])))
            for path, t in outs]
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
    if not (a.no_build or a.no_closures):
        closures()
    e2e.log("checker.s is now stale: build, then run scripts/asm_file.py and commit the file")


if __name__ == "__main__":
    main()
