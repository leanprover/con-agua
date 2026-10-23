# Lane `compproofB`: compopt prototype B, proved (journal)

Branch `compproofB`, worktree `_tmp/wt/compproofB`. Task: port lane `compopt`'s prototype B
(commit bb0e4f8b: per-function result count) onto master (after A+E1) and prove it, so
`compile_correct` stays sorry-free; regenerate the derived output; measure.

## The code generator (`Compile.lean`)

* `Stmt.nret`: the most results a statement returns (its longest `return`). A function sets only
  its first `nret body` results (`Ctx.nr`), at every `return` and when it falls off the end;
  before, every return wrote all `tab.nres` (9 for the checker: 6 registers, 3 table words).
* A call site reads the callee's count `c = nrOf ctx.nrt tab f` and stores results `0 … c-1`
  into `xs.take c` as before; the locals `xs.drop c` it zeroes itself (`zeroVars`,
  `mov qword [rsp+8x], 0`): L gives them `0` (`setLocs` with `headD 0`).
* The trampoline zeroes the results the entry function does not set (`ca_ok`: `loadRes` from
  `c` to `tab.nres`, then `rdx := 0`), so `compile_correct`'s statement (`OutcomeRel`: all
  `tab.nres` results) and everything downstream (Capstone, Final) is unchanged.

**The count lookup.** The prototype looked the callee up in a `List (FnName × Nat)` with
`List.lookup`. The kernel evaluates `compileFn` once per function (`asm_lit`), and a `String`
comparison in the kernel unfolds to UTF-8 byte lists (`WFFast.lean`: ~55 s for ~1300 calls over
~500 functions): with ~1750 functions that is several thousand comparisons per call site. Instead
the counts are an `NTree` keyed by `nameCode` (moved from `WFFast.lean` to `Compile.lean`):
`Prog.nrTree`/`Prog.nrt`, built right to left like `progTree`. `compileProg tab p entry :=
compileProgT tab (Prog.nrt p) p entry`; `compileFn` takes the tree. For the checker, `nrt_lit
checkerNrt : checkerProg` (`WFSplit.lean`, in the generated `Prog.lean`) declares the tree as a
literal and `checkerNrt_eq : Prog.nrt checkerProg = checkerNrt` (one kernel check); `asm_lit` /
`asm_lit_fns` take `checkerNrt`, the per-function checks evaluate `compileFn tab checkerNrt f fd`
(one `nameCode` per call site, then `Nat` comparisons down a tree of depth 27 for 1751
functions), and `checkerAsm_eq` is rewritten with `checkerNrt_eq`.

Result counts of `checkerProg`: 7 functions return nothing, 1225 one result, 306 two, 130 three,
49 four, 21 five, 5 six, 6 eight, 2 nine.

## The proof

* `ResOut G n vs s` (`Rel.lean`) takes the count: results `< n` in the registers / result area,
  and `vs.length ≤ n`. `OutcomeRel` uses `G.tab.nres` (unchanged meaning plus the length bound).
* `NrOk p G ctx s` (`SimStmt.lean`), a new hypothesis of `SimS`: `nret s ≤ ctx.nr`,
  `ctx.nr ≤ tab.nres`, and `nrOf ctx.nrt tab g = nret fd.body` for every function `g` of `p`.
  It passes to the parts of `seq`/`ite`/`while` by `NrOk.sub`. `Conts.ret` gives `ResOut G ctx.nr`.
* `FunSim p G t n`: the callees compiled with tree `t`; the return delivers `ResOut G (nret body)`.
  `funSim` builds the body's `ctx` with `nr := nret body` (`Stmt.nret_le_of_wf`: `≤ tab.nres`).
* `sim_call`: `St.setLocs_take_drop` (with `r.length ≤ c`, `setLocs xs r` = store the first `c`,
  then zero the rest), `sim_storeRes` on `xs.take c`, `sim_zeroVars` on `xs.drop c`.
* `sim_loadRes` gets a second value list `ws` (the results so far; it agrees with `vs` from `i`
  on), for the trampoline, which zeroes results `c …` while `0 … c-1` hold the entry's.
* `compile_correct`: the tree's spec from `Prog.wf`'s distinct names (`Prog.nrTree_spec`,
  `nrOf_nrt`, `NTree.insert_isSome` in `WFFast.lean`); the trampoline's `ca_ok` block.

`compile_correct`, `checker_x64_accepts`, `checkerAsm_accepts`, `checkerAsm_eq`: `propext`,
`Classical.choice`, `Quot.sound`; `checkerAsm_accepts_remaining`: `+ sorryAx`, as before.
About 300 lines of proof changes; the plan (`ResOut` per callee, the lookup fact, `es.length ≤ nret`)
held as compopt estimated. The one new idea was keeping the entry's outcome statement: the
trampoline zeroes the missing results instead of `OutcomeRel` reading fewer.

## Derived output

* `checkerAsm` (master e66ea826 → this branch): 286 646 → 235 406 directives (−18%).
  `harness/check-asm.sh`: OK (checker 216 739 instructions match).
* Kernel checks: `checkerNrt_eq` one check in `Prog.lean`; the ten `AsmPart`s 26–70 s each in
  a parallel full build, as before.
* `scripts/checker_prog.py --check`: up to date (templates: `nrt_lit` in `Prog.lean`,
  `checkerNrt` in `asm_lit_fns`/`asm_lit`).

## Verdicts and performance

`scripts/e2e.py`, branch vs master e66ea826 (both run here): `check` 407 agree-accept /
3 agree-reject / 262 L aborts / 2 timeouts / 1 ref-memout, `check_np` 391/3/278/2/1;
**0 class changes, 0 L verdict changes**; perf column (407 fixtures): L instructions **0.916×**
(0.899–0.944).

`bench.py --set full --reps 3 --no-conron --no-ref` (base = master e66ea826's `checkerAsm`, both
printed by `AsmEmit`; load ~20):

| fixture | base instr | B instr | ratio | base wall | B wall |
|---|---:|---:|---:|---:|---:|
| irrel_commit | 83M | 76M | 0.92 | 0.033 s | 0.033 s |
| long_line_5mib | 1 397M | 1 318M | 0.94 | 0.108 s | 0.104 s |
| c03d_pi_depth_1030 | 4 083M | 3 757M | 0.92 | 0.769 s | 0.778 s |
| let-ladder | 9 209M | 8 569M | 0.93 | 1.51 s | 1.47 s |
| beta-ladder | 17 138M | 15 955M | 0.93 | 3.07 s | 3.00 s |
| c04a_restart_70 | 29 198M | 26 867M | 0.92 | 3.67 s | 3.52 s |
| c05b_nest30_pi1000 | 22 580M | 20 914M | 0.93 | 2.97 s | 2.82 s |
| app-lam | 63 797M | 59 769M | 0.94 | 11.5 s | 11.7 s |
| eager_open_nat_control | 26 000M | 24 055M | 0.93 | 4.08 s | 3.93 s |
| init-prelude | 2 570M | 2 356M | 0.92 | 0.249 s | 0.234 s |
| **Init** (v4.35.0 export) | 453 283M | 417 944M | 0.92 | 40.4 s | 37.9 s |

Geometric mean over 18 fixtures: **0.920× instructions, 0.976× wall**. RSS unchanged.
(compopt measured B on top of A at 0.916× of A's instructions on the default set: as predicted.)

Side effect to note: `scripts/e2e.py` run in a worktree writes the shared
`_tmp/e2e/latest/results.json` (`_tmp` is symlinked): this branch's run overwrote it (rev 752ac52b).
The master baseline run used `--latest ''`.
