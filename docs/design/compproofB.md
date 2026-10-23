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
