# Lane `compproofA`: compopt prototypes A and E1, proved (journal)

Branch `compproofA`, worktree `_tmp/wt/compproofA`. Task: port lane `compopt`'s prototype A
(commit 5e5d8c74: simple right operands in place) and E1 (c79031ff: `x * 2^k` as a shift) onto
master and prove them, so `compile_correct` stays sorry-free; regenerate what depends on the
compiler output; measure.

## The code generator changes (`Compile.lean`)

A right operand that is a variable, a global, an array length or a constant (`simpleOp`) is no
longer evaluated into `rax`, spilled and reloaded:

* `a op b` (`binSimple`): `op rax, [rsp+8x]` / `op rax, [r15+off]` / `op rax, imm32` for add, sub,
  and, or, xor (`aluDirect`), `imul rax, [m]`; `shl/shr rax, imm8` for a constant count;
  otherwise `mov rcx, b` (`loadInto`) and the old `binCode`.
* `x * k` with `k = 2^n` (E1): `shl rax, n`. The prototype's test `k != 0 && k &&& (k-1) == 0`
  became `k.toNat == 2 ^ Nat.log2 k.toNat` (same functions, direct to prove).
* comparisons (`cmpSimple`, in `compileE`'s `cmpw` and `compileC`'s `cmp`): `cmp rax, [m]` /
  `cmp rax, imm32`, else `mov rcx, b; cmp rax, rcx`.
* `x := x op k` (`setInPlace`; add, sub, and, or, xor, imm32): one read-modify-write
  `op qword [rsp+8x], imm32`.
* `A[i] := e` with a simple `e`: `mov rdx, e` after `i`, no temporary.

The immediates are written `.imm (.int64 w.toInt64)` (the prototype had `oI w.toInt64.toInt`, the
same value): that is `movRI`'s form, so the immediate case of the proofs is `ev_movRI`'s.
`binDirect` reuses `aluDirect` (also `setInPlace`'s); the emitted code is the prototype's.

## The proof

`Inv` unchanged, as compopt estimated. New:

* `Step.lean`: `OpReads s o v` (an immediate `v`, or a mapped `[b+off]` holding `v`);
  `ev_movRO`, `ev_binO` (the `binDirect` forms), `ev_cmpO`, `ev_shiftI` (shl/shr imm8,
  `imm8_count`), `ev_aluMI` (RMW on memory with an immediate; `ev_flags_mem`).
* `SimExpr.lean`: `simpleOp_reads` (a simple operand reads `evalP σ b`), `sim_loadInto`,
  `sim_binCode`, `sim_binSimple`, `sim_cmpSimple` (each: `∃ vb, evalP σ b = .ok vb ∧` a
  continuation-passing simulation), arithmetic `shl_mod64`, `shr_mod64`, `shl_log2`; one new
  branch each in `sim_expr` (`bin`, `cmpw`) and `sim_cond` (`cmp`).
* `SimStmt.lean`: `sim_set`'s in-place branch.
* `SimStore.lean`: the bounds check and store of `sim_st8`/`sim_st64` became `sim_st8_tail`/
  `sim_st64_tail` (from `rax = i`, `rdx = e`), shared by the old path and the `mov rdx, e` one.

About 450 lines; `compile_correct`: `propext`, `Classical.choice`, `Quot.sound`.
