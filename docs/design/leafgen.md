# Lane `leafgen`: a better back end for leaf functions (journal)

Branch `leafgen`, worktree `_tmp/wt/leafgen`, scratch `_tmp/leafgen`. Acts on perfgap's cause 1
(docs/design/perfgap.md §4). Phase 1: unproved prototype, numbers, proof plan.

## Prototype

`scripts/leafgen/LGEmit.lean` (run with `lake env lean --run`, `OUT.s FLAGS [LO HI]`): a copy of the
statement/function compiler in namespace `L.Compiler.LG` that reuses everything else of
`Compile.lean` and falls back to the old code wherever the new code does not apply; it prints the
checker exactly as `AsmEmit.lean` (stub included). With no flags the output is byte-identical to
`asm/checker.s`. Flags:

* **G** (`gen`): expressions evaluated straight into a target register (the local's register, the
  result/argument register), temporaries on a register stack (`rax rcx rdx` plus the argument
  registers holding no local); operands in place (memory, imm32, `lea r+k`, `lea r+s`, `imul r, imm`),
  `x := x op e` in place (also on a frame slot), constant indices folded into the address
  (`cmp $k, len; jbe; mov base, t; mov 8k(t), d`), stores of immediates/registers without a move,
  conditions compared in place (`cmp mem, imm`, `cmp reg, mem`, swapped for a constant left operand,
  a bounds-checked word load as the memory operand of the `cmp`), `setcc`+`movzx` for `cmpw`,
  constant-left commutative operands swapped, and one common subexpression per expression/condition
  evaluated once into a spare register (e.g. the hash `k*C ^ (k*C >> 32)`, `(i+1) * (i+1 < n)`).
* **S** (`stk`): leaves (except the entry) skip the stack check; a caller checks for its frame + 8 +
  the largest frame of the leaves it calls (directly or by tail call).
* **B** (`base`): drop a reload of an array base into a register that still holds it within a
  straight-line run.
* **Z** (`zero`): zero only the locals that may be read before assigned (definite assignment over the
  structured body; compopt2's E2).
* **R** (`regs`): leaves keep up to 9 locals in registers (`rbx r12 r13` too). Measured with a
  trampoline that pushes them; lane calleesave (4b7b4313) has since made them free for the compiler.

Tools in `scripts/leafgen/`: `mk.sh` (emit, build, Init count, e2e verdicts), `verd.sh`, `bisect.sh`
(finds the function whose new code changes a verdict), `lprof.py` (`cats`, `cmp`: per-function
counts side by side, `oracle`: leaf/non-leaf totals against perfgap's clang `-fno-inline` counts).

## Numbers (Init `init435.ndjson`, `instructions:u`, exact)

| variant | Init | Δ step | leaf L / gap to clang | non-leaf L / gap |
|---|---:|---:|---:|---:|
| master | 359.04 G | | 202.9 / 79.8 G | 156.1 / 28.7 G |
| conditions in place only | 351.22 G | −7.8 G | | |
| G | 295.70 G | −63.3 G (−17.6%) | 154.4 / 31.2 G | 141.3 / 13.9 G |
| G+S | 291.26 G | −4.4 G (−1.2%) | 149.9 / 26.8 G | 141.3 / 13.9 G |
| G+S+Z | 267.59 G | −23.7 G (−6.6%) | 138.8 / 15.7 G | 128.8 / 1.3 G |
| G+S+Z+R | 263.18 G | −4.4 G (−1.2%) | 134.4 / 11.3 G | 128.8 / 1.3 G |
| G+S+Z+B | 267.02 G | −0.6 G | | |

Hot leaves, instructions per call, master → G+S+Z+R (clang -fno-inline): `der_b` 60.0 → 37.0 (43.1),
`app_find` 110.9 → 64.3 (64.7), `ilm_find` 94.8 → 53.6 (65.4), `ilm_put` 122.2 → 80.1 (60.1),
`app_push` 171.5 → 102.7 (76.7); `mk_app` (non-leaf) 102.7 → 71.1 (67.3).

`bench.py --set full --reps 3 --no-ref` (interleaved, load ~4, `_tmp/leafgen/bench/full.*`), geometric
means vs master: G+S 0.801 instructions / 0.976 cycles / 0.979 wall; G+S+Z 0.741 / 0.931 / 0.943;
G+S+Z+R 0.724 / 0.898 / 0.911 (con-ron 0.670 / 0.987 / 0.943). Init wall: master 22.11 s, G+S 20.65 s,
G+S+Z 19.06 s, G+S+Z+R 18.80 s, con-ron 17.44 s.

Verdicts: e2e fixtures (`verd.sh`) 0 differences for every variant above; `bench.py --set all --reps 0`
(master, G+S, G+S+Z+R): 675 fixtures, 0 disagreements (`_tmp/leafgen/bench/verd_*`).

## Proof plan (for the go/no-go)

`compile_correct`'s statement and the final assumptions stay as they are in every step; all of it is
local to `Compiler/` except Z's L-level lemma.

* **G** (−17.6%). `gen` becomes a total, structural, kernel-evaluable function (no `partial`, no
  hash maps), returning `Option Program`; the old `compileE` stays as the fallback, so every
  existing lemma keeps working. New local lemma `sim_gen`: from `Inv`, the known subexpressions
  (CSE) holding their values in their registers, and the target/scratch registers disjoint from
  the allocation, `rsp rbp r14 r15` (and `rsi` with a tier local): the code sets `d` to the value,
  changes only `d`, the scratch registers and the flags (a post like `SimCall`'s `RPost`), no
  memory; or reaches `ca_error` when L errors. Plus `sim_genCmp` (flags + condition code, incl.
  the swapped forms and the load-as-operand form). Use sites get one new branch each: `set`
  (target register / in place / slot), `st8`/`st64`/`st64t`, `gset`, `ret` (`retDirect`), call
  arguments, conditions. `tempsS` follows the new choices (0 where `gen` applies), so the
  frame-size facts move with it. `Inv`/`AllocOk` unchanged. Estimate ~2000–2500 lines, two
  proof lanes; conditions in place alone (−7.8 G) can go first as a small warm-up.
* **S** (−1.2%). A table of frame sizes (an `NTree` as `Prog.nrt`); unchecked leaves (`sub/add`
  only), callers check `8F + 8 + need` (largest unchecked leaf frame among their callees and tail
  callees). The stack-check contract becomes `FunSim`'s premise `G.lo + needOf f ≤ rsp`
  (0 for checked functions), and the caller's `Inv.lo8` the stronger `G.lo + 8 + need ≤ rsp`,
  discharged at call and tail-call sites. The entry keeps its check: the trampoline and
  `AbiSim` are untouched. ~500 lines, one lane.
* **Z** (−6.6%). An L-level non-interference lemma over the definite-assignment analysis `da`:
  states that differ only in locals not read before assigned run alike (same outcome, memory,
  and the same assigned locals). The compiler then skips their zeroing and starts the simulation
  from the L state with the machine's values. ~600–900 lines, one lane (in `L/` + `SimFun`).
* **R** (−1.2%, −3% wall on top). With lane calleesave's trampoline (4b7b4313) `rbx r12 r13` are
  free: `allocRegs`/`leafAlloc` get them (9 registers), `allocRegs_ne` and the `AllocOk`
  facts follow; callers are never leaves, so call sites are unaffected. ~200 lines.
* **B** (−0.6 G after G+Z): dropped.

Suggested order: R (small), G (conditions first), Z, S. Ordering against verdicts-a: G and
verdicts-a both edit `compileS`'s `abort`/`if c abort` arms and the error jumps in `SimStmt`;
whichever lands second rebases.

## Landings

* **R** (leaves keep locals in `rbx r12 r13` too; `allocRegs = argRegs ++ [rbx, r12, r13]`,
  `argRegs` stays the six argument registers, `leafAlloc` gives non-parameter locals `r13 r12 rbx`
  first). Proofs: `mem_allocRegs`, `argRegs_sub`, nine-way case splits; `compile_correct` and the
  final theorems unchanged. Init 359.13 G → 358.85 G (−0.08%): with the old expression code the
  extra registers barely help (as compproofD measured); the prototype's −4.4 G comes on top of G.
  Verdicts: `bench.py --set all --reps 0`, 675 fixtures, 0 disagreements.
* **G1** (conditions compared in place; helper leafgen-g): `cmpIn` replaces `cmpReg` in `compileC`
  and `compileE`'s `cmpw` (`cmp reg, op`, `cmp mem, imm|reg`, swapped condition code for a constant
  left operand); lemmas `ev_cmpG`, `swapCC_interp` (Step), `sim_cmpIn` (SimExpr). Init 358.87 G →
  350.12 G (−8.75 G, −2.4%). Verdicts: 675 fixtures, 0 disagreements.
