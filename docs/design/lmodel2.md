# Lane `lmodel2`: `l_model` for several results and loops (journal)

Branch `lmodel2`, worktree `_tmp/wt/lmodel2`. Goal: extend the `l_model` generator
(`ConAgua/L/ModelGen.lean`, lane `modelgen`, docs/design/modelgen.md) so that it covers functions
with several results and functions with loops (38 % of the L functions it cannot take today,
docs/design/shrink.md, batch 2), measure it on 10–20 representative functions, and propose a
retrofit plan. Phase 1: generator and measurements only, no mass retrofit.

## Status

Phase 1 done: the generator (`ConAgua/L/ModelGen.lean`) takes several results, loops, inline
binds; measured on 23 functions in 8 files (scratch retrofits, not landed); retrofit plan below,
waiting for the coordinator's OK. Developed as a copy `ModelGenDev.lean` (`l_model2`), folded back.

## Survey (master `9411dbf2`)

* 1485 `lfn`s, 163 named blocks (`lblk`); 143 blocks are a single `while`, 20 have no loop.
  162 functions have a loop (33 written in the `lfn`, the rest a spliced named block);
  440 return `(a, b, …)`; 56 both.
* 180 loops: 117 call a function, 84 contain a `return`, 64 store, 5 `break`, 2 nested.
* Hand loop specs (113 theorems on `exec p n <block>`) come in two shapes:
  * the loop ends normally: `r = .normal ∧ s'.loc j = s₀.loc j ∧ … ∧
    W n s₀.mem (s₀.loc i) … = some (s'.loc a, s'.loc b, s'.mem)` (`pisLoop`, `spLoop`,
    `lamsLoop`, `isW`, `epW`, …), or `= some s'.mem` when only the memory changes;
  * the loop returns: `r ≠ .brk ∧ W n s₀.mem … = some ((r.retOr [0]).headD 0, s'.mem) ∧
    r ≠ .normal` (`lstW`, `peelW`, `whnfLoopW`, `coreLoopW`), or `r.retOr d = […]` for pure ones.
  Models are by L fuel, `exec` convention: `| 0 => none | k + 1 => if c then … W k … else exit`,
  locals as arguments in local order, the memory first.
* Hand multi-result models: list form `Option (List Word × Mem)` with spec
  `W … = some (r, s'.mem)` (771 `some ([a, b], m)` leaves in 134 files) is far more common than the
  tuple form `Option (Word × Word × Mem)` with spec `= some (r.headD 0, r.tail.headD 0, s'.mem)`
  (36 files).

## Design

### Several results

* A function with a `return (a, b, …)` gets a **list model** `Option (List Word × Mem)`;
  `return e` is `some ([e], m)`, falling off the end `some ([], m)` (exactly `r.retVal`).
  Spec: `LocEq s' s₀ ∧ fW n s₀.mem args = some (r, s'.mem)` (read-only: `Option (List Word)`,
  `s'.mem = s₀.mem ∧ fW … = some r`). `↦ fW list` forces the list form for a one-result function.
* `↦ fW tuple`: a **tuple model** `Option (Word × … × Mem)` (arity: the longest `return`; shorter
  returns padded with `0`), spec `fW … = some (r.headD 0, r.tail.headD 0, …, s'.mem)`, for
  retrofits onto hand tuple models.
* Callees: list posts (`F = some (r, s'.mem)`, already read), read-only lists (`F = some r`),
  tuple posts (`F = some (r.headD 0, r.tail.headD 0, …[, s'.mem])`); a spec over any argument
  list (`callW_spec p n "f"`, `callF_spec`: `invoke … f vs`) is read with `vs` as the call's
  argument list. A tuple callee's continuation binds `some (r₀, r₁, …, m₁)`.

### Loops

* `while c { body }; rest` (in the `lfn`, or a spliced named block `⟪X⟫` whose body is one
  `while`) becomes a **loop model** `fW.loopᵢ n m x₁ … xₖ` in the `exec` convention of the hand
  loop models: `| 0 => none | n + 1 => if c then body else exit`, the next iteration
  `fW.loopᵢ n …`; the enclosing code applies it at `n + 1` (`step p (exec p n) w =
  exec p (n + 1) w`).
* Its arguments: the locals live at the loop head (read before written, a fixpoint over the
  body), in local order, after the memory. Its result: `(signal, outs…, memory)`: the signal
  (`Sig.normal`/`Sig.ret vs`) only if the body has a `return`; the outs are the locals the loop
  assigns that `rest` reads; no memory in a read-only model.
* `rest` is a continuation `fW.kⱼ` of the loop's result (as after a call); with a signal:
  `if r = Sig.normal then rest else <return r.retVal>`. `break` is the exit leaf.
* **Loop spec** `fW.loopᵢ.spec`: `⦃s = s₀⦄ exec p n X ⦃r = .normal (or r ≠ .brk) ∧
  s'.loc j = s₀.loc j (the locals rest reads that the loop does not assign) ∧ [s'.mem = s₀.mem] ∧
  fW.loopᵢ n s₀.mem (s₀.loc i) … = some ([r,] s'.loc o …[, s'.mem])⦄`, by induction on `n`:
  `rw [exec, step_while rfl]; sym => vcgen [step, …, callee specs, ih] <;> finish`. The model is
  the loop's meaning: no invariant. The function's step gets
  `fun s => Triple.step_exec (fW.loopᵢ.spec … (n + 1) s)`.
* A `while` written in the `lfn` becomes a named block `fW.loopᵢ.stmt := lblk (vars) { while … }`
  and `fW.lfn_eq : F = lfn … { … ⟪fW.loopᵢ.stmt⟫ … } := rfl` (so `vcgen` sees a constant, not a
  `.while`, and uses the loop spec). Named blocks without a loop are inlined.
* **Definitions in dependency order**: each strongly connected component of the reference graph
  is one definition or `mutual` block; well-founded on `(fuel, depth)` if it has a continuation
  or loop (models `(n, D)`, continuations `(n + 1, d)`, loops `(n, d)`, `d` below the depth of
  every continuation that applies it), structural on the fuel if only models.
* **Fused exit**: a loop with a `return`, followed by the function's last statement (`return e…`
  or `abort`), returns the function's result directly (no signal, no continuation): its exit leaf
  is that statement, its spec `r ≠ .brk ∧ [r ≠ .normal] ∧ fW.loopᵢ n s₀.mem … =
  some ((r.retOr [e…(s')]).headD 0, s'.mem)` (the results of `return e…` over the final state).
  This is the shape of the hand returning-loop models (`lstW`, `pirW`, `rcLoopW`), and makes their
  retrofit a rename.
* Not supported (error): nested loops, a loop that calls a member of its own group (the loop
  spec would need the group's induction hypothesis at every smaller fuel).

### Smaller changes

* `st64`, `setG` in the default `vcgen` lemmas (stores and global writes; `extra [L.st64]` is
  no longer needed); numerals in bit operations typed `(k : L.Word)`.
* `sym "(gen := 80) (instances := 5000)"`: options for `sym`; `instances N` for `finish` (a
  function with many callees on one path, `lds_both`, the `Decl*` certificates).
* `fW.abortᵢ` (one per `none` leaf: the path conditions imply `none`) and `fW.kᵢ.none` (a
  continuation of a failed call is `none`): what refinements use to dismiss abort paths (the hand
  files have them as `…_ab1`, `…_none`, or `simp [model, conds]`).
* **`bind c`** (`bind ntBW`): the code after a call with several results is an inline continuation
  `c (call) fun ρᵢ μᵢ => …` instead of a named `fW.kᵢ`. This reproduces the hand models of the
  `Decl*`/`Rom` families (418 `ntBW (callW …)` binds in ~25 files), whose refinements are
  `Sim.ntB` chains over exactly that shape.
* The `lfn` (and `lblk`) text is found after `:=` followed by any white space (`:=\n    lfn`).

## Measurements

Method: a retrofit of the real file in a scratch copy (`_tmp/lmodel2/r/`): the hand model, its
continuations, equations, patterns, loop spec and function spec replaced by one `l_model2` (the development name of `l_model`), the
refinements in the same file adapted until the file elaborates. Lines: non-blank, whole file.
Cost: `perf stat -e instructions:u` of `lake env lean <file>` (one run; the import baseline,
2.7 G, is in both). Churn: lines of the kept declarations (refinements) that changed.

| file | functions (kind) | lines before → after | churn (kept decls) | G instr before → after | max RSS |
|---|---|---:|---:|---:|---|
| `DefEqMidLoops` | `defeq_lst`, `defeq_list_rev` (returning loops, `callW`) | 389 → 288 (−101) | 16 of 191 | 37.3 → 26.5 | equal |
| `InferBodyBindPi` | `infer_pis_leaf` (loop with outs, 5 callees) | 780 → 724 (−56) | 17 of 165 | 81.6 → 88.2 | +50 MB |
| `IndPartsSpec10` | `block_rec_want`, `block_rec_got` (several results, recursive) | 361 → 302 (−59) | 10 of 76 | 27.7 → 23.7 | equal |
| `DefEqLeaves` | `head_hint` (tuple, 2 callees, aborts) | 1164 → 1117 (−47) | 12 of 62 | 280.7 → 276.8 | equal |
| `WhnfM2CRefine` | `reserved_contains` (returning loop, list) | 677 → 628 (−49) | 9 of 84 | 109.7 → 109.8 | equal |
| `WhnfIotaRefine` | `pi_residual` (returning loop with outs, list) | 984 → 930 (−54) | 10 of 107 | 61.1 → 61.9 | equal |
| `DefEqMidLazy` | `lds_both` (tuple, 5 callees) | 792 → 744 (−48) | 13 of 96 | 217.3 → 250.6 | equal |
| `DeclDivMod4` | 14 certificate functions (list, `bind ntBW`) | 622 → 426 (−196) | 42 of 268 | 382.4 → 389.2 | +90 MB |
| **total** | **23 functions, 8 files** | **5769 → 5159 (−610, −11 %)** | **129 of 1049 (12 %)** | **1198 → 1227 (+2.4 %)** | |

Per function: −46 lines on average for named-continuation families (−30 … −56), −14 for the
`bind` family (whose hand models were already compact `ntBW` chains). The refinements keep their
size (+11 lines in all) and change in ~12 % of their lines, almost all renames: `fW_exit` →
`fW.loop1.arm1`, `cases hc … rw [hc] at h; cases h` → `rw [hc, fW.kᵢ.none] at h; cases h`, the
callee's own fuel (`spec p hp n` → `spec p hp (n + 1)`, the hand specs were stated at `n + 1`
with the model at `n`), and in `bind` refinements `unfold fW` → `rw [fW.eq_2]` (scripted for all
14 of `DeclDivMod4`). Cost: the generated proofs are as fast as the hand ones within ±10 % per
file, except where one step theorem checks many callees on one path (`lds_both` +15 % of its
file: the hand proof had extra hints); memory unchanged.

What made retrofits cheap: the generated model's shape equals the hand one (fused loop exits,
list/tuple results as the hand models had them, `bind` for `ntBW` chains, argument order = local
order, which is what the hand loop models used). What will make them expensive (seen while
choosing the sample, not retrofitted):
* hand loop models **without fuel** (`findRuleW` by a step bound `K`, `chunkN`/`madW` in
  `Front/NatDec` by well-founded recursion): the refinement's induction changes (from the bound to
  the fuel);
* hand models that **model array bounds** of stores (`pisLoop`'s `tPushOK`, a guard the generated
  model does not have): the refinement must get the bounds from an invariant;
* hand models that **share helper continuations** across functions (`llK3`) or fold code into
  named memory functions (`tPush`): renames in every user, or a `fold` for memory functions;
* models **read by other files** (2-file models: one more file to rename; 3+ files: a cascade).

## Inventory and retrofit plan

`_tmp/lmodel2/candidates.py` (heuristic: the spec theorem of each L function, its model, the
files that mention the model): of the 544 functions with a loop or several results,

| spec of the function | functions |
|---|---:|
| word model read in 1 file (the spec's own) | 134 |
| word model read in 2 files | 95 |
| word model read in 3+ files | 137 |
| refinement-style post, no word model (scanner/front loops spec'd against `Nat` functions) | 85 |
| no spec found by the heuristic | 87 |

1- and 2-file models by family (where the model lives): IndInstall 18, RecGen 16, DeclDivMod 14,
IndParts 14 (+19 in 3+ files), RecClass* ~30, WhnfDelta 11, RecCheck 10, DeclNatEq 9,
DefEqMidLazy 7, WhnfIota(+Rec) 13, WhnfSpineArgs 6, WhnfCoreProj 5, DefEqMidLams 4,
DefEqMid/Loops/Peel/Leaves 9, InferBodyBind* 4, Rom/CIReadRef 3, smaller ones ~40.

Expected saving: ~230 functions with 1- or 2-file models × ~40 lines ≈ **9k lines** (−14 per
function for the ~35 `bind` ones, −46 for the rest), the refinements unchanged in size; the 137
3+-file models perhaps 3–5k more, only where a family is rewritten anyway.

Proposed order (each batch one landing per family, helpers by file, ≤ 3 at a time):
1. **Land the generator** (this branch; no retrofit; the existing `l_model` families build
   unchanged).
2. **R1, `bind` families** (`DeclDivMod*`, `DeclNat*`, `Rom/CIReadRefW`, ~40 functions): the
   retrofit is scripted (`_tmp/lmodel2` regex: model + spec → `l_model … bind ntBW`, `CallRef.of_sim`
   at `k + 1`, `unfold fW` → `rw [fW.eq_2]`); ~−0.6k lines, low risk.
3. **R2, `DefEq*`/`Whnf*`/`Infer*` 1-file models** (~70 functions): renames as in the sample;
   ~−3k lines.
4. **R3, `Ind*`/`Rec*`** (IndInstall, IndParts, RecGen, RecCheck, RecClass*; many 2-file
   models): ~−4k lines.
5. The rest, and 3+-file models only together with other work on their family.
Skip (or do last, by hand): fuel-free loop models, models with store bounds, `memoFindG`-style
parameterised functions (not supported).

Generator work that would make R2/R3 cheaper (each small):
* hypotheses of negative branches in their natural form (`a = b` for `¬ (a ≠ b)`): today a
  refinement passes `not_not_intro h` (changes the existing families' arm statements, so best
  done together with their next edit);
* continuations named after the call they follow (`fW.k_head_hint`), so a code change does not
  renumber `kᵢ` in refinements;
* loops that call their own group (strong induction over the fuel) — none in the sample.

## Log

* 2026-10-24: survey; several results (list, tuple), loops, SCC emission; tests on
  `block_rec_want`, `defeq_lst`, `infer_pis_leaf`, `app_fill`, `dec_len`, `reserved_contains`,
  `head_hint`, `lds_both`; fused loop exits, abort/none lemmas, `bind`; scratch retrofits of 8
  files (23 functions); folded into `ModelGen.lean`; full build of `ConAgua` passes before and after merging master
  (tieracc batch 2), the existing `l_model` families unchanged. The scratch copies with the
  final `l_model` (`_tmp/lmodel2/final/`) still elaborate where master did not change the file
  meanwhile (`DeclDivMod4`, `DefEqMidLazy`, `DefEqMidLoops`, `IndPartsSpec10`); the other four are
  stale against master's newer refinements, not against the generator.
