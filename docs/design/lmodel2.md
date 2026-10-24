# Lane `lmodel2`: `l_model` for several results and loops (journal)

Branch `lmodel2`, worktree `_tmp/wt/lmodel2`. Goal: extend the `l_model` generator
(`ConAgua/L/ModelGen.lean`, lane `modelgen`, docs/design/modelgen.md) so that it covers functions
with several results and functions with loops (38 % of the L functions it cannot take today,
docs/design/shrink.md, batch 2), measure it on 10–20 representative functions, and propose a
retrofit plan. Phase 1: generator and measurements only, no mass retrofit.

## Status

Phase 1 in progress. Development copy `ConAgua/L/ModelGenDev.lean` (command `l_model2`, so the
master `l_model` families keep their cached build); folded back into `ModelGen.lean` before
landing.

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
* Not supported (error): nested loops, a loop that calls a member of its own group (the loop
  spec would need the group's induction hypothesis at every smaller fuel).

### Smaller changes

* `st64`, `setG` in the default `vcgen` lemmas (stores and global writes; `extra [L.st64]` is
  no longer needed); numerals in bit operations typed `(k : L.Word)`.
* `sym "(gen := 80) (instances := 5000)"`: options for `sym` (a function with many callees,
  `lds_both`).

## Measurements

Method: a retrofit of the real file in a scratch copy (`_tmp/lmodel2/r/`): the hand model, its
continuations, equations, patterns, loop spec and function spec replaced by one `l_model2`, the
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

(in progress)

## Log

* 2026-10-24: survey; several results (list, tuple), loops, SCC emission; tests on
  `block_rec_want`, `defeq_lst`, `infer_pis_leaf`, `app_fill`, `dec_len`, `reserved_contains`,
  `head_hint`, `lds_both`.
