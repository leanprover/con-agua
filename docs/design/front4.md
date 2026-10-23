# Lane `front4`: the ground hoist's refinement, phase 0/1 leftovers (continues `front3`)

Journal of lane `front4`. Only this lane edits this file.

## Landing 1: `l_model` for callees with several results and Lean-parameter models; the last hoist models

`hoist_targets_go` and `hoist_nat_op_ground` had no generated model (front3, "Open"): they call
`nat_op_deps` (`(o, l) := call …`), whose spec post is `natOpDepsW p n s₀.mem c = some (r, s'.mem)`
with `r` the whole result list, and `natOpDepsW` (like every hand model over `callW p n "…"`)
mentions the program `p`. Two contained extensions of `L/ModelGen.lean`:

* **Several results with the memory.** A callee post `F = some (r, s'.mem)` (`F : Option (List
  Word × Mem)`) is a new callee kind `effL`; the code after the call becomes a continuation over
  `some (r, m₁)` (binder kind 4, `r : List Word`) whose locals are `r.headD 0`, `r.tail.headD 0`,
  … (`St.setLocs`' convention).
* **Lean parameters of the models.** The command's explicit binders that a callee model mentions
  (in practice `p`) become leading parameters of every model and continuation of the group
  (`hTargetsGoW p n m …`, `hTargetsGoW.k3 p n …`); an L local of the same name gets a prime. No
  existing `l_model` call changes: with no callee mentioning a binder, nothing is added.

With both, external callees can be given as `callW_spec p n "f" [args]` (`fun s₀ c => callW_spec p
n "nat_op_deps" [c] s₀` for an argument), so the models speak `callW` and compose directly with the
`CallRef` refinements (`natOpDeps_ref`, `natOpNames_ref`, …). Both new groups needed `gen 20`
(the two-local `setLocs` makes the terms deeper).

`slice_has` (a `while` loop) is now a self-recursion `slice_has(o, l, n, j)`, and it and
`nat_op_record` moved from `Prelude.lean` into `Hoist.lean` (into `hoistProg`), so the whole pass
has models: `sliceHas_spec`, `natOpRecord_spec`, `hoistTargetsGo_spec`, `hoistNatOpGround_spec`.
`hoistExtProg`/`HoistExt` bundle the outside callees (`nat_op_names`, `nat_div_mod_names`,
`nat_op_deps`, `pin_at`, `iw_alloc`). `Hoist.lean` elaborates in ~40 s, peak 2.7 GB.

Census after the landing (worktree, master `109fa860` merged): phase 0 185 proven / 5 written /
106 todo (991 / 1003 / 1305 Lean lines); phase 1c 35 / 36 / 2 (380 / 609 / 625). Of phase 1c's
38 open targets, 27 are the hoist and the prelude driver (`frontOf`, `pick`, `prepareD`,
`preparePrelude`, `preludeKey`, `declares`, `builtinPreludeE`), the rest the ROM interns
(`internCI`, `internCaps`, `internRules`, …, partial) and `internProjTable`/`movedNames` (todo).

## Landing 2: the ground hoist refines `hoistNatOpGround`

`hoistNatOpGround_refines` (`Checker/HoistRef.lean`, `@[refines_part hoistNatOpGround]`: the first
component; `movedNames` is not computed, D30): when `hoist_nat_op_ground(ord, c)` returns `r`, the
twin's `hoistNatOpGround ds` succeeds in the same state, and `IW[r ‥ r + c)` is its records' order
(`OrdR`); the store relation, the pins and `IWOK` survive and the pool only grew. The pieces, each
stated over the generated models (L = model by the generated specs, model ⊑ twin here):

| file | lines | what | by |
|---|---:|---|---|
| `HoistRefBase.lean` | ~100 | `SeenR`, `NixR` (memo ↔ `HashSet`/`HashMap`), `TgtR`, `OrdR`, `RecOK`, `notesW` | lane |
| `HoistWalkRef.lean` + `HoistDecode.lean` | 834 + 188 | walk ⊑ `usedConsts*`: the twin's names, L's notes of them in order | helper `front4-walk` |
| `HoistIndexRef.lean` | 321 | `hoist_index_go` ⊑ `nameIndex`, `hoist_ix` = lookup | helper `front4-index` |
| `HoistOrderRef{,2,3}.lean` | 226 + 358 + 487 | buckets/emit = `mergeSort` by `hoistLt` (unique sorted permutation), `hoist_any` = `isEmpty` | helper `front4-order` |
| `HoistNatRef.lean` | 679 | `nat_op_record` ⊑ `isNatOpRecord`'s test, `nat_op_deps` call ⊑ `natOpDeps` under `IWOK` + `PinsFull` | helper `front4-nat` |
| `HoistClosureTwin.lean` | ~350 | the twin's worklist on a closed set; exactness given reachability | lane |
| `HoistClosureL.lean` | ~830 | L's mark-at-push invariant; `closure_ok`, `deps_ok` | lane |
| `HoistTargetsRef.lean`, `HoistRef.lean` | ~230 + ~280 | the outer loop, the assembly | lane |

**The key lemma, as proved.** The twin's `hoistClosure` is characterised on any set `N` that is
closed (every successor of a member is a member or marked in `T₀`) and whose members' constants it
computes: it succeeds, marks only members, marks the stack, and the result is closed
(`closure_twin`); if moreover every member is reachable from `j` through members, the result is
exactly `T₀ + (N ↦ i)` (`closure_exact`). L's run produces such an `N`: the invariant
(`CloseInv`) is "marked and off the stack ⇒ walked and all successors marked", "marked ⇒
reachable from `j` through marked", "the stack holds distinct marked records" (so it never
overflows its `c` words). `N` = the records L marked; the twin's result equals L's targets
extensionally. The twin's fuel `ds.size` is the count of unmarked members (`pend`).

**Statement fixes found by the helpers** (trunc clears pool word 0): an inductive record's member
pointers must not start at offset 0 nor be 0 (`RecOK`'s kind-6 clause, `BlockAt`); a stored target
`t + 1` must not wrap (`hoist_any` needs `TLt`); `HoistExt` must include `nat_op_pins{,_a,_b,_c}`.

**Preconditions a caller (`prepare_prelude`'s refinement) must establish**: `ArenaR`, some
visited set and some name index represented (all-zero memory does it: `memoRG_zero`), `OrdR` of
the prepared stream (with `RecOK`: handle words `< 2^32`, block offsets and pointers nonzero), no
projection table in a parsed block (`WalkableDecl`), `IWOK`, `ord`'s slice below the pool top,
fewer than `2^60` records, `PinsR`.

Census (worktree): phase 1c 53 proven / 18 written / 2 todo (507 / 609 / 625 Lean lines), was
35 / 36 / 2 (380 / 609 / 625); phase 0 unchanged 185 / 5 / 106 (991 / 1003 / 1305). The hoist's
targets are all proven except `hoistNatOpGround`, `applyHoist` (parts: `movedNames` not computed)
and `movedNames` (todo, D30).

## Landing 3: `prepare_prelude` refines `preparePrelude`

* **L rewritten as self-recursions** (`Checker/Prelude.lean`; the `while` loops gave no model):
  `decl_declares_go`, `prep_find` (`pick`'s `findIdx` over the unmarked stream), `prep_front`
  (`frontOf`), `prep_rest`, `prep_copy{,_rec}`, `prep_back{,_rec}` (the record rewrite, depth `c`,
  not `8 c`); all models generated (`l_model`, in the file, ~20 s). The record bound is now
  `n < 2^59` (was `2^60`; the hoist's `OrdR` needs records below `2^59`, `1 + 8 r` fits a word).
  `Prog.lean`/`AsmPart*` regenerated; e2e (all 675 fixtures, `--jobs 8`): 671 agree (master's
  `docs/e2e.md`: 670), no new disagreement; `natop` 5/5.
* **The twin's array after `pick`'s erasures** is the list of unmarked stream positions mapped
  through the records (`unm`, `recsAt`); marking is erasing (`unm_mark`), `findIdx` on the mapped
  list is the first unmarked declaring position (`findIdx_hit`).
* Merged with lane `pipeline`'s `prelude_join` (the prelude's records now come in `PDECL`):
  its `while` loops are self-recursions too (`prep_shift{,_rec}`, backward per record, depth `ns`;
  `prep_join{,_rec}`), counts bounded by `2^59` each; `pPJoin_ok` (helper `front4-pjoin`).
* `preparePrelude_refines` (`Checker/PrepRef.lean`, `@[refines preparePrelude]`): from `PDECL`
  holding `pre.decls` and `DECL` holding `ds` (counts in word `0`), each record with
  `DeclAtF` + `RecOK` and walkable, `ArenaR`, the hoist's memos represented, `IWOK`, `PinsR`: when
  L returns, `preparePrelude pre ds` succeeds and `DECL` represents its result with the same
  per-record facts; `ArenaR`, `IWOK`, `PinsR` at the twin's state after. `movedNames` is covered
  through it (dropped by `preparePrelude`). Pieces: `PrepLeafRef` (`decl_declares`, `decl_key`
  incl. the anonymous name's interning, `prep_find`; helper `front4-pleaf`), `PrepLoopRef`
  (`prep_front` = `frontOf`, `prep_rest`; helper `front4-ploop`), `PrepCopyRef` (the rewrite;
  helper `front4-pcopy`), `PrepRef` (the assembly, lane).
* For the pipeline lane (`PrepareStage`): the preconditions above are what `R5` must give
  (beyond `StateDR`'s `DeclsF`: `RecOK` and `WalkableDecl` of the parsed records, the hoist's
  two memos represented, e.g. by all-zero arrays 75/76 and `CTL[73‥76]`).

Census (worktree): phase 1c 62 proven / 10 written / 1 todo (545 / 616 / 625 Lean lines); phase 0
185 / 5 / 106 (991 / 1003 / 1305). Left in 1c: `builtinPreludeE`, the ROM interns (`internCI`,
`internCaps`, `internRules`, `internRule`, `internFire`, `internCV`, `internCIList`,
`internExprList`, `internExpr`: parts only), `internProjTable` (todo).

### Open (front4)

* Phase 1c: `builtinPreludeE` (lane `pipeline` rewrote `builtin_prelude`; its `PreludeStage`),
  the ROM interns (`internCI`, `internCaps`, `internRules`, `internRule`, `internFire`, `internCV`,
  `internCIList`: parts only; `internExpr`, `internExprList`: `rom_exprs_to`/`rom_pins_to` have
  models in `Rom/PinReadSpec.lean` but no refinement against the twin's `EMemo`-keyed interning),
  `internProjTable` (todo). Phase 0's five `written` targets are the same ROM interns
  (`internExpr`, `internExprList`, `internCIList`) and two parts (`viewN`, `EStore.dropScratch`);
  the con-leche hash/beq targets of phase 0 are covered once `internExpr*` are proven.
* For `PrepareStage`: `RecOK`/`WalkableDecl` of the parsed records and the hoist memos' relation
  must come from the front's relation (`R5`), see Landing 3.
