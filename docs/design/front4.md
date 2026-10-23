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
