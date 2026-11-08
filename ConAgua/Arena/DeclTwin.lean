module

import ConRon.Bridge.Specs
public import ConAgua.Arena.Refine
import ConRon.Bridge.Inductives.Decl
import ConRon.Bridge.Frontend.Capstone
public import ConRon.Bridge.Checker.Decl
public import ConRon.Arena.Checker
public import ConRon.Bridge.Checker.Basis
import ConRon.Bridge.Checker.Fold
import Std.Tactic.BVDecide.Normalize.Prop
public import ConLeche.Verify.EnvBound

@[expose] public section

/-!
# The twin's fold invariant, step by step (lane `decls4`)

The L side compares literal handles where the twin compares literal values (`canon_expr_eq`,
lane `decls3`'s `LitInj`), which is sound because the twin's store is well formed
(`StateOK`: con-ron's `EWFAt.view_inj`). The stage relation `StageR` relates memories to twin
states but says nothing about the twin state's own well-formedness, and no L-side relation can
give it. So the loop carries it on the twin side alone: `TwinFold` is con-ron's
fold invariant (`FoldOK`, unique names, the pins and the records denote, persistence); its step
(con-ron #143: the job's `checkDecl` at the stream index's view) is stage 3's. From it, every state the step's arms start from is
`StateOK` (`TwinFold.stateOK`, `.andPin`, `.enter`).

Pure twin reasoning: no L, no memory.
-/

open ConLeche ConRon.Arena

namespace ConRon.Bridge

/-- A record of a denoting list denotes. -/
theorem denoteDecl_of_mem {st : EStore} :
    ∀ {ds : List IDeclaration} {xs : List Declaration}, denoteDecls st ds = some xs →
      ∀ d ∈ ds, ∃ x, Frontend.denoteDecl st d = some x
  | [], _, _, d, hd => absurd hd (by simp)
  | a :: as, xs, h, d, hd => by
    simp only [denoteDecls] at h
    cases ha : Frontend.denoteDecl st a with
    | none => rw [ha] at h; simp at h
    | some x =>
      cases has : denoteDecls st as with
      | none => rw [ha, has] at h; simp at h
      | some ys =>
        rcases List.mem_cons.mp hd with rfl | hd
        · exact ⟨x, ha⟩
        · exact denoteDecl_of_mem has d hd

/-- A well-formed store hash-conses: two handles with the same view are equal (con-ron's
`EWFAt.view_inj`). This is what makes L's comparison of literal handles the twin's comparison of
literal values (`LitInj`). -/
theorem StateOK.view_inj {a : AState} (h : StateOK a) {x y : EIdx} {v : ENodeView}
    (hx : a.store.view x = some v) (hy : a.store.view y = some v) : x = y := by
  obtain ⟨rk, hw⟩ := h.wf
  exact hw.view_inj hx hy

end ConRon.Bridge

namespace L.Arena

open ConRon.Bridge

/-- **The twin's fold invariant** at a loop head: the state `a`, the environment `fe`, for the pin
list `pins` and the records `ds`. -/
structure TwinFold (pins : List INatOpPinSet) (ds : Array IDeclaration) (fe : IFEnv)
    (a : AState) : Prop where
  fold : ∃ env, FoldOK env fe a ∧ NodupNames env
  pinsD : ∃ pinsP, PinsDenote a.store pins pinsP
  pp : PersPinSets pins
  pd : ∀ x ∈ ds.toList, PersDecl x
  den : ∃ dsP, denoteDecls a.store ds.toList = some dsP
  /-- The scratch tier is off (every step ends in `dropScratch`): the bracket's `enterScratch`
  then changes no denotation (`TwinOK.enter`). -/
  off : a.store.scratchOn = false

/-- **The fold's start, con-ron's `FoldOK` at the empty environment** (`FoldOK_of_start`), from the
twin facts the pipeline has before the fold: `StateOK`, `PinsOK`, `PersPins` and the
per-declaration caches empty. -/
theorem foldOK_start {s : AState} (hok : StateOK s) (hpins : PinsOK s) (hpp : PersPins s)
    (hc : s.caches = Caches.empty) :
    FoldOK Env.empty (mkIFEnv IEnv.empty) s :=
  sorry

/-- **`TwinFold` at the loop's start** (lane `loopt2`, for lane `pipeline`'s R7 → start lemma):
`foldOK_start`, the pins' and records' denotations and persistence, the scratch tier off. -/
theorem TwinFold.start {pins : List INatOpPinSet} {ds : Array IDeclaration} {s : AState}
    (hok : StateOK s) (hpins : PinsOK s) (hpp : PersPins s) (hc : s.caches = Caches.empty)
    (hpd : ∃ pinsP, PinsDenote s.store pins pinsP) (hps : PersPinSets pins)
    (hdp : ∀ x ∈ ds.toList, PersDecl x) (hden : ∃ dsP, denoteDecls s.store ds.toList = some dsP)
    (hoff : s.store.scratchOn = false) : TwinFold pins ds (mkIFEnv IEnv.empty) s :=
  ⟨⟨Env.empty, foldOK_start hok hpins hpp hc, by simp [NodupNames, Env.empty]⟩, hpd, hps, hdp, hden,
    hoff⟩

namespace TwinFold

variable {pins : List INatOpPinSet} {ds : Array IDeclaration} {fe : IFEnv} {a : AState}

theorem stateOK (h : TwinFold pins ds fe a) : StateOK a := by
  obtain ⟨env, hok, -⟩ := h.fold
  exact hok.check.state

theorem pinsOK (h : TwinFold pins ds fe a) : PinsOK a := by
  obtain ⟨env, hok, -⟩ := h.fold
  exact hok.check.pins

/-- Record `i` denotes. -/
theorem denote (h : TwinFold pins ds fe a) {i : Nat} (hi : i < ds.size) :
    ∃ x, Frontend.denoteDecl a.store ds[i] = some x := by
  obtain ⟨dsP, hd⟩ := h.den
  exact denoteDecl_of_mem hd _ (by simp)

/-- After the `And` pin's run, the state is `StateOK`. -/
theorem andPin (h : TwinFold pins ds fe a) {i : Nat} (hi : i < ds.size) {b : Bool}
    {a' : AState} (hrun : andPinOk ds[i] a = .ok (b, a')) : StateOK a' := by
  obtain ⟨x, hx⟩ := h.denote hi
  exact (andPinOk_run h.stateOK h.pinsOK hx hrun).1

/-- The bracket's opening keeps `StateOK`. -/
theorem enter {a a' : AState} (h : StateOK a) (hs : a'.store = a.store.enableScratch) :
    StateOK a' :=
  ⟨hs ▸ EStore.enableScratch_wf h.wf⟩

/-! ## In the `AM.ok`/`AM.st` form the loop's theorems use -/

theorem andPinAM (h : TwinFold pins ds fe a) {i : Nat} (hi : i < ds.size)
    (hok : AM.ok (andPinOk ds[i]) a) : StateOK (AM.st (andPinOk ds[i]) a) :=
  h.andPin hi (AM.run_of_ok _ _ hok)

theorem enterAM {a : AState} (h : StateOK a) :
    StateOK (AM.st enterScratch (AM.st flushCaches a)) :=
  enter h rfl

end TwinFold

end L.Arena
