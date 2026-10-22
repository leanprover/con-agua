import ConRon.Bridge.Checker.Split
import ConRon.Bridge.Inductives.Decl

/-!
# The twin's fold invariant, step by step (lane `decls4`)

The L side compares literal handles where the twin compares literal values (`canon_expr_eq`,
lane `decls3`'s `LitInj`), which is sound because the twin's store is well formed
(`StateOK`: con-ron's `EWFAt.view_inj`). The stage relation `StageR` relates memories to twin
states but says nothing about the twin state's own well-formedness, and no L-side relation can
give it. So the loop carries it on the twin side alone: `TwinFold` is con-ron's
`installFold_bridge` induction invariant (`FoldOK`, unique names, the pins and the records
denote, persistence), and `TwinFold.step` is that induction's step (`installStep_split`), applied
to the twin run the L step refines. From it, every state the step's arms start from is
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

end ConRon.Bridge

namespace L.Arena

open ConRon.Bridge

/-- **The twin's fold invariant** at a loop head: the state `a`, the environment `fe`, the pending
records `pend`, for the pin list `pins` and the records `ds` (con-ron's `installFold_bridge`
hypotheses, the pending relation weakened to persistence). -/
structure TwinFold (pins : List INatOpPinSet) (ds : Array IDeclaration) (fe : IFEnv)
    (pend : Array PendingCheck) (a : AState) : Prop where
  fold : ∃ env, FoldOK .verified env fe a ∧ NodupNames env
  pinsD : ∃ pinsP, PinsDenote a.store pins pinsP
  pp : PersPinSets pins
  pd : ∀ x ∈ ds.toList, PersDecl x
  den : ∃ dsP, denoteDecls a.store ds.toList = some dsP
  pend : ∀ pc ∈ pend.toList, PersVG pc.vg

namespace TwinFold

variable {pins : List INatOpPinSet} {ds : Array IDeclaration} {fe : IFEnv}
  {pend : Array PendingCheck} {a : AState}

theorem stateOK (h : TwinFold pins ds fe pend a) : StateOK a := by
  obtain ⟨env, hok, -⟩ := h.fold
  exact hok.check.state

theorem pinsOK (h : TwinFold pins ds fe pend a) : PinsOK a := by
  obtain ⟨env, hok, -⟩ := h.fold
  exact hok.check.pins

/-- Record `i` denotes. -/
theorem denote (h : TwinFold pins ds fe pend a) {i : Nat} (hi : i < ds.size) :
    ∃ x, Frontend.denoteDecl a.store ds[i] = some x := by
  obtain ⟨dsP, hd⟩ := h.den
  exact denoteDecl_of_mem hd _ (by simp)

/-- After the `And` pin's run, the state is `StateOK`. -/
theorem andPin (h : TwinFold pins ds fe pend a) {i : Nat} (hi : i < ds.size) {b : Bool}
    {a' : AState} (hrun : andPinOk ds[i] a = .ok (b, a')) : StateOK a' := by
  obtain ⟨x, hx⟩ := h.denote hi
  exact (andPinOk_run h.stateOK h.pinsOK hx hrun).1

/-- The bracket's opening keeps `StateOK`. -/
theorem enter {a a' : AState} (h : StateOK a) (hs : a'.store = a.store.enableScratch) :
    StateOK a' :=
  ⟨hs ▸ EStore.enableScratch_wf h.wf⟩

/-- **The fold's step**: an accepting `installDeclStep` on record `i` keeps the invariant. -/
theorem step (h : TwinFold pins ds fe pend a) {i : Nat} (hi : i < ds.size) {k : Nat}
    {fe' : IFEnv} {pend' : Array PendingCheck} {a' : AState}
    (hrun : installDeclStep .verified pins (i, fe, pend) ds[i] a = .ok (.ok (k, fe', pend'), a')) :
    TwinFold pins ds fe' pend' a' := by
  have hk : CoreSpec .verified ConRon.Arena.checkFuel := CoreSpec.of_core rfl
  have hind : IndSpec .verified := ConRon.Bridge.Inductives.indSpec_of_bridge rfl hk
  obtain ⟨env, hok, hnd⟩ := h.fold
  obtain ⟨pinsP, hpins⟩ := h.pinsD
  obtain ⟨dsP, hden⟩ := h.den
  obtain ⟨x, ha⟩ := h.denote hi
  have hmem : ds[i] ∈ ds.toList := by simp
  simp only [installDeclStep] at hrun
  cases hP : andPinOk ds[i] a with
  | error e => rw [hP] at hrun; simp at hrun
  | ok w =>
  obtain ⟨bA, s₀⟩ := w
  cases bA with
  | false => rw [hP] at hrun; simp at hrun
  | true =>
  rw [hP] at hrun
  simp only at hrun
  obtain ⟨hok0, hx0, hc0, hp0⟩ := andPinOk_run hok.check.state hok.check.pins ha hP
  have hok' : FoldOK .verified env fe s₀ := hok.step (hok.check.mono hok0 hx0 hc0 hp0) hx0 hp0
  have hx0' : PExt a.store s₀.store := PExt.of_ext hx0
  have hpins0 := PinsDenote.pmono hx0' _ _ h.pp hpins
  have ha0 : Frontend.denoteDecl s₀.store ds[i] = some x := denoteDecl_pext hx0' (h.pd _ hmem) ha
  cases hA : installStep .verified pins i fe pend ds[i] s₀ with
  | error e => rw [hA] at hrun; simp at hrun
  | ok v =>
  obtain ⟨⟨fe₁, pend₁⟩, s₁⟩ := v
  rw [hA] at hrun
  simp only [Except.ok.injEq, Prod.mk.injEq] at hrun
  obtain ⟨⟨-, rfl, rfl⟩, rfl⟩ := hrun
  obtain ⟨env₁, hok₁, hx₁', -, hpend₁, -, -, hcase⟩ :=
    Arena.installStep_split rfl hk hind hok' hnd hpins0 h.pp h.pend (h.pd _ hmem) ha0 hA
  have hx₁ : PExt a.store s₁.store := hx0'.trans hx₁'
  have hnd₁ : NodupNames env₁ := by
    rcases hcase with ⟨-, F, hF⟩ | ⟨pc, gP, F, -, -, -, hsplit, -⟩
    · exact checkDecl_nodup hF hnd
    · exact hsplit.nodup hnd
  exact ⟨⟨env₁, hok₁, hnd₁⟩, ⟨pinsP, PinsDenote.pmono hx₁ _ _ h.pp hpins⟩, h.pp, h.pd,
    ⟨dsP, denoteDecls_pext hx₁ _ _ h.pd hden⟩, hpend₁⟩

end TwinFold

end L.Arena
