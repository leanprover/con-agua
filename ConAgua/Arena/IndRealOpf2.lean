import ConAgua.Arena.IndRealOpf
import ConAgua.Arena.IndRealAbs

/-!
# `open_pis_at_fvars_f`'s callees under the stage relation (lane `indproofs4`, helper `opf`)

Each callee of `opf_go`/`opa_go` in `opfP`, from `StageR ∧ AbsOK`, is the twin's step with
`StageR ∧ AbsOK` after, and leaves the spine stack and its top alone (or, `spn_push`, pushes):

* `opfV_ok`: `e_view` at a `∀` is the twin's `view` (memory kept);
* `opfIl_ok`: `inst_list` is `instantiateListFast coreWalkFuel` under `ArenaL`, its memo from
  `AbsOK`'s `IlMemo` (the twin clears `instLC` at entry: the run from `a` is the run from `a` with
  any memo), `IlMemo` again after;
* `opfFv_ok`: `intern_fvar` is `internE (.fvar …)` (`internFVar_stage`);
* `opfI1_ok`: `inst_entry` is `instantiate1Fast coreWalkFuel` (as `i1F_ok`);
* `spnPushW_ok`: the push, the stage relation by its frame.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem opfP_il : InstListProg opfP := (ProgHas.refl opfP).left.right.left

theorem opfP_inst : L.Arena.InstProg opfP :=
  ⟨by unfold LiftProg liftProgFns; repeat (first | exact ProgHas.nil | refine ProgHas.cons rfl ?_),
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

section
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

theorem opf_view_run {a : AState} {h : EIdx} {v : ENodeView} (hv : a.store.view h = some v) :
    (view h).run a = .ok (v, a) := by
  simp [view, hv, StateT.run_bind, StateT.run_get]; rfl

/-- **`e_view` at a `∀`**: the memory kept, the binder's words, the twin's `view`. -/
theorem opfV_ok {k : Nat} {m m' : Mem} {a : AState} (hS : StageR dn vis fe m a) {e : Word}
    (hg : e >>> 28 = 6) {r : List Word} (hc : callW opfP k "e_view" [e] m = some (r, m')) :
    m' = m ∧ (r.tail.headD 0).toNat < 2 ^ 32 ∧ (r.tail.tail.headD 0).toNat < 2 ^ 32 ∧
      (view (decE e)).run a = .ok (.forallE (decE (r.tail.headD 0)) (decE (r.tail.tail.headD 0)), a) := by
  obtain ⟨s', hm, hs', hne, hr⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (eView_spec opfP rfl k ⟨m, Locals.init []⟩ e) hc
  subst hs'
  simp only at hr hm
  subst hr hm
  obtain ⟨v, hv, hvr⟩ := eViewW_ok m a hS.1.arena.1 e hne
  obtain ⟨-, hw⟩ := eViewW_forall m e hg hne
  rw [hw] at hvr ⊢
  generalize tfld m FORALL (tierW e) (idxW e) 0 = x at hvr ⊢
  generalize tfld m FORALL (tierW e) (idxW e) 1 = y at hvr ⊢
  refine ⟨rfl, ?_⟩
  cases v <;> simp [ViewR] at hvr
  simp only [List.tail_cons, List.headD_cons]
  exact ⟨hvr.1, hvr.2.2.1, by rw [opf_view_run hv, hvr.2.1, hvr.2.2.2]⟩

/-- The writers below array 64 keep the spine stack and its top. -/
theorem spn_of_lt64 {A : List ArrId} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, b < 64 ∨ (256 ≤ b ∧ b < 320)) (hC : ∀ x ∈ C, x.toNat < 64) :
    m'.arr64 SPN = m.arr64 SPN ∧ rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 :=
  ⟨hf.1 SPN (fun h => by have := hA _ h; simp [SPN] at this) (by decide),
    hf.2.1 136 (fun h => by have := hC _ h; simp at this)⟩

/-- **`inst_list` under the stage relation and `AbsOK`.** -/
theorem opfIl_ok {k : Nat} {m m' : Mem} {a : AState} (hS : StageR dn vis fe m a) (hAb : AbsOK m)
    {e o l d : Word} {vs : Array EIdx} (hsl : SpineR m o l vs) (he : e.toNat < 2 ^ 32)
    {r : List Word} (hc : callW opfP k "inst_list" [e, o, l, d] m = some (r, m')) :
    ∃ a', (instantiateListFast coreWalkFuel (decE e) vs d.toNat).run a = .ok (decE (r.headD 0), a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ AbsOK m' ∧ m'.arr64 SPN = m.arr64 SPN ∧
      rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 ∧ (r.headD 0).toNat < 2 ^ 32 := by
  rcases k with _ | k
  · rw [callW_zero] at hc; cases hc
  obtain ⟨mp, hmp⟩ := hAb.2.2.2.1
  have hA : ArenaL m (withLLC a mp) := ⟨hS.1.arena.withLLC mp, hmp⟩
  have hbd : o.toNat + l.toNat < 2 ^ 64 := by
    have := hsl.bound; have := hAb.2.2.2.2.2.2.1; omega
  obtain ⟨s', hs', -, hok, hA', hres, -, hlt⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (instList_refines opfP opfP_il rfl k _ _ hA e o l d vs hsl hbd he) hc
  rw [hs'] at hA'
  have hfr : MemFrame instListA instListC m m' := instList_frame opfP_il rfl (run_of_callW hc)
  have hrun0 := AM.run_of_ok _ _ hok
  have hrun : (instantiateListFast coreWalkFuel (decE e) vs d.toNat).run a =
      .ok (AM.res (instantiateListFast coreWalkFuel (decE e) vs d.toNat) (withLLC a mp),
        AM.st (instantiateListFast coreWalkFuel (decE e) vs d.toNat) (withLLC a mp)) := by
    rw [← hrun0]; rfl
  have hk := Keeps.run (keepsW_instListFast coreWalkFuel (decE e) vs d.toNat).cp_of_cpl hrun
  obtain ⟨hS', hg⟩ := StageR.of_walk hS hA'.1 hfr (lt64A_of_all rfl) (lt64_of_all rfl) hk
  obtain ⟨h1, h2⟩ := spn_of_lt64 hfr (lt64A_of_all rfl) (lt64_of_all rfl)
  refine ⟨_, by rw [hrun, hres], hS', hg, ?_, h1, h2, hlt⟩
  exact ⟨hAb.1.frame hfr (by decide) (by decide), hAb.2.1.frame hfr (by decide) (by decide),
    hAb.2.2.1.frame hfr (by decide) (by decide), ⟨_, hA'.2⟩,
    hAb.2.2.2.2.frame hfr (by decide) (by decide) (by decide) (by decide) (by decide)⟩

/-- **`intern_fvar` under the stage relation and `AbsOK`.** -/
theorem opfFv_ok {k : Nat} {m m' : Mem} {a : AState} (hS : StageR dn vis fe m a) (hAb : AbsOK m)
    {u ty : Word} (hty : ty.toNat < 2 ^ 32) {r : List Word}
    (hc : callW opfP k "intern_fvar" [u, ty] m = some (r, m')) :
    ∃ a', (internE (.fvar u.toNat (decE ty))).run a = .ok (decE (r.headD 0), a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ AbsOK m' ∧ m'.arr64 SPN = m.arr64 SPN ∧
      rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 ∧ (r.headD 0).toNat < 2 ^ 32 := by
  obtain ⟨s', hs', -, hI⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (internFVar_spec opfP rfl rfl rfl k ⟨m, Locals.init []⟩ u ty) hc
  rw [hs'] at hI
  have hfr := fvinternW_frame m u ty _ _ hI
  obtain ⟨a', hrun, hS', hg⟩ := internFVar_stage hS u ty hty hI
  obtain ⟨h1, h2⟩ := spn_of_lt64 hfr (by simp [FVREC, FVSLOT, FVLP]) (by simp)
  exact ⟨a', hrun, hS', hg, hAb.frameD hfr (by decide) (by decide), h1, h2,
    fvinternW_hw m a hS.1.arena.1.fvar u ty _ _ hI⟩

/-- **`inst_entry` under the stage relation and `AbsOK`.** -/
theorem opfI1_ok {k : Nat} {m m' : Mem} {a : AState} (hS : StageR dn vis fe m a) (hAb : AbsOK m)
    {e v d : Word} (he : e.toNat < 2 ^ 32) {r : List Word}
    (hc : callW opfP k "inst_entry" [e, v, d] m = some (r, m')) :
    ∃ a', (instantiate1Fast coreWalkFuel (decE e) (decE v) d.toNat).run a = .ok (decE (r.headD 0), a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ AbsOK m' ∧ m'.arr64 SPN = m.arr64 SPN ∧
      rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 ∧ (r.headD 0).toNat < 2 ^ 32 := by
  rcases k with _ | k
  · rw [callW_zero] at hc; cases hc
  obtain ⟨s', hs', -, hok, hD, hres, hlt⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (instEntry_refines opfP opfP_inst rfl k _ a hS.1.arena e v d he) hc
  rw [hs'] at hD
  have hfr : MemFrame instA instC m m' := instEntry_frame opfP_inst rfl rfl (run_of_callW hc)
  have hrun := AM.run_of_ok _ a hok
  have hk := (keeps_inst1Fast coreWalkFuel (decE e) (decE v) d.toNat).run hrun
  obtain ⟨hS', hg⟩ := StageR.of_walk hS hD hfr instA_lt instC_lt hk
  obtain ⟨h1, h2⟩ := spn_of_lt64 hfr instA_lt instC_lt
  exact ⟨_, by rw [hrun, hres], hS', hg, hAb.frameD hfr (by decide) (by decide), h1, h2, hlt⟩

/-- **`spn_push` under the stage relation and `AbsOK`.** -/
theorem spnPushW_ok {m m' : Mem} {a : AState} (hS : StageR dn vis fe m a) (hAb : AbsOK m)
    {x : Word} {r : List Word} (h : spnPushW m x = some (r, m')) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ AbsOK m' ∧
      (rdW (m.arr64 CTL) 136).toNat < (m.arr64 SPN).size ∧
      rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 + 1 ∧
      (∀ w : Word, spW m' w = if w = rdW (m.arr64 CTL) 136 then x else spW m w) ∧
      (m'.arr64 SPN).size = (m.arr64 SPN).size := by
  simp only [spnPushW] at h
  split at h
  · cases h
  rename_i hlt
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hfr : MemFrame [SPN] [136] m
      ((m.set64 SPN (rdW (m.arr64 CTL) 136) x).set64 CTL 136 (rdW (m.arr64 CTL) 136 + 1)) :=
    ((MemFrame.set64 m SPN (by decide) _ _).mono (fun b hb => hb) (by simp)).trans
      ((MemFrame.setCtl _ 136 _).mono (by simp) (fun c hc => hc))
  obtain ⟨hS', hg⟩ := stageR_hi hS hfr (by simp [SPN]) (by simp) (by decide) (by decide)
  have hsz : (rdW (m.arr64 CTL) 136).toNat < (m.arr64 SPN).size := by
    have : ¬ (((m.arr64 SPN).size : Nat).toUInt64 ≤ rdW (m.arr64 CTL) 136) := hlt
    rw [UInt64.le_iff_toNat_le] at this
    have h2 : (((m.arr64 SPN).size : Nat).toUInt64).toNat = (m.arr64 SPN).size % 2 ^ 64 := by
      simp [Nat.toUInt64]
    have h3 : (m.arr64 SPN).size < 2 ^ 64 := by have := hAb.2.2.2.2.2.2.1; omega
    omega
  refine ⟨hS', hg, hAb.frameD hfr (by decide) (by decide), hsz, ?_, ?_, hfr.2.2.1 SPN⟩
  · have hc := hS.2.2.2.2.2
    rw [rdW_set64E, Mem.arr64_set64_ne _ _ _ _ _ (by decide),
      ite_eq_left ⟨rfl, rfl, by simp; omega⟩]
  · intro w
    simp only [spW]
    rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), rdW_set64E]
    by_cases hw : w = rdW (m.arr64 CTL) 136
    · subst hw; simp [hsz]
    · simp [hw, Ne.symm hw]

end

end L.Ind
