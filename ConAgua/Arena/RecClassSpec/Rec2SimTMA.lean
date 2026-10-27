import ConAgua.Arena.RecCheckSpec.TargetMajorAt2
import ConAgua.Arena.RecStab

/-!
# Rec2SimTMA

`rec2TMD_ds`, `rec2SimTMA`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `target_major_at`, its `ds` slice decoded below the tops -/

theorem rec2TMD_ds {a a' : AState} {tm : TargetMajor}
    (h : ConRon.Arena.targetMajorDefault.run a = .ok (tm, a')) : tm.ds = [] := by
  simp only [ConRon.Arena.targetMajorDefault, StateT.run_bind] at h
  cases h1 : (internNNode .anonymous).run a with
  | error e => rw [h1] at h; cases h
  | ok p =>
    rw [h1, except_ok_bind] at h
    cases h2 : StateT.run pinEmptyLevels p.snd with
    | error e => rw [h2] at h; cases h
    | ok q =>
      rw [h2, except_ok_bind] at h
      injection h with h'
      injection h' with e1 e2
      rw [← e1]

theorem rec2SimTMA (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem)
    (a : AState) (mo ml c : Word) (ms : List TargetMajor) (hS : StageR dn vis fe m a)
    (hms : DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) m ms) (hb : mo.toNat + ml.toNat < 2 ^ 64) :
    RSim (tmaW n m mo ml c) (ConRon.Arena.targetMajorAt ms c.toNat) a
      (fun b a' tm => StageR dn vis fe b.2 a' ∧ IWGrow m b.2 ∧ TMR b.2 (b.1.headD 0).toNat tm) := by
  have hms0 : decPL m (decTM m) mo.toNat ml.toNat = some ms :=
    hms.get (OMono.decPL (fun q => decTM_mono q) _ _)
  intro b hb'
  obtain ⟨tm, a', hrun, hS', hg, hd⟩ := tmaW_sim dn vis fe n m a mo ml c ms hS hms0 hb b hb'
  refine ⟨tm, a', hrun, hS', hg, hd, fun o l ho hl => ?_⟩
  rcases hc : ms[c.toNat]? with _ | x
  · have hrun' : ConRon.Arena.targetMajorDefault.run a = .ok (tm, a') := by
      simpa [ConRon.Arena.targetMajorAt, hc] using hrun
    rw [rec2TMD_ds hrun']
    obtain ⟨-, -, ⟨o', l', ho', hl', hds⟩, -⟩ := rec2DecTM_parts hd
    rw [ho] at ho'; rw [hl] at hl'; cases ho'; cases hl'
    rw [rec2TMD_ds hrun'] at hds
    have : l = 0 := by have := decHL_length _ hds; simp at this; omega
    subst this
    show decHL (truncM b.2) o 0 = some []
    simp [decHL, hslice?]
  have hrun' : (pure x : AM TargetMajor).run a = .ok (tm, a') := by
    simpa [ConRon.Arena.targetMajorAt, hc] using hrun
  have hx : x = tm := by injection hrun' with e; injection e
  subst hx
  have hct : c.toNat < ms.length := (List.getElem?_eq_some_iff.mp hc).1
  have hlen := decPL_length m hms0
  obtain ⟨v, hv, hdv⟩ := decPL_getH (truncM m) hms c.toNat (by omega)
  obtain ⟨hvt, hv'⟩ := rec2IwN_trunc hv
  have hxe : ms[c.toNat] = x := (List.getElem?_eq_some_iff.mp hc).2
  rw [hxe] at hdv
  obtain ⟨-, -, ⟨o', l', ho', hl', hds⟩, -⟩ := rec2DecTM_parts hdv
  -- the record pointer is the one the model returns
  have hq : (b.1.headD 0).toNat = v := by
    have := hdv; have hd0 := hd
    by_cases hcl : c < ml
    · cases n with
      | zero => simp [tmaW] at hb'
      | succ n =>
        rw [tmaW_hit n m mo ml c hcl] at hb'
        cases hb'
        have hrd := iwN_rdW_at (w := mo) (k := c.toNat) hv' hS.2.2.2.1
        have hcw : mo + UInt64.ofNat c.toNat = mo + c := by simp
        rw [hcw] at hrd
        simp only [List.headD_cons]; rw [hrd.1, UInt64.toNat_ofNat_of_lt' hrd.2]
    · exfalso; apply hcl; apply UInt64.lt_iff_toNat_lt.mpr; omega
  rw [hq] at ho hl
  have e1 : iwN b.2 (v + 2) = some o' := by
    rw [iwN_grow hg (rec2IwN_trunc ho').1]; exact (rec2IwN_trunc ho').2
  have e2 : iwN b.2 (v + 3) = some l' := by
    rw [iwN_grow hg (rec2IwN_trunc hl').1]; exact (rec2IwN_trunc hl').2
  rw [e1] at ho; rw [e2] at hl
  simp only [Option.some.injEq] at ho hl
  subst ho hl
  exact (show DecB (fun m => (decHL m o' l' : Option (List EIdx))) m x.ds from hds).grow
    (OMono.decHL _ _) hg

end L.Ind

end
