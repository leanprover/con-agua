import ConAgua.Verdict.PosE2M
import ConAgua.Arena.IndRealAbsPos
import ConAgua.Arena.IndPosSpec.NestCrest

/-!
# `nest_group_ctors`: one model and one refinement for both outcomes

`ngcE` (`l_model … unified`, `PosE2M.lean`): the recursive call through the model itself,
`nest_container` and `sl_append` (outside the verdict closure) through their `Option` models.
`ngc_ref` refines `nestGroupCtors` for both outcomes; its users are `nestGroupCtors_refines` and
`nest_frame`'s refinement (`frameRef_step`, through the run).
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind
open L.Arena

/-- What `nest_group_ctors` gives besides the twin's constructors `res` (from `m`): the result
slice `r` (offset, length), the stage, the growth, the frames. -/
structure GcPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m : Mem) (r : List Word)
    (m' : Mem) (res : List (IConstantVal × Nat)) (a' : AState) : Prop where
  stage : StageR dn vis fe m' a'
  grow : IWGrow m m'
  length : (r.tail.headD 0).toNat = res.length
  bound : (r.headD 0).toNat + res.length ≤ iwTop m'
  cs : CsAt m' (r.headD 0).toNat res (· < iwTop m')
  abs : AFr m m'
  mfr : MFr [] [] m m'

/-- **`nest_group_ctors` refines `nestGroupCtors`, both outcomes**: a container that is none, or
whose parameter count disagrees, rejects as the twin does. -/
theorem ngc_ref {p : Prog} (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis nPc : Word) (k : Nat) :
    ∀ (m : Mem) (a : AState) (off l oo ol : Word) (cs : List NIdx) (out : List (IConstantVal × Nat)),
    StageR dn vis fe m a →
    decHL m off.toNat l.toNat = some cs → (∀ j < l.toNat, off.toNat + j < iwTop m) →
    ol.toNat = out.length → oo.toNat + out.length ≤ iwTop m → CsAt m oo.toNat out (· < iwTop m) →
    RefE (closedNV p _root_.L.Checker.nvFns = true) (ngcE p k m vis nPc off l oo ol)
      (ConRon.Arena.nestGroupCtors fe nPc.toNat cs out) a (fun v res a' => GcPost dn vis fe m v.1 v.2 res a') := by
  induction k with
  | zero => intro m a off l oo ol cs out _ _ _ _ _ _; rw [ngcE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ k ih =>
    intro m a off l oo ol cs out hS hcs' hcb hol hob hout
    by_cases hl0 : l = 0
    · rw [ngcE.arm1 p k m vis nPc off l oo ol hl0]
      subst hl0
      have : cs = [] := by simpa [decHL, hslice?] using hcs'.symm
      subst this
      exact RefE.ret (by simp [ConRon.Arena.nestGroupCtors]; rfl) ⟨hS, IWGrow.refl _, by simpa using hol,
        by simpa using hob, by simpa using hout, AFr.refl _, MFr.refl _ _ _⟩
    rw [ngcE.arm2 p k m vis nPc off l oo ol hl0]
    have hl : l.toNat ≠ 0 := fun e => hl0 (UInt64.toNat_inj.mp (by simpa using e))
    obtain ⟨l', hl'⟩ : ∃ l', l.toNat = l' + 1 := ⟨l.toNat - 1, by omega⟩
    have hcs2 := hcs'
    simp only [decHL, hl', hslice?_succ, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hcs2
    obtain ⟨c, hc, cs', hcs'', rfl⟩ := hcs2
    obtain ⟨hcH, hcd⟩ := rd_iwH0E (m := m) (o := off) (k := IdxKind.name) (by simpa [iwH, iwA] using hc)
    have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
    have hoff1 : (off + 1).toNat = off.toNat + 1 :=
      word_add_toNat (show off.toNat + 1 < 2 ^ 64 by have := hcb 0 (by omega); omega)
    have hl1 : (l - 1).toNat = l' := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    rcases hnt : ntWf k m vis (rdW (m.arr64 IW) off) with _ | ⟨r1, m1⟩
    · rw [liftE_none, ngcE.k_nest_container.none]; exact RefE.of_cls0 (by simp)
    rw [liftE_some]
    cases k with
    | zero => simp [ntWf] at hnt
    | succ k =>
    have hnt' : ntW k m vis (rdW (m.arr64 IW) off) = some (r1, m1) := by simpa [ntWf] using hnt
    obtain ⟨x, a1, hrun1, hS1, hg1, hnc⟩ := ntW_ok dn fe vis _ hcH k m m1 a r1 hnt' hS
    rw [hcd] at hrun1
    simp only [ConRon.Arena.nestGroupCtors.eq_2]
    refine RefE.bind_right hrun1 ?_
    cases x with
    | none =>
      have h0 : r1.headD 0 = 0 := hnc
      rw [ngcE.k_nest_container.abort1 p _ vis nPc off l oo ol r1 m1 h0]
      exact fun _ => ErrClaim.fail _ _ (by decide)
    | some pc =>
    obtain ⟨nPc2, ctors⟩ := pc
    obtain ⟨h0, h1', h3, h2b, hcs3⟩ := hnc
    have hne0 : r1.headD 0 ≠ 0 := by rw [h0]; decide
    by_cases hbad : r1.tail.headD 0 ≠ nPc ∧ r1.tail.tail.tail.headD 0 ≠ 0
    · rw [ngcE.k_nest_container.abort2 p _ vis nPc off l oo ol r1 m1 hne0 hbad]
      have hneq : nPc2 ≠ nPc.toNat := fun e => hbad.1 (UInt64.toNat_inj.mp (by rw [h1', e]))
      have hlen : ctors.length ≠ 0 := by
        intro e; apply hbad.2; apply UInt64.toNat_inj.mp; rw [h3, e]; rfl
      have hc : (!(nPc2 == nPc.toNat || ctors.length == 0)) = true := by
        simp [hneq, hlen]
      intro _
      show ErrClaim (if (!(nPc2 == nPc.toNat || ctors.length == 0)) = true then _ else _) a1 _
      rw [ite_eq_left hc]
      exact ErrClaim.fail _ _ (by decide)
    rw [ngcE.k_nest_container.arm1 p _ vis nPc off l oo ol r1 m1 hne0 hbad]
    have hchk : (nPc2 == nPc.toNat || ctors.length == 0) = true := by
      by_cases hp1 : r1.tail.headD 0 = nPc
      · rw [← h1', hp1]; simp
      · have : r1.tail.tail.tail.headD 0 = 0 := by
          by_cases hh : r1.tail.tail.tail.headD 0 = 0
          · exact hh
          · exact absurd ⟨hp1, hh⟩ hbad
        have : ctors.length = 0 := by rw [← h3, this]; rfl
        simp [this]
    show RefE _ _ (if (!(nPc2 == nPc.toNat || ctors.length == 0)) = true then _ else _) a1 _
    rw [hchk]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    rcases hap : appendW (k + 1) m1 oo ol (r1.tail.tail.headD 0) (r1.tail.tail.tail.headD 0) with _ | ⟨r2, m2⟩
    · rw [liftE_none, ngcE.k_sl_append.none]; exact RefE.of_cls0 (by simp)
    rw [liftE_some, ngcE.k_sl_append.arm1]
    obtain ⟨hS2, hg2, hr20, hr21, ht2, hw1, hw2⟩ := appendW_stage hap hS1 (by have := hg1.1; omega)
      (by rw [h3]; exact h2b)
    rw [h3] at hr21 ht2 hw2
    have hcsA : CsAt m2 (r2.headD 0).toNat (out ++ ctors) (· < iwTop m2) := by
      intro i hi
      rw [hr20]
      by_cases hio : i < out.length
      · obtain ⟨w, hw, hc'⟩ := hout i hio
        refine ⟨w, ?_, ?_⟩
        · rw [hw1 i (by omega), hg1.2.2.1 _ (by omega)]; exact hw
        · rw [List.getElem_append_left hio]; exact (hc'.grow hg1).grow hg2
      · simp only [List.length_append] at hi
        obtain ⟨w, hw, hc'⟩ := hcs3 (i - out.length) (by omega)
        refine ⟨w, ?_, ?_⟩
        · have := hw2 (i - out.length) (by omega)
          rw [show iwTop m1 + ol.toNat + (i - out.length) = iwTop m1 + i by omega] at this
          rw [this]; exact hw
        · rw [List.getElem_append_right (by omega)]; exact hc'.grow hg2
    have hR := ih m2 a1 (off + 1) (l - 1) (r2.headD 0) (r2.tail.headD 0) cs' (out ++ ctors) hS2
      (by rw [hoff1, hl1, decHL_agree (RdS.of_grow (hg1.trans hg2)) (fun j hj => by
            have := hcb (j + 1) (by omega); omega)]
          simpa [decHL] using hcs'')
      (fun j hj => by rw [hoff1, hl1] at *; have := hcb (j + 1) (by omega); have := hg1.1; have := hg2.1; omega)
      (by rw [hr21]; simp [hol]) (by rw [hr20]; simp; omega) hcsA
    rcases h3' : ngcE p (k + 1) m2 vis nPc (off + 1) (l - 1) (r2.headD 0) (r2.tail.headD 0) with e3 | ⟨r3, m3⟩
    · rw [ngcE.k_nest_group_ctors.none]; rw [h3'] at hR; exact hR
    rw [ngcE.k_nest_group_ctors.arm1]
    rw [h3'] at hR
    obtain ⟨res, a', hrun, hpost⟩ := hR
    exact RefE.ret hrun ⟨hpost.stage, (hg1.trans hg2).trans hpost.grow, hpost.length, hpost.bound, hpost.cs,
      ((ntWf_afr hnt).trans (appendW_afr hap)).trans hpost.abs,
      ((ntWf_mfr hnt).trans (appendW_mfr hap)).trans hpost.mfr⟩

section census
variable (p : Prog) (hl : NtLook p) (hc : p.lookup "iw_copy" = some iwCopy)
  (hap : p.lookup "sl_append" = some slAppend)
  (hp : p.lookup "nest_group_ctors" = some nestGroupCtorsL)
include hl hc hap hp

/-- **`nest_group_ctors` refines `nestGroupCtors`** (through `nest_container`'s stubs). -/
@[refines ConRon.Arena.nestGroupCtors]
theorem nestGroupCtors_refines (k : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis nPc off l oo ol : Word) (cs : List NIdx) (out : List (IConstantVal × Nat))
    (hS : StageR dn vis fe s₀.mem a₀)
    (hcs' : decHL s₀.mem off.toNat l.toNat = some cs) (hcb : ∀ j < l.toNat, off.toNat + j < iwTop s₀.mem)
    (hol : ol.toNat = out.length) (hob : oo.toNat + out.length ≤ iwTop s₀.mem)
    (hout : CsAt s₀.mem oo.toNat out (· < iwTop s₀.mem)) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_group_ctors" [vis, nPc, off, l, oo, ol]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.nestGroupCtors fe nPc.toNat cs out) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.nestGroupCtors fe nPc.toNat cs out) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      (r.tail.headD 0).toNat = (AM.res (ConRon.Arena.nestGroupCtors fe nPc.toNat cs out) a₀).length ∧
      (r.headD 0).toNat + (AM.res (ConRon.Arena.nestGroupCtors fe nPc.toNat cs out) a₀).length ≤ iwTop s'.mem ∧
      CsAt s'.mem (r.headD 0).toNat (AM.res (ConRon.Arena.nestGroupCtors fe nPc.toNat cs out) a₀)
        (· < iwTop s'.mem); ⊤⦄ := by
  refine triple_post (RefE.triple (ngcE_spec p hl hc hap hp k s₀ vis nPc off l oo ol)
    (ngc_ref dn fe vis nPc k _ a₀ off l oo ol cs out hS hcs' hcb hol hob hout)) ?_
  rintro r s' ⟨hlc, res, a', hrun, hpost⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hlc, hok, by rw [hst]; exact hpost.stage, hpost.grow, ?_, ?_, ?_⟩
  · rw [hres]; exact hpost.length
  · rw [hres]; exact hpost.bound
  · rw [hres]; exact hpost.cs

end census

end L.Ind

end
