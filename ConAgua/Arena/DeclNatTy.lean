module

public import ConAgua.Arena.DeclNatGuard
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.DeclNatGate
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.WP.Triple.SpecLemmas
public import ConRon.Arena.DeclCheck
import all ConAgua.Arena.DeclArmsNat

@[expose] public section

/-!
# The structural-`Nat` gate: the pinned types (lane `decls3`, helper `decls3-nat`)

`nat_op_cod`, `nat_op_ty_pinned`, `nat_op_stored_ok`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

structure NatTyProg (p : Prog) : Prop extends NatGuardProg p where
  lNatOpCod : p.lookup "nat_op_cod" = some natOpCodL
  lNatOpTyPinned : p.lookup "nat_op_ty_pinned" = some natOpTyPinnedL
  lNatOpStoredOk : p.lookup "nat_op_stored_ok" = some natOpStoredOkL

section ty
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

/-! ### `nat_op_cod` -/

/-- **`nat_op_cod` is its model `natOpCodW`** (generated). -/
l_model natOpCod_specW (p : Prog) (hp : p.lookup "nat_op_cod" = some natOpCodL)
  fns [hp ↦ natOpCodW list]
  specs [callW_spec p n "pin_at", callW_spec p n "const_e", callW_spec p n "env_find", callW_spec p n "ci_to_cv", callW_spec p n "pin_word"]
  grind [arena_grind] finish [ntBW] gen 20 bind ntBW instances 10000

theorem natOpCod_ref (hN : NatTyProg p) (c e : Word) :
    CallRef p "nat_op_cod" [vis, c, e] (fun m a => StageR vis fe m a ∧ H c ∧ H e)
      (natOpCod fe (decI c) (decI e)) (KeepPost vis fe decW0B) := by
  refine CallRef.of_succ fun k m a r m' ⟨hS, hc, he⟩ hcall => ?_
  have hw := callW_model (M := fun mm => natOpCodW p (k + 1) mm vis c e) (natOpCod_specW p hN.lNatOpCod (k + 1) · vis c e) hcall
  rw [natOpCodW.arm1] at hw
  simp only [erRd_foldN] at hw
  cases h1 : callW p k "pin_at" [19] m with
  | none => rw [h1] at hw; simp [ntBW] at hw
  | some q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, bW_some] at hw
  obtain ⟨hm1, h0, hr1⟩ := pinAt_call hN.lPinAt (j := 20) rfl h1
  rw [hm1] at hw
  cases h2 : callW p k "pin_at" [20] m with
  | none => rw [h2] at hw; simp [ntBW] at hw
  | some q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, bW_some] at hw
  obtain ⟨hm2, -, hr2⟩ := pinAt_call hN.lPinAt (j := 21) rfl h2
  rw [hm2] at hw
  have hF := hS.check.pins.full h0
  have hp1 : H (r1.headD 0) := by rw [hr1]; exact hF.names_lt 19 (by decide)
  have hp2 : H (r2.headD 0) := by rw [hr2]; exact hF.names_lt 20 (by decide)
  have e1 : (pinAt 19).run a = .ok (decI (r1.headD 0), a) := by
    have := pinAt_run hF 19 (by decide); rw [hr1]; exact this
  have e2 : (pinAt 20).run a = .ok (decI (r2.headD 0), a) := by
    have := pinAt_run hF 20 (by decide); rw [hr2]; exact this
  have hcond : ((decI c : NIdx) == decI (r1.headD 0) || (decI c : NIdx) == decI (r2.headD 0)) =
      decide (c = r1.headD 0 ∨ c = r2.headD 0) := by
    rw [decI_beq _ _ hc hp1, decI_beq _ _ hc hp2]; simp
  by_cases hP : c = r1.headD 0 ∨ c = r2.headD 0
  · rw [ite_eq_left hP] at hw
    cases h3 : callW p k "pin_at" [29] m with
    | none => rw [h3] at hw; simp [ntBW] at hw
    | some q3 =>
    obtain ⟨r3, m3⟩ := q3
    rw [h3, bW_some] at hw
    obtain ⟨hm3, -, hr3⟩ := pinAt_call hN.lPinAt (j := 30) rfl h3
    rw [hm3] at hw
    have hp3 : H (r3.headD 0) := by rw [hr3]; exact hF.names_lt 29 (by decide)
    have e3 : (pinAt 29).run a = .ok (decI (r3.headD 0), a) := by
      have := pinAt_run hF 29 (by decide); rw [hr3]; exact this
    cases h4 : callW p k "const_e" [r3.headD 0] m with
    | none => rw [h4] at hw; simp [ntBW] at hw
    | some q4 =>
    obtain ⟨r4, m4⟩ := q4
    rw [h4, bW_some] at hw
    obtain ⟨x4, a4, hrun4, hS4, hg4, hx4l, hx4⟩ := constE_ref (vis := vis) (fe := fe)
      hN.toMasterProg (r3.headD 0) k m a r4 m4 ⟨hS, hp3⟩ h4
    have hne : (decI e != x4) = decide (e ≠ r4.headD 0) := by
      rw [← hx4]; rw [decI_bne _ _ he hx4l]; simp
    by_cases hee : e ≠ r4.headD 0
    · rw [ite_eq_left hee] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      refine ⟨false, a4, ?_, hS4, hg4, by simp [decW0B]⟩
      simp only [natOpCod, natBeqName_eq, natBleName_eq, StateT.run_bind, e1, e2, L.Arena.except_ok_bind,
        hcond, decide_eq_true hP, ite_true, boolName_eq, e3, hrun4, hne, decide_eq_true hee]
      rfl
    · rw [ite_eq_right hee] at hw
      have hee' : e = r4.headD 0 := by simpa using hee
      cases h5 : callW p k "env_find" [r3.headD 0, vis] m4 with
      | none => rw [h5] at hw; simp [ntBW] at hw
      | some q5 =>
      obtain ⟨rf, m5⟩ := q5
      rw [h5, bW_some] at hw
      obtain ⟨hm5, hfd⟩ := envFind_call hN.toMasterProg (r3.headD 0) hp3 hS4.check.env h5
      rw [hm5] at hw
      cases hf : fe.find? (decI (r3.headD 0)) with
      | none =>
        rw [hf] at hfd
        have hz : rf.headD 0 = 0 := hfd
        rw [ite_eq_left hz] at hw
        simp only [Option.some.injEq, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        refine ⟨false, a4, ?_, hS4, hg4, by simp [decW0B]⟩
        simp only [natOpCod, natBeqName_eq, natBleName_eq, StateT.run_bind, e1, e2, L.Arena.except_ok_bind,
          hcond, decide_eq_true hP, ite_true, boolName_eq, e3, hrun4, hne, decide_eq_false hee, hf]
        rfl
      | some ci =>
        rw [hf] at hfd
        obtain ⟨hf1, hci⟩ := hfd
        have hnz : ¬ rf.headD 0 = 0 := by rw [hf1]; decide
        rw [ite_eq_right hnz] at hw
        cases h6 : callW p k "ci_to_cv" [rf.tail.headD 0] m4 with
        | none => rw [h6] at hw; simp [ntBW] at hw
        | some q6 =>
        obtain ⟨r6, m6⟩ := q6
        rw [h6, bW_some] at hw
        obtain ⟨cv, a6, hrun6, hS6, hg6, hcv⟩ := ciToCv_ref (vis := vis) (fe := fe)
          hN.toNatCvProg (rf.tail.headD 0) ci k m4 a4 r6 m6 ⟨hS4, hci⟩ h6
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hrun6)
        cases h7 : callW p k "pin_word" [54] m6 with
        | none => rw [h7] at hw; simp [ntBW] at hw
        | some q7 =>
        obtain ⟨r7, m7⟩ := q7
        rw [h7, bW_some] at hw
        obtain ⟨hm7, h07, hr7⟩ := callW_pinWord' hN.lPinWord h7
        rw [hm7] at hw
        have hF6 := hS6.check.pins.full h07
        obtain ⟨wt, hiff, hrd, hlt, hty, -⟩ := cvWordsAt hcv
        have hp54 : (pinW m6 54).toNat < 2 ^ 32 := hF6.lv_lt.2.2
        have hr7' : r7.headD 0 = pinW m6 54 := by rw [hr7]; rfl
        by_cases hl : erRd m6 (r6.headD 0 + CV.lpsLen) = 0
        · simp only [ne_eq, hl, not_true_eq_false, ite_false, Option.some.injEq, Prod.mk.injEq] at hw
          obtain ⟨rfl, rfl⟩ := hw
          have hisE : ci.toConstantVal.levelParams.isEmpty = true := hiff.mp hl
          simp only [hrd, hr7']
          refine ⟨decide (wt = pinW m6 54), a4, ?_, hS6, hg4.trans hg6, ?_⟩
          · simp only [natOpCod, natBeqName_eq, natBleName_eq, StateT.run_bind, e1, e2, L.Arena.except_ok_bind,
              hcond, decide_eq_true hP, ite_true, boolName_eq, e3, hrun4, hne, decide_eq_false hee, Bool.false_eq_true, ite_false, hf,
              sortOne, pinSortOne_run hF6, hisE, hty, decI_beq _ _ hlt hp54]
            rfl
          · simp only [decW0B, List.headD_cons]
            by_cases he' : wt = pinW m6 54
            · rw [ite_eq_left he', decide_eq_true he']; decide
            · rw [ite_eq_right he', decide_eq_false he']; decide
        · simp only [ne_eq, hl, not_false_eq_true, ite_true, Option.some.injEq, Prod.mk.injEq] at hw
          obtain ⟨rfl, rfl⟩ := hw
          have hisE : ci.toConstantVal.levelParams.isEmpty = false := by
            cases h : ci.toConstantVal.levelParams.isEmpty
            · rfl
            · exact absurd (hiff.mpr h) hl
          refine ⟨false, a4, ?_, hS6, hg4.trans hg6, by simp [decW0B]⟩
          simp only [natOpCod, natBeqName_eq, natBleName_eq, StateT.run_bind, e1, e2, L.Arena.except_ok_bind,
            hcond, decide_eq_true hP, ite_true, boolName_eq, e3, hrun4, hne, decide_eq_false hee, Bool.false_eq_true, ite_false, hf,
            sortOne, pinSortOne_run hF6, hisE]
          rfl
  · rw [ite_eq_right hP] at hw
    cases h3 : callW p k "pin_at" [1] m with
    | none => rw [h3] at hw; simp [ntBW] at hw
    | some q3 =>
    obtain ⟨r3, m3⟩ := q3
    rw [h3, bW_some] at hw
    obtain ⟨hm3, -, hr3⟩ := pinAt_call hN.lPinAt (j := 2) rfl h3
    rw [hm3] at hw
    have hp3 : H (r3.headD 0) := by rw [hr3]; exact hF.names_lt 1 (by decide)
    have e3 : (pinAt 1).run a = .ok (decI (r3.headD 0), a) := by
      have := pinAt_run hF 1 (by decide); rw [hr3]; exact this
    cases h4 : callW p k "const_e" [r3.headD 0] m with
    | none => rw [h4] at hw; simp [ntBW] at hw
    | some q4 =>
    obtain ⟨r4, m4⟩ := q4
    rw [h4, bW_some] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    obtain ⟨x4, a4, hrun4, hS4, hg4, hx4l, hx4⟩ := constE_ref (vis := vis) (fe := fe)
      hN.toMasterProg (r3.headD 0) k m a r4 m4 ⟨hS, hp3⟩ h4
    have hbeq : ((decI e : EIdx) == x4) = decide (e = r4.headD 0) := by
      rw [← hx4]; exact decI_beq _ _ he hx4l
    refine ⟨decide (e = r4.headD 0), a4, ?_, hS4, hg4, ?_⟩
    · simp only [natOpCod, natBeqName_eq, natBleName_eq, StateT.run_bind, e1, e2, L.Arena.except_ok_bind,
        hcond, decide_eq_false hP, Bool.false_eq_true, ite_false, pinNat_eq, e3, hrun4, hbeq]
      rfl
    · simp only [decW0B, List.headD_cons]
      by_cases he' : e = r4.headD 0
      · rw [ite_eq_left he', decide_eq_true he']; decide
      · rw [ite_eq_right he', decide_eq_false he']; decide

@[refines ConRon.Arena.natOpCod]
theorem natOpCod_refines (hN : NatTyProg p) (c e : Word) :
    RefAM p "nat_op_cod" [vis, c, e] (fun m a => StageR vis fe m a ∧ H c ∧ H e)
      (natOpCod fe (decI c) (decI e)) (KeepPost vis fe decW0B) :=
  (natOpCod_ref hN c e).refAM

/-! ### `nat_op_ty_pinned` -/

/-- **`nat_op_ty_pinned` is its model `natOpTyPinnedW`** (generated). -/
l_model natOpTyPinned_specW (p : Prog) (hp : p.lookup "nat_op_ty_pinned" = some natOpTyPinnedL)
  fns [hp ↦ natOpTyPinnedW list]
  specs [callW_spec p n "pin_at", callW_spec p n "const_e", callW_spec p n "e_view", callW_spec p n "nat_op_cod"]
  grind [arena_grind] heartbeats 3200000 bind ntBW

theorem viewR_forall {rv : List Word} {v : ENodeView} (h : ViewR rv v) :
    (rv.headD 0 = 6 ∧ ∃ dom body, v = .forallE dom body ∧ H (rv.tail.headD 0) ∧
      decE (rv.tail.headD 0) = dom ∧ H (rv.tail.tail.headD 0) ∧ decE (rv.tail.tail.headD 0) = body) ∨
    (rv.headD 0 ≠ 6 ∧ ∀ dom body, v ≠ .forallE dom body) := by
  cases v <;> simp only [ViewR] at h
  all_goals first
    | (left; obtain ⟨h0, h1, h2, h3, h4⟩ := h
       refine ⟨h0, _, _, rfl, ?_, ?_, ?_, ?_⟩ <;> simp_all [H])
    | (right; refine ⟨?_, fun _ _ => by simp⟩; simp_all)

theorem natOpTyPinned_ref (hN : NatTyProg p) (c ty : Word) :
    CallRef p "nat_op_ty_pinned" [vis, c, ty] (fun m a => StageR vis fe m a ∧ H c ∧ H ty)
      (natOpTyPinned fe (decI c) (decI ty)) (KeepPost vis fe decW0B) := by
  refine CallRef.of_succ fun k m a r m' ⟨hS, hc, hty⟩ hcall => ?_
  have hw := callW_model (M := fun mm => natOpTyPinnedW p (k + 1) mm vis c ty) (natOpTyPinned_specW p hN.lNatOpTyPinned (k + 1) · vis c ty) hcall
  rw [natOpTyPinnedW.arm1] at hw
  cases h1 : callW p k "pin_at" [1] m with
  | none => rw [h1] at hw; simp [ntBW] at hw
  | some q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, bW_some] at hw
  obtain ⟨hm1, h0, hr1⟩ := pinAt_call hN.lPinAt (j := 2) rfl h1
  rw [hm1] at hw
  have hF := hS.check.pins.full h0
  have hp1 : H (r1.headD 0) := by rw [hr1]; exact hF.names_lt 1 (by decide)
  have e1 : (pinAt 1).run a = .ok (decI (r1.headD 0), a) := by
    have := pinAt_run hF 1 (by decide); rw [hr1]; exact this
  cases h2 : callW p k "const_e" [r1.headD 0] m with
  | none => rw [h2] at hw; simp [ntBW] at hw
  | some q2 =>
  obtain ⟨nc, m2⟩ := q2
  rw [h2, bW_some] at hw
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2l, hx2⟩ := constE_ref (vis := vis) (fe := fe)
    hN.toMasterProg (r1.headD 0) k m a nc m2 ⟨hS, hp1⟩ h2
  cases h3 : callW p k "pin_at" [14] m2 with
  | none => rw [h3] at hw; simp [ntBW] at hw
  | some q3 =>
  obtain ⟨pr, m3⟩ := q3
  rw [h3, bW_some] at hw
  obtain ⟨hm3, h02, hr3⟩ := pinAt_call hN.lPinAt (j := 15) rfl h3
  rw [hm3] at hw
  have hF2 := hS2.check.pins.full h02
  have hp3 : H (pr.headD 0) := by rw [hr3]; exact hF2.names_lt 14 (by decide)
  have e3 : (pinAt 14).run a2 = .ok (decI (pr.headD 0), a2) := by
    have := pinAt_run hF2 14 (by decide); rw [hr3]; exact this
  have htag : ((decI ty : EIdx).tag == ETag.forallE) = decide (tagW ty = 6) := decI_tag_forallE_beq ty hty
  have hbeqc : ((decI c : NIdx) == decI (pr.headD 0)) = decide (c = pr.headD 0) := decI_beq _ _ hc hp3
  have hshort : ¬ tagW ty = 6 → ∃ x a', (natOpTyPinned fe (decI c) (decI ty)).run a = .ok (x, a') ∧ KeepPost vis fe decW0B m m' a' r x := by
    intro h6
    rw [ite_eq_left (by simpa using h6)] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    refine ⟨false, a2, ?_, hS2, hg2, by simp [decW0B]⟩
    simp only [natOpTyPinned, pinNat_eq, StateT.run_bind, e1, L.Arena.except_ok_bind, hrun2, natPredName_eq, e3,
      hbeqc, htag, decide_eq_false h6]
    by_cases hcp : c = pr.headD 0
    · simp [hcp]; rfl
    · simp; rfl
  refine (if h6 : tagW ty = 6 then ?_ else hshort h6)
  rw [ite_eq_right (by simpa using h6)] at hw
  cases h4 : callW p k "e_view" [ty] m2 with
  | none => rw [h4] at hw; simp [ntBW] at hw
  | some q4 =>
  obtain ⟨rv, m4⟩ := q4
  rw [h4, bW_some] at hw
  obtain ⟨vv, a4, hrun4, hS4, hg4, hvr⟩ := eView_ref (vis := vis) (fe := fe) (p := p) ty hN.lEView k m2 a2 rv m4 hS2 h4
  have hrun4' : (view (decI ty)).run a2 = .ok (vv, a4) := hrun4
  have hg02 : IWGrow m m2 := hg2
  have hnonf : (rv.headD 0 ≠ 6 ∧ ∀ dom body, vv ≠ .forallE dom body) →
      ∃ x a', (natOpTyPinned fe (decI c) (decI ty)).run a = .ok (x, a') ∧
        KeepPost vis fe decW0B m m' a' r x := by
    rintro ⟨hrvn, hnf⟩
    rw [ite_eq_left hrvn] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    refine ⟨false, a4, ?_, hS4, hg02.trans hg4, by simp [decW0B]⟩
    simp only [natOpTyPinned, pinNat_eq, StateT.run_bind, e1, L.Arena.except_ok_bind, hrun2, natPredName_eq, e3,
      hbeqc, htag, decide_eq_true h6, ite_true]
    by_cases hcp : c = pr.headD 0
    · simp only [decide_eq_true hcp, ite_true, StateT.run_bind, hrun4', L.Arena.except_ok_bind]
      cases vv <;> first | rfl | (exfalso; exact hnf _ _ rfl)
    · simp only [decide_eq_false hcp, Bool.false_eq_true, ite_false, StateT.run_bind, hrun4', L.Arena.except_ok_bind]
      cases vv <;> first | rfl | (exfalso; exact hnf _ _ rfl)
  refine Or.elim (viewR_forall hvr) ?_ hnonf
  rintro ⟨hrv6, dom, body, hvv, hd0, hdom, hb0, hbody⟩
  rw [ite_eq_right (by simpa using hrv6)] at hw
  subst hvv
  by_cases hcp : c = pr.headD 0
  · rw [ite_eq_left hcp] at hw
    have hdn : ((decE (rv.tail.headD 0) : EIdx) == x2) = decide (rv.tail.headD 0 = nc.headD 0) := by
      rw [← hx2]; exact decI_beq _ _ hd0 hx2l
    by_cases hdc : rv.tail.headD 0 = nc.headD 0
    · rw [ite_eq_right (by simpa using hdc)] at hw
      cases h5 : callW p k "nat_op_cod" [vis, c, rv.tail.tail.headD 0] m4 with
      | none => rw [h5] at hw; simp [ntBW] at hw
      | some q5 =>
      obtain ⟨rr, m5⟩ := q5
      rw [h5, bW_some] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      obtain ⟨x5, a5, hrun5, hS5, hg5, hx5⟩ := natOpCod_ref (vis := vis) (fe := fe) hN c
        (rv.tail.tail.headD 0) k m4 a4 rr m5 ⟨hS4, hc, hb0⟩ h5
      refine ⟨x5, a5, ?_, hS5, hg02.trans (hg4.trans hg5), by simpa [decW0B] using hx5⟩
      have hrun5 : (natOpCod fe (decI c) body).run a4 = .ok (x5, a5) := by rw [← hbody]; exact hrun5
      simp only [natOpTyPinned, pinNat_eq, StateT.run_bind, e1, L.Arena.except_ok_bind, hrun2, natPredName_eq, e3,
        hbeqc, htag, decide_eq_true h6, ite_true, hrun4', decide_eq_true hcp, ← hdom, hdn, decide_eq_true hdc, ite_true, hrun5]
    · rw [ite_eq_left (by simpa using hdc)] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      refine ⟨false, a4, ?_, hS4, hg02.trans hg4, by simp [decW0B]⟩
      simp only [natOpTyPinned, pinNat_eq, StateT.run_bind, e1, L.Arena.except_ok_bind, hrun2, natPredName_eq, e3,
        hbeqc, htag, decide_eq_true h6, ite_true, hrun4', decide_eq_true hcp, ← hdom, hdn, decide_eq_false hdc, Bool.false_eq_true, ite_false]
      rfl
  · rw [ite_eq_right hcp] at hw
    have hdn : ((decE (rv.tail.headD 0) : EIdx) == x2) = decide (rv.tail.headD 0 = nc.headD 0) := by
      rw [← hx2]; exact decI_beq _ _ hd0 hx2l
    have htagb : ((decE (rv.tail.tail.headD 0) : EIdx).tag == ETag.forallE) =
        decide (tagW (rv.tail.tail.headD 0) = 6) := decI_tag_forallE_beq _ hb0
    have hshortb : ¬ tagW (rv.tail.tail.headD 0) = 6 → ∃ x a', (natOpTyPinned fe (decI c) (decI ty)).run a = .ok (x, a') ∧
        KeepPost vis fe decW0B m m' a' r x := by
      intro hb6
      rw [ite_eq_left (by simpa using hb6)] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      refine ⟨false, a4, ?_, hS4, hg02.trans hg4, by simp [decW0B]⟩
      simp only [natOpTyPinned, pinNat_eq, StateT.run_bind, e1, L.Arena.except_ok_bind, hrun2, natPredName_eq, e3,
        hbeqc, htag, decide_eq_true h6, ite_true, hrun4', decide_eq_false hcp, Bool.false_eq_true,
        ite_false, ← hbody, htagb, decide_eq_false hb6]
      rfl
    refine (if hb6 : tagW (rv.tail.tail.headD 0) = 6 then ?_ else hshortb hb6)
    rw [ite_eq_right (by simpa using hb6)] at hw
    cases h5 : callW p k "e_view" [rv.tail.tail.headD 0] m4 with
    | none => rw [h5] at hw; simp [ntBW] at hw
    | some q5 =>
    obtain ⟨rv2, m5⟩ := q5
    rw [h5, bW_some] at hw
    obtain ⟨vv2, a5, hrun5, hS5, hg5, hvr2⟩ := eView_ref (vis := vis) (fe := fe) (p := p)
      (rv.tail.tail.headD 0) hN.lEView k m4 a4 rv2 m5 hS4 h5
    have hnonf2 : (rv2.headD 0 ≠ 6 ∧ ∀ dom body, vv2 ≠ .forallE dom body) →
        ∃ x a', (natOpTyPinned fe (decI c) (decI ty)).run a = .ok (x, a') ∧
          KeepPost vis fe decW0B m m' a' r x := by
      rintro ⟨hrvn, hnf⟩
      rw [ite_eq_left hrvn] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      refine ⟨false, a5, ?_, hS5, hg02.trans (hg4.trans hg5), by simp [decW0B]⟩
      simp only [natOpTyPinned, pinNat_eq, StateT.run_bind, e1, L.Arena.except_ok_bind, hrun2, natPredName_eq, e3,
        hbeqc, htag, decide_eq_true h6, ite_true, hrun4', decide_eq_false hcp, Bool.false_eq_true,
        ite_false, htagb, decide_eq_true hb6, ← hbody, hrun5]
      cases vv2 <;> first | rfl | (exfalso; exact hnf _ _ rfl)
    refine Or.elim (viewR_forall hvr2) ?_ hnonf2
    rintro ⟨hrv26, dom2, body2, hvv2, hd02, hdom2, hb02, hbody2⟩
    rw [ite_eq_right (by simpa using hrv26)] at hw
    subst hvv2
    have hdn2 : ((decE (rv2.tail.headD 0) : EIdx) == x2) = decide (rv2.tail.headD 0 = nc.headD 0) := by
      rw [← hx2]; exact decI_beq _ _ hd02 hx2l
    by_cases hdd : rv.tail.headD 0 = nc.headD 0 ∧ rv2.tail.headD 0 = nc.headD 0
    · rw [ite_eq_right (fun h => h.elim (fun x => x hdd.1) (fun x => x hdd.2))] at hw
      cases h6' : callW p k "nat_op_cod" [vis, c, rv2.tail.tail.headD 0] m5 with
      | none => rw [h6'] at hw; simp [ntBW] at hw
      | some q6 =>
      obtain ⟨rr, m6⟩ := q6
      rw [h6', bW_some] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      obtain ⟨x6, a6, hrun6, hS6, hg6, hx6⟩ := natOpCod_ref (vis := vis) (fe := fe) hN c
        (rv2.tail.tail.headD 0) k m5 a5 rr m6 ⟨hS5, hc, hb02⟩ h6'
      refine ⟨x6, a6, ?_, hS6, hg02.trans (hg4.trans (hg5.trans hg6)), by simpa [decW0B] using hx6⟩
      have hrun6' : (natOpCod fe (decI c) body2).run a5 = .ok (x6, a6) := by rw [← hbody2]; exact hrun6
      simp only [natOpTyPinned, pinNat_eq, StateT.run_bind, e1, L.Arena.except_ok_bind, hrun2, natPredName_eq, e3,
        hbeqc, htag, decide_eq_true h6, ite_true, hrun4', decide_eq_false hcp, Bool.false_eq_true,
        ite_false, ← hbody, htagb, decide_eq_true hb6, hrun5, ← hdom, ← hdom2, hdn, hdn2,
        decide_eq_true hdd.1, decide_eq_true hdd.2, Bool.and_self, ite_true, hrun6']
    · rw [ite_eq_left (by by_cases h1 : rv.tail.headD 0 = nc.headD 0
                          · exact Or.inr (fun h2 => hdd ⟨h1, h2⟩)
                          · exact Or.inl h1)] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      refine ⟨false, a5, ?_, hS5, hg02.trans (hg4.trans hg5), by simp [decW0B]⟩
      simp only [natOpTyPinned, pinNat_eq, StateT.run_bind, e1, L.Arena.except_ok_bind, hrun2, natPredName_eq, e3,
        hbeqc, htag, decide_eq_true h6, ite_true, hrun4', decide_eq_false hcp, Bool.false_eq_true,
        ite_false, ← hbody, htagb, decide_eq_true hb6, hrun5, ← hdom, ← hdom2, hdn, hdn2]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      rw [ite_eq_right hdd]
      rfl

@[refines ConRon.Arena.natOpTyPinned]
theorem natOpTyPinned_refines (hN : NatTyProg p) (c ty : Word) :
    RefAM p "nat_op_ty_pinned" [vis, c, ty] (fun m a => StageR vis fe m a ∧ H c ∧ H ty)
      (natOpTyPinned fe (decI c) (decI ty)) (KeepPost vis fe decW0B) :=
  (natOpTyPinned_ref hN c ty).refAM

/-! ### `nat_op_stored_ok` -/

/-- **`nat_op_stored_ok` is its model `natOpStoredOkW`** (generated). -/
l_model natOpStoredOk_specW (p : Prog) (hp : p.lookup "nat_op_stored_ok" = some natOpStoredOkL)
  fns [hp ↦ natOpStoredOkW list]
  specs [callW_spec p n "env_find", callW_spec p n "nat_op_ty_pinned"]
  grind [arena_grind] finish [ntBW] gen 20 bind ntBW instances 10000

theorem natOpStoredOk_ref (hN : NatTyProg p) (w : Word) :
    CallRef p "nat_op_stored_ok" [vis, w] (fun m a => StageR vis fe m a ∧ H w)
      (natOpStoredOk fe (decI w)) (KeepPost vis fe decW0B) := by
  refine CallRef.of_succ fun k m a r m' ⟨hS, hw⟩ hcall => ?_
  have hW := callW_model (M := fun mm => natOpStoredOkW p (k + 1) mm vis w) (natOpStoredOk_specW p hN.lNatOpStoredOk (k + 1) · vis w) hcall
  rw [natOpStoredOkW.arm1] at hW
  cases h1 : callW p k "env_find" [w, vis] m with
  | none => rw [h1] at hW; simp [ntBW] at hW
  | some q1 =>
  obtain ⟨rf, m1⟩ := q1
  rw [h1, bW_some] at hW
  obtain ⟨hm1, hfd⟩ := envFind_call hN.toMasterProg w hw hS.check.env h1
  rw [hm1] at hW
  cases hf : fe.find? (decI w) with
  | none =>
    rw [hf] at hfd
    have hz : rf.headD 0 = 0 := hfd
    rw [ite_eq_left hz] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    exact ⟨false, a, by simp only [natOpStoredOk, hf]; rfl, hS, IWGrow.refl _, by simp [decW0B]⟩
  | some ci =>
    rw [hf] at hfd
    obtain ⟨hf1, hci⟩ := hfd
    rw [ite_eq_right (by rw [hf1]; decide)] at hW
    simp only [erRd_foldN] at hW
    rcases defnMono_words hci with ⟨hne, hdm⟩ | ⟨hk1, hiff⟩
    · simp only [ne_eq, hne, not_false_eq_true, ite_true, Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨rfl, rfl⟩ := hW
      refine ⟨false, a, ?_, hS, IWGrow.refl _, by simp [decW0B]⟩
      simp only [natOpStoredOk, hf]
      cases ci <;> first | rfl | (simp [defnMono] at hdm; simp [hdm]; rfl)
    · simp only [ne_eq, hk1, not_true_eq_false, ite_false] at hW
      -- the record is a definition
      obtain ⟨cv, v, hint, rfl, hk, hcv⟩ : ∃ cv v hint, ci = .defnInfo cv v hint ∧
          erecP m (rf.tail.headD 0).toNat = some 1 ∧ decCV (erecP m) ((rf.tail.headD 0).toNat + CI.cv.toNat) = some cv := by
        rcases decCI_defn_cases hci with h | ⟨wk, hwk, hne, -⟩
        · exact h
        · exfalso; have := (erRd_of_erecP hwk).1; rw [hk1] at this; exact hne this.symm
      obtain ⟨wt, hiffc, hrd, hlt, hty, -⟩ := natCvWords hcv
      by_cases hl : erRd m (rf.tail.headD 0 + (CI.cv + CV.lpsLen)) = 0
      · simp only [hl, not_true_eq_false, ite_false] at hW
        cases h2 : callW p k "nat_op_ty_pinned" [vis, w, erRd m (rf.tail.headD 0 + (CI.cv + CV.type))] m with
        | none => rw [h2] at hW; simp [ntBW] at hW
        | some q2 =>
        obtain ⟨rt, m2⟩ := q2
        rw [h2, bW_some] at hW
        simp only [Option.some.injEq, Prod.mk.injEq] at hW
        obtain ⟨rfl, rfl⟩ := hW
        rw [hrd] at h2
        obtain ⟨x2, a2, hrun2, hS2, hg2, hx2⟩ := natOpTyPinned_ref (vis := vis) (fe := fe) hN w wt
          k m a rt m2 ⟨hS, hw, hlt⟩ h2
        refine ⟨x2, a2, ?_, hS2, hg2, by simpa [decW0B] using hx2⟩
        have hisE : cv.levelParams.isEmpty = true := hiffc.mp hl
        simp only [natOpStoredOk, hf, hisE, ite_true, hty]
        exact hrun2
      · simp only [hl, not_false_eq_true, ite_true] at hW
        simp only [Option.some.injEq, Prod.mk.injEq] at hW
        obtain ⟨rfl, rfl⟩ := hW
        have hisE : cv.levelParams.isEmpty = false := by
          cases h : cv.levelParams.isEmpty
          · rfl
          · exact absurd (hiffc.mpr h) hl
        refine ⟨false, a, ?_, hS, IWGrow.refl _, by simp [decW0B]⟩
        simp only [natOpStoredOk, hf, hisE]
        rfl

@[refines ConRon.Arena.natOpStoredOk]
theorem natOpStoredOk_refines (hN : NatTyProg p) (w : Word) :
    RefAM p "nat_op_stored_ok" [vis, w] (fun m a => StageR vis fe m a ∧ H w)
      (natOpStoredOk fe (decI w)) (KeepPost vis fe decW0B) :=
  (natOpStoredOk_ref hN w).refAM

end ty

end L.Ind
