import ConAgua.Arena.DeclNatGuard

/-!
# The structural-`Nat` gate: the pinned types (lane `decls3`, helper `decls3-nat`)

`nat_op_cod`, `nat_op_ty_pinned`, `nat_op_stored_ok`, `nat_op_stored_ok_all`.
-/

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

structure NatTyProg (p : Prog) : Prop extends NatGuardProg p where
  lNatOpCod : p.lookup "nat_op_cod" = some natOpCodL
  lNatOpTyPinned : p.lookup "nat_op_ty_pinned" = some natOpTyPinnedL
  lNatOpStoredOk : p.lookup "nat_op_stored_ok" = some natOpStoredOkL
  lNatOpStoredOkAll : p.lookup "nat_op_stored_ok_all" = some natOpStoredOkAllL

theorem rd64_eq_rdW (m : Mem) (a : ArrId) (i : Word) : L.rd64 m a i = rdW (m.arr64 a) i := by
  simp [L.rd64, rdW, Array.getD_eq_getD_getElem?]

section ty
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

/-! ### `nat_op_cod` -/

section codmodel
variable (p : Prog) (n : Nat) (vis c e : Word)

def ncK10 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([if e = r.headD 0 then 1 else 0], m)

def ncK9 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => ncK10 e (callW p n "const_e" [r.headD 0] m)

def ncK7 (q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (s1, m) =>
    if rdW (m.arr64 EREC) (q + 2) ≠ 0 then some ([0], m)
    else some ([if rdW (m.arr64 EREC) (q + 3) = s1.headD 0 then 1 else 0], m)

def ncK6 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => ncK7 (r.headD 0) (callW p n "pin_word" [54] m)

def ncK5 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some ([0], m) else ncK6 p n (callW p n "ci_to_cv" [r.tail.headD 0] m)

def ncK4 (r3 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m) =>
    if e ≠ r4.headD 0 then some ([0], m)
    else ncK5 p n (callW p n "env_find" [r3.headD 0, vis] m)

def ncK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m) => ncK4 p n vis e r3 (callW p n "const_e" [r3.headD 0] m)

def ncK2 (r1 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m) =>
    if c = r1.headD 0 ∨ c = r2.headD 0 then ncK3 p n vis e (callW p n "pin_at" [29] m)
    else ncK9 p n e (callW p n "pin_at" [1] m)

def ncK1 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m) => ncK2 p n vis c e r1 (callW p n "pin_at" [20] m)

end codmodel

def natOpCodW (p : Prog) (n : Nat) (m : Mem) (vis c e : Word) : Option (List Word × Mem) :=
  ncK1 p n vis c e (callW p n "pin_at" [19] m)

section codarms
variable (p : Prog) (n : Nat) (vis c e : Word) (r r1 r3 : List Word) (m : Mem) (q : Word)
theorem ncK10_some : ncK10 e (some (r, m)) = some ([if e = r.headD 0 then 1 else 0], m) := rfl
theorem ncK9_some : ncK9 p n e (some (r, m)) = ncK10 e (callW p n "const_e" [r.headD 0] m) := rfl
theorem ncK7_some : ncK7 q (some (r, m)) =
    if rdW (m.arr64 EREC) (q + 2) ≠ 0 then some ([0], m)
    else some ([if rdW (m.arr64 EREC) (q + 3) = r.headD 0 then 1 else 0], m) := rfl
theorem ncK6_some : ncK6 p n (some (r, m)) = ncK7 (r.headD 0) (callW p n "pin_word" [54] m) := rfl
theorem ncK5_some : ncK5 p n (some (r, m)) = if r.headD 0 = 0 then some ([0], m)
    else ncK6 p n (callW p n "ci_to_cv" [r.tail.headD 0] m) := rfl
theorem ncK4_some : ncK4 p n vis e r3 (some (r, m)) = if e ≠ r.headD 0 then some ([0], m)
    else ncK5 p n (callW p n "env_find" [r3.headD 0, vis] m) := rfl
theorem ncK3_some : ncK3 p n vis e (some (r, m)) = ncK4 p n vis e r (callW p n "const_e" [r.headD 0] m) := rfl
theorem ncK2_some : ncK2 p n vis c e r1 (some (r, m)) =
    if c = r1.headD 0 ∨ c = r.headD 0 then ncK3 p n vis e (callW p n "pin_at" [29] m)
    else ncK9 p n e (callW p n "pin_at" [1] m) := rfl
theorem ncK1_some : ncK1 p n vis c e (some (r, m)) = ncK2 p n vis c e r (callW p n "pin_at" [20] m) := rfl
end codarms

grind_pattern [ind_grind] ncK10_some => ncK10 e (some (r, m))
grind_pattern [ind_grind] ncK9_some => ncK9 p n e (some (r, m))
grind_pattern [ind_grind] ncK7_some => ncK7 q (some (r, m))
grind_pattern [ind_grind] ncK6_some => ncK6 p n (some (r, m))
grind_pattern [ind_grind] ncK5_some => ncK5 p n (some (r, m))
grind_pattern [ind_grind] ncK4_some => ncK4 p n vis e r3 (some (r, m))
grind_pattern [ind_grind] ncK3_some => ncK3 p n vis e (some (r, m))
grind_pattern [ind_grind] ncK2_some => ncK2 p n vis c e r1 (some (r, m))
grind_pattern [ind_grind] ncK1_some => ncK1 p n vis c e (some (r, m))

theorem natOpCod_specW (p : Prog) (hp : p.lookup "nat_op_cod" = some natOpCodL) (n : Nat)
    (s₀ : St) (vis c e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_op_cod" [vis, c, e]
    ⦃fun r s' => LocEq s' s₀ ∧ natOpCodW p n s₀.mem vis c e = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, natOpCodL]
  vcgen [exec, step, evalE, L.evalC_spec, evalArgs, setLoc, setLocs, ld64,
    callW_spec p n "pin_at", callW_spec p n "const_e", callW_spec p n "env_find",
    callW_spec p n "ci_to_cv", callW_spec p n "pin_word"]
  all_goals (try simp only [Cond.pval, Expr.pval, Cmp.eval, Bool.or_eq_true, decide_eq_true_eq, rd64_eq_rdW] at *)
  all_goals grind (gen := 20) [lang_grind, arena_grind, ind_grind, natOpCodW]

theorem decI_bne_word {κ : IdxKind} {x y : Word} (hx : x.toNat < 2 ^ 32) (hy : y.toNat < 2 ^ 32) :
    ((decI x : Idx κ) != decI y) = decide (x ≠ y) := by
  rw [bne, decI_beq_word hx hy]; simp

theorem natOpCod_ref (hN : NatTyProg p) (c e : Word) :
    CallRef p "nat_op_cod" [vis, c, e] (fun m a => StageR dn vis fe m a ∧ H c ∧ H e)
      (natOpCod fe (decI c) (decI e)) (KeepPost dn vis fe decW0B) := by
  refine CallRef.of_succ fun k m a r m' ⟨hS, hc, he⟩ hcall => ?_
  have hw := callW_model (M := fun mm => natOpCodW p k mm vis c e) (natOpCod_specW p hN.lNatOpCod k · vis c e) hcall
  unfold natOpCodW at hw
  cases h1 : callW p k "pin_at" [19] m with
  | none => rw [h1] at hw; simp [ncK1] at hw
  | some q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, ncK1_some] at hw
  obtain ⟨hm1, h0, hr1⟩ := pinAt_call hN.lPinAt (j := 20) rfl h1
  rw [hm1] at hw
  cases h2 : callW p k "pin_at" [20] m with
  | none => rw [h2] at hw; simp [ncK2] at hw
  | some q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, ncK2_some] at hw
  obtain ⟨hm2, -, hr2⟩ := pinAt_call hN.lPinAt (j := 21) rfl h2
  rw [hm2] at hw
  have hF := hS.1.pins.full h0
  have hp1 : H (r1.headD 0) := by rw [hr1]; exact hF.names_lt 19 (by decide)
  have hp2 : H (r2.headD 0) := by rw [hr2]; exact hF.names_lt 20 (by decide)
  have e1 : (pinAt 19).run a = .ok (decI (r1.headD 0), a) := by
    have := pinAt_run hF 19 (by decide); rw [hr1]; exact this
  have e2 : (pinAt 20).run a = .ok (decI (r2.headD 0), a) := by
    have := pinAt_run hF 20 (by decide); rw [hr2]; exact this
  have hcond : ((decI c : NIdx) == decI (r1.headD 0) || (decI c : NIdx) == decI (r2.headD 0)) =
      decide (c = r1.headD 0 ∨ c = r2.headD 0) := by
    rw [decI_beq_word hc hp1, decI_beq_word hc hp2]; simp
  by_cases hP : c = r1.headD 0 ∨ c = r2.headD 0
  · rw [if_pos hP] at hw
    cases h3 : callW p k "pin_at" [29] m with
    | none => rw [h3] at hw; simp [ncK3] at hw
    | some q3 =>
    obtain ⟨r3, m3⟩ := q3
    rw [h3, ncK3_some] at hw
    obtain ⟨hm3, -, hr3⟩ := pinAt_call hN.lPinAt (j := 30) rfl h3
    rw [hm3] at hw
    have hp3 : H (r3.headD 0) := by rw [hr3]; exact hF.names_lt 29 (by decide)
    have e3 : (pinAt 29).run a = .ok (decI (r3.headD 0), a) := by
      have := pinAt_run hF 29 (by decide); rw [hr3]; exact this
    cases h4 : callW p k "const_e" [r3.headD 0] m with
    | none => rw [h4] at hw; simp [ncK4] at hw
    | some q4 =>
    obtain ⟨r4, m4⟩ := q4
    rw [h4, ncK4_some] at hw
    obtain ⟨x4, a4, hrun4, hS4, hg4, hx4l, hx4⟩ := constE_ref (dn := dn) (vis := vis) (fe := fe)
      hN.toMasterProg (r3.headD 0) k m a r4 m4 ⟨hS, hp3⟩ h4
    have hne : (decI e != x4) = decide (e ≠ r4.headD 0) := by
      rw [← hx4]; exact decI_bne_word he hx4l
    by_cases hee : e ≠ r4.headD 0
    · rw [if_pos hee] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      refine ⟨false, a4, ?_, hS4, hg4, by simp [decW0B]⟩
      simp only [natOpCod, natBeqName_eq, natBleName_eq, StateT.run_bind, e1, e2, exc_ok_bind',
        hcond, decide_eq_true hP, if_true, boolName_eq, e3, hrun4, hne, decide_eq_true hee]
      rfl
    · rw [if_neg hee] at hw
      have hee' : e = r4.headD 0 := by simpa using hee
      cases h5 : callW p k "env_find" [r3.headD 0, vis] m4 with
      | none => rw [h5] at hw; simp [ncK5] at hw
      | some q5 =>
      obtain ⟨rf, m5⟩ := q5
      rw [h5, ncK5_some] at hw
      obtain ⟨hm5, hfd⟩ := envFind_call hN.toMasterProg (r3.headD 0) hp3 hS4.1.env h5
      rw [hm5] at hw
      cases hf : fe.find? (decI (r3.headD 0)) with
      | none =>
        rw [hf] at hfd
        have hz : rf.headD 0 = 0 := hfd
        rw [if_pos hz] at hw
        simp only [Option.some.injEq, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        refine ⟨false, a4, ?_, hS4, hg4, by simp [decW0B]⟩
        simp only [natOpCod, natBeqName_eq, natBleName_eq, StateT.run_bind, e1, e2, exc_ok_bind',
          hcond, decide_eq_true hP, if_true, boolName_eq, e3, hrun4, hne, decide_eq_false hee, hf]
        rfl
      | some ci =>
        rw [hf] at hfd
        obtain ⟨hf1, hci⟩ := hfd
        have hnz : ¬ rf.headD 0 = 0 := by rw [hf1]; decide
        rw [if_neg hnz] at hw
        cases h6 : callW p k "ci_to_cv" [rf.tail.headD 0] m4 with
        | none => rw [h6] at hw; simp [ncK6] at hw
        | some q6 =>
        obtain ⟨r6, m6⟩ := q6
        rw [h6, ncK6_some] at hw
        obtain ⟨cv, a6, hrun6, hS6, hg6, hcv⟩ := ciToCv_ref (dn := dn) (vis := vis) (fe := fe)
          hN.toNatCvProg (rf.tail.headD 0) ci k m4 a4 r6 m6 ⟨hS4, hci⟩ h6
        cases h7 : callW p k "pin_word" [54] m6 with
        | none => rw [h7] at hw; simp [ncK7] at hw
        | some q7 =>
        obtain ⟨r7, m7⟩ := q7
        rw [h7, ncK7_some] at hw
        obtain ⟨hm7, h07, hr7⟩ := callW_pinWord' hN.lPinWord h7
        rw [hm7] at hw
        have hF6 := hS6.1.pins.full h07
        obtain ⟨wt, hiff, hrd, hlt, hty, -⟩ := cvWordsAt hS6.2.2.2.2.1 hcv
        have hp54 : (pinW m6 54).toNat < 2 ^ 32 := hF6.lv_lt.2.2
        have hr7' : r7.headD 0 = pinW m6 54 := by rw [hr7]; rfl
        by_cases hl : rdW (m6.arr64 EREC) (r6.headD 0 + 2) = 0
        · rw [if_neg (by simpa using hl)] at hw
          simp only [Option.some.injEq, Prod.mk.injEq] at hw
          obtain ⟨rfl, rfl⟩ := hw
          have hisE : cv.levelParams.isEmpty = true := hiff.mp hl
          rw [hrd, hr7']
          refine ⟨decide (wt = pinW m6 54), a6, ?_, hS6, hg4.trans hg6, ?_⟩
          · simp only [natOpCod, natBeqName_eq, natBleName_eq, StateT.run_bind, e1, e2, exc_ok_bind',
              hcond, decide_eq_true hP, if_true, boolName_eq, e3, hrun4, hne, decide_eq_false hee, Bool.false_eq_true, if_false, hf,
              hrun6, sortOne, pinSortOne_run hF6, hisE, hty, decI_beq_word hlt hp54, hrd]
            rfl
          · simp only [decW0B, List.headD_cons]
            by_cases he' : wt = pinW m6 54
            · rw [if_pos he', decide_eq_true he']; decide
            · rw [if_neg he', decide_eq_false he']; decide
        · rw [if_pos (by simpa using hl)] at hw
          simp only [Option.some.injEq, Prod.mk.injEq] at hw
          obtain ⟨rfl, rfl⟩ := hw
          have hisE : cv.levelParams.isEmpty = false := by
            cases h : cv.levelParams.isEmpty
            · rfl
            · exact absurd (hiff.mpr h) hl
          refine ⟨false, a6, ?_, hS6, hg4.trans hg6, by simp [decW0B]⟩
          simp only [natOpCod, natBeqName_eq, natBleName_eq, StateT.run_bind, e1, e2, exc_ok_bind',
            hcond, decide_eq_true hP, if_true, boolName_eq, e3, hrun4, hne, decide_eq_false hee, Bool.false_eq_true, if_false, hf,
            hrun6, sortOne, pinSortOne_run hF6, hisE]
          rfl
  · rw [if_neg hP] at hw
    cases h3 : callW p k "pin_at" [1] m with
    | none => rw [h3] at hw; simp [ncK9] at hw
    | some q3 =>
    obtain ⟨r3, m3⟩ := q3
    rw [h3, ncK9_some] at hw
    obtain ⟨hm3, -, hr3⟩ := pinAt_call hN.lPinAt (j := 2) rfl h3
    rw [hm3] at hw
    have hp3 : H (r3.headD 0) := by rw [hr3]; exact hF.names_lt 1 (by decide)
    have e3 : (pinAt 1).run a = .ok (decI (r3.headD 0), a) := by
      have := pinAt_run hF 1 (by decide); rw [hr3]; exact this
    cases h4 : callW p k "const_e" [r3.headD 0] m with
    | none => rw [h4] at hw; simp [ncK10] at hw
    | some q4 =>
    obtain ⟨r4, m4⟩ := q4
    rw [h4, ncK10_some] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    obtain ⟨x4, a4, hrun4, hS4, hg4, hx4l, hx4⟩ := constE_ref (dn := dn) (vis := vis) (fe := fe)
      hN.toMasterProg (r3.headD 0) k m a r4 m4 ⟨hS, hp3⟩ h4
    have hbeq : ((decI e : EIdx) == x4) = decide (e = r4.headD 0) := by
      rw [← hx4]; exact decI_beq_word he hx4l
    refine ⟨decide (e = r4.headD 0), a4, ?_, hS4, hg4, ?_⟩
    · simp only [natOpCod, natBeqName_eq, natBleName_eq, StateT.run_bind, e1, e2, exc_ok_bind',
        hcond, decide_eq_false hP, Bool.false_eq_true, if_false, pinNat_eq, e3, hrun4, hbeq]
      rfl
    · simp only [decW0B, List.headD_cons]
      by_cases he' : e = r4.headD 0
      · rw [if_pos he', decide_eq_true he']; decide
      · rw [if_neg he', decide_eq_false he']; decide

@[refines ConRon.Arena.natOpCod]
theorem natOpCod_refines (hN : NatTyProg p) (c e : Word) :
    RefAM p "nat_op_cod" [vis, c, e] (fun m a => StageR dn vis fe m a ∧ H c ∧ H e)
      (natOpCod fe (decI c) (decI e)) (KeepPost dn vis fe decW0B) :=
  (natOpCod_ref hN c e).refAM

end ty

end L.Ind
