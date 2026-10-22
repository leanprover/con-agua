import ConAgua.Arena.DeclNatOpEq
import ConAgua.Arena.DeclArmDefn

/-!
# `defn_nat_gate` refines `natGateT` (lane `decls3`, helper `decls3-nat`)

The definition arm's structural-`Nat` gate: `nat_op_names`, `sl_contains`, and for a member the
guard, the stored dependencies, the stored value's equations certified at the pre-insertion view.
-/

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind

local notation "V" => ConLeche.CheckMode.verified

section gate
variable {dn : NIdx → Option ConLeche.Name} {p : Prog}

def defnNatCertW (p : Prog) (k : Nat) (m : Mem) (vis w n : Word) : Option (List Word × Mem) :=
  bW (callW p k "env_find" [n, w] m) fun r6 m6 =>
  if r6.headD 0 = 0 then none else
  if rdW (m6.arr64 EREC) (r6.tail.headD 0) ≠ 1 then none else
  bW (callW p k "nat_op_equations" [0, n] m6) fun r7 m7 =>
  bW (callW p k "subst_const0_pairs" [n, rdW (m7.arr64 EREC) (r6.tail.headD 0 + 5), r7.headD 0, r7.tail.headD 0] m7)
    fun r8 m8 =>
  bW (callW p k "certify_nat_eqs" [vis, r8.headD 0, r8.tail.headD 0] m8) fun r9 m9 =>
  if r9.headD 0 = 0 then none else some ([0], m9)

set_option maxHeartbeats 6400000 in
theorem defnNatCert_specW (p : Prog) (hp : p.lookup "defn_nat_cert" = some defnNatCert) (k : Nat) (s₀ : St)
    (vis w n : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "defn_nat_cert" [vis, w, n]
    ⦃fun r s' => LocEq s' s₀ ∧ defnNatCertW p k s₀.mem vis w n = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, defnNatCert]
  vcgen [exec, step, evalE, L.evalC_spec, evalArgs, setLoc, setLocs, ld64,
    callW_spec p k "env_find", callW_spec p k "nat_op_equations", callW_spec p k "subst_const0_pairs",
    callW_spec p k "certify_nat_eqs"]
  all_goals (try simp only [Cond.pval, Expr.pval, Cmp.eval, Bool.or_eq_true, decide_eq_true_eq, rd64_eq_rdW, getElem_rdW'] at *)
  all_goals grind (gen := 20) (instances := 10000) [lang_grind, arena_grind, defnNatCertW, bW]

def defnNatGateW (p : Prog) (k : Nat) (m : Mem) (vis w n : Word) : Option (List Word × Mem) :=
  bW (callW p k "nat_op_names" [] m) fun r1 m1 =>
  bW (callW p k "sl_contains" [r1.headD 0, r1.tail.headD 0, n] m1) fun r2 m2 =>
  if r2.headD 0 = 0 then some ([0], m2) else
  bW (callW p k "nat_op_guard" [w, n] m2) fun r3 m3 =>
  bW (callW p k "nat_op_deps" [n] m3) fun r4 m4 =>
  bW (callW p k "nat_op_stored_ok_all" [w, r4.headD 0, r4.tail.headD 0] m4) fun r5 m5 =>
  if r3.headD 0 = 0 ∨ r5.headD 0 = 0 then none else
  bW (callW p k "defn_nat_cert" [vis, w, n] m5) fun r6 m6 => some ([0], m6)

set_option maxHeartbeats 6400000 in
theorem defnNatGate_specW (p : Prog) (hp : p.lookup "defn_nat_gate" = some defnNatGate) (k : Nat) (s₀ : St)
    (vis w n : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "defn_nat_gate" [vis, w, n]
    ⦃fun r s' => LocEq s' s₀ ∧ defnNatGateW p k s₀.mem vis w n = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, defnNatGate]
  vcgen [exec, step, evalE, L.evalC_spec, evalArgs, setLoc, setLocs, ld64,
    callW_spec p k "nat_op_names", callW_spec p k "sl_contains", callW_spec p k "nat_op_guard",
    callW_spec p k "nat_op_deps", callW_spec p k "nat_op_stored_ok_all", callW_spec p k "defn_nat_cert"]
  all_goals (try simp only [Cond.pval, Expr.pval, Cmp.eval, Bool.or_eq_true, decide_eq_true_eq, rd64_eq_rdW] at *)
  all_goals grind (gen := 20) (instances := 10000) [lang_grind, arena_grind, defnNatGateW, bW]

theorem decCI_defn_val {a : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Nat}
    {cv : IConstantVal} {v : EIdx} {hint : ConLeche.ReducibilityHint}
    (h : decCI a dn q = some (.defnInfo cv v hint)) :
    ∃ w, a[q]? = some 1 ∧ a[q + 5]? = some w ∧ w.toNat < 2 ^ 32 ∧ decI w = v := by
  unfold decCI at h
  cases hk : nat? a q with
  | none => simp [hk] at h
  | some k =>
  have hw : ∃ w, a[q]? = some w ∧ w.toNat = k := by
    simp only [nat?, Option.map_eq_some_iff] at hk
    obtain ⟨w, hw, hk⟩ := hk; exact ⟨w, hw, hk⟩
  obtain ⟨w0, hw0, hwk⟩ := hw
  rw [hk] at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨a1, ha1, h⟩ := h
  cases ha1
  by_cases h1 : k = 1
  · subst h1
    simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv', hcv, v', hv, hh, hhint, he⟩ := h
    cases he
    have : w0 = 1 := UInt64.toNat_inj.mp (by simpa using hwk)
    unfold hd? at hv
    obtain ⟨w, hw, hv⟩ : ∃ w, a[q + 5]? = some w ∧ (if w.toNat < 2 ^ 32 then some (decI w) else none) = some v := by
      cases hh5 : a[q + 5]? with
      | none => simp [hh5] at hv
      | some w => exact ⟨w, rfl, by simpa [hh5] using hv⟩
    by_cases hl : w.toNat < 2 ^ 32
    · rw [if_pos hl] at hv
      cases hv
      exact ⟨w, by rw [hw0, this], hw, hl, rfl⟩
    · rw [if_neg hl] at hv; cases hv
  · exfalso
    rcases k with _ | _ | _ | _ | _ | _ | _ | k
    · simp [Option.bind_eq_some_iff] at h
    · exact h1 rfl
    all_goals simp [Option.bind_eq_some_iff] at h

theorem erecP_get_rev {m : Mem} {i : Nat} {w : Word} (h : (erecP m)[i]? = some w) : (erecP m)[i]? = some w := h

theorem decEqRL_headD {m : Mem} {r : List Word} {ps : List (EIdx × EIdx)} (h : decEqRL m r ps) :
    EqL m (r.headD 0).toNat (r.tail.headD 0).toNat ps := by
  cases r with
  | nil => simpa [decEqRL] using h
  | cons a t => cases t <;> simpa [decEqRL] using h

theorem EqL.lt64 {m : Mem} {o l : Nat} {ps : List (EIdx × EIdx)} (h : EqL m o l ps) (hI : IWOK m) :
    o + l < 2 ^ 64 := by
  have := h.1; have := hI.1; have := hI.2.2.1; unfold iwTop at *; omega

def natCertT (fe2 feR : IFEnv) (c : NIdx) : AM Unit :=
  match fe2.find? c with
  | some (.defnInfo _ value' _) => do
      let eqs ← natOpEquations 0 c
      let ok ← certifyNatEqs V feR (← substConst0Pairs c value' eqs)
      unless ok do
        fail (.notImplemented
          "nonstandard structural Nat operation")
  | _ => fail (.internal
      "structural Nat operation not stored")

theorem defnNatCert_ref (hN : NatSubProg' p) (hc : p.lookup "defn_nat_cert" = some defnNatCert)
    {fe2 : IFEnv} (vis w n : Word) (hn : H n) :
    CallRef p "defn_nat_cert" [vis, w, n] (fun m a => StageR dn w fe2 m a)
      (natCertT fe2 (fe2.restrictTo vis.toNat) (decI n)) (KeepPost dn w fe2 decUnit) := by
  refine CallRef.of_succ fun k m a r m' hS hcall => ?_
  have hw := callW_model (M := fun mm => defnNatCertW p k mm vis w n) (defnNatCert_specW p hc k · vis w n) hcall
  unfold defnNatCertW at hw
  have hE := hN.toNatSubProg.toNatEqProg
  have hG := hE.toNatTyProg.toNatGuardProg.toNatLitProg.toNatCvProg.toNatGateProg
  cases h1 : callW p k "env_find" [n, w] m with
  | none => rw [h1] at hw; simp at hw
  | some q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, bW_some] at hw
  obtain ⟨hm1, hfd⟩ := envFind_call hG.toMasterProg n hn hS.1.env h1
  subst hm1
  cases hf : fe2.find? (decI n) with
  | none =>
    rw [hf] at hfd
    have hz : r1.headD 0 = 0 := hfd
    rw [if_pos hz] at hw; cases hw
  | some ci =>
  rw [hf] at hfd
  obtain ⟨hf1, hci⟩ := hfd
  have hnz : ¬ r1.headD 0 = 0 := by rw [hf1]; decide
  rw [if_neg hnz] at hw
  have hsz := hS.2.2.2.2.1
  generalize hq : r1.tail.headD 0 = q at hw hci
  rcases decCI_defn_cases hci with ⟨cv, v, hint, rfl, hk, hcv⟩ | ⟨w1, hw1, hne, hnd⟩
  rotate_left
  · have hk' := erecP_get hw1
    have : rdW (m1.arr64 EREC) q ≠ 1 := by rw [rdW, hk']; exact hne
    rw [if_pos this] at hw; cases hw
  obtain ⟨wv, hk1, hk5, hwl, hwd⟩ := decCI_defn_val hci
  have e1 : rdW (m1.arr64 EREC) q = 1 := by rw [rdW, erecP_get hk1]; rfl
  rw [if_neg (by rw [e1]; simp)] at hw
  have hq5 : (q + 5).toNat = q.toNat + 5 := by
    have : q.toNat + 5 < (m1.arr64 EREC).size := (Array.getElem?_eq_some_iff.mp (erecP_get hk5)).1
    rw [UInt64.toNat_add]; simp; omega
  have e5 : rdW (m1.arr64 EREC) (q + 5) = wv := by
    simp only [rdW, hq5]; rw [erecP_get hk5]; rfl
  have hv64 : (m1.arr64 EREC).size < 2 ^ 64 := hsz
  have hqlt : q.toNat + 5 < erTop m1 := erecP_lt (erecP_get_rev hk5)
  cases h2 : callW p k "nat_op_equations" [0, n] m1 with
  | none => rw [h2] at hw; simp at hw
  | some q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, bW_some] at hw
  obtain ⟨x2, a2, hrun2, hS2, hg2, hd2⟩ := natOpEquations_ref hN 0 n k m1 a r2 m2 ⟨hS, by decide, hn⟩ h2
  have hE2 := decEqRL_headD hd2
  have e5' : rdW (m2.arr64 EREC) (q + 5) = wv := by
    simp only [rdW, hq5]; rw [hg2.2.2.2 _ hqlt, erecP_get hk5]; rfl
  rw [e5'] at hw
  cases h3 : callW p k "subst_const0_pairs" [n, wv, r2.headD 0, r2.tail.headD 0] m2 with
  | none => rw [h3] at hw; simp at hw
  | some q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, bW_some] at hw
  obtain ⟨x3, a3, hrun3, hS3, hg3, hd3⟩ := pairs_ref hN.toNatSubProg n wv hn hwl x2 (r2.headD 0) (r2.tail.headD 0)
    k m2 a2 r3 m3 hS2 hE2 (EqL.lt64 hE2 hS2.2) h3
  have hE3 := decEqRL_headD hd3
  have hS3r := StageR.restrict hS3 vis
  cases h4 : callW p k "certify_nat_eqs" [vis, r3.headD 0, r3.tail.headD 0] m3 with
  | none => rw [h4] at hw; simp at hw
  | some q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [h4, bW_some] at hw
  obtain ⟨x4, a4, hrun4, hS4, hg4, hd4⟩ := certify_ref hN.toNatSubProg.toNatEqProg (r3.headD 0) (r3.tail.headD 0) x3
    k m3 a3 r4 m4 hS3r hE3 (EqL.lt64 hE3 hS3.2) h4
  by_cases e4 : r4.headD 0 = 0
  · rw [if_pos e4] at hw; cases hw
  rw [if_neg e4] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨-, rfl⟩ := hw
  have t4 : x4 = true := by rw [← hd4.1]; simpa using e4
  refine ⟨(), a4, ?_, ?_, ?_, trivial⟩
  · have hv : decE wv = v := hwd
    have hrun2' : (natOpEquations 0 (decI n)).run a = .ok (x2, a2) := hrun2
    have hrun3' : (substConst0Pairs (decI n) (decE wv) x2).run a2 = .ok (x3, a3) := hrun3
    simp only [natCertT, hf, StateT.run_bind, hrun2', exc_ok_bind']
    rw [← hv, hrun3']
    simp only [exc_ok_bind', hrun4, t4, if_true]
    rfl
  · have hvb : fe2.visibleBelow = w.toNat := hS.1.env.vis
    have := StageR.restrict hS4 w
    rw [IFEnv.restrictTo_restrictTo, ← hvb, IFEnv.restrictTo_self] at this
    exact this
  · exact ((hg2.trans hg3).trans hg4)

theorem decRL0 {α : Type} {g : Mem → Nat → Nat → Option (List α)} {m : Mem} {r : List Word} {l : List α}
    (h : decRL g 0 m r l) :
    g m (r.headD 0).toNat (r.tail.headD 0).toNat = some l ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m := by
  cases r with
  | nil => simpa [decRL] using h
  | cons a t => cases t <;> simpa [decRL] using h

theorem natGateT_eq (feR fe2 : IFEnv) (c : NIdx) : natGateT feR fe2 c = (do
    let ns ← natOpNames
    if ns.contains c then do
      let g ← natOpGuard fe2 c
      let deps ← natOpDeps c
      unless g && (← natOpStoredOkAll fe2 deps) do
        fail (.notImplemented "nonstandard structural Nat operation environment")
      natCertT fe2 feR c
    else pure ()) := rfl

theorem defnNatGate_ref (hN : NatSubProg' p) (hg : p.lookup "defn_nat_gate" = some defnNatGate)
    (hc : p.lookup "defn_nat_cert" = some defnNatCert)
    {fe2 : IFEnv} (vis w n : Word) (hn : H n) :
    CallRef p "defn_nat_gate" [vis, w, n] (fun m a => StageR dn w fe2 m a)
      (natGateT (fe2.restrictTo vis.toNat) fe2 (decI n)) (KeepPost dn w fe2 decUnit) := by
  refine CallRef.of_succ fun k m a r m' hS hcall => ?_
  have hw := callW_model (M := fun mm => defnNatGateW p k mm vis w n) (defnNatGate_specW p hg k · vis w n) hcall
  unfold defnNatGateW at hw
  have hE := hN.toNatSubProg.toNatEqProg
  have hT := hE.toNatTyProg
  have hGd := hT.toNatGuardProg
  have hG := hGd.toNatLitProg.toNatCvProg.toNatGateProg
  rw [natGateT_eq]
  cases h1 : callW p k "nat_op_names" [] m with
  | none => rw [h1] at hw; simp at hw
  | some q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, bW_some] at hw
  obtain ⟨xs, a1, hrun1, hS1, hg1, hd1⟩ := natOpNames_ref hG k m a r1 m1 hS h1
  obtain ⟨hdh1, hb1⟩ := decRL0 hd1
  cases h2 : callW p k "sl_contains" [r1.headD 0, r1.tail.headD 0, n] m1 with
  | none => rw [h2] at hw; simp at hw
  | some q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, bW_some] at hw
  obtain ⟨x2, a2, hrun2, hS2, hg2, hd2⟩ := slContains_ref hG.lSlContains (r1.headD 0) (r1.tail.headD 0) n xs hn
    k m1 a1 r2 m2 ⟨hS1, hdh1⟩ h2
  have ha2 : a2 = a1 := by
    simp only [pure, StateT.pure, StateT.run, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun2
    exact hrun2.2.symm
  subst ha2
  have hx2 : x2 = xs.contains (decI n) := by
    simp only [pure, StateT.pure, StateT.run, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun2
    exact hrun2.1.symm
  by_cases e2 : r2.headD 0 = 0
  · rw [if_pos e2] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hf : xs.contains (decI n) = false := by
      rw [← hx2]; have := hd2.1; rw [e2] at this; simpa using this.symm
    refine ⟨(), a2, ?_, hS2, hg1.trans hg2, trivial⟩
    simp only [StateT.run_bind, hrun1, exc_ok_bind', hf]
    rfl
  rw [if_neg e2] at hw
  have hx2t : xs.contains (decI n) = true := by
    rw [← hx2, ← hd2.1]; simpa using e2
  cases h3 : callW p k "nat_op_guard" [w, n] m2 with
  | none => rw [h3] at hw; simp at hw
  | some q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, bW_some] at hw
  obtain ⟨x3, a3, hrun3, hS3, hg3, hd3⟩ := natOpGuard_ref hGd n k m2 a2 r3 m3 ⟨hS2, hn⟩ h3
  cases h4 : callW p k "nat_op_deps" [n] m3 with
  | none => rw [h4] at hw; simp at hw
  | some q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [h4, bW_some] at hw
  obtain ⟨ds, a4, hrun4, hS4, hg4, hd4⟩ := natOpDeps_ref hG n k m3 a3 r4 m4 ⟨hS3, hn⟩ h4
  obtain ⟨hdh4, hb4⟩ := decRL0 hd4
  cases h5 : callW p k "nat_op_stored_ok_all" [w, r4.headD 0, r4.tail.headD 0] m4 with
  | none => rw [h5] at hw; simp at hw
  | some q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [h5, bW_some] at hw
  obtain ⟨x5, a5, hrun5, hS5, hg5, hd5⟩ := okAll_ref hT (r4.headD 0) (r4.tail.headD 0) ds k m4 a4 r5 m5 hS4 hdh4 hb4 h5
  by_cases e35 : r3.headD 0 = 0 ∨ r5.headD 0 = 0
  · rw [if_pos e35] at hw; cases hw
  rw [if_neg e35] at hw
  have t3 : x3 = true := by rw [← hd3.1]; simp at e35; simp [e35.1]
  have t5 : x5 = true := by rw [← hd5.1]; simp at e35; simp [e35.2]
  obtain ⟨-, -, -⟩ : True ∧ True ∧ True := ⟨trivial, trivial, trivial⟩
  cases h6 : callW p k "defn_nat_cert" [vis, w, n] m5 with
  | none => rw [h6] at hw; simp at hw
  | some q6 =>
  obtain ⟨r6, m6⟩ := q6
  rw [h6, bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨-, rfl⟩ := hw
  obtain ⟨u6, a6, hrun6, hS6, hg6, -⟩ := defnNatCert_ref hN hc vis w n hn k m5 a5 r6 m6 hS5 h6
  refine ⟨(), a6, ?_, hS6, ?_, trivial⟩
  · have hrun1' := hrun1
    simp only [StateT.run_bind, hrun1, exc_ok_bind', hx2t, if_true, hrun3, hrun4, hrun5, t3, t5,
      Bool.and_self, hrun6]
  · exact (((((hg1.trans hg2).trans hg3).trans hg4).trans hg5).trans hg6)

/-- The text the gate reaches: the functions of `armText` it calls, transitively. -/
def natGateFns : List FnName :=
  ["defn_nat_gate", "nat_op_names", "pin_at", "iw_alloc", "sl_contains", "nat_op_guard", "nat_lit_supported", "nat_op_deps", "nat_op_pins", "nat_op_pins_a", "nat_op_pins_b", "nat_op_pins_c", "nat_op_deps_stored", "env_find", "env_row_get", "env_ix", "nat_div_mod_names", "nat_op_bool_ctors", "bool_ctor_ok", "ci_to_cv", "intern_zero", "zero_find", "zero_push", "intern_succ", "succ_find", "succ_push", "intern_sort", "sort_find", "sort_push", "cv_new", "erec_alloc", "const_e", "pin_word", "intern_const", "const_find", "const_push", "nat_op_stored_ok_all", "nat_op_stored_ok", "nat_op_ty_pinned", "e_view", "nat_op_cod", "nat_op_equations", "nat_eq_ctx", "intern_fvar", "fvar_find", "fvar_push", "nat_ap1", "mk_app", "der_b", "intern_app", "app_find", "app_push", "nat_eq_disp", "nat_eq_pr", "nat_eq_list2", "rec2", "nat_eq_un", "nat_ap2", "nat_eq_mu", "nat_eq_po", "nat_eq_be", "nat_eq_list4", "nat_eq_bl", "nat_eq_list3", "subst_const0_pairs", "subst_const0", "sl_cons", "iw_copy", "certify_nat_eqs", "is_def_eq_core", "defn_nat_cert"]

theorem natGate_closed : closedA armText stepA stepC natGateFns = true := by decide +kernel

/-- **`defn_nat_gate` refines `natGateT`** at the extended view: the gate's program (a
`NatSubProg'` with the two gate functions), its text agreeing with `armText` on the functions it
reaches (for the write set). -/
theorem natGateSpec (hN : NatSubProg' p) (hg : p.lookup "defn_nat_gate" = some defnNatGate)
    (hc : p.lookup "defn_nat_cert" = some defnNatCert)
    (hT : ∀ f ∈ natGateFns, p.lookup f = armText.lookup f) (pins : List INatOpPinSet) :
    NatGateSpec p pins := by
  intro dn vis w fe2 n hn n' s₀ a₀ ⟨hS, hPS⟩
  have hR := defnNatGate_ref (dn := dn) hN hg hc (fe2 := fe2) vis w n hn
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hW⟩ := M.of_run (P := fun s => s = s₀) hs hrun (callW_spec p n' "defn_nat_gate" [vis, w, n] s₀)
  obtain ⟨hf, -⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (invoke_memFrame (closedW_of_agree natGate_closed hT) n' (f := "defn_nat_gate") (by decide) [vis, w, n] s₀)
  subst hs
  obtain ⟨x, a', hrun', hpost⟩ := hR n' s.mem a₀ r s'.mem hS hW
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
  refine ⟨hloc, hok, ?_⟩
  rw [hst, hres]
  exact ⟨hpost, PinSetsR.step hPS hpost.2.1 hf, hf⟩

end gate

end L.Arena
