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
  ntBW (callW p k "env_find" [n, w] m) fun r6 m6 =>
  if r6.headD 0 = 0 then none else
  if rdW (m6.arr64 EREC) (r6.tail.headD 0) ≠ 1 then none else
  ntBW (callW p k "nat_op_equations" [0, n] m6) fun r7 m7 =>
  ntBW (callW p k "subst_const0_pairs" [n, rdW (m7.arr64 EREC) (r6.tail.headD 0 + 5), r7.headD 0, r7.tail.headD 0] m7)
    fun r8 m8 =>
  ntBW (callW p k "certify_nat_eqs" [vis, r8.headD 0, r8.tail.headD 0] m8) fun r9 m9 =>
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
  all_goals grind (gen := 20) (instances := 10000) [lang_grind, arena_grind, defnNatCertW, ntBW]

def defnNatGateW (p : Prog) (k : Nat) (m : Mem) (vis w n : Word) : Option (List Word × Mem) :=
  ntBW (callW p k "nat_op_names" [] m) fun r1 m1 =>
  ntBW (callW p k "sl_contains" [r1.headD 0, r1.tail.headD 0, n] m1) fun r2 m2 =>
  if r2.headD 0 = 0 then some ([0], m2) else
  ntBW (callW p k "nat_op_guard" [w, n] m2) fun r3 m3 =>
  ntBW (callW p k "nat_op_deps" [n] m3) fun r4 m4 =>
  ntBW (callW p k "nat_op_stored_ok_all" [w, r4.headD 0, r4.tail.headD 0] m4) fun r5 m5 =>
  if r3.headD 0 = 0 ∨ r5.headD 0 = 0 then none else
  ntBW (callW p k "defn_nat_cert" [vis, w, n] m5) fun r6 m6 => some ([0], m6)

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
  all_goals grind (gen := 20) (instances := 10000) [lang_grind, arena_grind, defnNatGateW, ntBW]

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

/-- The text the gate reaches: the functions of `armText` it calls, transitively. -/
def natGateFns : List FnName :=
  ["defn_nat_gate", "nat_op_names", "pin_at", "iw_alloc", "sl_contains", "nat_op_guard", "nat_lit_supported", "nat_op_deps", "nat_op_pins", "nat_op_pins_a", "nat_op_pins_b", "nat_op_pins_c", "nat_op_deps_stored", "env_find", "env_row_get", "env_ix", "nat_div_mod_names", "nat_op_bool_ctors", "bool_ctor_ok", "ci_to_cv", "intern_zero", "zero_find", "zero_push", "intern_succ", "succ_find", "succ_push", "intern_sort", "sort_find", "sort_push", "cv_new", "erec_alloc", "const_e", "pin_word", "intern_const", "const_find", "const_push", "nat_op_stored_ok_all", "nat_op_stored_ok", "nat_op_ty_pinned", "e_view", "nat_op_cod", "nat_op_equations", "nat_eq_ctx", "intern_fvar", "fvar_find", "fvar_push", "nat_ap1", "mk_app", "der_b", "intern_app", "app_find", "app_push", "nat_eq_disp", "nat_eq_pr", "nat_eq_list2", "rec2", "nat_eq_un", "nat_ap2", "nat_eq_mu", "nat_eq_po", "nat_eq_be", "nat_eq_list4", "nat_eq_bl", "nat_eq_list3", "subst_const0_pairs", "subst_const0", "sl_cons", "iw_copy", "certify_nat_eqs", "is_def_eq_core", "defn_nat_cert"]

end gate

end L.Arena
