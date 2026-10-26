import ConAgua.Arena.DeclNatOpEq
import ConAgua.Arena.DeclArmDefn
import ConAgua.L.ModelGen

/-!
# `defn_nat_gate` refines `natGateT` (lane `decls3`, helper `decls3-nat`)

The definition arm's structural-`Nat` gate: `nat_op_names`, `sl_contains`, and for a member the
guard, the stored dependencies, the stored value's equations certified at the pre-insertion view.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind

local notation "V" => ConLeche.CheckMode.verified

section gate
variable {dn : NIdx → Option ConLeche.Name} {p : Prog}

/-- **`defn_nat_cert` is its model `defnNatCertW`** (generated). -/
l_model defnNatCert_specW (p : Prog) (hp : p.lookup "defn_nat_cert" = some defnNatCert)
  fns [hp ↦ defnNatCertW list]
  specs [callW_spec p n "env_find", callW_spec p n "nat_op_equations", callW_spec p n "subst_const0_pairs",
    callW_spec p n "certify_nat_eqs"]
  grind [arena_grind] finish [ntBW] gen 20 heartbeats 6400000 bind ntBW instances 10000

/-- **`defn_nat_gate` is its model `defnNatGateW`** (generated). -/
l_model defnNatGate_specW (p : Prog) (hp : p.lookup "defn_nat_gate" = some defnNatGate)
  fns [hp ↦ defnNatGateW list]
  specs [callW_spec p n "nat_op_names", callW_spec p n "sl_contains", callW_spec p n "nat_op_guard",
    callW_spec p n "nat_op_deps", callW_spec p n "nat_op_stored_ok_all", callW_spec p n "defn_nat_cert"]
  grind [arena_grind] heartbeats 6400000 bind ntBW simp [ntBW]

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
