module

public import ConAgua.Arena.DeclNatEq
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConRon.Bridge.Grind

@[expose] public section

/-!
# The structural-`Nat` gate's decoding lemmas and text (lane `decls3`, helper `decls3-nat`)

Lemmas the definition arm's structural-`Nat` gate (`snp_ref`, `DeclNatGateT.lean`) reads its
records and lists through, and the text it reaches (`natGateFns`).
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

theorem decCI_defn_val {rd : Nat → Option Word} {q : Nat}
    {cv : IConstantVal} {v : EIdx} {hint : ConLeche.ReducibilityHint}
    (h : decCI rd q = some (.defnInfo cv v hint)) :
    ∃ w, rd q = some 1 ∧ rd (q + CI.defnValue.toNat) = some w ∧ w.toNat < 2 ^ 32 ∧ decI w = v := by
  obtain ⟨hk, -, hv, -⟩ := decCI_defnInfo_iff.mp h
  obtain ⟨w0, hw0, e0⟩ := nat?_word hk
  obtain ⟨w, hw, hl, rfl⟩ := hd?_some hv
  have e1 : w0 = 1 := UInt64.toNat_inj.mp (by rw [e0]; rfl)
  exact ⟨w, by rw [hw0, e1], hw, hl, rfl⟩

theorem decEqRL_headD {m : Mem} {r : List Word} {ps : List (EIdx × EIdx)} (h : decEqRL m r ps) :
    EqL m (r.headD 0).toNat (r.tail.headD 0).toNat ps := by
  cases r with
  | nil => simpa [decEqRL] using h
  | cons a t => cases t <;> simpa [decEqRL] using h

theorem EqL.lt64 {m : Mem} {o l : Nat} {ps : List (EIdx × EIdx)} (h : EqL m o l ps) (hI : IWOK m) :
    o + l < 2 ^ 64 := by
  have := h.1; have := hI.iw; have := hI.iwSize; unfold iwTop at *; omega

theorem decRL0 {α : Type} {g : Mem → Nat → Nat → Option (List α)} {m : Mem} {r : List Word} {l : List α}
    (h : decRL g 0 m r l) :
    g m (r.headD 0).toNat (r.tail.headD 0).toNat = some l ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m := by
  cases r with
  | nil => simpa [decRL] using h
  | cons a t => cases t <;> simpa [decRL] using h

/-- The text the gate reaches: the functions of `armText` it calls, transitively. -/
def natGateFns : List FnName :=
  ["nat_op_names", "pin_at", "iw_alloc", "sl_contains", "nat_op_guard", "nat_lit_supported", "nat_op_deps", "nat_op_pins", "nat_op_pins_a", "nat_op_pins_b", "nat_op_pins_c", "nat_op_deps_stored", "env_find", "env_row_get", "env_ix", "nat_div_mod_names", "nat_op_bool_ctors", "bool_ctor_ok", "ci_to_cv", "intern_zero", "zero_find", "zero_push", "intern_succ", "succ_find", "succ_push", "intern_sort", "sort_find", "sort_push", "cv_new", "erec_alloc", "const_e", "pin_word", "intern_const", "const_find", "const_push", "nat_op_stored_ok", "nat_op_ty_pinned", "e_view", "nat_op_cod", "nat_op_equations", "nat_eq_ctx", "intern_fvar", "fvar_find", "fvar_push", "nat_ap1", "mk_app", "der_b", "intern_app", "app_find", "app_push", "nat_eq_disp", "nat_eq_pr", "nat_eq_list2", "rec2", "nat_eq_un", "nat_ap2", "nat_eq_mu", "nat_eq_po", "nat_eq_be", "nat_eq_list4", "nat_eq_bl", "nat_eq_list3", "subst_const0_pairs", "subst_const0", "sl_cons", "iw_copy", "certify_nat_eqs", "is_def_eq_core"]

end gate

end L.Arena
