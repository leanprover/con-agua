import ConAgua.Arena.IndDecStab
import ConAgua.Arena.RecCheckSpec

/-!
# More refinements of `RecCheck` (lane `indproofs2`, helper `rec`): `targetMajorPins`
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `target_major_pins` -/

def tmpK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m4) => some ([], m4)

def tmpK3 (cR : CallM) (N : Nat) (vis rP : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => tmpK4 (cR N "infer_type_core" [vis, rP, r3.headD 0] m3)

def tmpK2 (cR : CallM) (N : Nat) (vis rP M : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (hd, m2) =>
    if 4294967296 ≤ hd then none
    else tmpK3 cR N vis rP (mknF m2
      [hd, rdW (m2.arr64 IW) (M + 2), rdW (m2.arr64 IW) (M + 3)])

def tmpK1 (cR : CallM) (N : Nat) (vis rP M : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m1) => tmpK2 cR N vis rP M (ceinternW m1 (rdW (m1.arr64 IW) M) (rdW (m1.arr64 IW) (M + 1)))

/-- **The model of `target_major_pins`** (the core's call read through `cR`). -/
def tmpW (cR : CallM) : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | N + 1, m, vis, rP, M =>
    if rdW (m.arr64 IW) (M + 8) ≠ 0 then some ([], m)
    else tmpK1 cR N vis rP M (tptW cR N m vis rP (rdW (m.arr64 IW) (M + 2)) (rdW (m.arr64 IW) (M + 3)))

section arms
variable (cR : CallM) (N : Nat) (m m1 m2 m3 m4 : Mem) (vis rP M hd : Word) (r1 r3 r4 : List Word)
theorem tmpW_mem (h : rdW (m.arr64 IW) (M + 8) ≠ 0) : tmpW cR (N + 1) m vis rP M = some ([], m) := by
  simp only [tmpW]; rw [ite_eq_left h]
theorem tmpW_out (h : ¬ rdW (m.arr64 IW) (M + 8) ≠ 0) : tmpW cR (N + 1) m vis rP M =
    tmpK1 cR N vis rP M (tptW cR N m vis rP (rdW (m.arr64 IW) (M + 2)) (rdW (m.arr64 IW) (M + 3))) := by
  simp only [tmpW]; rw [ite_eq_right h]
theorem tmpK1_some : tmpK1 cR N vis rP M (some (r1, m1)) =
    tmpK2 cR N vis rP M (ceinternW m1 (rdW (m1.arr64 IW) M) (rdW (m1.arr64 IW) (M + 1))) := rfl
theorem tmpK2_some : tmpK2 cR N vis rP M (some (hd, m2)) =
    if 4294967296 ≤ hd then none
    else tmpK3 cR N vis rP (mknF m2 [hd, rdW (m2.arr64 IW) (M + 2), rdW (m2.arr64 IW) (M + 3)]) := rfl
theorem tmpK3_some : tmpK3 cR N vis rP (some (r3, m3)) =
    tmpK4 (cR N "infer_type_core" [vis, rP, r3.headD 0] m3) := rfl
theorem tmpK4_some : tmpK4 (some (r4, m4)) = some ([], m4) := rfl
end arms

grind_pattern [ind_grind] tmpW_mem => tmpW cR (N + 1) m vis rP M
grind_pattern [ind_grind] tmpW_out => tmpW cR (N + 1) m vis rP M
grind_pattern [ind_grind] tmpK1_some => tmpK1 cR N vis rP M (some (r1, m1))
grind_pattern [ind_grind] tmpK2_some => tmpK2 cR N vis rP M (some (hd, m2))
grind_pattern [ind_grind] tmpK3_some => tmpK3 cR N vis rP (some (r3, m3))
grind_pattern [ind_grind] tmpK4_some => tmpK4 (some (r4, m4))

/-- The lookups `target_major_pins` needs. -/
structure TmpProg (p : Prog) : Prop where
  ad : AdF p
  tpt : p.lookup "target_pin_tys" = some targetPinTys
  cf : p.lookup "const_find" = some constFind
  cp : p.lookup "const_push" = some constPush
  ic : p.lookup "intern_const" = some internConst
  tmp : p.lookup "target_major_pins" = some targetMajorPins

theorem targetMajorPins_spec (p : Prog) (h : TmpProg p) (cR : CallM) (hcR : CallSpec p cR) (N : Nat)
    (s₀ : St) (vis rP M : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p N) "target_major_pins" [vis, rP, M]
    ⦃fun r s' => LocEq s' s₀ ∧ tmpW cR N s₀.mem vis rP M = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.tmp]
  simp only [callFn, targetMajorPins]
  cases N with
  | zero => vcgen [exec] <;> grind
  | succ N =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        targetPinTys_spec p h.tpt cR hcR N, internConst_spec p h.cf h.cp h.ic N,
        mknF_spec p h.ad N, hcR N "infer_type_core"] <;>
      finish (gen := 20) [rdW_eq]

theorem decTM_ds {m : Mem} {p : Nat} {M : TargetMajor} (h : decTM m p = some M) :
    ∃ o l, iwN m (p + 2) = some o ∧ iwN m (p + 3) = some l ∧ decHL m o l = some M.ds := by
  simp only [decTM, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨w5, h5, a1, ha1, w4, h4, w3, h3, w2, h2, ac, hac, w1, hw1, w0, h0, a, ha, rfl⟩ := h
  obtain ⟨o, l, ho, hl, hd⟩ := decAt_some h4
  exact ⟨o, l, ho, by simpa using hl, hd⟩

/-- A non-empty slice decoded below the tops ends below the top. -/
theorem decHL_truncM_bound {k : IdxKind} {m : Mem} {o l : Nat} {xs : List (Idx k)}
    (h : decHL (truncM m) o l = some xs) (hl : l ≠ 0) : o + l ≤ iwTop m := by
  have := decHL_getI h (l - 1) (by omega)
  simp only [iwH, hd?] at this
  cases hw : (iwA (truncM m))[o + (l - 1)]? with
  | none => simp [hw] at this
  | some w =>
    have := (truncM_iw_get hw).1
    omega

end L.Ind
