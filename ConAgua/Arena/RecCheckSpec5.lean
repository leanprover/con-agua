import ConAgua.Arena.RecGenSpec5
import ConAgua.Arena.ConstStore

/-!
# More refinements of `RecCheck` (lane `indproofs2`, helper `rec`): `targetMajorPins`
-/

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

def tmpK3 (vis rP : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => tmpK4 (stubM "infer_type_core" m3 [vis, rP, r3.headD 0])

def tmpK2 (vis rP M : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (hd, m2) =>
    if 4294967296 ≤ hd then none
    else tmpK3 vis rP (stubM "mk_app_n_f" m2
      [hd, rdW (m2.arr64 IW) (M + 2), rdW (m2.arr64 IW) (M + 3)])

def tmpK1 (vis rP M : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m1) => tmpK2 vis rP M (ceinternW m1 (rdW (m1.arr64 IW) M) (rdW (m1.arr64 IW) (M + 1)))

/-- **The model of `target_major_pins`.** -/
def tmpW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | N + 1, m, vis, rP, M =>
    if rdW (m.arr64 IW) (M + 8) ≠ 0 then some ([], m)
    else tmpK1 vis rP M (tptW N m vis rP (rdW (m.arr64 IW) (M + 2)) (rdW (m.arr64 IW) (M + 3)))

section arms
variable (N : Nat) (m m1 m2 m3 m4 : Mem) (vis rP M hd : Word) (r1 r3 r4 : List Word)
theorem tmpW_mem (h : rdW (m.arr64 IW) (M + 8) ≠ 0) : tmpW (N + 1) m vis rP M = some ([], m) := by
  simp only [tmpW]; rw [if_pos h]
theorem tmpW_out (h : ¬ rdW (m.arr64 IW) (M + 8) ≠ 0) : tmpW (N + 1) m vis rP M =
    tmpK1 vis rP M (tptW N m vis rP (rdW (m.arr64 IW) (M + 2)) (rdW (m.arr64 IW) (M + 3))) := by
  simp only [tmpW]; rw [if_neg h]
theorem tmpK1_some : tmpK1 vis rP M (some (r1, m1)) =
    tmpK2 vis rP M (ceinternW m1 (rdW (m1.arr64 IW) M) (rdW (m1.arr64 IW) (M + 1))) := rfl
theorem tmpK2_some : tmpK2 vis rP M (some (hd, m2)) =
    if 4294967296 ≤ hd then none
    else tmpK3 vis rP (stubM "mk_app_n_f" m2 [hd, rdW (m2.arr64 IW) (M + 2), rdW (m2.arr64 IW) (M + 3)]) := rfl
theorem tmpK3_some : tmpK3 vis rP (some (r3, m3)) =
    tmpK4 (stubM "infer_type_core" m3 [vis, rP, r3.headD 0]) := rfl
theorem tmpK4_some : tmpK4 (some (r4, m4)) = some ([], m4) := rfl
end arms

grind_pattern [ind_grind] tmpW_mem => tmpW (N + 1) m vis rP M
grind_pattern [ind_grind] tmpW_out => tmpW (N + 1) m vis rP M
grind_pattern [ind_grind] tmpK1_some => tmpK1 vis rP M (some (r1, m1))
grind_pattern [ind_grind] tmpK2_some => tmpK2 vis rP M (some (hd, m2))
grind_pattern [ind_grind] tmpK3_some => tmpK3 vis rP (some (r3, m3))
grind_pattern [ind_grind] tmpK4_some => tmpK4 (some (r4, m4))

/-- The lookups `target_major_pins` needs. -/
structure TmpProg (p : Prog) : Prop where
  tpt : p.lookup "target_pin_tys" = some targetPinTys
  cf : p.lookup "const_find" = some constFind
  cp : p.lookup "const_push" = some constPush
  ic : p.lookup "intern_const" = some internConst
  tmp : p.lookup "target_major_pins" = some targetMajorPins

theorem targetMajorPins_spec (p : Prog) (h : TmpProg p) (N : Nat) (s₀ : St) (vis rP M : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p N) "target_major_pins" [vis, rP, M]
    ⦃fun r s' => LocEq s' s₀ ∧ tmpW N s₀.mem vis rP M = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.tmp]
  simp only [callFn, targetMajorPins]
  cases N with
  | zero => vcgen [exec] <;> grind
  | succ N =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        targetPinTys_spec p h.tpt N, internConst_spec p h.cf h.cp h.ic N,
        stubM_spec p "mk_app_n_f" N, stubM_spec p "infer_type_core" N] <;>
      finish (gen := 20) [rdW_eq]

end L.Ind
