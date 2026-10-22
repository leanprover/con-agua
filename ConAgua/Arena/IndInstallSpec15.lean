import ConAgua.Arena.IndInstallSpec14

/-!
# Refinements of `IndInstall`, part 15 (lane `indproofs2`, helper `install`): `checkBlockInds`

The formers' constants `cvTa₀ :: cvs.map (·.1)` (`check_block_inds_cv_tas`, `sl_cons`-built,
D18), `block_shape_with_sort` below the tops, then stage 1: the formers checked, agreed, consed.
-/

set_option experimental.vcgen true
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `check_block_inds_cv_tas` -/

def icvgK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, r.tail.headD 0], m)

mutual
/-- **The model of `check_block_inds_cv_tas_go(s, l)`** at exec fuel `n`. -/
def icvgW (p : Prog) : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, s, l => if l = 0 then some ([0, 0], m) else icvgK1 p n s (icvgW p n m (s + 1) (l - 1))
def icvgK1 (p : Prog) (n : Nat) (s : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => icvgK2 (callW p n "sl_cons" [rdW (m.arr64 IW) (rdW (m.arr64 IW) s), r.headD 0,
      r.tail.headD 0] m)
end

section arms
variable (p : Prog) (n : Nat) (m : Mem) (s l : Word) (r : List Word)
theorem icvgW_zero : icvgW p 0 m s l = none := by simp [icvgW]
theorem icvgW_nil (h : l = 0) : icvgW p (n + 1) m s l = some ([0, 0], m) := by simp [icvgW, h]
theorem icvgW_cons (h : l ≠ 0) : icvgW p (n + 1) m s l = icvgK1 p n s (icvgW p n m (s + 1) (l - 1)) := by
  simp [icvgW, h]
theorem icvgK1_some : icvgK1 p n s (some (r, m)) = icvgK2 (callW p n "sl_cons"
    [rdW (m.arr64 IW) (rdW (m.arr64 IW) s), r.headD 0, r.tail.headD 0] m) := by simp [icvgK1]
theorem icvgK2_some : icvgK2 (some (r, m)) = some ([r.headD 0, r.tail.headD 0], m) := rfl
end arms
attribute [ind_grind] icvgW_nil icvgW_cons icvgK1_some icvgK2_some

theorem icvg_spec (p : Prog) (hp : p.lookup "check_block_inds_cv_tas_go" = some checkBlockIndsCvTasGo)
    (n : Nat) : ∀ (s₀ : St) (s l : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "check_block_inds_cv_tas_go" [s, l]
    ⦃fun r s' => LocEq s' s₀ ∧ icvgW p n s₀.mem s l = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ s l; rw [invoke_eq _ hp]; simp only [callFn, checkBlockIndsCvTasGo]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ s l
    rw [invoke_eq _ hp]
    simp only [callFn, checkBlockIndsCvTasGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, callW_spec p n "sl_cons", ih] <;>
      finish (gen := 20) [rdW_eq]

/-- The model of `check_block_inds_cv_tas(c0, o, l)` (body fuel `n`). -/
def icvW (p : Prog) (n : Nat) (m : Mem) (c0 o l : Word) : Option (List Word × Mem) :=
  match callW p n "check_block_inds_cv_tas_go" [o, l] m with
  | none => none
  | some (r, m1) => icvgK2 (callW p n "sl_cons" [c0, r.headD 0, r.tail.headD 0] m1)

theorem icv_spec (p : Prog) (hp : p.lookup "check_block_inds_cv_tas" = some checkBlockIndsCvTas)
    (n : Nat) (s₀ : St) (c0 o l : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "check_block_inds_cv_tas" [c0, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ icvW p n s₀.mem c0 o l = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkBlockIndsCvTas]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "check_block_inds_cv_tas_go", callW_spec p n "sl_cons"] <;>
    finish (gen := 20) [icvW, rdW_eq]

end L.Ind
