import ConAgua.Arena.IndPosSpec.NoConstWf
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# NestOccAny

`noaW`, `noaK`, `noaW_nil`, `noaW_cons`, `noaK_hit`, `noaK_miss` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `nest_occ_any`: `xs.anyM (nestOcc names lo hi ·)` -/

mutual
def noaW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | k + 1, m, no, nl, lo, hi, off, l =>
    if l = 0 then some ([0], m) else noaK k no nl lo hi off l (noConstWf k m no nl lo hi (rdW (m.arr64 IW) off))
def noaK (k : Nat) (no nl lo hi off l : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (b, m1) => if b ≠ 0 then some ([1], m1) else noaW k m1 no nl lo hi (off + 1) (l - 1)
end

section arms
variable (k : Nat) (m m1 : Mem) (no nl lo hi off l b : Word)
theorem noaW_nil (h : l = 0) : noaW (k + 1) m no nl lo hi off l = some ([0], m) := by simp [noaW, h]
theorem noaW_cons (h : ¬ l = 0) : noaW (k + 1) m no nl lo hi off l =
    noaK k no nl lo hi off l (noConstWf k m no nl lo hi (rdW (m.arr64 IW) off)) := by simp [noaW, h]
theorem noaK_hit (h : b ≠ 0) : noaK k no nl lo hi off l (some (b, m1)) = some ([1], m1) := by rw [noaK, ite_eq_left h]
theorem noaK_miss (h : ¬ b ≠ 0) : noaK k no nl lo hi off l (some (b, m1)) =
    noaW k m1 no nl lo hi (off + 1) (l - 1) := by rw [noaK, ite_eq_right h]
end arms
attribute [ind_grind] noaW_nil noaW_cons noaK_hit noaK_miss

theorem nestOccAny_spec (p : Prog) (hl : NoLook p) (hp : p.lookup "nest_occ_any" = some nestOccAnyL)
    (k : Nat) : ∀ (s₀ : St) (no nl lo hi off ln : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_occ_any" [no, nl, lo, hi, off, ln]
    ⦃fun r s' => LocEq s' s₀ ∧ noaW k s₀.mem no nl lo hi off ln = some ([r.headD 0], s'.mem); ⊤⦄ := by
  induction k with
  | zero =>
    intro s₀ no nl lo hi off ln
    rw [invoke_eq _ hp]; simp only [callFn, nestOccAnyL]; vcgen [exec] <;> grind
  | succ k ih =>
    intro s₀ no nl lo hi off ln
    simp only [invoke_eq _ hp, callFn, nestOccAnyL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, nestOcc_spec' p hl k, ih] <;>
      finish (gen := 20) [Locals.init_cons_zero]

end L.Ind

end
