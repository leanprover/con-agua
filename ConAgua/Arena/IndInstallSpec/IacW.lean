import ConAgua.Arena.IndInstall
import ConAgua.Arena.WhnfBase
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# IacW

`iaaW`, the hand model of `check_abs_ctor_sorts_all` (`check_abs_ctor_sorts` through its run), with
its continuations, their arms and its spec `iaa_spec`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `check_abs_ctor_sorts_all` -/

def iaaK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => some ([0], m)

mutual
/-- **The model of `check_abs_ctor_sorts_all(vis, ctx, isProp, sO, sL, oO, oL)`** at exec fuel `n`. -/
def iaaW (p : Prog) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, ctx, isP, so, sl, oo, ol =>
    if sl = 0 then some ([0], m) else if ol = 0 then some ([0], m)
    else iaaK1 p n vis ctx isP so sl oo ol (callW p n "check_abs_ctor_sorts" [vis, ctx, isP,
      rdW (m.arr64 IW) (rdW (m.arr64 IW) so), rdW (m.arr64 IW) (rdW (m.arr64 IW) so + 1),
      rdW (m.arr64 IW) (rdW (m.arr64 IW) oo), rdW (m.arr64 IW) (rdW (m.arr64 IW) oo + 1)] m)
def iaaK1 (p : Prog) (n : Nat) (vis ctx isP so sl oo ol : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => iaaK2 (iaaW p n m vis ctx isP (so + 1) (sl - 1) (oo + 1) (ol - 1))
end

section arms
variable (p : Prog) (n : Nat) (m : Mem) (vis ctx isP so sl oo ol : Word) (r : List Word)
theorem iaaW_zero : iaaW p 0 m vis ctx isP so sl oo ol = none := by simp [iaaW]
theorem iaaW_nil1 (h : sl = 0) : iaaW p (n + 1) m vis ctx isP so sl oo ol = some ([0], m) := by
  simp [iaaW, h]
theorem iaaW_nil2 (h1 : sl ≠ 0) (h : ol = 0) : iaaW p (n + 1) m vis ctx isP so sl oo ol = some ([0], m) := by
  simp [iaaW, h1, h]
theorem iaaW_cons (h1 : sl ≠ 0) (h2 : ol ≠ 0) : iaaW p (n + 1) m vis ctx isP so sl oo ol =
    iaaK1 p n vis ctx isP so sl oo ol (callW p n "check_abs_ctor_sorts" [vis, ctx, isP,
      rdW (m.arr64 IW) (rdW (m.arr64 IW) so), rdW (m.arr64 IW) (rdW (m.arr64 IW) so + 1),
      rdW (m.arr64 IW) (rdW (m.arr64 IW) oo), rdW (m.arr64 IW) (rdW (m.arr64 IW) oo + 1)] m) := by
  simp [iaaW, h1, h2]
theorem iaaK1_some : iaaK1 p n vis ctx isP so sl oo ol (some (r, m)) =
    iaaK2 (iaaW p n m vis ctx isP (so + 1) (sl - 1) (oo + 1) (ol - 1)) := by simp [iaaK1]
theorem iaaK2_some : iaaK2 (some (r, m)) = some ([0], m) := rfl
end arms
attribute [ind_grind] iaaW_nil1 iaaW_nil2 iaaW_cons iaaK1_some iaaK2_some

theorem iaa_spec (p : Prog) (hp : p.lookup "check_abs_ctor_sorts_all" = some checkAbsCtorSortsAll)
    (n : Nat) : ∀ (s₀ : St) (vis ctx isP so sl oo ol : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "check_abs_ctor_sorts_all" [vis, ctx, isP, so, sl, oo, ol]
    ⦃fun r s' => LocEq s' s₀ ∧ iaaW p n s₀.mem vis ctx isP so sl oo ol = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ vis ctx isP so sl oo ol; rw [invoke_eq _ hp]; simp only [callFn, checkAbsCtorSortsAll]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ vis ctx isP so sl oo ol
    rw [invoke_eq _ hp]
    simp only [callFn, checkAbsCtorSortsAll]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "check_abs_ctor_sorts", ih] <;>
      finish (gen := 20) [rdW_eq]

end L.Ind

end
