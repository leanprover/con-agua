import ConAgua.Arena.RecCheckSpec.PtrNamesWDec
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# Tmn

`ctorsHaveName_spec` (the model of `ctors_have_name`, `chnW`).
-/

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem ctorsHaveName_spec (p : Prog) (hp : p.lookup "ctors_have_name" = some ctorsHaveName) (n : Nat) :
    ∀ (s₀ : St) (co cl name : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ctors_have_name" [co, cl, name]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ chnW n s₀.mem co cl name = some (r.headD 0); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ co cl name; rw [invoke_eq _ hp]; simp only [callFn, ctorsHaveName]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ co cl name
    rw [invoke_eq _ hp]
    simp only [callFn, ctorsHaveName]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      finish (gen := 20)

end L.Ind

end

end
