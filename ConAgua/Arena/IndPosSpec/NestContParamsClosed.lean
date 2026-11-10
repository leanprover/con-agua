module

public import ConAgua.Arena.IndPosSpec.FgW2
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.IndPos2
import all ConAgua.Arena.Pins

@[expose] public section

/-!
# NestContParamsClosed

`new1W_rec` and the lemmas only it uses.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem new1W_rec {m m' : Mem} {x : Word} {r : List Word} (h : new1W m x = some (r, m')) :
    posRecW m [x] = some (r.headD 0, m') ∧ r = [r.headD 0, 1] := by
  rw [posRecW_eq m [x] 1 rfl]
  simp only [new1W] at h
  rcases ha : allocW m 1 with _ | ⟨q, m1⟩ <;> rw [ha] at h; · simp at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  simp [wrIW]

end L.Ind

namespace L.Ind

open L.Arena

end L.Ind

namespace L.Ind

open L.Arena

theorem pos2Pin_spec (p : Prog) (hp : p.lookup "pin_at" = some pinAtL) (n : Nat) (s₀ : St) (i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pin_at" [i]
    ⦃fun r s' => LocEq s' s₀ ∧ pos2PinW s₀.mem i = some (r, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, pinAtL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [pos2PinW, pinW_eq, rdW_eq]

end L.Ind

end
