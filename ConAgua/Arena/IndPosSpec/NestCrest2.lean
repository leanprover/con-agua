import ConAgua.Arena.IndPosSpec.PcrW
import ConAgua.Arena.IndPosSpec.Rx

/-!
# NestCrest2

`pcrK1_zero`, `pcrK1_ok`, `nestCrest_spec`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section arms
variable (k : Nat) (m1 m2 m3 : Mem) (dO dL hO hL c f r : Word) (r1 : List Word)
theorem pcrK1_zero (h : r1.headD 0 = 0) : pcrK1 k dO dL hO hL (some (r1, m1)) = some ([0, 0], m1) := by
  simp only [pcrK1]; rw [ite_eq_left h]
theorem pcrK1_ok (h : ¬ r1.headD 0 = 0) : pcrK1 k dO dL hO hL (some (r1, m1)) =
    pcrK2 k (r1.tail.headD 0) (posRecW m1 [1, dO, dL, hO, hL]) := by simp only [pcrK1]; rw [ite_eq_right h]
end arms
attribute [ind_grind] pcrK1_zero pcrK1_ok

theorem nestCrest_spec (p : Prog) (L : CrLook p) (k : Nat) (s₀ : St) (no nl us dO dL hO hL cty : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 3)) "nest_crest" [no, nl, us, dO, dL, hO, hL, cty]
    ⦃fun r s' => LocEq s' s₀ ∧ pcrW k s₀.mem no nl us dO dL hO hL cty = some (r, s'.mem); ⊤⦄ := by
  have R := L.rx
  simp only [invoke_eq _ L.cr, callFn, nestCrest]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      nestCanonCrest_spec p R.ha R.hl R.hk L.ng L.np L.ip L.raf L.rap L.rgo L.rnd L.rcl L.ra L.cc k,
      posRec5_specW p R.ha R.h5 (k + 2), (rxSpec_all p R (k + 2)).2.2.2.2.2.2.2] <;>
    finish (gen := 20) [pcrW]

end L.Ind

end
