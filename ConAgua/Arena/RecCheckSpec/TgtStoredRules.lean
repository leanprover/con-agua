module

import ConAgua.Arena.IndSumSpec.TsrW
public import ConAgua.Arena.IndSumSpec.SumRules
public import ConAgua.Arena.RecCheckSpec.TsrLook

@[expose] public section

/-!
# TgtStoredRules: `ConRon.Arena.generatedRules`

The refinement theorem `generatedRules_refines` (the twin's `tgtStoredRules` is `generatedRules` now).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **`generated_rules` refines `generatedRules`**: the rules at the returned slice (`sum_rules` at
a member major; at an outside major the rules rebuilt with `auxRuleFire`'s nested fire), every
record's eleven words in the pool. -/
@[refines ConRon.Arena.generatedRules]
theorem generatedRules_refines (p : Prog) (hL : TsrLook p) (hpu : p.lookup "erec_put" = some erecPut)
    (n : Nat) (s₀ : St) (a₀ : AState) (fe : IFEnv) (vis rP M rhso rhsl : Word) (TM : TargetMajor)
    (rhss : List EIdx) (hS : StageR vis fe s₀.mem a₀) (hM : DecB (fun m => decTM m M.toNat) s₀.mem TM)
    (hrh : DecB (fun m => decHL m rhso.toNat rhsl.toNat) s₀.mem rhss) (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "generated_rules" [rP, M, rhso, rhsl]
    ⦃fun r s' => LocEq s' s₀ ∧ ∃ rules a',
      (ConRon.Arena.generatedRules rP.toNat TM rhss).run a₀ = .ok (rules, a') ∧
      decPL s'.mem (rlDec s'.mem) (r.headD 0).toNat (r.tail.headD 0).toNat = some rules ∧
      RuleWordsIn s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop s'.mem ∧ StageR vis fe s'.mem a' ∧
      IWGrow s₀.mem s'.mem ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (tsr_spec p hL hpu n s₀ rP M rhso rhsl) fun _ _ ⟨hl, hm⟩ =>
    ⟨hl, tsrW_ok fe vis n hm hS hM hrh hA⟩


end L.Ind

end
