import ConAgua.Arena.IndSumSpec.TsrW

/-!
# TgtStoredRules: `ConRon.Arena.tgtStoredRules`

The refinement theorems `tgtStoredRules_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **`tgt_stored_rules` (with `tgt_stored_rules_remap`, `tgt_rule_nested`) refines `tgtStoredRules`**
(through `sum_rules`' `rec_rule_bits` and `aux_rule_fire`'s `abstract1_fast` stubs): the major's
record and the right-hand sides decoded below the tops; the rules a pointer slice of rule records
in the record pool. (The constant `cv` is the recursor's; `sum_rules` reads only its name word, which
neither side's result depends on.) -/
@[refines ConRon.Arena.tgtStoredRules]
theorem tgtStoredRules_refines (p : Prog) (L : TsrLook p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis cv rP M rhso rhsl : Word) (cvv : IConstantVal)
    (TM : TargetMajor) (rhss : List EIdx) (hS : StageR dn vis fe s₀.mem a₀)
    (_hcv : DecB (fun m => decCVp m cv.toNat) s₀.mem cvv)
    (hM : DecB (fun m => decTM m M.toNat) s₀.mem TM) (hrh : DecB (fun m => decHL m rhso.toNat rhsl.toNat) s₀.mem rhss)
    (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "tgt_stored_rules" [vis, cv, rP, M, rhso, rhsl]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.tgtStoredRules fe cvv rP.toNat TM rhss) a₀ ∧
      decPL s'.mem (rlDec s'.mem) (r.headD 0).toNat (r.tail.headD 0).toNat =
        some (AM.res (ConRon.Arena.tgtStoredRules fe cvv rP.toNat TM rhss) a₀) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop s'.mem ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.tgtStoredRules fe cvv rP.toNat TM rhss) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (tsr_spec p L n s₀ vis cv rP M rhso rhsl) ?_
  rintro r s' ⟨hl', hm⟩
  obtain ⟨rules, a', run, hd, hb, hS', hg, hA'⟩ := tsrW_ok dn fe vis n hm hS hM hrh hA (cvv := cvv)
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl', hok, by rw [hres]; exact hd, hb, by rw [hst]; exact hS', hg, hA'⟩

end L.Ind

end
