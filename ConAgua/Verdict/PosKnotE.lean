import ConAgua.Verdict.PosE
import ConAgua.Verdict.WhnfMidE
import ConAgua.Verdict.DefEqBaseE

/-!
# `whnf_top`'s error claim under `StageT`

`whnfTop_stageE`: from the error knot.
-/


open ConRon.Arena

namespace L.Ind

open L.Arena

/-- **`whnf_top`'s error claim under `StageT`** (`WhnfTopE`), from the error knot. -/
theorem whnfTop_stageE {p : Prog} (hw : p.lookup "whnf_top" = some whnfTopL)
    (hKE : ∀ n, KnotOKE p n) : WhnfTopE p := by
  intro n hn dn vis fe m a hS dep t ht e hc
  refine ErrClaim.of_callE_succ hc fun k hk hc' => ?_
  subst hk
  obtain ⟨M, hC⟩ := hS.core
  exact CoreSpecE.of_callE (s₀ := ⟨m, Locals.init []⟩)
    (whnfTop_refinesE p hw k (fun j _ => hKE j) hn checkFuel (stage_fuel hn) ⟨m, Locals.init []⟩ a dn vis fe M
      dep t hC (hw_of_h ht)) hc'

end L.Ind
