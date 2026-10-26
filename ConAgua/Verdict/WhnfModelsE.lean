import ConAgua.L.ModelGen
import ConAgua.Arena.Verdict
import ConAgua.Arena.WhnfCoreSlot
import ConAgua.Arena.WhnfDelta

/-!
# Error models of the `whnf` family's slot bodies (lane `verdicts-b`, helper `k2`)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

l_model whnfCore_specE (p : Prog) (hf : p.lookup "whnf_core" = some whnfCoreL)
  fns [hf ↦ whnfCoreE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model whnfCoreLoop_specE (p : Prog) (hf : p.lookup "whnf_core_loop" = some whnfCoreLoopL)
  fns [hf ↦ whnfCoreLoopE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] finish [tierW, idxW] errors

l_model whnfCoreStep_specE (p : Prog) (hf : p.lookup "whnf_core_step" = some whnfCoreStepL)
  fns [hf ↦ whnfCoreStepE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model whnf_specE (p : Prog) (hf : p.lookup "whnf" = some whnfL)
  fns [hf ↦ whnfE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] finish [tierW, idxW] errors

l_model whnfLoop_specE (p : Prog) (hf : p.lookup "whnf_loop" = some whnfLoopL)
  fns [hf ↦ whnfLoopE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] finish [tierW, idxW] errors

l_model whnfStep_specE (p : Prog) (hf : p.lookup "whnf_step" = some whnfStepL)
  fns [hf ↦ whnfStepE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] finish [tierW, idxW] errors

end L.Arena
