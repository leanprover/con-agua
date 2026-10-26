import ConAgua.Verdict.PosE
import ConAgua.Verdict.IndA3
import ConAgua.Verdict.IndBE
import ConAgua.Arena.IndT.Positivity

/-!
# The positivity pass's entry points: error models (lane `verdicts-b`, helper `ia2`, fork `top`)

The `errors` models of `check_abs_ctor_sorts_one`, `check_abs_ctor_sorts`,
`check_abs_ctor_sorts_all`, `nest_uniform`, `nest_root`, `nest_seeds`, `check_block_positivity`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

l_model iaoE_spec (p : Prog) (hf : p.lookup "check_abs_ctor_sorts_one" = some checkAbsCtorSortsOne)
  fns [hf ↦ iaoE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model iacE_spec (p : Prog) (hf : p.lookup "check_abs_ctor_sorts" = some checkAbsCtorSorts)
  fns [hf ↦ iacE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model iaaE_spec (p : Prog) (hf : p.lookup "check_abs_ctor_sorts_all" = some checkAbsCtorSortsAll)
  fns [hf ↦ iaaE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model nuE_spec (p : Prog) (hf : p.lookup "nest_uniform" = some nestUniformL)
  fns [hf ↦ nuE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model nrtE_spec (p : Prog) (hf : p.lookup "nest_root" = some nestRootL)
  fns [hf ↦ nrtE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model nsdE_spec (p : Prog) (hf : p.lookup "nest_seeds" = some nestSeedsL)
  fns [hf ↦ nsdE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model cbpE_spec (p : Prog) (hf : p.lookup "check_block_positivity" = some checkBlockPositivity)
  fns [hf ↦ cbpE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

end L.Ind
