import ConAgua.Arena.IndPos2
import ConAgua.Arena.Verdict

/-!
# Error models of `nest_cont_new`, `nest_frame`, `nest_grow_group`, `nest_group_ctors` (lane
`verdicts-b`, helper `ia2`, fork `kn2a`)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

l_model nggE_spec (p : Prog) (hf : p.lookup "nest_grow_group" = some nestGrowGroupL)
  fns [hf ↦ nggE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model ngcE_spec (p : Prog) (hf : p.lookup "nest_group_ctors" = some nestGroupCtorsL)
  fns [hf ↦ ngcE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model nnewE_spec (p : Prog) (hf : p.lookup "nest_cont_new" = some nestContNewL)
  fns [hf ↦ nnewE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model nfrE_spec (p : Prog) (hf : p.lookup "nest_frame" = some nestFrameL)
  fns [hf ↦ nfrE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

end L.Ind
