import ConAgua.Verdict.IndA3
import ConAgua.Verdict.IndA5
import ConAgua.Verdict.IndBE
import ConAgua.Verdict.DeclValE
import ConAgua.Arena.IndT.Install4

/-!
# `check_block_inds`' error refinement: the error models (lane `verdicts-b`, helper `ia2-inds`)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

l_model cbdaE_spec (p : Prog) (hf : p.lookup "check_block_doms_at" = some checkBlockDomsAt)
  fns [hf ↦ cbdaE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model cbaoE_spec (p : Prog) (hf : p.lookup "check_block_agree_one" = some checkBlockAgreeOne)
  fns [hf ↦ cbaoE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model cbagE_spec (p : Prog) (hf : p.lookup "check_block_agree" = some checkBlockAgree)
  fns [hf ↦ cbagE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model cbtE_spec (p : Prog) (hf : p.lookup "check_block_tele" = some checkBlockTele)
  fns [hf ↦ cbtE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model cbtsE_spec (p : Prog) (hf : p.lookup "check_block_teles" = some checkBlockTeles)
  fns [hf ↦ cbtsE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model cbiE_spec (p : Prog) (hf : p.lookup "check_block_inds" = some checkBlockInds)
  fns [hf ↦ cbiE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

end L.Ind
