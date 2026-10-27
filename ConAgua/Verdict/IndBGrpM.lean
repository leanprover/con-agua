import ConAgua.Arena.RecGen
import ConAgua.Arena.Verdict
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# The error model of `gen_rec_check_prep` (lane `verdicts-b`, helper `ib`)

Generated alone: it takes minutes (the function has twelve callees and the record's fourteen
writes).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

l_model grpE_spec (p : Prog) (hf : p.lookup "gen_rec_check_prep" = some genRecCheckPrep)
  fns [hf ↦ grpE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 20000000 simp [Cmp.evalW, Cmp.eval] errors locals

end L.Ind
