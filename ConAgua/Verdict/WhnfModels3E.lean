import ConAgua.Arena.Verdict
import ConAgua.Arena.WhnfIotaRec
import ConAgua.Arena.WhnfM2C

/-!
# Error models of the ι family (lane `verdicts-b`, helper `k2`)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

l_model irAtE_spec (p : Prog) (hf : p.lookup "iota_rec_at" = some iotaRecAtL)
  fns [hf ↦ irAtE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model irCE_spec (p : Prog) (hf : p.lookup "iota_rec_c" = some iotaRecCL)
  fns [hf ↦ irCE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model irMajorE_spec (p : Prog) (hf : p.lookup "iota_rec_major" = some iotaRecMajorL)
  fns [hf ↦ irMajorE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model irFireE_spec (p : Prog) (hf : p.lookup "iota_rec_fire" = some iotaRecFireL)
  fns [hf ↦ irFireE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model irFamE_spec (p : Prog) (hf : p.lookup "iota_rec_fam" = some iotaRecFamL)
  fns [hf ↦ irFamE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model pmE_spec (p : Prog) (hf : p.lookup "prepare_major" = some prepareMajorL)
  fns [hf ↦ pmE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model lmtcE_spec (p : Prog) (hf : p.lookup "lit_major_to_ctor" = some litMajorToCtorL)
  fns [hf ↦ lmtcE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model pirrE_spec (p : Prog) (hf : p.lookup "proof_irrel" = some proofIrrelL)
  fns [hf ↦ pirrE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model pihE_spec (p : Prog) (hf : p.lookup "proof_irrel_half" = some proofIrrelHalfL)
  fns [hf ↦ pihE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

end L.Arena
