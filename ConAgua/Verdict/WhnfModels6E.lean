import ConAgua.L.ModelGen
import ConAgua.Arena.Verdict
import ConAgua.Arena.WhnfM2C

/-!
# Error models of `major_to_ctor`'s pieces (lane `verdicts-b`, helper `k2`)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

namespace L.Arena

l_model mtcE_spec (p : Prog) (hf : p.lookup "major_to_ctor" = some majorToCtorL)
  fns [hf ↦ mtcE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model m2cHeadE_spec (p : Prog) (hf : p.lookup "m2c_head" = some m2cHeadL)
  fns [hf ↦ m2cHeadE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model m2cCtorE_spec (p : Prog) (hf : p.lookup "m2c_ctor" = some m2cCtorL)
  fns [hf ↦ m2cCtorE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model m2cArmsE_spec (p : Prog) (hf : p.lookup "m2c_arms" = some m2cArmsL)
  fns [hf ↦ m2cArmsE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model m2cPreE_spec (p : Prog) (hf : p.lookup "m2c_pre" = some m2cPreL)
  fns [hf ↦ m2cPreE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model m2cCheckE_spec (p : Prog) (hf : p.lookup "m2c_check" = some m2cCheckL)
  fns [hf ↦ m2cCheckE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model m2cKE_spec (p : Prog) (hf : p.lookup "m2c_k" = some m2cKL)
  fns [hf ↦ m2cKE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model m2cK2E_spec (p : Prog) (hf : p.lookup "m2c_k2" = some m2cK2L)
  fns [hf ↦ m2cK2E list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model m2cEtaE_spec (p : Prog) (hf : p.lookup "m2c_eta" = some m2cEtaL)
  fns [hf ↦ m2cEtaE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model m2cAndE_spec (p : Prog) (hf : p.lookup "m2c_and" = some m2cAndL)
  fns [hf ↦ m2cAndE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model m2cAnd2E_spec (p : Prog) (hf : p.lookup "m2c_and2" = some m2cAnd2L)
  fns [hf ↦ m2cAnd2E list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

end L.Arena
