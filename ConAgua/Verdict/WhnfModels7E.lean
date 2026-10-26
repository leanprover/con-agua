import ConAgua.L.ModelGen
import ConAgua.Arena.Verdict
import ConAgua.Arena.DefEq
import ConAgua.Arena.WhnfEntry

/-!
# Error models of the `whnf` family's `defeq` helpers (lane `verdicts-b`, helper `k2`)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

namespace L.Arena

l_model btsE_spec (p : Prog) (hf : p.lookup "bool_true_shortcut" = some boolTrueShortcutL)
  fns [hf ↦ btsE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model tupaE_spec (p : Prog) (hf : p.lookup "try_unfold_proj_app" = some tryUnfoldProjAppL)
  fns [hf ↦ tupaE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model dqE_spec (p : Prog) (hf : p.lookup "delta_quick" = some deltaQuickL)
  fns [hf ↦ dqE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model lnE_spec (p : Prog) (hf : p.lookup "lazy_nat" = some lazyNatL)
  fns [hf ↦ lnE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model wtopE_spec (p : Prog) (hf : p.lookup "whnf_top" = some whnfTopL)
  fns [hf ↦ wtopE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model ecE_spec (p : Prog) (hf : p.lookup "eta_cert" = some etaCertL)
  fns [hf ↦ ecE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model ecbE_spec (p : Prog) (hf : p.lookup "eta_cert_body" = some etaCertBodyL)
  fns [hf ↦ ecbE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model ectE_spec (p : Prog) (hf : p.lookup "eta_cert_ty" = some etaCertTyL)
  fns [hf ↦ ectE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model secE_spec (p : Prog) (hf : p.lookup "struct_eta_cert" = some structEtaCertL)
  fns [hf ↦ secE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model secwE_spec (p : Prog) (hf : p.lookup "struct_eta_cert_with" = some structEtaCertWithL)
  fns [hf ↦ secwE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model secwtbE_spec (p : Prog) (hf : p.lookup "struct_eta_cert_wtb" = some structEtaCertWtbL)
  fns [hf ↦ secwtbE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model secgE_spec (p : Prog) (hf : p.lookup "struct_eta_cert_go" = some structEtaCertGoL)
  fns [hf ↦ secgE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model sectE_spec (p : Prog) (hf : p.lookup "struct_eta_cert_tail" = some structEtaCertTailL)
  fns [hf ↦ sectE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model sucE_spec (p : Prog) (hf : p.lookup "struct_unit_cert" = some structUnitCertL)
  fns [hf ↦ sucE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model suhE_spec (p : Prog) (hf : p.lookup "struct_unit_head" = some structUnitHeadL)
  fns [hf ↦ suhE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model sutE_spec (p : Prog) (hf : p.lookup "struct_unit_tail" = some structUnitTailL)
  fns [hf ↦ sutE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

end L.Arena
