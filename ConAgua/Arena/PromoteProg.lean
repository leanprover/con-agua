import ConAgua.Arena.Promote
import ConAgua.Arena.LiftSpec
import ConAgua.Arena.SortStore
import ConAgua.Arena.ConstStore
import ConAgua.Arena.FVarStore
import ConAgua.Arena.NAnonStore
import ConAgua.Arena.NStrStore
import ConAgua.Arena.NNumStore
import ConAgua.Arena.ZeroStore
import ConAgua.Arena.LevelStore
import ConAgua.Arena.MaxStore
import ConAgua.Arena.ImaxStore
import ConAgua.Arena.ParamStore
import ConAgua.Arena.LsStore
import ConAgua.Arena.LevelEquiv
import ConAgua.Arena.Env
import ConAgua.Compiler.WF

/-!
# The promotion's program: every function it calls, by name

`PromoteProg p`: the lookups the promotion's specs need (this module's functions, the four
memos, the stores' interners with their probes and appends, `mk_*`, the views `e_view`,
`lv_node`, `ls_node`, `erec_alloc`, the environment's row functions). `promoteProg` is that
program; `promoteProg_ok` and `promoteProg_wf` (it closes over itself).
-/

open ConRon.Arena

namespace L.Arena

/-- What the promotion's specs need of the program. -/
structure PromoteProg (p : Prog) : Prop where
  pi_bvar : p.lookup "pi_bvar" = some (piBVar)
  pi_fvar : p.lookup "pi_fvar" = some (piFVar)
  pi_sort : p.lookup "pi_sort" = some (piSort)
  pi_const : p.lookup "pi_const" = some (piConst)
  pi_app : p.lookup "pi_app" = some (piApp)
  pi_lam : p.lookup "pi_lam" = some (piLam)
  pi_forall : p.lookup "pi_forall" = some (piForall)
  pi_let : p.lookup "pi_let" = some (piLet)
  pi_lit : p.lookup "pi_lit" = some (piLit)
  pi_lit_str : p.lookup "pi_lit_str" = some (piLitStr)
  pi_proj : p.lookup "pi_proj" = some (piProj)
  pi_nanon : p.lookup "pi_nanon" = some (piNAnon)
  pi_nstr : p.lookup "pi_nstr" = some (piNStr)
  pi_nnum : p.lookup "pi_nnum" = some (piNNum)
  pi_zero : p.lookup "pi_zero" = some (piZero)
  pi_succ : p.lookup "pi_succ" = some (piSucc)
  pi_max : p.lookup "pi_max" = some (piMax)
  pi_imax : p.lookup "pi_imax" = some (piImax)
  pi_param : p.lookup "pi_param" = some (piParam)
  pi_ls : p.lookup "pi_ls" = some (piLs)
  pn_arm : p.lookup "pn_arm" = some (pnArm)
  promote_n : p.lookup "promote_n" = some (promoteNL)
  pl_arm : p.lookup "pl_arm" = some (plArm)
  promote_l : p.lookup "promote_l" = some (promoteLL)
  promote_l_pool : p.lookup "promote_l_pool" = some (promoteLPool)
  pls_arm : p.lookup "pls_arm" = some (plsArm)
  promote_ls : p.lookup "promote_ls" = some (promoteLsL)
  pe_lit : p.lookup "pe_lit" = some (peLit)
  pe_const : p.lookup "pe_const" = some (peConst)
  pe_app : p.lookup "pe_app" = some (peApp)
  pe_lam : p.lookup "pe_lam" = some (peLam)
  pe_forall : p.lookup "pe_forall" = some (peForall)
  pe_let : p.lookup "pe_let" = some (peLet)
  pe_proj : p.lookup "pe_proj" = some (peProj)
  pe_arm : p.lookup "pe_arm" = some (peArm)
  promote_e : p.lookup "promote_e" = some (promoteEL)
  promote_n_list : p.lookup "promote_n_list" = some (promoteNListL)
  promote_l_list : p.lookup "promote_l_list" = some (promoteLListL)
  promote_e_list : p.lookup "promote_e_list" = some (promoteEListL)
  promote_slice : p.lookup "promote_slice" = some (promoteSlice)
  promote_cv : p.lookup "promote_cv" = some (promoteCVL)
  promote_fire : p.lookup "promote_fire" = some (promoteFireL)
  promote_rule : p.lookup "promote_rule" = some (promoteRuleL)
  promote_rules : p.lookup "promote_rules" = some (promoteRulesL)
  promote_caps : p.lookup "promote_caps" = some (promoteCapsL)
  promote_proj_table : p.lookup "promote_proj_table" = some (promoteProjTableL)
  pci_cv : p.lookup "pci_cv" = some (pciCv)
  pci_defn : p.lookup "pci_defn" = some (pciDefn)
  pci_ind : p.lookup "pci_ind" = some (pciInd)
  pci_ctor : p.lookup "pci_ctor" = some (pciCtor)
  pci_rec : p.lookup "pci_rec" = some (pciRec)
  promote_ci : p.lookup "promote_ci" = some (promoteCIL)
  promote_ci_list : p.lookup "promote_ci_list" = some (promoteCIListL)
  promote_clear : p.lookup "promote_clear" = some (promoteClear)
  promote_vg : p.lookup "promote_vg" = some (promoteVGL)
  erase_installed : p.lookup "erase_installed" = some (eraseInstalledL)
  index_promoted : p.lookup "index_promoted" = some (indexPromotedL)
  promote_new : p.lookup "promote_new" = some (promoteNewL)
  pn_find : p.lookup "pn_find" = some (memoFindG pnSch)
  pn_put : p.lookup "pn_put" = some (memoPutG pnSch)
  pn_clear : p.lookup "pn_clear" = some (memoClearG pnSch)
  pl_find : p.lookup "pl_find" = some (memoFindG plSch)
  pl_put : p.lookup "pl_put" = some (memoPutG plSch)
  pl_clear : p.lookup "pl_clear" = some (memoClearG plSch)
  pls_find : p.lookup "pls_find" = some (memoFindG plsSch)
  pls_put : p.lookup "pls_put" = some (memoPutG plsSch)
  pls_clear : p.lookup "pls_clear" = some (memoClearG plsSch)
  pe_find : p.lookup "pe_find" = some (memoFindG peSch)
  pe_put : p.lookup "pe_put" = some (memoPutG peSch)
  pe_clear : p.lookup "pe_clear" = some (memoClearG peSch)
  der_b : p.lookup "der_b" = some (derB)
  mk_app : p.lookup "mk_app" = some (mkApp)
  mk_lam : p.lookup "mk_lam" = some (mkLam)
  mk_forall : p.lookup "mk_forall" = some (mkForall)
  mk_let : p.lookup "mk_let" = some (mkLet)
  mk_proj : p.lookup "mk_proj" = some (mkProj)
  bvar_find : p.lookup "bvar_find" = some (bvarFind)
  bvar_push : p.lookup "bvar_push" = some (bvarPush)
  intern_bvar : p.lookup "intern_bvar" = some (internBVar)
  app_find : p.lookup "app_find" = some (appFind)
  app_push : p.lookup "app_push" = some (appPush)
  intern_app : p.lookup "intern_app" = some (internApp)
  lam_find : p.lookup "lam_find" = some (lamFind)
  lam_push : p.lookup "lam_push" = some (lamPush)
  intern_lam : p.lookup "intern_lam" = some (internLamL)
  forall_find : p.lookup "forall_find" = some (forallFind)
  forall_push : p.lookup "forall_push" = some (forallPush)
  intern_forall : p.lookup "intern_forall" = some (internForallL)
  letE_find : p.lookup "letE_find" = some (letFind)
  letE_push : p.lookup "letE_push" = some (letPush)
  intern_letE : p.lookup "intern_letE" = some (internLet)
  proj_find : p.lookup "proj_find" = some (projFind)
  proj_push : p.lookup "proj_push" = some (projPush)
  intern_proj : p.lookup "intern_proj" = some (internProj)
  sort_find : p.lookup "sort_find" = some (sortFind)
  sort_push : p.lookup "sort_push" = some (sortPush)
  intern_sort : p.lookup "intern_sort" = some (internSort)
  const_find : p.lookup "const_find" = some (constFind)
  const_push : p.lookup "const_push" = some (constPush)
  intern_const : p.lookup "intern_const" = some (internConst)
  fvar_find : p.lookup "fvar_find" = some (fvarFind)
  fvar_push : p.lookup "fvar_push" = some (fvarPush)
  intern_fvar : p.lookup "intern_fvar" = some (internFVar)
  lit_hash : p.lookup "lit_hash" = some (litHash)
  limbs_eq : p.lookup "limbs_eq" = some (limbsEq)
  lit_match : p.lookup "lit_match" = some (litMatch)
  lit_find : p.lookup "lit_find" = some (litFind)
  lit_push : p.lookup "lit_push" = some (litPush)
  intern_lit : p.lookup "intern_lit" = some (internLit)
  lit_match_str : p.lookup "lit_match_str" = some (litMatchStr)
  lit_find_str : p.lookup "lit_find_str" = some (litFindStr)
  lit_push_str : p.lookup "lit_push_str" = some (litPushStr)
  intern_lit_str : p.lookup "intern_lit_str" = some (internLitStr)
  nanon_find : p.lookup "nanon_find" = some (nanonFind)
  nanon_push : p.lookup "nanon_push" = some (nanonPush)
  intern_nanon : p.lookup "intern_nanon" = some (internNAnon)
  nstr_match : p.lookup "nstr_match" = some (nsMatch)
  nstr_find : p.lookup "nstr_find" = some (nsFind)
  nstr_push : p.lookup "nstr_push" = some (nsPush)
  intern_nstr : p.lookup "intern_nstr" = some (internNStr)
  nnum_find : p.lookup "nnum_find" = some (nnumFind)
  nnum_push : p.lookup "nnum_push" = some (nnumPush)
  intern_nnum : p.lookup "intern_nnum" = some (internNNum)
  zero_find : p.lookup "zero_find" = some (zeroFind)
  zero_push : p.lookup "zero_push" = some (zeroPush)
  intern_zero : p.lookup "intern_zero" = some (internZero)
  succ_find : p.lookup "succ_find" = some (succFind)
  succ_push : p.lookup "succ_push" = some (succPush)
  intern_succ : p.lookup "intern_succ" = some (internSucc)
  max_find : p.lookup "max_find" = some (maxFind)
  max_push : p.lookup "max_push" = some (maxPush)
  intern_max : p.lookup "intern_max" = some (internMax)
  imax_find : p.lookup "imax_find" = some (imaxFind)
  imax_push : p.lookup "imax_push" = some (imaxPush)
  intern_imax : p.lookup "intern_imax" = some (internImax)
  param_find : p.lookup "param_find" = some (paramFind)
  param_push : p.lookup "param_push" = some (paramPush)
  intern_param : p.lookup "intern_param" = some (internParam)
  ls_match : p.lookup "ls_match" = some (lsMatch)
  ls_find : p.lookup "ls_find" = some (lsFind)
  ls_push : p.lookup "ls_push" = some (lsPush)
  intern_ls : p.lookup "intern_ls" = some (internLs)
  lv_node : p.lookup "lv_node" = some (lvNode)
  ls_node : p.lookup "ls_node" = some (lsNode)
  e_view : p.lookup "e_view" = some (L.Ind.eView)
  erec_alloc : p.lookup "erec_alloc" = some (L.Ind.erecAlloc)
  env_ix : p.lookup "env_ix" = some (envIxL)
  env_row_set : p.lookup "env_row_set" = some (envRowSetL)
  env_erase : p.lookup "env_erase" = some (envEraseL)

/-- The promotion with everything it calls. -/
def promoteProg : Prog :=
  [("pi_bvar", piBVar),
   ("pi_fvar", piFVar),
   ("pi_sort", piSort),
   ("pi_const", piConst),
   ("pi_app", piApp),
   ("pi_lam", piLam),
   ("pi_forall", piForall),
   ("pi_let", piLet),
   ("pi_lit", piLit),
   ("pi_lit_str", piLitStr),
   ("pi_proj", piProj),
   ("pi_nanon", piNAnon),
   ("pi_nstr", piNStr),
   ("pi_nnum", piNNum),
   ("pi_zero", piZero),
   ("pi_succ", piSucc),
   ("pi_max", piMax),
   ("pi_imax", piImax),
   ("pi_param", piParam),
   ("pi_ls", piLs),
   ("pn_arm", pnArm),
   ("promote_n", promoteNL),
   ("pl_arm", plArm),
   ("promote_l", promoteLL),
   ("promote_l_pool", promoteLPool),
   ("pls_arm", plsArm),
   ("promote_ls", promoteLsL),
   ("pe_lit", peLit),
   ("pe_const", peConst),
   ("pe_app", peApp),
   ("pe_lam", peLam),
   ("pe_forall", peForall),
   ("pe_let", peLet),
   ("pe_proj", peProj),
   ("pe_arm", peArm),
   ("promote_e", promoteEL),
   ("promote_n_list", promoteNListL),
   ("promote_l_list", promoteLListL),
   ("promote_e_list", promoteEListL),
   ("promote_slice", promoteSlice),
   ("promote_cv", promoteCVL),
   ("promote_fire", promoteFireL),
   ("promote_rule", promoteRuleL),
   ("promote_rules", promoteRulesL),
   ("promote_caps", promoteCapsL),
   ("promote_proj_table", promoteProjTableL),
   ("pci_cv", pciCv),
   ("pci_defn", pciDefn),
   ("pci_ind", pciInd),
   ("pci_ctor", pciCtor),
   ("pci_rec", pciRec),
   ("promote_ci", promoteCIL),
   ("promote_ci_list", promoteCIListL),
   ("promote_clear", promoteClear),
   ("promote_vg", promoteVGL),
   ("erase_installed", eraseInstalledL),
   ("index_promoted", indexPromotedL),
   ("promote_new", promoteNewL),
   ("pn_find", memoFindG pnSch),
   ("pn_put", memoPutG pnSch),
   ("pn_clear", memoClearG pnSch),
   ("pl_find", memoFindG plSch),
   ("pl_put", memoPutG plSch),
   ("pl_clear", memoClearG plSch),
   ("pls_find", memoFindG plsSch),
   ("pls_put", memoPutG plsSch),
   ("pls_clear", memoClearG plsSch),
   ("pe_find", memoFindG peSch),
   ("pe_put", memoPutG peSch),
   ("pe_clear", memoClearG peSch),
   ("der_b", derB),
   ("mk_app", mkApp),
   ("mk_lam", mkLam),
   ("mk_forall", mkForall),
   ("mk_let", mkLet),
   ("mk_proj", mkProj),
   ("bvar_find", bvarFind),
   ("bvar_push", bvarPush),
   ("intern_bvar", internBVar),
   ("app_find", appFind),
   ("app_push", appPush),
   ("intern_app", internApp),
   ("lam_find", lamFind),
   ("lam_push", lamPush),
   ("intern_lam", internLamL),
   ("forall_find", forallFind),
   ("forall_push", forallPush),
   ("intern_forall", internForallL),
   ("letE_find", letFind),
   ("letE_push", letPush),
   ("intern_letE", internLet),
   ("proj_find", projFind),
   ("proj_push", projPush),
   ("intern_proj", internProj),
   ("sort_find", sortFind),
   ("sort_push", sortPush),
   ("intern_sort", internSort),
   ("const_find", constFind),
   ("const_push", constPush),
   ("intern_const", internConst),
   ("fvar_find", fvarFind),
   ("fvar_push", fvarPush),
   ("intern_fvar", internFVar),
   ("lit_hash", litHash),
   ("limbs_eq", limbsEq),
   ("lit_match", litMatch),
   ("lit_find", litFind),
   ("lit_push", litPush),
   ("intern_lit", internLit),
   ("lit_match_str", litMatchStr),
   ("lit_find_str", litFindStr),
   ("lit_push_str", litPushStr),
   ("intern_lit_str", internLitStr),
   ("nanon_find", nanonFind),
   ("nanon_push", nanonPush),
   ("intern_nanon", internNAnon),
   ("nstr_match", nsMatch),
   ("nstr_find", nsFind),
   ("nstr_push", nsPush),
   ("intern_nstr", internNStr),
   ("nnum_find", nnumFind),
   ("nnum_push", nnumPush),
   ("intern_nnum", internNNum),
   ("zero_find", zeroFind),
   ("zero_push", zeroPush),
   ("intern_zero", internZero),
   ("succ_find", succFind),
   ("succ_push", succPush),
   ("intern_succ", internSucc),
   ("max_find", maxFind),
   ("max_push", maxPush),
   ("intern_max", internMax),
   ("imax_find", imaxFind),
   ("imax_push", imaxPush),
   ("intern_imax", internImax),
   ("param_find", paramFind),
   ("param_push", paramPush),
   ("intern_param", internParam),
   ("ls_match", lsMatch),
   ("ls_find", lsFind),
   ("ls_push", lsPush),
   ("intern_ls", internLs),
   ("lv_node", lvNode),
   ("ls_node", lsNode),
   ("e_view", L.Ind.eView),
   ("erec_alloc", L.Ind.erecAlloc),
   ("env_ix", envIxL),
   ("env_row_set", envRowSetL),
   ("env_erase", envEraseL)]

set_option maxHeartbeats 0 in
theorem promoteProg_ok : PromoteProg promoteProg := by
  constructor <;> rfl

theorem promoteProg_wf : L.Compiler.Prog.wf L.Ind.indTab promoteProg = true := by
  decide +kernel

end L.Arena
