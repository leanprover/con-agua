module

public import ConAgua.Arena.DeclBasisSpec
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
import all ConAgua.Arena.BasisL
import all ConAgua.Arena.DeclArms

@[expose] public section

/-!
# The quotient records' L functions: the word models (lane `ronsync2`, stage 3)

`BasisL.lean`'s `quot_pin(k)`, `quot_at(k, q)`, `quot_pin_hit(k, q)`, `quot_preds_ok(vis, k)` and
`cv_at_lps(d, q, po, pl)`, and `DeclArms.lean`'s `check_quot_record(vis, k, q)` and
`check_decl_quot(i, vis)`: their models (`l_model`), the callees through their runs.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **The model of `quot_pin(k)`**: the quotient block read, its slot `k`. -/
l_model quotPin_specW (p : Prog) (hp : p.lookup "quot_pin" = some quotPin)
  fns [hp ↦ quotPinW list]
  specs [callW_spec p n "rom_basis_decls"]
  grind [arena_grind]

/-- **The model of `quot_at(k, q)`**: the pin, then `ci_at_lps` at `q`'s names. -/
l_model quotAt_specW (p : Prog) (hp : p.lookup "quot_at" = some quotAt)
  fns [hp ↦ quotAtW list]
  specs [callW_spec p n "quot_pin", callW_spec p n "ci_at_lps"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE]

/-- **The model of `cv_at_lps(d, q, po, pl)`**. -/
l_model cvAtLps_specW (p : Prog) (hp : p.lookup "cv_at_lps" = some cvAtLps)
  fns [hp ↦ cvAtLpsW list]
  specs [callW_spec p n "er_to_iw", callW_spec p n "param_levels", callW_spec p n "inst_lp",
    callW_spec p n "erec_put"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE]

/-- **The model of `quot_pin_hit(k, q)`**. -/
l_model quotPinHit_specW (p : Prog) (hp : p.lookup "quot_pin_hit" = some quotPinHitL)
  fns [hp ↦ quotPinHitW list]
  specs [callW_spec p n "quot_pin", callW_spec p n "cv_lps", callW_spec p n "sl_nodup",
    callW_spec p n "erec_alloc", callW_spec p n "cv_at_lps", callW_spec p n "cv_eq"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE]

/-- **The model of `quot_preds_ok(vis, k)`**. -/
l_model quotPredsOk_specW (p : Prog) (hp : p.lookup "quot_preds_ok" = some quotPredsOk)
  fns [hp ↦ quotPredsOkW list]
  specs [callW_spec p n "pin_at", callW_spec p n "env_find"]
  grind [arena_grind]

/-- **The model of `check_quot_record(vis, k, q)`, both outcomes**: its callees (outside the
verdict closure) through their runs, `install_basis_decl` by its unified model. -/
l_model checkQuotRecord_specE (p : Prog) (hp : p.lookup "check_quot_record" = some checkQuotRecordL)
  (hB : BasisProg p)
  fns [hp ↦ checkQuotRecordE]
  specs [callW_spec p n "quot_pin_hit", callW_spec p n "quot_preds_ok", callW_spec p n "quot_at",
    installBasisDecl_specE p hB n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

end L.Ind
