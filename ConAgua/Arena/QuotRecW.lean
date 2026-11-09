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

/-- **The model of `er_copy_er(d, s, l)`**: the record words copied one by one. -/
l_model erCopyEr_specW (p : Prog) (hp : p.lookup "er_copy_er" = some erCopyEr)
  fns [hp ↦ erCopyErW list]
  specs [callW_spec p n "erec_put"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE]

/-- **The model of `spn_to_er(d, s, l)`**: the stack words copied to the record pool. -/
l_model spnToEr_specW (p : Prog) (hp : p.lookup "spn_to_er" = some spnToEr)
  fns [hp ↦ spnToErW list]
  specs [callW_spec p n "erec_put"]
  grind [arena_grind]

/-- **The model of `fire_levels_at(fo, fl, ko, kc, us)`**. -/
l_model fireLevelsAt_specW (p : Prog) (hp : p.lookup "fire_levels_at" = some fireLevelsAt)
  fns [hp ↦ fireLevelsAtW list]
  specs [callW_spec p n "ls_node", callW_spec p n "keys_push", callW_spec p n "sle_go",
    callW_spec p n "erec_alloc", callW_spec p n "spn_to_er"]
  grind [arena_grind]

/-- **The model of `rules_at_lps_go(ko, kc, us, o, l, d)`**. -/
l_model rulesAtLpsGo_specW (p : Prog) (hp : p.lookup "rules_at_lps_go" = some rulesAtLpsGo)
  fns [hp ↦ rulesAtLpsGoW list]
  specs [callW_spec p n "inst_lp", callW_spec p n "fire_levels_at", callW_spec p n "erec_put"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE]

/-- **The model of `ci_at_lps(p, po, pl)`**. -/
l_model ciAtLps_specW (p : Prog) (hp : p.lookup "ci_at_lps" = some ciAtLps)
  fns [hp ↦ ciAtLpsW list]
  specs [callW_spec p n "erec_alloc", callW_spec p n "erec_put", callW_spec p n "cv_at_lps",
    callW_spec p n "er_to_iw", callW_spec p n "param_levels", callW_spec p n "inst_lp",
    callW_spec p n "er_copy_er", callW_spec p n "rules_at_lps_go"]
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

/-! ## The pinned basis blocks' entry points (`basis_name_hit`, `basis_at_block`) -/

/-- **The model of `block_names_eq(ao, al, bo, bl)`**: the two `IW` slices' records' names. -/
l_model blockNamesEq_specW (p : Prog) (hp : p.lookup "block_names_eq" = some blockNamesEq)
  fns [hp ↦ blockNamesEqW list]
  specs []
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE]

/-- **The model of `basis_name_hit_go(io, il, k)`**. -/
l_model basisNameHitGo_specW (p : Prog) (hp : p.lookup "basis_name_hit_go" = some basisNameHitGo)
  fns [hp ↦ basisNameHitGoW list]
  specs [callW_spec p n "rom_basis_decls", callW_spec p n "block_names_eq"]
  grind [arena_grind]

/-- **The model of `basis_name_hit(bo, bl)`**. -/
l_model basisNameHit_specW (p : Prog) (hp : p.lookup "basis_name_hit" = some basisNameHit)
  fns [hp ↦ basisNameHitW list]
  specs [callW_spec p n "er_to_iw", callW_spec p n "basis_name_hit_go"]
  grind [arena_grind]

/-- **The model of `at_block_go(po, pl, co, cl)`**. -/
l_model atBlockGo_specW (p : Prog) (hp : p.lookup "at_block_go" = some atBlockGo)
  fns [hp ↦ atBlockGoW list]
  specs [callW_spec p n "ci_at_lps", callW_spec p n "sl_cons"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE]

/-- **The model of `basis_at_block(kind, bo, bl)`**. -/
l_model basisAtBlock_specW (p : Prog) (hp : p.lookup "basis_at_block" = some basisAtBlock)
  fns [hp ↦ basisAtBlockW list]
  specs [callW_spec p n "rom_basis_decls", callW_spec p n "er_to_iw", callW_spec p n "at_block_go"]
  grind [arena_grind]


/-! ## The block's comparison with its pin (`pin_list_ok`) -/

/-- **The model of `pin_agrees`**. -/
l_model pinAgrees_specW (p : Prog) (hp : p.lookup "pin_agrees" = some pinAgrees)
  fns [hp ↦ pinAgreesW list]
  specs [callW_spec p n "cv_eq", callW_spec p n "ci_eq"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE]

/-- **The model of `pin_copy_ok`**. -/
l_model pinCopyOk_specW (p : Prog) (hp : p.lookup "pin_copy_ok" = some pinCopyOk)
  fns [hp ↦ pinCopyOkW list]
  specs [callW_spec p n "cv_lps", callW_spec p n "sl_nodup", callW_spec p n "ci_at_lps", callW_spec p n "pin_agrees"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE]

/-- **The model of `pin_copies_ok`**. -/
l_model pinCopiesOk_specW (p : Prog) (hp : p.lookup "pin_copies_ok" = some pinCopiesOk)
  fns [hp ↦ pinCopiesOkW list]
  specs [callW_spec p n "pin_copy_ok"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE]

/-- **The model of `pin_link_go`**. -/
l_model pinLinkGo_specW (p : Prog) (hp : p.lookup "pin_link_go" = some pinLinkGo)
  fns [hp ↦ pinLinkGoW list]
  specs [callW_spec p n "canon_name_map"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE]

/-- **The model of `pin_link_ok`**. -/
l_model pinLinkOkL_specW (p : Prog) (hp : p.lookup "pin_link_ok" = some L.Ind.pinLinkOk)
  fns [hp ↦ pinLinkOkLW list]
  specs [callW_spec p n "pin_link_go"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE]

/-- **The model of `const_named`**. -/
l_model constNamed_specW (p : Prog) (hp : p.lookup "const_named" = some constNamed)
  fns [hp ↦ constNamedW list]
  specs []
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE]

/-- **The model of `rules_link_ok`**. -/
l_model rulesLinkOk_specW (p : Prog) (hp : p.lookup "rules_link_ok" = some rulesLinkOk)
  fns [hp ↦ rulesLinkOkW list]
  specs [callW_spec p n "const_named", callW_spec p n "cv_lps", callW_spec p n "pin_link_ok"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE]

/-- **The model of `block_link_ok_at`**. -/
l_model blockLinkOkAt_specW (p : Prog) (hp : p.lookup "block_link_ok_at" = some blockLinkOkAt)
  fns [hp ↦ blockLinkOkAtW list]
  specs [callW_spec p n "er_sl_eq", callW_spec p n "cv_lps", callW_spec p n "rules_link_ok"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE]

/-- **The model of `block_links_ok_go`**. -/
l_model blockLinksOkGo_specW (p : Prog) (hp : p.lookup "block_links_ok_go" = some blockLinksOkGo)
  fns [hp ↦ blockLinksOkGoW list]
  specs [callW_spec p n "block_link_ok_at"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE]

/-- **The model of `block_links_ok`**. -/
l_model blockLinksOk_specW (p : Prog) (hp : p.lookup "block_links_ok" = some blockLinksOk)
  fns [hp ↦ blockLinksOkW list]
  specs [callW_spec p n "block_links_ok_go"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE]

/-- **The model of `pin_list_ok`**. -/
l_model pinListOkL_specW (p : Prog) (hp : p.lookup "pin_list_ok" = some L.Ind.pinListOk)
  fns [hp ↦ pinListOkLW list]
  specs [callW_spec p n "pin_copies_ok", callW_spec p n "block_links_ok"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE]

end L.Ind
