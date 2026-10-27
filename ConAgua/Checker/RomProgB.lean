import ConAgua.Checker.RomProgA

/-!
# The checker's program under the pin-data substitution: expressions, items, pin sets

`ExprProg`, `ItemsProg` and `PinProg` for `Prog.subPB bs checkerProg`, every `bs`: one
lookup per function by `chk_lk` (`lkN`, `lkR`).
-/

namespace L.Checker

open L L.Rom L.Arena L.Ind

set_option maxRecDepth 100000

theorem checkerProg_exprProg (bs : List UInt8) : ExprProg bs (Prog.subPB bs checkerProg) where
  toLevelsProg := checkerProg_levelsProg bs
  rom_expr := lkR bs (f := "rom_expr") (by chk_lk) (romExpr_subPB bs)
  rom_ex_leaf := lkN bs (f := "rom_ex_leaf") (by chk_lk) rfl
  memo_get := lkN bs (f := "memo_get") (by chk_lk) rfl
  rom_ex_ref := lkN bs (f := "rom_ex_ref") (by chk_lk) rfl
  rom_ex_one := lkN bs (f := "rom_ex_one") (by chk_lk) rfl
  rom_ex_two := lkN bs (f := "rom_ex_two") (by chk_lk) rfl
  memo_push := lkN bs (f := "memo_push") (by chk_lk) rfl
  rset_find := lkN bs (f := "rset_find") (by chk_lk) rfl
  rset_put := lkN bs (f := "rset_put") (by chk_lk) rfl
  lit_match := lkN bs (f := "lit_match") (by chk_lk) rfl
  lit_find := lkN bs (f := "lit_find") (by chk_lk) rfl
  lit_push := lkN bs (f := "lit_push") (by chk_lk) rfl
  intern_lit := lkN bs (f := "intern_lit") (by chk_lk) rfl
  rom_lit := lkN bs (f := "rom_lit") (by chk_lk) rfl
  bvar_find := lkN bs (f := "bvar_find") (by chk_lk) rfl
  bvar_push := lkN bs (f := "bvar_push") (by chk_lk) rfl
  intern_bvar := lkN bs (f := "intern_bvar") (by chk_lk) rfl
  sort_find := lkN bs (f := "sort_find") (by chk_lk) rfl
  sort_push := lkN bs (f := "sort_push") (by chk_lk) rfl
  intern_sort := lkN bs (f := "intern_sort") (by chk_lk) rfl
  const_find := lkN bs (f := "const_find") (by chk_lk) rfl
  const_push := lkN bs (f := "const_push") (by chk_lk) rfl
  intern_const := lkN bs (f := "intern_const") (by chk_lk) rfl
  fvar_find := lkN bs (f := "fvar_find") (by chk_lk) rfl
  fvar_push := lkN bs (f := "fvar_push") (by chk_lk) rfl
  intern_fvar := lkN bs (f := "intern_fvar") (by chk_lk) rfl
  der_b := lkN bs (f := "der_b") (by chk_lk) rfl
  app_find := lkN bs (f := "app_find") (by chk_lk) rfl
  app_push := lkN bs (f := "app_push") (by chk_lk) rfl
  intern_app := lkN bs (f := "intern_app") (by chk_lk) rfl
  mk_app := lkN bs (f := "mk_app") (by chk_lk) rfl
  lam_find := lkN bs (f := "lam_find") (by chk_lk) rfl
  lam_push := lkN bs (f := "lam_push") (by chk_lk) rfl
  intern_lam := lkN bs (f := "intern_lam") (by chk_lk) rfl
  mk_lam := lkN bs (f := "mk_lam") (by chk_lk) rfl
  forall_find := lkN bs (f := "forall_find") (by chk_lk) rfl
  forall_push := lkN bs (f := "forall_push") (by chk_lk) rfl
  intern_forall := lkN bs (f := "intern_forall") (by chk_lk) rfl
  mk_forall := lkN bs (f := "mk_forall") (by chk_lk) rfl
  letE_find := lkN bs (f := "letE_find") (by chk_lk) rfl
  letE_push := lkN bs (f := "letE_push") (by chk_lk) rfl
  intern_letE := lkN bs (f := "intern_letE") (by chk_lk) rfl
  mk_let := lkN bs (f := "mk_let") (by chk_lk) rfl
  proj_find := lkN bs (f := "proj_find") (by chk_lk) rfl
  proj_push := lkN bs (f := "proj_push") (by chk_lk) rfl
  intern_proj := lkN bs (f := "intern_proj") (by chk_lk) rfl
  mk_proj := lkN bs (f := "mk_proj") (by chk_lk) rfl

theorem checkerProg_itemsProg (bs : List UInt8) : ItemsProg bs (Prog.subPB bs checkerProg) where
  toExprProg := checkerProg_exprProg bs
  rom_items := lkR bs (f := "rom_items") (by chk_lk) (romItems_subPB bs)
  rset_clear := lkN bs (f := "rset_clear") (by chk_lk) rfl

/-- **The pin-data stage's program hypothesis** for the substituted checker program. -/
theorem checkerProg_pinProg (bs : List UInt8) : PinProg bs (Prog.subPB bs checkerProg) where
  toItemsProg := checkerProg_itemsProg bs
  pb_check := lkR bs (f := "pb_check") (by chk_lk) rfl
  rom_exprs_to := lkN bs (f := "rom_exprs_to") (by chk_lk) rfl
  rom_pins_to := lkN bs (f := "rom_pins_to") (by chk_lk) rfl
  rom_lists_to := lkN bs (f := "rom_lists_to") (by chk_lk) rfl
  rom_tpairs_to := lkN bs (f := "rom_tpairs_to") (by chk_lk) rfl
  rom_tpins_to := lkN bs (f := "rom_tpins_to") (by chk_lk) rfl
  rom_sets_to := lkN bs (f := "rom_sets_to") (by chk_lk) rfl
  intern_pin_sets := lkN bs (f := "intern_pin_sets") (by chk_lk) rfl
  rom_pin_sets := lkN bs (f := "rom_pin_sets") (by chk_lk) rfl
  intern_all_pins := lkR bs (f := "intern_all_pins") (by chk_lk) rfl
  erec_alloc := lkN bs (f := "erec_alloc") (by chk_lk) rfl
  iw_alloc := lkN bs (f := "iw_alloc") (by chk_lk) rfl
  er_copy := lkN bs (f := "er_copy") (by chk_lk) rfl
  er_to_iw := lkN bs (f := "er_to_iw") (by chk_lk) rfl

end L.Checker
