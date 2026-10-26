import ConAgua.Checker.RomProgA

/-!
# The checker's program under the pin-data substitution: expressions, items, pin sets

`ExprProg`, `ItemsProg` and `PinProg` for `Prog.subPB bs checkerProg`, every `bs`: one `rfl`
lookup per function (`lkN`, `lkR`).
-/

namespace L.Checker

open L L.Rom L.Arena L.Ind

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkerProg_exprProg (bs : List UInt8) : ExprProg bs (Prog.subPB bs checkerProg) where
  toLevelsProg := checkerProg_levelsProg bs
  rom_expr := lkR bs (f := "rom_expr") rfl (romExpr_subPB bs)
  rom_ex_leaf := lkN bs (f := "rom_ex_leaf") rfl rfl
  memo_get := lkN bs (f := "memo_get") rfl rfl
  rom_ex_ref := lkN bs (f := "rom_ex_ref") rfl rfl
  rom_ex_one := lkN bs (f := "rom_ex_one") rfl rfl
  rom_ex_two := lkN bs (f := "rom_ex_two") rfl rfl
  memo_push := lkN bs (f := "memo_push") rfl rfl
  rset_find := lkN bs (f := "rset_find") rfl rfl
  rset_put := lkN bs (f := "rset_put") rfl rfl
  lit_match := lkN bs (f := "lit_match") rfl rfl
  lit_find := lkN bs (f := "lit_find") rfl rfl
  lit_push := lkN bs (f := "lit_push") rfl rfl
  intern_lit := lkN bs (f := "intern_lit") rfl rfl
  rom_lit := lkN bs (f := "rom_lit") rfl rfl
  bvar_find := lkN bs (f := "bvar_find") rfl rfl
  bvar_push := lkN bs (f := "bvar_push") rfl rfl
  intern_bvar := lkN bs (f := "intern_bvar") rfl rfl
  sort_find := lkN bs (f := "sort_find") rfl rfl
  sort_push := lkN bs (f := "sort_push") rfl rfl
  intern_sort := lkN bs (f := "intern_sort") rfl rfl
  const_find := lkN bs (f := "const_find") rfl rfl
  const_push := lkN bs (f := "const_push") rfl rfl
  intern_const := lkN bs (f := "intern_const") rfl rfl
  fvar_find := lkN bs (f := "fvar_find") rfl rfl
  fvar_push := lkN bs (f := "fvar_push") rfl rfl
  intern_fvar := lkN bs (f := "intern_fvar") rfl rfl
  der_b := lkN bs (f := "der_b") rfl rfl
  app_find := lkN bs (f := "app_find") rfl rfl
  app_push := lkN bs (f := "app_push") rfl rfl
  intern_app := lkN bs (f := "intern_app") rfl rfl
  mk_app := lkN bs (f := "mk_app") rfl rfl
  lam_find := lkN bs (f := "lam_find") rfl rfl
  lam_push := lkN bs (f := "lam_push") rfl rfl
  intern_lam := lkN bs (f := "intern_lam") rfl rfl
  mk_lam := lkN bs (f := "mk_lam") rfl rfl
  forall_find := lkN bs (f := "forall_find") rfl rfl
  forall_push := lkN bs (f := "forall_push") rfl rfl
  intern_forall := lkN bs (f := "intern_forall") rfl rfl
  mk_forall := lkN bs (f := "mk_forall") rfl rfl
  letE_find := lkN bs (f := "letE_find") rfl rfl
  letE_push := lkN bs (f := "letE_push") rfl rfl
  intern_letE := lkN bs (f := "intern_letE") rfl rfl
  mk_let := lkN bs (f := "mk_let") rfl rfl
  proj_find := lkN bs (f := "proj_find") rfl rfl
  proj_push := lkN bs (f := "proj_push") rfl rfl
  intern_proj := lkN bs (f := "intern_proj") rfl rfl
  mk_proj := lkN bs (f := "mk_proj") rfl rfl

theorem checkerProg_itemsProg (bs : List UInt8) : ItemsProg bs (Prog.subPB bs checkerProg) where
  toExprProg := checkerProg_exprProg bs
  rom_items := lkR bs (f := "rom_items") rfl (romItems_subPB bs)
  rset_clear := lkN bs (f := "rset_clear") rfl rfl

/-- **The pin-data stage's program hypothesis** for the substituted checker program. -/
theorem checkerProg_pinProg (bs : List UInt8) : PinProg bs (Prog.subPB bs checkerProg) where
  toItemsProg := checkerProg_itemsProg bs
  pb_check := lkR bs (f := "pb_check") rfl rfl
  rom_exprs_to := lkN bs (f := "rom_exprs_to") rfl rfl
  rom_pins_to := lkN bs (f := "rom_pins_to") rfl rfl
  rom_lists_to := lkN bs (f := "rom_lists_to") rfl rfl
  rom_tpairs_to := lkN bs (f := "rom_tpairs_to") rfl rfl
  rom_tpins_to := lkN bs (f := "rom_tpins_to") rfl rfl
  rom_sets_to := lkN bs (f := "rom_sets_to") rfl rfl
  intern_pin_sets := lkN bs (f := "intern_pin_sets") rfl rfl
  rom_pin_sets := lkN bs (f := "rom_pin_sets") rfl rfl
  intern_all_pins := lkR bs (f := "intern_all_pins") rfl rfl
  erec_alloc := lkN bs (f := "erec_alloc") rfl rfl
  iw_alloc := lkN bs (f := "iw_alloc") rfl rfl
  er_copy := lkN bs (f := "er_copy") rfl rfl
  er_to_iw := lkN bs (f := "er_to_iw") rfl rfl

end L.Checker
