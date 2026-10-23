import ConAgua.Checker.RomProg0

/-!
# The checker's program under the pin-data substitution: names, levels, reserved pins

`NameProg`, `LevelsProg` and `IrpProg` (at offset `0`) for `Prog.subPB bs checkerProg`, every `bs`:
one `rfl` lookup per function (`lkN`: no pin-data read; `lkR`: a reader, `romName_subPB`, …).
-/

namespace L.Checker

open L L.Rom L.Arena L.Ind

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkerProg_nameProg (bs : List UInt8) : NameProg bs (Prog.subPB bs checkerProg) where
  rom_name := lkR bs (f := "rom_name") rfl (romName_subPB bs)
  rom_u64 := lkR bs (f := "rom_u64") rfl (romU64PB_subPB bs)
  rom_put := lkR bs (f := "rom_put") rfl (romPutPB_subPB bs)
  nanon_find := lkN bs (f := "nanon_find") rfl rfl
  nanon_push := lkN bs (f := "nanon_push") rfl rfl
  intern_nanon := lkN bs (f := "intern_nanon") rfl rfl
  lit_hash := lkN bs (f := "lit_hash") rfl rfl
  limbs_eq := lkN bs (f := "limbs_eq") rfl rfl
  nstr_match := lkN bs (f := "nstr_match") rfl rfl
  nstr_find := lkN bs (f := "nstr_find") rfl rfl
  nstr_push := lkN bs (f := "nstr_push") rfl rfl
  intern_nstr := lkN bs (f := "intern_nstr") rfl rfl
  nnum_find := lkN bs (f := "nnum_find") rfl rfl
  nnum_push := lkN bs (f := "nnum_push") rfl rfl
  intern_nnum := lkN bs (f := "intern_nnum") rfl rfl
  no_st8 := checkerProg_subPB_noSt8 bs

theorem checkerProg_levelProg (bs : List UInt8) : LevelProg bs (Prog.subPB bs checkerProg) where
  toNameProg := checkerProg_nameProg bs
  rom_level := lkR bs (f := "rom_level") rfl (romLevel_subPB bs)
  zero_find := lkN bs (f := "zero_find") rfl rfl
  zero_push := lkN bs (f := "zero_push") rfl rfl
  intern_zero := lkN bs (f := "intern_zero") rfl rfl
  succ_find := lkN bs (f := "succ_find") rfl rfl
  succ_push := lkN bs (f := "succ_push") rfl rfl
  intern_succ := lkN bs (f := "intern_succ") rfl rfl
  max_find := lkN bs (f := "max_find") rfl rfl
  max_push := lkN bs (f := "max_push") rfl rfl
  intern_max := lkN bs (f := "intern_max") rfl rfl
  imax_find := lkN bs (f := "imax_find") rfl rfl
  imax_push := lkN bs (f := "imax_push") rfl rfl
  intern_imax := lkN bs (f := "intern_imax") rfl rfl
  param_find := lkN bs (f := "param_find") rfl rfl
  param_push := lkN bs (f := "param_push") rfl rfl
  intern_param := lkN bs (f := "intern_param") rfl rfl

theorem checkerProg_levelsProg (bs : List UInt8) : LevelsProg bs (Prog.subPB bs checkerProg) where
  toLevelProg := checkerProg_levelProg bs
  stk_push := lkN bs (f := "stk_push") rfl rfl
  rom_lvls_go := lkN bs (f := "rom_lvls_go") rfl rfl
  stk_pool := lkN bs (f := "stk_pool") rfl rfl
  ls_match := lkN bs (f := "ls_match") rfl rfl
  ls_find := lkN bs (f := "ls_find") rfl rfl
  ls_push := lkN bs (f := "ls_push") rfl rfl
  intern_ls := lkN bs (f := "intern_ls") rfl rfl
  rom_levels := lkN bs (f := "rom_levels") rfl rfl

/-- **The reserved pins' program hypothesis** for the substituted checker program. -/
theorem checkerProg_irp (bs : List UInt8) : IrpProg bs 0 (Prog.subPB bs checkerProg) where
  toNameProg := checkerProg_nameProg bs
  rom_names_to := lkN bs (f := "rom_names_to") rfl rfl
  ls_match := lkN bs (f := "ls_match") rfl rfl
  ls_find := lkN bs (f := "ls_find") rfl rfl
  ls_push := lkN bs (f := "ls_push") rfl rfl
  intern_ls := lkN bs (f := "intern_ls") rfl rfl
  zero_find := lkN bs (f := "zero_find") rfl rfl
  zero_push := lkN bs (f := "zero_push") rfl rfl
  intern_zero := lkN bs (f := "intern_zero") rfl rfl
  succ_find := lkN bs (f := "succ_find") rfl rfl
  succ_push := lkN bs (f := "succ_push") rfl rfl
  intern_succ := lkN bs (f := "intern_succ") rfl rfl
  sort_find := lkN bs (f := "sort_find") rfl rfl
  sort_push := lkN bs (f := "sort_push") rfl rfl
  intern_sort := lkN bs (f := "intern_sort") rfl rfl
  irp := lkN bs (f := "intern_reserved_pins") rfl rfl

end L.Checker
