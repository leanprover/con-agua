import ConAgua.Checker.RomProg0
import ConAgua.Checker.LoopProgTac

/-!
# The checker's program under the pin-data substitution: names, levels, reserved pins

`NameProg`, `LevelsProg` and `IrpProg` (at offset `0`) for `Prog.subPB bs checkerProg`, every `bs`:
one lookup per function by `chk_lk` (`lkN`: no pin-data read; `lkR`: a reader, `romName_subPB`, …).
-/

namespace L.Checker

open L L.Rom L.Arena L.Ind

set_option maxRecDepth 100000

theorem checkerProg_nameProg (bs : List UInt8) : NameProg bs (Prog.subPB bs checkerProg) where
  rom_name := lkR bs (f := "rom_name") (by chk_lk) (romName_subPB bs)
  rom_u64 := lkR bs (f := "rom_u64") (by chk_lk) (romU64PB_subPB bs)
  rom_put := lkR bs (f := "rom_put") (by chk_lk) (romPutPB_subPB bs)
  nanon_find := lkN bs (f := "nanon_find") (by chk_lk) rfl
  nanon_push := lkN bs (f := "nanon_push") (by chk_lk) rfl
  intern_nanon := lkN bs (f := "intern_nanon") (by chk_lk) rfl
  lit_hash := lkN bs (f := "lit_hash") (by chk_lk) rfl
  limbs_eq := lkN bs (f := "limbs_eq") (by chk_lk) rfl
  nstr_match := lkN bs (f := "nstr_match") (by chk_lk) rfl
  nstr_find := lkN bs (f := "nstr_find") (by chk_lk) rfl
  nstr_push := lkN bs (f := "nstr_push") (by chk_lk) rfl
  intern_nstr := lkN bs (f := "intern_nstr") (by chk_lk) rfl
  nnum_find := lkN bs (f := "nnum_find") (by chk_lk) rfl
  nnum_push := lkN bs (f := "nnum_push") (by chk_lk) rfl
  intern_nnum := lkN bs (f := "intern_nnum") (by chk_lk) rfl
  no_st8 := checkerProg_subPB_noSt8 bs

theorem checkerProg_levelProg (bs : List UInt8) : LevelProg bs (Prog.subPB bs checkerProg) where
  toNameProg := checkerProg_nameProg bs
  rom_level := lkR bs (f := "rom_level") (by chk_lk) (romLevel_subPB bs)
  zero_find := lkN bs (f := "zero_find") (by chk_lk) rfl
  zero_push := lkN bs (f := "zero_push") (by chk_lk) rfl
  intern_zero := lkN bs (f := "intern_zero") (by chk_lk) rfl
  succ_find := lkN bs (f := "succ_find") (by chk_lk) rfl
  succ_push := lkN bs (f := "succ_push") (by chk_lk) rfl
  intern_succ := lkN bs (f := "intern_succ") (by chk_lk) rfl
  max_find := lkN bs (f := "max_find") (by chk_lk) rfl
  max_push := lkN bs (f := "max_push") (by chk_lk) rfl
  intern_max := lkN bs (f := "intern_max") (by chk_lk) rfl
  imax_find := lkN bs (f := "imax_find") (by chk_lk) rfl
  imax_push := lkN bs (f := "imax_push") (by chk_lk) rfl
  intern_imax := lkN bs (f := "intern_imax") (by chk_lk) rfl
  param_find := lkN bs (f := "param_find") (by chk_lk) rfl
  param_push := lkN bs (f := "param_push") (by chk_lk) rfl
  intern_param := lkN bs (f := "intern_param") (by chk_lk) rfl

theorem checkerProg_levelsProg (bs : List UInt8) : LevelsProg bs (Prog.subPB bs checkerProg) where
  toLevelProg := checkerProg_levelProg bs
  stk_push := lkN bs (f := "stk_push") (by chk_lk) rfl
  rom_lvls_go := lkN bs (f := "rom_lvls_go") (by chk_lk) rfl
  stk_pool := lkN bs (f := "stk_pool") (by chk_lk) rfl
  ls_match := lkN bs (f := "ls_match") (by chk_lk) rfl
  ls_find := lkN bs (f := "ls_find") (by chk_lk) rfl
  ls_push := lkN bs (f := "ls_push") (by chk_lk) rfl
  intern_ls := lkN bs (f := "intern_ls") (by chk_lk) rfl
  rom_levels := lkN bs (f := "rom_levels") (by chk_lk) rfl

/-- **The reserved pins' program hypothesis** for the substituted checker program. -/
theorem checkerProg_irp (bs : List UInt8) : IrpProg bs 0 (Prog.subPB bs checkerProg) where
  toNameProg := checkerProg_nameProg bs
  rom_names_to := lkN bs (f := "rom_names_to") (by chk_lk) rfl
  ls_match := lkN bs (f := "ls_match") (by chk_lk) rfl
  ls_find := lkN bs (f := "ls_find") (by chk_lk) rfl
  ls_push := lkN bs (f := "ls_push") (by chk_lk) rfl
  intern_ls := lkN bs (f := "intern_ls") (by chk_lk) rfl
  zero_find := lkN bs (f := "zero_find") (by chk_lk) rfl
  zero_push := lkN bs (f := "zero_push") (by chk_lk) rfl
  intern_zero := lkN bs (f := "intern_zero") (by chk_lk) rfl
  succ_find := lkN bs (f := "succ_find") (by chk_lk) rfl
  succ_push := lkN bs (f := "succ_push") (by chk_lk) rfl
  intern_succ := lkN bs (f := "intern_succ") (by chk_lk) rfl
  sort_find := lkN bs (f := "sort_find") (by chk_lk) rfl
  sort_push := lkN bs (f := "sort_push") (by chk_lk) rfl
  intern_sort := lkN bs (f := "intern_sort") (by chk_lk) rfl
  irp := lkN bs (f := "intern_reserved_pins") (by chk_lk) rfl

end L.Checker
