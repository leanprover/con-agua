import ConAgua.Arena.IndPosSpec.BvbWMfr
import ConAgua.Arena.IndSumSpec.TblProg

/-!
# TabsProg

`HbMemo`, `PosMR.hbOK`, `TabsProg`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `check_struct_proj_table`, keeping the memos -/

/-! ## The `hb` memo in the memory at hand -/

/-- **The `has_loose_bvar_b` memo is well formed** (at some twin map). -/
def HbMemo (m : Mem) : Prop := ∃ mp, hbMR m mp

theorem PosMR.hbOK {m : Mem} (h : PosMR m) : HbMemo m := h.hb

/-! ## The program -/

/-- The lookups of `check_block_tables`. -/
structure TabsProg (p : Prog) : Prop where
  tbl : TblProg p
  hf : p.lookup "hb_find" = some (memoFindG hbSch)
  hput : p.lookup "hb_put" = some (memoPutG hbSch)
  hins : p.lookup "has_loose_b_var_b_ins" = some hasLooseBVarBInsL
  hgo : p.lookup "has_loose_b_var_b_go" = some hasLooseBVarBGoL
  hbp : BvbProg p
  hst : StripProg p
  hsg : p.lookup "struct_used_later_go" = some structUsedLaterGoL
  hul : p.lookup "struct_used_later_list" = some structUsedLaterListL
  hgd : p.lookup "sl_getd" = some slGetD
  hmf : p.lookup "max_find" = some maxFind
  hmp : p.lookup "max_push" = some maxPush
  him : p.lookup "intern_max" = some internMax
  hcol : p.lookup "struct_proj_guards_col" = some structProjGuardsColL
  hrow : p.lookup "struct_proj_guards_row" = some structProjGuardsRowL
  hpw : p.lookup "pin_word" = some pinWordL
  hcl : p.lookup "hb_clear" = some (memoClearG hbSch)
  hspg : p.lookup "struct_proj_guards" = some structProjGuardsL
  erCopy : p.lookup "er_copy" = some erCopy
  erToIw : p.lookup "er_to_iw" = some erToIw
  lps : p.lookup "block_shape_lps" = some blockShapeLps
  one : p.lookup "check_block_tables_one" = some checkBlockTablesOne
  tabs : p.lookup "check_block_tables" = some checkBlockTables

end L.Ind
