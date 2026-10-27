import ConAgua.L.Syntax
import ConAgua.Arena.Reasons

/-!
# The `AbsKeep` callees of the inductive stage under `StageC` (lane `indstaget`)

The callees whose `AbsKeep` (`AbsOK` across the call, a program fact) the `StageC` chain still
takes: exactly those that write no walk memo, so the fact is a write-set frame
(`absKeep_of_closed`). The callees that do write the walk memos (`check_constant_val`,
`block_nest_ctx`, `class_read`, `nest_uniform`, …) hand back `AbsOK` in their `StageC` posts.
-/

namespace L.Ind

open L.Arena

/-- `check_block_inds`' `AbsKeep` callees. -/
def indsKeepCalleesC : List FnName :=
  ["block_shape_with_sort", "check_block_inds_cv_tas", "cons_block_inds"]

/-- `check_block_positivity`'s `AbsKeep` callees. -/
def posKeepCalleesC : List FnName := ["check_block_positivity_init", "check_block_positivity_nfs"]

/-- `gen_rec_check`'s `AbsKeep` callees. -/
def grcKeepCalleesC : List FnName :=
  ["target_rec_pins", "gen_rec_check_former_tys", "struct_elim_level", "class_fe_r",
    "gen_rec_check_pop_all"]

/-- `check_block_tail`'s `AbsKeep` callees. -/
def tailKeepCalleesC : List FnName := ["cons_block_ctors", "struct_proj_guards"] ++ grcKeepCalleesC

/-- `check_block_pass`' `AbsKeep` callees. -/
def passKeepCalleesC : List FnName :=
  ["class_seeds", "check_block_pass_rec", "class_read_classes", "check_block_classes_keys"] ++
    indsKeepCalleesC ++ posKeepCalleesC

end L.Ind
