module

public import ConAgua.Arena.JustifySide
public import ConAgua.Arena.DeclNatBase
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import all ConAgua.Arena.JustifySide

@[expose] public section

/-!
# The comparison's driver steps: the generated models (lane compare)

The word models of `JustifySide.lean`'s functions (`l_model`); the refinements are in
`JustifySideRef*.lean`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Front (DECL DLP)
open L.Ind (ntBW)

/-- **`sd_move_a` is its model `sdMoveAW`** (generated). -/
l_model sdMoveA_specW (p : Prog) (hp : p.lookup "sd_move_a" = some sdMoveAL)
  fns [hp ↦ sdMoveAW]
  grind [arena_grind]

/-- **`sd_move_s` is its model `sdMoveSW`** (generated). -/
l_model sdMoveS_specW (p : Prog) (hp : p.lookup "sd_move_s" = some sdMoveSL)
  fns [hp ↦ sdMoveSW]
  grind [arena_grind]

/-- **`sd_move_n` is its model `sdMoveNW`** (generated). -/
l_model sdMoveN_specW (p : Prog) (hp : p.lookup "sd_move_n" = some sdMoveNL)
  fns [hp ↦ sdMoveNW]
  grind [arena_grind]

/-- **`index_to_solution` is its model `indexToSolutionW`** (generated). -/
l_model indexToSolution_specW (p : Prog) (hp : p.lookup "index_to_solution" = some indexToSolutionL)
  fns [hp ↦ indexToSolutionW]
  specs [callW_spec p n "sd_move_a", callW_spec p n "sd_move_s", callW_spec p n "sd_move_n"]
  grind [arena_grind] bind ntBW

/-- **`builtin_axiom_name` is its model `builtinAxiomNameW`** (generated). -/
l_model builtinAxiomName_specW (p : Prog) (hp : p.lookup "builtin_axiom_name" = some builtinAxiomNameL)
  fns [hp ↦ builtinAxiomNameW ro]
  grind [arena_grind]

/-- **`side_record` is its model `sideRecordW`** (generated). -/
l_model sideRecord_specW (p : Prog) (hp : p.lookup "side_record" = some sideRecordL)
  fns [hp ↦ sideRecordW]
  specs [callW_spec p n "builtin_axiom_name", callW_spec p n "pin_at", callW_spec p n "mentions_const"]
  grind [arena_grind] bind ntBW

/-- **`side_records` is its model `sideRecordsW`** (generated). -/
l_model sideRecords_specW (p : Prog) (hp : p.lookup "side_records" = some sideRecordsL)
  fns [hp ↦ sideRecordsW]
  specs [callW_spec p n "side_record"]
  grind [arena_grind] bind ntBW

/-- **`sd_copy_prev` is its model `sdCopyPrevW`** (generated). -/
l_model sdCopyPrev_specW (p : Prog) (hp : p.lookup "sd_copy_prev" = some sdCopyPrevL)
  fns [hp ↦ sdCopyPrevW]
  grind [arena_grind] bind ntBW

/-- **`sd_copy_names` is its model `sdCopyNamesW`** (generated). -/
l_model sdCopyNames_specW (p : Prog) (hp : p.lookup "sd_copy_names" = some sdCopyNamesL)
  fns [hp ↦ sdCopyNamesW]
  grind [arena_grind] bind ntBW

/-- **`mates_insert` is its model `matesInsertW`** (generated). -/
l_model matesInsert_specW (p : Prog) (hp : p.lookup "mates_insert" = some matesInsertL)
  fns [hp ↦ matesInsertW]
  specs [callW_spec p n "mates_get", callW_spec p n "erec_alloc", callW_spec p n "sd_copy_prev",
    callW_spec p n "sd_copy_names", callW_spec p n "mates_set"]
  grind [arena_grind] bind ntBW

/-- **`solution_of` is its model `solutionOfW`** (generated). -/
l_model solutionOf_specW (p : Prog) (hp : p.lookup "solution_of" = some solutionOfL)
  fns [hp ↦ solutionOfW]
  specs [callW_spec p n "mates_insert"]
  grind [arena_grind] bind ntBW

end L.Arena
