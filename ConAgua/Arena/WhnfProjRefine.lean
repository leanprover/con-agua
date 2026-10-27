import ConAgua.Arena.WhnfProj
import ConAgua.Arena.Env

/-!
# The projection lookups' programs (lane `whnf3`, helper `whnf3-proj`)

`ProjProg`: the lookups `find_proj` and `fire_ok` need (`WhnfProjRefine2.lean` proves `find_proj`,
`WhnfProjRefine3.lean` `fire_ok`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The programs -/

/-- **The lookups the projection functions need.** -/
structure ProjProg (p : Prog) : Prop where
  findProj : p.lookup "find_proj" = some findProjL
  fireOk : p.lookup "fire_ok" = some fireOkL
  envix : p.lookup "env_ix" = some envIxL
  envrow : p.lookup "env_row_get" = some envRowGetL
  tblix : p.lookup "tbl_ix" = some tblIxL
  tblrow : p.lookup "tbl_row_get" = some tblRowGetL
  findTable : p.lookup "find_table" = some findTableL

end L.Arena
