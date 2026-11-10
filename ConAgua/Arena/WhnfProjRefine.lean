module

public import ConAgua.Arena.WhnfProj
public import ConAgua.Arena.Env

@[expose] public section

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
  findTable : p.lookup "find_table" = some findTableL
  rawTable : p.lookup "raw_table" = some rawTableL
  tblOwnGet : p.lookup "tbl_own_get" = some tblOwnGetL
  tblBaseGet : p.lookup "tbl_base_get" = some tblBaseGetL
  envFind : p.lookup "env_find" = some envFindL
  envRowGet : p.lookup "env_row_get" = some envRowGetL
  baseRowGet : p.lookup "base_row_get" = some baseRowGetL

end L.Arena
