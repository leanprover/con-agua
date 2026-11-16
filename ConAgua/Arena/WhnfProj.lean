module

public import ConAgua.Arena.Tiers
import ConAgua.Census.Attr

@[expose] public section

/-!
# Projection tables: `find_proj` (lane `whnf3`)

The stub of `CoreCallees` that looks a projection table up (`WhnfCore.lean`'s module note):
`find_proj(vis, t, i)` is `IFEnv.findProj? fe T i`: `(0, 0)` none, `(1, q)` the table record `q`.

The table is the environment's table component (`find_table`, `Env.lean`): a table is keyed on its
structure's name and visible exactly where the structure is. (The tower-fire guard `fire_ok` went
with con-leche's task #480: a projection fires unguarded, and `infer_proj` computes its guard at
the use, `check_proj_guard`.)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- `find_proj(vis, t, i)`: the projection table of structure `t` below the view `vis`
(`find_table`), if it has a field `i`: `(1, q)` the table record `q`, else `(0, 0)`. -/
-- con-ron: ConRon/Arena/Env.lean:401-406 ConRon.Arena.IFEnv.findProj?
@[no_expose, l_impl ConRon.Arena.IFEnv.findProj?]
def findProjL : FunDecl := lfn (vis, t, i) locals (r, q) {
  if 4294967295 < t { abort };
  r := call find_table(vis, t);
  if r == 0 { return (0, 0) };
  q := r - 1;
  if i < EREC⦃q + ⟪ProjTbl.numFields⟫⦄ { return (1, q) };
  return (0, 0)
}

end L.Arena
