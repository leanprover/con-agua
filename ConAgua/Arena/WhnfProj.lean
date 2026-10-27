import ConAgua.Arena.Tiers

/-!
# Projection tables: `find_proj`, `fire_ok` (lane `whnf3`)

The two stubs of `CoreCallees` that look a projection table up (`WhnfCore.lean`'s module note):

| L | twin |
|---|---|
| `find_proj(vis, t, i)` | `IFEnv.findProj? fe T i`: `(0, 0)` none, `(1, q)` the table record `q` |
| `fire_ok(q, i, us)` | `IProjEntry.fireOk (tbl.entry i) us` at the table record `q` |

The table is the environment's table component (`find_table`, `Env.lean`): a table is keyed on its
structure's name and visible exactly where the structure is.

`fire_ok` is `inferProj`'s propositional-structure test (`Infer.lean`'s `infer_proj`) with the
answer inverted: the twin reads `lvlEq? structSort zeroLevel` and, at `some true` only, the
field's guard level through `fieldSortZeroT` (`field_sort_zero`, a stub of lane `defeq`'s
`DefeqCallees`). A guard past the list is `default` (`IProjTable.entry`'s `getD`), the handle word
`0`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- `find_proj(vis, t, i)`: the projection table of structure `t` below the view `vis`
(`find_table`), if it has a field `i`: `(1, q)` the table record `q`, else `(0, 0)`. -/
-- con-ron: ConRon/Arena/Env.lean:303-308 ConRon.Arena.IFEnv.findProj?
@[l_impl ConRon.Arena.IFEnv.findProj?]
def findProjL : FunDecl := lfn (vis, t, i) locals (r, q) {
  if 4294967295 < t { abort };
  r := call find_table(vis, t);
  if r == 0 { return (0, 0) };
  q := r - 1;
  if i < EREC.u64[q + 7] { return (1, q) };
  return (0, 0)
}

/-- `fire_ok(q, i, us)`: the tower-fire guard of field `i` of the table record `q` at the
universe arguments `us`. -/
-- con-ron: ConRon/Arena/Core.lean:1646-1657 ConRon.Arena.IProjEntry.fireOk
@[l_impl ConRon.Arena.IProjEntry.fireOk]
def fireOkL : FunDecl := lfn (q, i, us) locals (z, ok, fs) {
  z := call pin_word(53);
  ok := call lvl_eq_c(EREC.u64[q + 8], z);
  if ok < 2 { return 1 };
  fs := 0;
  if i < EREC.u64[q + 12] { fs := EREC.u64[EREC.u64[q + 11] + i] };
  ok := call field_sort_zero(EREC.u64[q + 3], EREC.u64[q + 4], us, fs);
  return ok
}

end L.Arena
