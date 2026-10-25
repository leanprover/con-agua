import ConAgua.Arena.WhnfCore
import ConAgua.Arena.CoreLevels
import ConAgua.Arena.NStrStore
import ConAgua.Arena.NNumStore

/-!
# Projection tables: `proj_table_name`, `find_proj`, `fire_ok` (lane `whnf3`)

The three stubs of `CoreCallees` that look a projection table up (`WhnfCore.lean`'s module note):

| L | twin |
|---|---|
| `proj_table_name(t)` | `projTableName T`: interns `num (str T "projTable") 0` |
| `find_proj(vis, t, i)` | `IFEnv.findProj? fe T i`: `(0, 0)` none, `(1, q)` the table record `q` |
| `fire_ok(q, i, us)` | `IProjEntry.fireOk (tbl.entry i) us` at the table record `q` |

`proj_table_name` first checks that `t` is a name handle of the store (tag, tier, index below its
tier's count; the scratch tier only while it is open), as the views do: the twin interns the
prefix without a check, but its store is well formed (`NStoreWF`), so every name it holds is
valid; the check gives L the twin's `NStore.ViewOK` for the new `str` node. Then it puts the nine bytes of `"projTable"` at the pool top and raises the top before
`intern_nstr` (whose refinement needs the slice below the top, `SliceOK`), as the `Nat` arms put
their constant limbs (`nat_pred_lit`, `nat_succ_lit`). The twin's string interning allocates
nothing when the name exists; L leaves nine pool words per call (docs/deviations.md, D21).

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

/-- `proj_table_name(t)`: the reserved name `num (str t "projTable") 0`. -/
-- con-ron: ConRon/Arena/Env.lean:195-199 ConRon.Arena.projTableName
-- con-ron: CHANGED since 12752ca7 — `ConRon.Arena.projTableName` is gone upstream; re-check the L code and its proofs, then delete this line
@[l_impl ConRon.Arena.projTableName]
def projTableNameL : FunDecl := lfn (t) locals (o, s, g, k, c, pt, pb) {
  if 4294967295 < t { abort };
  g := t >> 28;
  if 2 < g { abort };
  k := ⟦t⟧.tier;
  if k != 0 && CTL.u64[1] == 0 { abort };
  c := NANON⟨k⟩.count;
  if g == 1 { c := NSTR⟨k⟩.count };
  if g == 2 { c := NNUM⟨k⟩.count };
  if c <= ⟦t⟧.idx { abort };
  o := CTL.u64[0];
  pt := ⦃o⦄.tier;
  pb := ⦃o⦄.idx;
  if o + 9 < o { abort };
  if len(POOL⟨pt⟩) < pb + 9 { abort };
  POOL⟨pt⟩[pb] := 112;
  POOL⟨pt⟩[pb + 1] := 114;
  POOL⟨pt⟩[pb + 2] := 111;
  POOL⟨pt⟩[pb + 3] := 106;
  POOL⟨pt⟩[pb + 4] := 84;
  POOL⟨pt⟩[pb + 5] := 97;
  POOL⟨pt⟩[pb + 6] := 98;
  POOL⟨pt⟩[pb + 7] := 108;
  POOL⟨pt⟩[pb + 8] := 101;
  CTL.u64[0] := o + 9;
  s := call intern_nstr(t, o, 9);
  if s >= 4294967296 { abort };
  s := call intern_nnum(s, 0);
  return s
}

/-- `find_proj(vis, t, i)`: the projection table of structure `t` below the view `vis`, if it has
a field `i`. -/
-- con-ron: ConRon/Arena/Env.lean:303-308 ConRon.Arena.IFEnv.findProj?
-- con-ron: CHANGED since 12752ca7 — `ConRon.Arena.IFEnv.findProj?` changed; re-check the L code and its proofs, then delete this line
@[l_impl ConRon.Arena.IFEnv.findProj?]
def findProjL : FunDecl := lfn (vis, t, i) locals (nm, f, q) {
  nm := call proj_table_name(t);
  if nm >= 4294967296 { abort };
  (f, q) := call env_find(nm, vis);
  if f == 0 { return (0, 0) };
  if EREC.u64[q] != 6 { return (0, 0) };
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
