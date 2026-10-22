module

public import ConAgua.Arena.Lift
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
import ConAgua.Census.Attr
public import ConAgua.L.ModelGen

@[expose] public section

/-!
# The entry of `liftLooseBVars`, and the program

`Lift.lean` has the walk, its models and specs (generated); here the entry `lift_entry`
(`liftLooseBVarsFast`), its model and spec (generated), and the program `liftProg`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## `lift_entry(h, k, c)`: `liftLooseBVarsFast`, between two clears -/

/-- con-ron: ConRon/Arena/ExprOps.lean:789-795 ConRon.Arena.liftLooseBVarsFast -/
@[l_impl ConRon.Arena.liftLooseBVarsFast]
def liftEntry : FunDecl := lfn (h, k, c) locals (r, u) {
  u := call lf_clear();
  r := call lift_go(h, c, k);
  u := call lf_clear();
  return r
}

/-- **`lift_entry` is its model `liftEntryW`** (generated). -/
l_model liftEntry_spec (p : Prog) (hp : LiftProg p)
  (he : p.lookup "lift_entry" = some liftEntry)
  fns [he ↦ liftEntryW]
  specs [memoClearG_spec lfSch p _ hp.lfc n, (liftGo_spec p hp n).1]
  grind [arena_grind]

/-- The walk, the memo, the `mk_*` and the stores they call, as one program. -/
def liftProg : Prog :=
  [("der_b", derB), ("lf_find", memoFindG lfSch), ("lf_put", memoPutG lfSch),
    ("lf_clear", memoClearG lfSch), ("lift_go", liftGo), ("lift_app", liftApp),
    ("lift_lam", liftLam), ("lift_forall", liftForall), ("lift_let", liftLet),
    ("lift_proj", liftProj), ("lift_entry", liftEntry), ("mk_app", mkApp), ("mk_lam", mkLam),
    ("mk_forall", mkForall), ("mk_let", mkLet), ("mk_proj", mkProj)] ++
  bvarProg ++ appProg ++ lamProg ++ forallProg ++ letProg ++ projProg

theorem liftProg_ok : LiftProg liftProg :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end L.Arena
