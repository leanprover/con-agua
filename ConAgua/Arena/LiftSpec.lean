module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
public import ConAgua.Arena.Lift
import all ConAgua.Arena.LiftL
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
public import ConAgua.L.ModelGen
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# The entry of `liftLooseBVars`, and the program

`Lift.lean` has the walk's models and specs (generated); here the model and spec (generated) of
the entry `lift_entry` (`liftLooseBVarsFast`). The L code and the program `liftProg` are in
`LiftL.lean`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## `lift_entry(h, k, c, f)`: `liftLooseBVarsFast f k c h`, between two clears

The walk's counter is the twin's fuel `f` (the entry's callers pass theirs: `coreWalkFuel`, or
`instantiate1LiftGo`'s remaining fuel at a `bvar` leaf). -/

/-- **`lift_entry` is its model `liftEntryW`** (generated). -/
l_model liftEntry_spec (p : Prog) (hp : LiftProg p)
  (he : p.lookup "lift_entry" = some liftEntry)
  fns [he ↦ liftEntryW]
  specs [memoClearG_spec lfSch p _ (hp.get "lf_clear") n, (liftGo_spec p hp n).1]
  grind [arena_grind]

end L.Arena
