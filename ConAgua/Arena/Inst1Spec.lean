module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
public import ConAgua.Arena.Inst1
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
public import ConAgua.L.ModelGen
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# The entry of `instantiate1`, and the program

As `LiftSpec.lean`: the entry `inst_entry` (`instantiate1Fast`), its model and spec (generated),
and the program `instProg`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## `inst_entry(e, v, d)`: `instantiate1Fast`, between two clears

The walk's depth counter starts at `coreWalkFuel` (`4000000000`). -/

/-- con-ron: ConRon/Arena/ExprOps.lean:377-384 ConRon.Arena.instantiate1Fast -/
@[l_impl ConRon.Arena.instantiate1Fast]
def instEntry : FunDecl := lfn (e, v, d) locals (r, u) {
  u := call if_clear();
  r := call inst_go(e, d, v, 4000000000);
  u := call if_clear();
  return r & 4294967295
}

/-- **`inst_entry` is its model `instEntryW`** (generated): the walk between two clears, the
handle word returned masked to 32 bits (the callers' contract `HW`; `decE` reads the same
handle). -/
l_model instEntry_spec (p : Prog) (hp : InstProg p)
  (he : p.lookup "inst_entry" = some instEntry)
  fns [he ↦ instEntryW]
  specs [memoClearG_spec imSch p _ hp.ifc n, (instGo_spec p hp n).1]
  grind [arena_grind]

/-- The walk, the memo and `liftProg` (the `mk_*`, the stores), as one program. -/
def instProg : Prog :=
  [("if_find", memoFindG imSch), ("if_put", memoPutG imSch), ("if_clear", memoClearG imSch),
    ("inst_go", instGo), ("inst_app", instApp), ("inst_lam", instLam),
    ("inst_forall", instForall), ("inst_let", instLet), ("inst_proj", instProj),
    ("inst_entry", instEntry)] ++ liftProg

end L.Arena
