module

import ConAgua.Arena.StubNamesRefine
public import ConAgua.Arena.CallF
public import ConAgua.Arena.StripTeleSpec
public import ConAgua.Arena.StubNames
import all ConAgua.Arena.DeclArmsCanon
import all ConAgua.Arena.Env
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.Pins
import all ConAgua.Arena.StubInd
import all ConAgua.Arena.StubNames
import all ConAgua.Arena.WhnfEntry
import all ConAgua.Arena.WhnfIota
import all ConAgua.Arena.WhnfSpineRefine

@[expose] public section

/-!
# Stub contracts discharged by real refinements (lane `indproofs4`)

`IndStubs.lean`'s contracts stand for callees another lane owns. When that lane lands a
refinement (a `RefAM` in its program bundle), the stage's models swap `stubM f` for the callee's
program- and fuel-free model `callF P f` (`CallF.lean`, the precedent `StageInst1.lean`), where
`P` is the callee's call-closed function list:

* `xF_spec`: every call of `f` in a program with `ProgHas p P` returns `callF P f`;
* `xF_ok`: the relational fact, `RelW (callF P f) …` in the shape of the stub contract, from the
  owner's refinement in `P` itself (`relW_callF`: `RefAM P` is `RelW (callF P)`);
* the write set of `P` (`closedA`), for memo frames (`MFr`).

Callers then need `ProgHas p P` (added to their program bundles); `Checker/IndReal.lean` proves
these bundles for `checkerProg`, one `rfl` lookup per function.
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **A refinement in a closed program is a fact about its fuel-free model.** -/
theorem relW_callF {α : Type} [Inhabited α] {P : Prog} {f : FnName} {args : List Word}
    {pre : Mem → AState → Prop} {op : AM α} {post : Mem → Mem → AState → List Word → α → Prop}
    (h : RefAM P f args pre op post) : RelW (callF P f) args pre op post := by
  intro m m' a r hc hpre
  obtain ⟨n, hn⟩ := callF_run hc
  obtain ⟨s', hs', -, hok, hpost⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (h n _ a hpre) hn
  subst hs'
  exact ⟨_, _, AM.run_of_ok _ a hok, hpost⟩

/-! ## `reserved_rec_name` (lane `tails`' `reservedRecName_refines`) -/

/-- `reserved_rec_name` and its callees. -/
def rrnProg : Prog :=
  [("reserved_rec_name", L.Stubs.reservedRecNameL), ("reserved_contains", reservedContains),
   ("reserved_from", reservedFrom), ("lit_guard_has", L.Stubs.litGuardHas),
   ("pin_range_has", L.Stubs.pinRangeHas), ("pin_at", pinAtL),
   ("reserved_rec_bool", L.Stubs.reservedRecBoolL)]

def rrnFns : List FnName := rrnProg.map (·.1)

/-- `reserved_rec_name` writes nothing. -/
theorem rrnProg_closed : closedA rrnProg [] [] rrnFns = true := by decide +kernel

/-- The program bundle. -/
abbrev RrnF (p : Prog) : Prop := ProgHas p rrnProg

/-- **The model of `reserved_rec_name`.** -/
noncomputable def rrnF (m : Mem) (args : List Word) : Option (List Word × Mem) :=
  callF rrnProg "reserved_rec_name" m args

theorem rrnF_spec (p : Prog) (hp : RrnF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "reserved_rec_name" args
    ⦃fun r s' => LocEq s' s₀ ∧ rrnF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  callF_spec rrnProg_closed (hp.agree rrnFns) (by decide) n s₀ args

/-- **`reserved_rec_name`'s model refines `reservedRecName`** (replaces
`IndStubs.reservedRecName_spec`). -/
theorem rrnF_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Word) (hn : H n) :
    RelW rrnF [n] (StageR vis fe) (reservedRecName (decI n)) (KeepPost vis fe decW0B) :=
  relW_callF (L.Stubs.reservedRecName_refines (p := rrnProg) (by constructor <;> rfl) dn vis fe n hn)

end L.Ind
