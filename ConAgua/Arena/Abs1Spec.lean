module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
public import ConAgua.Arena.Abs1
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# The specs of `abstract1`'s arms, and the entry

The entry `abs_entry` (`abstract1Fast`) and the program `absProg`; the walk's models and specs
(`absGo_spec`) are generated in `Abs1.lean`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## `abs_entry(e, d, k)`: `abstract1Fast`, between two clears

The walk's depth counter starts at `coreWalkFuel` (`4000000000`, `ConRon/Arena/Core.lean`): the
core calls `abstract1Fast coreWalkFuel`. Its code `absEntry` and the final clear `aclrK` are in
`Abs1.lean` (`ArRangeSpec.lean` needs them, not these specs). -/

/-- **The model of `abs_entry`.** -/
def absEntryW (n : Nat) (m : Mem) (e d k : Word) : Option (Word × Mem) :=
  if rdW (m.arr64 CTL) 48 + 2 = 0 then none else aclrK (absW n (mclearG abSch m) e k d 4000000000)

theorem absEntryW_eq (n : Nat) (m : Mem) (e d k : Word) (h0 : rdW (m.arr64 CTL) 48 + 2 ≠ 0) :
    absEntryW n m e d k = aclrK (absW n (mclearG abSch m) e k d 4000000000) := by
  simp [absEntryW, h0]

grind_pattern [arena_grind] absEntryW_eq => absEntryW n m e d k

theorem absEntry_spec (p : Prog) (hp : AbsProg p) (he : p.lookup "abs_entry" = some absEntry)
    (n : Nat) (s₀ : St) (e d k : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "abs_entry" [e, d, k]
    ⦃fun r s' => LocEq s' s₀ ∧ absEntryW n s₀.mem e d k = some (r.headD 0, s'.mem); ⊤⦄ := by
  have ih := (absGo_spec p hp n).2.1
  rw [invoke_eq _ he]
  simp only [callFn, absEntry]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, memoClearG_spec abSch p _
        (hp.get "ab_clear") n,
      ih] <;>
    finish

/-- The walk, its memo, `fvarRangeProg` and `liftProg` (the `mk_*`, the stores), as one program. -/
def absProg : Prog := absWalkProg ++ [("abs_entry", absEntry)]

theorem absProg_ok : AbsProg absProg := (ProgHas.refl _).left

end L.Arena
