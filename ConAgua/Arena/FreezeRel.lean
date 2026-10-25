import ConAgua.Arena.PhaseBT
import ConAgua.Arena.Freeze

/-!
# What phase B starts from, and the frozen arrays cut to their extents (lane parmode)

docs/design/parmode.md, "Redesign" and "Step 4". The statements both modes of the parallel mode
share:

* `PhaseBStart … m a v`: what phase A leaves for phase B at the twin's phase-A state `a` and the
  final view `v` (lane parallel's structure, with the view an argument): the loop's relation, the
  memory's half (`LoopMem`, `CoreMemos`, `CrOK`) and con-ron's phase-B invariant `TwinPend` over all
  the pending groups.
* `fzExt m z`: the extent of frozen image `z` in memory `m` (the value `fz_i` computes).
* `truncFrozen m`: `m` with every frozen array cut to its extent. Entry 2 reads exactly these
  prefixes (in place in the sequential driver, from the buffer in the threads).

The truncation theorem (`PhaseBStart.trunc`, to prove): phase B's relations read no frozen array
beyond its extent, so `PhaseBStart … m a v → PhaseBStart … (truncFrozen m) a v`.
-/

namespace L.Arena

open ConRon.Arena

/-- **What phase A leaves for phase B** at the twin's phase-A state `a`, the environment `fe`, the
pending groups `pend` and the final view `v`. -/
structure PhaseBStart (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
    (ds : Array IDeclaration) (fe : IFEnv) (pend : Array PendingCheck) (m : Mem) (a : AState)
    (v : Word) : Prop where
  loop : LoopR pins dn m a v fe pend ds
  mem : LoopMem dn m a
  core : CoreMemos m
  twin : TwinPend fe pend.toList a
  cr : L.Stubs.CrOK m

/-- The extent of frozen image `z` in memory `m` (what `fz_i` computes, locals irrelevant). -/
def fzExt (m : Mem) (z : Fz) : Nat := (Expr.pval ⟨m, fun _ => 0⟩ z.e).toNat

/-- The arrays of frozen entries `zs` cut to their extents in `m₀` (the extents are read in the
original memory). -/
def truncList (m₀ : Mem) : Mem → List (ArrId × Fz) → Mem
  | m, [] => m
  | m, (_, z) :: zs =>
    truncList m₀ { m with words := m.words.set! z.src ((m₀.arr64 z.src).extract 0 (fzExt m₀ z)) } zs

/-- **`m` with every frozen array cut to its extent** (the header's and `CTL`'s seed entries cut
`OUT` and `CTL`; entry 2 reads `CTL` whole from its own copy, so the seed's cut is not applied to
`CTL` itself: it starts at the pool). -/
def truncFrozen (m : Mem) : Mem := truncList m m (frozen.drop 1)

end L.Arena
