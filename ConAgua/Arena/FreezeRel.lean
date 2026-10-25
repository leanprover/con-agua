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

/-- A word array of `n` zeros. -/
def zeros (n : Nat) : Array Word := Array.replicate n 0

/-- **A thread's fresh worker memory** (the threads' entry 2, first call, after `check_b` copied the
seed): `m` with every frozen array cut to its extent, every owned array but `CTL` zero (at its
size in `m`), and `CTL` its first 256 words followed by zeros. Arrays neither frozen nor owned keep
`m`'s contents (phase B's loop does not name them; the worker's actual memory has them empty,
which `L/Agree.lean` bridges). -/
def freshMem (m : Mem) : Mem :=
  let t := truncFrozen m
  { t with words := (List.range t.words.size).toArray.map fun a =>
      if a = CTL then (t.arr64 CTL).extract 0 256 ++ zeros ((t.arr64 CTL).size - 256)
      else if parOwned.contains a then zeros (t.arr64 a).size
      else t.arr64 a }

end L.Arena
