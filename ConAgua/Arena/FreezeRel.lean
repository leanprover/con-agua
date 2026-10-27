import ConAgua.Arena.PhaseBT

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

/-- **The arrays a fresh worker memory zeroes** (beside `CTL`): the owned arrays (`parOwnedL`, the
literal the entry stub is built from), and the lift memo
`LMEMO` (41). Phase B never names `LMEMO` (its walk is gone; `lf_clear` only bumps its stamp in
`CTL`), so it is neither frozen nor owned, but `ArenaR` ties it to the twin's `liftC`, which a
worker (`AState.worker`) has empty; the worker's actual memory has no `LMEMO` at all
(`L/Agree.lean` bridges arrays outside phase B's read set). -/
def freshZ : List ArrId := LMEMO :: parOwnedL

/-- The `CTL` of a fresh worker: the seed (its first 256 words), then zeros. -/
def freshCtl (c : Array Word) : Array Word := c.extract 0 256 ++ zeros (c.size - 256)

/-- **A thread's fresh worker memory** (the threads' entry 2, first call, after `check_b` copied the
seed): `m` with every frozen array cut to its extent, every owned array but `CTL` zero (at its
size in `m`), and `CTL` its first 256 words followed by zeros. Arrays neither frozen nor owned keep
`m`'s contents (phase B's loop does not name them; the worker's actual memory has them empty,
which `L/Agree.lean` bridges), except `LMEMO`, which is zero as well (`freshZ`). -/
def freshMem (m : Mem) : Mem :=
  let t := truncFrozen m
  { t with words := (Array.range t.words.size).map fun a =>
      if a = CTL then freshCtl (t.arr64 CTL)
      else if a ∈ freshZ then zeros (t.arr64 a).size
      else t.arr64 a }

/-! ## A thread's worker memory for one call (the threads' entry 2, `ca_check_b`) -/

/-- Frozen entry `i`'s offset and length in the buffer `B` (header words `8 + 2i`, `9 + 2i`; entry
`0` is the header itself). -/
def bufEntry (B : Array Word) (i : Nat) : Nat × Nat :=
  ((B.getD (8 + 2 * i) 0).toNat, (B.getD (9 + 2 * i) 0).toNat)

/-- The words of frozen entry `i` in `B`. -/
def bufImg (B : Array Word) (i : Nat) : Array Word :=
  B.extract (bufEntry B i).1 ((bufEntry B i).1 + (bufEntry B i).2)

/-- **The L memory of one `ca_check_b(buf, len, j, region, …)` call**, for the buffer's words `B`
and the region's L memory `r` (what the previous call on the region left; the zero memory on the
first call): frozen array `frozenIdsL[i]` is `bufImg B i`; the owned arrays (`parOwnedL`) are
`r`'s; every other word array and both byte arrays are empty; the globals are `r`'s with
`PLO := j`, `PHI := j + 1`, `MODE := 2`. -/
def bufMem (B : Array Word) (r : Mem) (j : Word) : Mem :=
  { bytes := #[#[], #[]]
    words := (Array.range r.words.size).map fun a =>
      match frozenIdsL.idxOf? a with
      | some i => bufImg B i
      | none => if parOwnedL.contains a then r.arr64 a else #[]
    glob := fun g =>
      if g = PLO then j else if g = PHI then j + 1 else if g = MODE then 2 else r.glob g }

end L.Arena
