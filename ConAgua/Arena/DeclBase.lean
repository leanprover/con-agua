module

public import ConAgua.Rom.PinSets
public import ConAgua.Front.StateDR

@[expose] public section

/-!
# A job's relation (`LoopR`)

Split out of `Checker.lean` so that a job's callees (`Decl*.lean`) can state their specs over
`LoopR`: the checker state at the view `vis` of `fe` (`CheckR`, whose environment is the job's own
layer over the frozen stream index), the front's declaration records, the work pools, the pin
variants.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Front (DECL DLP DeclsF)

/-- For `AM.res` at the check's result types. -/
instance : Inhabited IFEnv := ⟨mkIFEnv IEnv.empty⟩

/-- A front record that is not an inductive block is a one-constant record. -/
theorem declAt_of_F {D P : Array Word} {i : Nat} {d : IDeclaration} (h : L.Front.DeclAtF D P i d)
    (hne : ∀ b k, d ≠ .indDecl b k) : L.Front.DeclAt D P i d := by
  cases d with
  | indDecl b k => exact (hne b k rfl).elim
  | _ => exact h

/-- **What a job keeps**: the checker state at the view `vis` of `fe`, and the declaration
records. -/
structure LoopR (pins : List INatOpPinSet) (m : Mem) (a : AState) (vis : Word) (fe : IFEnv)
    (ds : Array IDeclaration) : Prop where
  check : CheckR m a vis fe
  decls : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds
  /-- The work pool and the record pool are in bounds (lane `induct`'s `IWOK`): the callees of
  the check run on the stage relation `StageR = CheckR ∧ IWOK`. -/
  iw : L.Ind.IWOK m
  /-- The pin variants the startup interned are `pins` (lane `romload`'s `PinSetsR`): the
  definition arm's `Nat.div`-family gate reads them. -/
  pinsets : L.Rom.PinSetsR m pins

/-- `IWOK` survives a frame that keeps `IW`, both `EREC` tiers and the three tops `CTL[129]`,
`CTL[130]`, `CTL[200]` (the tier-1 premises last, discharged by `decide` for a concrete frame). -/
theorem IWOK.frame {m m' : Mem} {A : List TieredArray} {C : List Word} (hf : MemFrame A C m m')
    (hA : (L.Ind.IW : TieredArray) ∉ A) (hE : (EREC : TieredArray) ∉ A) (h129 : (129 : Word) ∉ C) (h200 : (200 : Word) ∉ C)
    (h : L.Ind.IWOK m) (hE1 : (tier1 EREC : TieredArray) ∉ A := by decide)
    (h130 : (130 : Word) ∉ C := by decide) : L.Ind.IWOK m' := by
  have hI : m'.arr64 L.Ind.IW = m.arr64 L.Ind.IW := hf.arr _ hA (by decide)
  have hR : m'.arr64 EREC = m.arr64 EREC := hf.arr _ hE (by decide)
  have hR1 : m'.arr64 (tier1 EREC) = m.arr64 (tier1 EREC) := hf.arr _ hE1 (by decide)
  have hc : (m'.arr64 CTL).size = (m.arr64 CTL).size := hf.size CTL
  have := (L.Ind.IWOK_iff m).mp h
  simp only [L.Ind.IWOK_iff, L.Ind.iwTop, L.Ind.erTop, erecTop1, hI, hR, hR1, hc, hf.ctl _ h129,
    hf.ctl _ h130, hf.ctl _ h200] at this ⊢
  exact this

/-- Declaration record `i` (a plain function, so that congruence sees through it). -/
def dsAt (ds : Array IDeclaration) (i : Word) : IDeclaration := ds.getD i.toNat default

end L.Arena
