import ConAgua.Arena.PromoteMemo
import ConAgua.Rom.PinSets

/-!
# The declaration loop's relation (`LoopR`) and the pending checks (`PendR`)

Split out of `Checker.lean` so that the loop's callees (`Decl*.lean`) can state their specs over
`LoopR`: the pending checks `PEND` (137, three words each, `CTL[130]` of them), the promotion
`LoopR` (`CheckR` + `PendR` + the front's `DeclsF` + the work pools + the promotion memo's arrays),
`dsAt`, `vgOut`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Front (DECL DLP DeclsF)

/-- For `AM.res` at the fold's result types. -/
instance : Inhabited IFEnv := ⟨mkIFEnv IEnv.empty⟩

/-! ## The pending checks: `PEND` (137), `CTL[130]` -/

/-- The number of pending checks, `CTL[130]`. -/
def pendCount (m : Mem) : Nat := (rdW (m.arr64 CTL) 130).toNat

/-- Pending check `j`: three words of `PEND`, the value group a record of `EREC`. -/
def decPend (m : Mem) (j : Nat) : Option PendingCheck := do
  let a := m.arr64 PEND
  pure ⟨← decVG (erecP m) (← nat? a (3 * j)), ← nat? a (3 * j + 1), ← nat? a (3 * j + 2)⟩

/-- **The pending checks.** -/
structure PendR (m : Mem) (pend : Array PendingCheck) : Prop where
  count : pendCount m = pend.size
  recs : ∀ j (h : j < pend.size), decPend m j = some pend[j]
  /-- The count is at most `2^62` (`pend_push` aborts at `2^62`), so `PEND`'s extent `3 · count`
  does not wrap (the truncation, `FreezeTrunc.lean`). -/
  bound : pendCount m ≤ 2 ^ 62

/-! ## The loop's relation -/

/-- A front record that is not an inductive block is a one-constant record. -/
theorem declAt_of_F {D P : Array Word} {i : Nat} {d : IDeclaration} (h : L.Front.DeclAtF D P i d)
    (hne : ∀ b k, d ≠ .indDecl b k) : L.Front.DeclAt D P i d := by
  cases d with
  | indDecl b k => exact (hne b k rfl).elim
  | _ => exact h

/-- **What the declaration loop keeps**: the checker state at the view `vis` of `fe`, the
pending checks, and the declaration records. -/
structure LoopR (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (m : Mem) (a : AState)
    (vis : Word) (fe : IFEnv) (pend : Array PendingCheck) (ds : Array IDeclaration) : Prop where
  check : CheckR dn m a vis fe
  pend : PendR m pend
  decls : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds
  /-- The work pool and the record pool are in bounds (lane `induct`'s `IWOK`): the callees of
  the step run on the stage relation `StageR = CheckR ∧ IWOK`. -/
  iw : L.Ind.IWOK m
  /-- The promotion memo's arrays hold some memo (`PMemoR`): the promotion clears them at each
  declaration (an epoch bump), which needs them well formed. -/
  pmemo : ∃ pm, PMemoR m pm
  /-- The pin variants the startup interned are `pins` (lane `romload`'s `PinSetsR`): the
  definition arm's `Nat.div`-family gate reads them. -/
  pinsets : L.Rom.PinSetsR m pins

/-- `IWOK` survives a frame that keeps `IW`, `EREC` and the two tops `CTL[129]`, `CTL[200]`. -/
theorem IWOK.frame {m m' : Mem} {A : List ArrId} {C : List Word} (hf : MemFrame A C m m')
    (hA : L.Ind.IW ∉ A) (hE : EREC ∉ A) (h129 : (129 : Word) ∉ C) (h200 : (200 : Word) ∉ C)
    (h : L.Ind.IWOK m) : L.Ind.IWOK m' := by
  have hI : m'.arr64 L.Ind.IW = m.arr64 L.Ind.IW := hf.1 _ hA (by decide)
  have hR : m'.arr64 EREC = m.arr64 EREC := hf.1 _ hE (by decide)
  have hc : (m'.arr64 CTL).size = (m.arr64 CTL).size := hf.2.2.1 CTL
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  simp only [L.Ind.IWOK, L.Ind.iwTop, L.Ind.erTop, hI, hR, hc, hf.2.1 _ h129, hf.2.1 _ h200]
  exact ⟨h1, h2, h3, h4, h5⟩

/-- Declaration record `i` (a plain function, so that congruence sees through it). -/
def dsAt (ds : Array IDeclaration) (i : Word) : IDeclaration := ds.getD i.toNat default

/-- The result of phase A: `.ok` with every record installed, and the loop's relation. -/
def FoldOut (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (m : Mem) (a : AState) (v : Word)
    (ds : Array IDeclaration) : Except (CheckError × Nat) (Nat × IFEnv × Array PendingCheck) → Prop
  | .ok (k, fe, pend) => k = ds.size ∧ LoopR pins dn m a v fe pend ds
  | .error _ => False

/-- Phase A's environment and pending checks out of its result. -/
def foldFe : Except (CheckError × Nat) (Nat × IFEnv × Array PendingCheck) → IFEnv
  | .ok (_, fe, _) => fe
  | .error _ => default
def foldPend : Except (CheckError × Nat) (Nat × IFEnv × Array PendingCheck) → Array PendingCheck
  | .ok (_, _, pend) => pend
  | .error _ => #[]

theorem FoldOut.eq {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {v : Word}
    {ds : Array IDeclaration} {x : Except (CheckError × Nat) (Nat × IFEnv × Array PendingCheck)}
    (h : FoldOut pins dn m a v ds x) :
    x = .ok (ds.size, foldFe x, foldPend x) ∧ LoopR pins dn m a v (foldFe x) (foldPend x) ds := by
  match x, h with
  | .ok (k, fe, pend), ⟨hk, hR⟩ => exact ⟨by rw [hk]; rfl, hR⟩

/-- A value group out of `install_step_go`: flag `f` (`0`: none) and record `g`. -/
def vgOut (m : Mem) (f g : Word) : Option ValueGroup :=
  if f = 0 then none else decVG (erecP m) g.toNat

end L.Arena
