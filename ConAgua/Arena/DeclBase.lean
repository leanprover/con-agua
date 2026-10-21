import ConAgua.Arena.Env
import ConAgua.Arena.CoreRefine
import ConAgua.Front.StateDR
import ConRon.Arena.Checker

/-!
# The declaration loop's relation (`LoopR`) and the pending checks (`PendR`)

Split out of `Checker.lean` so that the loop's callees (`Decl*.lean`) can state their specs over
`LoopR`: the pending checks `PEND` (137, three words each, `CTL[130]` of them), the promotion
memo's relation (a stub), `LoopR` (`CheckR` + `PendR` + the front's `DeclsR`), `dsAt`, `vgOut`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

namespace L.Arena

open L.Front (DECL DLP DeclsR)

/-- For `AM.res` at the fold's result types. -/
instance : Inhabited IFEnv := ⟨mkIFEnv IEnv.empty⟩

/-! ## The pending checks: `PEND` (137), `CTL[130]` -/

abbrev PEND : ArrId := 137

/-- The number of pending checks, `CTL[130]`. -/
def pendCount (m : Mem) : Nat := (rdW (m.arr64 CTL) 130).toNat

/-- Pending check `j`: three words of `PEND`, the value group a record of `EREC`. -/
def decPend (m : Mem) (j : Nat) : Option PendingCheck := do
  let a := m.arr64 PEND
  pure ⟨← decVG (m.arr64 EREC) (← nat? a (3 * j)), ← nat? a (3 * j + 1), ← nat? a (3 * j + 2)⟩

/-- **The pending checks.** -/
structure PendR (m : Mem) (pend : Array PendingCheck) : Prop where
  count : pendCount m = pend.size
  recs : ∀ j (h : j < pend.size), decPend m j = some pend[j]

/-- The promotion memo (an argument relation, arrays 144‥191). Stub: no fields. -/
structure PMemoR (m : Mem) (pm : PMemo) : Prop

/-! ## The loop's relation -/

/-- **What the declaration loop keeps**: the checker state at the view `vis` of `fe`, the
pending checks, and the declaration records. -/
structure LoopR (dn : NIdx → Option ConLeche.Name) (m : Mem) (a : AState) (vis : Word) (fe : IFEnv)
    (pend : Array PendingCheck) (ds : Array IDeclaration) : Prop where
  check : CheckR dn m a vis fe
  pend : PendR m pend
  decls : DeclsR (m.arr64 DECL) (m.arr64 DLP) ds

/-- Declaration record `i` (a plain function, so that congruence sees through it). -/
def dsAt (ds : Array IDeclaration) (i : Word) : IDeclaration := ds.getD i.toNat default

/-- The result of phase A: `.ok` with every record installed, and the loop's relation. -/
def FoldOut (dn : NIdx → Option ConLeche.Name) (m : Mem) (a : AState) (v : Word)
    (ds : Array IDeclaration) : Except (CheckError × Nat) (Nat × IFEnv × Array PendingCheck) → Prop
  | .ok (k, fe, pend) => k = ds.size ∧ LoopR dn m a v fe pend ds
  | .error _ => False

/-- Phase A's environment and pending checks out of its result. -/
def foldFe : Except (CheckError × Nat) (Nat × IFEnv × Array PendingCheck) → IFEnv
  | .ok (_, fe, _) => fe
  | .error _ => default
def foldPend : Except (CheckError × Nat) (Nat × IFEnv × Array PendingCheck) → Array PendingCheck
  | .ok (_, _, pend) => pend
  | .error _ => #[]

theorem FoldOut.eq {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {v : Word}
    {ds : Array IDeclaration} {x : Except (CheckError × Nat) (Nat × IFEnv × Array PendingCheck)}
    (h : FoldOut dn m a v ds x) :
    x = .ok (ds.size, foldFe x, foldPend x) ∧ LoopR dn m a v (foldFe x) (foldPend x) ds := by
  match x, h with
  | .ok (k, fe, pend), ⟨hk, hR⟩ => exact ⟨by rw [hk]; rfl, hR⟩

/-- A value group out of `install_step_go`: flag `f` (`0`: none) and record `g`. -/
def vgOut (m : Mem) (f g : Word) : Option ValueGroup :=
  if f = 0 then none else decVG (m.arr64 EREC) g.toNat


end L.Arena
