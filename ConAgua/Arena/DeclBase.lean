import ConAgua.Arena.Env
import ConAgua.Arena.IndIface
import ConAgua.Arena.CoreRefine
import ConAgua.Front.StateDR
import ConAgua.Arena.PromoteProg
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
  pure ⟨← decVG (erecP m) (← nat? a (3 * j)), ← nat? a (3 * j + 1), ← nat? a (3 * j + 2)⟩

/-- **The pending checks.** -/
structure PendR (m : Mem) (pend : Array PendingCheck) : Prop where
  count : pendCount m = pend.size
  recs : ∀ j (h : j < pend.size), decPend m j = some pend[j]

/-! ## The promotion memo: four memos of the library (`Promote.lean`) -/

/-- A promotion memo's keys: one handle word (below `2^32`), the second key word `0`. -/
def hKey (k : IdxKind) : MemoKey (Idx k) where
  dk k1 _ := decI k1
  ek x := (x.word.toUInt64, 0)
  ok k1 k2 := k1.toNat < 2 ^ 32 ∧ k2 = 0
  ek_dk k1 k2 h := by
    have e : (decI k1 : Idx k).word.toUInt64 = k1 := (word_decI _ k1 h.1).mpr rfl
    simp only [e, h.2]
  ok_tomb k1 k2 h e := by subst e; exact absurd h.1 (by decide)

/-- A promotion memo's values: a handle word below `2^32` of the **persistent** tier (every
promoted handle is persistent), denoting the entry. Independent of the memory. -/
def VP (k : IdxKind) (_ : Mem) (w : Word) (v : Idx k) : Prop :=
  v = decI w ∧ w.toNat < 2 ^ 32 ∧ tierW w = 0

/-- **The promotion memo** (an argument relation, arrays 146‥149, `CTL` 140‥147): the twin's four
`PMemo` maps are the four memos. -/
structure PMemoR (m : Mem) (pm : PMemo) : Prop where
  n : MemoRV pnSch (hKey .name) (VP .name) m pm.nM
  l : MemoRV plSch (hKey .level) (VP .level) m pm.lM
  ls : MemoRV plsSch (hKey .levels) (VP .levels) m pm.lsM
  e : MemoRV peSch (hKey .expr) (VP .expr) m pm.eM

/-- **The promotion memo's frame**: a writer of other arrays and other `CTL` words keeps it. -/
theorem PMemoR.frame {A : List ArrId} {C : List Word} {m m' : Mem} {pm : PMemo}
    (hA : ∀ b ∈ A, b < 146 ∨ 149 < b) (hC : ∀ x ∈ C, x.toNat < 140 ∨ 147 < x.toNat)
    (hf : MemFrame A C m m') (h : PMemoR m pm) : PMemoR m' pm :=
  ⟨memoRV_frame pnSch ⟨by decide, by decide⟩ _ _ A C (fun h => by have := hA _ h; revert this; decide)
      (fun h => by have := hC _ h; simp at this) m m' hf (fun _ _ h => h) _ h.n,
    memoRV_frame plSch ⟨by decide, by decide⟩ _ _ A C (fun h => by have := hA _ h; revert this; decide)
      (fun h => by have := hC _ h; simp at this) m m' hf (fun _ _ h => h) _ h.l,
    memoRV_frame plsSch ⟨by decide, by decide⟩ _ _ A C (fun h => by have := hA _ h; revert this; decide)
      (fun h => by have := hC _ h; simp at this) m m' hf (fun _ _ h => h) _ h.ls,
    memoRV_frame peSch ⟨by decide, by decide⟩ _ _ A C (fun h => by have := hA _ h; revert this; decide)
      (fun h => by have := hC _ h; simp at this) m m' hf (fun _ _ h => h) _ h.e⟩

/-! ## The loop's relation -/

/-- **What the declaration loop keeps**: the checker state at the view `vis` of `fe`, the
pending checks, and the declaration records. -/
structure LoopR (dn : NIdx → Option ConLeche.Name) (m : Mem) (a : AState) (vis : Word) (fe : IFEnv)
    (pend : Array PendingCheck) (ds : Array IDeclaration) : Prop where
  check : CheckR dn m a vis fe
  pend : PendR m pend
  decls : DeclsR (m.arr64 DECL) (m.arr64 DLP) ds
  /-- The work pool and the record pool are in bounds (lane `induct`'s `IWOK`): the callees of
  the step run on the stage relation `StageR = CheckR ∧ IWOK`. -/
  iw : L.Ind.IWOK m

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
  if f = 0 then none else decVG (erecP m) g.toNat


end L.Arena
