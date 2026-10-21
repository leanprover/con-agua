import ConAgua.Arena.Env
import ConAgua.Front.StateDR
import ConRon.Arena.Checker

/-!
# The declaration loop in L, top down: `installFold`, `checkPendingList`, `installThenCheck`

The twin's two-phase fold (`vendor/con-ron/ConRon/Arena/Checker.lean`): phase A installs every
declaration record (`installFold` → `installDeclStep` → `installStep`, the per-declaration
bracket `flushCaches; enterScratch; installStepGo; promote…; dropScratch`), recording the value
groups to check; phase B checks each against the prefix view it was installed at
(`checkPendingList` → `checkPending`). This file has that structure in L, with the callees that
are not translated yet as **stubs** (L bodies `abort`, no census tags) whose refinement specs are
stated here and proved with `sorry` (each listed in DESIGN.md). The skeleton functions are real L
code; their refinements are proved from the stub specs, so the census counts them as proven with
`sorry` until the stubs are filled.

* The declarations are the front's records (`DECL`/`DLP`, `DeclsR`, `Front/StateDR.lean`); record
  `i` is the fold position `i`.
* The pending checks are `PEND` (137), three words each (the value group's record pointer in
  `EREC`, `pos`, `vis`), `CTL[130]` of them: `PendR`.
* Errors: the twin's error results (`.error (e, i)`) are `abort` (ROADMAP §3 (c), "L recovers
  nowhere"); a returning run is an accepting one.
* The relation the loop keeps, `LoopR`: `CheckR` (arena, caches, pins, the environment at a view),
  `PendR` and `DeclsR`.
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

/-- A value group out of `install_step_go`: flag `f` (`0`: none) and record `g`. -/
def vgOut (m : Mem) (f g : Word) : Option ValueGroup :=
  if f = 0 then none else decVG (m.arr64 EREC) g.toNat

section stubs
variable (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
  (ds : Array IDeclaration) (p : Prog)

/-! ## The stubs and their specs

Each stub is a not-yet-translated callee; the spec is what the real code will have to prove. -/

/-- Stub: `flushCaches` (the 14 cache epochs). -/
def flushCachesL : FunDecl := lfn (vis) locals () { abort }
/-- Stub: `enterScratch` (open the scratch tier, clear the walk memos). -/
def enterScratchL : FunDecl := lfn (vis) locals () { abort }
/-- Stub: `dropScratch` (drop the scratch tier, flush). -/
def dropScratchL : FunDecl := lfn (vis) locals () { abort }
/-- Stub: `andPinOk` on declaration record `i` (returns `1`/`0`). -/
def andPinOkL : FunDecl := lfn (i) locals () { abort }
/-- Stub: `installStepGo` on record `i` at view `vis`: returns the new view and the value group
(flag, record). -/
def installStepGoL : FunDecl := lfn (i, vis) locals () { abort }
/-- Stub: `promoteVG PMemo.empty coreWalkFuel` on the value group record `g`; returns the
promoted record. -/
def promoteVGL : FunDecl := lfn (g, vis) locals () { abort }
/-- Stub: `promoteNew pm coreWalkFuel k` at view `vis` (`fresh ≠ 0`: `pm = PMemo.empty`, else
the memo `promote_vg` left). -/
def promoteNewL : FunDecl := lfn (k, vis, fresh) locals () { abort }
/-- Stub: `checkValueGroup` at view `vis` on the value group record `g`. -/
def checkValueGroupL : FunDecl := lfn (vis, g) locals () { abort }

/-- The shape of a spec of a stub with no result that keeps `LoopR` (the view word is an
argument of every stub, so that a caller's `vcgen` sees it). -/
abbrev UnitSpec (f : FnName) (op : AM Unit) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (vis : Word) (fe : IFEnv) (pend : Array PendingCheck),
    LoopR dn s₀.mem a₀ vis fe pend ds →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) f [vis]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok op a₀ ∧ LoopR dn s'.mem (AM.st op a₀) vis fe pend ds; ⊤⦄

theorem flushCaches_spec : UnitSpec dn ds p "flush_caches" flushCaches := sorry
theorem enterScratch_spec : UnitSpec dn ds p "enter_scratch" enterScratch := sorry
theorem dropScratch_spec : UnitSpec dn ds p "drop_scratch" dropScratch := sorry

theorem andPinOk_spec :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (vis : Word) (fe : IFEnv) (pend : Array PendingCheck)
      (i : Word) (hi : i.toNat < ds.size), LoopR dn s₀.mem a₀ vis fe pend ds →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "and_pin_ok" [i]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (andPinOk (dsAt ds i)) a₀ ∧
      LoopR dn s'.mem (AM.st (andPinOk (dsAt ds i)) a₀) vis fe pend ds ∧
      AM.res (andPinOk (dsAt ds i)) a₀ = (r.headD 0 != 0); ⊤⦄ := sorry

theorem installStepGo_spec :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (vis : Word) (fe : IFEnv) (pend : Array PendingCheck)
      (i : Word) (hi : i.toNat < ds.size), LoopR dn s₀.mem a₀ vis fe pend ds →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_step_go" [i, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (installStepGo mode pins fe (dsAt ds i)) a₀ ∧
      LoopR dn s'.mem (AM.st (installStepGo mode pins fe (dsAt ds i)) a₀) (r.headD 0)
        (AM.res (installStepGo mode pins fe (dsAt ds i)) a₀).1 pend ds ∧
      (AM.res (installStepGo mode pins fe (dsAt ds i)) a₀).2 =
        vgOut s'.mem (r.tail.headD 0) (r.tail.tail.headD 0) ∧
      (r.tail.headD 0 ≠ 0 → (AM.res (installStepGo mode pins fe (dsAt ds i)) a₀).2 ≠ none); ⊤⦄ :=
  sorry

theorem promoteVG_spec :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (vis : Word) (fe : IFEnv) (pend : Array PendingCheck)
      (g : Word) (vg : ValueGroup), decVG (s₀.mem.arr64 EREC) g.toNat = some vg →
      LoopR dn s₀.mem a₀ vis fe pend ds →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "promote_vg" [g, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (promoteVG PMemo.empty coreWalkFuel vg) a₀ ∧
      LoopR dn s'.mem (AM.st (promoteVG PMemo.empty coreWalkFuel vg) a₀) vis fe pend ds ∧
      PMemoR s'.mem (AM.res (promoteVG PMemo.empty coreWalkFuel vg) a₀).1 ∧
      decVG (s'.mem.arr64 EREC) (r.headD 0).toNat =
        some (AM.res (promoteVG PMemo.empty coreWalkFuel vg) a₀).2; ⊤⦄ := sorry

theorem promoteNew_spec :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (vis : Word) (fe : IFEnv) (pend : Array PendingCheck)
      (k fresh : Word) (pm : PMemo), (if fresh = 0 then PMemoR s₀.mem pm else pm = PMemo.empty) →
      LoopR dn s₀.mem a₀ vis fe pend ds →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "promote_new" [k, vis, fresh]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (promoteNew pm coreWalkFuel k.toNat fe) a₀ ∧
      LoopR dn s'.mem (AM.st (promoteNew pm coreWalkFuel k.toNat fe) a₀) vis
        (AM.res (promoteNew pm coreWalkFuel k.toNat fe) a₀).2 pend ds; ⊤⦄ := sorry

theorem checkValueGroup_spec :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (vis : Word) (fe : IFEnv) (pend : Array PendingCheck)
      (g : Word) (vg : ValueGroup), decVG (s₀.mem.arr64 EREC) g.toNat = some vg →
      LoopR dn s₀.mem a₀ vis fe pend ds →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_value_group" [vis, g]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (checkValueGroup mode fe vg) a₀ ∧
      LoopR dn s'.mem (AM.st (checkValueGroup mode fe vg) a₀) vis fe pend ds; ⊤⦄ := sorry

end stubs

/-- The pending checks after pushing `(g, i, vis)`. -/
def pendPushMem (m : Mem) (g i vis : Word) : Mem :=
  let c := rdW (m.arr64 CTL) 130
  (((m.set64 PEND (3 * c) g).set64 PEND (3 * c + 1) i).set64 PEND (3 * c + 2) vis).set64 CTL 130
    (c + 1)

theorem LoopR.vis {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {v : Word}
    {fe : IFEnv} {pend : Array PendingCheck} {ds : Array IDeclaration}
    (h : LoopR dn m a v fe pend ds) : fe.visibleBelow = v.toNat := h.check.env.vis

/-- **Pushing a pending check** keeps the loop's relation. -/
theorem LoopR.pendPush {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {pend : Array PendingCheck} {ds : Array IDeclaration}
    (h : LoopR dn m a vis fe pend ds) (g i v : Word) (vg : ValueGroup)
    (hg : decVG (m.arr64 EREC) g.toNat = some vg)
    (hb : 3 * (rdW (m.arr64 CTL) 130).toNat + 2 < (m.arr64 PEND).size)
    (hc : 130 < (m.arr64 CTL).size) (h1 : (rdW (m.arr64 CTL) 130).toNat < 2 ^ 62) :
    LoopR dn (pendPushMem m g i v) a vis fe (pend.push ⟨vg, i.toNat, v.toNat⟩) ds := by
  have hc' := h.pend.count
  simp only [pendCount] at hc'
  generalize hcw : rdW (m.arr64 CTL) 130 = c at hb h1 hc'
  have hf : MemFrame [PEND] [130] m (pendPushMem m g i v) := by
    simp only [pendPushMem, hcw]
    have fP : ∀ (m₁ : Mem) (k x : Word), MemFrame [PEND] [130] m₁ (m₁.set64 PEND k x) :=
      fun m₁ k x => MemFrame.mono (MemFrame.set64 m₁ PEND (by decide) k x) (by simp) (by simp)
    have fC : ∀ (m₁ : Mem) (x : Word), MemFrame [PEND] [130] m₁ (m₁.set64 CTL 130 x) :=
      fun m₁ x => MemFrame.mono (MemFrame.setCtl m₁ 130 x) (by simp) (by simp)
    exact (((fP _ _ _).trans (fP _ _ _)).trans (fP _ _ _)).trans (fC _ _)
  have hE : (pendPushMem m g i v).arr64 EREC = m.arr64 EREC := hf.1 _ (by decide) (by decide)
  have hD1 : (pendPushMem m g i v).arr64 DECL = m.arr64 DECL := hf.1 _ (by decide) (by decide)
  have hD2 : (pendPushMem m g i v).arr64 DLP = m.arr64 DLP := hf.1 _ (by decide) (by decide)
  have hc1 : (c + 1).toNat = c.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  have h30 : (3 * c).toNat = 3 * c.toNat := by rw [UInt64.toNat_mul]; simp; omega
  have h31 : (3 * c + 1).toNat = 3 * c.toNat + 1 := by
    rw [UInt64.toNat_add, h30]; simp; omega
  have h32 : (3 * c + 2).toNat = 3 * c.toNat + 2 := by
    rw [UInt64.toNat_add, h30]; simp; omega
  have hP : (pendPushMem m g i v).arr64 PEND =
      (((m.arr64 PEND).set! (3 * c.toNat) g).set! (3 * c.toNat + 1) i).set! (3 * c.toNat + 2) v := by
    simp only [pendPushMem, hcw, Mem.arr64_set64_ne _ _ _ _ _ (show PEND ≠ CTL by decide),
      Mem.arr64_set64_same, h30, h31, h32]
  have hC : (pendPushMem m g i v).arr64 CTL = (m.arr64 CTL).set! 130 (c + 1) := by
    simp only [pendPushMem, hcw, Mem.arr64_set64_same,
      Mem.arr64_set64_ne _ _ _ _ _ (show CTL ≠ PEND by decide)]
    rfl
  refine ⟨h.check.frame_hi (by simp) (by simp) hf, ⟨?_, ?_⟩, by rw [hD1, hD2]; exact h.decls⟩
  · simp only [pendCount, hC, rdW_set!]
    simp [hc, hc1, hc']
  · intro j hj
    simp only [Array.size_push] at hj
    simp only [decPend, hP, hE, nat?, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    by_cases hjs : j < pend.size
    · have := h.pend.recs j hjs
      simp only [decPend, nat?] at this
      simp only [Array.getElem_push, hjs, dite_true]
      rw [← this]
      have e1 : ¬ 3 * c.toNat + 2 = 3 * j := by omega
      have e2 : ¬ 3 * c.toNat + 1 = 3 * j := by omega
      have e3 : ¬ 3 * c.toNat = 3 * j := by omega
      have e4 : ¬ 3 * c.toNat + 2 = 3 * j + 1 := by omega
      have e5 : ¬ 3 * c.toNat + 1 = 3 * j + 1 := by omega
      have e6 : ¬ 3 * c.toNat = 3 * j + 1 := by omega
      have e7 : ¬ 3 * c.toNat + 2 = 3 * j + 2 := by omega
      have e8 : ¬ 3 * c.toNat + 1 = 3 * j + 2 := by omega
      have e9 : ¬ 3 * c.toNat = 3 * j + 2 := by omega
      simp [e1, e2, e3, e4, e5, e6, e7, e8, e9]
    · have hj' : j = pend.size := by omega
      subst hj'
      simp only [Array.getElem_push, Nat.lt_irrefl, dite_false, ← hc']
      have : 3 * c.toNat + 2 < (m.arr64 PEND).size := hb
      simp [this, show 3 * c.toNat < (m.arr64 PEND).size by omega,
        show 3 * c.toNat + 1 < (m.arr64 PEND).size by omega, hg]

@[simp] theorem exc_ok_bind {ε α β : Type} (x : α) (f : α → Except ε β) :
    (Except.ok x >>= f) = f x := rfl

section twin
variable (mode : ConLeche.CheckMode) (pins : List INatOpPinSet)

theorem installStep_none_run (i : Nat) (fe : IFEnv) (pend : Array PendingCheck)
    (pd : IDeclaration) (a0 a1 a2 a3 a4 a5 : AState) (fe' fe'' : IFEnv) (pm : PMemo)
    (h1 : flushCaches.run a0 = .ok ((), a1)) (h2 : enterScratch.run a1 = .ok ((), a2))
    (h3 : (installStepGo mode pins fe pd).run a2 = .ok ((fe', none), a3))
    (h4 : (promoteNew PMemo.empty coreWalkFuel (fe'.visibleBelow - fe.visibleBelow) fe').run a3 =
      .ok ((pm, fe''), a4))
    (h5 : dropScratch.run a4 = .ok ((), a5)) :
    (installStep mode pins i fe pend pd).run a0 = .ok ((fe'', pend), a5) := by
  simp only [installStep, StateT.run_bind, exc_ok_bind, h1, h2, h3, h4, h5]
  rfl

theorem installStep_some_run (i : Nat) (fe : IFEnv) (pend : Array PendingCheck)
    (pd : IDeclaration) (a0 a1 a2 a3 a4 a5 a6 : AState) (fe' fe'' : IFEnv) (pm pm' : PMemo)
    (vg vg' : ValueGroup)
    (h1 : flushCaches.run a0 = .ok ((), a1)) (h2 : enterScratch.run a1 = .ok ((), a2))
    (h3 : (installStepGo mode pins fe pd).run a2 = .ok ((fe', some vg), a3))
    (h4 : (promoteVG PMemo.empty coreWalkFuel vg).run a3 = .ok ((pm, vg'), a4))
    (h5 : (promoteNew pm coreWalkFuel (fe'.visibleBelow - fe.visibleBelow) fe').run a4 =
      .ok ((pm', fe''), a5))
    (h6 : dropScratch.run a5 = .ok ((), a6)) :
    (installStep mode pins i fe pend pd).run a0 =
      .ok ((fe'', pend.push ⟨vg', i, fe.visibleBelow⟩), a6) := by
  simp only [installStep, StateT.run_bind, exc_ok_bind, h1, h2, h3, h4, h5, h6]
  rfl

/-- `installStep`'s `none` arm, named. -/
def isNoneT (vis : Nat) (fe' : IFEnv) (pend : Array PendingCheck) :
    AM (IFEnv × Array PendingCheck) := do
  let r ← promoteNew PMemo.empty coreWalkFuel (fe'.visibleBelow - vis) fe'
  dropScratch
  pure (r.2, pend)

/-- `installStep`'s `some` arm, named. -/
def isSomeT (i vis : Nat) (fe' : IFEnv) (pend : Array PendingCheck) (vg : ValueGroup) :
    AM (IFEnv × Array PendingCheck) := do
  let r ← promoteVG PMemo.empty coreWalkFuel vg
  let r2 ← promoteNew r.1 coreWalkFuel (fe'.visibleBelow - vis) fe'
  dropScratch
  pure (r2.2, pend.push ⟨r.2, i, vis⟩)

/-- `installStep` after `installStepGo`, named. -/
def installStepK (i vis : Nat) (pend : Array PendingCheck) (r : IFEnv × Option ValueGroup) :
    AM (IFEnv × Array PendingCheck) :=
  match r.2 with
  | none => isNoneT vis r.1 pend
  | some vg => isSomeT i vis r.1 pend vg

theorem installStep_eq (i : Nat) (fe : IFEnv) (pend : Array PendingCheck) (pd : IDeclaration) :
    installStep mode pins i fe pend pd = (do
      flushCaches
      enterScratch
      let r ← installStepGo mode pins fe pd
      installStepK i fe.visibleBelow pend r) := by
  simp only [installStep, installStepK, isNoneT, isSomeT]; rfl

theorem installStepK_none (i v : Nat) (pend : Array PendingCheck) (r : IFEnv × Option ValueGroup)
    (h : r.2 = none) : installStepK i v pend r = isNoneT v r.1 pend := by
  simp [installStepK, h]

theorem installStepK_some (i v : Nat) (pend : Array PendingCheck) (r : IFEnv × Option ValueGroup)
    (vg : ValueGroup) (h : r.2 = some vg) : installStepK i v pend r = isSomeT i v r.1 pend vg := by
  simp [installStepK, h]

/-- `installStep` from its pieces, in `AM.ok`/`AM.st`/`AM.res` terms. -/
theorem installStep_ok (i : Nat) (fe : IFEnv) (pend : Array PendingCheck) (pd : IDeclaration)
    (a0 : AState) (h1 : AM.ok flushCaches a0) (h2 : AM.ok enterScratch (AM.st flushCaches a0))
    (h3 : AM.ok (installStepGo mode pins fe pd) (AM.st enterScratch (AM.st flushCaches a0))) (h4 : AM.ok (installStepK i fe.visibleBelow pend (AM.res (installStepGo mode pins fe pd) (AM.st enterScratch (AM.st flushCaches a0)))) (AM.st (installStepGo mode pins fe pd) (AM.st enterScratch (AM.st flushCaches a0)))) :
    AM.ok (installStep mode pins i fe pend pd) a0 ∧ AM.st (installStep mode pins i fe pend pd) a0 = AM.st (installStepK i fe.visibleBelow pend (AM.res (installStepGo mode pins fe pd) (AM.st enterScratch (AM.st flushCaches a0)))) (AM.st (installStepGo mode pins fe pd) (AM.st enterScratch (AM.st flushCaches a0))) ∧ AM.res (installStep mode pins i fe pend pd) a0 = AM.res (installStepK i fe.visibleBelow pend (AM.res (installStepGo mode pins fe pd) (AM.st enterScratch (AM.st flushCaches a0)))) (AM.st (installStepGo mode pins fe pd) (AM.st enterScratch (AM.st flushCaches a0))) := by
  have r1 := AM.run_of_ok _ _ h1
  have r2 := AM.run_of_ok _ _ h2
  have r3 := AM.run_of_ok _ _ h3
  have r4 := AM.run_of_ok _ _ h4
  apply AM.of_run_ok
  rw [installStep_eq]
  simp only [StateT.run_bind, exc_ok_bind, r1, r2, r3, r4]

end twin

/-! ## Phase A's step: `install_step` -/


/-- `is_none(vis, v2)`: `installStep`'s `none` arm (`isNoneT`). -/
@[l_impl ConRon.Arena.installStep]
def isNoneL : FunDecl := lfn (vis, v2) locals (k, z) {
  k := 0;
  if vis <= v2 { k := v2 - vis };
  z := call promote_new(k, v2, 1);
  z := call drop_scratch(v2);
  return 0
}

/-- `pend_push(g, i, v)`: append the pending check `(g, i, v)` to `PEND`. -/
def pendPushL : FunDecl := lfn (g, i, v) locals (c) {
  c := CTL.u64[130];
  if 4611686018427387904 <= c { abort };
  PEND.u64[3 * c] := g;
  PEND.u64[3 * c + 1] := i;
  PEND.u64[3 * c + 2] := v;
  CTL.u64[130] := c + 1;
  return 0
}

/-- `is_some(i, vis, v2, g)`: `installStep`'s `some` arm (`isSomeT`); the pending check is
written right after `promote_vg` (where its record is known to decode), the twin pushes it at
the end (a value, so the order is invisible). -/
@[l_impl ConRon.Arena.installStep]
def isSomeL : FunDecl := lfn (i, vis, v2, g) locals (k, z, g2) {
  k := 0;
  if vis <= v2 { k := v2 - vis };
  g2 := call promote_vg(g, v2);
  z := call pend_push(g2, i, vis);
  z := call promote_new(k, v2, 0);
  z := call drop_scratch(v2);
  return 0
}

/-- `install_step(i, vis)`: `installStep` (the bracket, `installStepGo`, then one of the arms). -/
@[l_impl ConRon.Arena.installStep]
def installStepL : FunDecl := lfn (i, vis) locals (v2, f, g, z) {
  z := call flush_caches(vis);
  z := call enter_scratch(vis);
  (v2, f, g) := call install_step_go(i, vis);
  if f == 0 { z := call is_none(vis, v2) } else { z := call is_some(i, vis, v2, g) };
  return v2
}

section skel
variable (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
  (ds : Array IDeclaration) (p : Prog)

theorem isNone_refines (hp : p.lookup "is_none" = some isNoneL) (n : Nat) (s₀ : St) (a₀ : AState)
    (vis v2 : Word) (fe' : IFEnv) (pend : Array PendingCheck)
    (hR : LoopR dn s₀.mem a₀ v2 fe' pend ds) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "is_none" [vis, v2]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (isNoneT vis.toNat fe' pend) a₀ ∧
      LoopR dn s'.mem (AM.st (isNoneT vis.toNat fe' pend) a₀) v2
        (AM.res (isNoneT vis.toNat fe' pend) a₀).1 (AM.res (isNoneT vis.toNat fe' pend) a₀).2 ds; ⊤⦄ := by
  have hv := hR.vis
  rw [invoke_eq _ hp]
  simp only [callFn, isNoneL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        (promoteNew_spec dn ds p n · a₀ · fe' pend · · PMemo.empty),
        (dropScratch_spec dn ds p n · (AM.st (promoteNew PMemo.empty coreWalkFuel
          (fe'.visibleBelow - vis.toNat) fe') a₀) ·
          (AM.res (promoteNew PMemo.empty coreWalkFuel (fe'.visibleBelow - vis.toNat) fe') a₀).2
          pend)] <;>
      finish [isNoneT]

theorem pendPush_spec (hp : p.lookup "pend_push" = some pendPushL) (n : Nat) (s₀ : St)
    (a₀ : AState) (vis : Word) (fe : IFEnv) (pend : Array PendingCheck) (g i v : Word)
    (vg : ValueGroup) (hg : decVG (s₀.mem.arr64 EREC) g.toNat = some vg)
    (hR : LoopR dn s₀.mem a₀ vis fe pend ds) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pend_push" [g, i, v]
    ⦃fun _ s' => LocEq s' s₀ ∧
      LoopR dn s'.mem a₀ vis fe (pend.push ⟨vg, i.toNat, v.toNat⟩) ds; ⊤⦄ := by
  have key := hR.pendPush g i v vg hg
  have hrd : ∀ (h : 130 < (s₀.mem.arr64 CTL).size),
      rdW (s₀.mem.arr64 CTL) 130 = (s₀.mem.arr64 CTL)[130] := fun h => rdW_eq _ _ 130 rfl h
  rw [invoke_eq _ hp]
  simp only [callFn, pendPushL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64] <;>
      finish [pendPushMem]

theorem isSome_refines (hpp : p.lookup "pend_push" = some pendPushL)
    (hp : p.lookup "is_some" = some isSomeL) (n : Nat) (s₀ : St) (a₀ : AState)
    (i vis v2 g : Word) (fe' : IFEnv) (pend : Array PendingCheck) (vg : ValueGroup)
    (hg : decVG (s₀.mem.arr64 EREC) g.toNat = some vg)
    (hR : LoopR dn s₀.mem a₀ v2 fe' pend ds) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "is_some" [i, vis, v2, g]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (isSomeT i.toNat vis.toNat fe' pend vg) a₀ ∧
      LoopR dn s'.mem (AM.st (isSomeT i.toNat vis.toNat fe' pend vg) a₀) v2
        (AM.res (isSomeT i.toNat vis.toNat fe' pend vg) a₀).1
        (AM.res (isSomeT i.toNat vis.toNat fe' pend vg) a₀).2 ds; ⊤⦄ := by
  -- `PEND` is not the promotion memo's (arrays 144‥191): `pend_push` keeps `PMemoR` (a stub
  -- with no fields today; with fields, by its group frame)
  have hPM : ∀ m pm, PMemoR m pm := fun _ _ => ⟨⟩
  have hv := hR.vis
  rw [invoke_eq _ hp]
  simp only [callFn, isSomeL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        (promoteVG_spec dn ds p n · a₀ · fe' pend · vg),
        (pendPush_spec dn ds p hpp n · (AM.st (promoteVG PMemo.empty coreWalkFuel vg) a₀) v2 fe' pend ·
          · · (AM.res (promoteVG PMemo.empty coreWalkFuel vg) a₀).2),
        (promoteNew_spec dn ds p n · (AM.st (promoteVG PMemo.empty coreWalkFuel vg) a₀) · fe' (pend.push ⟨(AM.res (promoteVG PMemo.empty coreWalkFuel vg) a₀).2, i.toNat, vis.toNat⟩) · · (AM.res (promoteVG PMemo.empty coreWalkFuel vg) a₀).1),
        (dropScratch_spec dn ds p n · (AM.st (promoteNew (AM.res (promoteVG PMemo.empty coreWalkFuel vg) a₀).1 coreWalkFuel (fe'.visibleBelow - vis.toNat) fe') (AM.st (promoteVG PMemo.empty coreWalkFuel vg) a₀)) · (AM.res (promoteNew (AM.res (promoteVG PMemo.empty coreWalkFuel vg) a₀).1 coreWalkFuel (fe'.visibleBelow - vis.toNat) fe') (AM.st (promoteVG PMemo.empty coreWalkFuel vg) a₀)).2 (pend.push ⟨(AM.res (promoteVG PMemo.empty coreWalkFuel vg) a₀).2, i.toNat, vis.toNat⟩))] <;>
      finish [isSomeT]

/-- `install_step`, stated over the pieces of `installStep` (`installStep_ok` assembles them). -/
theorem installStep_pieces (hpp : p.lookup "pend_push" = some pendPushL)
    (hpn : p.lookup "is_none" = some isNoneL) (hps : p.lookup "is_some" = some isSomeL)
    (hp : p.lookup "install_step" = some installStepL) (n : Nat) (s₀ : St) (a₀ : AState)
    (i vis : Word) (fe : IFEnv) (pend : Array PendingCheck) (hi : i.toNat < ds.size)
    (hR : LoopR dn s₀.mem a₀ vis fe pend ds) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_step" [i, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok flushCaches a₀ ∧ AM.ok enterScratch (AM.st flushCaches a₀) ∧ AM.ok (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀)) ∧
      AM.ok (installStepK i.toNat vis.toNat pend (AM.res (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀)))) (AM.st (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀))) ∧ LoopR dn s'.mem (AM.st (installStepK i.toNat vis.toNat pend (AM.res (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀)))) (AM.st (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀)))) (r.headD 0) (AM.res (installStepK i.toNat vis.toNat pend (AM.res (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀)))) (AM.st (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀)))).1
        (AM.res (installStepK i.toNat vis.toNat pend (AM.res (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀)))) (AM.st (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀)))).2 ds; ⊤⦄ := by
  have hK0 : (AM.res (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀))).2 = none → (installStepK i.toNat vis.toNat pend (AM.res (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀)))) = isNoneT vis.toNat (AM.res (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀))).1 pend :=
    fun h => installStepK_none _ _ _ _ h
  have hK1 : (AM.res (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀))).2 ≠ none → (installStepK i.toNat vis.toNat pend (AM.res (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀)))) = isSomeT i.toNat vis.toNat (AM.res (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀))).1 pend ((AM.res (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀))).2.getD default) := by
    intro h
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp h
    rw [installStepK_some _ _ _ _ x hx, hx]; rfl
  have hsome : (AM.res (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀))).2 ≠ none →
      (AM.res (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀))).2 =
        some ((AM.res (installStepGo mode pins fe (dsAt ds i))
          (AM.st enterScratch (AM.st flushCaches a₀))).2.getD default) := by
    intro h; obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp h; rw [hx]; rfl
  rw [invoke_eq _ hp]
  simp only [callFn, installStepL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        (flushCaches_spec dn ds p n · a₀ · fe pend),
        (enterScratch_spec dn ds p n · (AM.st flushCaches a₀) · fe pend),
        (installStepGo_spec mode pins dn ds p n · (AM.st enterScratch (AM.st flushCaches a₀)) · fe pend · ·),
        (isNone_refines dn ds p hpn n · (AM.st (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀))) · · (AM.res (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀))).1 pend),
        (isSome_refines dn ds p hpp hps n · (AM.st (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀))) · · · · (AM.res (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀))).1 pend ((AM.res (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀))).2.getD default))] <;>
      -- the view `vis` is read after three calls: four `LocEq` hops (depth, not search)
      finish (gen := 20) [vgOut]

/-- **`install_step` refines `installStep`** (from the stub specs). -/
@[refines ConRon.Arena.installStep]
theorem installStep_refines (hpp : p.lookup "pend_push" = some pendPushL)
    (hpn : p.lookup "is_none" = some isNoneL) (hps : p.lookup "is_some" = some isSomeL)
    (hp : p.lookup "install_step" = some installStepL) (n : Nat) (s₀ : St) (a₀ : AState)
    (i vis : Word) (fe : IFEnv) (pend : Array PendingCheck) (hi : i.toNat < ds.size)
    (hR : LoopR dn s₀.mem a₀ vis fe pend ds) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_step" [i, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (installStep mode pins i.toNat fe pend (dsAt ds i)) a₀ ∧
      LoopR dn s'.mem (AM.st (installStep mode pins i.toNat fe pend (dsAt ds i)) a₀) (r.headD 0) (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) a₀).1 (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) a₀).2 ds; ⊤⦄ := by
  have hv := hR.vis
  refine triple_post (installStep_pieces mode pins dn ds p hpp hpn hps hp n s₀ a₀ i vis fe pend hi hR)
    fun r s' ⟨hl, h1, h2, h3, h4, h5⟩ => ?_
  rw [← hv] at h4 h5
  obtain ⟨o, st, rs⟩ := installStep_ok mode pins i.toNat fe pend (dsAt ds i) a₀ h1 h2 h3 h4
  exact ⟨hl, o, by rw [st, rs]; exact h5⟩

end skel

end L.Arena

