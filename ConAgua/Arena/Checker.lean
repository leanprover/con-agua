import ConAgua.Arena.Env
import ConAgua.Arena.CoreRefine
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
code; their refinements are proved from the stub specs and tagged `@[refines …]`, so the census
counts the skeleton as proven with `sorry` (the stub specs). A refinement modulo `sorry` gives its
callees no coverage (scripts/census.py), so the targets below `installFold` keep their own status.
`installThenCheck` is not a
census target (`TwinAccepts` runs `installFold` and `checkPendingList` itself);
`install_then_check` is the loop's top for the driver.

* The declarations are the front's records (`DECL`/`DLP`, `DeclsR`, `Front/StateDR.lean`); record
  `i` is the fold position `i`.
* The pending checks are `PEND` (137), three words each (the value group's record pointer in
  `EREC`, `pos`, `vis`), `CTL[130]` of them: `PendR`.
* Errors: the twin's error results (`.error (e, i)`) are `abort` (ROADMAP §3 (c), "L recovers
  nowhere"); a returning run is an accepting one.
* The relation the loop keeps, `LoopR`: `CheckR` (arena, caches, pins, the environment at a view),
  `PendR` and `DeclsR`.
* The bracket (`flush_caches`, `scratch_enter`, `scratch_drop`) is lane `whnf`'s real code,
  lifted to `LoopR` here (`flush_loop`, `enter_loop`, `drop_loop`).
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

section stubs
variable (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
  (ds : Array IDeclaration) (p : Prog)

/-! ## The stubs and their specs

Each stub is a not-yet-translated callee; the spec is what the real code will have to prove. -/

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

/-! ## The bracket: lane `whnf`'s `flush_caches`, `scratch_enter`, `scratch_drop` under `LoopR`

They refine `flushCaches`/`enterScratch`/`dropScratch` under `CheckR` (`CoreRefine.lean`,
`ScratchRefine.lean`) and write `CTL` words below 128 only, so the pending checks and the
declaration records ride along. -/

/-- The bracket's functions in a program. -/
structure BracketProg (p : Prog) : Prop where
  fl : FlushProg p
  se : p.lookup "scratch_enter" = some scratchEnter
  sd : p.lookup "scratch_drop" = some scratchDrop
  sr : p.lookup "scratch_reset" = some scratchReset
  bm : p.lookup "bm_clear" = some (memoClearG bmSch)
  lf : p.lookup "lf_clear" = some (memoClearG lfSch)
  im : p.lookup "if_clear" = some (memoClearG imSch)
  fm : p.lookup "fm_clear" = some (memoClearG frSch)

theorem PendR.frameLo {m m' : Mem} {pend : Array PendingCheck} {C : List Word}
    (hf : MemFrame [] C m m') (hC : ∀ x ∈ C, x.toNat < 128) (h : PendR m pend) : PendR m' pend := by
  have hP : m'.arr64 PEND = m.arr64 PEND := hf.1 _ (by simp) (by decide)
  have hE : m'.arr64 EREC = m.arr64 EREC := hf.1 _ (by simp) (by decide)
  have hc : rdW (m'.arr64 CTL) 130 = rdW (m.arr64 CTL) 130 :=
    hf.2.1 130 (fun h' => by have := hC _ h'; simp at this)
  refine ⟨by simp only [pendCount, hc]; exact h.count, fun j hj => ?_⟩
  rw [← h.recs j hj]; simp only [decPend, hP, hE]

theorem LoopR.of_lo {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState} {vis : Word}
    {fe : IFEnv} {pend : Array PendingCheck} {ds : Array IDeclaration} {C : List Word}
    (h : LoopR dn m a vis fe pend ds) (hC' : CheckR dn m' a' vis fe) (hf : MemFrame [] C m m')
    (hC : ∀ x ∈ C, x.toNat < 128) : LoopR dn m' a' vis fe pend ds := by
  have h1 : m'.arr64 DECL = m.arr64 DECL := hf.1 _ (by simp) (by decide)
  have h2 : m'.arr64 DLP = m.arr64 DLP := hf.1 _ (by simp) (by decide)
  exact ⟨hC', h.pend.frameLo hf hC, by rw [h1, h2]; exact h.decls⟩

section bracket
variable (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration) (p : Prog)
  (hb : BracketProg p)
include hb

theorem flush_loop (n : Nat) (s₀ : St) (a₀ : AState) (vis : Word) (fe : IFEnv)
    (pend : Array PendingCheck) (hR : LoopR dn s₀.mem a₀ vis fe pend ds) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "flush_caches" []
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok flushCaches a₀ ∧
      LoopR dn s'.mem (AM.st flushCaches a₀) vis fe pend ds; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hok, hC⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (flushCaches_refinesC p hb.fl a₀ n s₀ dn vis fe hR.check)
  obtain ⟨-, -, hm⟩ := M.of_run (P := fun s => s = s₀) hs hrun (flushCaches_spec p hb.fl n s₀)
  subst hs
  exact ⟨hloc, hok, hR.of_lo hC (by rw [hm]; exact flushMem_frame _) flushCtl_lt⟩

theorem enter_loop (n : Nat) (s₀ : St) (a₀ : AState) (vis : Word) (fe : IFEnv)
    (pend : Array PendingCheck) (hR : LoopR dn s₀.mem a₀ vis fe pend ds) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "scratch_enter" []
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok enterScratch a₀ ∧
      LoopR dn s'.mem (AM.st enterScratch a₀) vis fe pend ds; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hok, hC⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (scratchEnter_refinesC p hb.se hb.sr hb.bm hb.lf hb.im hb.fm a₀ n s₀ dn vis fe hR.check)
  obtain ⟨-, -, -, -, -, -, -, hm⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (scratchEnter_spec p hb.se hb.sr hb.bm hb.lf hb.im hb.fm n s₀)
  subst hs
  exact ⟨hloc, hok, hR.of_lo hC (by rw [hm]; exact enterMem_frame _)
    (fun x h => Nat.lt_trans (resetCtl_lt x h) (by decide))⟩

theorem drop_loop (n : Nat) (s₀ : St) (a₀ : AState) (vis : Word) (fe : IFEnv)
    (pend : Array PendingCheck) (hR : LoopR dn s₀.mem a₀ vis fe pend ds) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "scratch_drop" []
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok dropScratch a₀ ∧
      LoopR dn s'.mem (AM.st dropScratch a₀) vis fe pend ds; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hok, hC⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (scratchDrop_refinesC p hb.sd hb.sr hb.fl a₀ n s₀ dn vis fe hR.check)
  obtain ⟨-, -, -, -, hm⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (scratchDrop_spec p hb.sd hb.sr hb.fl n s₀)
  subst hs
  have hf : MemFrame [] (flushCtl ++ resetCtl) s.mem s'.mem := by
    rw [hm]
    exact ((flushMem_frame _).mono (by simp) (fun x h => List.mem_append_left _ h)).trans
      ((resetMem_frame _ 0).mono (by simp) (fun x h => List.mem_append_right _ h))
  refine ⟨hloc, hok, hR.of_lo hC hf fun x h => ?_⟩
  rcases List.mem_append.mp h with h | h
  · exact flushCtl_lt x h
  · exact Nat.lt_trans (resetCtl_lt x (List.mem_append_left _ h)) (by decide)

end bracket

theorem LoopR.restrict {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {pend : Array PendingCheck} {ds : Array IDeclaration}
    (h : LoopR dn m a vis fe pend ds) (v : Word) : LoopR dn m a v (fe.restrictTo v.toNat) pend ds :=
  ⟨⟨h.check.arena, h.check.core, h.check.pins, h.check.env.restrictTo v⟩, h.pend, h.decls⟩

theorem LoopR.unrestrict {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {v vis : Word}
    {fe : IFEnv} {k : Nat} {pend : Array PendingCheck} {ds : Array IDeclaration}
    (h : LoopR dn m a v (fe.restrictTo k) pend ds) (hv : fe.visibleBelow = vis.toNat) :
    LoopR dn m a vis fe pend ds := by
  have := h.restrict vis
  have e : (fe.restrictTo k).restrictTo vis.toNat = fe := by
    cases fe; simp only [IFEnv.restrictTo] at hv ⊢; rw [hv]
  rwa [e] at this

/-- Pending check `j` (a plain function, as `dsAt`). -/
def pdAt (pend : Array PendingCheck) (j : Word) : PendingCheck := pend.getD j.toNat default

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

/-- `installDeclStep` from its pieces (the `And` pin passed, the step went through). -/
theorem installDeclStep_ok (p : Nat × IFEnv × Array PendingCheck) (pd : IDeclaration) (a0 : AState)
    (h1 : AM.ok (andPinOk pd) a0) (hb : AM.res (andPinOk pd) a0 = true)
    (h2 : AM.ok (installStep mode pins p.1 p.2.1 p.2.2 pd) (AM.st (andPinOk pd) a0)) :
    AM.ok (installDeclStep mode pins p pd) a0 ∧ AM.st (installDeclStep mode pins p pd) a0 = AM.st (installStep mode pins p.1 p.2.1 p.2.2 pd) (AM.st (andPinOk pd) a0) ∧
    AM.res (installDeclStep mode pins p pd) a0 = .ok (p.1 + 1, (AM.res (installStep mode pins p.1 p.2.1 p.2.2 pd) (AM.st (andPinOk pd) a0)).1, (AM.res (installStep mode pins p.1 p.2.1 p.2.2 pd) (AM.st (andPinOk pd) a0)).2) := by
  have r1 := AM.run_of_ok _ _ h1
  rw [hb] at r1
  have r2 := AM.run_of_ok _ _ h2
  apply AM.of_run_ok
  simp only [installDeclStep, StateT.run] at r1 r2 ⊢
  rw [r1]; simp only; rw [r2]

/-- `installFold` past a successful step. -/
theorem installFold_cons (p p' : Nat × IFEnv × Array PendingCheck) (d : IDeclaration)
    (rest : List IDeclaration) (a0 : AState)
    (h1 : AM.ok (installDeclStep mode pins p d) a0)
    (hr : AM.res (installDeclStep mode pins p d) a0 = .ok p') :
    (installFold mode pins p (d :: rest)).run a0 =
      (installFold mode pins p' rest).run (AM.st (installDeclStep mode pins p d) a0) := by
  have r1 := AM.run_of_ok _ _ h1
  rw [hr] at r1
  simp only [installFold, StateT.run_bind, r1, exc_ok_bind]

theorem installFold_cons_ok (p p' : Nat × IFEnv × Array PendingCheck) (d : IDeclaration)
    (rest : List IDeclaration) (a0 : AState)
    (h1 : AM.ok (installDeclStep mode pins p d) a0)
    (hr : AM.res (installDeclStep mode pins p d) a0 = .ok p')
    (h2 : AM.ok (installFold mode pins p' rest) (AM.st (installDeclStep mode pins p d) a0)) :
    AM.ok (installFold mode pins p (d :: rest)) a0 ∧
    AM.st (installFold mode pins p (d :: rest)) a0 =
      AM.st (installFold mode pins p' rest) (AM.st (installDeclStep mode pins p d) a0) ∧
    AM.res (installFold mode pins p (d :: rest)) a0 =
      AM.res (installFold mode pins p' rest) (AM.st (installDeclStep mode pins p d) a0) := by
  have e := installFold_cons mode pins p p' d rest a0 h1 hr
  have r2 := AM.run_of_ok _ _ h2
  exact AM.of_run_ok _ _ _ _ (e.trans r2)

theorem installFold_nil_ok (p : Nat × IFEnv × Array PendingCheck) (a0 : AState) :
    AM.ok (installFold mode pins p []) a0 ∧ AM.st (installFold mode pins p []) a0 = a0 ∧
    AM.res (installFold mode pins p []) a0 = .ok p :=
  AM.of_run_ok _ _ _ _ rfl

theorem checkPending_ok (fe : IFEnv) (pc : PendingCheck) (a0 : AState)
    (h1 : AM.ok enterScratch a0)
    (h2 : AM.ok (checkValueGroup mode (fe.restrictTo pc.vis) pc.vg) (AM.st enterScratch a0))
    (h3 : AM.ok dropScratch
      (AM.st (checkValueGroup mode (fe.restrictTo pc.vis) pc.vg) (AM.st enterScratch a0))) :
    AM.ok (checkPending mode fe pc) a0 ∧ AM.st (checkPending mode fe pc) a0 =
      AM.st dropScratch
        (AM.st (checkValueGroup mode (fe.restrictTo pc.vis) pc.vg) (AM.st enterScratch a0)) := by
  have r1 := AM.run_of_ok _ _ h1
  have r2 := AM.run_of_ok _ _ h2
  have r3 := AM.run_of_ok _ _ h3
  have := AM.of_run_ok (checkPending mode fe pc) a0
    (AM.st dropScratch
      (AM.st (checkValueGroup mode (fe.restrictTo pc.vis) pc.vg) (AM.st enterScratch a0))) ()
    (by simp only [checkPending, StateT.run_bind, exc_ok_bind, r1, r2, r3])
  exact ⟨this.1, this.2.1⟩

theorem checkPendingList_cons_ok (fe : IFEnv) (pc : PendingCheck) (rest : List PendingCheck)
    (a0 : AState) (h1 : AM.ok (checkPending mode fe pc) a0)
    (h2 : AM.ok (checkPendingList mode fe rest) (AM.st (checkPending mode fe pc) a0)) :
    AM.ok (checkPendingList mode fe (pc :: rest)) a0 ∧
    AM.st (checkPendingList mode fe (pc :: rest)) a0 =
      AM.st (checkPendingList mode fe rest) (AM.st (checkPending mode fe pc) a0) ∧
    AM.res (checkPendingList mode fe (pc :: rest)) a0 =
      AM.res (checkPendingList mode fe rest) (AM.st (checkPending mode fe pc) a0) := by
  have r1 := AM.run_of_ok _ _ h1
  have r2 := AM.run_of_ok _ _ h2
  apply AM.of_run_ok
  simp only [checkPendingList, StateT.run] at r1 r2 ⊢
  rw [r1]; exact r2

theorem checkPendingList_nil_ok (fe : IFEnv) (a0 : AState) :
    AM.ok (checkPendingList mode fe []) a0 ∧ AM.st (checkPendingList mode fe []) a0 = a0 ∧
    AM.res (checkPendingList mode fe []) a0 = .ok () :=
  AM.of_run_ok _ _ _ _ rfl

theorem installThenCheck_ok (ds : Array IDeclaration) (a0 : AState) (k : Nat) (fe : IFEnv)
    (pend : Array PendingCheck)
    (h1 : AM.ok (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a0)
    (h2 : AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a0 = .ok (k, fe, pend))
    (h3 : AM.ok (checkPendingList mode fe pend.toList)
      (AM.st (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a0))
    (h4 : AM.res (checkPendingList mode fe pend.toList)
      (AM.st (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a0) = .ok ()) :
    AM.ok (installThenCheck mode pins ds) a0 ∧
    AM.st (installThenCheck mode pins ds) a0 = AM.st (checkPendingList mode fe pend.toList)
      (AM.st (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a0) ∧
    AM.res (installThenCheck mode pins ds) a0 = .ok fe := by
  have r1 := AM.run_of_ok _ _ h1
  have r3 := AM.run_of_ok _ _ h3
  rw [h2] at r1; rw [h4] at r3
  apply AM.of_run_ok
  simp only [installThenCheck, StateT.run_bind, r1, exc_ok_bind, r3]
  rfl

end twin

/-! ## Phase A's step: `install_step` -/


/-- `is_none(vis, v2)`: `installStep`'s `none` arm (`isNoneT`). -/
@[l_impl ConRon.Arena.installStep]
def isNoneL : FunDecl := lfn (vis, v2) locals (k, z) {
  k := 0;
  if vis <= v2 { k := v2 - vis };
  z := call promote_new(k, v2, 1);
  z := call scratch_drop();
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
  z := call scratch_drop();
  return 0
}

/-- `install_step(i, vis)`: `installStep` (the bracket, `installStepGo`, then one of the arms). -/
@[l_impl ConRon.Arena.installStep]
def installStepL : FunDecl := lfn (i, vis) locals (v2, f, g, z) {
  z := call flush_caches();
  z := call scratch_enter();
  (v2, f, g) := call install_step_go(i, vis);
  if f == 0 { z := call is_none(vis, v2) } else { z := call is_some(i, vis, v2, g) };
  return v2
}

/-- `install_decl_step(i, vis)`: `installDeclStep` (the `And` pin, then the step; a rejected pin
or a failing step is an `abort`). -/
@[l_impl ConRon.Arena.installDeclStep]
def installDeclStepL : FunDecl := lfn (i, vis) locals (ok, v) {
  ok := call and_pin_ok(i);
  if ok == 0 { abort };
  v := call install_step(i, vis);
  return v
}

/-- `install_fold_go(i, cnt, vis)`: `installFold` over records `i`‥`cnt - 1`. -/
@[l_impl ConRon.Arena.installFold]
def installFoldGoL : FunDecl := lfn (i, cnt, vis) locals (r) {
  if i == cnt { return vis };
  r := call install_fold_next(i, cnt, vis);
  return r
}

/-- `install_fold_next(i, cnt, vis)`: one step of `installFold` (`i < cnt`), then the rest. -/
@[l_impl ConRon.Arena.installFold]
def installFoldNextL : FunDecl := lfn (i, cnt, vis) locals (v, r) {
  v := call install_decl_step(i, vis);
  r := call install_fold_go(i + 1, cnt, v);
  return r
}

/-- `check_pending(j, vis)`: `checkPending` on pending check `j`, the environment seen at its
recorded view. -/
@[l_impl ConRon.Arena.checkPending]
def checkPendingL : FunDecl := lfn (j, vis) locals (g, v, z) {
  if 4611686018427387904 <= j { abort };
  z := call scratch_enter();
  g := PEND.u64[3 * j];
  v := PEND.u64[3 * j + 2];
  z := call check_value_group(v, g);
  z := call scratch_drop();
  return 0
}

/-- `check_pending_go(j, cnt, vis)`: `checkPendingList` over pending checks `j`‥`cnt - 1`. -/
@[l_impl ConRon.Arena.checkPendingList]
def checkPendingGoL : FunDecl := lfn (j, cnt, vis) locals (z) {
  if j == cnt { return 0 };
  z := call check_pending_next(j, cnt, vis);
  return 0
}

/-- `check_pending_next(j, cnt, vis)`: one pending check (`j < cnt`), then the rest. -/
@[l_impl ConRon.Arena.checkPendingList]
def checkPendingNextL : FunDecl := lfn (j, cnt, vis) locals (z) {
  if 4611686018427387904 <= j { abort };
  z := call check_pending(j, vis);
  z := call check_pending_go(j + 1, cnt, vis);
  return 0
}

/-- `install_then_check()`: phase A over the front's declaration records, then phase B; returns
the final view. **The declaration loop.** -/
def installThenCheckL : FunDecl := lfn () locals (cnt, v, c, z) {
  cnt := DECL.u64[0];
  v := call install_fold_go(0, cnt, 0);
  c := CTL.u64[130];
  z := call check_pending_go(0, c, v);
  return v
}

section skel
variable (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
  (ds : Array IDeclaration) (p : Prog)

theorem isNone_refines (hb : BracketProg p) (hp : p.lookup "is_none" = some isNoneL) (n : Nat) (s₀ : St) (a₀ : AState)
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
        (drop_loop dn ds p hb n · (AM.st (promoteNew PMemo.empty coreWalkFuel
          (fe'.visibleBelow - vis.toNat) fe') a₀) v2
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

theorem isSome_refines (hb : BracketProg p) (hpp : p.lookup "pend_push" = some pendPushL)
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
        (drop_loop dn ds p hb n · (AM.st (promoteNew (AM.res (promoteVG PMemo.empty coreWalkFuel vg) a₀).1 coreWalkFuel (fe'.visibleBelow - vis.toNat) fe') (AM.st (promoteVG PMemo.empty coreWalkFuel vg) a₀)) v2 (AM.res (promoteNew (AM.res (promoteVG PMemo.empty coreWalkFuel vg) a₀).1 coreWalkFuel (fe'.visibleBelow - vis.toNat) fe') (AM.st (promoteVG PMemo.empty coreWalkFuel vg) a₀)).2 (pend.push ⟨(AM.res (promoteVG PMemo.empty coreWalkFuel vg) a₀).2, i.toNat, vis.toNat⟩))] <;>
      finish [isSomeT]

/-- `install_step`, stated over the pieces of `installStep` (`installStep_ok` assembles them). -/
theorem installStep_pieces (hb : BracketProg p) (hpp : p.lookup "pend_push" = some pendPushL)
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
        (flush_loop dn ds p hb n · a₀ vis fe pend),
        (enter_loop dn ds p hb n · (AM.st flushCaches a₀) vis fe pend),
        (installStepGo_spec mode pins dn ds p n · (AM.st enterScratch (AM.st flushCaches a₀)) · fe pend · ·),
        (isNone_refines dn ds p hb hpn n · (AM.st (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀))) · · (AM.res (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀))).1 pend),
        (isSome_refines dn ds p hb hpp hps n · (AM.st (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀))) · · · · (AM.res (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀))).1 pend ((AM.res (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀))).2.getD default))] <;>
      -- the view `vis` is read after three calls: four `LocEq` hops (depth, not search)
      finish (gen := 20) [vgOut]

/-- **`install_step` refines `installStep`** (from the stub specs). -/
@[refines ConRon.Arena.installStep]
theorem installStep_refines (hb : BracketProg p) (hpp : p.lookup "pend_push" = some pendPushL)
    (hpn : p.lookup "is_none" = some isNoneL) (hps : p.lookup "is_some" = some isSomeL)
    (hp : p.lookup "install_step" = some installStepL) (n : Nat) (s₀ : St) (a₀ : AState)
    (i vis : Word) (fe : IFEnv) (pend : Array PendingCheck) (hi : i.toNat < ds.size)
    (hR : LoopR dn s₀.mem a₀ vis fe pend ds) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_step" [i, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (installStep mode pins i.toNat fe pend (dsAt ds i)) a₀ ∧
      LoopR dn s'.mem (AM.st (installStep mode pins i.toNat fe pend (dsAt ds i)) a₀) (r.headD 0) (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) a₀).1 (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) a₀).2 ds; ⊤⦄ := by
  have hv := hR.vis
  refine triple_post (installStep_pieces mode pins dn ds p hb hpp hpn hps hp n s₀ a₀ i vis fe pend hi hR)
    fun r s' ⟨hl, h1, h2, h3, h4, h5⟩ => ?_
  rw [← hv] at h4 h5
  obtain ⟨o, st, rs⟩ := installStep_ok mode pins i.toNat fe pend (dsAt ds i) a₀ h1 h2 h3 h4
  exact ⟨hl, o, by rw [st, rs]; exact h5⟩

/-- **`install_decl_step` refines `installDeclStep`**: a returning run is the twin's `.ok` with
the position advanced. -/
@[refines ConRon.Arena.installDeclStep]
theorem installDeclStep_refines (hb : BracketProg p) (hpp : p.lookup "pend_push" = some pendPushL)
    (hpn : p.lookup "is_none" = some isNoneL) (hps : p.lookup "is_some" = some isSomeL)
    (hpi : p.lookup "install_step" = some installStepL)
    (hp : p.lookup "install_decl_step" = some installDeclStepL) (n : Nat) (s₀ : St) (a₀ : AState)
    (i vis : Word) (fe : IFEnv) (pend : Array PendingCheck) (hi : i.toNat < ds.size)
    (hR : LoopR dn s₀.mem a₀ vis fe pend ds) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_decl_step" [i, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (installDeclStep mode pins (i.toNat, fe, pend) (dsAt ds i)) a₀ ∧
      AM.res (installDeclStep mode pins (i.toNat, fe, pend) (dsAt ds i)) a₀ = .ok (i.toNat + 1, (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).1, (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).2) ∧
      LoopR dn s'.mem (AM.st (installDeclStep mode pins (i.toNat, fe, pend) (dsAt ds i)) a₀) (r.headD 0) (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).1 (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).2 ds; ⊤⦄ := by
  have hok := installDeclStep_ok mode pins (i.toNat, fe, pend) (dsAt ds i) a₀
  rw [invoke_eq _ hp]
  simp only [callFn, installDeclStepL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        (andPinOk_spec dn ds p n · a₀ vis fe pend · ·),
        (installStep_refines mode pins dn ds p hb hpp hpn hps hpi n · (AM.st (andPinOk (dsAt ds i)) a₀) · · fe pend ·)] <;>
      finish

theorem drop_cons_dsAt (ds : Array IDeclaration) (i : Word) (hi : i.toNat < ds.size)
    (h1 : (i + 1).toNat = i.toNat + 1) :
    ds.toList.drop i.toNat = dsAt ds i :: ds.toList.drop (i + 1).toNat := by
  rw [h1, List.drop_eq_getElem_cons (by simpa using hi)]
  simp [dsAt, hi]


/-- What `install_fold_go` from record `k` ends with: phase A's fold from `(k, fe, pend)` over the
records from `k` succeeds with every record installed, related to the memory `m` at view `v`. -/
def FoldPost (m : Mem) (a : AState) (v : Word) (k : Nat) (fe : IFEnv) (pend : Array PendingCheck) :
    Prop :=
  AM.ok (installFold mode pins (k, fe, pend) (ds.toList.drop k)) a ∧
    FoldOut dn m (AM.st (installFold mode pins (k, fe, pend) (ds.toList.drop k)) a) v ds
      (AM.res (installFold mode pins (k, fe, pend) (ds.toList.drop k)) a)

/-- `install_fold_go`'s spec at fuel `n`. -/
def FoldGoSpec (n : Nat) : Prop :=
  ∀ (s₀ : St) (a₀ : AState) (i cnt vis : Word) (fe : IFEnv) (pend : Array PendingCheck),
    i.toNat ≤ ds.size → cnt.toNat = ds.size → LoopR dn s₀.mem a₀ vis fe pend ds →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_fold_go" [i, cnt, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ FoldPost mode pins dn ds s'.mem a₀ (r.headD 0) i.toNat fe pend; ⊤⦄

/-- `install_fold_next`'s spec at fuel `n`. -/
def FoldNextSpec (n : Nat) : Prop :=
  ∀ (s₀ : St) (a₀ : AState) (i cnt vis : Word) (fe : IFEnv) (pend : Array PendingCheck),
    i.toNat < ds.size → cnt.toNat = ds.size → LoopR dn s₀.mem a₀ vis fe pend ds →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_fold_next" [i, cnt, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ FoldPost mode pins dn ds s'.mem a₀ (r.headD 0) i.toNat fe pend; ⊤⦄

section fold
variable (hpp : p.lookup "pend_push" = some pendPushL)
    (hpn : p.lookup "is_none" = some isNoneL) (hps : p.lookup "is_some" = some isSomeL)
    (hpi : p.lookup "install_step" = some installStepL)
    (hpd : p.lookup "install_decl_step" = some installDeclStepL)
    (hpg : p.lookup "install_fold_go" = some installFoldGoL)
    (hpx : p.lookup "install_fold_next" = some installFoldNextL) (hsz : ds.size < 2 ^ 63)
    (hb : BracketProg p)
include hpp hpn hps hpi hpd hpg hpx hsz hb

theorem foldGo_step (n : Nat) (ih : FoldNextSpec mode pins dn ds p n) :
    FoldGoSpec mode pins dn ds p (n + 1) := by
  unfold FoldNextSpec at ih
  intro s₀ a₀ i cnt vis fe pend hi hc hR
  have hlt : i ≠ cnt → i.toNat < ds.size := fun h => by
    have : i.toNat ≠ cnt.toNat := fun e => h (UInt64.toNat_inj.mp e)
    omega
  have hnil : i = cnt → FoldPost mode pins dn ds s₀.mem a₀ vis i.toNat fe pend := fun h => by
    have e : ds.toList.drop i.toNat = [] := by simp [h, hc]
    have := installFold_nil_ok mode pins (i.toNat, fe, pend) a₀
    simp only [FoldPost, e]
    refine ⟨this.1, ?_⟩
    rw [this.2.1, this.2.2]; exact ⟨by rw [h, hc], hR⟩
  have hmem : ∀ m : Mem, m = s₀.mem → FoldPost mode pins dn ds s₀.mem a₀ vis i.toNat fe pend →
      FoldPost mode pins dn ds m a₀ vis i.toNat fe pend := fun m h p => h ▸ p
  have hsz' : i = cnt → i.toNat = ds.size := fun h => by rw [h, hc]
  rw [invoke_eq _ hpg]
  simp only [callFn, installFoldGoL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, (ih · a₀ · · · fe pend)] <;>
    finish

theorem foldNext_step (n : Nat) (ih : FoldGoSpec mode pins dn ds p n) :
    FoldNextSpec mode pins dn ds p (n + 1) := by
  unfold FoldGoSpec at ih
  intro s₀ a₀ i cnt vis fe pend hi hc hR
  have h1 : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have h2 : (i + 1).toNat ≤ ds.size := by omega
  have hcons : ∀ (m : Mem) (v j : Word), j = i + 1 → AM.ok (installDeclStep mode pins (i.toNat, fe, pend) (dsAt ds i)) a₀ → AM.res (installDeclStep mode pins (i.toNat, fe, pend) (dsAt ds i)) a₀ = .ok (i.toNat + 1, (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).1, (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).2) →
      FoldPost mode pins dn ds m (AM.st (installDeclStep mode pins (i.toNat, fe, pend) (dsAt ds i)) a₀) v j.toNat (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).1
        (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).2 →
      FoldPost mode pins dn ds m a₀ v i.toNat fe pend := by
    intro m v j hj hok hres hp
    rw [hj, h1] at hp
    obtain ⟨hp1, hp2⟩ := hp
    have e := drop_cons_dsAt ds i hi h1
    rw [h1] at e
    have := installFold_cons_ok mode pins (i.toNat, fe, pend) (i.toNat + 1, (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).1, (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).2) (dsAt ds i)
      (ds.toList.drop (i.toNat + 1)) a₀ hok hres hp1
    refine ⟨?_, ?_⟩
    · rw [e]; exact this.1
    · rw [e, this.2.1, this.2.2]; exact hp2
  have hloc : ∀ (s : St) (m : Mem) (rs : List Word), LocEq s { mem := m, loc := Locals.init [i, cnt, vis] } →
      (s.setLocs [3] rs).loc 0 = i ∧ (s.setLocs [3] rs).loc 1 = cnt := by
    intro s m rs h; grind [lang_grind]
  have hpre : ∀ (s : St) (rs : List Word) (A : AState) (fe' : IFEnv) (pend' : Array PendingCheck),
      LoopR dn s.mem A (rs.headD 0) fe' pend' ds →
      LoopR dn (s.setLocs [3] rs).mem A ((s.setLocs [3] rs).loc 3) fe' pend' ds := by
    intro s rs A fe' pend' h; simpa [St.setLocs, St.setLoc] using h
  have hmemL : ∀ (s : St) (rs : List Word), (s.setLocs [4] rs).mem = s.mem := by
    intro s rs; simp [St.setLocs, St.setLoc]
  have hret : ∀ (s : St) (rs : List Word),
      (Sig.ret [(s.setLocs [4] rs).loc 4]).retVal.headD 0 = rs.headD 0 := by
    intro s rs; simp [St.setLocs, St.setLoc, Sig.retVal, Sig.retOr]
  have inner : ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "install_fold_next" [i, cnt, vis]
      ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (installDeclStep mode pins (i.toNat, fe, pend) (dsAt ds i)) a₀ ∧ AM.res (installDeclStep mode pins (i.toNat, fe, pend) (dsAt ds i)) a₀ = .ok (i.toNat + 1, (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).1, (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).2) ∧
        FoldPost mode pins dn ds s'.mem (AM.st (installDeclStep mode pins (i.toNat, fe, pend) (dsAt ds i)) a₀) (r.headD 0) (i + 1).toNat
          (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).1 (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).2; ⊤⦄ := by
    rw [invoke_eq _ hpx]
    simp only [callFn, installFoldNextL]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, Locals.init,
        (installDeclStep_refines mode pins dn ds p hb hpp hpn hps hpi hpd n · a₀ · · fe pend ·),
        (ih · (AM.st (installDeclStep mode pins (i.toNat, fe, pend) (dsAt ds i)) a₀) · · · (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).1 (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).2)] <;>
      finish
  exact triple_post inner fun r s' ⟨h0, h1, h2, h3⟩ => ⟨h0, hcons _ _ (i + 1) rfl h1 h2 h3⟩

/-- **`install_fold_go` refines `installFold`** from record `i` on (and `install_fold_next`
for one step and the rest). -/
@[refines ConRon.Arena.installFold]
theorem installFoldGo_refines (n : Nat) :
    FoldGoSpec mode pins dn ds p n ∧ FoldNextSpec mode pins dn ds p n := by
  induction n with
  | zero =>
    constructor
    · intro s₀ a₀ i cnt vis fe pend _ _ _; rw [invoke_eq _ hpg]; simp only [callFn]
      vcgen [exec] <;> grind
    · intro s₀ a₀ i cnt vis fe pend _ _ _; rw [invoke_eq _ hpx]; simp only [callFn]
      vcgen [exec] <;> grind
  | succ n ih =>
    exact ⟨foldGo_step mode pins dn ds p hpp hpn hps hpi hpd hpg hpx hsz hb n ih.2,
      foldNext_step mode pins dn ds p hpp hpn hps hpi hpd hpg hpx hsz hb n ih.1⟩

end fold

theorem pend_words (m : Mem) (pend : Array PendingCheck) (hP : PendR m pend) (j : Word)
    (hj : j.toNat < pend.size) (hj62 : j.toNat < 2 ^ 62) :
    (∀ (h : (3 * j).toNat < (m.arr64 PEND).size),
      decVG (m.arr64 EREC) ((m.arr64 PEND)[(3 * j).toNat]).toNat = some (pdAt pend j).vg) ∧
    (∀ (h : (3 * j + 2).toNat < (m.arr64 PEND).size),
      ((m.arr64 PEND)[(3 * j + 2).toNat]).toNat = (pdAt pend j).vis) := by
  have hr := hP.recs j.toNat hj
  have e0 : (3 * j).toNat = 3 * j.toNat := by rw [UInt64.toNat_mul]; simp; omega
  have e2 : (3 * j + 2).toNat = 3 * j.toNat + 2 := by rw [UInt64.toNat_add, e0]; simp; omega
  have hpd : pdAt pend j = pend[j.toNat] := by simp [pdAt, hj]
  simp only [decPend, nat?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.map_eq_some_iff] at hr
  obtain ⟨g, ⟨w0, hw0, rfl⟩, vg, hvg, x, ⟨w1, hw1, rfl⟩, y, ⟨w2, hw2, rfl⟩, he⟩ := hr
  rw [hpd, ← Option.some.inj he]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [e0] at h ⊢
    have : (m.arr64 PEND)[3 * j.toNat] = w0 := by simpa [h] using hw0
    rw [this]; exact hvg
  · simp only [e2] at h ⊢
    have : (m.arr64 PEND)[3 * j.toNat + 2] = w2 := by simpa [h] using hw2
    rw [this]

/-- **`check_pending` refines `checkPending`** (from the stub specs). -/
@[refines ConRon.Arena.checkPending]
theorem checkPending_refines (hb : BracketProg p) (hp : p.lookup "check_pending" = some checkPendingL) (n : Nat)
    (s₀ : St) (a₀ : AState) (j vis : Word) (fe : IFEnv) (pend : Array PendingCheck)
    (hj : j.toNat < pend.size) (hR : LoopR dn s₀.mem a₀ vis fe pend ds) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_pending" [j, vis]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (checkPending mode fe (pdAt pend j)) a₀ ∧
      LoopR dn s'.mem (AM.st (checkPending mode fe (pdAt pend j)) a₀) vis fe pend ds; ⊤⦄ := by
  have hvB := hR.vis
  have hres : ∀ m a, LoopR dn m a vis fe pend ds → ∀ v : Word,
      LoopR dn m a v (fe.restrictTo v.toNat) pend ds := fun m a h v => h.restrict v
  have hunr : ∀ m a (v : Word), LoopR dn m a v (fe.restrictTo (pdAt pend j).vis) pend ds →
      LoopR dn m a vis fe pend ds := fun m a v h => h.unrestrict hvB
  have hw : ∀ (m : Mem) (a : AState), LoopR dn m a vis fe pend ds → j.toNat < 2 ^ 62 →
      (∀ (h : (3 * j).toNat < (m.arr64 PEND).size),
        decVG (m.arr64 EREC) ((m.arr64 PEND)[(3 * j).toNat]).toNat = some (pdAt pend j).vg) ∧
      (∀ (h : (3 * j + 2).toNat < (m.arr64 PEND).size),
        ((m.arr64 PEND)[(3 * j + 2).toNat]).toNat = (pdAt pend j).vis) :=
    fun m a h h62 => pend_words m pend h.pend j hj h62
  have inner : ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_pending" [j, vis]
      ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok enterScratch a₀ ∧ AM.ok (checkValueGroup mode (fe.restrictTo (pdAt pend j).vis) (pdAt pend j).vg) (AM.st enterScratch a₀) ∧
        AM.ok dropScratch (AM.st (checkValueGroup mode (fe.restrictTo (pdAt pend j).vis) (pdAt pend j).vg) (AM.st enterScratch a₀)) ∧ LoopR dn s'.mem (AM.st dropScratch (AM.st (checkValueGroup mode (fe.restrictTo (pdAt pend j).vis) (pdAt pend j).vg) (AM.st enterScratch a₀))) vis fe pend ds; ⊤⦄ := by
    rw [invoke_eq _ hp]
    simp only [callFn, checkPendingL]
    cases n with
    | zero => vcgen [exec] <;> grind
    | succ n =>
      sym only [lang_grind, arena_grind] =>
        vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
          (enter_loop dn ds p hb n · a₀ vis fe pend),
          (checkValueGroup_spec mode dn ds p n · (AM.st enterScratch a₀) · (fe.restrictTo (pdAt pend j).vis) pend · (pdAt pend j).vg),
          (drop_loop dn ds p hb n · (AM.st (checkValueGroup mode (fe.restrictTo (pdAt pend j).vis) (pdAt pend j).vg) (AM.st enterScratch a₀)) vis fe pend)] <;>
        finish
  exact triple_post inner fun r s' ⟨h0, h1, h2, h3, h4⟩ => by
    obtain ⟨o, st⟩ := checkPending_ok mode fe (pdAt pend j) a₀ h1 h2 h3
    exact ⟨h0, o, by rw [st]; exact h4⟩

section phaseB
variable (fe : IFEnv) (pend : Array PendingCheck)

/-- What `check_pending_go` from check `k` ends with: phase B over the checks from `k` accepts,
related to the memory `m` at view `v`. -/
def PendPost (m : Mem) (a : AState) (v : Word) (k : Nat) : Prop :=
  AM.ok (checkPendingList mode fe (pend.toList.drop k)) a ∧
    AM.res (checkPendingList mode fe (pend.toList.drop k)) a = .ok () ∧
    LoopR dn m (AM.st (checkPendingList mode fe (pend.toList.drop k)) a) v fe pend ds

def CPGoSpec (n : Nat) : Prop :=
  ∀ (s₀ : St) (a₀ : AState) (j cnt vis : Word), j.toNat ≤ pend.size → cnt.toNat = pend.size →
    LoopR dn s₀.mem a₀ vis fe pend ds →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_pending_go" [j, cnt, vis]
    ⦃fun _ s' => LocEq s' s₀ ∧ PendPost mode dn ds fe pend s'.mem a₀ vis j.toNat; ⊤⦄

def CPNextSpec (n : Nat) : Prop :=
  ∀ (s₀ : St) (a₀ : AState) (j cnt vis : Word), j.toNat < pend.size → cnt.toNat = pend.size →
    LoopR dn s₀.mem a₀ vis fe pend ds →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_pending_next" [j, cnt, vis]
    ⦃fun _ s' => LocEq s' s₀ ∧ PendPost mode dn ds fe pend s'.mem a₀ vis j.toNat; ⊤⦄

theorem drop_cons_pdAt (j : Word) (hj : j.toNat < pend.size) (h1 : (j + 1).toNat = j.toNat + 1) :
    pend.toList.drop j.toNat = pdAt pend j :: pend.toList.drop (j + 1).toNat := by
  rw [h1, List.drop_eq_getElem_cons (by simpa using hj)]
  simp [pdAt, hj]

section cp
variable (hpc : p.lookup "check_pending" = some checkPendingL)
    (hpg : p.lookup "check_pending_go" = some checkPendingGoL)
    (hpx : p.lookup "check_pending_next" = some checkPendingNextL) (hb : BracketProg p)
include hpc hpg hpx hb

theorem cpGo_step (n : Nat) (ih : CPNextSpec mode dn ds p fe pend n) :
    CPGoSpec mode dn ds p fe pend (n + 1) := by
  unfold CPNextSpec at ih
  intro s₀ a₀ j cnt vis hj hc hR
  have hlt : j ≠ cnt → j.toNat < pend.size := fun h => by
    have : j.toNat ≠ cnt.toNat := fun e => h (UInt64.toNat_inj.mp e)
    omega
  have hnil : j = cnt → PendPost mode dn ds fe pend s₀.mem a₀ vis j.toNat := fun h => by
    have e : pend.toList.drop j.toNat = [] := by simp [h, hc]
    have := checkPendingList_nil_ok mode fe a₀
    simp only [PendPost, e]
    exact ⟨this.1, this.2.2, by rw [this.2.1]; exact hR⟩
  rw [invoke_eq _ hpg]
  simp only [callFn, checkPendingGoL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, (ih · a₀ · · ·)] <;>
    finish

theorem cpNext_step (n : Nat) (ih : CPGoSpec mode dn ds p fe pend n) :
    CPNextSpec mode dn ds p fe pend (n + 1) := by
  unfold CPGoSpec at ih
  intro s₀ a₀ j cnt vis hj hc hR
  have h1 : j.toNat < 2 ^ 62 → (j + 1).toNat = j.toNat + 1 := by
    intro h; rw [UInt64.toNat_add]; simp; omega
  have hcons : j.toNat < 2 ^ 62 → ∀ (m : Mem) (k : Word), k = j + 1 → AM.ok (checkPending mode fe (pdAt pend j)) a₀ →
      PendPost mode dn ds fe pend m (AM.st (checkPending mode fe (pdAt pend j)) a₀) vis k.toNat →
      PendPost mode dn ds fe pend m a₀ vis j.toNat := by
    intro h62 m k hk hok hp
    rw [hk] at hp
    obtain ⟨hp1, hp2, hp3⟩ := hp
    have e := drop_cons_pdAt pend j hj (h1 h62)
    have := checkPendingList_cons_ok mode fe (pdAt pend j) (pend.toList.drop (j + 1).toNat) a₀ hok hp1
    refine ⟨?_, ?_, ?_⟩
    · rw [e]; exact this.1
    · rw [e, this.2.2]; exact hp2
    · rw [e, this.2.1]; exact hp3
  have inner : ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check_pending_next" [j, cnt, vis]
      ⦃fun _ s' => LocEq s' s₀ ∧ j.toNat < 2 ^ 62 ∧ AM.ok (checkPending mode fe (pdAt pend j)) a₀ ∧
        PendPost mode dn ds fe pend s'.mem (AM.st (checkPending mode fe (pdAt pend j)) a₀) vis (j + 1).toNat; ⊤⦄ := by
    have hloc : ∀ (s : St) (m : Mem) (rs : List Word),
        LocEq s { mem := m, loc := Locals.init [j, cnt, vis] } →
        (s.setLocs [3] rs).loc 0 = j ∧ (s.setLocs [3] rs).loc 1 = cnt ∧
          (s.setLocs [3] rs).loc 2 = vis := by
      intro s m rs h; grind [lang_grind]
    have hmemL : ∀ (s : St) (rs : List Word), (s.setLocs [3] rs).mem = s.mem := by
      intro s rs; simp [St.setLocs, St.setLoc]
    rw [invoke_eq _ hpx]
    simp only [callFn, checkPendingNextL]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        (checkPending_refines mode dn ds p hb hpc n · a₀ · · fe pend ·),
        (ih · (AM.st (checkPending mode fe (pdAt pend j)) a₀) · · ·)] <;>
      finish
  exact triple_post inner fun r s' ⟨h0, h62, h2, h3⟩ => ⟨h0, hcons h62 _ (j + 1) rfl h2 h3⟩

/-- **`check_pending_go` refines `checkPendingList`** from check `j` on (and
`check_pending_next` for one check and the rest). -/
@[refines ConRon.Arena.checkPendingList]
theorem checkPendingGo_refines (n : Nat) :
    CPGoSpec mode dn ds p fe pend n ∧ CPNextSpec mode dn ds p fe pend n := by
  induction n with
  | zero =>
    constructor
    · intro s₀ a₀ j cnt vis _ _ _; rw [invoke_eq _ hpg]; simp only [callFn]
      vcgen [exec] <;> grind
    · intro s₀ a₀ j cnt vis _ _ _; rw [invoke_eq _ hpx]; simp only [callFn]
      vcgen [exec] <;> grind
  | succ n ih =>
    exact ⟨cpGo_step mode dn ds p fe pend hpc hpg hpx hb n ih.2,
      cpNext_step mode dn ds p fe pend hpc hpg hpx hb n ih.1⟩

end cp
end phaseB

/-- **`install_then_check` refines `installThenCheck`** (from the stub specs): a returning run
is the twin's accepting fold, its environment related at the returned view. -/
theorem installThenCheck_refines (hb : BracketProg p) (hpp : p.lookup "pend_push" = some pendPushL)
    (hpn : p.lookup "is_none" = some isNoneL) (hps : p.lookup "is_some" = some isSomeL)
    (hpi : p.lookup "install_step" = some installStepL)
    (hpd : p.lookup "install_decl_step" = some installDeclStepL)
    (hpg : p.lookup "install_fold_go" = some installFoldGoL)
    (hpx : p.lookup "install_fold_next" = some installFoldNextL)
    (hpc : p.lookup "check_pending" = some checkPendingL)
    (hpcg : p.lookup "check_pending_go" = some checkPendingGoL)
    (hpcx : p.lookup "check_pending_next" = some checkPendingNextL)
    (hp : p.lookup "install_then_check" = some installThenCheckL) (n : Nat) (s₀ : St) (a₀ : AState)
    (hR : LoopR dn s₀.mem a₀ 0 (mkIFEnv IEnv.empty) #[] ds) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_then_check" []
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (installThenCheck mode pins ds) a₀ ∧ AM.res (installThenCheck mode pins ds) a₀ = .ok (foldFe (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀)) ∧
      LoopR dn s'.mem (AM.st (installThenCheck mode pins ds) a₀) (r.headD 0) (foldFe (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀)) (foldPend (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀)) ds; ⊤⦄ := by
  have hsz : ds.size < 2 ^ 63 := by have := hR.decls.dsize; have := hR.decls.room; omega
  have hcnt : ∀ (h : 0 < (s₀.mem.arr64 DECL).size), ((s₀.mem.arr64 DECL)[0]).toNat = ds.size := by
    intro h; have := hR.decls.count; simpa [h] using this
  have hc : ∀ (m : Mem) (a : AState) (v : Word) (fe : IFEnv) (pend : Array PendingCheck),
      LoopR dn m a v fe pend ds → ∀ (h : 130 < (m.arr64 CTL).size),
      ((m.arr64 CTL)[130]).toNat = pend.size := by
    intro m a v fe pend h h1
    have := h.pend.count; simp only [pendCount] at this; rwa [rdW_eq _ _ 130 rfl h1] at this
  have hcB : ∀ (m : Mem) (a : AState) (v : Word), FoldOut dn m a v ds (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀) →
      ∀ (h : 130 < (m.arr64 CTL).size), ((m.arr64 CTL)[130]).toNat = (foldPend (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀)).size :=
    fun m a v h h1 => hc m a v _ _ (FoldOut.eq h).2 h1
  have hLB : ∀ (m : Mem) (a : AState) (v : Word), FoldOut dn m a v ds (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀) →
      (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀) = .ok (ds.size, foldFe (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀), foldPend (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀)) ∧ LoopR dn m a v (foldFe (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀)) (foldPend (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀)) ds :=
    fun m a v h => FoldOut.eq h
  have hFP : ∀ (m : Mem) (v : Word), FoldPost mode pins dn ds m a₀ v (UInt64.toNat 0)
      (mkIFEnv IEnv.empty) #[] → AM.ok (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀ ∧ FoldOut dn m (AM.st (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀) v ds (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀) := by
    intro m v h; simpa [FoldPost] using h
  have inner : ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_then_check" []
      ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀ ∧ (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀) = .ok (ds.size, foldFe (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀), foldPend (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀)) ∧
        PendPost mode dn ds (foldFe (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀)) (foldPend (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀)) s'.mem (AM.st (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀) (r.headD 0) 0; ⊤⦄ := by
    rw [invoke_eq _ hp]
    simp only [callFn, installThenCheckL]
    cases n with
    | zero => vcgen [exec] <;> grind
    | succ n =>
      sym only [lang_grind, arena_grind] =>
        vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
          ((installFoldGo_refines mode pins dn ds p hpp hpn hps hpi hpd hpg hpx hsz hb n).1 · a₀ · · ·
            (mkIFEnv IEnv.empty) #[]),
          ((checkPendingGo_refines mode dn ds p (foldFe (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀)) (foldPend (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀)) hpc hpcg hpcx hb n).1 ·
            (AM.st (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀) · · ·)] <;>
        finish
  exact triple_post inner fun r s' ⟨h0, h1, h2, h3⟩ => by
    obtain ⟨o, st, rs⟩ := installThenCheck_ok mode pins ds a₀ _ _ _ h1 h2 h3.1 h3.2.1
    exact ⟨h0, o, rs, by rw [st]; exact h3.2.2⟩

end skel

end L.Arena

