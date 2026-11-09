module

public import ConAgua.Checker.PhaseBReads
public import ConAgua.Arena.FreezeRel
public import ConAgua.Checker.JobsStart
import ConAgua.Checker.RomProg0
import ConAgua.Rom.Subst
import ConRon.Bridge.Checker.Pool
import ConRon.Bridge.Checker.Hyp
import ConRon.Bridge.Checker.Install
import ConRon.Bridge.Inductives.Decl
import ConRon.Bridge.Stages
import ConAgua.Checker.LoopProgTac
public import ConAgua.Final.Statement
meta import ConAgua.Checker.PhaseBReads
meta import ConAgua.Arena.FreezeRel
meta import ConAgua.Checker.LoopProgTac
meta import ConAgua.Final.Statement
import ConAgua.L.Blocks
import all ConAgua.Checker.Entry

@[expose] public section

/-!
# The jobs of the sequential driver's entry 2, in L (lane parmode, stage 3 of lane ronsync2)

docs/design/parmode.md, "Redesign". The driver's entry 2 (`ca_check_seq`) runs `check` with the mode
word `2` on a memory `w` that is phase A's memory `m` except in the arrays the jobs never name
(`OUT`, the header `HDRF`, the seed `CTLF`, the byte arrays) and in the globals. `check_b` flushes
the core caches and runs `check_jobs(0, k)`. Then:

* `flushMem_agree`: the flush keeps an agreement that covers `CTL`;
* `poolHyps_of_phaseA`: the twin's side of the pool's induction (`PoolHyps`) at an accepting
  phase A, as con-ron's `pooledAccepts_bridge` assembles it;
* `checkJobs_seq`: a returning `check_jobs(0, k)` on a memory that agrees with the flushed `m` is
  the twin's `checkJobList` over every record accepting from the index state's worker
  (`L/Agree.lean`'s non-interference over `checkerProg_phaseBReads`, then `checkJobsLoop_chain`
  and `pool_twin` with one worker over `JobRel`).
-/

set_option experimental.vcgen true

open ConRon.Arena ConRon.Bridge
open Std.WP
open scoped Lean.Order

namespace L.Checker

open L L.Arena

universe w

-- `check_b` (`checkBL`, `ConAgua/Checker/Entry.lean`) returns the literal `ACCEPT`.
example : (71757147230292 : Word) = ConAgua.Final.ACCEPT := rfl

/-- The arrays phase B's loop may name: every word array but `OUT`, `HDRF`, `CTLF`. -/
abbrev phaseBS : TieredArray → Bool := phaseBPa

theorem checkerProg_lookup_check_b : checkerProg.lookup "check_b" = some checkBL := by chk_lk
theorem checkerProg_lookup_check' : checkerProg.lookup "check" = some checkL := by chk_lk

/-! ## The flush keeps an agreement -/

theorem mclearG_agree {S : TieredArray → Bool} {S8 : ArrId → Bool} {m₁ m₂ : Mem}
    (h : Agree S S8 m₁ m₂) (hc : S CTL = true) (Sch : MemoSch) :
    Agree S S8 (mclearG Sch m₁) (mclearG Sch m₂) := by
  unfold mclearG
  have e : m₁.arr64 CTL = m₂.arr64 CTL := h.1 CTL hc
  have h1 := h.set64 hc Sch.cs (rdW (m₁.arr64 CTL) Sch.cs + 1)
  have h2 := h1.set64 hc (Sch.cs + 1) 0
  rw [e] at h2 ⊢
  exact h2

theorem flushMem_agree {S : TieredArray → Bool} {S8 : ArrId → Bool} {m₁ m₂ : Mem}
    (h : Agree S S8 m₁ m₂) (hc : S CTL = true) : Agree S S8 (flushMem m₁) (flushMem m₂) := by
  have g := fun (Sch : MemoSch) {x y : Mem} (hxy : Agree S S8 x y) => mclearG_agree hxy hc Sch
  exact g _ (g _ (g _ (g _ (g _ (g _ (g _ (g _ (g _ (g _ (g _ h))))))))))

/-! ## The twin's side of the pool at an accepting phase A -/

local notation "VM" => ConLeche.CheckMode.verified

/-- **The pool's twin facts at an accepting phase A** (con-ron's `pooledAccepts_bridge`): the
driver state after the index build, its pins and records denoting, the index denoting, for any
worker step `hstep`. -/
theorem poolHyps_of_phaseA {b : ByteArray} (PA : PhaseA b) {σ : Type} (Rel : σ → AState → Prop)
    (Call : Nat → σ → σ → Prop) :
    ∃ (pinsP : List ConLeche.NatOpPinSet) (dsP : List ConLeche.Declaration),
      StateOK PA.sF ∧ (ConRon.Bridge.RecordSpec PA.ipins pinsP) ∧ PersPinSets PA.ipins ∧
      (∀ x ∈ PA.ds.toList, PersDecl x ∧ ∃ d, Frontend.denoteDecl PA.sF.store x = some d) ∧
      PinsDenote PA.sF.store PA.ipins pinsP ∧
      ((∀ (k : Nat) (r r' : σ) (a : AState) (hk : k < PA.ds.size), Rel r a → Call k r r' →
        (∃ env, FoldOK env (PA.I.view k) (AM.st enterScratch a)) →
        ∃ a', recordJob VM PA.ipins PA.I k PA.ds[k] a = .ok ((), a') ∧ Rel r' a') →
      PoolHyps (pins := PA.ipins) (pinsP := pinsP) (ds := PA.ds) (dsP := dsP) (I := PA.I)
        (s₁ := PA.sF) Rel Call) := by
  obtain ⟨hA, hB, hC, hD, hE⟩ := PA.pfx
  obtain ⟨hoff, hst, hpp, hipins, hpps, hpd, rc, preC, -, hden⟩ :=
    ConRon.Bridge.stages_frame (chunks := [b]) hA hB hC hD hE
  obtain ⟨hst', hx, hp', -, hI, hpI⟩ := buildIndex_run constsSpec tablesSpec hst hoff hpd hden PA.idx
  have hx' := PExt.of_ext hx
  obtain ⟨hlen, hget⟩ := denoteDecls_getElem hden
  have hden' : ∀ (i : Nat) (hi : i < PA.ds.size), ∃ hi' : i < (ConLeche.Frontend.preparePrelude preC rc.decls).toList.length,
      Frontend.denoteDecl PA.sF.store PA.ds[i] = some (ConLeche.Frontend.preparePrelude preC rc.decls).toList[i] :=
    fun i hi => by
      obtain ⟨hi', h⟩ := hget i (by simpa using hi)
      exact ⟨hi', Frontend.denoteDecl_ext hx (by simpa using h)⟩
  have hrec : RecordSpec PA.ipins PA.pins :=
    recordSpec (CoreSpec.of_core) ConRon.Bridge.Inductives.indSpec_of_bridge
  have hPD := PinsDenote.mono hx PA.ipins PA.pins hipins
  refine ⟨PA.pins, _, hst'.state, hrec, hpps, fun x hx'' => ⟨hpd x hx'', ?_⟩, hPD, fun hstep =>
    { hrec := hrec, hpush := kernelPushes _, hpp := hpps,
      hpinsOK := hst.pins.pmono hpp hx' hp', hpersPins := hpp.mono hp', hpins := hPD,
      hpd := hpd, hlen := by simpa using hlen, hden := hden', hI := hI, hpI := hpI,
      hstep := hstep }⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx''
  obtain ⟨_, hd⟩ := hden' i (by simpa using hi)
  exact ⟨_, by simpa using hd⟩

end L.Checker
