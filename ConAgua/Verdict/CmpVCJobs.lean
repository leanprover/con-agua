module

public import ConAgua.Verdict.CmpVSJobs
public import ConAgua.Final.CmpChainC
public import ConAgua.Checker.CompareJobs
import ConAgua.Checker.CompareChain6J
import ConAgua.Checker.CompareTwinJ
import ConAgua.Checker.CmpVerdictNv
import ConAgua.Checker.CrsProgPB
import ConAgua.Checker.RomProgInit
import ConAgua.Checker.JobsProg
import ConAgua.Checker.ArmsT
import ConAgua.Checker.CheckARun
import ConAgua.Checker.AsmFinal
import ConAgua.Checker.VerdictEntry1
import ConAgua.Checker.LoopStage
import ConAgua.L.Blocks
import all ConAgua.Checker.Entry
import ConAgua.Front.FrontRunRef
import ConAgua.Arena.JobStart
import ConAgua.Arena.PoolJobsJ
import ConAgua.Final.DrvFinal

@[expose] public section

/-!
# The challenge's jobs of the compared run fail only where the twin's do (lane compare2, helper
compare2-verdict)

The error halves of `CompareJobs.lean`'s `checkJobs_seqTR` … `checkMode2_seqR` (entry 2 in place
at any job relation): a failing run is a failing `check_jobs(0, hi)` from a memory in the job
relation (`checkJobs_seqER`, `checkB_seqER`, `checkMode2_seqER`), whatever that call claims.
-/

set_option experimental.vcgen true

open ConRon.Arena ConAgua.Final
open ConRon.Bridge (JobChain PExt WorkerOK MixedPrefix job_specC PersDecl)
open Std.WP
open scoped Lean.Order

namespace L.Checker

open L L.Arena L.Rom L.Compiler

local notation "VM" => ConLeche.CheckMode.verified

section
variable {pb : ByteArray} {ipins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}
  {ds : Array IDeclaration} {J : Option ISolution} {I : IStreamIndex} {a₀ : AState}
  {α β : Type} {T : AM (Except (CheckError × α) β)}

/-- **`check_jobs` after the flush, error half of `checkJobs_seqTR`**: a failing run is a failing
`check_jobs(0, hi)` call (at the ROM's program) from a memory in the job relation. -/
theorem checkJobs_seqER {m : Mem} (hJ0 : FlushOK m → JobR ipins dn ds J I (flushMem m) a₀)
    (hPB : m.arr8 L.Rom.PB = pb.data.toList.toArray) (hi : Word)
    (hE : ∀ n, n ≤ 2 ^ 62 → ∀ M : Mem, JobR ipins dn ds J I M a₀ → ∀ e,
      callE (Prog.subPB pb.data.toList checkerProg) n "check_jobs" [0, hi] M = .error e →
      ErrClaimV T a₀ e)
    (n : Nat) (hn : n ≤ 2 ^ 62) (x y : Word) :
    ⦃fun s => x = 0 ∧ y = hi ∧ ∃ X, FlushOK X ∧ s.mem = flushMem X ∧
      ∀ a, phaseBS a = true → X.arr64 a = m.arr64 a⦄
    invoke checkerProg (exec checkerProg n) "check_jobs" [x, y]
    ⦃fun _ _ => True; ErrClaimV T a₀⦄ := by
  apply M.triple_of_run' (fun _ _ _ _ _ => trivial)
  rintro s e ⟨rfl, rfl, X, hfx, hsX, hXm⟩ hrun
  let m₂ : Mem := ⟨m.bytes, m.words, X.glob⟩
  have hAg0 : Agree phaseBS (fun _ => false) X m₂ :=
    ⟨fun a ha => hXm a ha, fun _ h => absurd h (by simp), rfl⟩
  have hcC : phaseBS CTL = true := by decide
  have hfok : FlushOK m := by
    rw [flushOK_eq] at hfx ⊢
    exact clearsOK_words _ (m₁ := m₂) (m₂ := m) rfl (clearsOK_agree hcC _ hAg0 hfx)
  have hA2 := flushMem_agree hAg0 hcC
  have hw2 : (flushMem m₂).words = (flushMem m).words := flushMem_words rfl
  have hag : ∀ a, phaseBS a = true → s.mem.arr64 a = (flushMem m).arr64 a := fun a ha => by
    rw [hsX, hA2.1 a ha]; show (flushMem m₂).words a = (flushMem m).words a; rw [hw2]
  have hJ1 := hJ0 hfok
  have hPB1 : (flushMem m).arr8 L.Rom.PB = pb.data.toList.toArray := by
    rw [Mem.arr8, flushMem_bytes]; exact hPB
  generalize flushMem m = F at hJ1 hag hPB1
  let s₂ : St := ⟨⟨F.bytes, F.words, s.mem.glob⟩, s.loc⟩
  have hAg : Agree phaseBS (fun _ => false) s.mem s₂.mem :=
    ⟨fun a ha => hag a ha, fun _ h => absurd h (by simp), rfl⟩
  have hrun₂ := invoke_agree_err checkerProg_phaseBReads check_jobs_mem_phaseBJobFns hAg rfl hrun
  have hPB2 : s₂.mem.arr8 L.Rom.PB = pb.data.toList.toArray := hPB1
  rw [← L.Rom.invoke_subPB (bs := pb.data.toList) checkerProg_noSt8PB n _ _ (s := s₂) hPB2] at hrun₂
  exact hE n hn s₂.mem (hJ1.setGlob _) e (L.Front.callE_of_run_err hrun₂)

/-- **Entry 2 in place, `check_b`, error half of `checkB_seqR`.** -/
theorem checkB_seqER {m : Mem} (hJ0 : FlushOK m → JobR ipins dn ds J I (flushMem m) a₀)
    (hPB : m.arr8 L.Rom.PB = pb.data.toList.toArray) (hi : Word)
    (hE : ∀ n, n ≤ 2 ^ 62 → ∀ M : Mem, JobR ipins dn ds J I M a₀ → ∀ e,
      callE (Prog.subPB pb.data.toList checkerProg) n "check_jobs" [0, hi] M = .error e →
      ErrClaimV T a₀ e)
    (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (hw : ∀ a, phaseBS a = true → s₀.mem.arr64 a = m.arr64 a)
    (hlo : s₀.mem.glob PLO = 0) (hhi' : s₀.mem.glob PHI = hi) (hctlf : (s₀.mem.arr64 CTLF).size = 0) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "check_b" []
    ⦃fun _ _ => True; ErrClaimV T a₀⦄ := by
  have hl : (UInt64.toNat (s₀.mem.len64 CTLF)) = 0 := by simp [Mem.len64, hctlf]
  have hlo' : s₀.mem.glob ⟨9⟩ = 0 := hlo
  have hhi'' : s₀.mem.glob ⟨11⟩ = hi := hhi'
  -- in place the seed re-read is the identity (`CTLF` empty)
  have hl0 : s₀.mem.len64 CTLF = 0 := by simp [Mem.len64, hctlf]
  have hl0' : ∀ b g, (Mem.mk b s₀.mem.words g).len64 CTLF = 0 := fun _ _ => hl0
  rw [invoke_eq _ checkerProg_lookup_check_b]
  simp only [callFn, checkBL]
  cases n with
  | zero => vcgen [exec] <;> simp [ErrClaimV.of_cls0]
  | succ n =>
    have hJ := checkJobs_seqER hJ0 hPB hi hE n (by omega)
    have hFl := flushCaches_specNV n
    have hRR := seedReread_specNV n
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, setG, ld64, warr, (hJ · ·), (hFl ·), (hRR ·)]
    all_goals (try simp only [L.St.setLoc_mem, St.setLoc_loc,
      L.Locals.init_nil, Cmp.eval,
      reduceIte, beq_iff_eq, decide_eq_true_eq] at *)
    all_goals (try simp only [hl, Mem.copy64_zero] at *)
    all_goals (try simp only [St.setG, Mem.setG, St.setLoc] at *)
    all_goals (try simp only [rereadMem_empty, hl0, hl0'] at *)
    all_goals first
      | exact ErrClaimV.of_cls0 (by decide)
      | exact ErrClaimV.of_cls0 ‹_›
      | (simp_all (config := { decide := true }) [Mem.arr64]; done)
      | skip
    all_goals first
      | (obtain ⟨-, hfx, hm⟩ := ‹LocEq _ _ ∧ FlushOK _ ∧ _›
         first
          | exact ⟨_, hfx, by rw [L.St.setLocs_mem]; exact hm, fun a ha => hw a ha⟩
          | exact ⟨_, hfx, by rw [L.St.setLocs_mem]; exact hm,
              fun a ha => by rw [L.St.setLocs_mem]; simp_all [Mem.arr64]⟩
          | (rw [L.St.setLocs_mem, hm, flushMem_glob]; simp_all; done))
      | (trace_state; fail "CmpVCJobs.checkB_seqER: no closing tactic applies")

/-- **Entry 2 in place, `check` with the mode word `2`, error half of `checkMode2_seqR`.** -/
theorem checkMode2_seqER {m : Mem} (hJ0 : FlushOK m → JobR ipins dn ds J I (flushMem m) a₀)
    (hPB : m.arr8 L.Rom.PB = pb.data.toList.toArray) (hi : Word)
    (hE : ∀ n, n ≤ 2 ^ 62 → ∀ M : Mem, JobR ipins dn ds J I M a₀ → ∀ e,
      callE (Prog.subPB pb.data.toList checkerProg) n "check_jobs" [0, hi] M = .error e →
      ErrClaimV T a₀ e)
    (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (hw : ∀ a, phaseBS a = true → s₀.mem.arr64 a = m.arr64 a) (hmode : s₀.mem.glob MODE = 2)
    (hlo : s₀.mem.glob PLO = 0) (hhi' : s₀.mem.glob PHI = hi) (hctlf : (s₀.mem.arr64 CTLF).size = 0) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "check" []
    ⦃fun _ _ => True; ErrClaimV T a₀⦄ := by
  rw [invoke_eq _ checkerProg_lookup_check']
  simp only [callFn, checkL]
  cases n with
  | zero => vcgen [exec] <;> simp [ErrClaimV.of_cls0]
  | succ n =>
    have hB : ⦃fun s => s.mem = s₀.mem⦄ invoke checkerProg (exec checkerProg n) "check_b" []
        ⦃fun _ _ => True; ErrClaimV T a₀⦄ := by
      apply M.triple_of_run' (fun _ _ _ _ _ => trivial)
      intro s₁ e hs hrun
      exact M.of_run_err (P := fun x => x = s₁) rfl hrun
        (checkB_seqER hJ0 hPB hi hE n (by omega) s₁ (hs ▸ hw) (hs ▸ hlo) (hs ▸ hhi') (hs ▸ hctlf))
    have hmode' : s₀.mem.glob ⟨8⟩ = 2 := hmode
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, hB,
      (callE_spec checkerProg n "check_a" [1] ·), (callE_spec checkerProg n "check_a" [0] ·),
      (callE_spec checkerProg n "check_bs" [] ·), (callE_spec checkerProg n "check_bc" [] ·),
      (callE_spec checkerProg n "check_c1" [] ·), (callE_spec checkerProg n "check_c2" [] ·),
      (callE_spec checkerProg n "check_c3" [·] ·)]
    all_goals (try simp only [Cmp.eval, beq_iff_eq] at *)
    all_goals first
      | exact ErrClaimV.of_cls0 (by decide)
      | (simp_all (config := { decide := true }); done)
      | (simp_all [St.setLoc]; done)
      | (trace_state; fail "CmpVCJobs.checkMode2_seqER: no closing tactic applies")

end

end L.Checker
