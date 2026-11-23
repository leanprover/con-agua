module

import ConRon.Bridge.Checker.Pool
import ConRon.Bridge.Checker.Hyp
import ConRon.Bridge.Checker.Install
import ConRon.Bridge.Inductives.Decl
import ConRon.Bridge.Stages
meta import ConAgua.Checker.PhaseBReads
meta import ConAgua.Arena.FreezeRel
meta import ConAgua.Checker.LoopProgTac
meta import ConAgua.Final.Statement
import ConAgua.L.Blocks
import all ConAgua.Checker.Entry
public import ConAgua.Checker.ParDriverL
import ConAgua.Checker.JobsStart
import ConAgua.Checker.RomProg0

@[expose] public section

/-!
# The sequential driver's jobs at any job relation (lane compare)

`ParDriverL.lean`'s `checkJobs_seqO` … `checkMode2_seqO` with the index build's `FoldOn` and the
twin's pool replaced by the job relation the jobs start from (`JobR` at the flushed memory) and
the memory-level conclusion `JobsRan`: a returning entry 2 (`check` with the mode word `2`, the
range `[0, k)`, an empty seed) that returns `ACCEPT` is a chain of `record_job` calls over every
record from a memory in the job relation. The twin's side is the caller's (`pool_twin` without a
solution, `pool_twinJ` with one).
-/

set_option experimental.vcgen true

open ConRon.Arena ConAgua.Final
open ConRon.Bridge (JobChain)
open Std.WP
open scoped Lean.Order

namespace L.Checker

open L L.Arena L.Rom

/-- **The jobs ran**: a memory in the job relation (from `a₀`) and a chain of returning
`record_job` calls from it over the records `0‥k-1`. -/
def JobsRan (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)
    (J : Option ISolution) (I : IStreamIndex) (a₀ : AState) (p : Prog) (k : Nat) : Prop :=
  ∃ r, JobR pins dn ds J I r a₀ ∧ JobChain (RecCall p) r (List.range k)

section
variable {pb : ByteArray} {ipins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}
  {ds : Array IDeclaration} {J : Option ISolution} {I : IStreamIndex} {a₀ : AState}

/-- **`check_jobs(0, k)` as a chain** (`checkJobs_seqO`'s memory half): a returning run on a
memory that agrees with `F` (in the job relation) on every array the jobs name. -/
theorem checkJobs_chainR {F : Mem} (hJ0 : JobR ipins dn ds J I F a₀)
    (hPB : F.arr8 L.Rom.PB = pb.data.toList.toArray)
    (hJP : JobProg ipins dn ds (Prog.subPB pb.data.toList checkerProg))
    {n : Nat} (hn : n ≤ 2 ^ 62) {s : St} {hi : Word} (hhi : hi.toNat = ds.size)
    (hag : ∀ a, phaseBS a = true → s.mem.arr64 a = F.arr64 a)
    {rs : List Word} {s' : St}
    (hrun : (invoke checkerProg (exec checkerProg n) "check_jobs" [0, hi]).run s = .ok (rs, s')) :
    JobsRan ipins dn ds J I a₀ (Prog.subPB pb.data.toList checkerProg) ds.size := by
  let p := Prog.subPB pb.data.toList checkerProg
  let s₂ : St := ⟨⟨F.bytes, F.words, s.mem.glob⟩, s.loc⟩
  have hAg : Agree phaseBS (fun _ => false) s.mem s₂.mem :=
    ⟨fun a ha => hag a ha, fun _ h => absurd h (by simp), rfl⟩
  obtain ⟨s₂', hrun₂, -, -⟩ :=
    invoke_agree_ok checkerProg_phaseBReads check_jobs_mem_phaseBJobFns hAg rfl hrun
  have hPB' : s₂.mem.arr8 L.Rom.PB = pb.data.toList.toArray := hPB
  rw [← L.Rom.invoke_subPB (bs := pb.data.toList) checkerProg_noSt8PB n _ _ (s := s₂) hPB'] at hrun₂
  have hc := callE_of_run hrun₂
  obtain ⟨_s3, -, -, hx⟩ := triple_of_callE
    (checkJobs_specE p hJP.check_jobs n ⟨s₂.mem, Locals.init []⟩ 0 hi) hc
  rcases n with _ | n
  · obtain ⟨e, he, -⟩ := callE_zero p "check_jobs" [0, hi] s₂.mem
    rw [hc] at he; cases he
  have hx' : checkJobsE.k_loop1 p (checkJobsE.loop1 p (n + 1) s₂.mem 0 hi) = _ := hx
  cases hl : checkJobsE.loop1 p (n + 1) s₂.mem 0 hi with
  | error ε => rw [hl] at hx'; cases hx'
  | ok q =>
  have hch := checkJobsLoop_chain (n + 1) (by omega) s₂.mem 0 q hl
  simp only [UInt64.toNat_zero, Nat.sub_zero, hhi] at hch
  exact ⟨s₂.mem, hJ0.setGlob _, by rw [List.range_eq_range']; exact hch⟩

/-- **`check_jobs` after the flush**, as a triple (`checkJobs_seqTO` at any job relation). -/
theorem checkJobs_seqTR {m : Mem} (hJ0 : FlushOK m → JobR ipins dn ds J I (flushMem m) a₀)
    (hPB : m.arr8 L.Rom.PB = pb.data.toList.toArray)
    (hJP : JobProg ipins dn ds (Prog.subPB pb.data.toList checkerProg))
    (n : Nat) (hn : n ≤ 2 ^ 62) (hi : Word) (hhi : hi.toNat = ds.size) (x y : Word) :
    ⦃fun s => x = 0 ∧ y = hi ∧ ∃ X, FlushOK X ∧ s.mem = flushMem X ∧
      ∀ a, phaseBS a = true → X.arr64 a = m.arr64 a⦄
    invoke checkerProg (exec checkerProg n) "check_jobs" [x, y]
    ⦃fun _ _ => JobsRan ipins dn ds J I a₀ (Prog.subPB pb.data.toList checkerProg) ds.size; ⊤⦄ := by
  apply M.triple_of_run
  rintro s rs s' ⟨rfl, rfl, X, hfx, hsX, hXm⟩ hrun
  let m₂ : Mem := ⟨m.bytes, m.words, X.glob⟩
  have hAg : Agree phaseBS (fun _ => false) X m₂ :=
    ⟨fun a ha => hXm a ha, fun _ h => absurd h (by simp), rfl⟩
  have hc : phaseBS CTL = true := by decide
  have hfok : FlushOK m := by
    rw [flushOK_eq] at hfx ⊢
    exact clearsOK_words _ (m₁ := m₂) (m₂ := m) rfl (clearsOK_agree hc _ hAg hfx)
  have hA2 := flushMem_agree hAg hc
  have hw2 : (flushMem m₂).words = (flushMem m).words := flushMem_words rfl
  exact checkJobs_chainR (hJ0 hfok) (by rw [Mem.arr8, flushMem_bytes]; exact hPB) hJP hn hhi
    (fun a ha => by
      rw [hsX, hA2.1 a ha]; show (flushMem m₂).words a = (flushMem m).words a; rw [hw2]) hrun

/-- **Entry 2 in place, `check_b`** (`checkB_seqO` at any job relation). -/
theorem checkB_seqR {m : Mem} (hJ0 : FlushOK m → JobR ipins dn ds J I (flushMem m) a₀)
    (hPB : m.arr8 L.Rom.PB = pb.data.toList.toArray)
    (hJP : JobProg ipins dn ds (Prog.subPB pb.data.toList checkerProg))
    (n : Nat) (hn : n ≤ 2 ^ 62) (hi : Word) (hhi : hi.toNat = ds.size) (s₀ : St)
    (hw : ∀ a, phaseBS a = true → s₀.mem.arr64 a = m.arr64 a)
    (hlo : s₀.mem.glob PLO = 0) (hhi' : s₀.mem.glob PHI = hi) (hctlf : (s₀.mem.arr64 CTLF).size = 0) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "check_b" []
    ⦃fun r _ => r.headD 0 = ConAgua.Final.ACCEPT →
      JobsRan ipins dn ds J I a₀ (Prog.subPB pb.data.toList checkerProg) ds.size; ⊤⦄ := by
  have hl : (UInt64.toNat (s₀.mem.len64 CTLF)) = 0 := by simp [Mem.len64, hctlf]
  have hlo' : s₀.mem.glob ⟨9⟩ = 0 := hlo
  have hhi'' : s₀.mem.glob ⟨11⟩ = hi := hhi'
  rw [invoke_eq _ checkerProg_lookup_check_b]
  simp only [callFn, checkBL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hJ := checkJobs_seqTR hJ0 hPB hJP n (by omega) hi hhi
    have hFl := flushCaches_spec checkerProg checkerProg_flushProg n
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, setG, ld64, warr, (hJ · ·), (hFl ·)]
    all_goals (try simp only [L.St.setLoc_mem, St.setLoc_loc,
      L.Locals.init_nil, Cmp.eval,
      reduceIte, beq_iff_eq, decide_eq_true_eq] at *)
    all_goals (try simp only [hl, Mem.copy64_zero] at *)
    all_goals (try simp only [St.setG, Mem.setG, St.setLoc] at *)
    all_goals first
      | (simp_all (config := { decide := true }) [Mem.arr64]; done)
      | skip
    all_goals
      obtain ⟨-, hfx, hm⟩ := ‹LocEq _ _ ∧ FlushOK _ ∧ _›
      first
        | exact ⟨_, hfx, by rw [L.St.setLocs_mem]; exact hm, fun a ha => hw a ha⟩
        | (rw [L.St.setLocs_mem, hm, flushMem_glob]; simp_all)

/-- **Entry 2 in place, `check` with the mode word `2`** (`checkMode2_seqO` at any job relation). -/
theorem checkMode2_seqR {m : Mem} (hJ0 : FlushOK m → JobR ipins dn ds J I (flushMem m) a₀)
    (hPB : m.arr8 L.Rom.PB = pb.data.toList.toArray)
    (hJP : JobProg ipins dn ds (Prog.subPB pb.data.toList checkerProg))
    (n : Nat) (hn : n ≤ 2 ^ 62) (hi : Word) (hhi : hi.toNat = ds.size) (s₀ : St)
    (hw : ∀ a, phaseBS a = true → s₀.mem.arr64 a = m.arr64 a) (hmode : s₀.mem.glob MODE = 2)
    (hlo : s₀.mem.glob PLO = 0) (hhi' : s₀.mem.glob PHI = hi) (hctlf : (s₀.mem.arr64 CTLF).size = 0) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "check" []
    ⦃fun r _ => r.headD 0 = ACCEPT →
      JobsRan ipins dn ds J I a₀ (Prog.subPB pb.data.toList checkerProg) ds.size; ⊤⦄ := by
  rw [invoke_eq _ checkerProg_lookup_check']
  simp only [callFn, checkL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hB := checkB_seqR hJ0 hPB hJP n (by omega) hi hhi
    have hmode' : s₀.mem.glob ⟨8⟩ = 2 := hmode
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, hB,
      (L.invoke_loc checkerProg (exec checkerProg n) "check_a" [1] ·),
      (L.invoke_loc checkerProg (exec checkerProg n) "check_a" [0] ·),
      (L.invoke_loc checkerProg (exec checkerProg n) "check_c1" [] ·),
      (L.invoke_loc checkerProg (exec checkerProg n) "check_c2" [] ·),
      (L.invoke_loc checkerProg (exec checkerProg n) "check_c3" [·] ·)]
    all_goals (try simp only [St.setLoc_loc, St.setLocs_cons,
      Cmp.eval, reduceIte, beq_iff_eq, Sig.retVal, Sig.retOr, St.setLocs_nil, List.headD_cons] at *)
    all_goals first
      | (simp_all (config := { decide := true }); done)
      | (simp_all [St.setLoc]; done)

end

end L.Checker
