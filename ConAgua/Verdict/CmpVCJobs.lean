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
`cmpCJobs_err`: after mode `6`, the challenge's jobs at the solution (`J = some`) failing with a
class other than `0` are the twin's job list failing with that class (`checkJobs_ref` under
`JobGJ`, the fold's prefix a mixed run, `job_specC`, as `pool_walkJ`); `cmpV_cjob`: the same from
the driver's runs (`CmpErr`'s last arm), as `TwinCompareVerdict.jobsC`.
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
  rw [invoke_eq _ checkerProg_lookup_check_b]
  simp only [callFn, checkBL]
  cases n with
  | zero => vcgen [exec] <;> simp [ErrClaimV.of_cls0]
  | succ n =>
    have hJ := checkJobs_seqER hJ0 hPB hi hE n (by omega)
    have hFl := flushCaches_specNV n
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, setG, ld64, warr, (hJ · ·), (hFl ·)]
    all_goals (try simp only [L.St.setLoc_mem, St.setLoc_loc,
      L.Locals.init_nil, Cmp.eval,
      reduceIte, beq_iff_eq, decide_eq_true_eq] at *)
    all_goals (try simp only [hl, Mem.copy64_zero] at *)
    all_goals (try simp only [St.setG, Mem.setG, St.setLoc] at *)
    all_goals first
      | exact ErrClaimV.of_cls0 (by decide)
      | exact ErrClaimV.of_cls0 ‹_›
      | (simp_all (config := { decide := true }) [Mem.arr64]; done)
      | skip
    all_goals first
      | (obtain ⟨-, hfx, hm⟩ := ‹LocEq _ _ ∧ FlushOK _ ∧ _›
         first
          | exact ⟨_, hfx, by rw [L.St.setLocs_mem]; exact hm, fun a ha => hw a ha⟩
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
      (callE_spec checkerProg n "check_c1" [] ·), (callE_spec checkerProg n "check_c2" [] ·),
      (callE_spec checkerProg n "check_c3" [] ·)]
    all_goals (try simp only [Cmp.eval, beq_iff_eq] at *)
    all_goals first
      | exact ErrClaimV.of_cls0 (by decide)
      | (simp_all (config := { decide := true }); done)
      | (simp_all [St.setLoc]; done)
      | (trace_state; fail "CmpVCJobs.checkMode2_seqER: no closing tactic applies")

end

/-- **The challenge's jobs of the compared run failing ⇒ the twin's job list fails** (one worker,
at the solution `solutionOf IS res`; the error half of `cmpCJobs_twin`): after mode `6` (`F6`),
entry 2 in place on a memory `w` that agrees with mode `6`'s memory before `par_compact(0)` on
every array the jobs name, with the range `[0, c)` and an empty seed, failing with a class other
than `0`. -/
theorem cmpCJobs_err {bC bS pb : ByteArray} (hpb : pb.size < 2 ^ 63) (PS : PhaseS bC bS) {m₇ m : Mem}
    (hF : FoldOn bS pb (abiSz checkerTab) PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m)
    (hS : ∃ s'', checkJobList .verified PS.ipins none PS.IS PS.dsS (List.range PS.dsS.size)
      PS.sF.worker = .ok (.ok (), s''))
    {c : Word} {m9 : Mem} (h6 : F6 PS m c m9) (hb9 : m9.bytes = m.bytes)
    {w : Mem} (hw : ∀ a, phaseBS a = true → w.arr64 a = m9.arr64 a) (hmode : w.glob MODE = 2)
    (hlo : w.glob PLO = 0) (hhi : w.glob PHI = c) (hctlf : (w.arr64 CTLF).size = 0)
    {e : Err} (h7 : L.run checkerProg abiFuel "check" [] w = .error e) (hk : e.cls ≠ 0) :
    ∃ (m2 m3 : Mem) (dsC : Array IDeclaration) (sG : AState) (res : List IDeclaration) (m4 : Mem)
      (I : IStreamIndex) (a' : AState),
      Side6 PS m c m2 m3 dsC sG res m4 ∧ buildIndex res.toArray sG = .ok (.ok I, a') ∧
      TwinFailsV (checkJobList .verified PS.ipins (some (solutionOf PS.IS res)) I res.toArray
        (List.range res.toArray.size)) a'.worker e.cls := by
  obtain ⟨m2, m3, dsC, sG, res, m4, I, a', h, hI, hJ0⟩ := F6.jobR hF h6
  refine ⟨m2, m3, dsC, sG, res, m4, I, a', h, hI, ?_⟩
  obtain ⟨-, -, -, -, ho⟩ := h.phase.out
  -- the program facts
  have hr : RomOK pb.data.toList := by simpa [RomOK] using hpb
  have hpre := hF.r7.since.pbpre
  have hinj : L.Ind.DnInj (dnOf sG.store) := dnOf_inj ho.drv.state.wf
  have hq : L.Ind.QuotDn (dnOf sG.store) := by
    obtain ⟨k, hk, hd⟩ := ho.quot
    exact ⟨k, by simp only [dnOf, hk]; exact hd⟩
  obtain ⟨hdf, hind⟩ := checkerCdG_proved pb PS.ipins (dnOf sG.store) res.toArray hpb hpre hinj
  have hcd := checkerProg_cdProgPB pb.data.toList hr hpre hinj hq hdf hind
  have hJP := checkerProg_jobProgPB pb.data.toList hr hpre hcd (checkerProg_canonPB _)
  let p := Prog.subPB pb.data.toList checkerProg
  have hPB : m9.arr8 L.Rom.PB = pb.data.toList.toArray := by
    show m9.bytes L.Rom.PB = _
    rw [hb9, hF.bytes, ← Mem.arr8, hF.r7.since.keep.arr8]
    exact loadMem_pb bS pb _
  have hcnt : c.toNat = res.toArray.size := by simpa using h.count.1
  have hN : abiFuel ≤ 2 ^ 62 := by simp [abiFuel]
  -- the twin
  let JS := solutionOf PS.IS res
  let a₀ : AState := { a' with caches := Caches.empty }
  obtain ⟨pinsP, dsP, dsSP, matesU, hst, hspec, hpp, hden, hPD, hH⟩ := poolHypsJ_of h.phase hS hI
    (JobRel PS.ipins (dnOf sG.store) res.toArray (some JS) I a₀) (RecCall p)
  have hdn : DnPers (dnOf sG.store) := fun k x hk => by
    simp only [dnOf] at hk; split at hk
    · assumption
    · cases hk
  have hds : res.toArray.size < 2 ^ 64 := by rw [← hcnt]; exact UInt64.toNat_lt c
  have hcrs : CrsFor PS.ipins (dnOf sG.store) res.toArray p (some JS) :=
    fun _ => checkerProg_crsSpecPB pb.data.toList hr hpre hcd
  have H := hH (recCall_stepE (J := some JS) hJP ho.front (declsLpsDn_dnOf ho.pd ho.den) hdn hpp hds
    hden hPD hspec hcrs)
  have hw0 : WorkerOK a' a₀ := ⟨⟨hst.wf⟩, PExt.of_ext (Ext.refl _), rfl, rfl⟩
  -- the jobs before a job accepted in order: a mixed prefix, a worker state
  have hseq : ∀ (n t : Nat) (a a'' : AState), WorkerOK a' a →
      MixedPrefix pinsP ⟨ConLeche.mkFEnv (ConLeche.streamEnv dsSP), matesU⟩ dsP t →
      t + n ≤ res.toArray.size →
      checkJobList VM PS.ipins (some JS) I res.toArray (List.range' t n) a = .ok (.ok (), a'') →
      WorkerOK a' a'' ∧ MixedPrefix pinsP ⟨ConLeche.mkFEnv (ConLeche.streamEnv dsSP), matesU⟩ dsP (t + n) := by
    intro n
    induction n with
    | zero =>
      intro t a a'' hw hP _ hl
      rw [List.range'_zero] at hl
      cases hl
      exact ⟨hw, hP⟩
    | succ n ih =>
      intro t a a'' hw hP hle hl
      have htk : t < res.toArray.size := by omega
      rw [List.range'_succ] at hl
      cases hrj : recordJob VM PS.ipins (some JS) I t res.toArray[t] a with
      | error ce =>
        have e1 : (checkJobList VM PS.ipins (some JS) I res.toArray (t :: List.range' (t + 1) n)) a =
            .ok (.error (ce, t), AState.abandoned) := by
          simp only [checkJobList, runJob, Array.getElem?_eq_getElem htk, hrj]
        rw [show (checkJobList VM PS.ipins (some JS) I res.toArray (t :: List.range' (t + 1) n)) a = _
          from hl] at e1
        cases e1
      | ok v =>
        obtain ⟨u, a₁⟩ := v
        cases u
        rw [checkJobList_cons_ok htk hrj] at hl
        obtain ⟨htk', hdk⟩ := H.hden t htk
        obtain ⟨hw₁, env', hd⟩ := job_specC H.hrec H.hpp H.hpinsOK H.hpersPins H.hpins H.hpd H.hI
          H.hpI H.hIS H.hpIS H.hndS H.hmates hw htk htk' hdk hP hrj
        have := ih (t + 1) a₁ a'' hw₁ (MixedPrefix.step htk' hP hd) (by omega) hl
        rwa [show t + 1 + n = t + (n + 1) by omega] at this
  have hG : JobGJ PS.ipins (dnOf sG.store) res.toArray p (some JS) :=
    ⟨jobG_ofDn hinj hq pb hpb hpre, crsG_checker _⟩
  have hden' : ∀ x ∈ res.toArray.toList, PersDecl x ∧ ∃ d, Frontend.denoteDecl a₀.store x = some d := hden
  have hE : ∀ n, n ≤ 2 ^ 62 → ∀ M : Mem,
      JobR PS.ipins (dnOf sG.store) res.toArray (some JS) I M a₀ → ∀ e,
      callE p n "check_jobs" [0, c] M = .error e →
      ErrClaimV (checkJobList VM PS.ipins (some JS) I res.toArray (List.range res.toArray.size)) a₀ e := by
    intro n hn M hJ e hc
    have hh := checkJobs_ref (J := some JS) (I := I) hJP ho.front (declsLpsDn_dnOf ho.pd ho.den) hdn hpp
      hden' hPD hspec hcrs (hi := c) (j := 0) (by omega) hn ⟨hJ, PExt.of_ext (Ext.refl _), rfl⟩
      (fun t a'' _ h2 h3 => by
        simp only [UInt64.toNat_zero, Nat.sub_zero] at h3 h2
        have ht : t < res.toArray.size := by omega
        obtain ⟨hw', hP⟩ := hseq t 0 a₀ a'' hw0 (MixedPrefix.zero _ _ _) (by omega) h3
        rw [Nat.zero_add] at hP
        obtain ⟨htk', -⟩ := H.hden t ht
        exact worker_foldOKJ H.hpinsOK H.hpersPins H.hI H.hpI htk' hP hw')
    have h' := RefC.run_err (checkJobs_specE p hJP.check_jobs n ⟨M, Locals.init []⟩ 0 c)
      (fun e h0 => ErrClaimV.of_cls0 h0) trivial hG hh hc
    simpa only [UInt64.toNat_zero, Nat.sub_zero, hcnt, ← List.range_eq_range'] using h'
  have hc7 := M.of_run_err (P := fun x => x = ⟨w, Locals.init []⟩) rfl (run_err h7)
    (checkMode2_seqER hJ0 hPB c hE abiFuel hN ⟨w, Locals.init []⟩ hw hmode hlo hhi hctlf)
  exact twinFailsV_of_sameEnter sameEnter_worker.symm (hc7 hk)

/-- **A challenge job of the compared run failing is the twin's** (`CmpErr`'s last arm): after
modes `4` and `5` returned, the solution's jobs accepted on the buffer as the jobs before left it
(`CmpJobs`), mode `6` returned `2^63 + c`, entry 2 in place over the challenge's records
`[0, c)` failing with a class other than `0`. -/
theorem cmpV_cjob (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (hbC : bC.size < 2 ^ 63) (hbS : bS.size < 2 ^ 63) (hpb : pb.size < 2 ^ 63)
    {rs4 : List Word} {m4 : Mem} {rs5 : List Word} {m5 : Mem}
    (h4 : cmpRun checkerProg (cmpM4 checkerTab MODE bC pb) = .ok (rs4, m4))
    (hge4 : 2 ^ 63 ≤ (rs4.getD 0 0).toNat)
    (h5 : cmpRun checkerProg (cmpM5 MODE m4 bS) = .ok (rs5, m5))
    (hge5 : 2 ^ 63 ≤ (rs5.getD 0 0).toNat) {rm : Nat → Mem} (hrm0 : rm 0 = zeroMem checkerTab)
    (hjobs : CmpJobs checkerProg MODE PLO PHI frozenIdsL parOwnedL (cmpBuf OUT m5) rm
      (rs5.getD 0 0 - 9223372036854775808).toNat)
    {rs6 : List Word} {m6 : Mem}
    (h6 : cmpRun checkerProg (cmpM6 MODE OUT m5 (bufSeq frozenIdsL (cmpBuf OUT m5) rm
      (rs5.getD 0 0 - 9223372036854775808).toNat)) = .ok (rs6, m6))
    {e : Err} (h7 : cmpRun checkerProg (seqMem m6 MODE PLO PHI OUT HDRF CTLF 138 0
      (rs6.getD 0 0 - 9223372036854775808)) = .error e)
    (hk : e.cls ≠ 0) : TwinCompareVerdict bC bS e.cls := by
  have hsz : ∀ s, abiSz checkerTab s < 2 ^ 64 := fun s => by
    have := abiSz_le checkerTab_abiOk s; simp only [abiWords] at this; omega
  have hN : abiFuel < 2 ^ 62 := by simp [abiFuel]
  obtain ⟨-, PS, m₇, m, hF, hst, hk6, hok, rfl, hres5⟩ :=
    checker_modes45 bC bS pb h64 hbC hbS hpb h4 hge4 h5 hge5
  -- the solution's jobs
  have hn : PS.dsS.size < 2 ^ 63 := by
    have := hF.build.decls.room; have := hF.build.decls.dsize; omega
  have hkS : (rs5.getD 0 0 - 9223372036854775808).toNat = PS.dsS.size := by
    have e : (9223372036854775808 : Word) + UInt64.ofNat PS.dsS.size - 9223372036854775808 =
        UInt64.ofNat PS.dsS.size := by rw [UInt64.add_comm, UInt64.add_sub_cancel]
    rw [L.getD_zero, hres5, e, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
  obtain ⟨s'', hSJ⟩ := cmpSJobs_twin hpb PS hF hok rfl hjobs hrm0 hkS
  rw [hkS] at hSJ
  -- mode `6`
  have hO5 : OutEq m (parCompactMem m 1) := OutEq.of_out (parCompactMem_out m 1)
  have hO : OutEq m (cmpM6 MODE OUT (parCompactMem m 1) (bufSeq frozenIdsL (cmpBuf OUT (parCompactMem m 1)) rm
      (rs5.getD 0 0 - 9223372036854775808).toNat)) :=
    (⟨fun a ha => by rw [cmpSetOut_ne _ _ _ ha]; exact hO5.arr a ha,
      fun a => by rw [cmpSetOut_size]; exact hO5.size a, by rw [cmpSetOut_bytes]; exact hO5.bytes⟩ :
      OutEq m (cmpSetOut OUT (parCompactMem m 1) _)).setG MODE 6
  have hsz6 : ∀ g ≤ 2, abiSz checkerTab (sixArr g) = abiSz checkerTab (eixArr g) ∧
      abiSz checkerTab (stxArr g) = abiSz checkerTab (tixArr g) := by
    intro g hg
    rcases (show g = 0 ∨ g = 1 ∨ g = 2 by omega) with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
  obtain ⟨c, ⟨m9, hF6, -, rfl⟩, hres6⟩ := checkC3_run PS hF hst hk6 hsz hpb hsz6 hO
    (by simp [cmpM6, Mem.setG]) abiFuel hN rs6 _ h6
  -- the challenge's jobs
  have hO9 : OutEq m9 (parCompactMem m9 0) := OutEq.of_out (parCompactMem_out m9 0)
  have hb9 : m9.bytes = m.bytes := by
    rw [← hO9.bytes, run_check_bytes h6, cmpM6_bytes]
    exact hO5.bytes
  have hhi : (rs6.getD 0 0 - 9223372036854775808) = c := by
    rw [L.getD_zero, hres6, UInt64.add_comm, UInt64.add_sub_cancel]
  obtain ⟨m2, m3, dsC, sG, res, m4', I, a', hS6, hI, hCJ⟩ := cmpCJobs_err hpb PS hF ⟨s'', hSJ⟩ hF6 hb9
    (w := seqMem (parCompactMem m9 0) MODE PLO PHI OUT HDRF CTLF 138 0 (rs6.getD 0 0 - 9223372036854775808))
    (fun a ha => by
      rw [seqMem_arr64]
      have h1 : ¬ (a = ↑OUT ∨ a = ↑CTLF) := by
        rintro (rfl | rfl) <;> revert ha <;> decide
      have h2 : a ≠ ↑HDRF := by rintro rfl; revert ha; decide
      simp only [h1, h2, ite_false]
      exact hO9.arr a (fun e => h1 (.inl e)))
    rfl rfl (by rw [← hhi]; rfl) (by rw [seqMem_arr64]; simp) h7 hk
  obtain ⟨⟨hA, hB, hC⟩, hCS, hDS⟩ := PS.pfx
  exact TwinCompareVerdict.jobsC hA hB hC hCS hDS PS.pinsR ⟨s'', PS.idx, hSJ⟩ hS6.prep.run hS6.run hI hCJ

end L.Checker
