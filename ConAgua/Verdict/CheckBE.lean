module

public import ConAgua.Checker.VerdictTop
public import ConAgua.Verdict.ThreadsE
import ConAgua.Checker.CheckARun
import ConAgua.Checker.VerdictEntry1
import ConAgua.Checker.LoopStage
import ConAgua.Checker.RomProgInit
import ConAgua.L.Blocks
import all ConAgua.Checker.Entry
import ConAgua.Front.FrontRunRef

@[expose] public section

/-!
# Entry 2's `check_b` fails only where the twin's jobs do (lane verdicts-b, stage 3 of ronsync2)

The error halves of `ParDriverL.lean`'s `checkJobs_seqT`, `checkB_seq` and `ParDriverTwin.lean`'s
`checkMode2_seq`: `check_jobs(0, k)` on a memory that agrees with the flushed memory after the
index build on what the jobs name (`invoke_agree`, the same error), the ROM substitution
(`invoke_subPB`), the loop's error claim (`checkJobs_ref` under `JobG`, con-ron's fold invariant
at each job's view from the jobs before it, `seq_prefix`) and the worker (`twinFailsV_of_sameEnter`).
Hence `entry2Verdict_of`: entry 2's verdict claim, given `check_decl`'s program facts and the
jobs' error claims at every phase A.
-/

set_option experimental.vcgen true

open ConRon.Arena ConRon.Bridge
open Std.WP
open scoped Lean.Order

namespace L.Checker

open L L.Arena L.Rom

local notation "VM" => ConLeche.CheckMode.verified

universe w

/-- **`check_jobs(0, k)` after the flush, error half of `checkJobs_seqT`**: from a memory that is
the flush of one agreeing with `m` on every array the jobs name, a failing run claims the twin's
jobs over every record failing from the index state's worker. -/
theorem checkJobs_seqE {b pb : ByteArray}
    {sz : TieredArray → Nat} {PA : PhaseA b} {m₇ m : Mem}
    (hF : FoldAt b pb sz PA m₇ m)
    (hJP : JobProg PA.ipins (dnOf PA.sE.store) PA.ds (Prog.subPB pb.data.toList checkerProg))
    (hJG : JobG PA.ipins (dnOf PA.sE.store) PA.ds (Prog.subPB pb.data.toList checkerProg))
    (n : Nat) (hn : n ≤ 2 ^ 62) (hi : Word) (hhi : hi.toNat = PA.ds.size) (x y : Word) :
    ⦃fun s => x = 0 ∧ y = hi ∧ ∃ X, FlushOK X ∧ s.mem = flushMem X ∧
      ∀ a, phaseBS a = true → X.arr64 a = m.arr64 a⦄
    invoke checkerProg (exec checkerProg n) "check_jobs" [x, y]
    ⦃fun _ _ => True;
      ErrClaimV (checkJobList VM PA.ipins none PA.I PA.ds (List.range PA.ds.size)) PA.sF.worker⦄ := by
  apply M.triple_of_run' (fun _ _ _ _ _ => trivial)
  rintro s e ⟨rfl, hy, X, hfx, hsX, hXm⟩ hrun
  rw [hy] at hrun
  let p := Prog.subPB pb.data.toList checkerProg
  -- the memory: the flush of `m`, with the run's globals
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
  have hJ0 : JobR PA.ipins (dnOf PA.sE.store) PA.ds none PA.I (flushMem m)
      { PA.sF with caches := Caches.empty } := hF.jobR hfok
  have hby : (flushMem m).bytes = m₇.bytes := by rw [flushMem_bytes, hF.bytes]
  generalize flushMem m = F at hJ0 hag hby
  let s₂ : St := ⟨⟨F.bytes, F.words, s.mem.glob⟩, s.loc⟩
  have hAg : Agree phaseBS (fun _ => false) s.mem s₂.mem :=
    ⟨fun a ha => hag a ha, fun _ h => absurd h (by simp), rfl⟩
  have hrun₂ := invoke_agree_err checkerProg_phaseBReads check_jobs_mem_phaseBJobFns hAg rfl hrun
  have hPB : s₂.mem.arr8 L.Rom.PB = pb.data.toList.toArray := by
    show F.bytes L.Rom.PB = _
    rw [hby, ← Mem.arr8, hF.r7.since.keep.arr8]
    exact loadMem_pb b pb sz
  rw [← L.Rom.invoke_subPB (bs := pb.data.toList) checkerProg_noSt8PB n _ _ (s := s₂) hPB] at hrun₂
  have hc := L.Front.callE_of_run_err hrun₂
  -- the twin's side
  let a₀ : AState := { PA.sF with caches := Caches.empty }
  obtain ⟨pinsP, dsP, hst, hrec, hpp, hden, hPD, hH⟩ := poolHyps_of_phaseA PA
    (JobRel PA.ipins (dnOf PA.sE.store) PA.ds none PA.I a₀) (RecCall p)
  obtain ⟨hA, hB, hC, hD, hE⟩ := PA.pfx
  obtain ⟨-, -, -, -, -, hpd, _rc, _preC, -, hden0⟩ :=
    ConRon.Bridge.stages_frame (chunks := [b]) hA hB hC hD hE
  have hFD : FrontDecls PA.ds := frontDecls_of_prefix PA.pfx
  have hLD : DeclsLpsDn (dnOf PA.sE.store) PA.ds := declsLpsDn_dnOf hpd ⟨_, hden0⟩
  have hdn : DnPers (dnOf PA.sE.store) := fun k x hk => by
    simp only [dnOf] at hk; split at hk
    · assumption
    · cases hk
  have hds : PA.ds.size < 2 ^ 64 := by rw [← hhi]; exact UInt64.toNat_lt hi
  have H := hH (recCall_stepE (J := none) hJP hFD hLD hdn hpp hds hden hPD hrec (fun h => absurd h (by simp)))
  have hJ : JobR PA.ipins (dnOf PA.sE.store) PA.ds none PA.I s₂.mem a₀ := hJ0.setGlob _
  have hw0 : WorkerOK PA.sF a₀ := ⟨⟨hst.wf⟩, PExt.of_ext (Ext.refl _), rfl, rfl⟩
  -- the jobs before a job accepted in order: the fold's prefix, a worker state
  have hseq : ∀ (c t : Nat) (a a' : AState), WorkerOK PA.sF a →
      (PrefixOK pinsP dsP t ∧ ((ConLeche.Cached.recsConsts (dsP.take t)).map (·.name)).Nodup) →
      t + c ≤ PA.ds.size →
      checkJobList VM PA.ipins none PA.I PA.ds (List.range' t c) a = .ok (.ok (), a') →
      WorkerOK PA.sF a' ∧ PrefixOK pinsP dsP (t + c) ∧
        ((ConLeche.Cached.recsConsts (dsP.take (t + c))).map (·.name)).Nodup := by
    intro c
    induction c with
    | zero =>
      intro t a a' hw hP _ hl
      rw [List.range'_zero] at hl
      cases hl
      exact ⟨hw, hP⟩
    | succ c ih =>
      intro t a a' hw ⟨hPt, hndt⟩ hle hl
      have htk : t < PA.ds.size := by omega
      rw [List.range'_succ] at hl
      cases hrj : recordJob VM PA.ipins none PA.I t PA.ds[t] a with
      | error ce =>
        have e1 : (checkJobList VM PA.ipins none PA.I PA.ds (t :: List.range' (t + 1) c)) a =
            .ok (.error (ce, t), AState.abandoned) := by
          simp only [checkJobList, runJob, Array.getElem?_eq_getElem htk, hrj]
        rw [show (checkJobList VM PA.ipins none PA.I PA.ds (t :: List.range' (t + 1) c)) a = _ from hl] at e1
        cases e1
      | ok v =>
        obtain ⟨u, a₁⟩ := v
        cases u
        rw [checkJobList_cons_ok htk hrj] at hl
        obtain ⟨htk', hdk⟩ := H.hden t htk
        obtain ⟨hw₁, env', F, hd⟩ := job_spec H.hrec H.hpp H.hpinsOK H.hpersPins H.hpins H.hpd
          H.hI H.hpI hw htk htk' hdk hPt.envWF hndt hrj
        have := ih (t + 1) a₁ a' hw₁ (PrefixOK.step H.hpush htk' hPt hd hndt) (by omega) hl
        rwa [show t + 1 + c = t + (c + 1) by omega] at this
  have h0 : PrefixOK pinsP dsP 0 ∧ ((ConLeche.Cached.recsConsts (dsP.take 0)).map (·.name)).Nodup := by
    have h0 : (ConLeche.Cached.recsConsts ([] : List ConLeche.Declaration)).length = 0 := by
      have := (ConLeche.Cached.buildIndex_spec (#[] : Array ConLeche.Declaration)).next
      simpa [ConLeche.Cached.buildIndex] using this.symm
    refine ⟨⟨0, fun _ _ => rfl⟩, ?_⟩
    rw [List.take_zero, List.eq_nil_of_length_eq_zero h0]
    exact List.nodup_nil
  have hden' : ∀ x ∈ PA.ds.toList, PersDecl x ∧ ∃ d, Frontend.denoteDecl a₀.store x = some d := hden
  have h := checkJobs_ref (J := none) (I := PA.I) hJP hFD hLD hdn hpp hden' hPD hrec (fun h => absurd h (by simp)) (hi := hi) (j := 0)
    (by omega) hn ⟨hJ, PExt.of_ext (Ext.refl _), rfl⟩
    (fun t a' _ h2 h3 => by
      simp only [UInt64.toNat_zero, Nat.sub_zero] at h3 h2
      obtain ⟨hw', hP, hnd⟩ := hseq t 0 a₀ a' hw0 h0 (by omega) h3
      rw [Nat.zero_add] at hP hnd
      obtain ⟨htk', -⟩ := H.hden t (by omega)
      exact worker_foldOK H.hpinsOK H.hpersPins H.hI H.hpI htk' hP hnd hw')
  have h' := RefC.run_err (checkJobs_specE p hJP.check_jobs n ⟨s₂.mem, Locals.init []⟩ 0 hi)
    (fun e h0 => ErrClaimV.of_cls0 h0) trivial (JobGL.none hJG) h hc
  simp only [UInt64.toNat_zero, Nat.sub_zero, hhi, ← List.range_eq_range'] at h'
  exact fun hk => twinFailsV_of_sameEnter sameEnter_worker.symm (h' hk)

/-- **Entry 2 in place, `check_b`, error half of `checkB_seq`.** -/
theorem checkB_seqE {b pb : ByteArray}
    {sz : TieredArray → Nat} {PA : PhaseA b} {m₇ m : Mem}
    (hF : FoldAt b pb sz PA m₇ m)
    (hJP : JobProg PA.ipins (dnOf PA.sE.store) PA.ds (Prog.subPB pb.data.toList checkerProg))
    (hJG : JobG PA.ipins (dnOf PA.sE.store) PA.ds (Prog.subPB pb.data.toList checkerProg))
    (n : Nat) (hn : n ≤ 2 ^ 62) (hi : Word) (hhi : hi.toNat = PA.ds.size) (s₀ : St)
    (hw : ∀ a, phaseBS a = true → s₀.mem.arr64 a = m.arr64 a)
    (hlo : s₀.mem.glob PLO = 0) (hhi' : s₀.mem.glob PHI = hi) (hctlf : (s₀.mem.arr64 CTLF).size = 0) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "check_b" []
    ⦃fun _ _ => True;
      ErrClaimV (checkJobList VM PA.ipins none PA.I PA.ds (List.range PA.ds.size)) PA.sF.worker⦄ := by
  have hl : (UInt64.toNat (s₀.mem.len64 CTLF)) = 0 := by simp [Mem.len64, hctlf]
  have hlo' : s₀.mem.glob ⟨9⟩ = 0 := hlo
  have hhi'' : s₀.mem.glob ⟨11⟩ = hi := hhi'
  rw [invoke_eq _ checkerProg_lookup_check_b]
  simp only [callFn, checkBL]
  cases n with
  | zero => vcgen [exec] <;> simp [ErrClaimV.of_cls0]
  | succ n =>
    have hJ := checkJobs_seqE hF hJP hJG n (by omega) hi hhi
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
      | (trace_state; fail "CheckBE.checkB_seqE: no closing tactic applies")

/-- **Entry 2 in place, `check` with the mode word `2`, error half of `checkMode2_seq`.** -/
theorem checkMode2_seqE {b pb : ByteArray}
    {sz : TieredArray → Nat} {PA : PhaseA b} {m₇ m : Mem}
    (hF : FoldAt b pb sz PA m₇ m)
    (hJP : JobProg PA.ipins (dnOf PA.sE.store) PA.ds (Prog.subPB pb.data.toList checkerProg))
    (hJG : JobG PA.ipins (dnOf PA.sE.store) PA.ds (Prog.subPB pb.data.toList checkerProg))
    (n : Nat) (hn : n ≤ 2 ^ 62) (hi : Word) (hhi : hi.toNat = PA.ds.size) (s₀ : St)
    (hw : ∀ a, phaseBS a = true → s₀.mem.arr64 a = m.arr64 a) (hmode : s₀.mem.glob MODE = 2)
    (hlo : s₀.mem.glob PLO = 0) (hhi' : s₀.mem.glob PHI = hi) (hctlf : (s₀.mem.arr64 CTLF).size = 0) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "check" []
    ⦃fun _ _ => True;
      ErrClaimV (checkJobList VM PA.ipins none PA.I PA.ds (List.range PA.ds.size)) PA.sF.worker⦄ := by
  rw [invoke_eq _ checkerProg_lookup_check']
  simp only [callFn, checkL]
  cases n with
  | zero => vcgen [exec] <;> simp [ErrClaimV.of_cls0]
  | succ n =>
    have hB : ⦃fun s => s.mem = s₀.mem⦄ invoke checkerProg (exec checkerProg n) "check_b" []
        ⦃fun _ _ => True;
          ErrClaimV (checkJobList VM PA.ipins none PA.I PA.ds (List.range PA.ds.size)) PA.sF.worker⦄ := by
      apply M.triple_of_run' (fun _ _ _ _ _ => trivial)
      intro s₁ e hs hrun
      exact M.of_run_err (P := fun x => x = s₁) rfl hrun
        (checkB_seqE hF hJP hJG n (by omega) hi hhi s₁ (hs ▸ hw) (hs ▸ hlo) (hs ▸ hhi')
          (hs ▸ hctlf))
    have hmode' : s₀.mem.glob ⟨8⟩ = 2 := hmode
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, hB,
      (callE_spec checkerProg n "check_a" [1] ·), (callE_spec checkerProg n "check_a" [0] ·),
      (callE_spec checkerProg n "check_c1" [] ·), (callE_spec checkerProg n "check_c2" [] ·),
      (callE_spec checkerProg n "check_c3" [·] ·)]
    all_goals (try simp only [Cmp.eval, beq_iff_eq] at *)
    all_goals first
      | exact ErrClaimV.of_cls0 (by decide)
      | (simp_all (config := { decide := true }); done)
      | (simp_all [St.setLoc]; done)
      | (trace_state; fail "CheckBE.checkMode2_seqE: no closing tactic applies")

open ConAgua.Final in
/-- **Entry 2's verdict claim** (`Entry2Verdict`), given `check_decl`'s program facts
(`CheckerCd`) and the jobs' error claims (`JobG`) at every phase A: the
failing run of `check_b` over every record is the twin's jobs failing (`TwinVerdict.jobs`). -/
theorem entry2Verdict_of (hCd : CheckerCd)
    (hJG : ∀ (b pb : ByteArray) (PA : PhaseA b), pb.size < 2 ^ 63 → PbPre pb →
      JobG PA.ipins (dnOf PA.sE.store) PA.ds (Prog.subPB pb.data.toList checkerProg)) :
    Entry2Verdict checkerProg := by
  intro b pb sz hin N₁ hN₁ rs₁ m₁ h₁ hge N₂ hN₂ w hw hmode hlo hhi hctlf _ e hrun hk
  have hr : rs₁.headD 0 ≠ 1 := fun e => by rw [e] at hge; simp at hge
  obtain ⟨PA, m₇, m, hF, -, hm₁, hres⟩ := checkA_run b pb sz hin 3 (Or.inr rfl) N₁ hN₁ rs₁ m₁ h₁ hr
  have hfr := parCompactMem_out m (modeFlag 3)
  rw [← hm₁] at hfr
  have hw' : ∀ a, phaseBS a = true → w.arr64 a = m.arr64 a := fun a ha => by
    rw [hw a ha, hfr.arr a (fun e => by subst e; revert ha; decide)]
  have hsz : PA.ds.size < 2 ^ 63 := by
    have := hF.build.decls.room; have := hF.build.decls.dsize; omega
  have hk' : (rs₁.headD 0 - 9223372036854775808).toNat = PA.ds.size := by
    have e : (9223372036854775808 : Word) + UInt64.ofNat PA.ds.size - 9223372036854775808 =
        UInt64.ofNat PA.ds.size := by rw [UInt64.add_comm, UInt64.add_sub_cancel]
    rw [hres, e, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
  have hJP := jobProg_of_cd hCd PA hin.2.2.1 hF.r7.since.pbpre
  have hJG' := hJG b pb PA hin.2.2.1 hF.r7.since.pbpre
  have hr' := run_err hrun
  have hc := M.of_run_err (P := fun x => x = ⟨w, Locals.init []⟩) rfl hr'
    (checkMode2_seqE hF hJP hJG' N₂ hN₂ _ hk' ⟨w, Locals.init []⟩ hw' hmode hlo hhi hctlf)
  obtain ⟨hA, hBp, hC, hD, hE⟩ := PA.pfx
  exact TwinVerdict.jobs hA hBp hC hD hE PA.idx (hc hk)

end L.Checker
