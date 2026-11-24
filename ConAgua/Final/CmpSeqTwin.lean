module

public import ConAgua.Checker.CmpSPhaseThr
public import ConAgua.Checker.CmpSeqJobs
public import ConAgua.Checker.CmpSeqErr
public import ConAgua.Final.CompareTwinI
import ConAgua.Checker.CrsProgPB
import ConAgua.Checker.RomProgInit
import ConAgua.Checker.RomProg0
import ConAgua.Checker.JobsProg
import ConAgua.Checker.AsmFinal
import ConAgua.Final.DrvFinal
import ConAgua.Arena.FreezeTrunc
import ConAgua.Verdict.CmpVSJobs
import ConAgua.Verdict.CmpVModes
import ConAgua.Checker.CmpVerdictNv
import all ConAgua.Checker.Entry

@[expose] public section

/-!
# The sequential compared run at the L level (lane compare2, the sJ variant)

`ca_start_c`'s L runs (`CmpAccS`, `CmpErrS`, `Final/CmpAbi.lean`): the front (modes `4`, `5`),
mode `6` (the challenge's preparation, index, `par_compact(0)`), then `check` in place with the mode
word `8` (the solution's jobs, `check_bs`) and `9` (the challenge's, `check_bc`).

* `cmpFront_run`: the front returning `2^63 + |dsS|` is the solution's index build (`checkC1_run`,
  `checkC2_run`); `cmpFrontAcc45_false`: the front never accepts.
* `cmpAccS_twin`: an accept is `TwinComparesAcceptsSeqI`: the solution's jobs in order from
  `sI.worker` (mode `8`: `JobM.csViewS`, `cq_jobsOk`), then the challenge's continuing on that
  worker (mode `9`: `cq_phaseC`, `cq_jobsOk`).
-/

namespace ConAgua.Final

open L L.Compiler L.Checker L.Arena L.Rom
open ConRon.Arena ConRon.Bridge

local notation "VM" => ConLeche.CheckMode.verified

/-- **TEMP stand-in** (H2d, compare2-freeze): `cmp_sstash`'s copies of the solution's records,
firsts, pool and frozen words survive mode `6`'s stages. -/
theorem _root_.L.Checker.F6.csStash_standin {bC bS : ByteArray} {PS : PhaseS bC bS} {m : Mem} {c : Word}
    {m9 : Mem} (h : F6 PS m c m9) : CsStash m m9 := by
  sorry

theorem cmp_absz : ∀ s, abiSz checkerTab s < 2 ^ 64 := fun s => by
  have := abiSz_le checkerTab_abiOk s; simp only [abiWords] at this; omega

/-- **The front returning `2^63` or more** is the solution's index build after the challenge's
first parse (`checkC1_run`, `checkC2_run`; mode `5` leaves its memory `m` as it is). -/
theorem cmpFront_run (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64) {rs5 : List Word}
    {m5 : Mem} (hf : CmpFront45 checkerTab checkerProg MODE bC bS pb rs5 m5) :
    ∃ (PS : PhaseS bC bS) (m₇ m : Mem), FoldOn bS pb (abiSz checkerTab) PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m ∧
      Stash m PS.pre PS.rC ∧ Keep6 m PS.pre ∧ m5 = m ∧
      rs5.headD 0 = 9223372036854775808 + UInt64.ofNat PS.dsS.size := by
  obtain ⟨hbC, hpb, hbS, rs4, m4, h4, hge4, h5, hge5⟩ := hf
  have hN : abiFuel < 2 ^ 62 := by simp [abiFuel]
  have hr4 : rs4.headD 0 ≠ 1 := fun e => by rw [L.getD_zero, e] at hge4; simp at hge4
  have hr5 : rs5.headD 0 ≠ 1 := fun e => by rw [L.getD_zero, e] at hge5; simp at hge5
  obtain ⟨-, hA4⟩ := checkC1_run bC bS pb _ ⟨h64, hbC, hpb, cmp_absz⟩ abiFuel hN rs4 m4 h4 hr4
  exact checkC2_run bC bS pb _ ⟨h64, hbS, hpb, cmp_absz⟩ abiFuel hN m4 hA4 rs5 m5 h5 hr5

/-- **The front never accepts**: mode `4` returns `2^63` and mode `5` `2^63 + |dsS|`. -/
theorem cmpFrontAcc45_false (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (h : CmpFrontAcc45 checkerTab checkerProg MODE bC bS pb) : False := by
  obtain ⟨hbC, hpb, rs4, m4, h4, hor⟩ := h
  have hN : abiFuel < 2 ^ 62 := by simp [abiFuel]
  rcases hor with hA4 | ⟨hge4, hbS, rs5, m5, h5, hA5⟩
  · rw [L.getD_zero] at hA4
    have hr : rs4.headD 0 ≠ 1 := by rw [hA4]; decide
    have := (checkC1_run bC bS pb _ ⟨h64, hbC, hpb, cmp_absz⟩ abiFuel hN rs4 m4 h4 hr).1
    rw [hA4] at this; exact absurd this (by decide)
  · rw [L.getD_zero] at hA5
    have hr4 : rs4.headD 0 ≠ 1 := fun e => by rw [L.getD_zero, e] at hge4; simp at hge4
    obtain ⟨-, hA4⟩ := checkC1_run bC bS pb _ ⟨h64, hbC, hpb, cmp_absz⟩ abiFuel hN rs4 m4 h4 hr4
    have hr : rs5.headD 0 ≠ 1 := by rw [hA5]; decide
    obtain ⟨PS, m₇, m, hF, -, -, -, hres⟩ :=
      checkC2_run bC bS pb _ ⟨h64, hbS, hpb, cmp_absz⟩ abiFuel hN m4 hA4 rs5 m5 h5 hr
    have hn : PS.dsS.size < 2 ^ 63 := by
      have := hF.build.decls.room; have := hF.build.decls.dsize; omega
    exact high_ne_accept (by rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]; exact hn)
      (hres.symm.trans hA5)

/-- `callE` at the ROM's program is `callE` at the program on a memory holding the ROM. -/
theorem cq_callE_subPB {bs : List UInt8} {n : Nat} {f : FnName} {vs : List Word} {m : Mem}
    (hPB : m.arr8 L.Rom.PB = bs.toArray) :
    callE (Prog.subPB bs checkerProg) n f vs m = callE checkerProg n f vs m := by
  unfold callE
  rw [L.Rom.invoke_subPB checkerProg_noSt8PB n f vs (s := ⟨m, Locals.init []⟩) hPB]

/-- A returning call at the checker keeps the bytes. -/
theorem cq_callE_bytes {n : Nat} {f : FnName} {vs : List Word} {m m' : Mem} {r : List Word}
    (h : callE checkerProg n f vs m = .ok (r, m')) : m'.bytes = m.bytes := by
  have t := Triple.keep checkerProg_noSt8 (n := n) (f := f) (vs := vs)
    (s₀ := ⟨m, Locals.init []⟩) (Q := fun _ _ => True)
    (M.triple_of_run fun _ _ _ _ _ => trivial)
  obtain ⟨s', hs', hk⟩ := triple_of_callE t h
  rw [← hs']
  exact hk.2.1.1

/-- **Mode `6` after the front** (`checkC3_run` on mode `5`'s memory): the frozen memory `m9`
(`F6`), mode `6`'s memory `parCompactMem m9 0`, `2^63 + c`. -/
theorem cmpMode6_run {bC bS pb : ByteArray} (hpb : pb.size < 2 ^ 63) (PS : PhaseS bC bS) {m₇ m : Mem}
    (hF : FoldOn bS pb (abiSz checkerTab) PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m)
    (hst : Stash m PS.pre PS.rC) (hk6 : Keep6 m PS.pre) {rs6 : List Word} {m6 : Mem}
    (h6 : cmpRun checkerProg (m.setG MODE 6) = .ok (rs6, m6)) :
    ∃ c m9, F6 PS m c m9 ∧ m6 = parCompactMem m9 0 ∧ m9.bytes = m.bytes ∧
      rs6.headD 0 = (9223372036854775808 : Word) + c ∧ c.toNat < 2 ^ 63 := by
  have hN : abiFuel < 2 ^ 62 := by simp [abiFuel]
  have hsz6 : ∀ g ≤ 2, abiSz checkerTab (sixArr g) = abiSz checkerTab (eixArr g) ∧
      abiSz checkerTab (stxArr g) = abiSz checkerTab (tixArr g) := by
    intro g hg
    rcases (show g = 0 ∨ g = 1 ∨ g = 2 by omega) with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
  have hO : OutEq m (m.setG MODE 6) := (⟨fun _ _ => rfl, fun _ => rfl, rfl⟩ : OutEq m m).setG MODE 6
  obtain ⟨c, hpost, hres6⟩ := checkC3_run PS hF hst hk6 cmp_absz hpb hsz6 hO 6 0
    (Or.inl ⟨rfl, rfl⟩) (by simp [Mem.setG]) abiFuel hN rs6 m6 h6
  obtain ⟨m9, hF6, -, rfl⟩ := hpost.1 rfl
  have hc63 : c.toNat < 2 ^ 63 := by
    obtain ⟨m2, m3, dsC, sG, res, m4', I, a', h, -⟩ := F6.jobM hF hF6
    have := h.count.1
    have := h.decls.room; have := h.decls.dsize
    simp only [List.size_toArray] at *
    omega
  refine ⟨c, m9, hF6, rfl, ?_, hres6, hc63⟩
  rw [← (parCompactMem_out m9 0).bytes, run_check_bytes h6]
  rfl

/-- The job program facts at the ROM's program, for any records. -/
theorem cq_jobProg {pb : ByteArray} (hpb : pb.size < 2 ^ 63)
    (hpre : pb.data.toList = romData ++ pb.data.toList.drop romData.length) (ipins : List INatOpPinSet)
    {dn : NIdx → Option ConLeche.Name} (ds : Array IDeclaration) (hinj : L.Ind.DnInj dn)
    (hq : L.Ind.QuotDn dn) :
    JobProg ipins dn ds (Prog.subPB pb.data.toList checkerProg) ∧
      CdProg ipins dn ds (Prog.subPB pb.data.toList checkerProg) := by
  have hr : RomOK pb.data.toList := by simpa [RomOK] using hpb
  obtain ⟨hdf, hind⟩ := checkerCdG_proved pb ipins dn ds hpb hpre hinj
  have hcd := checkerProg_cdProgPB pb.data.toList hr hpre hinj hq hdf hind
  exact ⟨checkerProg_jobProgPB pb.data.toList hr hpre hcd (checkerProg_canonPB _), hcd⟩

/-- `seqMemW`'s globals. -/
theorem cq_seqNext_glob (M : Mem) (w lo hi : Word) :
    (seqNext M MODE PLO PHI w lo hi).glob MODE = w ∧ (seqNext M MODE PLO PHI w lo hi).glob PLO = lo ∧
      (seqNext M MODE PLO PHI w lo hi).glob PHI = hi := by
  simp [seqNext, Mem.setG]

/-- **The sequential compared run's phases, refined**: after the front and mode `6` (returning
`2^63 + c`), the stages up to the challenge's index state `sI` are the twin's, and mode `8` in
place (the solution's jobs, from the switched memory in the job relation, `JobM.cqViewS`) fails
only where the twin's solution jobs from `sI.worker` do; returning, they accept (ending in `sJ`),
and mode `9` in place (the challenge's view restored, `cq_phaseC`) accepts or fails as the twin's
challenge jobs continuing from `sJ` do. -/
theorem cq_seq (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (hQ : CqSeqProg checkerProg) {rs5 : List Word} {m5 : Mem}
    (hf : CmpFront45 checkerTab checkerProg MODE bC bS pb rs5 m5) {rs6 : List Word} {m6 : Mem}
    (h6 : cmpRun checkerProg (m5.setG MODE 6) = .ok (rs6, m6)) :
    ∃ (pins : List ConLeche.NatOpPinSet) (ipins : List INatOpPinSet) (dsS : Array IDeclaration)
      (recsC : List IDeclaration) (IS IC : IStreamIndex) (sI : AState),
      CmpStagesI bC bS pins ipins dsS recsC IS IC sI ∧ rs6.getD 0 0 ≠ ACCEPT ∧
      (∀ e, cmpRun checkerProg (seqMemW m6 MODE PLO PHI OUT HDRF CTLF hdrHw 8 0
          (rs5.getD 0 0 - 9223372036854775808)) = .error e → e.cls ≠ 0 →
        TwinFailsV (checkJobList VM ipins none IS dsS (List.range dsS.size)) sI.worker e.cls) ∧
      ∀ rs8 m8, cmpRun checkerProg (seqMemW m6 MODE PLO PHI OUT HDRF CTLF hdrHw 8 0
          (rs5.getD 0 0 - 9223372036854775808)) = .ok (rs8, m8) →
        ∃ sJ, checkJobList VM ipins none IS dsS (List.range dsS.size) sI.worker = .ok (.ok (), sJ) ∧
          (∀ rs9 m9', cmpRun checkerProg (seqNext m8 MODE PLO PHI 9 0 (rs6.getD 0 0 - 9223372036854775808)) =
              .ok (rs9, m9') →
            ∃ sK, checkJobList VM ipins (some (solutionOf IS recsC)) IC recsC.toArray
              (List.range recsC.toArray.size) sJ = .ok (.ok (), sK)) ∧
          ∀ e, cmpRun checkerProg (seqNext m8 MODE PLO PHI 9 0 (rs6.getD 0 0 - 9223372036854775808)) =
              .error e → e.cls ≠ 0 →
            TwinFailsV (checkJobList VM ipins (some (solutionOf IS recsC)) IC recsC.toArray
              (List.range recsC.toArray.size)) sJ e.cls := by
  have hpb : pb.size < 2 ^ 63 := hf.2.1
  obtain ⟨PS, m₇, m, hF, hst, hk6, rfl, hres5⟩ := cmpFront_run bC bS pb h64 hf
  obtain ⟨c, m9, hF6, rfl, hb9, hres6, hc63⟩ := cmpMode6_run hpb PS hF hst hk6 h6
  have hN62 : abiFuel ≤ 2 ^ 62 := by simp [abiFuel]
  -- the counts
  have hn : PS.dsS.size < 2 ^ 63 := by
    have := hF.build.decls.room; have := hF.build.decls.dsize; omega
  have ekS : rs5.getD 0 0 - 9223372036854775808 = UInt64.ofNat PS.dsS.size := by
    rw [L.getD_zero, hres5, UInt64.add_comm, UInt64.add_sub_cancel]
  have hkS : (UInt64.ofNat PS.dsS.size).toNat = PS.dsS.size :=
    UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
  have ekC : rs6.getD 0 0 - 9223372036854775808 = c := by
    rw [L.getD_zero, hres6, UInt64.add_comm, UInt64.add_sub_cancel]
  have hA6 : rs6.getD 0 0 ≠ ACCEPT := fun e => by
    rw [L.getD_zero] at e; exact high_ne_accept hc63 (hres6.symm.trans e)
  rw [ekS, ekC]
  -- the twin's side of mode `6`
  obtain ⟨m2, m3, dsC, sG, res, m4', I, a', hS6, hI, -⟩ := F6.jobM hF hF6
  obtain ⟨hJM9, hwf, hoff, -⟩ := F6.jobMAt hF hF6 hS6 hI
  obtain ⟨-, hxFG, -, -, ho⟩ := hS6.phase.out
  have hoS := StagesOut.cmp PS.pfx PS.pinsR
  obtain ⟨dsSP, hdenS⟩ := hoS.den
  obtain ⟨-, hxF, -, -, -, -⟩ :=
    buildIndex_run constsSpec tablesSpec hoS.drv hoS.pp hoS.off hoS.pd hdenS PS.idx
  have hxEG : Ext PS.sE.store sG.store := hxF.trans hxFG
  obtain ⟨_, hdenC⟩ := ho.den
  obtain ⟨-, -, -, -, hIC, hpIC⟩ :=
    buildIndex_run constsSpec tablesSpec ho.drv ho.pp ho.off ho.pd hdenC hI
  have hpre := hF.r7.since.pbpre
  have hinj : L.Ind.DnInj (dnOf sG.store) := dnOf_inj ho.drv.state.wf
  have hq : L.Ind.QuotDn (dnOf sG.store) := by
    obtain ⟨k, hk, hd⟩ := ho.quot
    exact ⟨k, by simp only [dnOf, hk]; exact hd⟩
  have hr : RomOK pb.data.toList := by simpa [RomOK] using hpb
  have hdn : DnPers (dnOf sG.store) := fun k x hk => by
    simp only [dnOf] at hk; split at hk
    · assumption
    · cases hk
  have hLD : DeclsLpsDn (dnOf sG.store) PS.dsS :=
    declsLpsDn_dnOf hoS.pd ⟨_, ConRon.Bridge.Frontend.denoteDecls_ext hxEG _ _ hdenS⟩
  obtain ⟨hJPS, -⟩ := cq_jobProg hpb hpre PS.ipins PS.dsS hinj hq
  obtain ⟨hJPC, hcdC⟩ := cq_jobProg hpb hpre PS.ipins res.toArray hinj hq
  have hJG : ∀ ds : Array IDeclaration, JobG PS.ipins (dnOf sG.store) ds (Prog.subPB pb.data.toList checkerProg) :=
    fun _ => jobG_ofDn hinj hq pb hpb hpre
  have hcnt : c.toNat = res.toArray.size := by simpa using hS6.count.1
  -- mode `8`'s memory and the frozen side `N`
  let W8 := seqMemW (parCompactMem m9 0) MODE PLO PHI OUT HDRF CTLF hdrHw 8 0 (UInt64.ofNat PS.dsS.size)
  let N : Mem := ⟨m9.bytes, m9.words, W8.glob⟩
  have hAg8 : Agree phaseBPa (fun _ => false) W8 N := ⟨fun a ha => by
      have h1 : ¬ (a = ↑OUT ∨ a = ↑CTLF) := by rintro (rfl | rfl) <;> revert ha <;> decide
      have h2 : a ≠ ↑HDRF := by rintro rfl; revert ha; decide
      show (seqMem0 (parCompactMem m9 0) OUT HDRF CTLF hdrHw).arr64 a = m9.arr64 a
      rw [seqMem0_arr64]; simp only [h1, h2, ite_false]
      exact (parCompactMem_out m9 0).arr a (fun e => h1 (.inl e)),
    fun _ h => absurd h (by simp), rfl⟩
  obtain ⟨g8, g8lo, g8hi⟩ := cq_seqNext_glob (seqMem0 (parCompactMem m9 0) OUT HDRF CTLF hdrHw) 8 0
    (UInt64.ofNat PS.dsS.size)
  have eglo : (cqSM N).glob PLO = 0 := by rw [cqSM_glob]; exact g8lo
  have eghi : (cqSM N).glob PHI = UInt64.ofNat PS.dsS.size := by rw [cqSM_glob]; exact g8hi
  have hPBm : m5.arr8 L.Rom.PB = pb.data.toList.toArray := by
    show m5.bytes L.Rom.PB = _
    rw [hF.bytes, ← Mem.arr8, hF.r7.since.keep.arr8]; exact loadMem_pb bS pb _
  have hPBN : (cqSM N).arr8 L.Rom.PB = pb.data.toList.toArray := by
    show (cqSM N).bytes L.Rom.PB = _
    rw [cqSM_bytes]; show m9.bytes L.Rom.PB = _; rw [hb9]; exact hPBm
  -- the solution's jobs' start
  have hJMN : JobM PS.ipins (dnOf sG.store) res.toArray (some (solutionOf PS.IS res)) I N a' :=
    hJM9.frame0 (memFrame_glob m9 _)
  have hStash : CsStash m5 N := by
    have h := F6.csStash_standin hF6
    exact ⟨h.decl, h.firsts, h.dlp, h.frz⟩
  obtain ⟨pinsP, dsP, hstI, hrec, hpp, hden, hPD, -, -, -, hH⟩ :=
    poolHypsS_I hS6.phase hI (fun (_ : Unit) (_ : AState) => False) (fun _ _ _ => False)
  have HS := hH (fun _ _ _ _ _ h => h.elim)
  have hKS : IndexKeysIn N PS.IS := indexKeysIn_of hJMN.arena.base HS.hI HS.hpI
  have hKC : IndexKeysIn N I := indexKeysIn_of hJMN.arena.base hIC hpIC
  let a₀ : AState := { a' with caches := Caches.empty }
  have hJR0 : CqRowsSOK N → CqTailSOK (cqRowsS N) → CqCtlSOK (cqBankSM N) → FlushOK (cqCtlSM (cqBankSM N)) →
      JobR PS.ipins (dnOf sG.store) PS.dsS none PS.IS (cqSM N) a₀ := fun hR hT hCt hFl =>
    (hJMN.cqViewS rfl hStash hF.build.idx hF.build.decls hF.frozen hF.fsize hKS hKC hR hT hCt).flushR
      hwf hoff hFl
  have hw0 : WorkerOK a' a₀ := ⟨⟨hstI.wf⟩, PExt.of_ext (Ext.refl _), rfl, rfl⟩
  refine ⟨PS.pins, PS.ipins, PS.dsS, res, PS.IS, I, a', hS6.stagesI hI, hA6, ?_, ?_⟩
  · -- mode `8` fails
    intro e h8 hk0
    rcases cq_check8_err hQ hAg8 g8 hN62 h8 with h0 | ⟨hR, hT, hCt, hFl, k, hk, hcall⟩
    · exact absurd h0 hk0
    rw [eglo, eghi, ← cq_callE_subPB hPBN] at hcall
    exact twinFailsV_of_sameEnter sameEnter_worker.symm
      (cq_jobsErr (J := none) hJPS hoS.front hLD hdn hpp hden hPD hrec (fun h => absurd h (by simp))
        (JobGJ.none (hJG _)) hkS hk ⟨hJR0 hR hT hCt hFl, PExt.of_ext (Ext.refl _), rfl⟩ (seq_foldS HS hw0)
        hcall hk0)
  intro rs8 m8 h8
  obtain ⟨k, r', N', hk, hAg8', -, hR, hT, hCt, hFl, -, -, hcall⟩ := cq_check8 hQ hAg8 g8 hN62 h8
  rw [eglo, eghi] at hcall
  have hcallP := hcall
  rw [← cq_callE_subPB hPBN] at hcallP
  obtain ⟨a1, hl1, hP1, hX1⟩ := cq_jobsOk (J := none) hJPS hoS.front hLD hdn hpp hden hPD hrec
    (fun h => absurd h (by simp)) hkS hk ⟨hJR0 hR hT hCt hFl, PExt.of_ext (Ext.refl _), rfl⟩
    (seq_foldS HS hw0) hcallP
  obtain ⟨sJ, hSacc, hse1⟩ := checkJobList_ok_sameEnter sameEnter_worker.symm hl1
  have h224 : rdW ((cqSM N).arr64 CTL) 224 = 0 := by
    show rdW ((flushMem (cqCtlSM (cqBankSM N))).arr64 CTL) 224 = 0
    rw [(flushMem_frame _).ctl 224 (by decide)]; exact (cqCtlSM_ctl hCt).2.2
  have hfr : MemFrame cqA cqC (cqSM N) N' :=
    cq_checkJobs_frame0 checkerProg_cqF0W (by chk_lk) (by chk_lk) hcall h224
  -- mode `9`'s memory and the frozen side `N9`
  let W9 := seqNext m8 MODE PLO PHI 9 0 c
  let N9 : Mem := ⟨N'.bytes, N'.words, W9.glob⟩
  have hAg9 : Agree phaseBPa (fun _ => false) W9 N9 :=
    ⟨fun a ha => hAg8'.1 a ha, fun _ h => absurd h (by simp), rfl⟩
  obtain ⟨g9, g9lo, g9hi⟩ := cq_seqNext_glob m8 9 0 c
  have eglo2 : (cqCM N9).glob PLO = 0 := by rw [cqCM_glob]; exact g9lo
  have eghi2 : (cqCM N9).glob PHI = c := by rw [cqCM_glob]; exact g9hi
  have hPBN9 : (cqCM N9).arr8 L.Rom.PB = pb.data.toList.toArray := by
    show (cqCM N9).bytes L.Rom.PB = _
    rw [cqCM_bytes]; show N'.bytes L.Rom.PB = _
    rw [cq_callE_bytes hcall, cqSM_bytes]; show m9.bytes L.Rom.PB = _; rw [hb9]; exact hPBm
  -- the challenge's jobs' start
  have hJRC : CqCtlCOK (cqBankCM N9) → FlushOK (cqCtlCM (cqBankCM N9)) →
      JobR PS.ipins (dnOf sG.store) res.toArray (some (solutionOf PS.IS res)) I (cqCM N9) a1 := by
    intro hCC hFl2
    have h := (cq_phaseC hJMN hP1.1.toJobM hR hT hCt hfr hX1 W9.glob hCC).flushR hP1.1.state.wf hP1.1.off hFl2
    have ea : ({ a1 with caches := Caches.empty } : AState) = a1 := by rw [← hP1.1.caches]
    rwa [ea] at h
  obtain ⟨pinsPJ, dsPJ, dsSPJ, matesU, -, hspec, hppJ, hdenJ, hPDJ, hHJ⟩ :=
    poolHypsJ_ofPI hS6.phase hI (PoolJobs.of_seq hSacc) (fun (_ : Unit) (_ : AState) => False)
      (fun _ _ _ => False)
  have HJ := hHJ (fun _ _ _ _ _ h => h.elim)
  have hwJ : WorkerOK a' sJ := seq_workerS HS (WorkerOK.start hstI) hSacc
  have hcrs : CrsFor PS.ipins (dnOf sG.store) res.toArray (Prog.subPB pb.data.toList checkerProg)
      (some (solutionOf PS.IS res)) := fun _ => checkerProg_crsSpecPB pb.data.toList hr hpre hcdC
  have hLDC := declsLpsDn_dnOf ho.pd ho.den
  refine ⟨sJ, hSacc, fun rs9 m9' h9 => ?_, fun e h9 hk0 => ?_⟩
  · obtain ⟨k2, r2, N'', hk2, -, -, hCC, hFl2, -, -, hcall2⟩ := cq_check9 hQ hAg9 g9 hN62 h9
    rw [eglo2, eghi2, ← cq_callE_subPB hPBN9] at hcall2
    obtain ⟨a2, hl2, -, -⟩ := cq_jobsOk hJPC ho.front hLDC hdn hppJ hdenJ hPDJ hspec hcrs hcnt hk2
      ⟨hJRC hCC hFl2, hP1.2.1, hP1.2.2⟩ (fold_sameEnter hse1 (seq_foldJ HJ hwJ)) hcall2
    obtain ⟨sK, hCacc, -⟩ := checkJobList_ok_sameEnter hse1 hl2
    exact ⟨sK, hCacc⟩
  · rcases cq_check9_err hQ hAg9 g9 hN62 h9 with h0 | ⟨hCC, hFl2, k2, hk2, hcall2⟩
    · exact absurd h0 hk0
    rw [eglo2, eghi2, ← cq_callE_subPB hPBN9] at hcall2
    exact twinFailsV_of_sameEnter hse1
      (cq_jobsErr hJPC ho.front hLDC hdn hppJ hdenJ hPDJ hspec hcrs ⟨hJG _, crsG_checker _⟩ hcnt hk2
        ⟨hJRC hCC hFl2, hP1.2.1, hP1.2.2⟩ (fold_sameEnter hse1 (seq_foldJ HJ hwJ)) hcall2 hk0)

/-- **The sequential compared run's accept is the twin's** (`TwinComparesAcceptsSeqI`, `cq_seq`). -/
theorem cmpAccS_twin (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (hQ : CqSeqProg checkerProg)
    (h : CmpAccS checkerTab checkerProg MODE PLO PHI OUT HDRF CTLF hdrHw bC bS pb) :
    TwinComparesAcceptsSeqI bC bS := by
  rcases h with hA | ⟨rs5, m5, hf, rs6, m6, h6, hor⟩
  · exact (cmpFrontAcc45_false bC bS pb h64 hA).elim
  obtain ⟨pins, ipins, dsS, recsC, IS, IC, sI, hSt, hA6, -, hS⟩ := cq_seq bC bS pb h64 hQ hf h6
  rcases hor with hA6' | ⟨-, rs8, m8, h8, -, rs9, m9', h9, -⟩
  · exact (hA6 hA6').elim
  obtain ⟨sJ, hSacc, hC, -⟩ := hS rs8 m8 h8
  obtain ⟨sK, hCacc⟩ := hC rs9 m9' h9
  exact ⟨pins, ipins, dsS, recsC, IS, IC, sI, sJ, sK, hSt, hSacc, hCacc⟩

/-- **A failing sequential compared run with a class other than `0` is the twin's**
(`TwinCompareVerdictSeqI`): the front's stages (`cmpV_a4`, `cmpV_a5`), mode `6` (class `0` only),
or the solution's or (those accepting) the challenge's jobs (`cq_seq`). -/
theorem cmpErrS_twin (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (hQ : CqSeqProg checkerProg) {k : Word}
    (h : CmpErrS checkerTab checkerProg MODE PLO PHI OUT HDRF CTLF hdrHw bC bS pb k) (hk : k &&& 3 ≠ 0) :
    TwinCompareVerdictSeqI bC bS (k &&& 3) := by
  rcases h with ⟨hbC, hpb, ⟨e, he, hc'⟩ | ⟨rs4, m4, h4, hge4, hbS, e, he, hc'⟩⟩ |
      ⟨rs5, m5, hf, ⟨e, he, hc'⟩ | ⟨rs6, m6, h6, -, hor⟩⟩
  · have hcls : e.cls = k &&& 3 := by rw [Err.cls, hc']
    rw [← hcls] at hk ⊢
    exact .inl (cmpV_a4 bC bS pb h64 hbC hpb e he hk)
  · have hcls : e.cls = k &&& 3 := by rw [Err.cls, hc']
    rw [← hcls] at hk ⊢
    exact .inl (cmpV_a5 bC bS pb h64 hbC hbS hpb rs4 m4 h4 hge4 e he hk)
  · have hcls : e.cls = k &&& 3 := by rw [Err.cls, hc']
    exact absurd (hcls ▸ cmpV_a67 (.inl (by simp [Mem.setG])) he) hk
  obtain ⟨pins, ipins, dsS, recsC, IS, IC, sI, hSt, -, hE8, hS⟩ := cq_seq bC bS pb h64 hQ hf h6
  rcases hor with ⟨e, he, hc'⟩ | ⟨rs8, m8, h8, -, e, he, hc'⟩
  · have hcls : e.cls = k &&& 3 := by rw [Err.cls, hc']
    rw [← hcls] at hk ⊢
    exact .inr (.inl ⟨pins, ipins, dsS, recsC, IS, IC, sI, hSt, hE8 e he hk⟩)
  · have hcls : e.cls = k &&& 3 := by rw [Err.cls, hc']
    rw [← hcls] at hk ⊢
    obtain ⟨sJ, hSacc, -, hE9⟩ := hS rs8 m8 h8
    exact .inr (.inr ⟨pins, ipins, dsS, recsC, IS, IC, sI, sJ, hSt, hSacc, hE9 e he hk⟩)

end ConAgua.Final
