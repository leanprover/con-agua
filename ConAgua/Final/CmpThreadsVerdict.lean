module

public import ConAgua.Final.CmpThreads
public import ConAgua.Final.ThreadsVerdict
public import ConAgua.Final.CompareTwinVerdict
import ConAgua.Final.CmpChain
import ConAgua.Final.BufAbi
import ConAgua.Final.DrvFinal
import ConAgua.Checker.AsmFinal
import ConAgua.Checker.ProgIRef
import ConAgua.Checker.AsmXOk
import ConAgua.Checker.ProgWf
import all ConAgua.Checker.Entry

@[expose] public section

/-!
# The verdict theorem for the threaded compared run (lane compare2)

`checkerFile_compare_threads_verdict_of`: the trusted threaded harness (`main.c`,
`run_compare_jobs`) drives the mode entries and the two pools as `CmpThreadsRun` says
(`Final/CmpThreads.lean`) up to a failure. If the run reports a failure with the code `k`
(`CmpThreadsFail`) of class `k &&& 3` `1` (reject) or `2` (decline), the twin's pooled comparison
fails with that class (`TwinCompareVerdictPooled bC bS`). The failure is one of: a driver call
(`ca_start_a4`, `ca_start_a5`, `ca_start_a7`) returning `rdx = 2`, or a thread's call of one of
the pools returning `rdx = 2` after its earlier calls accepted, every job index below its own
claimed by an accepting call (`CmpTPoolFail`, as `ThreadFail`'s: the harness reports the failing
job with the smallest index). From the machine-level runs (`cmpT_post5`, `cmpT_post7`,
`cmpT_upToS`, `cmpT_upToC`, the threads' chains) and the L-level claims (`CmpThreadVerdicts`).

**What the theorem trusts of the harness**: `CmpThreadsRun`'s facts for the calls up to the
failing one (`CmpTRun4` … `CmpTRunC`), and for a failing thread `ThreadFail`'s facts about its
pool (`CmpTPoolFail`); beyond them, what `Final/Statement.lean` lists.
-/

namespace ConAgua.Final

open L L.Compiler L.Checker L.Arena ConRon.Arena

/-! ## The harness's facts on a failing run -/

/-- **A thread's call `i` of a pool fails** (trusted; `ThreadFail`'s facts about the pool): the
pool after the driver call at `dm` returning at `st` with the buffer `B`, and the thread `t`'s
calls `0, …, i`, the calls before `i` accepting and claiming smaller job indices, call `i`
returning `rdx = 2`; and every job index below call `i`'s claimed by an accepting call of the
threads `ths` (`ThreadsAcc`). -/
structure CmpTPoolFail [Host] (dm : MachineData) (st : MachineState) (B : Array Word) (ths : List ThreadM)
    (t : ThreadM) (i : Nat) : Prop where
  calls : ∀ i' ≤ i, BufCallH B (t.dm i') (t.ra i') ∧
    (t.dm i').regs.rdi.toNat = outAddr dm.regs.r8.toNat ∧ (t.dm i').regs.rcx.toNat = t.base ∧
    (t.dm i').regs.r8.toNat = t.blen
  zero : ∀ x, t.base ≤ x → x < t.base + t.blen → (t.dm 0).dmem.get? (A x) = some 0
  ret : ∀ i' ≤ i, FirstReturn (t.dm i') (label abiCheckBL) (t.ra i') (t.st i')
  acc : ∀ i' < i, (t.st i').data.regs.rdx = 0 ∧ (t.st i').data.regs.rax = ACCEPT
  rdx : (t.st i).data.regs.rdx = 2
  /-- route A: the buffer's words at each accepting call's return -/
  kept : ∀ i' < i, ∀ q (h : q < B.size),
    rdW (t.st i').data.dmem (A (outAddr dm.regs.r8.toNat + 8 * q)) = some B[q]
  next : ∀ i', i' < i → ∀ x, t.base ≤ x → x < t.base + t.blen →
    (t.dm (i' + 1)).dmem.get? (A x) = (t.st i').data.dmem.get? (A x)
  claimed : ∀ i' ≤ i, (t.dm i').regs.rdx < st.data.regs.rax - 9223372036854775808
  /-- the thread's earlier calls claimed smaller job indices -/
  before : ∀ i' < i, (t.dm i').regs.rdx < (t.dm i).regs.rdx
  /-- the jobs below call `i`'s: each claimed by an accepting call of a thread of `ths` -/
  others : ThreadsAcc dm st B ths
  below : ∀ j < (t.dm i).regs.rdx, ∃ t' ∈ ths, ∃ i' < t'.n, (t'.dm i').regs.rdx = j

/-- **The threaded compared harness reports a failure with the code `k`**: `ca_start_a4` (called
at `dm₄`) failed with `rax = k`; or `ca_start_a5` did; or a thread's call of the solution's pool
did; or `ca_start_a7` did; or a thread's call of the challenge's pool did, each after the calls
before it as `CmpThreadsRun` has them. -/
def CmpThreadsFail [Host] (bC bS pb : ByteArray) (dm₄ : MachineData) (ra₄ : Word) (st₄ : MachineState)
    (k : Word) : Prop :=
  (CmpTRun4 bC pb dm₄ ra₄ st₄ ∧ st₄.data.regs.rdx = 2 ∧ k = st₄.data.regs.rax) ∨
  (∃ dm₅ ra₅ st₅, CmpTRun5 bC bS pb dm₄ ra₄ st₄ dm₅ ra₅ st₅ ∧ st₅.data.regs.rdx = 2 ∧
    k = st₅.data.regs.rax) ∨
  (∃ dm₅ ra₅ st₅ BS thsS t i, CmpTRunS bC bS pb dm₄ ra₄ st₄ dm₅ ra₅ st₅ BS ∧
    CmpTPoolFail dm₅ st₅ BS thsS t i ∧ k = (t.st i).data.regs.rax) ∨
  (∃ dm₅ ra₅ st₅ BS thsS dm₇ ra₇ st₇, CmpTRun7 bC bS pb dm₄ ra₄ st₄ dm₅ ra₅ st₅ BS thsS dm₇ ra₇ st₇ ∧
    st₇.data.regs.rdx = 2 ∧ k = st₇.data.regs.rax) ∨
  (∃ dm₅ ra₅ st₅ BS thsS dm₇ ra₇ st₇ BC thsC t i,
    CmpTRunC bC bS pb dm₄ ra₄ st₄ dm₅ ra₅ st₅ BS thsS dm₇ ra₇ st₇ BC ∧
    CmpTPoolFail dm₇ st₇ BC thsC t i ∧ k = (t.st i).data.regs.rax)

/-! ## The L-level claims -/

/-- A pool's failing thread at the L level, on the buffer of `m` (the phase's driver memory,
whose run returned `rs`): a fresh region `r₀` whose calls `cs`, each on an index below `j`, ran
(`ThreadFails`), its next call on `j < k` failing with `e`; and threads `ths`, each a fresh region
with its calls (`ThreadRuns`), claims below `k` and increasing, running every index below `j`. -/
def CmpTPoolFailL (m : Mem) (rs : List Word) (e : Err) : Prop :=
  ∃ (r₀ : Mem) (j : Word) (cs : List (Word × Nat × Mem)) (n : Nat),
    (∀ b ∈ parOwnedL, r₀.arr64 b = zeros (m.arr64 b).size) ∧ r₀.glob INIT = 0 ∧
    ThreadFails (cmpBuf OUT m) j n e r₀ cs ∧ (∀ c ∈ cs, c.1 < j) ∧ j < rs.getD 0 0 - 9223372036854775808 ∧
    ∃ ths : List (Mem × List (Word × Nat × Mem)),
      (∀ t ∈ ths, (∀ b ∈ parOwnedL, t.1.arr64 b = zeros (m.arr64 b).size) ∧ t.1.glob INIT = 0 ∧
        ThreadRuns (cmpBuf OUT m) t.1 t.2 ∧ ∀ c ∈ t.2, c.1 < rs.getD 0 0 - 9223372036854775808) ∧
      (∀ t ∈ ths, (t.2.map (·.1)).Pairwise (· < ·)) ∧
      (∀ i : Word, i < j → ∃ t ∈ ths, ∃ c ∈ t.2, c.1 = i)

/-- **The threaded compared run's verdict claims** (the L-level obligations; helper H1): a failure
of class other than `0` of mode `4`'s run, of mode `5`'s, of a job of the solution's pool, of mode
`7`'s, or of a job of the challenge's pool, each after the runs before it ok, is the twin's. -/
structure CmpThreadVerdicts : Prop where
  a4 : ∀ (bC bS pb : ByteArray), System.Platform.numBits = 64 → bC.size < 2 ^ 63 → pb.size < 2 ^ 63 →
    ∀ e, cmpRun checkerProg (cmpM4 checkerTab MODE bC pb) = .error e → e.cls ≠ 0 →
    TwinCompareVerdict bC bS e.cls
  a5 : ∀ (bC bS pb : ByteArray), System.Platform.numBits = 64 → bC.size < 2 ^ 63 → bS.size < 2 ^ 63 →
    pb.size < 2 ^ 63 → ∀ rs4 m4, cmpRun checkerProg (cmpM4 checkerTab MODE bC pb) = .ok (rs4, m4) →
    2 ^ 63 ≤ (rs4.getD 0 0).toNat →
    ∀ e, cmpRun checkerProg (cmpM5 MODE m4 bS) = .error e → e.cls ≠ 0 →
    TwinCompareVerdict bC bS e.cls
  jobS : ∀ (bC bS pb : ByteArray), System.Platform.numBits = 64 → bC.size < 2 ^ 63 → bS.size < 2 ^ 63 →
    pb.size < 2 ^ 63 → ∀ rs4 m4, cmpRun checkerProg (cmpM4 checkerTab MODE bC pb) = .ok (rs4, m4) →
    2 ^ 63 ≤ (rs4.getD 0 0).toNat → ∀ rs5 m5, cmpRun checkerProg (cmpM5 MODE m4 bS) = .ok (rs5, m5) →
    2 ^ 63 ≤ (rs5.getD 0 0).toNat →
    ∀ e, CmpTPoolFailL m5 rs5 e → e.cls ≠ 0 → TwinCompareVerdictPooled bC bS e.cls
  a7 : ∀ (bC bS pb : ByteArray), System.Platform.numBits = 64 → bC.size < 2 ^ 63 → bS.size < 2 ^ 63 →
    pb.size < 2 ^ 63 → ∀ rs4 m4, cmpRun checkerProg (cmpM4 checkerTab MODE bC pb) = .ok (rs4, m4) →
    2 ^ 63 ≤ (rs4.getD 0 0).toNat → ∀ rs5 m5, cmpRun checkerProg (cmpM5 MODE m4 bS) = .ok (rs5, m5) →
    2 ^ 63 ≤ (rs5.getD 0 0).toNat → ∀ thsS, CmpTPoolS m5 rs5 thsS →
    ∀ e, cmpRun checkerProg (cmpM7 MODE m5 bS) = .error e → e.cls ≠ 0 →
    TwinCompareVerdictPooled bC bS e.cls
  jobC : ∀ (bC bS pb : ByteArray), System.Platform.numBits = 64 → bC.size < 2 ^ 63 → bS.size < 2 ^ 63 →
    pb.size < 2 ^ 63 → ∀ rs4 m4, cmpRun checkerProg (cmpM4 checkerTab MODE bC pb) = .ok (rs4, m4) →
    2 ^ 63 ≤ (rs4.getD 0 0).toNat → ∀ rs5 m5, cmpRun checkerProg (cmpM5 MODE m4 bS) = .ok (rs5, m5) →
    2 ^ 63 ≤ (rs5.getD 0 0).toNat → ∀ thsS, CmpTPoolS m5 rs5 thsS →
    ∀ rs7 m7, cmpRun checkerProg (cmpM7 MODE m5 bS) = .ok (rs7, m7) → 2 ^ 63 ≤ (rs7.getD 0 0).toNat →
    ∀ e, CmpTPoolFailL m7 rs7 e → e.cls ≠ 0 → TwinCompareVerdictPooled bC bS e.cls

/-! ## A pool's failing thread -/

set_option linter.constructorNameAsVariable false in
/-- **A pool's failing call, at the L level**: the thread's calls before it and the other threads'
calls as `CmpTPoolFailL` takes them, the failing call's run failing with `e`, `e.code` its `rax`. -/
theorem cmpT_poolFail [Host] (k0 : Nat) (hcode : Code checkerFile k0) (dm : MachineData) (st : MachineState)
    (B : Array Word) (ths : List ThreadM) (t : ThreadM) (i : Nat) (hR : CmpTPoolFail dm st B ths t i)
    {inp n pins np : Nat} {m : Mem} (hM : MemRel (abiLayout checkerTab dm.regs.r8.toNat inp n pins np) m st.data.dmem)
    (hok : CmpBufOk frozenIdsL OUT m) (hBm : B = cmpBuf OUT m) {rs : List Word}
    (hrax : st.data.regs.rax = rs.getD 0 0) :
    ∃ e, (t.st i).data.regs.rax = e.code ∧ CmpTPoolFailL m rs e := by
  have hc := code_of_checkerFile_par hcode
  have hnres : 1 ≤ checkerTab.nres := by decide
  have hBo := hok.2
  rw [← hBm] at hBo
  have hpos : 0 < frozenIdsL.length := by rw [frozenIdsL_eq]; simp
  have hhdr : ∀ i < frozenIdsL.length, 9 + 2 * i < B.size := fun i hi => by
    have := hBo.hdr i hi; have := hBo.ent 0 hpos; have := hBo.hdr0; omega
  have hent' := hBo.ent
  have hdisj := hBo.disj
  -- the thread: a call's outcome, at any region memory
  obtain ⟨hH0, -, hcx0, h80⟩ := hR.calls 0 (Nat.zero_le _)
  have hneed : workerNeed parOwnedL ≤ t.blen := h80 ▸ hH0.need
  have hfit : t.base + t.blen < 2 ^ 64 := hcx0 ▸ h80 ▸ hH0.fits
  have hpost : ∀ i' ≤ i, ∀ r, RegionRel checkerTab t.base parOwnedL r (t.dm i').dmem →
      EntryPost (bufLayout checkerTab (outAddr dm.regs.r8.toNat) B t.base frozenIdsL parOwnedL) (t.dm i')
        (t.ra i') (L.run checkerProg abiFuel "check" [] (bufMemG frozenIdsL parOwnedL PLO PHI MODE B r
          (t.dm i').regs.rdx)) (t.st i') := by
    intro i' hi r hr
    obtain ⟨hH, hdi, hcx, h8⟩ := hR.calls i' hi
    have hbc : BufCall checkerTab frozenIdsL parOwnedL B (t.dm i') (t.ra i') :=
      ⟨⟨hH.need, hH.fits, hH.bend, hhdr, hent', hdisj, hH.apart⟩, hH.hB, hH.hmap, hH.hra, hH.hcs,
        hH.hcs24, hH.hcs8⟩
    have hEv := abiB_outcome checkerProgI checkerProg checkerProgI_refines checkerTab checkerTab_abiOk checkerX_ok
      checkerProgI_wf MODE PLO PHI OUT HDRF CTLF (hdrW + 2) frozenIdsL parOwnedL (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) k0 hc L.Checker.checkL checkerProg_lookup_check (by decide)
      B r (t.dm i') (t.ra i') hbc (by rw [hcx]; exact hr) checker_bufMinOk
    rw [hdi, hcx] at hEv
    exact hR.ret i' hi _ hEv (fun s h => h.1)
  -- the calls before `i` (`thread_chain`)
  obtain ⟨rm, h0, hrun⟩ := thread_chain checkerProg checkerTab checkerTab_abiOk hnres frozenIdsL parOwnedL
    parOwnedL_not_frozen PLO PHI MODE B (outAddr dm.regs.r8.toNat) t.base t.blen i hneed hfit t.dm t.ra t.st
    (fun _ => hR.zero) (fun i' hi r hr => hpost i' (by omega) r hr) hR.acc
    (fun i' hi => hR.next i' (by omega))
  -- the region at call `i`, and call `i`'s failure
  have hreg : RegionRel checkerTab t.base parOwnedL (rm i) (t.dm i).dmem := by
    rcases i with _ | i
    · rw [h0]; exact regionRel_zero checkerTab_abiOk hneed hfit _ hR.zero
    · obtain ⟨-, -, -, h3, -⟩ := hrun i (by omega)
      exact (RegionRel.of_memRel parOwnedL_not_frozen h3).transfer checkerTab_abiOk hneed (hR.next i (by omega))
  obtain ⟨-, -, -, hout⟩ := hpost i (Nat.le_refl _) (rm i) hreg
  obtain ⟨e, he, hrax'⟩ := outcome_err (hout.resolve_left (by rw [hR.rdx]; decide)) hR.rdx
  have hruns := threadFails_range B t rm i e (fun i' hi => by
    obtain ⟨rs, h1, -, h3, -⟩ := hrun i' hi
    exact ⟨⟨rs, h1⟩, bufKept_of_memRel h3 hent' (hR.kept i' hi)⟩) he i 0 (by omega)
  rw [h0] at hruns
  -- the other threads' calls (`threadsAcc_runs`)
  obtain ⟨f, hf⟩ := Classical.axiomOfChoice
    (threadsAcc_runs k0 hcode dm st B ths hR.others hhdr hent' hdisj)
  have hzero : ∀ a ∈ parOwnedL, (zeroMem checkerTab).arr64 a = zeros (m.arr64 a).size := by
    intro a ha
    have hl := parOwnedL_dom a ha
    rw [hM.size64 a hl]
    simp only [abiLayout_tab]
    rw [abiLayout_s64 _ _ _ _ _ _ (by
      have := checkerTab.pos64_lt hl; have := (abiTabOk_spec checkerTab_abiOk).1; omega), checkerTab.wAt_pos64 hl]
    simp [zeroMem, Mem.arr64, zeros]
  refine ⟨e, hrax', zeroMem checkerTab, _, _, abiFuel, hzero, rfl, hBm ▸ hruns, fun c hc => ?_,
    by rw [← hrax]; exact hR.claimed i (Nat.le_refl _), ths.map fun t' => (zeroMem checkerTab, f t'),
    fun t' ht' => ?_, fun t' ht' => ?_, fun j hj => ?_⟩
  · obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hc
    rw [List.mem_range'] at hi'
    exact hR.before i' (by omega)
  · obtain ⟨t', ht, rfl⟩ := List.mem_map.mp ht'
    obtain ⟨h1, h2, -, -, -⟩ := hf t' ht
    exact ⟨hzero, rfl, hBm ▸ h1, fun c hc => by rw [← hrax]; exact h2 c hc⟩
  · obtain ⟨t', ht, rfl⟩ := List.mem_map.mp ht'
    exact (hf t' ht).2.2.2.2
  · obtain ⟨t', ht', i', hi', hj'⟩ := hR.below j hj
    obtain ⟨-, -, h3, -, -⟩ := hf t' ht'
    obtain ⟨c, hc', hcj⟩ := h3 i' hi'
    exact ⟨_, List.mem_map.mpr ⟨t', ht', rfl⟩, c, hc', by rw [hcj, hj']⟩

/-! ## The theorem -/

/-- A driver call's failing return: the sizes, and the L run failed with the code in `rax`. -/
theorem cmpT_fail {tab : Tab} {base inp n pins np : Nat} {dm : MachineData} {ra : Word}
    {r : Except Err (List Word × Mem)} {st : MachineState} {b pb : ByteArray}
    (h : EntryPost (abiLayout tab base inp n pins np) dm ra r st ∧ SizesPost b pb st)
    (h2 : st.data.regs.rdx = 2) :
    b.size < 2 ^ 63 ∧ pb.size < 2 ^ 63 ∧ ∃ e, r = .error e ∧ st.data.regs.rax = e.code := by
  obtain ⟨⟨-, -, -, hout⟩, hsz⟩ := h
  have hne : st.data.regs.rdx ≠ 1 := by rw [h2]; decide
  obtain ⟨hb, hpb⟩ := hsz.resolve_left hne
  exact ⟨hb, hpb, outcome_err (hout.resolve_left hne) h2⟩

set_option linter.constructorNameAsVariable false in
/-- **The verdict theorem for the threaded compared run of `checker.s`**: when the trusted
threaded harness's run reports a failure with the code `k` (`CmpThreadsFail`) and the class
`k &&& 3` is `1` (reject) or `2` (decline), the twin's pooled comparison of the challenge `bC` with
the solution `bS` fails with that class (`TwinCompareVerdictPooled`), given the L-level verdict
claims (`CmpThreadVerdicts`). -/
theorem checkerFile_compare_threads_verdict_of [Host] (k0 : Nat) (hcode : Code checkerFile k0)
    (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (dm₄ : MachineData) (ra₄ : Word) (st₄ : MachineState) (k : Word)
    (hV : CmpThreadVerdicts) (hF : CmpThreadsFail bC bS pb dm₄ ra₄ st₄ k) (hk : k &&& 3 ≠ 0) :
    TwinCompareVerdictPooled bC bS (k &&& 3) := by
  rcases hF with ⟨hR, h2, rfl⟩ | ⟨dm₅, ra₅, st₅, hR, h2, rfl⟩ | ⟨dm₅, ra₅, st₅, BS, thsS, t, i, hR, hT, rfl⟩ |
    ⟨dm₅, ra₅, st₅, BS, thsS, dm₇, ra₇, st₇, hR, h2, rfl⟩ |
    ⟨dm₅, ra₅, st₅, BS, thsS, dm₇, ra₇, st₇, BC, thsC, t, i, hR, hT, rfl⟩
  · -- `ca_start_a4` failed
    obtain ⟨hbC, hpb, e, he, hrax⟩ :=
      cmpT_fail (hR.ret₄ _ (cta_a4 k0 hcode bC pb dm₄ ra₄ hR.call₄) (fun s h => h.1.1)) h2
    rw [hrax] at hk ⊢
    exact (hV.a4 bC bS pb h64 hbC hpb e he hk).pooled
  · -- `ca_start_a5` failed
    obtain ⟨hbC, hpb, -, rs4, m4, h4, hge4, hP5⟩ := cmpT_post5 k0 hcode hR
    obtain ⟨hbS, -, e, he, hrax⟩ := cmpT_fail hP5 h2
    rw [hrax] at hk ⊢
    exact (hV.a5 bC bS pb h64 hbC hbS hpb rs4 m4 h4 hge4 e he hk).pooled
  · -- a job of the solution's pool failed
    obtain ⟨hbC, hbS, hpb, -, -, rs4, m4, rs5, m5, h4, hge4, h5, hrax5, hM5⟩ :=
      cmpT_upToS k0 hcode hR.toCmpTRun5 hR.rdx₅
    have hge5 : 2 ^ 63 ≤ (rs5.getD 0 0).toNat := by rw [← hrax5]; exact hR.rax₅
    have hok5 := checker_cmpBufOk bC bS pb h64 hbC hbS hpb h4 hge4 h5 hge5
    have hBS := cta_bufEq hM5 hok5 hR.bufwS hR.buflenS
    obtain ⟨e, hrax, hL⟩ := cmpT_poolFail k0 hcode dm₅ st₅ BS thsS t i hT hM5 hok5 hBS hrax5
    rw [hrax] at hk ⊢
    exact hV.jobS bC bS pb h64 hbC hbS hpb rs4 m4 h4 hge4 rs5 m5 h5 hge5 e hL hk
  · -- `ca_start_a7` failed
    obtain ⟨hbC, hbS, hpb, -, -, -, rs4, m4, rs5, m5, h4, hge4, h5, hge5, thsS', hS, hP7⟩ :=
      cmpT_post7 k0 hcode h64 hR
    obtain ⟨-, -, e, he, hrax⟩ := cmpT_fail hP7 h2
    rw [hrax] at hk ⊢
    exact hV.a7 bC bS pb h64 hbC hbS hpb rs4 m4 h4 hge4 rs5 m5 h5 hge5 thsS' hS e he hk
  · -- a job of the challenge's pool failed
    obtain ⟨hbC, hbS, hpb, -, -, -, -, rs4, m4, rs5, m5, h4, hge4, h5, hge5, thsS', hS, rs7, m7, h7, hrax7, hM7⟩ :=
      cmpT_upToC k0 hcode h64 hR.toCmpTRun7 hR.rdx₇
    have hge7 : 2 ^ 63 ≤ (rs7.getD 0 0).toNat := by rw [← hrax7]; exact hR.rax₇
    have hok7 := checker_cmp7BufOk bC bS pb h64 hbC hbS hpb h4 hge4 h5 hge5 h7 hge7
    have hBC := cta_bufEq hM7 hok7 hR.bufwC hR.buflenC
    obtain ⟨e, hrax, hL⟩ := cmpT_poolFail k0 hcode dm₇ st₇ BC thsC t i hT hM7 hok7 hBC hrax7
    rw [hrax] at hk ⊢
    exact hV.jobC bC bS pb h64 hbC hbS hpb rs4 m4 h4 hge4 rs5 m5 h5 hge5 thsS' hS rs7 m7 h7 hge7 e hL hk

end ConAgua.Final
