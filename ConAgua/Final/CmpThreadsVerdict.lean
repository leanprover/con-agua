module

public import ConAgua.Final.CmpThreads
public import ConAgua.Final.ThreadsVerdict
import ConAgua.Final.CpThreadFail
import ConAgua.Verdict.CmpVSPhase

@[expose] public section

/-!
# The verdict theorem for the threaded compared run of the committed file (lane compare2)

`checkerFile_compare_threads_verdict`: the trusted threaded harness (`main.c`, `run_jobs` with a
solution) runs the compared entry 1 (`ca_start_ac`, `CmpCall`) and its threads over the buffer it
left, as in a flat threaded run (`Final/ThreadsVerdict.lean`). If the run reports a failure with
the code `k` (`CmpThreadsFail`: entry 1 returned `rdx = 2` with `rax = k`, or entry 1 returned ok
and some thread's call `i` returned `rdx = 2` with `rax = k`, its earlier calls accepted, and every
job index below call `i`'s was claimed by an accepting call), then for a class `k &&& 3` of `1`
(reject) or `2` (decline) the twin's comparison, run as the threads do, fails with that class
(`TwinCompareVerdictThr bC bS`): a stage fails, or some worker's list of the solution's jobs fails
from the challenge's index state, or the solution's jobs are accepted by workers covering them and
some worker, after its list of the solution's jobs, fails on its list of the challenge's jobs.

**What the theorem trusts of the harness**: what `ThreadFail`/`Entry1Fail` trust
(`Final/ThreadsVerdict.lean`), with the compared entry 1 (`CmpCall`, its first return at
`ca_start_ac`). One pool runs both phases: the indices below `kS` are the solution's jobs, the
others the challenge's, so the smallest failing index is the solution's failure if any, as
con-ron's two pools report it.
-/

namespace ConAgua.Final

open L L.Compiler L.Checker L.Arena ConRon.Arena

/-- **The compared entry 1 fails** (trusted; the module doc lists it). -/
structure CmpEntry1Fail [Host] (bC bS pb : ByteArray) (sa : Word) (dm₀ : MachineData) (ra₀ : Word)
    (st₀ : MachineState) : Prop where
  call₀ : CmpCall bC bS pb sa dm₀ ra₀
  ret₀ : FirstReturn dm₀ (label abiStartACL) ra₀ st₀
  rdx₀ : st₀.data.regs.rdx = 2

/-- **A thread's call `i` fails in a compared run** (trusted; the module doc lists it):
`ThreadFail`'s facts, with the compared entry 1, and the thread's calls up to `i` claiming
increasing indices (`ThreadFail` has only the earlier calls below call `i`: here a thread's
solution jobs must come before its challenge jobs, which continue on the region they left). -/
structure CmpThreadFail [Host] (bC bS pb : ByteArray) (sa : Word) (dm₀ : MachineData) (ra₀ : Word)
    (st₀ : MachineState) (B : Array Word) (ths : List ThreadM) (t : ThreadM) (i : Nat) : Prop where
  call₀ : CmpCall bC bS pb sa dm₀ ra₀
  ret₀ : FirstReturn dm₀ (label abiStartACL) ra₀ st₀
  rdx₀ : st₀.data.regs.rdx = 0
  rax₀ : 9223372036854775808 ≤ st₀.data.regs.rax.toNat
  /-- the buffer: `OUT`'s first `len` words, `len` its word `1` -/
  bufw : ∀ q (h : q < B.size), rdW st₀.data.dmem (A (outAddr dm₀.regs.r8.toNat + 8 * q)) = some B[q]
  buflen : ∃ w, rdW st₀.data.dmem (A (outAddr dm₀.regs.r8.toNat + 8)) = some w ∧ w.toNat = B.size
  /-- the calls: the buffer in place, on the thread's region -/
  calls : ∀ i' ≤ i, BufCallH B (t.dm i') (t.ra i') ∧
    (t.dm i').regs.rdi.toNat = outAddr dm₀.regs.r8.toNat ∧ (t.dm i').regs.rcx.toNat = t.base ∧
    (t.dm i').regs.r8.toNat = t.blen
  zero : ∀ x, t.base ≤ x → x < t.base + t.blen → (t.dm 0).dmem.get? (A x) = some 0
  ret : ∀ i' ≤ i, FirstReturn (t.dm i') (label abiCheckBL) (t.ra i') (t.st i')
  acc : ∀ i' < i, (t.st i').data.regs.rdx = 0 ∧ (t.st i').data.regs.rax = ACCEPT
  rdx : (t.st i).data.regs.rdx = 2
  /-- route A: the buffer's words at each accepting call's return -/
  kept : ∀ i' < i, ∀ q (h : q < B.size),
    rdW (t.st i').data.dmem (A (outAddr dm₀.regs.r8.toNat + 8 * q)) = some B[q]
  next : ∀ i', i' < i → ∀ x, t.base ≤ x → x < t.base + t.blen →
    (t.dm (i' + 1)).dmem.get? (A x) = (t.st i').data.dmem.get? (A x)
  claimed : ∀ i' ≤ i, (t.dm i').regs.rdx < st₀.data.regs.rax - 9223372036854775808
  /-- the thread's claims increase (one monotone claim counter, as `ThreadsAcc`'s `incr`) -/
  incr : ∀ i₁ i₂, i₁ < i₂ → i₂ ≤ i → (t.dm i₁).regs.rdx < (t.dm i₂).regs.rdx
  /-- the jobs below call `i`'s: each claimed by an accepting call of a thread of `ths` -/
  others : ThreadsAcc dm₀ st₀ B ths
  below : ∀ j < (t.dm i).regs.rdx, ∃ t' ∈ ths, ∃ i' < t'.n, (t'.dm i').regs.rdx = j

/-- **The threaded compared run reports a failure with the code `k`**: entry 1 failed with
`rax = k`, or a thread's call `i` failed with `rax = k`. -/
def CmpThreadsFail [Host] (bC bS pb : ByteArray) (sa : Word) (dm₀ : MachineData) (ra₀ : Word)
    (st₀ : MachineState) (k : Word) : Prop :=
  (CmpEntry1Fail bC bS pb sa dm₀ ra₀ st₀ ∧ k = st₀.data.regs.rax) ∨
  ∃ (B : Array Word) (ths : List ThreadM) (t : ThreadM) (i : Nat),
    CmpThreadFail bC bS pb sa dm₀ ra₀ st₀ B ths t i ∧ k = (t.st i).data.regs.rax

/-- **Stand-in (L level, lane compare2 H7)**: a thread whose solution calls over header S ran from
a fresh region, and whose challenge calls over header C, continuing from the memory those left,
ran and then failed on the challenge's job `j < c` with `e` of class other than `0`, its earlier
challenge calls below `j`; threads `ths` as in `c1Thr_accepts_standin` (every solution job and
every challenge job below `j` claimed): the twin's threaded comparison fails with that class. -/
theorem c1Thr_failC_standin {bC bS pb : ByteArray} (hpb : pb.size < 2 ^ 63) (PS : PhaseS bC bS)
    {m₇ m : Mem} (hF : FoldOn bS pb (abiSz checkerTab) PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m)
    {c : Word} {m9 mS : Mem} (h6 : F6 PS m c m9) (hb9 : m9.bytes = m.bytes) (hV : CsViewS m m9 mS)
    (B : Array Word) (hBS : CsFirst B mS) (khi : Word) (hk : khi.toNat = PS.dsS.size)
    (BC : Array Word) (hBC : CsFirst BC m9)
    (r₀ : Mem) (hz : ∀ b ∈ parOwnedL, r₀.arr64 b = zeros (mS.arr64 b).size) (hI0 : r₀.glob INIT = 0)
    (csS : List (Word × Nat × Mem)) (hS : ThreadRuns B r₀ csS) (hcsS : ∀ c' ∈ csS, c'.1 < khi)
    (hincS1 : (csS.map (·.1)).Pairwise (· < ·))
    (j : Word) (csC : List (Word × Nat × Mem)) (n : Nat) (e : Err)
    (hruns : ThreadFails BC j n e (runsEnd r₀ csS) csC) (hcs : ∀ c' ∈ csC, c'.1 < j)
    (hj : j < c) (hk0 : e.cls ≠ 0)
    (ths : List (Mem × List (Word × Nat × Mem) × List (Word × Nat × Mem)))
    (hth : ∀ t ∈ ths, (∀ b ∈ parOwnedL, t.1.arr64 b = zeros (mS.arr64 b).size) ∧ t.1.glob INIT = 0 ∧
      ThreadRuns B t.1 t.2.1 ∧ (∀ c' ∈ t.2.1, c'.1 < khi) ∧
      ThreadRuns BC (runsEnd t.1 t.2.1) t.2.2 ∧ ∀ c' ∈ t.2.2, c'.1 < c)
    (hcovS : ∀ j' : Word, j' < khi → ∃ t ∈ ths, ∃ c' ∈ t.2.1, c'.1 = j')
    (hcovC : ∀ j' : Word, j' < j → ∃ t ∈ ths, ∃ c' ∈ t.2.2, c'.1 = j')
    (hincS : ∀ t ∈ ths, (t.2.1.map (·.1)).Pairwise (· < ·))
    (hincC : ∀ t ∈ ths, (t.2.2.map (·.1)).Pairwise (· < ·)) :
    TwinCompareVerdictThr bC bS e.cls := by
  sorry

theorem cp_lt_of_lt_le' {a b c : Word} (h1 : a < b) (h2 : b ≤ c) : a < c := cp_lt_of_lt_le h1 h2

set_option linter.constructorNameAsVariable false in
/-- **A thread's failing call in a compared run is the twin's threaded failure**: the failing
call's phase by its index against `kS` (`cpThreadFail_runs`), the other threads' chains
(`cpThreadsAcc_runs`), then the solution's failure (`cmpV_tjobSI`) or the challenge's failure
after the thread's solution calls (`c1Thr_failC_standin`; every solution index lies below the
failing one). -/
theorem cmpThreadFail_twin [Host] (k0 : Nat) (hcode : Code checkerFile k0)
    (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64) (sa : Word)
    (dm₀ : MachineData) (ra₀ : Word) (st₀ : MachineState) (B : Array Word) (ths : List ThreadM)
    (t : ThreadM) (i : Nat) (hR : CmpThreadFail bC bS pb sa dm₀ ra₀ st₀ B ths t i)
    (hk : (t.st i).data.regs.rax &&& 3 ≠ 0) :
    TwinCompareVerdictThr bC bS ((t.st i).data.regs.rax &&& 3) := by
  obtain ⟨-, hpb, PS, m₇, m, c, m9, mS, hF, h6, hb9, hV, hsz, hS, hfS, hk2S, hL5, -, hC, hfC, hkC, hnov⟩ :=
    (cmpEntry1_out k0 hcode bC bS pb h64 sa dm₀ ra₀ st₀ hR.call₀ hR.ret₀ hR.rdx₀ hR.rax₀ B hR.bufw hR.buflen)
  have hL0 : (B.getD 5 0).toNat ≠ 0 := fun h => hL5 (UInt64.toNat_inj.mp (by rw [h]; rfl))
  obtain ⟨e, hrax, hcase⟩ := cpThreadFail_runs k0 hcode dm₀ B hS _ rfl hL0 hC (B.getD 2 0) rfl t i
    hR.calls hR.zero hR.ret hR.acc hR.rdx hR.kept hR.next hR.incr
  rw [hrax] at hk ⊢
  change TwinCompareVerdictThr bC bS e.cls
  have hk0 : e.cls ≠ 0 := hk
  -- the other threads' chains
  have hthr := cpThreadsAcc_runs k0 hcode dm₀ st₀ B ths hR.others hS _ rfl hL0 hC (B.getD 2 0) c rfl hkC hnov
  obtain ⟨fS, hf'⟩ := Classical.axiomOfChoice hthr
  obtain ⟨fC, hf⟩ := Classical.axiomOfChoice hf'
  -- an index below the failing one, of the solution's phase, is in another thread's header-S chain
  have hcovS : ∀ j : Word, j < (t.dm i).regs.rdx → j < B.getD 2 0 →
      ∃ t' ∈ ths.map (fun t => (zeroMem checkerTab, fS t, fC t)), ∃ x ∈ t'.2.1, x.1 = j := by
    intro j hj hjS
    obtain ⟨t', ht', i', hi', hj'⟩ := hR.below j hj
    rcases (hf t' ht').2.2.2.2.2.2.1 i' hi' with ⟨-, x, hx, hxj⟩ | ⟨hge, -⟩
    · exact ⟨_, List.mem_map.mpr ⟨t', ht', rfl⟩, x, hx, by rw [hxj, hj']⟩
    · rw [hj'] at hge
      exact absurd hjS (UInt64.not_lt.mpr hge)
  rcases hcase with ⟨hph, cs, hruns, hcs⟩ | ⟨hge, csS, csC, hRS, hcsS, hincS1, hruns, hcs⟩
  · -- the solution's job fails
    obtain ⟨m2, m3, dsC, sG, res, m4, I, a', h, hI, -⟩ := F6.jobM hF h6
    exact cmpV_tjobSI hpb PS hF h6 hb9 h hI hV B hfS (B.getD 2 0) hk2S (zeroMem checkerTab)
      (cp_zeroOwned fun b hb => (hsz b hb).1) rfl _ cs abiFuel e hruns hcs hph hk0
      (ths.map fun t => (zeroMem checkerTab, fS t)) (fun t' ht' => by
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
        obtain ⟨h1, h2, -⟩ := hf t ht
        exact ⟨cp_zeroOwned fun b hb => (hsz b hb).1, rfl, h1, h2⟩)
      (fun t' ht' => by
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
        exact (hf t ht).2.2.1)
      (fun j hj => by
        obtain ⟨t', ht', x, hx, hxj⟩ := hcovS j hj (cp_lt_of_lt_le' hj (UInt64.le_of_lt hph))
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
        exact ⟨_, List.mem_map.mpr ⟨t, ht, rfl⟩, x, hx, hxj⟩)
  · -- the challenge's job fails, after the thread's solution calls
    have hcl := hR.claimed i (Nat.le_refl _)
    rw [hkC] at hcl
    refine c1Thr_failC_standin hpb PS hF h6 hb9 hV B hfS (B.getD 2 0) hk2S (B.extract (B.getD 5 0).toNat B.size) hfC
      (zeroMem checkerTab) (cp_zeroOwned fun b hb => (hsz b hb).1) rfl csS hRS hcsS hincS1 _ csC abiFuel e hruns hcs
      (cp_sub_lt hcl hge hnov) hk0 (ths.map fun t => (zeroMem checkerTab, fS t, fC t)) (fun t' ht' => ?_)
      (fun j hj => hcovS j (cp_lt_of_lt_le' hj hge) hj) (fun j hj => ?_) (fun t' ht' => ?_) (fun t' ht' => ?_)
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
      obtain ⟨h1, h2, -, h4, h5, -⟩ := hf t ht
      exact ⟨cp_zeroOwned fun b hb => (hsz b hb).1, rfl, h1, h2, h4, h5⟩
    · -- `kS + j` is below the failing index
      have e1 := UInt64.lt_iff_toNat_lt.mp hj
      have e2 := UInt64.le_iff_toNat_le.mp hge
      rw [UInt64.toNat_sub_of_le _ _ hge] at e1
      have hlt : B.getD 2 0 + j < (t.dm i).regs.rdx := UInt64.lt_iff_toNat_lt.mpr (by
        rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by have := UInt64.toNat_lt ((t.dm i).regs.rdx); omega)]; omega)
      obtain ⟨t', ht', i', hi', hj'⟩ := hR.below _ hlt
      rcases (hf t' ht').2.2.2.2.2.2.1 i' hi' with ⟨hlt', -⟩ | ⟨-, x, hx, hxj⟩
      · exfalso
        rw [hj'] at hlt'
        have := UInt64.lt_iff_toNat_lt.mp hlt'
        rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by have := UInt64.toNat_lt ((t.dm i).regs.rdx); omega)] at this
        omega
      · exact ⟨_, List.mem_map.mpr ⟨t', ht', rfl⟩, x, hx, by rw [hxj, hj', UInt64.add_comm, UInt64.add_sub_cancel]⟩
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
      exact (hf t ht).2.2.1
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
      exact (hf t ht).2.2.2.2.2.1

/-- **The verdict theorem for the threaded compared run of `checker.s`**: when the trusted
threaded harness's compared run reports a failure with the code `k` (`CmpThreadsFail`) of class
`1` (reject) or `2` (decline), the twin's comparison, run as the threads do, fails with that class
(`TwinCompareVerdictThr`). -/
theorem checkerFile_compare_threads_verdict [Host] (k0 : Nat) (hcode : Code checkerFile k0)
    (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64) (sa : Word)
    (dm₀ : MachineData) (ra₀ : Word) (st₀ : MachineState) (k : Word)
    (hF : CmpThreadsFail bC bS pb sa dm₀ ra₀ st₀ k) (hk : k &&& 3 ≠ 0) :
    TwinCompareVerdictThr bC bS (k &&& 3) := by
  rcases hF with ⟨hE, rfl⟩ | ⟨B, ths, t, i, hT, rfl⟩
  · exact .inl (cmpEntry1_fail k0 hcode bC bS pb h64 sa dm₀ ra₀ st₀ hE.call₀ hE.ret₀ hE.rdx₀ hk)
  · exact cmpThreadFail_twin k0 hcode bC bS pb h64 sa dm₀ ra₀ st₀ B ths t i hT hk

end ConAgua.Final
