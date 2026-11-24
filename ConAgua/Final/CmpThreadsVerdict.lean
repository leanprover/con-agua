module

public import ConAgua.Final.CmpThreads
public import ConAgua.Final.ThreadsVerdict

@[expose] public section

/-!
# The verdict theorem for the threaded compared run of the committed file (lane compare2)

`checkerFile_compare_threads_verdict`: the trusted threaded harness (`main.c`, `run_jobs` with a
solution) runs the compared entry 1 (`ca_start_ac`, `CmpCall`) and its threads over the buffer it
left, as in a flat threaded run (`Final/ThreadsVerdict.lean`). If the run reports a failure with
the code `k` (`CmpThreadsFail`: entry 1 returned `rdx = 2` with `rax = k`, or entry 1 returned ok
and some thread's call `i` returned `rdx = 2` with `rax = k`, its earlier calls accepted, and every
job index below call `i`'s was claimed by an accepting call), then for a class `k &&& 3` of `1`
(reject) or `2` (decline) the twin's pooled comparison fails with that class
(`TwinCompareVerdictPooledI bC bS`): a stage fails, or some worker's list of the solution's jobs
fails from the challenge's index state, or the solution's pool accepts there and some worker's
list of the challenge's jobs fails.

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
increasing indices (`ThreadFail` has only the earlier calls below call `i`: here the phase of each
call decides which half of the region it uses, so the order among them matters). -/
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

/-- **A thread's failing call in a compared run is the twin's pooled failure** (TODO: the proof;
the failing thread's two chains as `cpThreadsAcc_runs` builds them, the call's phase by its index
against `kS`, then `cmpV_tjobSI` resp. `cmpThreadsS_poolI` + `cmpV_tjobCI`). -/
theorem cmpThreadFail_twin [Host] (k0 : Nat) (hcode : Code checkerFile k0)
    (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64) (sa : Word)
    (dm₀ : MachineData) (ra₀ : Word) (st₀ : MachineState) (B : Array Word) (ths : List ThreadM)
    (t : ThreadM) (i : Nat) (hR : CmpThreadFail bC bS pb sa dm₀ ra₀ st₀ B ths t i)
    (hk : (t.st i).data.regs.rax &&& 3 ≠ 0) :
    TwinCompareVerdictPooledI bC bS ((t.st i).data.regs.rax &&& 3) := by
  sorry

/-- **The verdict theorem for the threaded compared run of `checker.s`**: when the trusted
threaded harness's compared run reports a failure with the code `k` (`CmpThreadsFail`) of class
`1` (reject) or `2` (decline), the twin's pooled comparison fails with that class, both phases'
jobs from the challenge's index state (`TwinCompareVerdictPooledI`). -/
theorem checkerFile_compare_threads_verdict [Host] (k0 : Nat) (hcode : Code checkerFile k0)
    (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64) (sa : Word)
    (dm₀ : MachineData) (ra₀ : Word) (st₀ : MachineState) (k : Word)
    (hF : CmpThreadsFail bC bS pb sa dm₀ ra₀ st₀ k) (hk : k &&& 3 ≠ 0) :
    TwinCompareVerdictPooledI bC bS (k &&& 3) := by
  rcases hF with ⟨hE, rfl⟩ | ⟨B, ths, t, i, hT, rfl⟩
  · exact cmpEntry1_fail k0 hcode bC bS pb h64 sa dm₀ ra₀ st₀ hE.call₀ hE.ret₀ hE.rdx₀ hk
  · exact cmpThreadFail_twin k0 hcode bC bS pb h64 sa dm₀ ra₀ st₀ B ths t i hT hk

end ConAgua.Final
