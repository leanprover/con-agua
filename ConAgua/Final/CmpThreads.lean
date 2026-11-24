module

public import ConAgua.Final.CpThreads
public import ConAgua.Final.CmpEntry1
public import ConAgua.Final.CmpAbi
public import ConAgua.Final.CompareTwinI
import ConAgua.Final.CompareTwinThr
public import ConAgua.Checker.CmpSPhaseThr
import ConAgua.Final.DrvFinal
import ConAgua.Final.BufAbi
public import ConAgua.Checker.ProgTab
public import ConAguaAsm.Checker

@[expose] public section

/-!
# The threaded compared run, end to end, for the committed file (lane compare2)

`checkerFile_compare_threads_accept`: the trusted threaded harness (`main.c`, `run_jobs` with a
solution) calls entry 1 of `checker.s` in its compared form, `ca_start_ac` (the challenge's bytes
as `ca_start_a`'s input, the solution's on the stack: `CmpCall`), which leaves one frozen buffer
with two headers in `OUT` and returns `2^63 + kS + kC`; then the threads claim the job indices
`0, …, kS + kC - 1` and call `ca_check_b` on each, exactly as in the flat threaded run
(`ThreadsAcc`): entry 2 maps the indices below `kS` (the buffer's word `2`) to the solution's
jobs (header S) and the others to the challenge's jobs (header C, at the buffer's word `5`), on
the thread's one region: a thread's solution jobs come first (its claims increase), then its
challenge jobs continue on the region as they left it. If every call reports accept, the twin
accepts the comparison as the threaded run does (`TwinComparesAcceptsThr bC bS`: the stages up to
the challenge's index state, then each worker its solution jobs from there and, continuing, its
challenge jobs).

**What the theorem trusts of the harness** (the hypotheses of `CmpThreadsRun`; they are
`ThreadsRun`'s, `Final/ThreadsFinal.lean`, with the compared entry 1, and what
`Final/Statement.lean` lists): entry 1's call (`CmpCall`) and first return; the buffer `OUT`'s
first `len` words at entry 1's return, `len` its word `1`, in place and read-only for the threads;
each thread's region its own, zero at its first call and carried over between its calls; every
claimed index below `k`, every index below `k` claimed, each thread's claims increasing; entry 1
returns `rdx = 0`, `rax ≥ 2^63`, every call `rdx = 0`, `rax = ACCEPT`.
-/


namespace ConAgua.Final

universe w

open L L.Compiler L.Checker L.Arena ConRon.Arena

/-! ## The harness's facts -/

/-- **What the threaded harness does in a compared run** (trusted; the module doc lists it):
`ThreadsRun`'s facts, entry 1 the compared one (`ca_start_ac`, called as `CmpCall` says, the
solution's bytes the stack arguments). -/
structure CmpThreadsRun [Host] (bC bS pb : ByteArray) (sa : Word) (dm₀ : MachineData) (ra₀ : Word)
    (st₀ : MachineState) (B : Array Word) (ths : List ThreadM) : Prop extends ThreadsAcc dm₀ st₀ B ths where
  call₀ : CmpCall bC bS pb sa dm₀ ra₀
  ret₀ : FirstReturn dm₀ (label abiStartACL) ra₀ st₀
  rdx₀ : st₀.data.regs.rdx = 0
  rax₀ : 9223372036854775808 ≤ st₀.data.regs.rax.toNat
  /-- the buffer: `OUT`'s first `len` words, `len` its word `1` -/
  bufw : ∀ i (h : i < B.size), rdW st₀.data.dmem (A (outAddr dm₀.regs.r8.toNat + 8 * i)) = some B[i]
  buflen : ∃ w, rdW st₀.data.dmem (A (outAddr dm₀.regs.r8.toNat + 8)) = some w ∧ w.toNat = B.size
  cover : ∀ j : Word, j < st₀.data.regs.rax - 9223372036854775808 → ∃ t ∈ ths, ∃ i < t.n, (t.dm i).regs.rdx = j

/-! ## Entry 1: `CmpOut`, `cmpEntry1_out`, `cmpEntry1_fail` (`Final/CmpEntry1.lean`) -/

/-! ## Pieces -/

/-- The zero region holds zero owned arrays of the lengths `m`'s layout gives them. -/
theorem cp_zeroOwned {m : Mem} (hsz : ∀ b ∈ parOwnedL, (m.arr64 b).size = abiSz checkerTab b) :
    ∀ b ∈ parOwnedL, (zeroMem checkerTab).arr64 b = zeros (m.arr64 b).size := by
  intro b hb
  rw [hsz b hb]
  simp [zeroMem, Mem.arr64, zeros]

/-- An index of the first phase is below the whole count. -/
theorem cp_lt_add {j kS c : Word} (h : j < kS) (hnov : kS.toNat + c.toNat < 2 ^ 64) : j < kS + c := by
  have := UInt64.lt_iff_toNat_lt.mp h
  exact UInt64.lt_iff_toNat_lt.mpr (by rw [UInt64.toNat_add, Nat.mod_eq_of_lt hnov]; omega)

/-- An index of the second phase, shifted, is below the whole count. -/
theorem cp_add_lt {j kS c : Word} (h : j < c) (hnov : kS.toNat + c.toNat < 2 ^ 64) : kS + j < kS + c := by
  have := UInt64.lt_iff_toNat_lt.mp h
  have hj : kS.toNat + j.toNat < 2 ^ 64 := by omega
  refine UInt64.lt_iff_toNat_lt.mpr ?_
  rw [UInt64.toNat_add, UInt64.toNat_add, Nat.mod_eq_of_lt hnov, Nat.mod_eq_of_lt hj]
  omega

/-! ## Stand-ins (to be proved) -/

/-- **Stand-in (L level, lane compare2 H7)**: the threads over both headers, each a fresh region
running its solution calls over header S (`B`, first call at `mS`'s fresh memory) and then,
continuing from the memory they left (`runsEnd`), its challenge calls over header C (`BC`),
together claiming every job of each phase, each phase's claims increasing in each thread: the
twin accepts the comparison as the threaded run does. -/
theorem c1Thr_accepts_standin {bC bS pb : ByteArray} (hpb : pb.size < 2 ^ 63) (PS : PhaseS bC bS)
    {m₇ m : Mem} (hF : FoldOn bS pb (abiSz checkerTab) PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m)
    {c : Word} {m9 mS : Mem} (h6 : F6 PS m c m9) (hb9 : m9.bytes = m.bytes) (hV : CsViewS m m9 mS)
    (B : Array Word) (hBS : CsFirst B mS) (khi : Word) (hk : khi.toNat = PS.dsS.size)
    (BC : Array Word) (hBC : CsFirst BC m9)
    (ths : List (Mem × List (Word × Nat × Mem) × List (Word × Nat × Mem)))
    (hth : ∀ t ∈ ths, (∀ b ∈ parOwnedL, t.1.arr64 b = zeros (mS.arr64 b).size) ∧ t.1.glob INIT = 0 ∧
      ThreadRuns B t.1 t.2.1 ∧ (∀ c' ∈ t.2.1, c'.1 < khi) ∧
      ThreadRuns BC (runsEnd t.1 t.2.1) t.2.2 ∧ ∀ c' ∈ t.2.2, c'.1 < c)
    (hcovS : ∀ j : Word, j < khi → ∃ t ∈ ths, ∃ c' ∈ t.2.1, c'.1 = j)
    (hcovC : ∀ j : Word, j < c → ∃ t ∈ ths, ∃ c' ∈ t.2.2, c'.1 = j)
    (hincS : ∀ t ∈ ths, (t.2.1.map (·.1)).Pairwise (· < ·))
    (hincC : ∀ t ∈ ths, (t.2.2.map (·.1)).Pairwise (· < ·)) :
    TwinComparesAcceptsThr bC bS := by
  sorry

/-! ## The theorem -/

set_option linter.constructorNameAsVariable false in
/-- **The compared threads' accept is the twin's threaded accept**, for the committed file
`checker.s`: the trusted threaded harness runs as `CmpThreadsRun` says. And every call returns
with the caller's registers. -/
theorem cmpThreadsRun_twinThr_regs [Host] (k0 : Nat) (hcode : Code checkerFile k0)
    (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64) (sa : Word)
    (dm₀ : MachineData) (ra₀ : Word) (st₀ : MachineState) (B : Array Word) (ths : List ThreadM)
    (hR : CmpThreadsRun bC bS pb sa dm₀ ra₀ st₀ B ths) : TwinComparesAcceptsThr bC bS ∧
      RegsRestored dm₀.regs st₀.data.regs ∧
      ∀ t ∈ ths, ∀ i < t.n, RegsRestored (t.dm i).regs (t.st i).data.regs := by
  obtain ⟨hRR₀, hpb, PS, m₇, m, c, m9, mS, hF, h6, hb9, hV, hsz, hS, hfS, hk2S, hL5, -, hC, hfC, hk, hnov⟩ :=
    cmpEntry1_out k0 hcode bC bS pb h64 sa dm₀ ra₀ st₀ hR.call₀ hR.ret₀ hR.rdx₀ hR.rax₀ B hR.bufw hR.buflen
  have hL0 : (B.getD 5 0).toNat ≠ 0 := fun h => hL5 (UInt64.toNat_inj.mp (by rw [h]; rfl))
  have hthr := cpThreadsAcc_runs k0 hcode dm₀ st₀ B ths hR.toThreadsAcc hS _ rfl hL0 hC (B.getD 2 0) c rfl
    hk hnov
  obtain ⟨fS, hf'⟩ := Classical.axiomOfChoice hthr
  obtain ⟨fC, hf⟩ := Classical.axiomOfChoice hf'
  refine ⟨?_, hRR₀, fun t ht i hi => (hf t ht).2.2.2.2.2.2.2 i hi⟩
  refine c1Thr_accepts_standin hpb PS hF h6 hb9 hV B hfS (B.getD 2 0) hk2S
    (B.extract (B.getD 5 0).toNat B.size) hfC
    (ths.map fun t => (zeroMem checkerTab, fS t, fC t)) (fun t' ht' => ?_) (fun j hj => ?_) (fun j hj => ?_)
    (fun t' ht' => ?_) (fun t' ht' => ?_)
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    obtain ⟨h1, h2, -, h4, h5, -⟩ := hf t ht
    exact ⟨cp_zeroOwned fun b hb => (hsz b hb).1, rfl, h1, h2, h4, h5⟩
  · obtain ⟨t, ht, i, hi, hj'⟩ := hR.cover j (by rw [hk]; exact cp_lt_add hj hnov)
    rcases (hf t ht).2.2.2.2.2.2.1 i hi with ⟨-, x, hx, hxj⟩ | ⟨hge, -⟩
    · exact ⟨_, List.mem_map.mpr ⟨t, ht, rfl⟩, x, hx, by rw [hxj, hj']⟩
    · rw [hj'] at hge
      exact absurd hj (UInt64.not_lt.mpr hge)
  · obtain ⟨t, ht, i, hi, hj'⟩ := hR.cover (B.getD 2 0 + j) (by rw [hk]; exact cp_add_lt hj hnov)
    rcases (hf t ht).2.2.2.2.2.2.1 i hi with ⟨hlt, -⟩ | ⟨-, x, hx, hxj⟩
    · rw [hj'] at hlt
      exfalso
      have := UInt64.lt_iff_toNat_lt.mp hlt
      have := UInt64.lt_iff_toNat_lt.mp hj
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)] at *
      omega
    · exact ⟨_, List.mem_map.mpr ⟨t, ht, rfl⟩, x, hx, by rw [hxj, hj', UInt64.add_comm, UInt64.add_sub_cancel]⟩
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    exact (hf t ht).2.2.1
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    exact (hf t ht).2.2.2.2.2.1

/-! ## The final statements -/

/-- **The compared threads' accept** (`TwinComparesAcceptsThr`). -/
theorem checkerFile_compare_threads_accept [Host] (k0 : Nat) (hcode : Code checkerFile k0)
    (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64) (sa : Word)
    (dm₀ : MachineData) (ra₀ : Word) (st₀ : MachineState) (B : Array Word) (ths : List ThreadM)
    (hR : CmpThreadsRun bC bS pb sa dm₀ ra₀ st₀ B ths) : TwinComparesAcceptsThr bC bS :=
  (cmpThreadsRun_twinThr_regs k0 hcode bC bS pb h64 sa dm₀ ra₀ st₀ B ths hR).1

/-- **The compared threads' registers**: entry 1 and every `ca_check_b` call return with the
caller's callee-saved registers. -/
theorem checkerFile_compare_threads_regs [Host] (k0 : Nat) (hcode : Code checkerFile k0)
    (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64) (sa : Word)
    (dm₀ : MachineData) (ra₀ : Word) (st₀ : MachineState) (B : Array Word) (ths : List ThreadM)
    (hR : CmpThreadsRun bC bS pb sa dm₀ ra₀ st₀ B ths) :
    RegsRestored dm₀.regs st₀.data.regs ∧ ∀ t ∈ ths, ∀ i < t.n, RegsRestored (t.dm i).regs (t.st i).data.regs :=
  (cmpThreadsRun_twinThr_regs k0 hcode bC bS pb h64 sa dm₀ ra₀ st₀ B ths hR).2

/-- **An accepting compared threaded run's challenge has a model** (relative to set theory). -/
theorem checkerFile_compare_threads_model (V : Type w) [ConLeche.SetTheory V] [Host] (k0 : Nat)
    (hcode : Code checkerFile k0) (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64) (sa : Word)
    (dm₀ : MachineData) (ra₀ : Word) (st₀ : MachineState) (B : Array Word) (ths : List ThreadM)
    (hR : CmpThreadsRun bC bS pb sa dm₀ ra₀ st₀ B ths) :
    ∃ (rcC : ConLeche.Frontend.ParseResultD) (preC : ConLeche.Frontend.PreludeIx),
      ConLeche.Frontend.parseChunks [bC] = .ok rcC ∧
      Nonempty (ConLeche.Model V (ConLeche.streamEnv
        ((ConLeche.Frontend.preparePrelude preC rcC.decls).toList.map ConLeche.Cached.sideRecord))) :=
  twinComparesAcceptsThr_model V
    (checkerFile_compare_threads_accept k0 hcode bC bS pb h64 sa dm₀ ra₀ st₀ B ths hR)

/-- **No compared threaded run accepts a challenge with a theorem of type `False`** (relative to set
theory). -/
theorem checkerFile_compare_threads_no_False (V : Type w) [ConLeche.SetTheory V] [Host] (k0 : Nat)
    (hcode : Code checkerFile k0) (bC bS pb : ByteArray) (hfalse : ConLeche.jsonWithTheoremFalse [bC])
    (h64 : System.Platform.numBits = 64) (sa : Word)
    (dm₀ : MachineData) (ra₀ : Word) (st₀ : MachineState) (B : Array Word) (ths : List ThreadM)
    (hR : CmpThreadsRun bC bS pb sa dm₀ ra₀ st₀ B ths) : False :=
  twinComparesAcceptsThr_no_False V hfalse
    (checkerFile_compare_threads_accept k0 hcode bC bS pb h64 sa dm₀ ra₀ st₀ B ths hR)

end ConAgua.Final
