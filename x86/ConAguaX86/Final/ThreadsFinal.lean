module

public import ConAguaX86.Final.BufChain
public import ConAguaX86.Compiler.AbiCmp
import ConAguaX86.Final.DrvFinal
public import ConAgua.Checker.ParThreadTwin
import ConAguaX86.Final.BufAbi
import ConAguaX86.Checker.AsmFinal
import ConAgua.Checker.CheckARun
import ConAgua.Checker.ProgIRef
import ConAguaX86.Checker.AsmXOk
import ConAgua.Checker.ProgWf
public import ConAgua.Checker.ProgTab
public import ConAguaAsm.Checker
import all ConAgua.Checker.Entry
import ConAgua.L.WordOff

@[expose] public section

/-!
# The threads end to end, for the committed file

`threadsRun_twinAcceptsPooled` (restated as `checkerFile_threads_accept` in
`Final/EndToEnd.lean`, with the model and no-`False` corollaries): the trusted threaded harness
(`main.c`, `run_jobs`) runs entry 1 (`ca_start_a`: the stages, the stream index and the frozen
buffer; it returns `2^63 + k` for `k` records) of `checker.s`, hands the buffer it left to its
threads, and each thread calls `ca_check_b` once per job index it claims (a record's position: the
record's job at the stream index's view of it), on its own region (`ThreadsRun`). If every call
reports accept, the threads claim every job index and each thread's claims increase, the twin's
pooled pipeline accepts `[b]` (`TwinAcceptsPooled [b]`). Relative to a set theory `V`: con-ron's
fold invariant at a job's view comes from the model of the accepted prefix.

**What the theorem trusts of the harness** (the hypotheses of `ThreadsRun`, whose per-thread
facts are `ThreadsAcc`, which the threaded verdict reuses for the jobs below a failing one; beyond
them, what `Final/Statement.lean` lists: Kraken's semantics, the assembler, linker and loader):

* **Entry 1's call**: `ca_start_a` (with a solution: `ca_start_ac`) is called as `AbiCall` says (the input and pin buffers, a zero
  region, the 32 bytes of machine stack around `rsp`; `mmap` gives the stated memory facts).
* **First return** (`FirstReturn`): the harness regains control, at each call's return address,
  in a state that has every property the machine is guaranteed to reach at that address
  (`abiA_outcome`'s and `abiB_outcome`'s posts).
* **The buffer** is the first `len` words of `OUT`'s slot of entry 1's region at its return, `len`
  `OUT`'s word `1`, and stays in place: every thread's call is passed its address and sees the
  same words, before the call and at its return (**route A**: read-only, `mprotect`).
* **Each thread's region** is its own (pthreads: the threads' regions are apart from each other,
  from the buffer and from every thread's stack window): zero at the thread's first call, and at
  each later call holding the bytes the previous call left. Each call is made as `BufCallH` says
  (the region mapped and large enough, the buffer apart from it, the return address and the
  32-byte stack window).
* **The claim counter's coverage**: every claimed job index `j` (in `rdx`) is below `k`
  (`k = rax - 2^63` from entry 1), and every index below `k` is claimed by some thread.
* **The claims increase** in each thread: a thread's later call claims a larger index (`main.c`
  claims off one monotone counter; con-ron's pool, `PooledAccepts`, has each worker's jobs
  increasing, since a job's start state is reached through the jobs before it).
* The verdicts: entry 1 returns `rdx = 0`, `rax ≥ 2^63`; every call returns `rdx = 0`,
  `rax = ACCEPT`.
-/

namespace ConAgua.Final

universe w

open L L.Compiler L.Checker L.Arena ConRon.Arena

/-! ## Entry 1's buffer, at the L level -/

/-- **Entry 1's buffer** (the first `len` words of `OUT`, `len` its word `1`, after a run of
`check` in mode `1` that returned `2^63 + k`): inside `OUT`, at least the header long, its header
entries inside it and in increasing order. -/
theorem entry1_buf (b pb : ByteArray) (sz : TieredArray → Nat) (hin : InputsOK b pb sz)
    (N : Nat) (hN : N < 2 ^ 62) (rs₁ : List Word) (m₁ : Mem)
    (h₁ : L.run checkerProg N "check" [] (loadMemM b pb sz 1) = .ok (rs₁, m₁))
    (hge : 9223372036854775808 ≤ (rs₁.headD 0).toNat)
    (B : Array Word) (hB : B = (m₁.arr64 OUT).extract 0 ((m₁.arr64 OUT).getD 1 0).toNat) :
    ((m₁.arr64 OUT).getD 1 0).toNat ≤ (m₁.arr64 OUT).size ∧ hdrW ≤ ((m₁.arr64 OUT).getD 1 0).toNat ∧
      (∀ i < frozenIdsL.length, (bufEntry B i).1 + (bufEntry B i).2 ≤ B.size) ∧
      (∀ i < frozenIdsL.length, ∀ i' < frozenIdsL.length, i < i' →
        (bufEntry B i).1 + (bufEntry B i).2 ≤ (bufEntry B i').1) := by
  have hr : rs₁.headD 0 ≠ 1 := fun e => by rw [e] at hge; simp at hge
  obtain ⟨PA, m₇, m, -, hok, hm₁, -⟩ := checkA_run b pb sz hin 1 (Or.inl rfl) N hN rs₁ m₁ h₁ hr
  have hflag : modeFlag 1 = 1 := rfl
  rw [hflag] at hok hm₁
  have hF := parCompactMem_out m 1
  rw [← hm₁] at hF
  have hlt : (m.arr64 OUT).size < 2 ^ 64 := by
    rw [← hF.size OUT]; exact run_load_size hin.2.2.2 h₁ OUT
  have hlen : ((m₁.arr64 OUT).getD 1 0).toNat = (fzOff m frozen.length).toNat := by
    rw [hm₁, (parCompactMem_hdr hok).2.1]
  have hBm : B = bufOf m := by rw [hB, bufOf, hm₁, (parCompactMem_hdr hok).2.1]
  have hs := bufOf_size hok hlt
  have hoffs := buf_offs hok hlt
  have hFl := frozen_length
  have hL : frozenIdsL.length = frozen.length + 1 := by rw [frozenIdsL_eq]; simp
  refine ⟨by rw [hlen, hF.size, hs.2]; exact hoffs.2, by rw [hlen, hs.2]; omega,
    fun i hi => hBm ▸ buf_entries_inside hok hlt hi, fun i hi i' hi' hii => ?_⟩
  rw [hBm]
  obtain ⟨c, rfl⟩ : ∃ c, i' = c + 1 := ⟨i' - 1, by omega⟩
  obtain ⟨he', ho'⟩ := bufEntry_succ hok hlt (i := c) (by omega)
  rw [he', ho']
  rcases i with _ | a
  · rw [bufEntry_zero hok hlt]; simp only; omega
  · obtain ⟨he, ho⟩ := bufEntry_succ hok hlt (i := a) (by omega)
    rw [he, ho]
    have := fzSum_mono m (j := a + 1) (n := c) (by omega)
    rw [fzSum_succ, ← fzExt_eq] at this
    simp only; omega

/-- **Entry 1's buffer counts its jobs**: `OUT`'s word `2` (the header's record count) is
`k = rax - 2^63`, entry 1's result less `2^63`. -/
theorem entry1_word2 (b pb : ByteArray) (sz : TieredArray → Nat) (hin : InputsOK b pb sz)
    (N : Nat) (hN : N < 2 ^ 62) (rs₁ : List Word) (m₁ : Mem)
    (h₁ : L.run checkerProg N "check" [] (loadMemM b pb sz 1) = .ok (rs₁, m₁))
    (hge : 9223372036854775808 ≤ (rs₁.headD 0).toNat) :
    (m₁.arr64 OUT).getD 2 0 = rs₁.headD 0 - 9223372036854775808 := by
  have hr : rs₁.headD 0 ≠ 1 := fun e => by rw [e] at hge; simp at hge
  obtain ⟨PA, m₇, m, hF, hok, hm₁, hrs⟩ := checkA_run b pb sz hin 1 (Or.inl rfl) N hN rs₁ m₁ h₁ hr
  have hflag : modeFlag 1 = 1 := rfl
  rw [hflag] at hok hm₁
  rw [hm₁, (parCompactMem_hdr hok).2.2.1, hrs, show ∀ a b : Word, a + b - a = b from fun a b => by
    rw [UInt64.add_comm, UInt64.add_sub_cancel]]
  have hc := hF.build.decls.count
  simp only [rd64, Array.getD_eq_getD_getElem?, show (0 : Word).toNat = 0 from rfl]
  rw [← hc, UInt64.ofNat_toNat]

/-- The buffer's word `2` is entry 1's job count (`entry1_word2`, on `OUT`'s prefix). -/
theorem entry1_k (b pb : ByteArray) (sz : TieredArray → Nat) (hin : InputsOK b pb sz)
    (N : Nat) (hN : N < 2 ^ 62) (rs₁ : List Word) (m₁ : Mem)
    (h₁ : L.run checkerProg N "check" [] (loadMemM b pb sz 1) = .ok (rs₁, m₁))
    (hge : 9223372036854775808 ≤ (rs₁.headD 0).toNat)
    (B : Array Word) (hBeq : B = (m₁.arr64 OUT).extract 0 ((m₁.arr64 OUT).getD 1 0).toNat)
    (h2 : 2 < B.size) : rs₁.headD 0 - 9223372036854775808 ≤ B.getD 2 0 := by
  rw [← entry1_word2 b pb sz hin N hN rs₁ m₁ h₁ hge, hBeq]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_extract]
  rw [hBeq] at h2
  simp only [Array.size_extract] at h2
  simp only [Array.getD_eq_getD_getElem?] at h2 ⊢
  rw [ite_eq_left h2, Nat.zero_add]
  exact UInt64.le_refl _

/-! ## The harness's facts -/

/-- **First return** (trusted): the harness regains control from the call made at `dm` (code
`pc`) in the state `st`, which has every property the machine is guaranteed to reach at the
return address `ra`. -/
def FirstReturn [Host] (dm : MachineData) (pc : Int64) (ra : Word) (st : MachineState) : Prop :=
  ∀ P : MachineState → Prop, Ev P dm pc → (∀ s, P s → s.pc = Int64.ofBitVec ra.toBitVec) → P st

/-- **Entry 1's label**: `ca_start_a` (the flat threaded run), `ca_start_ac` with a solution (the
compared threaded run). -/
def abiEntryAL : Option ByteArray → Label
  | none => abiStartAL
  | some _ => abiStartACL

/-- **The sequential driver's label**: `ca_start`, `ca_start_c` with a solution (the sequential
compared run). -/
def abiSeqL : Option ByteArray → Label
  | none => abiStartL
  | some _ => abiStartCL

/-- **How a thread calls `ca_check_b`** (the harness's part of `BufCall`; the buffer's header
facts come from entry 1): the region mapped, large enough and in the address space, the buffer
holding `B` and apart from the region, the return address and the stack window. -/
structure BufCallH (B : Array Word) (dm : MachineData) (ra : Word) : Prop where
  need : workerNeed parOwnedL ≤ dm.regs.r8.toNat
  fits : dm.regs.rcx.toNat + dm.regs.r8.toNat < 2 ^ 64
  bend : dm.regs.rdi.toNat + 8 * B.size < 2 ^ 64
  apart : ∀ x, dm.regs.rdi.toNat ≤ x → x < dm.regs.rdi.toNat + 8 * B.size →
    x < dm.regs.rcx.toNat ∨ dm.regs.rcx.toNat + dm.regs.r8.toNat ≤ x
  hB : ∀ i (h : i < B.size), rdW dm.dmem (A (dm.regs.rdi.toNat + 8 * i)) = some B[i]
  hmap : ∀ x, dm.regs.rcx.toNat ≤ x → x < dm.regs.rcx.toNat + dm.regs.r8.toNat → (dm.dmem.get? (A x)).isSome
  hra : rdW dm.dmem (A dm.regs.rsp.toNat) = some ra
  hcs : ∀ x, dm.regs.rsp.toNat - 24 ≤ x → x < dm.regs.rsp.toNat + 8 →
    (dm.dmem.get? (A x)).isSome ∧ (x < dm.regs.rcx.toNat ∨ dm.regs.rcx.toNat + dm.regs.r8.toNat ≤ x) ∧
    ¬ (dm.regs.rdi.toNat ≤ x ∧ x < dm.regs.rdi.toNat + 8 * B.size)
  hcs24 : 24 ≤ dm.regs.rsp.toNat
  hcs8 : dm.regs.rsp.toNat + 8 < 2 ^ 64

/-- A thread on the machine: its calls `i < n` (state at the call `dm i`, return address `ra i`,
state at the return `st i`) on the region `[base, base + blen)`. -/
structure ThreadM where
  n : Nat
  dm : Nat → MachineData
  ra : Nat → Word
  st : Nat → MachineState
  base : Nat
  blen : Nat

/-- The address of `OUT`'s slot in entry 1's region at `base`. -/
def outAddr (base : Nat) : Nat := base + abiSlot * abiSlot64 checkerTab OUT

/-- **The threads' accepting calls** (trusted; the module doc lists it): for entry 1 at `dm₀`
returning at `st₀` and the buffer `B`, every call `i < t.n` of each thread `t` of `ths` is made
with the buffer in place and on the thread's region, returns accept with the buffer kept, and
claims a job index below `k`; each thread's region is zero at its first call and carries over
between its calls, and its claims increase. -/
structure ThreadsAcc [Host] (dm₀ : MachineData) (st₀ : MachineState) (B : Array Word)
    (ths : List ThreadM) : Prop where
  /-- the calls: the buffer in place, each thread on its region -/
  calls : ∀ t ∈ ths, ∀ i < t.n, BufCallH B (t.dm i) (t.ra i) ∧
    (t.dm i).regs.rdi.toNat = outAddr dm₀.regs.r8.toNat ∧ (t.dm i).regs.rcx.toNat = t.base ∧
    (t.dm i).regs.r8.toNat = t.blen
  zero : ∀ t ∈ ths, 0 < t.n → ∀ x, t.base ≤ x → x < t.base + t.blen → (t.dm 0).dmem.get? (A x) = some 0
  ret : ∀ t ∈ ths, ∀ i < t.n, FirstReturn (t.dm i) (label abiCheckBL) (t.ra i) (t.st i)
  acc : ∀ t ∈ ths, ∀ i < t.n, (t.st i).data.regs.rdx = 0 ∧ (t.st i).data.regs.rax = ACCEPT
  /-- route A: the buffer's words at each call's return -/
  kept : ∀ t ∈ ths, ∀ i < t.n, ∀ q (h : q < B.size),
    rdW (t.st i).data.dmem (A (outAddr dm₀.regs.r8.toNat + 8 * q)) = some B[q]
  next : ∀ t ∈ ths, ∀ i, i + 1 < t.n → ∀ x, t.base ≤ x → x < t.base + t.blen →
    (t.dm (i + 1)).dmem.get? (A x) = (t.st i).data.dmem.get? (A x)
  claimed : ∀ t ∈ ths, ∀ i < t.n, (t.dm i).regs.rdx < st₀.data.regs.rax - 9223372036854775808
  /-- the claims increase in each thread (the claim counter is monotone) -/
  incr : ∀ t ∈ ths, ∀ i j, i < j → j < t.n → (t.dm i).regs.rdx < (t.dm j).regs.rdx

/-- **What the threaded harness does** (trusted; the module doc lists it): entry 1 at `dm₀`
returning at `st₀`, the buffer `B`, and the threads `ths`, whose calls all accept
(`ThreadsAcc`) and claim every job index below `k`. -/
structure ThreadsRun [Host] (b : ByteArray) (sol : Option ByteArray) (pb : ByteArray) (dm₀ : MachineData)
    (ra₀ : Word) (st₀ : MachineState) (B : Array Word) (ths : List ThreadM) : Prop
    extends ThreadsAcc dm₀ st₀ B ths where
  call₀ : AbiCall b sol pb dm₀ ra₀
  ret₀ : FirstReturn dm₀ (label (abiEntryAL sol)) ra₀ st₀
  rdx₀ : st₀.data.regs.rdx = 0
  rax₀ : 9223372036854775808 ≤ st₀.data.regs.rax.toNat
  /-- the buffer: `OUT`'s first `len` words, `len` its word `1` -/
  bufw : ∀ i (h : i < B.size), rdW st₀.data.dmem (A (outAddr dm₀.regs.r8.toNat + 8 * i)) = some B[i]
  buflen : ∃ w, rdW st₀.data.dmem (A (outAddr dm₀.regs.r8.toNat + 8)) = some w ∧ w.toNat = B.size
  cover : ∀ j : Word, j < st₀.data.regs.rax - 9223372036854775808 → ∃ t ∈ ths, ∃ i < t.n, (t.dm i).regs.rdx = j

/-! ## Pieces -/

/-- The frozen arrays are in the checker's layout (the kernel evaluates the layout map). -/
theorem frozenIdsL_dom : frozenIdsL.all (checkerTab.dom64 ·) = true := by decide +kernel

/-- Every array with a minimum length is frozen or owned (`ca_check_b`'s layout gives the others
no memory). -/
theorem checker_bufMinOk : bufMinOk checkerTab frozenIdsL parOwnedL = true := by decide +kernel

/-- No owned array is frozen. -/
theorem parOwnedL_not_frozen : ∀ a ∈ parOwnedL, a ∉ frozenIdsL := by
  have h : parOwnedL.all (fun a => !frozenIdsL.contains a) = true := by decide +kernel
  intro a ha hf
  have := List.all_eq_true.mp h a ha
  simp [hf] at this

/-- The owned arrays are in the checker's layout. -/
theorem parOwnedL_dom : ∀ a ∈ parOwnedL, checkerTab.dom64 a = true := by
  have h : parOwnedL.all (checkerTab.dom64 ·) = true := by decide +kernel
  exact List.all_eq_true.mp h

/-- The final memory's frozen arrays are the buffer's images, when the buffer is unchanged. -/
theorem bufKept_of_memRel {B : Array Word} {buf base : Nat} {r : Mem} {d : DataMem}
    (hm : MemRel (bufLayout checkerTab buf B base frozenIdsL parOwnedL) r d)
    (hent : ∀ i < frozenIdsL.length, (bufEntry B i).1 + (bufEntry B i).2 ≤ B.size)
    (hkept : ∀ q (h : q < B.size), rdW d (A (buf + 8 * q)) = some B[q]) : BufKept B r := by
  intro k hk h1
  obtain ⟨hidx, -, -⟩ := frozen_facts hk h1
  have hnw : checkerTab.dom64 ↑frozen[k].1 = true := by
    obtain ⟨hl, e, -⟩ := List.idxOf?_eq_some_iff.mp hidx
    rw [← e]; exact List.all_eq_true.mp frozenIdsL_dom _ (List.getElem_mem _)
  have h59 : k + 1 < frozenIdsL.length := by rw [frozenIdsL_eq]; simp; omega
  have he := hent (k + 1) h59
  have hs := hm.size64 _ hnw
  simp only [bufLayout_tab] at hs
  rw [bufLayout_s64 _ _ _ _ _ _ (checkerTab.pos64_lt hnw).1, checkerTab.wAt_pos64 hnw] at hs
  simp only [bufL, hidx] at hs
  apply Array.ext
  · rw [hs]; simp only [bufImg, Array.size_extract]; omega
  · intro i h₁ h₂
    have hg := hm.get64 _ hnw i h₁
    simp only [bufLayout_tab] at hg
    rw [bufLayout_b64 _ _ _ _ _ _ (checkerTab.pos64_lt hnw).1, checkerTab.wAt_pos64 hnw] at hg
    simp only [bufB, hidx] at hg
    rw [show buf + 8 * (bufEntry B (k + 1)).1 + 8 * i = buf + 8 * ((bufEntry B (k + 1)).1 + i) by omega,
      hkept _ (by rw [hs] at h₁; omega)] at hg
    simp only [bufImg, Array.getElem_extract]
    exact (Option.some.inj hg).symm

/-- A thread's calls, as `ThreadRuns` lists them. -/
def thrCalls (t : ThreadM) (rm : Nat → Mem) : List (Word × Nat × Mem) :=
  (List.range t.n).map fun i => ((t.dm i).regs.rdx, abiFuel, rm (i + 1))

theorem threadRuns_range (B : Array Word) (t : ThreadM) (rm : Nat → Mem)
    (h : ∀ i < t.n, (∃ rs, L.run checkerProg abiFuel "check" [] (bufMem B (rm i) (t.dm i).regs.rdx) = .ok (rs, rm (i + 1))) ∧
      BufKept B (rm (i + 1))) :
    ∀ c s, s + c = t.n → ThreadRuns B (rm s) ((List.range' s c).map fun i => ((t.dm i).regs.rdx, abiFuel, rm (i + 1)))
  | 0, _, _ => trivial
  | c + 1, s, hs => by
    obtain ⟨h1, h2⟩ := h s (by omega)
    exact ⟨by simp [abiFuel], h1, h2, threadRuns_range B t rm h c (s + 1) (by omega)⟩

theorem cp_lt_of_lt_le {a b c : Word} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  have := UInt64.lt_iff_toNat_lt.mp h1; have := UInt64.le_iff_toNat_le.mp h2
  exact UInt64.lt_iff_toNat_lt.mpr (by omega)

set_option linter.constructorNameAsVariable false in
/-- **Each thread's calls, at the L level** (`thread_chain`): for a buffer with entry 1's header
facts, a thread of `ThreadsAcc` ran a chain of L calls from the zero region (`ThreadRuns`), one
per machine call, on the claimed indices (below `k`, increasing), and every call returned with the
caller's registers. -/
theorem threadsAcc_runs [Host] (k0 : Nat) (hcode : Code checkerFile k0) (dm₀ : MachineData)
    (st₀ : MachineState) (B : Array Word) (ths : List ThreadM) (hA : ThreadsAcc dm₀ st₀ B ths)
    (hhdr : ∀ i < frozenIdsL.length, 9 + 2 * i < B.size)
    (hent' : ∀ i < frozenIdsL.length, (bufEntry B i).1 + (bufEntry B i).2 ≤ B.size)
    (hdisj : ∀ i < frozenIdsL.length, ∀ i' < frozenIdsL.length, i ≠ i' →
      (bufEntry B i).1 + (bufEntry B i).2 ≤ (bufEntry B i').1 ∨
      (bufEntry B i').1 + (bufEntry B i').2 ≤ (bufEntry B i).1 ∨ (bufEntry B i).2 = 0 ∨ (bufEntry B i').2 = 0)
    (hk2 : st₀.data.regs.rax - 9223372036854775808 ≤ B.getD 2 0) :
    ∀ t, ∃ cs : List (Word × Nat × Mem), t ∈ ths → ThreadRuns B (zeroMem checkerTab) cs ∧
      (∀ c ∈ cs, c.1 < st₀.data.regs.rax - 9223372036854775808) ∧
      (∀ i < t.n, ∃ c ∈ cs, c.1 = (t.dm i).regs.rdx) ∧
      (∀ i < t.n, RegsRestored (t.dm i).regs (t.st i).data.regs) ∧
      (cs.map (·.1)).Pairwise (· < ·) := by
  have hc := code_of_checkerFile_par hcode
  have hnres : 1 ≤ checkerTab.nres := by decide
  intro t
  by_cases ht : t ∈ ths
  · by_cases hn0 : t.n = 0
    · exact ⟨[], fun _ => ⟨trivial, fun c h => absurd h (by simp), fun i hi => absurd hi (by omega),
        fun i hi => absurd hi (by omega), List.Pairwise.nil⟩⟩
    obtain ⟨hH0, -, hcx0, h80⟩ := hA.calls t ht 0 (by omega)
    have hneed : workerNeed parOwnedL ≤ t.blen := h80 ▸ hH0.need
    have hfit : t.base + t.blen < 2 ^ 64 := hcx0 ▸ h80 ▸ hH0.fits
    obtain ⟨rm, h0, hrun⟩ := thread_chain checkerProg checkerTab checkerTab_abiOk hnres frozenIdsL parOwnedL
      parOwnedL_not_frozen PLO PHI MODE B (outAddr dm₀.regs.r8.toNat) t.base t.blen t.n hneed hfit t.dm t.ra t.st
      (hA.zero t ht)
      (fun i hi r hr => by
        obtain ⟨hH, hdi, hcx, h8⟩ := hA.calls t ht i hi
        have hbc : BufCall checkerTab frozenIdsL parOwnedL B (t.dm i) (t.ra i) :=
          ⟨⟨hH.need, hH.fits, hH.bend, hhdr, hent', hdisj, hH.apart⟩, hH.hB, hH.hmap, hH.hra, hH.hcs,
            hH.hcs24, hH.hcs8⟩
        have hEv := abiB_outcome checkerProgI checkerProg checkerProgI_refines checkerTab checkerTab_abiOk checkerX_ok checkerProgI_wf MODE PLO PHI OUT HDRF
          CTLF hdrHw frozenIdsL parOwnedL (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) k0 hc L.Checker.checkL checkerProg_lookup_check (by decide) B r (t.dm i) (t.ra i) hbc
          (by rw [hcx]; exact hr) checker_bufMinOk (by have := hhdr 0 (by decide); omega)
          (.inl (cp_lt_of_lt_le (hA.claimed t ht i hi) hk2))
        rw [hdi, hcx] at hEv
        exact hA.ret t ht i hi _ hEv (fun s h => h.1))
      (hA.acc t ht) (hA.next t ht)
    refine ⟨thrCalls t rm, fun _ => ⟨?_, ?_, ?_, fun i hi => by obtain ⟨_, -, -, -, h⟩ := hrun i hi; exact h, ?_⟩⟩
    · rw [← h0, thrCalls, List.range_eq_range']
      refine threadRuns_range B t rm (fun i hi => ?_) t.n 0 (by omega)
      obtain ⟨rs, h1, -, h3, -⟩ := hrun i hi
      exact ⟨⟨rs, h1⟩, bufKept_of_memRel h3 hent' (hA.kept t ht i hi)⟩
    · intro c hc'
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc'
      rw [List.mem_range] at hi
      exact hA.claimed t ht i hi
    · intro i hi
      exact ⟨_, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, rfl⟩
    · simp only [thrCalls, List.map_map]
      rw [List.pairwise_map]
      refine (List.pairwise_lt_range (n := t.n)).imp_of_mem fun hi hj hij => ?_
      exact hA.incr t ht _ _ hij (List.mem_range.mp hj)
  · exact ⟨[], fun h => absurd h ht⟩

/-! ## The theorem -/

-- the linter's traversal of this proof exceeds the recursion limit
set_option linter.constructorNameAsVariable false in
/-- **The threads' accept is the twin's pooled accept**, for the committed file `checker.s`:
the trusted threaded harness runs as `ThreadsRun` says. And every call, entry 1 and each
`ca_check_b`, returns with the caller's registers (`RegsRestored`). -/
theorem threadsRun_twinAcceptsPooled_regs [Host] (k0 : Nat) (hcode : Code checkerFile k0)
    (b pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (dm₀ : MachineData) (ra₀ : Word) (st₀ : MachineState) (B : Array Word) (ths : List ThreadM)
    (hR : ThreadsRun b none pb dm₀ ra₀ st₀ B ths) : TwinAcceptsPooled [b] ∧
      RegsRestored dm₀.regs st₀.data.regs ∧
      ∀ t ∈ ths, ∀ i < t.n, RegsRestored (t.dm i).regs (t.st i).data.regs := by
  have hc := code_of_checkerFile_par hcode
  have hnres : 1 ≤ checkerTab.nres := by decide
  -- entry 1
  have hE := abiA_outcome checkerProgI checkerProg checkerProgI_refines checkerTab checkerTab_abiOk checkerX_ok checkerTab_abiIO checkerProgI_wf MODE PLO PHI OUT HDRF CTLF hdrHw
    frozenIdsL parOwnedL (by decide) k0 hc L.Checker.checkL checkerProg_lookup_check (by decide) b pb dm₀ ra₀ hR.call₀.toAbiArgs
  obtain ⟨⟨-, hRR₀, -, hout₀⟩, hsz⟩ := hR.ret₀ _ hE (fun s h => h.1.1)
  have hne : st₀.data.regs.rdx ≠ 1 := by rw [hR.rdx₀]; decide
  obtain ⟨hb, hpb⟩ := hsz.resolve_left hne
  have hin : InputsOK b pb (abiSz checkerTab) := ⟨h64, hb, hpb, fun s => by
    have := abiSz_le checkerTab_abiOk s; simp only [abiWords] at this; omega⟩
  rcases hout₀ with h1 | hout₀'
  · exact absurd h1 hne
  rcases hres₁ : L.run checkerProg abiFuel "check" []
      ((loadMem b pb (abiSz checkerTab)).setG MODE 1) with e | ⟨rs₁, m₁⟩
  · rw [hres₁] at hout₀'
    cases e <;> simp only [OutcomeRel] at hout₀' <;> (rw [hR.rdx₀] at hout₀'; exact absurd hout₀'.1 (by decide))
  rw [hres₁] at hout₀'
  obtain ⟨-, hRes₁, hMem₁⟩ := hout₀'
  have hrax₁ : st₀.data.regs.rax = rs₁.headD 0 := by
    rw [← L.getD_zero]; exact hRes₁.1 0 (by simp only [abiLayout_tab]; omega) (by decide)
  have h₁ : L.run checkerProg abiFuel "check" [] (loadMemM b pb (abiSz checkerTab) 1) =
      .ok (rs₁, m₁) := hres₁
  have hN : abiFuel < 2 ^ 62 := by simp [abiFuel]
  have hge : 9223372036854775808 ≤ (rs₁.headD 0).toNat := by rw [← hrax₁]; exact hR.rax₀
  -- the buffer is `OUT`'s prefix
  obtain ⟨hlen, h126, hent', hinc'⟩ := entry1_buf b pb _ hin abiFuel hN rs₁ m₁ h₁ hge _ rfl
  have hOUT : checkerTab.dom64 ↑OUT = true := by decide +kernel
  have hOUTp : 2 ≤ checkerTab.pos64 ↑OUT := by
    have := checkerTab.pos64_lt hOUT; have := (abiTabOk_spec checkerTab_abiOk).1; omega
  have hsz := hMem₁.size64 _ hOUT
  have hget : ∀ i (h : i < (m₁.arr64 OUT).size),
      rdW st₀.data.dmem (A (outAddr dm₀.regs.r8.toNat + 8 * i)) = some (m₁.arr64 OUT)[i] := fun i h => by
    have := hMem₁.get64 _ hOUT i h
    simp only [abiLayout_tab] at this
    rw [abiLayout_b64 _ _ _ _ _ _ hOUTp, abiOff_slot (by rw [checkerTab.wAt_pos64 hOUT]; decide)] at this
    simpa only [outAddr, abiSlot64] using this
  have hH := hdrW_eq
  have hBsz : B.size = ((m₁.arr64 OUT).getD 1 0).toNat := by
    obtain ⟨w, hw, hwB⟩ := hR.buflen
    have h1 := hget 1 (by omega)
    rw [Nat.mul_one, hw] at h1
    rw [← hwB, Option.some.inj h1]
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (show 1 < (m₁.arr64 OUT).size by omega)]
  have hBeq : B = (m₁.arr64 OUT).extract 0 ((m₁.arr64 OUT).getD 1 0).toNat := by
    apply Array.ext
    · simp only [Array.size_extract]; omega
    · intro i h₁ h₂
      have e := hR.bufw i h₁
      rw [hget i (by omega)] at e
      simp only [Array.getElem_extract, Nat.zero_add]
      exact (Option.some.inj e).symm
  rw [← hBeq] at hent' hinc'
  -- the buffer's header facts (`BufGeom`'s)
  have hhdr : ∀ i < frozenIdsL.length, 9 + 2 * i < B.size := by
    intro i hi
    have : frozenIdsL.length = frozen.length + 1 := by rw [frozenIdsL_eq]; simp
    have  := frozen_length
    have := h126; have  := hdrW_eq
    omega
  have hdisj : ∀ i < frozenIdsL.length, ∀ i' < frozenIdsL.length, i ≠ i' →
      (bufEntry B i).1 + (bufEntry B i).2 ≤ (bufEntry B i').1 ∨
      (bufEntry B i').1 + (bufEntry B i').2 ≤ (bufEntry B i).1 ∨ (bufEntry B i).2 = 0 ∨ (bufEntry B i').2 = 0 := by
    intro i hi i' hi' hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact Or.inl (hinc' i hi i' hi' h)
    · exact Or.inr (Or.inl (hinc' i' hi' i hi h))
  -- each thread: its chain of L runs
  have hk2 : st₀.data.regs.rax - 9223372036854775808 ≤ B.getD 2 0 := by
    rw [hrax₁]
    exact entry1_k b pb _ hin abiFuel hN rs₁ m₁ h₁ hge B hBeq (by have := hhdr 0 (by decide); omega)
  have hthr := threadsAcc_runs k0 hcode dm₀ st₀ B ths hR.toThreadsAcc hhdr hent' hdisj hk2
  obtain ⟨f, hf⟩ := Classical.axiomOfChoice hthr
  refine ⟨?_, hRR₀, fun t ht i hi => (hf t ht).2.2.2.1 i hi⟩
  refine threads_twinAcceptsPooled checkerCd_proved b pb _ hin abiFuel hN rs₁ m₁ h₁ hge B hBeq
    (ths.map fun t => (zeroMem checkerTab, f t)) (fun t' ht' => ?_) (fun j hj => ?_) ?_
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    obtain ⟨h1, h2, -, -, -⟩ := hf t ht
    refine ⟨fun a ha => ?_, rfl, h1, fun c hc => by rw [← hrax₁]; exact h2 c hc⟩
    have hl := parOwnedL_dom a ha
    rw [hMem₁.size64 a hl]
    simp only [abiLayout_tab]
    rw [abiLayout_s64 _ _ _ _ _ _ (by
      have := checkerTab.pos64_lt hl; have := (abiTabOk_spec checkerTab_abiOk).1; omega), checkerTab.wAt_pos64 hl]
    simp [zeroMem, Mem.arr64, zeros]
  · rw [← hrax₁] at hj
    obtain ⟨t, ht, i, hi, hj'⟩ := hR.cover j hj
    obtain ⟨-, -, h3, -, -⟩ := hf t ht
    obtain ⟨c, hc', hcj⟩ := h3 i hi
    exact ⟨_, List.mem_map.mpr ⟨t, ht, rfl⟩, c, hc', by rw [hcj, hj']⟩
  · intro t' ht'
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    exact (hf t ht).2.2.2.2

/-- **The threads' accept is the twin's pooled accept** (`threadsRun_twinAcceptsPooled_regs`
without the registers). -/
theorem threadsRun_twinAcceptsPooled [Host] (k0 : Nat) (hcode : Code checkerFile k0)
    (b pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (dm₀ : MachineData) (ra₀ : Word) (st₀ : MachineState) (B : Array Word) (ths : List ThreadM)
    (hR : ThreadsRun b none pb dm₀ ra₀ st₀ B ths) : TwinAcceptsPooled [b] :=
  (threadsRun_twinAcceptsPooled_regs k0 hcode b pb h64 dm₀ ra₀ st₀ B ths hR).1

end ConAgua.Final
