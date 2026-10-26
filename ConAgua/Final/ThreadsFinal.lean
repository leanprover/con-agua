import ConAgua.Final.BufChain
import ConAgua.Final.DrvFinal
import ConAgua.Checker.ParThreadTwin

/-!
# The threads end to end, for the committed file

`threadsRun_twinAcceptsPooled` (restated as `checkerFile_threads_accept` in
`Final/EndToEnd.lean`, with the model and no-`False` corollaries): the trusted threaded harness (`main.c`, `run_jobs`) runs
entry 1 (`ca_start_a`) of `checker.s`, hands the buffer it left to its threads, and each thread
calls `ca_check_b` once per group index it claims, on its own region (`ThreadsRun`). If every call
reports accept and the threads claim every group index, the twin's pooled pipeline accepts `[b]`
(`TwinAcceptsPooled [b]`).

**What the theorem trusts of the harness** (the hypotheses of `ThreadsRun`; beyond them, what
`Final/Statement.lean` lists: Kraken's semantics, the assembler, linker and loader):

* **Entry 1's call**: `ca_start_a` is called as `AbiCall` says (the input and pin buffers, a zero
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
* **The claim counter's coverage**: every claimed group index `j` (in `rdx`) is below `k`
  (`k = rax - 2^63` from entry 1), and every index below `k` is claimed by some thread.
* The verdicts: entry 1 returns `rdx = 0`, `rax ≥ 2^63`; every call returns `rdx = 0`,
  `rax = ACCEPT`.
-/

namespace ConAgua.Final

open L L.Compiler L.Checker L.Arena ConRon.Arena

/-! ## Entry 1's buffer, at the L level -/

/-- **Entry 1's buffer** (the first `len` words of `OUT`, `len` its word `1`, after a run of
`check` in mode `1` that returned `2^63 + k`): inside `OUT`, at least the header long, its header
entries inside it and in increasing order. -/
theorem entry1_buf (b pb : ByteArray) (s8 s64 : List Nat) (hin : InputsOK b pb s64)
    (N : Nat) (hN : N < 2 ^ 62) (rs₁ : List Word) (m₁ : Mem)
    (h₁ : L.run checkerProg N "check" [] (loadMemM b pb s8 s64 1) = .ok (rs₁, m₁))
    (hge : 9223372036854775808 ≤ (rs₁.headD 0).toNat)
    (B : Array Word) (hB : B = (m₁.arr64 OUT).extract 0 ((m₁.arr64 OUT).getD 1 0).toNat) :
    ((m₁.arr64 OUT).getD 1 0).toNat ≤ (m₁.arr64 OUT).size ∧ 132 ≤ ((m₁.arr64 OUT).getD 1 0).toNat ∧
      (∀ i < frozenIdsL.length, (bufEntry B i).1 + (bufEntry B i).2 ≤ B.size) ∧
      (∀ i < frozenIdsL.length, ∀ i' < frozenIdsL.length, i < i' →
        (bufEntry B i).1 + (bufEntry B i).2 ≤ (bufEntry B i').1) := by
  have hr : rs₁.headD 0 ≠ 1 := fun e => by rw [e] at hge; simp at hge
  obtain ⟨PA, m, v, hS, -, -, hok, hm₁, -⟩ := checkA_run b pb s8 s64 hin 1 (Or.inl rfl) N hN rs₁ m₁ h₁ hr
  have hflag : modeFlag 1 = 1 := rfl
  rw [hflag] at hok hm₁
  have hF := parCompactMem_out m v 1
  rw [← hm₁] at hF
  have hlt : (m.arr64 OUT).size < 2 ^ 64 := by
    rw [← hF.size OUT]; exact run_load_size hin.2.2.2 h₁ OUT
  have hlen : ((m₁.arr64 OUT).getD 1 0).toNat = (fzOff m frozen.length).toNat := by
    rw [hm₁, (parCompactMem_hdr hok).2.1]
  have hBm : B = bufOf m v := by rw [hB, bufOf, hm₁, (parCompactMem_hdr hok).2.1]
  have hs := bufOf_size (v := v) hok hlt
  have hoffs := buf_offs hok hlt
  have hH : hdrW = 132 := by decide
  have hF61 : frozen.length = 61 := frozen_length
  have hL : frozenIdsL.length = 62 := rfl
  refine ⟨by rw [hlen, hF.size, hs.2]; exact hoffs.2, by rw [hlen, hs.2]; omega,
    fun i hi => hBm ▸ buf_entries_inside hok hlt hi, fun i hi i' hi' hii => ?_⟩
  rw [hBm]
  obtain ⟨c, rfl⟩ : ∃ c, i' = c + 1 := ⟨i' - 1, by omega⟩
  obtain ⟨he', ho'⟩ := bufEntry_succ (v := v) hok hlt (i := c) (by omega)
  rw [he', ho']
  rcases i with _ | a
  · rw [bufEntry_zero hok hlt]; simp only; omega
  · obtain ⟨he, ho⟩ := bufEntry_succ (v := v) hok hlt (i := a) (by omega)
    rw [he, ho]
    have := fzSum_mono m (j := a + 1) (n := c) (by omega)
    rw [fzSum_succ, ← fzExt_eq] at this
    simp only; omega

/-! ## The harness's facts -/

/-- **First return** (trusted): the harness regains control from the call made at `dm` (code
`pc`) in the state `st`, which has every property the machine is guaranteed to reach at the
return address `ra`. -/
def FirstReturn [Host] (dm : MachineData) (pc : Int64) (ra : Word) (st : MachineState) : Prop :=
  ∀ P : MachineState → Prop, Ev P dm pc → (∀ s, P s → s.pc = Int64.ofBitVec ra.toBitVec) → P st

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

/-- **What the threaded harness does** (trusted; the module doc lists it): entry 1 at `dm₀`
returning at `st₀`, the buffer `B`, and the threads `ths`. -/
structure ThreadsRun [Host] (b pb : ByteArray) (dm₀ : MachineData) (ra₀ : Word) (st₀ : MachineState)
    (B : Array Word) (ths : List ThreadM) : Prop where
  call₀ : AbiCall b pb dm₀ ra₀
  ret₀ : FirstReturn dm₀ (label abiStartAL) ra₀ st₀
  rdx₀ : st₀.data.regs.rdx = 0
  rax₀ : 9223372036854775808 ≤ st₀.data.regs.rax.toNat
  /-- the buffer: `OUT`'s first `len` words, `len` its word `1` -/
  bufw : ∀ i (h : i < B.size), rdW st₀.data.dmem (A (outAddr dm₀.regs.r8.toNat + 8 * i)) = some B[i]
  buflen : ∃ w, rdW st₀.data.dmem (A (outAddr dm₀.regs.r8.toNat + 8)) = some w ∧ w.toNat = B.size
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
  cover : ∀ j : Word, j < st₀.data.regs.rax - 9223372036854775808 → ∃ t ∈ ths, ∃ i < t.n, (t.dm i).regs.rdx = j

/-! ## Pieces -/

/-- The final memory's frozen arrays are the buffer's images, when the buffer is unchanged. -/
theorem bufKept_of_memRel {B : Array Word} {buf base : Nat} {r : Mem} {d : DataMem}
    (hm : MemRel (bufLayout checkerTab buf B base frozenIdsL parOwnedL) r d)
    (hent : ∀ i < frozenIdsL.length, (bufEntry B i).1 + (bufEntry B i).2 ≤ B.size)
    (hkept : ∀ q (h : q < B.size), rdW d (A (buf + 8 * q)) = some B[q]) : BufKept B r := by
  intro k hk h1
  obtain ⟨hidx, -, -, hlt⟩ := frozen_facts hk h1
  have hnw : frozen[k].1 < checkerTab.nw := by
    have : checkerTab.nw = 388 := by decide
    rw [this]; exact hlt
  have h59 : k + 1 < frozenIdsL.length := by rw [frozenIdsL_eq]; simp; omega
  have he := hent (k + 1) h59
  have hs := hm.size64 _ hnw
  simp only [bufLayout_s64, bufL, hidx] at hs
  apply Array.ext
  · rw [hs]; simp only [bufImg, Array.size_extract]; omega
  · intro i h₁ h₂
    have hg := hm.get64 _ hnw i h₁
    simp only [bufLayout_b64, bufB, hidx] at hg
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

theorem parOwnedL_lt : ∀ a ∈ parOwnedL, a < checkerTab.nw := by
  have h1 : parOwnedL.all (· < 388) = true := by decide
  have h2 : checkerTab.nw = 388 := by decide
  intro a ha; rw [h2]; simpa using List.all_eq_true.mp h1 a ha

/-! ## The theorem -/

-- the linter's traversal of this proof exceeds the recursion limit
set_option linter.constructorNameAsVariable false in
/-- **The threads' accept is the twin's pooled accept**, for the committed file `checker.s`:
the trusted threaded harness runs as `ThreadsRun` says. And every call, entry 1 and each
`ca_check_b`, returns with the caller's registers (`RegsRestored`). -/
theorem threadsRun_twinAcceptsPooled_regs [Host] (k0 : Nat) (hcode : Code checkerFile k0)
    (b pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (dm₀ : MachineData) (ra₀ : Word) (st₀ : MachineState) (B : Array Word) (ths : List ThreadM)
    (hR : ThreadsRun b pb dm₀ ra₀ st₀ B ths) : TwinAcceptsPooled [b] ∧
      RegsRestored dm₀.regs st₀.data.regs ∧
      ∀ t ∈ ths, ∀ i < t.n, RegsRestored (t.dm i).regs (t.st i).data.regs := by
  have hc := code_of_checkerFile_par hcode
  have hnres : 1 ≤ checkerTab.nres := by decide
  -- entry 1
  have hE := abiA_outcome checkerProg checkerTab checkerTab_abiOk checkerProg_wf MODE PLO PHI OUT HDRF CTLF 132
    frozenIdsL parOwnedL (by decide) k0 hc L.Checker.checkL checkerProg_lookup_check (by decide) b pb dm₀ ra₀ hR.call₀
  obtain ⟨⟨-, hRR₀, -, hout₀⟩, hsz⟩ := hR.ret₀ _ hE (fun s h => h.1.1)
  have hne : st₀.data.regs.rdx ≠ 1 := by rw [hR.rdx₀]; decide
  obtain ⟨hb, hpb⟩ := hsz.resolve_left hne
  have hin : InputsOK b pb (List.replicate checkerTab.nw abiWords) :=
    ⟨h64, hb, hpb, fun n hn => by simp [List.mem_replicate] at hn; rw [hn.2]; simp [abiWords]⟩
  rcases hout₀ with h1 | hout₀'
  · exact absurd h1 hne
  rcases hres₁ : L.run checkerProg abiFuel "check" []
      ((loadMem b pb [] (List.replicate checkerTab.nw abiWords)).setG MODE 1) with e | ⟨rs₁, m₁⟩
  · rw [hres₁] at hout₀'
    cases e <;> simp only [OutcomeRel] at hout₀' <;> (rw [hR.rdx₀] at hout₀'; exact absurd hout₀'.1 (by decide))
  rw [hres₁] at hout₀'
  obtain ⟨-, hRes₁, hMem₁⟩ := hout₀'
  have hrax₁ : st₀.data.regs.rax = rs₁.headD 0 := by
    rw [← getD_zero_headD]; exact hRes₁.1 0 (by simp only [abiLayout_tab]; omega) (by decide)
  have h₁ : L.run checkerProg abiFuel "check" [] (loadMemM b pb [] (List.replicate checkerTab.nw abiWords) 1) =
      .ok (rs₁, m₁) := hres₁
  have hN : abiFuel < 2 ^ 62 := by simp [abiFuel]
  have hge : 9223372036854775808 ≤ (rs₁.headD 0).toNat := by rw [← hrax₁]; exact hR.rax₀
  -- the buffer is `OUT`'s prefix
  obtain ⟨hlen, h126, hent', hinc'⟩ := entry1_buf b pb [] _ hin abiFuel hN rs₁ m₁ h₁ hge _ rfl
  have hOUT : OUT < checkerTab.nw := by decide
  have hsz := hMem₁.size64 OUT hOUT
  have hget : ∀ i (h : i < (m₁.arr64 OUT).size),
      rdW st₀.data.dmem (A (outAddr dm₀.regs.r8.toNat + 8 * i)) = some (m₁.arr64 OUT)[i] := fun i h =>
    hMem₁.get64 OUT hOUT i h
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
    intro i hi; have : frozenIdsL.length = 62 := rfl; omega
  have hdisj : ∀ i < frozenIdsL.length, ∀ i' < frozenIdsL.length, i ≠ i' →
      (bufEntry B i).1 + (bufEntry B i).2 ≤ (bufEntry B i').1 ∨
      (bufEntry B i').1 + (bufEntry B i').2 ≤ (bufEntry B i).1 ∨ (bufEntry B i).2 = 0 ∨ (bufEntry B i').2 = 0 := by
    intro i hi i' hi' hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact Or.inl (hinc' i hi i' hi' h)
    · exact Or.inr (Or.inl (hinc' i' hi' i hi h))
  -- each thread: its chain of L runs
  have hthr : ∀ t, ∃ cs : List (Word × Nat × Mem), t ∈ ths → ThreadRuns B (zeroMem checkerTab) cs ∧
      (∀ c ∈ cs, c.1 < rs₁.headD 0 - 9223372036854775808) ∧
      (∀ i < t.n, ∃ c ∈ cs, c.1 = (t.dm i).regs.rdx) ∧
      (∀ i < t.n, RegsRestored (t.dm i).regs (t.st i).data.regs) := by
    intro t
    by_cases ht : t ∈ ths
    · by_cases hn0 : t.n = 0
      · exact ⟨[], fun _ => ⟨trivial, fun c h => absurd h (by simp), fun i hi => absurd hi (by omega),
          fun i hi => absurd hi (by omega)⟩⟩
      obtain ⟨hH0, -, hcx0, h80⟩ := hR.calls t ht 0 (by omega)
      have hneed : workerNeed parOwnedL ≤ t.blen := h80 ▸ hH0.need
      have hfit : t.base + t.blen < 2 ^ 64 := hcx0 ▸ h80 ▸ hH0.fits
      obtain ⟨rm, h0, hrun⟩ := thread_chain checkerProg checkerTab checkerTab_abiOk hnres frozenIdsL parOwnedL
        (by decide) PLO PHI MODE B (outAddr dm₀.regs.r8.toNat) t.base t.blen t.n hneed hfit t.dm t.ra t.st
        (hR.zero t ht)
        (fun i hi r hr => by
          obtain ⟨hH, hdi, hcx, h8⟩ := hR.calls t ht i hi
          have hbc : BufCall checkerTab frozenIdsL parOwnedL B (t.dm i) (t.ra i) :=
            ⟨⟨hH.need, hH.fits, hH.bend, hhdr, hent', hdisj, hH.apart⟩, hH.hB, hH.hmap, hH.hra, hH.hcs,
              hH.hcs24, hH.hcs8⟩
          have hEv := abiB_outcome checkerProg checkerTab checkerTab_abiOk checkerProg_wf MODE PLO PHI OUT HDRF
            CTLF 132 frozenIdsL parOwnedL (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) k0 hc L.Checker.checkL checkerProg_lookup_check (by decide) B r (t.dm i) (t.ra i) hbc
            (by rw [hcx]; exact hr)
          rw [hdi, hcx] at hEv
          exact hR.ret t ht i hi _ hEv (fun s h => h.1))
        (hR.acc t ht) (hR.next t ht)
      refine ⟨thrCalls t rm, fun _ => ⟨?_, ?_, ?_, fun i hi => by obtain ⟨_, -, -, -, h⟩ := hrun i hi; exact h⟩⟩
      · rw [← h0, thrCalls, List.range_eq_range']
        refine threadRuns_range B t rm (fun i hi => ?_) t.n 0 (by omega)
        obtain ⟨rs, h1, -, h3, -⟩ := hrun i hi
        exact ⟨⟨rs, h1⟩, bufKept_of_memRel h3 hent' (hR.kept t ht i hi)⟩
      · intro c hc'
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc'
        rw [List.mem_range] at hi
        rw [← hrax₁]; exact hR.claimed t ht i hi
      · intro i hi
        exact ⟨_, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, rfl⟩
    · exact ⟨[], fun h => absurd h ht⟩
  obtain ⟨f, hf⟩ := Classical.axiomOfChoice hthr
  refine ⟨?_, hRR₀, fun t ht i hi => (hf t ht).2.2.2 i hi⟩
  refine threads_twinAcceptsPooled b pb [] _ hin abiFuel hN rs₁ m₁ h₁ hge B hBeq
    (ths.map fun t => (zeroMem checkerTab, f t)) (fun t' ht' => ?_) (fun j hj => ?_)
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    obtain ⟨h1, h2, -, -⟩ := hf t ht
    refine ⟨by simp [zeroMem]; decide, fun a ha => ?_, rfl, h1, h2⟩
    have hl := parOwnedL_lt a ha
    rw [hMem₁.size64 a hl]
    simp [zeroMem, Mem.arr64, hl, zeros]
  · rw [← hrax₁] at hj
    obtain ⟨t, ht, i, hi, hj'⟩ := hR.cover j hj
    obtain ⟨-, -, h3, -⟩ := hf t ht
    obtain ⟨c, hc', hcj⟩ := h3 i hi
    exact ⟨_, List.mem_map.mpr ⟨t, ht, rfl⟩, c, hc', by rw [hcj, hj']⟩

/-- **The threads' accept is the twin's pooled accept** (`threadsRun_twinAcceptsPooled_regs`
without the registers). -/
theorem threadsRun_twinAcceptsPooled [Host] (k0 : Nat) (hcode : Code checkerFile k0)
    (b pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (dm₀ : MachineData) (ra₀ : Word) (st₀ : MachineState) (B : Array Word) (ths : List ThreadM)
    (hR : ThreadsRun b pb dm₀ ra₀ st₀ B ths) : TwinAcceptsPooled [b] :=
  (threadsRun_twinAcceptsPooled_regs k0 hcode b pb h64 dm₀ ra₀ st₀ B ths hR).1

end ConAgua.Final
