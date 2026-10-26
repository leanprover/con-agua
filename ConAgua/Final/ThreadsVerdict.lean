import ConAgua.Final.ThreadsFinal
import ConAgua.Final.VerdictFinal
import ConAgua.Verdict.ThreadsE

/-!
# The verdict theorem for the threaded harness of the committed file

`checkerFile_threads_verdict`: the trusted threaded harness (`main.c`, `run_jobs`) runs entry 1
(`ca_start_a`) of `checker.s` and hands the buffer it left to its threads, each calling
`ca_check_b` once per group index it claims, on its own region (as `ThreadsRun`,
`Final/ThreadsFinal.lean`). If the run reports a failure with the code `k` (`ThreadsFail`): entry 1
returns `rdx = 2` with `rax = k`, or entry 1 returns ok and some thread's call `i` returns
`rdx = 2` with `rax = k` while its calls before `i` returned accept, then a class `k &&& 3` of `1`
(reject) or `2` (decline) is the twin pool's failure with that class (`TwinVerdictPooled [b]`):
the pipeline fails before phase B, or the stages and phase A ran ok and the failing thread's
groups up to and including the failing one, checked in order from the phase-A state's worker,
fail. Every other outcome claims nothing.

From the machine-level entries (`abiA_outcome`, `abiB_outcome`, the thread's chain
`thread_chain`) and the L-level claims (`ThreadVerdicts`: entry 1's `Entry1Verdict`, and
`check_pending`'s error claim `CPVerdict`, which `threads_twinVerdictPooled`,
`Verdict/ThreadsE.lean`, turns into the pool's failure).

**What the theorem trusts of the harness** (the hypotheses of `Entry1Fail` and `ThreadFail`;
beyond them, what `Final/Statement.lean` lists: Kraken's semantics, the assembler, linker and
loader):

* **Entry 1's call**: `ca_start_a` is called as `AbiCall` says; **first return** (`FirstReturn`):
  the harness regains control at the return address in a state with every property the machine
  is guaranteed to reach there (`abiA_outcome`'s and `abiB_outcome`'s posts).
* On a thread's failure (`ThreadFail`), for the thread's calls up to the failing call `i`, what
  `ThreadsRun` trusts: the buffer (`OUT`'s first `len` words at entry 1's return) stays in place
  and is passed to each call (route A: read-only, `mprotect`); the thread's region is its own,
  zero at the first call, and at each later call holding the bytes the previous call left; each
  call is made as `BufCallH` says; every claimed group index (in `rdx`) is below `k`
  (`k = rax - 2^63` from entry 1). Coverage of the group indices by the threads is not needed.
* The verdicts: entry 1 returns `rdx = 2` (`Entry1Fail`), or `rdx = 0` and `rax ≥ 2^63`, the
  thread's calls before `i` return `rdx = 0`, `rax = ACCEPT`, and call `i` returns `rdx = 2`
  (`ThreadFail`). The harness reports the code `k` it read from that call's `rax`.
-/

namespace ConAgua.Final

open L L.Compiler L.Checker L.Arena ConRon.Arena

/-! ## The harness's facts on a failing run -/

/-- **Entry 1 fails** (trusted; the module doc lists it): `ca_start_a` called at `dm₀` returns at
`st₀` with `rdx = 2`. -/
structure Entry1Fail [Host] (b pb : ByteArray) (dm₀ : MachineData) (ra₀ : Word) (st₀ : MachineState) :
    Prop where
  call₀ : AbiCall b pb dm₀ ra₀
  ret₀ : FirstReturn dm₀ (label abiStartAL) ra₀ st₀
  rdx₀ : st₀.data.regs.rdx = 2

/-- **A thread's call `i` fails** (trusted; the module doc lists it): entry 1 at `dm₀` returning
at `st₀`, the buffer `B`, and the thread `t`'s calls `0, …, i` (`ThreadsRun`'s fields for them),
the calls before `i` accepting, call `i` returning `rdx = 2`. -/
structure ThreadFail [Host] (b pb : ByteArray) (dm₀ : MachineData) (ra₀ : Word) (st₀ : MachineState)
    (B : Array Word) (t : ThreadM) (i : Nat) : Prop where
  call₀ : AbiCall b pb dm₀ ra₀
  ret₀ : FirstReturn dm₀ (label abiStartAL) ra₀ st₀
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

/-- **The threaded harness reports a failure with the code `k`**: entry 1 failed with
`rax = k`, or a thread's call `i` failed with `rax = k`. -/
def ThreadsFail [Host] (b pb : ByteArray) (dm₀ : MachineData) (ra₀ : Word) (st₀ : MachineState)
    (k : Word) : Prop :=
  (Entry1Fail b pb dm₀ ra₀ st₀ ∧ k = st₀.data.regs.rax) ∨
  ∃ (B : Array Word) (t : ThreadM) (i : Nat), ThreadFail b pb dm₀ ra₀ st₀ B t i ∧
    k = (t.st i).data.regs.rax

/-- **The threaded harness's verdict claims** (the L-level obligations): entry 1's
(`Entry1Verdict`, as in `SeqVerdicts`) and `check_pending`'s error claim at the programs phase B
runs (`CPVerdict`, the hypothesis `entry2Verdict_of` takes). -/
structure ThreadVerdicts : Prop where
  entry1 : Entry1Verdict checkerProg
  cp : CPVerdict

/-! ## Pieces -/

theorem threadFails_range (B : Array Word) (t : ThreadM) (rm : Nat → Mem) (i : Nat) (e : Err)
    (h : ∀ i' < i, (∃ rs, L.run checkerProg abiFuel "check" [] (bufMem B (rm i') (t.dm i').regs.rdx) =
      .ok (rs, rm (i' + 1))) ∧ BufKept B (rm (i' + 1)))
    (hf : L.run checkerProg abiFuel "check" [] (bufMem B (rm i) (t.dm i).regs.rdx) = .error e) :
    ∀ c s, s + c = i → ThreadFails B (t.dm i).regs.rdx abiFuel e (rm s)
      ((List.range' s c).map fun i' => ((t.dm i').regs.rdx, abiFuel, rm (i' + 1)))
  | 0, s, hs => by
    obtain rfl : s = i := by omega
    exact ⟨by simp [abiFuel], hf⟩
  | c + 1, s, hs => by
    obtain ⟨h1, h2⟩ := h s (by omega)
    exact ⟨by simp [abiFuel], h1, h2, threadFails_range B t rm i e h hf c (s + 1) (by omega)⟩

/-- An L outcome of `rdx = 2` is a failing run with the code in `rax`. -/
theorem outcome_err {G : Layout} {r : Except Err (List Word × Mem)} {d : MachineData}
    (h : OutcomeRel G r d) (h2 : d.regs.rdx = 2) : ∃ e, r = .error e ∧ d.regs.rax = e.code := by
  rcases r with e | ⟨rs, m'⟩
  · refine ⟨e, rfl, ?_⟩
    cases e <;> simp only [OutcomeRel] at h <;> first | exact h.elim | exact h.2
  · simp only [OutcomeRel] at h; rw [h2] at h; exact absurd h.1 (by decide)

/-! ## The theorem -/

/-- Entry 1's failure is the twin's. -/
theorem entry1Fail_twin [Host] (k0 : Nat) (hcode : Code checkerFile k0)
    (b pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (dm₀ : MachineData) (ra₀ : Word) (st₀ : MachineState) (hV : Entry1Verdict checkerProg)
    (hF : Entry1Fail b pb dm₀ ra₀ st₀) (hk : st₀.data.regs.rax &&& 3 ≠ 0) :
    TwinVerdict [b] (st₀.data.regs.rax &&& 3) := by
  have hc := code_of_checkerFile_par hcode
  have hE := abiA_outcome checkerProg checkerTab checkerTab_abiOk checkerProg_wf MODE PLO PHI OUT HDRF CTLF 132
    frozenIdsL parOwnedL (by decide) k0 hc L.Checker.checkL checkerProg_lookup_check (by decide) b pb dm₀ ra₀ hF.call₀
  obtain ⟨⟨-, -, -, hout₀⟩, hsz⟩ := hF.ret₀ _ hE (fun s h => h.1.1)
  have hne : st₀.data.regs.rdx ≠ 1 := by rw [hF.rdx₀]; decide
  obtain ⟨hb, hpb⟩ := hsz.resolve_left hne
  have hin : InputsOK b pb (List.replicate checkerTab.nw abiWords) :=
    ⟨h64, hb, hpb, fun n hn => by simp [List.mem_replicate] at hn; rw [hn.2]; simp [abiWords]⟩
  obtain ⟨e, he, hrax⟩ := outcome_err (hout₀.resolve_left hne) hF.rdx₀
  have hN : abiFuel < 2 ^ 62 := by simp [abiFuel]
  rw [hrax] at hk ⊢
  exact hV b pb [] _ hin 1 (Or.inl rfl) abiFuel hN e he hk

-- the linter's traversal of this proof exceeds the recursion limit
set_option linter.constructorNameAsVariable false in
/-- A thread's failing call is the twin pool's failure. -/
theorem threadFail_twin [Host] (k0 : Nat) (hcode : Code checkerFile k0)
    (b pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (dm₀ : MachineData) (ra₀ : Word) (st₀ : MachineState) (B : Array Word) (t : ThreadM) (i : Nat)
    (hV : CPVerdict) (hR : ThreadFail b pb dm₀ ra₀ st₀ B t i)
    (hk : (t.st i).data.regs.rax &&& 3 ≠ 0) :
    TwinVerdictPooled [b] ((t.st i).data.regs.rax &&& 3) := by
  have hc := code_of_checkerFile_par hcode
  have hnres : 1 ≤ checkerTab.nres := by decide
  -- entry 1 (as `threadsRun_twinAcceptsPooled_regs`)
  have hE := abiA_outcome checkerProg checkerTab checkerTab_abiOk checkerProg_wf MODE PLO PHI OUT HDRF CTLF 132
    frozenIdsL parOwnedL (by decide) k0 hc L.Checker.checkL checkerProg_lookup_check (by decide) b pb dm₀ ra₀ hR.call₀
  obtain ⟨⟨-, -, -, hout₀⟩, hsz⟩ := hR.ret₀ _ hE (fun s h => h.1.1)
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
  have hhdr : ∀ i < frozenIdsL.length, 9 + 2 * i < B.size := by
    intro i hi; have : frozenIdsL.length = 62 := rfl; omega
  have hdisj : ∀ i < frozenIdsL.length, ∀ i' < frozenIdsL.length, i ≠ i' →
      (bufEntry B i).1 + (bufEntry B i).2 ≤ (bufEntry B i').1 ∨
      (bufEntry B i').1 + (bufEntry B i').2 ≤ (bufEntry B i).1 ∨ (bufEntry B i).2 = 0 ∨ (bufEntry B i').2 = 0 := by
    intro i hi i' hi' hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact Or.inl (hinc' i hi i' hi' h)
    · exact Or.inr (Or.inl (hinc' i' hi' i hi h))
  -- the thread: a call's outcome, at any region memory
  obtain ⟨hH0, -, hcx0, h80⟩ := hR.calls 0 (Nat.zero_le _)
  have hneed : workerNeed parOwnedL ≤ t.blen := h80 ▸ hH0.need
  have hfit : t.base + t.blen < 2 ^ 64 := hcx0 ▸ h80 ▸ hH0.fits
  have hpost : ∀ i' ≤ i, ∀ r, RegionRel checkerTab t.base parOwnedL r (t.dm i').dmem →
      EntryPost (bufLayout checkerTab (outAddr dm₀.regs.r8.toNat) B t.base frozenIdsL parOwnedL) (t.dm i')
        (t.ra i') (L.run checkerProg abiFuel "check" [] (bufMemG frozenIdsL parOwnedL PLO PHI MODE B r
          (t.dm i').regs.rdx)) (t.st i') := by
    intro i' hi r hr
    obtain ⟨hH, hdi, hcx, h8⟩ := hR.calls i' hi
    have hbc : BufCall checkerTab frozenIdsL parOwnedL B (t.dm i') (t.ra i') :=
      ⟨⟨hH.need, hH.fits, hH.bend, hhdr, hent', hdisj, hH.apart⟩, hH.hB, hH.hmap, hH.hra, hH.hcs,
        hH.hcs24, hH.hcs8⟩
    have hEv := abiB_outcome checkerProg checkerTab checkerTab_abiOk checkerProg_wf MODE PLO PHI OUT HDRF
      CTLF 132 frozenIdsL parOwnedL (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) k0 hc L.Checker.checkL checkerProg_lookup_check (by decide) B r (t.dm i') (t.ra i') hbc
      (by rw [hcx]; exact hr)
    rw [hdi, hcx] at hEv
    exact hR.ret i' hi _ hEv (fun s h => h.1)
  -- the calls before `i` (`thread_chain`)
  obtain ⟨rm, h0, hrun⟩ := thread_chain checkerProg checkerTab checkerTab_abiOk hnres frozenIdsL parOwnedL
    (by decide) PLO PHI MODE B (outAddr dm₀.regs.r8.toNat) t.base t.blen i hneed hfit t.dm t.ra t.st
    (fun _ => hR.zero) (fun i' hi r hr => hpost i' (by omega) r hr) hR.acc
    (fun i' hi => hR.next i' (by omega))
  -- the region at call `i`, and call `i`'s failure
  have hreg : RegionRel checkerTab t.base parOwnedL (rm i) (t.dm i).dmem := by
    rcases i with _ | i
    · rw [h0]; exact regionRel_zero checkerTab_abiOk hneed hfit _ hR.zero
    · obtain ⟨-, -, -, h3, -⟩ := hrun i (by omega)
      exact (RegionRel.of_memRel (by decide) h3).transfer checkerTab_abiOk hneed (hR.next i (by omega))
  obtain ⟨-, -, -, hout⟩ := hpost i (Nat.le_refl _) (rm i) hreg
  obtain ⟨e, he, hrax⟩ := outcome_err (hout.resolve_left (by rw [hR.rdx]; decide)) hR.rdx
  rw [hrax] at hk ⊢
  -- the L-level claim
  have hruns := threadFails_range B t rm i e (fun i' hi => by
    obtain ⟨rs, h1, -, h3, -⟩ := hrun i' hi
    exact ⟨⟨rs, h1⟩, bufKept_of_memRel h3 hent' (hR.kept i' hi)⟩) he i 0 (by omega)
  rw [h0] at hruns
  refine threads_twinVerdictPooled hV b pb [] _ hin abiFuel hN rs₁ m₁ h₁ hge B hBeq (zeroMem checkerTab)
    (by simp [zeroMem]; decide) (fun a ha => ?_) rfl _ _ abiFuel e hruns (fun c hc => ?_)
    (by rw [← hrax₁]; exact hR.claimed i (Nat.le_refl _)) hk
  · have hl := parOwnedL_lt a ha
    rw [hMem₁.size64 a hl]
    simp [zeroMem, Mem.arr64, hl, zeros]
  · obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hc
    rw [List.mem_range'] at hi'
    rw [← hrax₁]; exact hR.claimed i' (by omega)

/-- **The verdict theorem for the threaded harness of `checker.s`**: when the trusted threaded
harness's run reports a failure with the code `k` (`ThreadsFail`: entry 1 returned `rdx = 2`, or
a thread's call returned `rdx = 2` after its earlier calls accepted) and the class `k &&& 3` is
`1` (reject) or `2` (decline), the twin's pool on `[b]` fails with that class
(`TwinVerdictPooled`), given the L-level verdict claims (`ThreadVerdicts`). -/
theorem checkerFile_threads_verdict [Host] (k0 : Nat) (hcode : Code checkerFile k0)
    (b pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (dm₀ : MachineData) (ra₀ : Word) (st₀ : MachineState) (k : Word)
    (hV : ThreadVerdicts) (hF : ThreadsFail b pb dm₀ ra₀ st₀ k) (hk : k &&& 3 ≠ 0) :
    TwinVerdictPooled [b] (k &&& 3) := by
  rcases hF with ⟨hE, rfl⟩ | ⟨B, t, i, hT, rfl⟩
  · exact (entry1Fail_twin k0 hcode b pb h64 dm₀ ra₀ st₀ hV.entry1 hE hk).pooled
  · exact threadFail_twin k0 hcode b pb h64 dm₀ ra₀ st₀ B t i hV.cp hT hk

/-- info: 'ConAgua.Final.checkerFile_threads_verdict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerFile_threads_verdict

end ConAgua.Final
