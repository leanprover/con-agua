module

public import ConAgua.Final.ThreadsFinal
public import ConAgua.Final.CmpThreadsL
public import ConAgua.Final.CmpOutcome
public import ConAgua.Final.ParAbi
import ConAgua.Final.CmpStub
import ConAgua.Final.DrvAbi
import ConAgua.Final.DrvFinal
import ConAgua.Final.CmpChain
import ConAgua.Final.BufAbi
import ConAgua.Checker.AsmFinal
import ConAgua.Checker.AsmFileEq
import ConAgua.Checker.AsmStubEq
import ConAgua.Checker.AsmTailEq
import ConAgua.Checker.ProgIRef
import ConAgua.Checker.AsmXOk
import ConAgua.Checker.ProgWf
public import ConAgua.Checker.ProgTab
public import ConAguaAsm.Checker
import all ConAgua.Checker.Entry

@[expose] public section

/-!
# The threaded compared run, end to end, for the committed file (lane compare2)

`checkerFile_compare_threads_accept_regs`: the trusted threaded harness (`main.c`,
`run_compare_jobs`) drives the mode entries of `checker.s` itself, all on one region: `ca_start_a4`
(the challenge's bytes: the stages up to the challenge's parse), `ca_start_a5` (the solution's
bytes: its parse, preparation, pins, index and frozen buffer, `2^63 + kS`), the solution's jobs on
its threads (`ca_check_b`, as the flat threaded mode), `ca_start_a7` (the solution's bytes again:
the challenge's preparation, side records, index and frozen buffer, `2^63 + kC`), the challenge's
jobs on its threads (`CmpThreadsRun`). If every call reports accept, the twin's pooled comparison
accepts (`TwinComparesAcceptsPooled bC bS`). From the machine-level entries (`abiMode_outcome`,
`abiModeM_outcome`, the threads' chains `threadsAcc_runs`) and the L-level composition
(`cmpThreads_twinPooled`).

**What the theorem trusts of the harness** (the hypotheses of `CmpThreadsRun`; beyond them what
`ThreadsRun` trusts of each pool, `Final/ThreadsFinal.lean`, and what `Final/Statement.lean`
lists):

* **The three driver calls**: `ca_start_a4` is called as `AbiCall` says (the challenge's bytes,
  the pin data, a zero region); `ca_start_a5` and `ca_start_a7` as `AbiCallM` says (the solution's
  bytes, the same pin data, the same region, which now holds what the previous call left), each on
  the same region `[base, base + len)` (`r8`, `r9`) with the same pin buffer (`rdx`) as the first.
* **First return** (`FirstReturn`) for each of them and for each thread's calls.
* **The region carries over**: at `ca_start_a5`'s call, the region, the challenge's buffer and the
  pin data hold the bytes they held at `ca_start_a4`'s return (nothing runs in between); at
  `ca_start_a7`'s call, the region, the solution's buffer and the pin data hold the bytes they held
  at `ca_start_a5`'s return (in between, the threads write only their own regions, and the buffer
  is read-only: `mprotect`, route A).
* **Each pool** as `ThreadsRun`'s (`ThreadsAcc`, and every job index below `k` claimed): the
  buffer `OUT`'s first `len` words at the phase's driver return, `len` its word `1`.
* The verdicts: every driver call returns `rdx = 0`, `rax ≥ 2^63`; every thread's call
  `rdx = 0`, `rax = ACCEPT`.
-/

namespace ConAgua.Final

universe w

open L L.Compiler L.Checker L.Arena ConRon.Arena

/-! ## The code -/

/-- The file's code as the threaded compared run sees it: the mode entries (`cmpStubL`) and mode
`7`'s entry (`ctaStub`) right after them. -/
theorem code_of_checkerFile_cta [Host] {k0 : Nat} (hcode : Code checkerFile k0) :
    ∃ Kc, Code (cmpStubL checkerTab MODE OUT parOwnedL) Kc ∧
      Code (ctaStub checkerTab MODE) (Kc + (cmpStubL checkerTab MODE OUT parOwnedL).length) := by
  rw [checkerFile_eq, checkerStub_eq, checkerTail_eq, List.append_assoc, cmpStub_lit] at hcode
  exact ⟨_, hcode.right.right.right.left, hcode.right.right.right.right⟩

/-! ## A memory relation carried over -/

/-- **`MemRel` on a memory that agrees on the layout's cells** (the stack, the arrays, the table). -/
theorem MemRel.carry {G : L.Compiler.Layout} {m : Mem} {d d' : DataMem} (hm : MemRel G m d)
    (hag : ∀ x, G.InStack x ∨ G.InArr x ∨ G.InTab x → d'.get? (A x) = d.get? (A x)) : MemRel G m d' := by
  have hw : G.tab.rom.length ≤ 8 * G.tab.romWords := G.tab.rom_length_le
  have htab : ∀ x, G.InTab x → d'.get? (A x) = d.get? (A x) := fun x h => hag x (.inr (.inr h))
  have hcell : ∀ off, off + 8 ≤ 16 + 24 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres +
      8 * G.tab.ng → rdW d' (A (G.T + off)) = rdW d (A (G.T + off)) := fun off h =>
    rdW_congr fun j hj => by
      rw [A_add]; exact htab _ ⟨by omega, by simp only [Layout.tabEnd]; omega⟩
  exact {
    size8 := hm.size8
    size64 := hm.size64
    get8 := fun c hc i hi => by
      have hs := hm.size8 c hc
      have hp := G.tab.pos8_lt hc
      have hwd : G.tab.wd (G.tab.pos8 c) = 1 := Layout.wd_byte (G := G) hp
      rw [hag _ (.inr (.inl ⟨G.tab.pos8 c, by omega, by simp only [Layout.In, hwd]; omega⟩)), hm.get8 c hc i hi]
    get64 := fun c hc i hi => by
      have hs := hm.size64 c hc
      have hp := G.tab.pos64_lt hc
      have hwd : G.tab.wd (G.tab.pos64 c) = 8 := Layout.wd_word (G := G) hp.1
      rw [← hm.get64 c hc i hi]
      exact rdW_congr fun j hj => by
        rw [A_add]
        exact hag _ (.inr (.inl ⟨_, hp.2, by simp only [Layout.In, hwd]; omega⟩))
    limit := by rw [hcell 8 (by omega)]; exact hm.limit
    base := fun c hc => (by rw [hcell _ (by simp only [Tab.dbase]; omega)]; exact hm.base c hc)
    «len» := fun c hc => (by rw [hcell _ (by simp only [Tab.dlen]; omega)]; exact hm.len c hc)
    len32 := fun c h1 h2 => (by rw [hcell _ (by simp only [Tab.dlen32]; omega)]; exact hm.len32 c h1 h2)
    rom := fun i hi => by
      rw [htab _ ⟨by omega, by simp only [Layout.tabEnd]; omega⟩]; exact hm.rom i hi
    stack := fun x hx => by rw [hag x (.inl hx)]; exact hm.stack x hx
    res := fun x hx => by
      rw [htab x ⟨by have := hx.1; omega, by have := hx.2; simp only [Layout.tabEnd]; omega⟩]
      exact hm.res x hx
    glob := fun g hg => by
      rw [← hm.glob g hg]
      refine rdW_congr fun j hj => ?_
      rw [A_add]
      exact htab _ (Layout.InGlob.tab (Layout.inGlob_cell hg j hj)) }

/-- The stub's layout's cells are in the region, the input or the pin data. -/
theorem abiLayout_cells {tab : Tab} (hok : abiTabOk tab = true) {base blen inp n pins np x : Nat}
    (hneed : abiNeed tab ≤ blen)
    (h : (abiLayout tab base inp n pins np).InStack x ∨ (abiLayout tab base inp n pins np).InArr x ∨
      (abiLayout tab base inp n pins np).InTab x) :
    (base ≤ x ∧ x < base + blen) ∨ (inp ≤ x ∧ x < inp + n) ∨ (pins ≤ x ∧ x < pins + np) := by
  refine Classical.byContradiction fun hc => ?_
  simp only [not_or] at hc
  obtain ⟨h1, h2, h3⟩ := hc
  obtain ⟨q1, q2, q3⟩ := abiLayout_out hok (base := base) (blen := blen) (inp := inp) (n := n)
    (pins := pins) (np := np) (x := x) hneed (by omega) h2 h3
  rcases h with h | h | h
  · exact q1 h
  · exact q2 h
  · exact q3 h

/-- **A memory relation in the stub's layout, carried to a later call**: the region, the input and
the pin data hold the same bytes. -/
theorem memRel_carry {tab : Tab} (hok : abiTabOk tab = true) {base blen inp n pins np : Nat}
    (hneed : abiNeed tab ≤ blen) {m : Mem} {d d' : DataMem}
    (hm : MemRel (abiLayout tab base inp n pins np) m d)
    (hkeep : ∀ x, (base ≤ x ∧ x < base + blen) ∨ (inp ≤ x ∧ x < inp + n) ∨ (pins ≤ x ∧ x < pins + np) →
      d'.get? (A x) = d.get? (A x)) :
    MemRel (abiLayout tab base inp n pins np) m d' :=
  MemRel.carry hm fun x h => hkeep x (abiLayout_cells hok hneed h)

/-! ## A driver call's return -/

/-- **A mode entry's accepting return** (`rdx = 0`): both buffers below `2^63` bytes, the
caller's registers, and the L run returned `(rs, m)` with `rax` its first result and `m` in the
region. -/
theorem cta_ret {tab : Tab} (hn : 1 ≤ tab.nres) {base inp n pins np : Nat} {dm : MachineData} {ra : Word}
    {r : Except Err (List Word × Mem)} {st : MachineState} {b pb : ByteArray}
    (h : EntryPost (abiLayout tab base inp n pins np) dm ra r st ∧ SizesPost b pb st)
    (h0 : st.data.regs.rdx = 0) :
    b.size < 2 ^ 63 ∧ pb.size < 2 ^ 63 ∧ RegsRestored dm.regs st.data.regs ∧
      ∃ rs m, r = .ok (rs, m) ∧ st.data.regs.rax = rs.getD 0 0 ∧
        MemRel (abiLayout tab base inp n pins np) m st.data.dmem := by
  obtain ⟨⟨-, hRR, -, hout⟩, hsz⟩ := h
  have hne : st.data.regs.rdx ≠ 1 := by rw [h0]; decide
  obtain ⟨hb, hpb⟩ := hsz.resolve_left hne
  refine ⟨hb, hpb, hRR, ?_⟩
  have hout' := hout.resolve_left hne
  rcases r with e | ⟨rs, m⟩
  · exfalso
    cases e <;> simp only [OutcomeRel] at hout' <;> (rw [h0] at hout'; exact absurd hout'.1 (by decide))
  · obtain ⟨-, hRes, hMem⟩ := hout'
    exact ⟨rs, m, rfl, hRes.1 0 (by simp only [abiLayout_tab]; omega) (by decide), hMem⟩

/-! ## A phase's buffer and pool -/

/-- **The buffer is `OUT`'s prefix**: the words the harness reads at `OUT` (`len` its word `1`),
for an L memory in the stub's layout whose buffer has its geometry. -/
theorem cta_bufEq {base inp n pins np : Nat} {m : Mem} {d : DataMem} {B : Array Word}
    (hM : MemRel (abiLayout checkerTab base inp n pins np) m d) (hok : CmpBufOk frozenIdsL OUT m)
    (bufw : ∀ i (h : i < B.size), rdW d (A (outAddr base + 8 * i)) = some B[i])
    (buflen : ∃ w, rdW d (A (outAddr base + 8)) = some w ∧ w.toNat = B.size) :
    B = cmpBuf OUT m := by
  obtain ⟨hlen, hB⟩ := hok
  have hpos : 0 < frozenIdsL.length := by rw [frozenIdsL_eq]; simp
  have h9 := hB.hdr 0 hpos
  have he := hB.ent 0 hpos
  have hcs : (cmpBuf OUT m).size = ((m.arr64 OUT).getD 1 0).toNat := by
    simp only [cmpBuf, Array.size_extract]; omega
  have hOUT : checkerTab.dom64 ↑OUT = true := by decide +kernel
  have hOUTp : 2 ≤ checkerTab.pos64 ↑OUT := by
    have := checkerTab.pos64_lt hOUT; have := (abiTabOk_spec checkerTab_abiOk).1; omega
  have hget : ∀ i (h : i < (m.arr64 OUT).size),
      rdW d (A (outAddr base + 8 * i)) = some (m.arr64 OUT)[i] := fun i h => by
    have := hM.get64 _ hOUT i h
    simp only [abiLayout_tab] at this
    rw [abiLayout_b64 _ _ _ _ _ _ hOUTp, abiOff_slot (by rw [checkerTab.wAt_pos64 hOUT]; decide)] at this
    simpa only [outAddr, abiSlot64] using this
  have hBsz : B.size = ((m.arr64 OUT).getD 1 0).toNat := by
    obtain ⟨w, hw, hwB⟩ := buflen
    have h1 := hget 1 (by omega)
    rw [Nat.mul_one, hw] at h1
    rw [← hwB, Option.some.inj h1]
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (show 1 < (m.arr64 OUT).size by omega)]
  apply Array.ext
  · rw [hcs, hBsz]
  · intro i h₁ h₂
    have e := bufw i h₁
    rw [hget i (by omega)] at e
    simp only [cmpBuf, Array.getElem_extract, Nat.zero_add]
    exact (Option.some.inj e).symm

/-- **A pool's calls, at the L level**: the threads of `ThreadsAcc` on the buffer of the L memory
`m` the phase's driver call left (`rax = rs`'s first result), every job index below `k` claimed:
the threads' chains of L runs, as `cmpThreads_twinPooled` takes them, and every call returned
with the caller's registers. -/
theorem cta_pool [Host] (k0 : Nat) (hcode : Code checkerFile k0) (dm : MachineData) (st : MachineState)
    (B : Array Word) (ths : List ThreadM) (hA : ThreadsAcc dm st B ths)
    (hcov : ∀ j : Word, j < st.data.regs.rax - 9223372036854775808 →
      ∃ t ∈ ths, ∃ i < t.n, (t.dm i).regs.rdx = j)
    {inp n pins np : Nat} {m : Mem} (hM : MemRel (abiLayout checkerTab dm.regs.r8.toNat inp n pins np) m st.data.dmem)
    (hok : CmpBufOk frozenIdsL OUT m) (hBm : B = cmpBuf OUT m) {rs : List Word}
    (hrax : st.data.regs.rax = rs.getD 0 0) :
    ∃ ths' : List (Mem × List (Word × Nat × Mem)),
      (∀ t ∈ ths', (∀ b ∈ parOwnedL, t.1.arr64 b = zeros (m.arr64 b).size) ∧ t.1.glob INIT = 0 ∧
        ThreadRuns (cmpBuf OUT m) t.1 t.2 ∧ ∀ c ∈ t.2, c.1 < rs.getD 0 0 - 9223372036854775808) ∧
      (∀ j : Word, j < rs.getD 0 0 - 9223372036854775808 → ∃ t ∈ ths', ∃ c ∈ t.2, c.1 = j) ∧
      (∀ t ∈ ths', (t.2.map (·.1)).Pairwise (· < ·)) ∧
      ∀ t ∈ ths, ∀ i < t.n, RegsRestored (t.dm i).regs (t.st i).data.regs := by
  have hB := hok.2
  rw [← hBm] at hB
  have hpos : 0 < frozenIdsL.length := by rw [frozenIdsL_eq]; simp
  have hhdr : ∀ i < frozenIdsL.length, 9 + 2 * i < B.size := fun i hi => by
    have := hB.hdr i hi; have := hB.ent 0 hpos; have := hB.hdr0; omega
  obtain ⟨f, hf⟩ := Classical.axiomOfChoice (threadsAcc_runs k0 hcode dm st B ths hA hhdr hB.ent hB.disj)
  have hzero : ∀ a ∈ parOwnedL, (zeroMem checkerTab).arr64 a = zeros (m.arr64 a).size := by
    intro a ha
    have hl := parOwnedL_dom a ha
    rw [hM.size64 a hl]
    simp only [abiLayout_tab]
    rw [abiLayout_s64 _ _ _ _ _ _ (by
      have := checkerTab.pos64_lt hl; have := (abiTabOk_spec checkerTab_abiOk).1; omega), checkerTab.wAt_pos64 hl]
    simp [zeroMem, Mem.arr64, zeros]
  refine ⟨ths.map fun t => (zeroMem checkerTab, f t), fun t' ht' => ?_, fun j hj => ?_, fun t' ht' => ?_,
    fun t ht i hi => (hf t ht).2.2.2.1 i hi⟩
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    obtain ⟨h1, h2, -, -, -⟩ := hf t ht
    exact ⟨hzero, rfl, hBm ▸ h1, fun c hc => by rw [← hrax]; exact h2 c hc⟩
  · rw [← hrax] at hj
    obtain ⟨t, ht, i, hi, hj'⟩ := hcov j hj
    obtain ⟨-, -, h3, -, -⟩ := hf t ht
    obtain ⟨c, hc', hcj⟩ := h3 i hi
    exact ⟨_, List.mem_map.mpr ⟨t, ht, rfl⟩, c, hc', by rw [hcj, hj']⟩
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    exact (hf t ht).2.2.2.2

/-! ## The harness's facts

`CmpThreadsRun` is the chain `CmpTRun4` ⊂ `CmpTRun5` ⊂ `CmpTRunS` ⊂ `CmpTRun7` ⊂ `CmpTRunC`: the
harness's facts up to each call, which the threaded verdict (`Final/CmpThreadsVerdict.lean`)
reuses for the calls before a failing one. -/

/-- The challenge's driver call (`ca_start_a4`) and its return. -/
structure CmpTRun4 [Host] (bC pb : ByteArray) (dm₄ : MachineData) (ra₄ : Word) (st₄ : MachineState) : Prop where
  call₄ : AbiCall bC pb dm₄ ra₄
  ret₄ : FirstReturn dm₄ (label abiStartA4L) ra₄ st₄

/-- Then the solution's driver call (`ca_start_a5`), on the same region and pin data, holding what
the first call left, and its return. -/
structure CmpTRun5 [Host] (bC bS pb : ByteArray) (dm₄ : MachineData) (ra₄ : Word) (st₄ : MachineState)
    (dm₅ : MachineData) (ra₅ : Word) (st₅ : MachineState) : Prop extends CmpTRun4 bC pb dm₄ ra₄ st₄ where
  rdx₄ : st₄.data.regs.rdx = 0
  rax₄ : 9223372036854775808 ≤ st₄.data.regs.rax.toNat
  call₅ : AbiCallM bS pb dm₅ ra₅
  same₅ : dm₅.regs.r8 = dm₄.regs.r8 ∧ dm₅.regs.r9 = dm₄.regs.r9 ∧ dm₅.regs.rdx = dm₄.regs.rdx
  /-- the region, the challenge's buffer and the pin data as the first call left them -/
  keep₅ : ∀ x, (dm₄.regs.r8.toNat ≤ x ∧ x < dm₄.regs.r8.toNat + dm₄.regs.r9.toNat) ∨
    (dm₄.regs.rdi.toNat ≤ x ∧ x < dm₄.regs.rdi.toNat + bC.size) ∨
    (dm₄.regs.rdx.toNat ≤ x ∧ x < dm₄.regs.rdx.toNat + pb.size) →
    dm₅.dmem.get? (A x) = st₄.data.dmem.get? (A x)
  ret₅ : FirstReturn dm₅ (label abiStartA5L) ra₅ st₅

/-- Then the solution's buffer `BS`. -/
structure CmpTRunS [Host] (bC bS pb : ByteArray) (dm₄ : MachineData) (ra₄ : Word) (st₄ : MachineState)
    (dm₅ : MachineData) (ra₅ : Word) (st₅ : MachineState) (BS : Array Word) : Prop
    extends CmpTRun5 bC bS pb dm₄ ra₄ st₄ dm₅ ra₅ st₅ where
  rdx₅ : st₅.data.regs.rdx = 0
  rax₅ : 9223372036854775808 ≤ st₅.data.regs.rax.toNat
  /-- the solution's buffer: `OUT`'s first `len` words, `len` its word `1` -/
  bufwS : ∀ i (h : i < BS.size), rdW st₅.data.dmem (A (outAddr dm₅.regs.r8.toNat + 8 * i)) = some BS[i]
  buflenS : ∃ w, rdW st₅.data.dmem (A (outAddr dm₅.regs.r8.toNat + 8)) = some w ∧ w.toNat = BS.size

/-- Then the solution's pool `thsS` (every call accepting, every job index below `kS` claimed),
and the challenge's index call (`ca_start_a7`), on the same region and pin data, holding what the
second call left, and its return. -/
structure CmpTRun7 [Host] (bC bS pb : ByteArray) (dm₄ : MachineData) (ra₄ : Word) (st₄ : MachineState)
    (dm₅ : MachineData) (ra₅ : Word) (st₅ : MachineState) (BS : Array Word) (thsS : List ThreadM)
    (dm₇ : MachineData) (ra₇ : Word) (st₇ : MachineState) : Prop
    extends CmpTRunS bC bS pb dm₄ ra₄ st₄ dm₅ ra₅ st₅ BS where
  thrS : ThreadsAcc dm₅ st₅ BS thsS
  coverS : ∀ j : Word, j < st₅.data.regs.rax - 9223372036854775808 →
    ∃ t ∈ thsS, ∃ i < t.n, (t.dm i).regs.rdx = j
  call₇ : AbiCallM bS pb dm₇ ra₇
  same₇ : dm₇.regs.r8 = dm₄.regs.r8 ∧ dm₇.regs.r9 = dm₄.regs.r9 ∧ dm₇.regs.rdx = dm₄.regs.rdx
  /-- the region, the solution's buffer and the pin data as the second call left them -/
  keep₇ : ∀ x, (dm₄.regs.r8.toNat ≤ x ∧ x < dm₄.regs.r8.toNat + dm₄.regs.r9.toNat) ∨
    (dm₅.regs.rdi.toNat ≤ x ∧ x < dm₅.regs.rdi.toNat + bS.size) ∨
    (dm₄.regs.rdx.toNat ≤ x ∧ x < dm₄.regs.rdx.toNat + pb.size) →
    dm₇.dmem.get? (A x) = st₅.data.dmem.get? (A x)
  ret₇ : FirstReturn dm₇ (label abiStartA7L) ra₇ st₇

/-- Then the challenge's buffer `BC`. -/
structure CmpTRunC [Host] (bC bS pb : ByteArray) (dm₄ : MachineData) (ra₄ : Word) (st₄ : MachineState)
    (dm₅ : MachineData) (ra₅ : Word) (st₅ : MachineState) (BS : Array Word) (thsS : List ThreadM)
    (dm₇ : MachineData) (ra₇ : Word) (st₇ : MachineState) (BC : Array Word) : Prop
    extends CmpTRun7 bC bS pb dm₄ ra₄ st₄ dm₅ ra₅ st₅ BS thsS dm₇ ra₇ st₇ where
  rdx₇ : st₇.data.regs.rdx = 0
  rax₇ : 9223372036854775808 ≤ st₇.data.regs.rax.toNat
  /-- the challenge's buffer -/
  bufwC : ∀ i (h : i < BC.size), rdW st₇.data.dmem (A (outAddr dm₇.regs.r8.toNat + 8 * i)) = some BC[i]
  buflenC : ∃ w, rdW st₇.data.dmem (A (outAddr dm₇.regs.r8.toNat + 8)) = some w ∧ w.toNat = BC.size

/-- **What the threaded compared harness does** (trusted; the module doc lists it): `ca_start_a4`
at `dm₄` (the challenge `bC`, the pin data `pb`, a zero region) returning at `st₄`;
`ca_start_a5` at `dm₅` (the solution `bS`, the same pin data and region, holding what the first
call left) returning at `st₅`; the solution's buffer `BS` and its threads `thsS`, whose calls all
accept and claim every job index below `kS`; `ca_start_a7` at `dm₇` (the solution again, the same
pin data and region, holding what the second call left) returning at `st₇`; the challenge's
buffer `BC` and its threads `thsC`, likewise. -/
structure CmpThreadsRun [Host] (bC bS pb : ByteArray)
    (dm₄ : MachineData) (ra₄ : Word) (st₄ : MachineState)
    (dm₅ : MachineData) (ra₅ : Word) (st₅ : MachineState) (BS : Array Word) (thsS : List ThreadM)
    (dm₇ : MachineData) (ra₇ : Word) (st₇ : MachineState) (BC : Array Word) (thsC : List ThreadM) : Prop
    extends CmpTRunC bC bS pb dm₄ ra₄ st₄ dm₅ ra₅ st₅ BS thsS dm₇ ra₇ st₇ BC where
  /-- the challenge's pool -/
  thrC : ThreadsAcc dm₇ st₇ BC thsC
  coverC : ∀ j : Word, j < st₇.data.regs.rax - 9223372036854775808 →
    ∃ t ∈ thsC, ∃ i < t.n, (t.dm i).regs.rdx = j

/-! ## The driver calls -/

/-- A mode entry (`cmpStub`'s and `ctaStub`'s): the mode word `w`, then the setup stub. -/
def modeEntry (tab : Tab) (mode : GVar) (w : Word) (lab : Label) : Program :=
  [.label lab, movRI .rax (abiNeed tab).toUInt64, i64 (.cmp (.reg (rr .r9)) (oR .rax)), jccL .c abiSetupL,
   movRI .rax w, movMR (mb .r8 (tab.globOff mode)) .rax, jmpL abiSetupL]

theorem modeEntry_length (tab : Tab) (mode : GVar) (w : Word) (lab : Label) :
    (modeEntry tab mode w lab).length = 7 := rfl

/-- `cmpStub` starts with the entries of modes `4` and `5`. -/
theorem cmpStubL_split (tab : Tab) (mode : GVar) (out : ArrId) (own : List TieredArray) :
    ∃ rest, cmpStubL tab mode out own =
      modeEntry tab mode 4 abiStartA4L ++ (modeEntry tab mode 5 abiStartA5L ++ rest) := ⟨_, rfl⟩

theorem ctaStub_eq (tab : Tab) (mode : GVar) : ctaStub tab mode = modeEntry tab mode 7 abiStartA7L := rfl

section
variable [Host]

/-- A mode entry's call on a zero region (`abiMode_outcome`). -/
theorem modeEntry_outcome (q p : Prog) (hq : Refines q p) (tab : Tab) (hok : abiTabOk tab = true)
    {X : AsmTab} (hAX : AsmOkT q tab X) (hio : abiIO tab = true)
    (hwf : Prog.wf tab q = true) (mode : GVar) (hng : mode.id < tab.ng) (w : Word) (lab : Label)
    (k k0 : Nat) (hC : Code (modeEntry tab mode w lab) k)
    (hcR : Code (abiStub tab ++ compileProgX X tab q "check") k0)
    (fd : FunDecl) (hentry : p.lookup "check" = some fd) (hnp : fd.nparams = 0)
    (b pb : ByteArray) (dm : MachineData) (ra : Word) (hc : AbiCall b pb dm ra) :
    Ev (fun st => EntryPost (abiLayout tab dm.regs.r8.toNat dm.regs.rdi.toNat b.size dm.regs.rdx.toNat pb.size)
        dm ra (L.run p abiFuel "check" [] ((loadMem b pb (abiSz tab)).setG mode w)) st ∧
        SizesPost b pb st)
      dm (label lab) :=
  abiMode_outcome q p hq tab hok hAX hio hwf mode hng w lab k k0 (Code.label (i := 0) hC rfl)
    (hC.get (i := 0) rfl) (hC.get (i := 1) rfl) (hC.get (i := 2) rfl) (hC.get (i := 3) rfl)
    (hC.get (i := 4) rfl) (hC.get (i := 5) rfl) (hC.get (i := 6) rfl) hcR fd hentry hnp b pb dm ra hc

/-- A mode entry's call on a region that holds an L memory (`abiModeM_outcome`). -/
theorem modeEntryM_outcome (q p : Prog) (hq : Refines q p) (tab : Tab) (hok : abiTabOk tab = true)
    {X : AsmTab} (hAX : AsmOkT q tab X) (hio : abiIO tab = true)
    (hwf : Prog.wf tab q = true) (mode : GVar) (hng : mode.id < tab.ng) (w : Word) (lab : Label)
    (k k0 : Nat) (hC : Code (modeEntry tab mode w lab) k)
    (hcR : Code (abiStub tab ++ compileProgX X tab q "check") k0)
    (fd : FunDecl) (hentry : p.lookup "check" = some fd) (hnp : fd.nparams = 0)
    (bs pb : ByteArray) (dm : MachineData) (ra : Word) (hc : AbiCallM bs pb dm ra)
    {m : Mem} {inp0 n0 : Nat}
    (hm : abiNeed tab ≤ dm.regs.r9.toNat →
      MemRel (abiLayout tab dm.regs.r8.toNat inp0 n0 dm.regs.rdx.toNat pb.size) m dm.dmem) :
    Ev (fun st => EntryPost (abiLayout tab dm.regs.r8.toNat dm.regs.rdi.toNat bs.size dm.regs.rdx.toNat pb.size)
        dm ra (L.run p abiFuel "check" [] ((cmpIn m bs).setG mode w)) st ∧
        SizesPost bs pb st)
      dm (label lab) :=
  abiModeM_outcome q p hq tab hok hAX hio hwf mode hng w lab k k0 (Code.label (i := 0) hC rfl)
    (hC.get (i := 0) rfl) (hC.get (i := 1) rfl) (hC.get (i := 2) rfl) (hC.get (i := 3) rfl)
    (hC.get (i := 4) rfl) (hC.get (i := 5) rfl) (hC.get (i := 6) rfl) hcR fd hentry hnp bs pb dm ra hc hm

end

/-- The three mode entries of the threaded compared run in the committed file. -/
theorem code_of_checkerFile_entries [Host] {k0 : Nat} (hcode : Code checkerFile k0) :
    (∃ k, Code (modeEntry checkerTab MODE 4 abiStartA4L) k) ∧
    (∃ k, Code (modeEntry checkerTab MODE 5 abiStartA5L) k) ∧
    (∃ k, Code (modeEntry checkerTab MODE 7 abiStartA7L) k) := by
  obtain ⟨Kc, hC, hC7⟩ := code_of_checkerFile_cta hcode
  obtain ⟨rest, e⟩ := cmpStubL_split checkerTab MODE OUT parOwnedL
  rw [e] at hC
  rw [ctaStub_eq] at hC7
  exact ⟨⟨_, hC.left⟩, ⟨_, hC.right.left⟩, ⟨_, hC7⟩⟩

/-- `ca_start_a4`'s outcome on the machine. -/
theorem cta_a4 [Host] (k0 : Nat) (hcode : Code checkerFile k0) (bC pb : ByteArray) (dm : MachineData)
    (ra : Word) (hc : AbiCall bC pb dm ra) :
    Ev (fun st => EntryPost (abiLayout checkerTab dm.regs.r8.toNat dm.regs.rdi.toNat bC.size dm.regs.rdx.toNat pb.size)
        dm ra (cmpRun checkerProg (cmpM4 checkerTab MODE bC pb)) st ∧ SizesPost bC pb st)
      dm (label abiStartA4L) := by
  obtain ⟨⟨k, hC⟩, -, -⟩ := code_of_checkerFile_entries hcode
  exact modeEntry_outcome checkerProgI checkerProg checkerProgI_refines checkerTab checkerTab_abiOk checkerX_ok
    checkerTab_abiIO checkerProgI_wf MODE (by decide) 4 abiStartA4L k _ hC
    (code_of_checkerFile_par hcode).right L.Checker.checkL checkerProg_lookup_check (by decide) bC pb dm ra hc

/-- `ca_start_a5`'s outcome on the machine, on a region that holds `m`. -/
theorem cta_a5 [Host] (k0 : Nat) (hcode : Code checkerFile k0) (bS pb : ByteArray) (dm : MachineData)
    (ra : Word) (hc : AbiCallM bS pb dm ra) {m : Mem} {inp0 n0 : Nat}
    (hm : abiNeed checkerTab ≤ dm.regs.r9.toNat →
      MemRel (abiLayout checkerTab dm.regs.r8.toNat inp0 n0 dm.regs.rdx.toNat pb.size) m dm.dmem) :
    Ev (fun st => EntryPost (abiLayout checkerTab dm.regs.r8.toNat dm.regs.rdi.toNat bS.size dm.regs.rdx.toNat pb.size)
        dm ra (cmpRun checkerProg (cmpM5 MODE m bS)) st ∧ SizesPost bS pb st)
      dm (label abiStartA5L) := by
  obtain ⟨-, ⟨k, hC⟩, -⟩ := code_of_checkerFile_entries hcode
  exact modeEntryM_outcome checkerProgI checkerProg checkerProgI_refines checkerTab checkerTab_abiOk checkerX_ok
    checkerTab_abiIO checkerProgI_wf MODE (by decide) 5 abiStartA5L k _ hC
    (code_of_checkerFile_par hcode).right L.Checker.checkL checkerProg_lookup_check (by decide) bS pb dm ra hc hm

/-- `ca_start_a7`'s outcome on the machine, on a region that holds `m`. -/
theorem cta_a7 [Host] (k0 : Nat) (hcode : Code checkerFile k0) (bS pb : ByteArray) (dm : MachineData)
    (ra : Word) (hc : AbiCallM bS pb dm ra) {m : Mem} {inp0 n0 : Nat}
    (hm : abiNeed checkerTab ≤ dm.regs.r9.toNat →
      MemRel (abiLayout checkerTab dm.regs.r8.toNat inp0 n0 dm.regs.rdx.toNat pb.size) m dm.dmem) :
    Ev (fun st => EntryPost (abiLayout checkerTab dm.regs.r8.toNat dm.regs.rdi.toNat bS.size dm.regs.rdx.toNat pb.size)
        dm ra (cmpRun checkerProg (cmpM7 MODE m bS)) st ∧ SizesPost bS pb st)
      dm (label abiStartA7L) := by
  obtain ⟨-, -, ⟨k, hC⟩⟩ := code_of_checkerFile_entries hcode
  exact modeEntryM_outcome checkerProgI checkerProg checkerProgI_refines checkerTab checkerTab_abiOk checkerX_ok
    checkerTab_abiIO checkerProgI_wf MODE (by decide) 7 abiStartA7L k _ hC
    (code_of_checkerFile_par hcode).right L.Checker.checkL checkerProg_lookup_check (by decide) bS pb dm ra hc hm

/-! ## The runs up to each phase -/

/-- **The solution's driver call's return**: mode `4`'s run ok (returning `2^63` or more), and
`ca_start_a5`'s post at `st₅` for mode `5`'s run from its memory `m4`. -/
theorem cmpT_post5 [Host] (k0 : Nat) (hcode : Code checkerFile k0) {bC bS pb : ByteArray}
    {dm₄ : MachineData} {ra₄ : Word} {st₄ : MachineState} {dm₅ : MachineData} {ra₅ : Word}
    {st₅ : MachineState} (hR5 : CmpTRun5 bC bS pb dm₄ ra₄ st₄ dm₅ ra₅ st₅) :
    bC.size < 2 ^ 63 ∧ pb.size < 2 ^ 63 ∧ RegsRestored dm₄.regs st₄.data.regs ∧
      ∃ rs4 m4, cmpRun checkerProg (cmpM4 checkerTab MODE bC pb) = .ok (rs4, m4) ∧
        2 ^ 63 ≤ (rs4.getD 0 0).toNat ∧
        EntryPost (abiLayout checkerTab dm₅.regs.r8.toNat dm₅.regs.rdi.toNat bS.size dm₅.regs.rdx.toNat pb.size)
          dm₅ ra₅ (cmpRun checkerProg (cmpM5 MODE m4 bS)) st₅ ∧ SizesPost bS pb st₅ := by
  have hn : 1 ≤ checkerTab.nres := by decide
  obtain ⟨h58, h59, h5x⟩ := hR5.same₅
  obtain ⟨hbC, hpb, hRR₄, rs4, m4, h4, hrax4, hM4⟩ :=
    cta_ret hn (hR5.ret₄ _ (cta_a4 k0 hcode bC pb dm₄ ra₄ hR5.call₄) (fun s h => h.1.1)) hR5.rdx₄
  have hge4 : 2 ^ 63 ≤ (rs4.getD 0 0).toNat := by rw [← hrax4]; exact hR5.rax₄
  have hE5 := cta_a5 k0 hcode bS pb dm₅ ra₅ hR5.call₅ (m := m4) (inp0 := dm₄.regs.rdi.toNat) (n0 := bC.size)
    (fun hneed => by
      rw [h58, h5x]
      rw [h59] at hneed
      exact memRel_carry checkerTab_abiOk hneed hM4 hR5.keep₅)
  exact ⟨hbC, hpb, hRR₄, rs4, m4, h4, hge4, hR5.ret₅ _ hE5 (fun s h => h.1.1)⟩

/-- **Up to the solution's buffer**: both driver calls ran ok (the L runs of modes `4` and `5`,
the first returning `2^63` or more), the memory `m5` in the region at `st₅`. -/
theorem cmpT_upToS [Host] (k0 : Nat) (hcode : Code checkerFile k0) {bC bS pb : ByteArray}
    {dm₄ : MachineData} {ra₄ : Word} {st₄ : MachineState} {dm₅ : MachineData} {ra₅ : Word}
    {st₅ : MachineState} (hR5 : CmpTRun5 bC bS pb dm₄ ra₄ st₄ dm₅ ra₅ st₅) (h0 : st₅.data.regs.rdx = 0) :
    bC.size < 2 ^ 63 ∧ bS.size < 2 ^ 63 ∧ pb.size < 2 ^ 63 ∧
      RegsRestored dm₄.regs st₄.data.regs ∧ RegsRestored dm₅.regs st₅.data.regs ∧
      ∃ rs4 m4 rs5 m5, cmpRun checkerProg (cmpM4 checkerTab MODE bC pb) = .ok (rs4, m4) ∧
        2 ^ 63 ≤ (rs4.getD 0 0).toNat ∧ cmpRun checkerProg (cmpM5 MODE m4 bS) = .ok (rs5, m5) ∧
        st₅.data.regs.rax = rs5.getD 0 0 ∧
        MemRel (abiLayout checkerTab dm₅.regs.r8.toNat dm₅.regs.rdi.toNat bS.size dm₅.regs.rdx.toNat pb.size)
          m5 st₅.data.dmem := by
  obtain ⟨hbC, hpb, hRR₄, rs4, m4, h4, hge4, hP5⟩ := cmpT_post5 k0 hcode hR5
  obtain ⟨hbS, -, hRR₅, rs5, m5, h5, hrax5, hM5⟩ := cta_ret (by decide) hP5 h0
  exact ⟨hbC, hbS, hpb, hRR₄, hRR₅, rs4, m4, rs5, m5, h4, hge4, h5, hrax5, hM5⟩

/-- The solution's pool at the L level, as `cmpThreads_twinPooled` takes it. -/
def CmpTPoolS (m5 : Mem) (rs5 : List Word) (thsS' : List (Mem × List (Word × Nat × Mem))) : Prop :=
  (∀ t ∈ thsS', (∀ b ∈ parOwnedL, t.1.arr64 b = zeros (m5.arr64 b).size) ∧ t.1.glob INIT = 0 ∧
    ThreadRuns (cmpBuf OUT m5) t.1 t.2 ∧ ∀ c ∈ t.2, c.1 < rs5.getD 0 0 - 9223372036854775808) ∧
  (∀ j : Word, j < rs5.getD 0 0 - 9223372036854775808 → ∃ t ∈ thsS', ∃ c ∈ t.2, c.1 = j) ∧
  (∀ t ∈ thsS', (t.2.map (·.1)).Pairwise (· < ·))

/-- **The challenge's index call's return**: as `cmpT_upToS`, mode `5` returning `2^63` or more,
the solution's pool at the L level, and `ca_start_a7`'s post at `st₇` for mode `7`'s run from
mode `5`'s memory `m5`. -/
theorem cmpT_post7 [Host] (k0 : Nat) (hcode : Code checkerFile k0) (h64 : System.Platform.numBits = 64)
    {bC bS pb : ByteArray}
    {dm₄ : MachineData} {ra₄ : Word} {st₄ : MachineState} {dm₅ : MachineData} {ra₅ : Word}
    {st₅ : MachineState} {BS : Array Word} {thsS : List ThreadM} {dm₇ : MachineData} {ra₇ : Word}
    {st₇ : MachineState} (hR7 : CmpTRun7 bC bS pb dm₄ ra₄ st₄ dm₅ ra₅ st₅ BS thsS dm₇ ra₇ st₇) :
    bC.size < 2 ^ 63 ∧ bS.size < 2 ^ 63 ∧ pb.size < 2 ^ 63 ∧
      RegsRestored dm₄.regs st₄.data.regs ∧ RegsRestored dm₅.regs st₅.data.regs ∧
      (∀ t ∈ thsS, ∀ i < t.n, RegsRestored (t.dm i).regs (t.st i).data.regs) ∧
      ∃ rs4 m4 rs5 m5, cmpRun checkerProg (cmpM4 checkerTab MODE bC pb) = .ok (rs4, m4) ∧
        2 ^ 63 ≤ (rs4.getD 0 0).toNat ∧ cmpRun checkerProg (cmpM5 MODE m4 bS) = .ok (rs5, m5) ∧
        2 ^ 63 ≤ (rs5.getD 0 0).toNat ∧
        ∃ thsS' : List (Mem × List (Word × Nat × Mem)), CmpTPoolS m5 rs5 thsS' ∧
          EntryPost (abiLayout checkerTab dm₇.regs.r8.toNat dm₇.regs.rdi.toNat bS.size dm₇.regs.rdx.toNat pb.size)
            dm₇ ra₇ (cmpRun checkerProg (cmpM7 MODE m5 bS)) st₇ ∧ SizesPost bS pb st₇ := by
  obtain ⟨h58, h59, h5x⟩ := hR7.same₅
  obtain ⟨h78, h79, h7x⟩ := hR7.same₇
  obtain ⟨hbC, hbS, hpb, hRR₄, hRR₅, rs4, m4, rs5, m5, h4, hge4, h5, hrax5, hM5⟩ :=
    cmpT_upToS k0 hcode hR7.toCmpTRun5 hR7.rdx₅
  have hge5 : 2 ^ 63 ≤ (rs5.getD 0 0).toNat := by rw [← hrax5]; exact hR7.rax₅
  have hok5 := checker_cmpBufOk bC bS pb h64 hbC hbS hpb h4 hge4 h5 hge5
  -- the solution's pool
  have hBS := cta_bufEq hM5 hok5 hR7.bufwS hR7.buflenS
  obtain ⟨thsS', hthS, hcovS, hincS, hRRS⟩ :=
    cta_pool k0 hcode dm₅ st₅ BS thsS hR7.thrS hR7.coverS hM5 hok5 hBS hrax5
  -- the challenge's index call
  have hE7 := cta_a7 k0 hcode bS pb dm₇ ra₇ hR7.call₇ (m := m5) (inp0 := dm₅.regs.rdi.toNat) (n0 := bS.size)
    (fun hneed => by
      rw [h78, h7x]
      rw [h79] at hneed
      rw [h58, h5x] at hM5
      exact memRel_carry checkerTab_abiOk hneed hM5 hR7.keep₇)
  exact ⟨hbC, hbS, hpb, hRR₄, hRR₅, hRRS, rs4, m4, rs5, m5, h4, hge4, h5, hge5, thsS', ⟨hthS, hcovS, hincS⟩,
    hR7.ret₇ _ hE7 (fun s h => h.1.1)⟩

/-- **Up to the challenge's buffer**: as `cmpT_post7`, mode `7`'s run ok, the memory `m7` in the
region at `st₇`. -/
theorem cmpT_upToC [Host] (k0 : Nat) (hcode : Code checkerFile k0) (h64 : System.Platform.numBits = 64)
    {bC bS pb : ByteArray}
    {dm₄ : MachineData} {ra₄ : Word} {st₄ : MachineState} {dm₅ : MachineData} {ra₅ : Word}
    {st₅ : MachineState} {BS : Array Word} {thsS : List ThreadM} {dm₇ : MachineData} {ra₇ : Word}
    {st₇ : MachineState} (hR7 : CmpTRun7 bC bS pb dm₄ ra₄ st₄ dm₅ ra₅ st₅ BS thsS dm₇ ra₇ st₇)
    (h0 : st₇.data.regs.rdx = 0) :
    bC.size < 2 ^ 63 ∧ bS.size < 2 ^ 63 ∧ pb.size < 2 ^ 63 ∧
      RegsRestored dm₄.regs st₄.data.regs ∧ RegsRestored dm₅.regs st₅.data.regs ∧
      RegsRestored dm₇.regs st₇.data.regs ∧
      (∀ t ∈ thsS, ∀ i < t.n, RegsRestored (t.dm i).regs (t.st i).data.regs) ∧
      ∃ rs4 m4 rs5 m5, cmpRun checkerProg (cmpM4 checkerTab MODE bC pb) = .ok (rs4, m4) ∧
        2 ^ 63 ≤ (rs4.getD 0 0).toNat ∧ cmpRun checkerProg (cmpM5 MODE m4 bS) = .ok (rs5, m5) ∧
        2 ^ 63 ≤ (rs5.getD 0 0).toNat ∧
        ∃ thsS' : List (Mem × List (Word × Nat × Mem)), CmpTPoolS m5 rs5 thsS' ∧
          ∃ rs7 m7, cmpRun checkerProg (cmpM7 MODE m5 bS) = .ok (rs7, m7) ∧
            st₇.data.regs.rax = rs7.getD 0 0 ∧
            MemRel (abiLayout checkerTab dm₇.regs.r8.toNat dm₇.regs.rdi.toNat bS.size dm₇.regs.rdx.toNat pb.size)
              m7 st₇.data.dmem := by
  obtain ⟨hbC, hbS, hpb, hRR₄, hRR₅, hRRS, rs4, m4, rs5, m5, h4, hge4, h5, hge5, thsS', hS, hP7⟩ :=
    cmpT_post7 k0 hcode h64 hR7
  obtain ⟨-, -, hRR₇, rs7, m7, h7, hrax7, hM7⟩ := cta_ret (by decide) hP7 h0
  exact ⟨hbC, hbS, hpb, hRR₄, hRR₅, hRR₇, hRRS, rs4, m4, rs5, m5, h4, hge4, h5, hge5, thsS', hS,
    rs7, m7, h7, hrax7, hM7⟩

/-! ## The theorem -/

set_option linter.constructorNameAsVariable false in
/-- **The threaded compared run's accept is the twin's pooled comparison's accept**, for the
committed file `checker.s`: the trusted threaded harness runs as `CmpThreadsRun` says. And every
call, the three driver calls and each `ca_check_b`, returns with the caller's registers. -/
theorem checkerFile_compare_threads_accept_regs [Host] (k0 : Nat) (hcode : Code checkerFile k0)
    (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (dm₄ : MachineData) (ra₄ : Word) (st₄ : MachineState)
    (dm₅ : MachineData) (ra₅ : Word) (st₅ : MachineState) (BS : Array Word) (thsS : List ThreadM)
    (dm₇ : MachineData) (ra₇ : Word) (st₇ : MachineState) (BC : Array Word) (thsC : List ThreadM)
    (hR : CmpThreadsRun bC bS pb dm₄ ra₄ st₄ dm₅ ra₅ st₅ BS thsS dm₇ ra₇ st₇ BC thsC) :
    TwinComparesAcceptsPooled bC bS ∧
      RegsRestored dm₄.regs st₄.data.regs ∧ RegsRestored dm₅.regs st₅.data.regs ∧
      RegsRestored dm₇.regs st₇.data.regs ∧
      (∀ t ∈ thsS, ∀ i < t.n, RegsRestored (t.dm i).regs (t.st i).data.regs) ∧
      (∀ t ∈ thsC, ∀ i < t.n, RegsRestored (t.dm i).regs (t.st i).data.regs) := by
  obtain ⟨hbC, hbS, hpb, hRR₄, hRR₅, hRR₇, hRRS, rs4, m4, rs5, m5, h4, hge4, h5, hge5, thsS',
    ⟨hthS, hcovS, hincS⟩, rs7, m7, h7, hrax7, hM7⟩ := cmpT_upToC k0 hcode h64 hR.toCmpTRun7 hR.rdx₇
  have hge7 : 2 ^ 63 ≤ (rs7.getD 0 0).toNat := by rw [← hrax7]; exact hR.rax₇
  have hok7 := checker_cmp7BufOk bC bS pb h64 hbC hbS hpb h4 hge4 h5 hge5 h7 hge7
  -- the challenge's pool
  have hBC := cta_bufEq hM7 hok7 hR.bufwC hR.buflenC
  obtain ⟨thsC', hthC, hcovC, hincC, hRRC⟩ :=
    cta_pool k0 hcode dm₇ st₇ BC thsC hR.thrC hR.coverC hM7 hok7 hBC hrax7
  exact ⟨cmpThreads_twinPooled bC bS pb h64 hbC hbS hpb rs4 m4 h4 hge4 rs5 m5 h5 hge5 thsS' hthS hcovS hincS
    rs7 m7 h7 hge7 thsC' hthC hcovC hincC, hRR₄, hRR₅, hRR₇, hRRS, hRRC⟩

/-- **The threaded compared run's final theorem**: the trusted threaded harness runs as
`CmpThreadsRun` says (every call reporting accept): the twin's pooled comparison accepts the
challenge `bC` with the solution `bS`. -/
theorem checkerFile_compare_threads_accept [Host] (k0 : Nat) (hcode : Code checkerFile k0)
    (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (dm₄ : MachineData) (ra₄ : Word) (st₄ : MachineState)
    (dm₅ : MachineData) (ra₅ : Word) (st₅ : MachineState) (BS : Array Word) (thsS : List ThreadM)
    (dm₇ : MachineData) (ra₇ : Word) (st₇ : MachineState) (BC : Array Word) (thsC : List ThreadM)
    (hR : CmpThreadsRun bC bS pb dm₄ ra₄ st₄ dm₅ ra₅ st₅ BS thsS dm₇ ra₇ st₇ BC thsC) :
    TwinComparesAcceptsPooled bC bS :=
  (checkerFile_compare_threads_accept_regs k0 hcode bC bS pb h64 dm₄ ra₄ st₄ dm₅ ra₅ st₅ BS thsS
    dm₇ ra₇ st₇ BC thsC hR).1

/-- **An accepted threaded comparison's challenge has a model** (as `checkerFile_compare_model`).
**Relative to set theory**, as `checkerFile_model_exists` (`Final/EndToEnd.lean`). -/
theorem checkerFile_compare_threads_model (V : Type w) [ConLeche.SetTheory V] [Host]
    (k0 : Nat) (hcode : Code checkerFile k0)
    (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (dm₄ : MachineData) (ra₄ : Word) (st₄ : MachineState)
    (dm₅ : MachineData) (ra₅ : Word) (st₅ : MachineState) (BS : Array Word) (thsS : List ThreadM)
    (dm₇ : MachineData) (ra₇ : Word) (st₇ : MachineState) (BC : Array Word) (thsC : List ThreadM)
    (hR : CmpThreadsRun bC bS pb dm₄ ra₄ st₄ dm₅ ra₅ st₅ BS thsS dm₇ ra₇ st₇ BC thsC) :
    ∃ (rcC : ConLeche.Frontend.ParseResultD) (preC : ConLeche.Frontend.PreludeIx),
      ConLeche.Frontend.parseChunks [bC] = .ok rcC ∧
      Nonempty (ConLeche.Model V (ConLeche.streamEnv
        ((ConLeche.Frontend.preparePrelude preC rcC.decls).toList.map ConLeche.Cached.sideRecord))) :=
  twinComparesAcceptsPooled_model V (checkerFile_compare_threads_accept k0 hcode bC bS pb h64
    dm₄ ra₄ st₄ dm₅ ra₅ st₅ BS thsS dm₇ ra₇ st₇ BC thsC hR)

/-- **No `False` in an accepted threaded comparison's challenge** (as
`checkerFile_compare_no_False`): if the challenge declares a theorem of type `False` (in
`jsonWithTheoremFalse`'s shape), the threaded harness's run cannot be as `CmpThreadsRun` says.
**Relative to set theory**, as `checkerFile_no_False` (`Final/EndToEnd.lean`). -/
theorem checkerFile_compare_threads_no_False (V : Type w) [ConLeche.SetTheory V] [Host]
    (k0 : Nat) (hcode : Code checkerFile k0)
    (bC bS pb : ByteArray) (hfalse : ConLeche.jsonWithTheoremFalse [bC])
    (h64 : System.Platform.numBits = 64)
    (dm₄ : MachineData) (ra₄ : Word) (st₄ : MachineState)
    (dm₅ : MachineData) (ra₅ : Word) (st₅ : MachineState) (BS : Array Word) (thsS : List ThreadM)
    (dm₇ : MachineData) (ra₇ : Word) (st₇ : MachineState) (BC : Array Word) (thsC : List ThreadM) :
    ¬ CmpThreadsRun bC bS pb dm₄ ra₄ st₄ dm₅ ra₅ st₅ BS thsS dm₇ ra₇ st₇ BC thsC := fun hR =>
  twinComparesAcceptsPooled_no_False V hfalse (checkerFile_compare_threads_accept k0 hcode bC bS pb h64
    dm₄ ra₄ st₄ dm₅ ra₅ st₅ BS thsS dm₇ ra₇ st₇ BC thsC hR)

end ConAgua.Final
