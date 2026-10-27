import ConAgua.Final.Statement
import ConAgua.Compiler.AbiSim
import Kraken.X64.Registers

/-!
# The setup stub on the machine: `ca_setup` (called with `ca_start`'s arguments)

`AbiCall`: how the harness calls `ca_start(in, in_len, pins, pins_len, base, base_len)`: the input
bytes `b` at `in`, the pin data `pb` at `pins`, and a zero region `[base, base + base_len)` apart
from both buffers and from the caller's stack. The driver `ca_start` passes the call on to entry 1,
which jumps to the setup stub (`ConAgua/Compiler/Abi.lean`) with the same arguments. The stub lays
out the table, the L stack and the word arrays inside the region (`abiLayout`; `sim_abiStub`,
`abi_memRel`) and enters the trampoline with `compile_correct`'s premises (`abi_harness`). If
`base_len` is too small the stub returns `rdx = 1` at once. Entry 1 on the machine:
`ConAgua/Final/ParAbi.lean`; the driver: `ConAgua/Final/DrvAbi.lean`.
-/

namespace ConAgua.Final

open L L.Compiler

/-- **How the harness calls `ca_start`**: System V arguments `rdi, rsi` = the input buffer and its
length, `rdx, rcx` = the pin-data buffer and its length, `r8, r9` = the region and its length;
the buffers hold `b` and `pb`; the region is zero, in the address space, and apart from both
buffers; the buffers are apart from each other; the return address is on the machine stack, whose
32 bytes around `rsp` are mapped and apart from the region and the buffers. -/
structure AbiCall (b pb : ByteArray) (dm : MachineData) (ra : Word) : Prop where
  hin : ∀ i (h : i < b.size), dm.dmem.get? (A (dm.regs.rdi.toNat + i)) = some b[i]
  hn : dm.regs.rsi.toNat = b.size
  hpins : ∀ i (h : i < pb.size), dm.dmem.get? (A (dm.regs.rdx.toNat + i)) = some pb[i]
  hnp : dm.regs.rcx.toNat = pb.size
  hzero : ∀ x, dm.regs.r8.toNat ≤ x → x < dm.regs.r8.toNat + dm.regs.r9.toNat → dm.dmem.get? (A x) = some 0
  hfits : dm.regs.r8.toNat + dm.regs.r9.toNat < 2 ^ 64
  hinEnd : dm.regs.rdi.toNat + b.size < 2 ^ 64
  hpinsEnd : dm.regs.rdx.toNat + pb.size < 2 ^ 64
  hinDisj : ∀ x, dm.regs.rdi.toNat ≤ x → x < dm.regs.rdi.toNat + b.size →
    x < dm.regs.r8.toNat ∨ dm.regs.r8.toNat + dm.regs.r9.toNat ≤ x
  hpinsDisj : ∀ x, dm.regs.rdx.toNat ≤ x → x < dm.regs.rdx.toNat + pb.size →
    x < dm.regs.r8.toNat ∨ dm.regs.r8.toNat + dm.regs.r9.toNat ≤ x
  hbufDisj : ∀ x, dm.regs.rdi.toNat ≤ x → x < dm.regs.rdi.toNat + b.size →
    ¬ (dm.regs.rdx.toNat ≤ x ∧ x < dm.regs.rdx.toNat + pb.size)
  hra : rdW dm.dmem (A dm.regs.rsp.toNat) = some ra
  hcs : ∀ x, dm.regs.rsp.toNat - 24 ≤ x → x < dm.regs.rsp.toNat + 8 →
    (dm.dmem.get? (A x)).isSome ∧ (x < dm.regs.r8.toNat ∨ dm.regs.r8.toNat + dm.regs.r9.toNat ≤ x) ∧
    ¬ (dm.regs.rdi.toNat ≤ x ∧ x < dm.regs.rdi.toNat + b.size) ∧
    ¬ (dm.regs.rdx.toNat ≤ x ∧ x < dm.regs.rdx.toNat + pb.size)
  hcs24 : 24 ≤ dm.regs.rsp.toNat
  hcs8 : dm.regs.rsp.toNat + 8 < 2 ^ 64

/-- A word of zero bytes reads as `0`. -/
theorem rdW_of_zero {d : DataMem} {x : Nat} (_hx : x + 8 ≤ 2 ^ 64)
    (h : ∀ j < 8, d.get? (A (x + j)) = some 0) : rdW d (A x) = some 0 := by
  have : rdW d (A x) = rdW (wrW d (A x) 0) (A x) := by
    refine rdW_congr fun j hj => ?_
    rw [A_add, get?_wrW_byte hj, h j hj]
    have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [this, rdW_wrW_same]; rfl

/-- The memory the stub leaves: L's initial memory (`loadMem` with the input bytes, the pin data
and zero word arrays of `abiWords` words) in the stub's layout. -/
theorem abi_memRel (tab : Tab) (hok : abiTabOk tab = true) (b pb : ByteArray) (dm : MachineData)
    (ra : Word) (hc : AbiCall b pb dm ra) (hneed : abiNeed tab ≤ dm.regs.r9.toNat) :
    MemRel (abiLayout tab dm.regs.r8.toNat dm.regs.rdi.toNat b.size dm.regs.rdx.toNat pb.size)
      (loadMem b pb [] (List.replicate tab.nw abiWords))
      (stores dm.regs dm.regs.r8.toNat dm.dmem 0 (abiVals tab)) := by
  obtain ⟨hnb, htab, hneed64⟩ := abiTabOk_spec hok
  have hL := abiVals_length tab hnb
  have hfits := hc.hfits
  have hneed' := hneed
  simp only [abiNeed, hnb, abiSlot] at hneed'
  generalize hbase : dm.regs.r8.toNat = base at *
  have hend : base + 8 * (abiVals tab).length ≤ 2 ^ 64 := by rw [hL]; omega
  have honly := stores_only dm.regs base (abiVals tab) dm.dmem 0 (by simpa using hend)
  simp only [Nat.add_zero] at honly
  obtain ⟨g0, g1, g2, g3, g4, g5, gw, grom⟩ := abiVals_getElem? tab hnb
  have hW : ∀ i v, (abiVals tab)[i]? = some v →
      rdW (stores dm.regs base dm.dmem 0 (abiVals tab)) (A (base + 8 * i)) = some (UInt64.ofBitVec (v.val dm.regs)) :=
    fun i v hv => stores_rdW? dm.regs base _ _ i v hv hend
  -- bytes past the stores are the region's zeros
  have hz : ∀ x, base + 8 * (abiVals tab).length ≤ x → x < base + dm.regs.r9.toNat →
      (stores dm.regs base dm.dmem 0 (abiVals tab)).get? (A x) = some 0 := by
    intro x h1 h2
    rw [honly.same x (by omega) (by omega)]
    exact hc.hzero x (by omega) (by omega)
  have hmapped : ∀ x, base ≤ x → x < base + dm.regs.r9.toNat →
      ((stores dm.regs base dm.dmem 0 (abiVals tab)).get? (A x)).isSome := by
    intro x h1 h2
    exact honly.grows _ (by rw [hc.hzero x (by omega) (by omega)]; rfl)
  have h2 : ∀ a, a < 2 → a = 0 ∨ a = 1 := by omega
  constructor
  · simp [loadMem, hnb]
  · simp [loadMem]
  · intro a ha; simp only [abiLayout_tab, hnb] at ha
    rcases h2 a ha with rfl | rfl <;> simp [loadMem, Mem.arr8]
  · intro a ha; simp only [abiLayout_tab] at ha; simp [loadMem, Mem.arr64, ha]
  · intro a ha i hi
    simp only [abiLayout_tab, hnb] at ha
    rcases h2 a ha with rfl | rfl
    · have hi' : i < b.size := by simpa [loadMem, Mem.arr8] using hi
      simp only [abiLayout_b8_0]
      rw [honly.same _ (by have := hc.hinEnd; omega)
        (by rcases hc.hinDisj (dm.regs.rdi.toNat + i) (by omega) (by omega) with h | h <;> omega),
        hc.hin i hi']
      simp [loadMem, Mem.arr8]; rfl
    · have hi' : i < pb.size := by simpa [loadMem, Mem.arr8] using hi
      simp only [abiLayout_b8_1]
      rw [honly.same _ (by have := hc.hpinsEnd; omega)
        (by rcases hc.hpinsDisj (dm.regs.rdx.toNat + i) (by omega) (by omega) with h | h <;> omega),
        hc.hpins i hi']
      simp [loadMem, Mem.arr8]; rfl
  · intro a ha i hi
    simp only [abiLayout_tab] at ha
    simp only [loadMem, Mem.arr64, abiLayout_b64] at hi ⊢
    simp [ha] at hi ⊢
    simp only [abiSlot64, hnb, abiSlot, abiWords] at hi ⊢
    have hle : 2 ^ 35 * (2 + (2 - 2) + a) + 2 ^ 35 ≤ 2 ^ 35 * (2 + tab.nw) :=
      by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
    refine rdW_of_zero (by omega) fun j hj => hz _ ?_ (by omega)
    rw [hL]; omega
  · have := hW 1 _ g1
    rw [addr_val _ _ (by rw [hbase]; simp only [abiSlot]; omega), hbase] at this
    simpa only [abiLayout_T, abiLayout_lo] using this
  · intro a ha
    simp only [abiLayout_tab, hnb] at ha
    rcases h2 a ha with rfl | rfl
    · have := hW 2 _ g2
      simp only [SVal.val, Reg64s.get64_rdi, UInt64.ofBitVec_toBitVec] at this
      simpa [Tab.base8] using this
    · have := hW 4 _ g4
      simp only [SVal.val, Reg64s.get64_rdx, UInt64.ofBitVec_toBitVec] at this
      simpa [Tab.base8] using this
  · intro a ha
    simp only [abiLayout_tab, hnb] at ha
    rcases h2 a ha with rfl | rfl
    · have := hW 3 _ g3
      simp only [SVal.val, Reg64s.get64_rsi, UInt64.ofBitVec_toBitVec] at this
      simpa [Tab.len8, ← hc.hn] using this
    · have := hW 5 _ g5
      simp only [SVal.val, Reg64s.get64_rcx, UInt64.ofBitVec_toBitVec] at this
      simpa [Tab.len8, ← hc.hnp] using this
  · intro a ha
    simp only [abiLayout_tab] at ha
    have := hW (6 + tab.wpos a) _ (gw a ha).1
    rw [addr_val _ _ (by simp only [abiSlot64, hnb, abiSlot] at hneed' ⊢; rw [hbase]; omega), hbase] at this
    simp only [abiLayout_T, abiLayout_tab, abiLayout_b64, Tab.base64, hnb]
    rw [show (16 + 16 * ((2 : Nat) : Int) + 8 * (tab.wpos a : Int)).toNat = 8 * (6 + tab.wpos a) by omega]
    exact this
  · intro a ha
    simp only [abiLayout_tab] at ha
    have := hW (6 + tab.nw + tab.wpos a) _ (gw a ha).2
    simp only [SVal.val, UInt64.ofBitVec_toBitVec] at this
    simp only [abiLayout_T, abiLayout_tab, abiLayout_s64, Tab.len64, hnb]
    rw [show (16 + 16 * ((2 : Nat) : Int) + 8 * (tab.nw : Int) + 8 * (tab.wpos a : Int)).toNat =
      8 * (6 + tab.nw + tab.wpos a) by omega]
    exact this
  · intro i hi
    simp only [abiLayout_T, abiLayout_tab, hnb]
    obtain ⟨w, hw1, hw2⟩ := romVals_byte tab.rom i hi
    have hv : (abiVals tab)[6 + 2 * tab.nw + i / 8]? = some (.imm w) := by rw [grom]; exact hw1
    obtain ⟨hlt, hv'⟩ := List.getElem?_eq_some_iff.mp hv
    have := stores_byte dm.regs base (abiVals tab) dm.dmem 0 (6 + 2 * tab.nw + i / 8) (i % 8) hlt
      (Nat.mod_lt _ (by omega)) (by simpa using hend)
    rw [hv'] at this
    simp only [SVal.val, UInt64.ofBitVec_toBitVec, hw2] at this
    rw [show base + 16 + 16 * (2 + tab.nw) + i = base + 0 + 8 * (6 + 2 * tab.nw + i / 8) + i % 8 by omega]
    exact this
  · intro x ⟨h1, h2'⟩
    simp only [abiLayout_lo, abiLayout_hi, abiSlot, abiStack] at h1 h2'
    exact hmapped x (by omega) (by omega)
  · intro x ⟨h1, h2'⟩
    simp only [abiLayout_T, abiLayout_tab] at h1 h2'
    exact hmapped x (by omega) (by simp only [Tab.nxres] at *; omega)
  · intro g hg
    simp only [abiLayout_tab] at hg
    simp only [loadMem, Layout.globAddr, Layout.globStart, abiLayout_T, abiLayout_tab]
    refine rdW_of_zero (by omega) fun j hj => hz _ ?_ (by omega)
    rw [hL]; simp only [hnb]; omega

theorem abiCall_geom {tab : Tab} {b pb : ByteArray} {dm : MachineData} {ra : Word}
    (hc : AbiCall b pb dm ra) (hneed : abiNeed tab ≤ dm.regs.r9.toNat) :
    AbiGeom tab dm.regs.r8.toNat dm.regs.r9.toNat dm.regs.rdi.toNat b.size dm.regs.rdx.toNat pb.size :=
  ⟨hneed, hc.hfits, hc.hinEnd, hc.hpinsEnd, hc.hinDisj, hc.hpinsDisj, hc.hbufDisj⟩

/-- **The trampoline's premises after the stub** (`HarnessCall` at the partition layout), and the
caller's registers back from the state after the stub's: the stub ran on a memory `d` that
differs from the caller's only inside the region (`ca_start_a`, `ca_start_a0`: the mode word
written). -/
theorem abi_harness {tab : Tab} (hok : abiTabOk tab = true) {b pb : ByteArray} {dm : MachineData}
    {ra : Word} (hc : AbiCall b pb dm ra) (hneed : abiNeed tab ≤ dm.regs.r9.toNat) (d : DataMem)
    (hd : Only dm.regs.r8.toNat (dm.regs.r8.toNat + dm.regs.r9.toNat) dm.dmem d) (s1 : MachineData)
    (hs1 : s1.dmem = stores dm.regs dm.regs.r8.toNat d 0 (abiVals tab))
    (hrdi : s1.regs.rdi = dm.regs.r8) (hrsi : s1.regs.rsi.toNat = abiFuel)
    (hregs : ∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → s1.regs.get64 r = dm.regs.get64 r) :
    HarnessCall (abiLayout tab dm.regs.r8.toNat dm.regs.rdi.toNat b.size dm.regs.rdx.toNat pb.size)
      abiFuel s1 ra ∧ ∀ r, RegsRestored s1.regs r → RegsRestored dm.regs r := by
  obtain ⟨hnb, htab, hneed64⟩ := abiTabOk_spec hok
  have hL := abiVals_length tab hnb
  have hfits := hc.hfits
  have hneed' := hneed
  simp only [abiNeed, hnb, abiSlot] at hneed'
  have hend : dm.regs.r8.toNat + 8 * (abiVals tab).length ≤ 2 ^ 64 := by rw [hL]; omega
  have honly : Only dm.regs.r8.toNat (dm.regs.r8.toNat + dm.regs.r9.toNat) dm.dmem s1.dmem := by
    rw [hs1]
    exact hd.union (stores_only dm.regs dm.regs.r8.toNat (abiVals tab) d 0 (by simpa using hend))
      (by omega) (by omega) (by omega) (by rw [hL] at hend ⊢; simp only [Nat.add_zero]; omega)
  have hsp : s1.regs.rsp = dm.regs.rsp := by
    have := hregs .rsp (by decide) (by decide) (by decide)
    exact UInt64.toBitVec_inj.mp (by simpa using this)
  have hcs := hc.hcs
  refine ⟨?_, ?_⟩
  · constructor
    · rw [hrdi]; rfl
    · exact hrsi
    · simp only [abiLayout_lo, abiLayout_hi, abiSlot, abiStack]; omega
    · have := stores_rdW? dm.regs dm.regs.r8.toNat (abiVals tab) d 0 _ (abiVals_getElem? tab hnb).1 hend
      rw [addr_val _ _ (by simp only [abiSlot, abiStack]; omega)] at this
      rw [← hs1] at this
      simp only [abiLayout_T, abiLayout_hi]
      simpa only [Nat.mul_zero, Nat.add_zero, Nat.add_assoc] using this
    · rw [hsp, ← hc.hra]
      refine rdW_congr fun j hj => ?_
      rw [A_add, honly.same _ (by have := hc.hcs8; omega) ?_]
      rcases (hcs (dm.regs.rsp.toNat + j) (by omega) (by have := hc.hcs8; omega)).2.1 with h | h
      · omega
      · omega
    · intro x h1 h2
      rw [hsp] at h1 h2
      obtain ⟨hm, hreg, hin, hpins⟩ := hcs x h1 h2
      refine ⟨honly.grows _ hm, ?_, ?_, ?_⟩
      · intro ⟨h3, h4⟩
        simp only [abiLayout_lo, abiLayout_hi, abiSlot, abiStack] at h3 h4; omega
      · rintro (⟨a, ha, h3, h4⟩ | ⟨a, ha, h3, h4⟩)
        · simp only [abiLayout_tab, hnb] at ha
          have : a = 0 ∨ a = 1 := by omega
          rcases this with rfl | rfl
          · simp only [abiLayout_b8_0, abiLayout_s8_0] at h3 h4; exact hin ⟨h3, h4⟩
          · simp only [abiLayout_b8_1, abiLayout_s8_1] at h3 h4; exact hpins ⟨h3, h4⟩
        · simp only [abiLayout_tab] at ha
          simp only [abiLayout_b64, abiLayout_s64, abiSlot64, hnb, abiSlot, abiWords] at h3 h4
          have hle : 2 ^ 35 * (2 + (2 - 2) + a) + 2 ^ 35 ≤ 2 ^ 35 * (2 + tab.nw) :=
            by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
          omega
      · intro ⟨h3, h4⟩
        simp only [Layout.tabEnd, abiLayout_T, abiLayout_tab, abiLayout_nargs] at h3 h4; omega
    · rw [hsp]; exact hc.hcs24
    · rw [hsp]; exact hc.hcs8
    · intro x h1 h2
      simp only [Layout.tabEnd, abiLayout_T, abiLayout_tab, abiLayout_nargs] at h1 h2
      refine ⟨honly.grows _ (by rw [hc.hzero x (by omega) (by omega)]; rfl), ?_, ?_, ?_⟩
      · intro ⟨h3, h4⟩
        simp only [abiLayout_lo, abiLayout_hi, abiSlot, abiStack] at h3 h4; omega
      · rintro (⟨a, ha, h3, h4⟩ | ⟨a, ha, h3, h4⟩)
        · simp only [abiLayout_tab, hnb] at ha
          have : a = 0 ∨ a = 1 := by omega
          rcases this with rfl | rfl
          · simp only [abiLayout_b8_0, abiLayout_s8_0] at h3 h4
            rcases hc.hinDisj x h3 h4 with h | h <;> omega
          · simp only [abiLayout_b8_1, abiLayout_s8_1] at h3 h4
            rcases hc.hpinsDisj x h3 h4 with h | h <;> omega
        · simp only [abiLayout_tab] at ha
          simp only [abiLayout_b64, abiLayout_s64, abiSlot64, hnb, abiSlot, abiWords] at h3 h4
          omega
      · rw [hsp]
        refine Classical.byContradiction fun hn => ?_
        simp only [not_or, Nat.not_lt, Nat.not_le] at hn
        rcases (hcs x (by omega) (by omega)).2.1 with h | h <;> omega
    · simp only [Layout.tabEnd, abiLayout_T, abiLayout_tab, abiLayout_nargs]; omega
  · have hkeep : ∀ q : Reg64, q ≠ .rax → q ≠ .rdi → q ≠ .rsi →
        (s1.regs.get64 q = dm.regs.get64 q) := hregs
    rintro r ⟨h1, h2, h3, h4, h5, h6, h7⟩
    refine ⟨by rw [h1, hsp], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h2]; exact UInt64.toBitVec_inj.mp (by simpa using hkeep .rbp (by decide) (by decide) (by decide))
    · rw [h3]; exact UInt64.toBitVec_inj.mp (by simpa using hkeep .r14 (by decide) (by decide) (by decide))
    · rw [h4]; exact UInt64.toBitVec_inj.mp (by simpa using hkeep .r15 (by decide) (by decide) (by decide))
    · rw [h5]; exact UInt64.toBitVec_inj.mp (by simpa using hkeep .rbx (by decide) (by decide) (by decide))
    · rw [h6]; exact UInt64.toBitVec_inj.mp (by simpa using hkeep .r12 (by decide) (by decide) (by decide))
    · rw [h7]; exact UInt64.toBitVec_inj.mp (by simpa using hkeep .r13 (by decide) (by decide) (by decide))

end ConAgua.Final
