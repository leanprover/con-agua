import ConAgua.Final.Statement
import ConAgua.Compiler.AbiSim

/-!
# The final theorem from the entry stub: `ca_start(in, in_len, pins, pins_len, base, base_len)`

`checker_x64_accepts_abi`: the harness calls the stub (`ConAgua/Compiler/Abi.lean`) with the input
bytes `b` at `in`, the pin data `pb` at `pins`, and a zero region `[base, base + base_len)` apart
from both buffers and from the caller's stack (`AbiCall`). The stub lays out the table, the L
stack and the word arrays inside the region (`abiLayout`; `sim_abiStub`, `abi_memRel`) and enters
the trampoline, so `checker_x64_accepts` (the theorem from `ca_enter`, which stays as the lemma
this one is built on) applies. If `base_len` is too small the stub returns `rdx = 1` at once.
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
theorem rdW_of_zero {d : DataMem} {x : Nat} (hx : x + 8 ≤ 2 ^ 64)
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
    have := hW (6 + 2 * a) _ (gw a ha).1
    rw [addr_val _ _ (by simp only [abiSlot64, hnb, abiSlot] at hneed' ⊢; rw [hbase]; omega), hbase] at this
    simp only [abiLayout_T, abiLayout_tab, abiLayout_b64, Tab.base64, hnb]
    rw [show (16 + 16 * ((2 : Nat) + a : Int)).toNat = 8 * (6 + 2 * a) by omega]
    exact this
  · intro a ha
    simp only [abiLayout_tab] at ha
    have := hW (6 + 2 * a + 1) _ (gw a ha).2
    simp only [SVal.val, UInt64.ofBitVec_toBitVec] at this
    simp only [abiLayout_T, abiLayout_tab, abiLayout_s64, Tab.len64, hnb]
    rw [show (24 + 16 * ((2 : Nat) + a : Int)).toNat = 8 * (6 + 2 * a + 1) by omega]
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

end ConAgua.Final
