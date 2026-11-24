module

public import ConAgua.Final.Statement
public import ConAgua.Compiler.AbiSim
import Kraken.X64.Registers

@[expose] public section

/-!
# The setup stub on the machine: `ca_setup` (called with `ca_start`'s arguments)

`AbiArgs`: how the harness calls `ca_start(in, in_len, pins, pins_len, base, base_len)`: the input
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

/-- **The input, pin and region arguments of an entry-1 call** (`AbiCall`'s facts without the
solution): System V arguments `rdi, rsi` = the input buffer and its
length, `rdx, rcx` = the pin-data buffer and its length, `r8, r9` = the region and its length;
the buffers hold `b` and `pb`; the region is zero, in the address space, and apart from both
buffers; the buffers are apart from each other; the return address is on the machine stack, whose
32 bytes around `rsp` are mapped and apart from the region and the buffers. -/
structure AbiArgs (b pb : ByteArray) (dm : MachineData) (ra : Word) : Prop where
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

/-- **`AbiArgs` on a mapped region** (not necessarily zero): how the compared run's driver calls the
setup stub again on a region that holds an L memory (`ConAgua/Final/CmpStub.lean`). -/
structure AbiCallM (b pb : ByteArray) (dm : MachineData) (ra : Word) : Prop where
  hin : ∀ i (h : i < b.size), dm.dmem.get? (A (dm.regs.rdi.toNat + i)) = some b[i]
  hn : dm.regs.rsi.toNat = b.size
  hpins : ∀ i (h : i < pb.size), dm.dmem.get? (A (dm.regs.rdx.toNat + i)) = some pb[i]
  hnp : dm.regs.rcx.toNat = pb.size
  hmap : ∀ x, dm.regs.r8.toNat ≤ x → x < dm.regs.r8.toNat + dm.regs.r9.toNat → (dm.dmem.get? (A x)).isSome
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

/-- A zero region is mapped. -/
theorem AbiArgs.toM {b pb : ByteArray} {dm : MachineData} {ra : Word} (hc : AbiArgs b pb dm ra) :
    AbiCallM b pb dm ra :=
  ⟨hc.hin, hc.hn, hc.hpins, hc.hnp, fun x h1 h2 => by rw [hc.hzero x h1 h2]; rfl, hc.hfits, hc.hinEnd,
    hc.hpinsEnd, hc.hinDisj, hc.hpinsDisj, hc.hbufDisj, hc.hra, hc.hcs, hc.hcs24, hc.hcs8⟩

/-- **The solution's address of a compared run's call**: the first stack argument, the word at
`rsp + 8` (`0` if unmapped). -/
def solAddr (dm : MachineData) : Word := (rdW dm.dmem (A (dm.regs.rsp.toNat + 8))).getD 0

/-- **The solution's stack arguments of a compared run's call** (`ca_start_ac`, `ca_start_c`,
System V's seventh and eighth arguments): the solution's buffer at `solAddr dm` (the word at
`rsp + 8`) holding `bS`, its length at `rsp + 16`; the buffer in the address space and apart from
the region, the challenge's and the pin data's buffers and the stack window; the two argument
words in the address space and apart from the region. -/
structure SolArgs (b bS pb : ByteArray) (dm : MachineData) : Prop where
  hsa : rdW dm.dmem (A (dm.regs.rsp.toNat + 8)) = some (solAddr dm)
  hsn : rdW dm.dmem (A (dm.regs.rsp.toNat + 16)) = some (UInt64.ofNat bS.size)
  hS : ∀ i (h : i < bS.size), dm.dmem.get? (A ((solAddr dm).toNat + i)) = some bS[i]
  hSEnd : (solAddr dm).toNat + bS.size < 2 ^ 64
  hSDisj : ∀ x, (solAddr dm).toNat ≤ x → x < (solAddr dm).toNat + bS.size →
    (x < dm.regs.r8.toNat ∨ dm.regs.r8.toNat + dm.regs.r9.toNat ≤ x) ∧
    ¬ (dm.regs.rdi.toNat ≤ x ∧ x < dm.regs.rdi.toNat + b.size) ∧
    ¬ (dm.regs.rdx.toNat ≤ x ∧ x < dm.regs.rdx.toNat + pb.size) ∧
    (x < dm.regs.rsp.toNat - 24 ∨ dm.regs.rsp.toNat + 8 ≤ x)
  hsEnd : dm.regs.rsp.toNat + 24 < 2 ^ 64
  hsArgs : ∀ x, dm.regs.rsp.toNat + 8 ≤ x → x < dm.regs.rsp.toNat + 24 →
    x < dm.regs.r8.toNat ∨ dm.regs.r8.toNat + dm.regs.r9.toNat ≤ x

/-- **How the harness calls entry 1** (`ca_start`, `ca_start_a`; with a solution `sol = some bS`,
a compared run's `ca_start_c`, `ca_start_ac`): System V arguments `rdi, rsi` = the input buffer
(the challenge's, in a compared run) and its length, `rdx, rcx` = the pin-data buffer and its
length, `r8, r9` = the region and its length; the buffers hold `b` and `pb`; the region is zero,
in the address space, and apart from both buffers; the buffers are apart from each other; the
return address is on the machine stack, whose 32 bytes around `rsp` are mapped and apart from the
region and the buffers (`AbiArgs`); with a solution, its buffer and length as the stack arguments
(`SolArgs`). -/
structure AbiCall (b : ByteArray) (sol : Option ByteArray) (pb : ByteArray) (dm : MachineData) (ra : Word) : Prop
    extends AbiArgs b pb dm ra where
  hsol : ∀ bS, sol = some bS → SolArgs b bS pb dm

/-- A word of zero bytes reads as `0`. -/
theorem rdW_of_zero {d : DataMem} {x : Nat} (_hx : x + 8 ≤ 2 ^ 64)
    (h : ∀ j < 8, d.get? (A (x + j)) = some 0) : rdW d (A x) = some 0 := by
  have : rdW d (A x) = rdW (wrW d (A x) 0) (A x) := by
    refine rdW_congr fun j hj => ?_
    rw [A_add, get?_wrW_byte hj, h j hj]
    have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [this, rdW_wrW_same]; rfl

/-- **The ABI's fixed positions**, a fact about the layout map that only the stub proofs use: the
table's byte arrays are the input `IN` at descriptor position `0` and the pin data `Rom.PB` at
position `1`, where the stub puts the caller's two buffers. -/
def abiIO (tab : Tab) : Bool :=
  tab.dom8 IN && tab.pos8 IN == 0 && tab.dom8 Rom.PB && tab.pos8 Rom.PB == 1

/-- A byte array of a two-byte-array table with `abiIO` is the input (position `0`) or the pin
data (position `1`). -/
theorem abiIO_cases {tab : Tab} (hio : abiIO tab = true) (hnb : tab.nb = 2) {a : ArrId} (ha : tab.dom8 a = true) :
    (a = IN ∧ tab.pos8 a = 0) ∨ (a = Rom.PB ∧ tab.pos8 a = 1) := by
  simp only [abiIO, Bool.and_eq_true, beq_iff_eq] at hio
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hio
  have := tab.pos8_lt ha
  rcases (by omega : tab.pos8 a = 0 ∨ tab.pos8 a = 1) with e | e
  · refine .inl ⟨Classical.byContradiction fun hne => tab.pos8_ne ha h1 hne (by rw [e, h2]), e⟩
  · refine .inr ⟨Classical.byContradiction fun hne => tab.pos8_ne ha h3 hne (by rw [e, h4]), e⟩

/-- The memory the stub leaves: L's initial memory (`loadMem` with the input bytes, the pin data
and every word array zeros of the length `abiSz` gives it) in the stub's layout. -/
theorem abi_memRel (tab : Tab) (hok : abiTabOk tab = true) (hio : abiIO tab = true) (b pb : ByteArray)
    (dm : MachineData) (ra : Word) (hc : AbiArgs b pb dm ra) (hneed : abiNeed tab ≤ dm.regs.r9.toNat) :
    MemRel (abiLayout tab dm.regs.r8.toNat dm.regs.rdi.toNat b.size dm.regs.rdx.toNat pb.size)
      (loadMem b pb (abiSz tab))
      (stores dm.regs dm.regs.r8.toNat dm.dmem 0 (abiVals tab)) := by
  obtain ⟨hnb, htab, hneed64⟩ := abiTabOk_spec hok
  have hL := abiVals_length tab
  have hfits := hc.hfits
  have hneed' := hneed
  have hns := two_le_nslot hok
  have hslot := Nat.mul_le_mul_left abiSlot hns
  have habi : abiSlot = 2 ^ 35 := rfl
  simp only [abiNeed] at hneed'
  generalize hbase : dm.regs.r8.toNat = base at *
  have hend : base + 8 * (abiVals tab).length ≤ 2 ^ 64 := by rw [hL]; simp only [abiSlot] at *; omega
  have honly := stores_only dm.regs base (abiVals tab) dm.dmem 0 (by simpa using hend)
  simp only [Nat.add_zero] at honly
  obtain ⟨g0, g1, gw, grom⟩ := abiVals_getElem? tab
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
  -- a word position's base
  have hoff : ∀ p, 2 ≤ p → p < tab.nb + tab.nw → abiOff tab p + abiSlot ≤ dm.regs.r9.toNat := by
    intro p hp2 hp
    cases hcc : tab.tbl64 (tab.wAt p) with
    | none =>
      rw [abiOff_slot hcc, Tab.slotOf_eq hnb]
      have := slot_lt_nslot hok hnb hp hcc
      have : abiSlot * p + abiSlot ≤ abiSlot * tab.nslot := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ this
      omega
    | some c => rw [abiOff_tbl hcc]; have := abiTabOk_tbl hok hcc; simp only [abiSlot] at *; omega
  have hnbuf : tab.nbuf = 2 := by simp [Tab.nbuf, hnb]
  constructor
  · intro a ha
    simp only [abiLayout_tab] at ha ⊢
    rcases abiIO_cases hio hnb ha with ⟨rfl, e⟩ | ⟨rfl, e⟩ <;> rw [e] <;> simp [loadMem, Mem.arr8, IN, Rom.PB, abiLayout]
  · intro s hs
    have := tab.pos64_lt hs
    simp only [abiLayout_tab] at hs ⊢
    rw [abiLayout_s64 _ _ _ _ _ _ (by omega)]
    simp [loadMem, Mem.arr64, tab.wAt_pos64 hs]
  · intro a ha i hi
    simp only [abiLayout_tab] at ha ⊢
    rcases abiIO_cases hio hnb ha with ⟨rfl, e⟩ | ⟨rfl, e⟩ <;> rw [e]
    · have hi' : i < b.size := by simpa [loadMem, Mem.arr8, IN] using hi
      simp only [abiLayout_b8_0]
      rw [honly.same _ (by have := hc.hinEnd; omega)
        (by rcases hc.hinDisj (dm.regs.rdi.toNat + i) (by omega) (by omega) with h | h <;> omega),
        hc.hin i hi']
      simp [loadMem, Mem.arr8, IN]; rfl
    · have hi' : i < pb.size := by simpa [loadMem, Mem.arr8, IN, Rom.PB] using hi
      simp only [abiLayout_b8_1]
      rw [honly.same _ (by have := hc.hpinsEnd; omega)
        (by rcases hc.hpinsDisj (dm.regs.rdx.toNat + i) (by omega) (by omega) with h | h <;> omega),
        hc.hpins i hi']
      simp [loadMem, Mem.arr8, IN, Rom.PB]; rfl
  · intro s ha i hi
    simp only [abiLayout_tab] at ha ⊢
    have hp := tab.pos64_lt ha
    have hi' : i < abiSz tab (tab.wAt (tab.pos64 s)) := by
      rw [tab.wAt_pos64 ha]; simpa [loadMem, Mem.arr64] using hi
    simp only [loadMem, Mem.arr64, Array.getElem_replicate]
    have hb := fun j (hj : j < 8) => abiLayout_in64_bounds (inp := dm.regs.rdi.toNat) (n := b.size)
      (pins := dm.regs.rdx.toNat) (np := pb.size) (base := base) hok (by omega) hp.2
      (x := base + abiOff tab (tab.pos64 s) + 8 * i + j)
      ⟨by rw [abiLayout_b64 _ _ _ _ _ _ (by omega)]; omega,
       by rw [abiLayout_b64 _ _ _ _ _ _ (by omega), abiLayout_s64 _ _ _ _ _ _ (by omega)]; omega⟩
    have hb0 := hb 0 (by omega); have hb7 := hb 7 (by omega)
    rw [abiLayout_b64 _ _ _ _ _ _ (by omega)]
    refine rdW_of_zero (by simp only [abiNeed] at hb7; omega) fun j hj => hz _ ?_ ?_
    · rw [hL]; simp only [Tab.romWords] at hb0 ⊢; omega
    · have := hb j hj; simp only [abiNeed] at this; omega
  · have := hW 1 _ g1
    rw [addr_val _ _ (by rw [hbase]; simp only [abiSlot] at *; omega), hbase] at this
    simpa only [abiLayout_T, abiLayout_lo] using this
  · intro p hp
    simp only [abiLayout_tab] at hp
    have := hW (2 + p) _ (gw p hp).1
    simp only [abiLayout_T, Tab.dbase]
    rw [show (16 + 8 * (p : Int)).toNat = 8 * (2 + p) by omega]
    rcases (by omega : p = 0 ∨ p = 1 ∨ 2 ≤ p) with rfl | rfl | h2
    · simpa [abiBase, hnbuf, SVal.val] using this
    · simpa [abiBase, hnbuf, SVal.val] using this
    · simp only [abiBase, hnbuf, show ¬ p < 2 by omega, hnb, ite_false] at this
      rw [addr_val _ _ (by rw [hbase]; have := hoff p h2 hp; simp only [abiSlot] at *; omega), hbase] at this
      rw [abiLayout_b64 _ _ _ _ _ _ h2]; exact this
  · intro p hp
    simp only [abiLayout_tab] at hp
    have := hW (2 + (tab.nb + tab.nw) + p) _ (gw p hp).2.1
    simp only [abiLayout_T, abiLayout_tab, Tab.dlen]
    rw [show (16 + 8 * ((tab.nb : Int) + (tab.nw : Int)) + 8 * (p : Int)).toNat =
      8 * (2 + (tab.nb + tab.nw) + p) by omega]
    rcases (by omega : p = 0 ∨ p = 1 ∨ 2 ≤ p) with rfl | rfl | h2
    · simpa [abiLen, hnbuf, SVal.val, ← hc.hn] using this
    · simpa [abiLen, hnbuf, SVal.val, ← hc.hnp] using this
    · simp only [abiLen, hnbuf, show ¬ p < 2 by omega, hnb, ite_false, SVal.val] at this
      rw [abiLayout_s64 _ _ _ _ _ _ h2]; simpa [hnb] using this
  · intro p hp1 hp
    simp only [abiLayout_tab] at hp hp1
    have := hW (2 + 2 * (tab.nb + tab.nw) + p) _ (gw p hp).2.2
    simp only [abiLayout_T, abiLayout_tab, Tab.dlen32]
    rw [show (16 + 16 * ((tab.nb : Int) + (tab.nw : Int)) + 8 * (p : Int)).toNat =
      8 * (2 + 2 * (tab.nb + tab.nw) + p) by omega]
    simp only [abiLen32, show ¬ p < tab.nb by omega, ite_false, SVal.val] at this
    rw [abiLayout_s64 _ _ _ _ _ _ (by omega)]; simpa [hnb] using this
  · intro i hi
    simp only [abiLayout_T, abiLayout_tab]
    obtain ⟨w, hw1, hw2⟩ := romVals_byte tab.rom i hi
    have hv : (abiVals tab)[2 + 3 * (tab.nb + tab.nw) + i / 8]? = some (.imm w) := by rw [grom]; exact hw1
    obtain ⟨hlt, hv'⟩ := List.getElem?_eq_some_iff.mp hv
    have := stores_byte dm.regs base (abiVals tab) dm.dmem 0 (2 + 3 * (tab.nb + tab.nw) + i / 8) (i % 8) hlt
      (Nat.mod_lt _ (by omega)) (by simpa using hend)
    rw [hv'] at this
    simp only [SVal.val, UInt64.ofBitVec_toBitVec, hw2] at this
    rw [show base + 16 + 24 * (tab.nb + tab.nw) + i = base + 0 + 8 * (2 + 3 * (tab.nb + tab.nw) + i / 8) + i % 8 by omega]
    exact this
  · intro x ⟨h1, h2'⟩
    simp only [abiLayout_lo, abiLayout_hi, abiSlot, abiStack] at h1 h2'
    exact hmapped x (by omega) (by simp only [abiSlot] at *; omega)
  · intro x ⟨h1, h2'⟩
    simp only [abiLayout_T, abiLayout_tab] at h1 h2'
    exact hmapped x (by omega) (by simp only [Tab.nxres, abiSlot] at *; omega)
  · intro g hg
    simp only [abiLayout_tab] at hg
    simp only [loadMem, Layout.globAddr, Layout.globStart, abiLayout_T, abiLayout_tab]
    refine rdW_of_zero (by simp only [abiSlot] at *; omega) fun j hj => hz _ ?_ (by simp only [abiSlot] at *; omega)
    rw [hL]; omega

theorem abiCall_geom {tab : Tab} {b pb : ByteArray} {dm : MachineData} {ra : Word}
    (hc : AbiArgs b pb dm ra) (hneed : abiNeed tab ≤ dm.regs.r9.toNat) :
    AbiGeom tab dm.regs.r8.toNat dm.regs.r9.toNat dm.regs.rdi.toNat b.size dm.regs.rdx.toNat pb.size :=
  ⟨hneed, hc.hfits, hc.hinEnd, hc.hpinsEnd, hc.hinDisj, hc.hpinsDisj, hc.hbufDisj⟩

theorem AbiCallM.geom {tab : Tab} {b pb : ByteArray} {dm : MachineData} {ra : Word}
    (hc : AbiCallM b pb dm ra) (hneed : abiNeed tab ≤ dm.regs.r9.toNat) :
    AbiGeom tab dm.regs.r8.toNat dm.regs.r9.toNat dm.regs.rdi.toNat b.size dm.regs.rdx.toNat pb.size :=
  ⟨hneed, hc.hfits, hc.hinEnd, hc.hpinsEnd, hc.hinDisj, hc.hpinsDisj, hc.hbufDisj⟩

/-- **The trampoline's premises after the stub** (`HarnessCall` at the partition layout), and the
caller's registers back from the state after the stub's: the stub ran on a memory `d` that
differs from the caller's only inside the region (`ca_start_a`, `ca_start_a0`: the mode word
written). -/
theorem abi_harness {tab : Tab} (hok : abiTabOk tab = true) {b pb : ByteArray} {dm : MachineData}
    {ra : Word} (hc : AbiCallM b pb dm ra) (hneed : abiNeed tab ≤ dm.regs.r9.toNat) (d : DataMem)
    (hd : Only dm.regs.r8.toNat (dm.regs.r8.toNat + dm.regs.r9.toNat) dm.dmem d) (s1 : MachineData)
    (hs1 : s1.dmem = stores dm.regs dm.regs.r8.toNat d 0 (abiVals tab))
    (hrdi : s1.regs.rdi = dm.regs.r8) (hrsi : s1.regs.rsi.toNat = abiFuelM)
    (hregs : ∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → s1.regs.get64 r = dm.regs.get64 r) :
    HarnessCall (abiLayout tab dm.regs.r8.toNat dm.regs.rdi.toNat b.size dm.regs.rdx.toNat pb.size)
      abiFuelM s1 ra ∧ ∀ r, RegsRestored s1.regs r → RegsRestored dm.regs r := by
  obtain ⟨hnb, htab, hneed64⟩ := abiTabOk_spec hok
  have hL := abiVals_length tab
  have hfits := hc.hfits
  have hneed' := hneed
  have hslot := Nat.mul_le_mul_left abiSlot (two_le_nslot hok)
  have habi : abiSlot = 2 ^ 35 := rfl
  simp only [abiNeed] at hneed'
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
    · have := stores_rdW? dm.regs dm.regs.r8.toNat (abiVals tab) d 0 _ (abiVals_getElem? tab).1 hend
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
      · rintro ⟨p, hp, hx⟩
        simp only [abiLayout_tab] at hp
        rcases abiLayout_in hok hp hx with ⟨-, h3, h4⟩ | ⟨-, h3, h4⟩ | ⟨h2, -⟩
        · exact hin ⟨h3, h4⟩
        · exact hpins ⟨h3, h4⟩
        · have := abiLayout_in64_bounds hok h2 hp (Layout.In.to64 (by simp [hnb]; omega) hx)
          simp only [abiNeed] at this; omega
      · intro ⟨h3, h4⟩
        simp only [Layout.tabEnd, abiLayout_T, abiLayout_tab, abiLayout_nargs] at h3 h4; omega
    · rw [hsp]; exact hc.hcs24
    · rw [hsp]; exact hc.hcs8
    · intro x h1 h2
      simp only [Layout.tabEnd, abiLayout_T, abiLayout_tab, abiLayout_nargs] at h1 h2
      refine ⟨honly.grows _ (hc.hmap x (by omega) (by omega)), ?_, ?_, ?_⟩
      · intro ⟨h3, h4⟩
        simp only [abiLayout_lo, abiLayout_hi, abiSlot, abiStack] at h3 h4; omega
      · rintro ⟨p, hp, hx⟩
        simp only [abiLayout_tab] at hp
        rcases abiLayout_in hok hp hx with ⟨-, h3, h4⟩ | ⟨-, h3, h4⟩ | ⟨h2, -⟩
        · rcases hc.hinDisj x h3 h4 with h | h <;> omega
        · rcases hc.hpinsDisj x h3 h4 with h | h <;> omega
        · have := abiLayout_in64_bounds hok h2 hp (Layout.In.to64 (by simp [hnb]; omega) hx)
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
