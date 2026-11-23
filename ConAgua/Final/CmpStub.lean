module

public import ConAgua.Final.ParAbi
import Kraken.X64.Registers

@[expose] public section

/-!
# The setup stub again, on a region that holds an L memory (lane compare)

The compared run's driver `ca_compare` (`ConAgua/Compiler/AbiCmp.lean`) runs `check` three times on
the same region `R` (modes `4`, `5`, `6`), each time through the setup stub `ca_setup` with the mode
word set first (`ca_start_a4`, `ca_start_a5`, `ca_start_a6`). From the second run on, `R` is not
zero but holds the L memory the run before left (`MemRel` in the stub's layout, `abiLayout`). The
stub writes the table again: every word as before but the input's descriptor (now the buffer in
`rdi`, `rsi`); everything else in `R` stays. So the next run starts from the previous run's memory
with the input replaced (`cmpIn`) and the mode word set (`memRel_restub`, `abiModeM_outcome`).
-/

namespace ConAgua.Final

open L L.Compiler

/-- The L memory `m` with the input `IN` replaced by the bytes `bs`. -/
def cmpIn (m : Mem) (bs : ByteArray) : Mem :=
  { m with bytes := fun a => if a = IN then bs.data else m.bytes a }

/-- Replacing the input by itself changes nothing. -/
theorem cmpIn_self (m : Mem) : cmpIn m ⟨m.arr8 IN⟩ = m := by
  cases m with
  | mk bytes words glob =>
    simp only [cmpIn, Mem.arr8, Mem.mk.injEq, and_true]
    funext a
    by_cases h : a = IN
    · subst h; simp
    · simp [h]

theorem cmpIn_arr64 (m : Mem) (bs : ByteArray) (s : TieredArray) : (cmpIn m bs).arr64 s = m.arr64 s := rfl
theorem cmpIn_glob (m : Mem) (bs : ByteArray) : (cmpIn m bs).glob = m.glob := rfl
theorem cmpIn_setG (m : Mem) (bs : ByteArray) (g : GVar) (v : Word) :
    (cmpIn m bs).setG g v = cmpIn (m.setG g v) bs := rfl

/-- **The stub's stores on a region that holds `m`**: in the stub's layout for the old input
(`inp0`, `n0`) and the pin data at `rdx`, `m`; after the stores, in the layout for the new input
`bs` at `rdi`, `m` with the input replaced. -/
theorem memRel_restub (tab : Tab) (hok : abiTabOk tab = true) (hio : abiIO tab = true) (bs pb : ByteArray)
    (dm : MachineData) (ra : Word) (hc : AbiCallM bs pb dm ra) (hneed : abiNeed tab ≤ dm.regs.r9.toNat)
    {m : Mem} {inp0 n0 : Nat}
    (hm : MemRel (abiLayout tab dm.regs.r8.toNat inp0 n0 dm.regs.rdx.toNat pb.size) m dm.dmem) :
    MemRel (abiLayout tab dm.regs.r8.toNat dm.regs.rdi.toNat bs.size dm.regs.rdx.toNat pb.size)
      (cmpIn m bs) (stores dm.regs dm.regs.r8.toNat dm.dmem 0 (abiVals tab)) := by
  obtain ⟨hnb, htab, hneed64⟩ := abiTabOk_spec hok
  have hL := abiVals_length tab
  have hfits := hc.hfits
  have hneed' := hneed
  have hns := two_le_nslot hok
  have hslot := Nat.mul_le_mul_left abiSlot hns
  have habi : abiSlot = 2 ^ 35 := rfl
  simp only [abiNeed] at hneed'
  have hin := hc.hin
  have hinEnd := hc.hinEnd
  have hinDisj := hc.hinDisj
  have hpinsEnd := hc.hpinsEnd
  have hpinsDisj := hc.hpinsDisj
  generalize hbase : dm.regs.r8.toNat = base at *
  have hend : base + 8 * (abiVals tab).length ≤ 2 ^ 64 := by rw [hL]; simp only [abiSlot] at *; omega
  have honly := stores_only dm.regs base (abiVals tab) dm.dmem 0 (by simpa using hend)
  simp only [Nat.add_zero] at honly
  obtain ⟨g0, g1, gw, grom⟩ := abiVals_getElem? tab
  have hW : ∀ i v, (abiVals tab)[i]? = some v →
      rdW (stores dm.regs base dm.dmem 0 (abiVals tab)) (A (base + 8 * i)) = some (UInt64.ofBitVec (v.val dm.regs)) :=
    fun i v hv => stores_rdW? dm.regs base _ _ i v hv hend
  -- past the stores, the memory is the old one
  have hsame : ∀ x, x < 2 ^ 64 → (x < base ∨ base + 8 * (abiVals tab).length ≤ x) →
      (stores dm.regs base dm.dmem 0 (abiVals tab)).get? (A x) = dm.dmem.get? (A x) :=
    fun x hx h => honly.same x hx h
  have hnbuf : tab.nbuf = 2 := by simp [Tab.nbuf, hnb]
  have hPB : Rom.PB ≠ IN := by decide
  constructor
  · intro a ha
    simp only [abiLayout_tab] at ha ⊢
    rcases abiIO_cases hio hnb ha with ⟨rfl, e⟩ | ⟨rfl, e⟩ <;> rw [e]
    · simp [cmpIn, Mem.arr8, abiLayout]
    · have := hm.size8 Rom.PB (by simpa using ha)
      simp only [abiLayout_tab, e] at this
      simpa [cmpIn, Mem.arr8, hPB, abiLayout] using this
  · intro s hs
    have := tab.pos64_lt hs
    have h := hm.size64 s (by simpa using hs)
    simp only [abiLayout_tab] at hs h ⊢
    rw [abiLayout_s64 _ _ _ _ _ _ (by omega)] at h ⊢
    exact h
  · intro a ha i hi
    simp only [abiLayout_tab] at ha ⊢
    rcases abiIO_cases hio hnb ha with ⟨rfl, e⟩ | ⟨rfl, e⟩ <;> rw [e]
    · have hi' : i < bs.size := by simpa [cmpIn, Mem.arr8] using hi
      simp only [abiLayout_b8_0]
      rw [hsame _ (by omega) (by rcases hinDisj (dm.regs.rdi.toNat + i) (by omega) (by omega) with h | h <;> omega),
        hin i hi']
      simp [cmpIn, Mem.arr8]; rfl
    · have hi' : i < (m.arr8 Rom.PB).size := by simpa [cmpIn, Mem.arr8, hPB] using hi
      have h := hm.get8 Rom.PB (by simpa using ha) i hi'
      have hs := hm.size8 Rom.PB (by simpa using ha)
      simp only [abiLayout_tab, e, abiLayout_b8_1, abiLayout_s8_1] at h hs
      simp only [abiLayout_b8_1]
      rw [hsame _ (by omega) (by rcases hpinsDisj (dm.regs.rdx.toNat + i) (by omega) (by omega) with h | h <;> omega), h]
      simp [cmpIn, Mem.arr8, hPB]
  · intro s ha i hi
    simp only [abiLayout_tab] at ha ⊢
    have hp := tab.pos64_lt ha
    have h := hm.get64 s (by simpa using ha) i hi
    have hs := hm.size64 s (by simpa using ha)
    simp only [abiLayout_tab] at h hs
    rw [abiLayout_s64 _ _ _ _ _ _ (by omega)] at hs
    rw [abiLayout_b64 _ _ _ _ _ _ (by omega)] at h ⊢
    have hi' : i < abiSz tab (tab.wAt (tab.pos64 s)) := by rw [← hs]; exact hi
    have hb := fun j (hj : j < 8) => abiLayout_in64_bounds (inp := inp0) (n := n0)
      (pins := dm.regs.rdx.toNat) (np := pb.size) (base := base) hok (by omega) hp.2
      (x := base + abiOff tab (tab.pos64 s) + 8 * i + j)
      ⟨by rw [abiLayout_b64 _ _ _ _ _ _ (by omega)]; omega,
       by rw [abiLayout_b64 _ _ _ _ _ _ (by omega), abiLayout_s64 _ _ _ _ _ _ (by omega)]; omega⟩
    show _ = some (m.arr64 s)[i]
    rw [← h]
    refine rdW_congr fun j hj => ?_
    have := hb j hj
    rw [A_add, hsame _ (by simp only [abiNeed] at this; omega) (Or.inr (by rw [hL]; simp only [Tab.romWords] at this ⊢; omega))]
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
    · have hoff : abiOff tab p + abiSlot ≤ dm.regs.r9.toNat := by
        cases hcc : tab.tbl64 (tab.wAt p) with
        | none =>
          rw [abiOff_slot hcc, Tab.slotOf_eq hnb]
          have := slot_lt_nslot hok hnb hp hcc
          have : abiSlot * p + abiSlot ≤ abiSlot * tab.nslot := by
            rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ this
          omega
        | some c => rw [abiOff_tbl hcc]; have := abiTabOk_tbl hok hcc; simp only [abiSlot] at *; omega
      simp only [abiBase, hnbuf, show ¬ p < 2 by omega, hnb, ite_false] at this
      rw [addr_val _ _ (by rw [hbase]; simp only [abiSlot] at *; omega), hbase] at this
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
  · intro x hx
    exact honly.grows _ (hm.stack x hx)
  · intro x hx
    exact honly.grows _ (hm.res x hx)
  · intro g hg
    have h := hm.glob g hg
    simp only [abiLayout_tab] at hg
    show _ = some (m.glob g)
    rw [← h]
    refine rdW_congr fun j hj => ?_
    simp only [Layout.globAddr, Layout.globStart, abiLayout_T, abiLayout_tab] at *
    rw [A_add, hsame _ (by simp only [abiSlot] at *; omega) (Or.inr (by rw [hL]; omega))]

/-- **From a mode entry, on a region that holds an L memory** (`ca_start_a5`, `ca_start_a6`): the
seven instructions at `k` (the label, the size check, the mode store, the jump to `ca_setup`),
then the stub; on a big enough region, the run of `check` from `m` with the input replaced by the
buffer in `rdi` and the mode word `w` (or `rdx = 1`). `m` is in the stub's layout for some old
input (`inp0`, `n0`) and the pin data at `rdx` (`pb`: the pin data as `m` holds it). -/
theorem abiModeM_outcome [Host] (q p : Prog) (hq : Refines q p) (tab : Tab) (hok : abiTabOk tab = true)
    {X : AsmTab} (hAX : AsmOkT q tab X) (hio : abiIO tab = true)
    (hwf : Prog.wf tab q = true) (mode : GVar) (hng : mode.id < tab.ng) (w : Word) (lab : Label)
    (k k0 : Nat) (hl : label lab = at_ k)
    (h0 : Host.prog[k + 0]? = some (.label lab))
    (h1 : Host.prog[k + 1]? = some (movRI .rax (abiNeed tab).toUInt64))
    (h2 : Host.prog[k + 2]? = some (i64 (.cmp (.reg (rr .r9)) (oR .rax))))
    (h3 : Host.prog[k + 3]? = some (jccL .c abiSetupL))
    (h4 : Host.prog[k + 4]? = some (movRI .rax w))
    (h5 : Host.prog[k + 5]? = some (movMR (mb .r8 (tab.globOff mode)) .rax))
    (h6 : Host.prog[k + 6]? = some (jmpL abiSetupL))
    (hcR : Code (abiStub tab ++ compileProgX X tab q "check") k0)
    (fd : FunDecl) (hentry : p.lookup "check" = some fd) (hnp : fd.nparams = 0)
    (bs pb : ByteArray) (dm : MachineData) (ra : Word) (hc : AbiCallM bs pb dm ra)
    {m : Mem} {inp0 n0 : Nat}
    (hm : abiNeed tab ≤ dm.regs.r9.toNat →
      MemRel (abiLayout tab dm.regs.r8.toNat inp0 n0 dm.regs.rdx.toNat pb.size) m dm.dmem) :
    Ev (fun st => EntryPost (abiLayout tab dm.regs.r8.toNat dm.regs.rdi.toNat bs.size dm.regs.rdx.toNat pb.size)
        dm ra (L.run p abiFuel "check" [] ((cmpIn m bs).setG mode w)) st ∧
        SizesPost bs pb st)
      dm (label lab) := by
  obtain ⟨hnb, htab, hneed64⟩ := abiTabOk_spec hok
  have hfits := hc.hfits
  rw [hl]
  refine ev_label h0 ?_
  refine ev_movRI h1 ?_
  refine ev_cmpRO (r := .r9) (o := oR .rax) (v := (abiNeed tab).toUInt64) h2
    (Or.inr (Or.inr ⟨.rax, rfl, rfl⟩)) ?_
  refine ev_jcc h3 (fun hlt => ?_) (fun hge => ?_)
  · simp only [CondCode.interp, cmpFlags_cf, decide_eq_true_eq, Reg64s.get64_r9, Reg64s.set64_rax,
      UInt64.toNat_toBitVec] at hlt
    refine abi_start_outcome q p hq tab hok hAX hwf _ hcR fd hentry hnp bs pb dm ra hc _ _ ?_ (Only.refl _ _ _)
      (Only.refl _ _ _) (fun hneed => absurd hlt ?_)
    · intro r hr; cases r <;> first | exact absurd rfl hr | rfl
    · have e : (UInt64.ofNat (abiNeed tab)).toNat = abiNeed tab :=
        UInt64.toNat_ofNat_of_lt' (by simpa [UInt64.size] using hneed64)
      simp only [Nat.toUInt64] at *
      rw [e]; omega
  · simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not, Reg64s.get64_r9, Reg64s.set64_rax,
      UInt64.toNat_toBitVec, Nat.not_lt] at hge
    have hneed : abiNeed tab ≤ dm.regs.r9.toNat := by
      simpa [Nat.toUInt64, UInt64.toNat_ofNat, Nat.mod_eq_of_lt hneed64] using hge
    have hneed' := hneed
    have := abiNeed_ge hok
    have hoff : SmallOff (tab.globOff mode) := by
      simp only [Tab.globOff, Tab.globBase]; constructor <;> omega
    have hgo : (tab.globOff mode).toNat + 8 ≤ 2 ^ 35 := by
      simp only [Tab.globOff, Tab.globBase]; omega
    refine ev_movRI h4 ?_
    refine ev_movMR h5 hoff ?_ ?_
    · simp only [Reg64s.set64_rax, Reg64s.get64_r8, UInt64.toNat_toBitVec]
      exact isSome_rdW fun j hj => by rw [A_add]; exact hc.hmap _ (by omega) (by omega)
    refine ev_jmp h6 ?_
    simp only [Reg64s.set64_rax, Reg64s.get64_r8, Reg64s.get64_rax, UInt64.toNat_toBitVec]
    have hGa : dm.regs.r8.toNat + (tab.globOff mode).toNat =
        (abiLayout tab dm.regs.r8.toNat dm.regs.rdi.toNat bs.size dm.regs.rdx.toNat pb.size).globAddr mode := by
      rw [← Layout.globAddr_toNat]; rfl
    have hGe : (abiLayout tab dm.regs.r8.toNat dm.regs.rdi.toNat bs.size dm.regs.rdx.toNat pb.size).globAddr mode + 8 ≤
        (abiLayout tab dm.regs.r8.toNat dm.regs.rdi.toNat bs.size dm.regs.rdx.toNat pb.size).tabEnd := by
      simp only [Layout.globAddr, Layout.globStart, Layout.tabEnd, abiLayout_T, abiLayout_tab]; omega
    refine abi_start_outcome q p hq tab hok hAX hwf _ hcR fd hentry hnp bs pb dm ra hc _ _ ?_ ?_ ?_ (fun _ => ?_)
    · intro r hr; cases r <;> first | exact absurd rfl hr | rfl
    · rw [hGa]
      exact (Only.wrW (by simp only [Layout.tabEnd, abiLayout_T, abiLayout_tab, abiLayout_nargs] at hGe ⊢; omega)).mono
        (by simp only [Layout.globAddr, Layout.globStart, abiLayout_T]; omega) hGe
    · exact (Only.wrW (x := dm.regs.r8.toNat + (tab.globOff mode).toNat) (by omega)).mono
        (by omega) (by omega)
    · have hG := abiLayout_ok hok (hc.geom hneed)
      have hL := abiVals_length tab
      have h0 := memRel_restub tab hok hio bs pb dm ra hc hneed (hm hneed)
      have h1 := h0.storeG hG (g := mode) (by simpa [abiLayout_tab] using hng) w
      rw [← Layout.globAddr_toNat, abiLayout_T, abiLayout_tab] at h1
      refine h1.onlyD hG (a := 0) (b := 0) ⟨fun y hy => ?_, fun x hx _ => ?_⟩
        (fun x h1 h2 => by omega) (fun x h1 h2 => by omega)
      · have ey : y = A y.toNat := by simp [A]
        rw [ey] at hy ⊢
        rw [stores_wrW_get dm.regs dm.regs.r8.toNat (abiVals tab) dm.dmem _ _ (by omega)
          (by rw [hL]; omega) (Or.inr (by rw [hL]; simp only [Tab.globOff, Tab.globBase, hnb] at *; omega))
          y.toNat y.isLt]
        exact hy
      · exact stores_wrW_get dm.regs dm.regs.r8.toNat (abiVals tab) dm.dmem _ _ (by omega)
          (by rw [hL]; omega) (Or.inr (by rw [hL]; simp only [Tab.globOff, Tab.globBase, hnb] at *; omega))
          x hx

end ConAgua.Final
