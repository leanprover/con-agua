import ConAgua.Final.Abi
import ConAgua.Compiler.Main
import Kraken.X64.Registers

/-!
# The parallel mode's entry 1 on the machine (lane parmode)

`ConAgua/Compiler/Abi.lean`'s `parStub`: `ca_start_a` (mode word `1`) and `ca_start_a0` (mode word
`3`, the sequential driver's entry 1). Both write the mode word into the zero region and continue
with the setup stub `ca_setup`; they end in `compile_correct_frame` for `check`:

* `abi_start_outcome`: from `ca_setup`, on a memory `s.dmem` that differs from the caller's only
  inside the table, with `MemRel` for an L memory `m0` after the stores: the run of `check` from
  `m0` (`EntryPost`: the caller's registers back, the memory outside the layout and the
  trampoline's save areas unchanged, `rdx = 1` or `OutcomeRel`), and `SizesPost`: `rdx = 1` or
  both buffers below `2^63` bytes (the stub's length check).
* `abiMode_outcome`: the mode word `w`, then `abi_start_outcome` at the loaded memory with
  `MODE = w`; `abiA_outcome` (`ca_start_a`, `w = 1`) and `abiA0_outcome` (`ca_start_a0`, `w = 3`).
-/

namespace ConAgua.Final

open L L.Compiler

/-- **What an entry leaves**: the return to `ra` with the caller's registers (`RegsRestored`), the
memory outside the layout and the trampoline's save areas (24 bytes below `rsp`, 32 past the
table) as the caller's (`MemFrame`), and
`rdx = 1` or the outcome `res` of the L run (`OutcomeRel`). -/
def EntryPost (G : L.Compiler.Layout) (dm : MachineData) (ra : Word) (res : Except Err (List Word × Mem))
    (st : MachineState) : Prop :=
  st.pc = Int64.ofBitVec ra.toBitVec ∧ RegsRestored dm.regs st.data.regs ∧
    MemFrame G dm.regs.rsp.toNat dm.dmem st.data.dmem ∧
    (st.data.regs.rdx = 1 ∨ OutcomeRel G res st.data)

/-- **What the setup stub adds**: `rdx = 1`, or both buffers below `2^63` bytes (the stub declines
when the top bit of `in_len` or `pins_len` is set). -/
def SizesPost (b pb : ByteArray) (st : MachineState) : Prop :=
  st.data.regs.rdx = 1 ∨ (b.size < 2 ^ 63 ∧ pb.size < 2 ^ 63)

theorem stores_regs {R₁ R₂ : Reg64s} (h : ∀ r, r ≠ .rax → R₁.get64 r = R₂.get64 r) (base : Nat) :
    ∀ (vs : List SVal) (m : DataMem) (d : Nat), (∀ v ∈ vs, v.noRax) →
      stores R₁ base m d vs = stores R₂ base m d vs
  | [], _, _, _ => rfl
  | v :: vs, m, d, hno => by
    have hv : v.val R₁ = v.val R₂ := by
      have := hno v List.mem_cons_self
      cases v with
      | reg r => exact h r this
      | imm w => rfl
      | addr off => simp only [SVal.val, h .r8 (by decide)]
    simp only [stores, hv]
    exact stores_regs h base vs _ _ fun v hv => hno v (List.mem_cons_of_mem _ hv)

/-- A frame composed with a change inside the table. -/
theorem MemFrame.only_tab {G : L.Compiler.Layout} {sp : Nat} {d d' d'' : DataMem} (h : MemFrame G sp d' d'')
    (ho : Only G.T G.tabEnd d d') : MemFrame G sp d d'' :=
  ⟨fun y hy => h.grows y (ho.grows y hy), fun x hx hs ha ht hsp hsv => by
    rw [h.same x hx hs ha ht hsp hsv]
    exact ho.same x hx (by unfold Layout.InTab at ht; omega)⟩

/-- A change inside the table is a frame. -/
theorem MemFrame.of_only_tab {G : L.Compiler.Layout} {sp : Nat} {d d' : DataMem} (ho : Only G.T G.tabEnd d d') :
    MemFrame G sp d d' :=
  ⟨ho.grows, fun x hx _ _ ht _ _ => ho.same x hx (by unfold Layout.InTab at ht; omega)⟩

/-- The stub's stores are inside the table. -/
theorem abiVals_tabEnd {tab : Tab} (hok : abiTabOk tab = true) (base inp n pins np : Nat) :
    base + 8 * (abiVals tab).length ≤ (abiLayout tab base inp n pins np).tabEnd := by
  obtain ⟨hnb, -, -⟩ := abiTabOk_spec hok
  rw [abiVals_length tab hnb]
  simp only [Layout.tabEnd, abiLayout_T, abiLayout_tab, abiLayout_nargs, hnb]; omega

/-- **From the stub `ca_setup` to the run of `check`**: the stub's state `s` agrees with the
caller's `dm` but in `rax` and the flags, and its memory differs from the caller's only inside
the table; if the region is big enough, the stores relate `s.dmem` to the L memory `m0`. Then
the machine returns, with the caller's registers and the memory outside the layout unchanged,
`rdx = 1` or `check`'s outcome from `m0`. -/
theorem abi_start_outcome [Host] (p : Prog) (tab : Tab) (hok : abiTabOk tab = true)
    (hwf : Prog.wf tab p = true) (k0 : Nat) (hcode : Code (abiStub tab ++ compileProg tab p "check") k0)
    (fd : FunDecl) (hentry : p.lookup "check" = some fd) (hnp : fd.nparams = 0)
    (b pb : ByteArray) (dm : MachineData) (ra : Word) (hc : AbiCall b pb dm ra) (m0 : Mem)
    (s : MachineData) (hregs : ∀ r, r ≠ .rax → s.regs.get64 r = dm.regs.get64 r)
    (hd : Only dm.regs.r8.toNat
      (abiLayout tab dm.regs.r8.toNat dm.regs.rdi.toNat b.size dm.regs.rdx.toNat pb.size).tabEnd
      dm.dmem s.dmem)
    (hd' : Only dm.regs.r8.toNat (dm.regs.r8.toNat + dm.regs.r9.toNat) dm.dmem s.dmem)
    (hmem : abiNeed tab ≤ dm.regs.r9.toNat →
      MemRel (abiLayout tab dm.regs.r8.toNat dm.regs.rdi.toNat b.size dm.regs.rdx.toNat pb.size) m0
        (stores dm.regs dm.regs.r8.toNat s.dmem 0 (abiVals tab))) :
    Ev (fun st => EntryPost (abiLayout tab dm.regs.r8.toNat dm.regs.rdi.toNat b.size dm.regs.rdx.toNat pb.size)
        dm ra (L.run p abiFuel "check" [] m0) st ∧ SizesPost b pb st)
      s (label abiSetupL) := by
  obtain ⟨hnb, htab, hneed64⟩ := abiTabOk_spec hok
  have hL := abiVals_length tab hnb
  have hfits := hc.hfits
  have hTE := abiVals_tabEnd hok dm.regs.r8.toNat dm.regs.rdi.toNat b.size dm.regs.rdx.toNat pb.size
  have hTE2 : (abiLayout tab dm.regs.r8.toNat dm.regs.rdi.toNat b.size dm.regs.rdx.toNat pb.size).tabEnd ≤
      dm.regs.r8.toNat + 2 ^ 31 := by
    simp only [Layout.tabEnd, abiLayout_T, abiLayout_tab, abiLayout_nargs]; omega
  have e8 : s.regs.r8 = dm.regs.r8 :=
    UInt64.toBitVec_inj.mp (by simpa using hregs .r8 (by decide))
  have e9 : s.regs.r9 = dm.regs.r9 :=
    UInt64.toBitVec_inj.mp (by simpa using hregs .r9 (by decide))
  have esp : s.regs.rsp = dm.regs.rsp :=
    UInt64.toBitVec_inj.mp (by simpa using hregs .rsp (by decide))
  have ebp : s.regs.rbp = dm.regs.rbp :=
    UInt64.toBitVec_inj.mp (by simpa using hregs .rbp (by decide))
  have e14 : s.regs.r14 = dm.regs.r14 :=
    UInt64.toBitVec_inj.mp (by simpa using hregs .r14 (by decide))
  have e15 : s.regs.r15 = dm.regs.r15 :=
    UInt64.toBitVec_inj.mp (by simpa using hregs .r15 (by decide))
  have ebx : s.regs.rbx = dm.regs.rbx :=
    UInt64.toBitVec_inj.mp (by simpa using hregs .rbx (by decide))
  have e12 : s.regs.r12 = dm.regs.r12 :=
    UInt64.toBitVec_inj.mp (by simpa using hregs .r12 (by decide))
  have e13 : s.regs.r13 = dm.regs.r13 :=
    UInt64.toBitVec_inj.mp (by simpa using hregs .r13 (by decide))
  refine sim_abiStub tab hok k0 hcode.left _ s ra ?_ ?_ ?_ ?_ ?_
  · intro hneed j hj
    rw [e9] at hneed
    simp only [abiNeed, hnb, abiSlot] at hneed
    rw [e8]
    exact hd.grows _ (by rw [hc.hzero _ (by omega) (by rw [hL] at hj; omega)]; rfl)
  · intro hneed
    rw [e9] at hneed
    simp only [abiNeed, hnb, abiSlot] at hneed
    rw [e8, hL]; omega
  · rw [esp, toBitVec_eq_A, ← hc.hra]
    refine rdW_congr fun j hj => ?_
    rw [A_add, hd'.same _ (by have := hc.hcs8; omega) ?_]
    rcases (hc.hcs (dm.regs.rsp.toNat + j) (by omega) (by have := hc.hcs8; omega)).2.1 with h | h
    · omega
    · omega
  · intro st hpc hrdx hsp hbp h14 h15 hbx h12 h13 hdm
    refine ⟨⟨hpc, ⟨?_, by rw [hbp, ebp], by rw [h14, e14], by rw [h15, e15], by rw [hbx, ebx],
      by rw [h12, e12], by rw [h13, e13]⟩,
      MemFrame.of_only_tab (G := abiLayout tab dm.regs.r8.toNat dm.regs.rdi.toNat b.size dm.regs.rdx.toNat pb.size)
        (by rw [hdm]; exact hd), Or.inl hrdx⟩, Or.inl hrdx⟩
    have e := congrArg BitVec.toNat hsp
    rw [BitVec.toNat_add, show (8 : BitVec 64).toNat = 8 from rfl, esp] at e
    simp only [UInt64.toNat_toBitVec] at e
    have := hc.hcs8
    omega
  intro hneed hsi hcx s1 hs1 hrdi hrsi hregs1
  have esi : s.regs.rsi = dm.regs.rsi :=
    UInt64.toBitVec_inj.mp (by simpa using hregs .rsi (by decide))
  have ecx : s.regs.rcx = dm.regs.rcx :=
    UInt64.toBitVec_inj.mp (by simpa using hregs .rcx (by decide))
  have hsz : b.size < 2 ^ 63 ∧ pb.size < 2 ^ 63 := by
    rw [← hc.hn, ← hc.hnp, ← esi, ← ecx]; exact ⟨hsi, hcx⟩
  rw [e9] at hneed
  have hneed' := hneed
  simp only [abiNeed, hnb, abiSlot] at hneed'
  have hs1' : s1.dmem = stores dm.regs dm.regs.r8.toNat s.dmem 0 (abiVals tab) := by
    rw [hs1, e8, stores_regs hregs _ _ _ _ (abiVals_noRax tab)]
  have hregs' : ∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → s1.regs.get64 r = dm.regs.get64 r :=
    fun r h1 h2 h3 => (hregs1 r h1 h2 h3).trans (hregs r h1)
  obtain ⟨hH, hRR⟩ := abi_harness hok hc hneed s.dmem hd' s1 hs1'
    (by rw [hrdi, e8]) hrsi hregs'
  have hm := hmem hneed
  rw [← hs1'] at hm
  have hsp1 : s1.regs.rsp = dm.regs.rsp :=
    UInt64.toBitVec_inj.mp (by simpa using hregs' .rsp (by decide) (by decide) (by decide))
  have hO1 : Only dm.regs.r8.toNat
      (abiLayout tab dm.regs.r8.toNat dm.regs.rdi.toNat b.size dm.regs.rdx.toNat pb.size).tabEnd
      dm.dmem s1.dmem := by
    rw [hs1']
    exact hd.union (stores_only dm.regs dm.regs.r8.toNat (abiVals tab) s.dmem 0 (by simp; omega))
      (Nat.le_refl _) (by omega) (Nat.le_refl _) (by simpa using hTE)
  refine eventually_weaken _ _ _ _ ?_
    (compile_correct_frame p "check" _ (abiLayout_ok hok (abiCall_geom hc hneed)) hwf
      (k0 + (abiStub tab).length) hcode.right fd hentry [] (by simp [hnp]) rfl m0 abiFuel s1 ra
      hH.hT hH.hN hm hH.hroom hH.htop (fun i h => absurd h (by simp)) hH.hra hH.hcs hH.hcs24 hH.hcs8
      hH.hsv hH.hsv64)
  intro st ⟨hpc, hsp, hbp, h14, h15, ⟨hbx, h12, h13⟩, hfr, hout⟩
  refine ⟨⟨hpc, hRR _ ⟨hsp, hbp, h14, h15, hbx, h12, h13⟩, ?_, hout⟩, Or.inr hsz⟩
  rw [hsp1] at hfr
  exact MemFrame.only_tab hfr hO1

/-- **From an entry-1 label** (`ca_start_a`, `ca_start_a0`): on a big enough region the mode word
`w` is written, then the stub; the run of `check` from the loaded memory with the mode word `w`
(or `rdx = 1`). The seven instructions at `k`: the label, the size check, the mode store, the jump
to `ca_setup`. -/
theorem abiMode_outcome [Host] (p : Prog) (tab : Tab) (hok : abiTabOk tab = true)
    (hwf : Prog.wf tab p = true) (mode : GVar) (hng : mode.id < tab.ng) (w : Word) (lab : Label)
    (k k0 : Nat) (hl : label lab = at_ k)
    (h0 : Host.prog[k + 0]? = some (.label lab))
    (h1 : Host.prog[k + 1]? = some (movRI .rax (abiNeed tab).toUInt64))
    (h2 : Host.prog[k + 2]? = some (i64 (.cmp (.reg (rr .r9)) (oR .rax))))
    (h3 : Host.prog[k + 3]? = some (jccL .c abiSetupL))
    (h4 : Host.prog[k + 4]? = some (movRI .rax w))
    (h5 : Host.prog[k + 5]? = some (movMR (mb .r8 (tab.globOff mode)) .rax))
    (h6 : Host.prog[k + 6]? = some (jmpL abiSetupL))
    (hcR : Code (abiStub tab ++ compileProg tab p "check") k0)
    (fd : FunDecl) (hentry : p.lookup "check" = some fd) (hnp : fd.nparams = 0)
    (b pb : ByteArray) (dm : MachineData) (ra : Word) (hc : AbiCall b pb dm ra) :
    Ev (fun st => EntryPost (abiLayout tab dm.regs.r8.toNat dm.regs.rdi.toNat b.size dm.regs.rdx.toNat pb.size)
        dm ra (L.run p abiFuel "check" [] ((loadMem b pb [] (List.replicate tab.nw abiWords)).setG mode w)) st ∧
        SizesPost b pb st)
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
    refine abi_start_outcome p tab hok hwf _ hcR fd hentry hnp b pb dm ra hc _ _ ?_ (Only.refl _ _ _)
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
    simp only [abiNeed, hnb, abiSlot] at hneed'
    have hoff : SmallOff (tab.globOff mode) := by
      simp only [Tab.globOff, Tab.globBase]; constructor <;> omega
    have hgo : (tab.globOff mode).toNat + 8 ≤ 2 ^ 35 := by
      simp only [Tab.globOff, Tab.globBase]; omega
    have hgz : ∀ j < 8, dm.dmem.get? (A (dm.regs.r8.toNat + (tab.globOff mode).toNat + j)) = some 0 :=
      fun j hj => hc.hzero _ (by omega) (by omega)
    refine ev_movRI h4 ?_
    refine ev_movMR h5 hoff ?_ ?_
    · simp only [Reg64s.set64_rax, Reg64s.get64_r8, UInt64.toNat_toBitVec]
      exact isSome_rdW fun j hj => by rw [A_add, hgz j hj]; rfl
    refine ev_jmp h6 ?_
    simp only [Reg64s.set64_rax, Reg64s.get64_r8, Reg64s.get64_rax, UInt64.toNat_toBitVec]
    have hGa : dm.regs.r8.toNat + (tab.globOff mode).toNat =
        (abiLayout tab dm.regs.r8.toNat dm.regs.rdi.toNat b.size dm.regs.rdx.toNat pb.size).globAddr mode := by
      rw [← Layout.globAddr_toNat]; rfl
    have hGe : (abiLayout tab dm.regs.r8.toNat dm.regs.rdi.toNat b.size dm.regs.rdx.toNat pb.size).globAddr mode + 8 ≤
        (abiLayout tab dm.regs.r8.toNat dm.regs.rdi.toNat b.size dm.regs.rdx.toNat pb.size).tabEnd := by
      simp only [Layout.globAddr, Layout.globStart, Layout.tabEnd, abiLayout_T, abiLayout_tab]; omega
    refine abi_start_outcome p tab hok hwf _ hcR fd hentry hnp b pb dm ra hc _ _ ?_ ?_ ?_ (fun _ => ?_)
    · intro r hr; cases r <;> first | exact absurd rfl hr | rfl
    · rw [hGa]
      exact (Only.wrW (by simp only [Layout.tabEnd, abiLayout_T, abiLayout_tab, abiLayout_nargs] at hGe ⊢; omega)).mono
        (by simp only [Layout.globAddr, Layout.globStart, abiLayout_T]; omega) hGe
    · exact (Only.wrW (x := dm.regs.r8.toNat + (tab.globOff mode).toNat) (by omega)).mono
        (by omega) (by omega)
    · have hG := abiLayout_ok hok (abiCall_geom hc hneed)
      have hL := abiVals_length tab hnb
      have h0 := abi_memRel tab hok b pb dm ra hc hneed
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

/-- **From `ca_start_a`** (entry 1, mode word `1`). -/
theorem abiA_outcome [Host] (p : Prog) (tab : Tab) (hok : abiTabOk tab = true)
    (hwf : Prog.wf tab p = true) (mode plo phi : GVar) (out hdrf ctlf : ArrId) (hw : Nat)
    (fz own : List ArrId) (hng : mode.id < tab.ng) (k0 : Nat)
    (hcode : Code (parStub tab mode plo phi out hdrf ctlf hw fz own ++ (abiStub tab ++ compileProg tab p "check")) k0)
    (fd : FunDecl) (hentry : p.lookup "check" = some fd) (hnp : fd.nparams = 0)
    (b pb : ByteArray) (dm : MachineData) (ra : Word) (hc : AbiCall b pb dm ra) :
    Ev (fun st => EntryPost (abiLayout tab dm.regs.r8.toNat dm.regs.rdi.toNat b.size dm.regs.rdx.toNat pb.size)
        dm ra (L.run p abiFuel "check" [] ((loadMem b pb [] (List.replicate tab.nw abiWords)).setG mode 1)) st ∧
        SizesPost b pb st)
      dm (label abiStartAL) := by
  have hcP := hcode.left
  simp only [parStub] at hcP
  exact abiMode_outcome p tab hok hwf mode hng 1 abiStartAL k0 _ (Code.label (i := 0) hcP rfl)
    (Code.get (i := 0) hcP rfl) (Code.get (i := 1) hcP rfl) (Code.get (i := 2) hcP rfl)
    (Code.get (i := 3) hcP rfl) (Code.get (i := 4) hcP rfl) (Code.get (i := 5) hcP rfl)
    (Code.get (i := 6) hcP rfl) hcode.right fd hentry hnp b pb dm ra hc

/-- **From `ca_start_a0`** (the sequential driver's entry 1, mode word `3`). -/
theorem abiA0_outcome [Host] (p : Prog) (tab : Tab) (hok : abiTabOk tab = true)
    (hwf : Prog.wf tab p = true) (mode plo phi : GVar) (out hdrf ctlf : ArrId) (hw : Nat)
    (fz own : List ArrId) (hng : mode.id < tab.ng) (k0 : Nat)
    (hcode : Code (parStub tab mode plo phi out hdrf ctlf hw fz own ++ (abiStub tab ++ compileProg tab p "check")) k0)
    (fd : FunDecl) (hentry : p.lookup "check" = some fd) (hnp : fd.nparams = 0)
    (b pb : ByteArray) (dm : MachineData) (ra : Word) (hc : AbiCall b pb dm ra) :
    Ev (fun st => EntryPost (abiLayout tab dm.regs.r8.toNat dm.regs.rdi.toNat b.size dm.regs.rdx.toNat pb.size)
        dm ra (L.run p abiFuel "check" [] ((loadMem b pb [] (List.replicate tab.nw abiWords)).setG mode 3)) st ∧
        SizesPost b pb st)
      dm (label abiStartA0L) := by
  have hcP := hcode.left
  simp only [parStub] at hcP
  exact abiMode_outcome p tab hok hwf mode hng 3 abiStartA0L (k0 + 7) _ (Code.label (i := 7) hcP rfl)
    (Code.get (i := 7) hcP rfl) (Code.get (i := 8) hcP rfl) (Code.get (i := 9) hcP rfl)
    (Code.get (i := 10) hcP rfl) (Code.get (i := 11) hcP rfl) (Code.get (i := 12) hcP rfl)
    (Code.get (i := 13) hcP rfl) hcode.right fd hentry hnp b pb dm ra hc

end ConAgua.Final
