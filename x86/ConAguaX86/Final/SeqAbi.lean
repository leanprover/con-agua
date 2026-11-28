module

public import ConAguaX86.Final.SeqLayout
public import ConAguaX86.Final.ParAbi
import Kraken.X64.Registers

@[expose] public section

/-!
# `ca_check_seq` on the machine (lane parmode)

`abiS_outcome`: from `ca_check_seq` (the sequential driver's entry 2 in place, `parStub`), on a
region that holds an L memory `m` in the partition layout (`MemRel (abiLayout …) m`), with the
region in `r8` and the range in `rsi`, `rdx`: the stores `seqVals`, the globals `plo`, `phi`,
`mode`, then `compile_correct_frame` in `ca_check_seq`'s layout (`seqLayout`) from
`seqMem m … rsi rdx`.
-/

namespace ConAgua.Final

open L L.Compiler

/-- **How the driver calls `ca_check_seq`**: the region `[base, base + blen)` (big enough, in the
address space) in `r8`, its first `2^31` bytes (the table) mapped, the return address on the
machine stack, whose 32 bytes around `rsp` are mapped and apart from the region. -/
structure SeqCall (tab : Tab) (base blen : Nat) (dm : MachineData) (ra : Word) : Prop where
  need : abiNeed tab ≤ blen
  fits : base + blen < 2 ^ 64
  hbase : dm.regs.r8.toNat = base
  hmap : ∀ x, base ≤ x → x < base + 2 ^ 31 → (dm.dmem.get? (A x)).isSome
  hra : rdW dm.dmem (A dm.regs.rsp.toNat) = some ra
  hcs : ∀ x, dm.regs.rsp.toNat - 24 ≤ x → x < dm.regs.rsp.toNat + 8 →
    (dm.dmem.get? (A x)).isSome ∧ (x < base ∨ base + blen ≤ x)
  hcs24 : 24 ≤ dm.regs.rsp.toNat
  hcs8 : dm.regs.rsp.toNat + 8 < 2 ^ 64

/-- **A write of the table's first word** (the stack's top, which `MemRel` does not describe)
keeps the memory relation. -/
theorem MemRel.wrTop {G : L.Compiler.Layout} (hG : G.Ok) {m : Mem} {d : DataMem} (hm : MemRel G m d) (v : BitVec 64) :
    MemRel G m (wrW d (A G.T) v) := by
  have he := hG.tab_end
  have hT : G.T + 16 ≤ G.tabEnd := by simp only [Layout.tabEnd]; omega
  have hnA : ∀ x, G.T ≤ x → x < G.T + 8 → ¬ G.InArr x := fun x h1 h2 =>
    hG.tab_arr x ⟨h1, by omega⟩
  have hgx : ∀ y, y + 8 ≤ 2 ^ 64 → (y + 8 ≤ G.T ∨ G.T + 8 ≤ y) → rdW (wrW d (A G.T) v) (A y) = rdW d (A y) :=
    fun y hy h => rdW_wrW_A (by omega) hy h
  have hget : ∀ x, x < 2 ^ 64 → (x < G.T ∨ G.T + 8 ≤ x) → (wrW d (A G.T) v).get? (A x) = d.get? (A x) :=
    fun x hx h => get?_wrW_A (by omega) hx h
  exact {
    size8 := hm.size8
    size64 := hm.size64
    get8 := fun c hc i hi => by
      have hp := G.tab.pos8_lt hc
      have hs := hm.size8 c hc
      have he8 := hG.end8 _ hp
      rw [hget _ (by omega) ?_, hm.get8 c hc i hi]
      refine Classical.byContradiction fun hx => ?_
      simp only [not_or, Nat.not_lt, Nat.not_le] at hx
      exact hnA _ hx.1 hx.2 (Layout.InArr.of8 hp ⟨by omega, by omega⟩)
    get64 := fun c hc i hi => by
      have hp := G.tab.pos64_lt hc
      have hs := hm.size64 c hc
      have he64 := hG.end64 _ hp
      rw [← hm.get64 c hc i hi]
      refine rdW_congr fun j hj => ?_
      rw [A_add, hget _ (by omega) ?_]
      refine Classical.byContradiction fun hx => ?_
      simp only [not_or, Nat.not_lt, Nat.not_le] at hx
      exact hnA _ hx.1 hx.2 (Layout.InArr.of64 hp ⟨by omega, by omega⟩)
    limit := by rw [hgx _ (by omega) (.inr (by omega))]; exact hm.limit
    base := fun c hc => by
      rw [hgx _ (by simp only [Tab.dbase]; simp only [Layout.tabEnd] at he; omega)
        (.inr (by simp only [Tab.dbase]; omega))]; exact hm.base c hc
    len := fun c hc => by
      rw [hgx _ (by simp only [Tab.dlen]; simp only [Layout.tabEnd] at he; omega)
        (.inr (by simp only [Tab.dlen]; omega))]; exact hm.len c hc
    len32 := fun c h1 h2 => by
      rw [hgx _ (by simp only [Tab.dlen32]; simp only [Layout.tabEnd] at he; omega)
        (.inr (by simp only [Tab.dlen32]; omega))]; exact hm.len32 c h1 h2
    rom := fun i hi => by
      have hw : G.tab.rom.length ≤ 8 * G.tab.romWords := G.tab.rom_length_le
      simp only [Layout.tabEnd] at he
      rw [hget _ (by omega) (.inr (by omega)), hm.rom i hi]
    stack := fun x hx => isSome_get?_storeInt (hm.stack x hx)
    res := fun x hx => isSome_get?_storeInt (hm.res x hx)
    glob := fun g hg => by
      have hc := Layout.inGlob_cell (G := G) hg
      have hT' : G.globAddr g + 8 ≤ G.tabEnd := by
        simp only [Layout.tabEnd, Layout.globAddr, Layout.globStart]; omega
      rw [hgx _ (by omega) (.inr (by simp only [Layout.globAddr, Layout.globStart]; omega))]
      exact hm.glob g hg }

/-- **From `ca_check_seq_g`** (past the table's stores): on a region that holds `M` in
`ca_check_seq`'s layout (`seqLayout`), the run of `check` from `seqNext M … w lo hi` (the mode
word `w`, `lo`, `hi` from `r10`, `rsi`, `rdx`) in that layout. -/
theorem abiSG_outcome [Host] (q p : Prog) (hq : Refines q p) (tab : Tab) (hok : abiTabOk tab = true)
    {X : AsmTab} (hAX : AsmOkT q tab X)
    (hwf : Prog.wf tab q = true) (mode plo phi : GVar) (out hdrf ctlf : ArrId) (hw : Nat)
    (fz own : List TieredArray) (hngm : mode.id < tab.ng) (hngl : plo.id < tab.ng) (hngh : phi.id < tab.ng)
    (hp : seqParamsOk tab out hdrf ctlf hw = true) (k0 : Nat)
    (hcode : Code (parStub tab mode plo phi out hdrf ctlf hw fz own ++ (abiStub tab ++ compileProgX X tab q "check")) k0)
    (fd : FunDecl) (hentry : p.lookup "check" = some fd) (hnp : fd.nparams = 0)
    {base blen : Nat} (M : Mem) (dm : MachineData) (ra : Word)
    (hc : SeqCall tab base blen dm ra) (hm : MemRel (seqLayout tab base out hdrf ctlf hw) M dm.dmem)
    (htop : rdW dm.dmem (A base) = some (UInt64.ofNat (base + (abiSlot + abiStack)))) :
    Ev (EntryPost (seqLayout tab base out hdrf ctlf hw) dm ra
        (L.run p abiFuel "check" [] (seqNext M mode plo phi dm.regs.r10 dm.regs.rsi dm.regs.rdx)))
      dm (label abiCheckSGL) := by
  obtain ⟨hnb, htab, hneed64⟩ := abiTabOk_spec hok
  have hneed := hc.need
  have hfits := hc.fits
  have hn := abiNeed_ge hok
  have hfit : base + abiNeed tab < 2 ^ 64 := by omega
  have hneed' := hneed
  have hG := seqLayout_ok (base := base) hok hp hfit
  have hcP := hcode.left
  have hcC := hcode.right.right
  simp only [parStub] at hcP
  replace hcP := hcP.left
  simp only [parStub0] at hcP
  have hL2 := hcP.left.left.right
  have hcQ := hcP
  rw [List.append_assoc] at hcQ
  have hS := hcQ.right.left
  have hL3 := hcQ.right.right
  have hLen := seqVals_length tab out hdrf ctlf hw
  rw [abiVals_length tab] at hLen
  have hend : base + 8 * (seqVals tab out hdrf ctlf hw).length ≤ 2 ^ 64 := by rw [hLen]; omega
  have hTE : (seqLayout tab base out hdrf ctlf hw).tabEnd ≤ base + 2 ^ 31 := by
    simp only [Layout.tabEnd, seqLayout_T, seqLayout_tab, seqLayout_nargs]; omega
  have hSE : base + 8 * (seqVals tab out hdrf ctlf hw).length ≤ (seqLayout tab base out hdrf ctlf hw).tabEnd := by
    rw [hLen]; simp only [Layout.tabEnd, seqLayout_T, seqLayout_tab, seqLayout_nargs, hnb]; omega
  have hgA : ∀ g : GVar, base + (tab.globOff g).toNat = (seqLayout tab base out hdrf ctlf hw).globAddr g :=
    fun g => Layout.globAddr_toNat (seqLayout tab base out hdrf ctlf hw) g
  have hgS : ∀ g : GVar, g.id < tab.ng → base + 8 * (seqVals tab out hdrf ctlf hw).length ≤
      (seqLayout tab base out hdrf ctlf hw).globAddr g ∧
      (seqLayout tab base out hdrf ctlf hw).globAddr g + 8 ≤ (seqLayout tab base out hdrf ctlf hw).tabEnd :=
    fun g hg => by
      rw [hLen]
      simp only [Layout.globAddr, Layout.globStart, Layout.tabEnd, seqLayout_T, seqLayout_tab,
        seqLayout_nargs, hnb]
      omega
  have hoffG : ∀ g : GVar, g.id < tab.ng → SmallOff (tab.globOff g) := fun g hg => by
    simp only [Tab.globOff, Tab.globBase]; constructor <;> omega
  rw [Code.label (i := 0) hL3 rfl]
  refine ev_label (Code.get (i := 0) hL3 rfl) ?_
  have e8r : dm.regs.r8.toNat = base := hc.hbase
  have e8 : (dm.regs.get64 .r8).toNat = base := by simpa using hc.hbase
  have hgb : ∀ g : GVar, g.id < tab.ng → ∀ j < 8,
      (dm.dmem.get? (A ((dm.regs.get64 .r8).toNat + (tab.globOff g).toNat + j))).isSome := fun g hg j hj => by
    rw [e8, hgA g]
    obtain ⟨h1, h2⟩ := hgS g hg
    exact hc.hmap _ (by simp only [Layout.globAddr, Layout.globStart, seqLayout_T] at h1 ⊢; omega) (by omega)
  refine ev_movMR (Code.get (i := 1) hL3 rfl) (hoffG plo hngl)
    (isSome_rdW fun j hj => by rw [A_add]; exact hgb plo hngl j hj) ?_
  refine ev_movMR (Code.get (i := 2) hL3 rfl) (hoffG phi hngh)
    (isSome_rdW fun j hj => by rw [A_add]; exact isSome_get?_storeInt (hgb phi hngh j hj)) ?_
  refine ev_movMR (Code.get (i := 3) hL3 rfl) (hoffG mode hngm)
    (isSome_rdW fun j hj => by
      rw [A_add]; exact isSome_get?_storeInt (isSome_get?_storeInt (hgb mode hngm j hj))) ?_
  refine ev_movRR (Code.get (i := 4) hL3 rfl) ?_
  refine ev_movRI (Code.get (i := 5) hL3 rfl) ?_
  refine ev_jmp (Code.get (i := 6) hL3 rfl) ?_
  simp only [Reg64s.set64_rdi, Reg64s.set64_rsi, Reg64s.get64_r8,
    Reg64s.get64_rsi, Reg64s.get64_rdx, Reg64s.get64_r10, UInt64.toNat_toBitVec]
  rw [e8r, hgA plo, hgA phi, hgA mode]
  have hOw : ∀ (d : DataMem) (g : GVar) (v : BitVec 64), g.id < tab.ng →
      Only (base + 16) (seqLayout tab base out hdrf ctlf hw).tabEnd d
        (wrW d (A ((seqLayout tab base out hdrf ctlf hw).globAddr g)) v) := fun d g v hg => by
    obtain ⟨h1, h2⟩ := hgS g hg
    refine (Only.wrW (by omega)).mono ?_ h2
    simp only [Layout.globAddr, Layout.globStart, seqLayout_T]; omega
  have hOg := ((hOw dm.dmem plo dm.regs.rsi.toBitVec hngl).union (hOw _ phi dm.regs.rdx.toBitVec hngh)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)).union (hOw _ mode dm.regs.r10.toBitVec hngm)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  have hOall : Only (seqLayout tab base out hdrf ctlf hw).T (seqLayout tab base out hdrf ctlf hw).tabEnd dm.dmem
      (wrW (wrW (wrW dm.dmem _ dm.regs.rsi.toBitVec) _ dm.regs.rdx.toBitVec) _ dm.regs.r10.toBitVec) :=
    hOg.mono (by simp only [seqLayout_T]; omega) (Nat.le_refl _)
  have hcs := hc.hcs
  refine eventually_weaken _ _ _ _ ?_ (compile_correct_frame_ref q p hq "check" _ hG X (hAX _ hG rfl) hwf _ hcC fd hentry []
    (by simp [hnp]) rfl (seqNext M mode plo phi dm.regs.r10 dm.regs.rsi dm.regs.rdx) abiFuelM _ ra ?_ ?_ ?_ ?_ ?_
    (fun i h => absurd h (by simp)) ?_ ?_ ?_ ?_ ?_ ?_)
  · intro st ⟨hpc, hsp, hbp, h14, h15, ⟨hbx, h12, h13⟩, hfr, hout⟩
    exact ⟨hpc, ⟨hsp, hbp, h14, h15, hbx, h12, h13⟩, MemFrame.only_tab hfr hOall, hout⟩
  · exact e8r
  · show (abiFuelM.toUInt64).toNat = abiFuelM
    simp [abiFuelM, abiFuel, abiInl]
  · show MemRel _ _ (wrW (wrW (wrW dm.dmem _ dm.regs.rsi.toBitVec) _ dm.regs.rdx.toBitVec) _ dm.regs.r10.toBitVec)
    exact ((hm.storeG hG (g := plo) hngl dm.regs.rsi).storeG hG (g := phi) hngh dm.regs.rdx).storeG hG
      (g := mode) hngm dm.regs.r10
  · simp only [seqLayout_lo, seqLayout_hi, abiStack]; omega
  · show rdW (wrW (wrW (wrW dm.dmem _ _) _ _) _ _) _ = _
    rw [hOg.rdW_eq (by simp only [seqLayout_T]; omega) (Or.inl (by simp only [seqLayout_T]; omega))]
    simpa only [seqLayout_T, seqLayout_hi, Nat.add_assoc] using htop
  · show rdW (wrW (wrW (wrW dm.dmem _ _) _ _) _ _) (A dm.regs.rsp.toNat) = some ra
    rw [← hc.hra]
    refine rdW_congr fun j hj => ?_
    rw [A_add, hOall.same _ (by have := hc.hcs8; omega) ?_]
    rcases (hcs (dm.regs.rsp.toNat + j) (by omega) (by have := hc.hcs8; omega)).2 with h | h
    · left; simp only [seqLayout_T]; omega
    · right; omega
  · intro x h1 h2
    change dm.regs.rsp.toNat - 24 ≤ x at h1
    change x < dm.regs.rsp.toNat + 8 at h2
    obtain ⟨hmx, hreg⟩ := hcs x h1 h2
    exact ⟨hOall.grows _ hmx, seq_out hok hp hneed hreg⟩
  · exact hc.hcs24
  · exact hc.hcs8
  · intro x h1 h2
    obtain ⟨q0, q1, q2, q3⟩ := seq_save hok hp h1 h2
    refine ⟨hOall.grows _ (hc.hmap x q0 q1), q2, q3, ?_⟩
    show x < dm.regs.rsp.toNat - 24 ∨ dm.regs.rsp.toNat + 8 ≤ x
    refine Classical.byContradiction fun hn => ?_
    simp only [not_or, Nat.not_lt, Nat.not_le] at hn
    rcases (hcs x (by omega) (by omega)).2 with h | h <;> omega
  · have := seq_save (x := (seqLayout tab base out hdrf ctlf hw).tabEnd) hok hp (Nat.le_refl _) (by omega)
    omega


/-- **From `ca_check_seq_m`**: on a region that holds `m` in the partition layout, the run of
`check` from `seqMemW m … w lo hi` (the mode word `w`, `lo`, `hi` from `r10`, `rsi`, `rdx`) in `ca_check_seq`'s layout. -/
theorem abiSM_outcome [Host] (q p : Prog) (hq : Refines q p) (tab : Tab) (hok : abiTabOk tab = true)
    {X : AsmTab} (hAX : AsmOkT q tab X)
    (hwf : Prog.wf tab q = true) (mode plo phi : GVar) (out hdrf ctlf : ArrId) (hw : Nat)
    (fz own : List TieredArray) (hngm : mode.id < tab.ng) (hngl : plo.id < tab.ng) (hngh : phi.id < tab.ng)
    (hp : seqParamsOk tab out hdrf ctlf hw = true) (k0 : Nat)
    (hcode : Code (parStub tab mode plo phi out hdrf ctlf hw fz own ++ (abiStub tab ++ compileProgX X tab q "check")) k0)
    (fd : FunDecl) (hentry : p.lookup "check" = some fd) (hnp : fd.nparams = 0)
    {base blen inp n pins np : Nat} (m : Mem) (dm : MachineData) (ra : Word)
    (hc : SeqCall tab base blen dm ra) (hm : MemRel (abiLayout tab base inp n pins np) m dm.dmem) :
    Ev (EntryPost (seqLayout tab base out hdrf ctlf hw) dm ra
        (L.run p abiFuel "check" [] (seqMemW m mode plo phi out hdrf ctlf hw dm.regs.r10 dm.regs.rsi dm.regs.rdx)))
      dm (label abiCheckSML) := by
  obtain ⟨hnb, htab, hneed64⟩ := abiTabOk_spec hok
  have hneed := hc.need
  have hfits := hc.fits
  have hn := abiNeed_ge hok
  have hfit : base + abiNeed tab < 2 ^ 64 := by omega
  have hneed' := hneed
  have hG := seqLayout_ok (base := base) hok hp hfit
  have hcP := hcode.left
  have hcC := hcode.right.right
  simp only [parStub] at hcP
  replace hcP := hcP.left
  simp only [parStub0] at hcP
  have hL2 := hcP.left.left.right
  have hcQ := hcP
  rw [List.append_assoc] at hcQ
  have hS := hcQ.right.left
  have hL3 := hcQ.right.right
  have hLen := seqVals_length tab out hdrf ctlf hw
  rw [abiVals_length tab] at hLen
  have hend : base + 8 * (seqVals tab out hdrf ctlf hw).length ≤ 2 ^ 64 := by rw [hLen]; omega
  have hTE : (seqLayout tab base out hdrf ctlf hw).tabEnd ≤ base + 2 ^ 31 := by
    simp only [Layout.tabEnd, seqLayout_T, seqLayout_tab, seqLayout_nargs]; omega
  have hSE : base + 8 * (seqVals tab out hdrf ctlf hw).length ≤ (seqLayout tab base out hdrf ctlf hw).tabEnd := by
    rw [hLen]; simp only [Layout.tabEnd, seqLayout_T, seqLayout_tab, seqLayout_nargs, hnb]; omega
  have hgA : ∀ g : GVar, base + (tab.globOff g).toNat = (seqLayout tab base out hdrf ctlf hw).globAddr g :=
    fun g => Layout.globAddr_toNat (seqLayout tab base out hdrf ctlf hw) g
  have hgS : ∀ g : GVar, g.id < tab.ng → base + 8 * (seqVals tab out hdrf ctlf hw).length ≤
      (seqLayout tab base out hdrf ctlf hw).globAddr g ∧
      (seqLayout tab base out hdrf ctlf hw).globAddr g + 8 ≤ (seqLayout tab base out hdrf ctlf hw).tabEnd :=
    fun g hg => by
      rw [hLen]
      simp only [Layout.globAddr, Layout.globStart, Layout.tabEnd, seqLayout_T, seqLayout_tab,
        seqLayout_nargs, hnb]
      omega
  have hoffG : ∀ g : GVar, g.id < tab.ng → SmallOff (tab.globOff g) := fun g hg => by
    simp only [Tab.globOff, Tab.globBase]; constructor <;> omega
  rw [Code.label (i := 9) hL2 rfl]
  refine ev_label (Code.get (i := 9) hL2 rfl) ?_
  refine ev_congr (sim_stores _ dm.regs base hc.hbase (seqVals tab out hdrf ctlf hw) 0 _ dm hS (fun _ _ => rfl)
    (seqVals_noRax tab out hdrf ctlf hw) (by rw [hLen]; omega) (by simpa using hend)
    (fun j hj => hc.hmap _ (by omega) (by rw [hLen] at hj; omega)) ?_)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  intro s1 hs1 hR1
  have e8 : (s1.regs.get64 .r8).toNat = base := by rw [hR1 .r8 (by decide)]; simpa using hc.hbase
  have hO1 := stores_only dm.regs base (seqVals tab out hdrf ctlf hw) dm.dmem 0 (by simpa using hend)
  simp only [Nat.add_zero] at hO1
  rw [← hs1] at hO1
  have hR8 : s1.regs.r8 = dm.regs.r8 := UInt64.toBitVec_inj.mp (by simpa using hR1 .r8 (by decide))
  have hRsi : s1.regs.rsi = dm.regs.rsi := UInt64.toBitVec_inj.mp (by simpa using hR1 .rsi (by decide))
  have hRdx : s1.regs.rdx = dm.regs.rdx := UInt64.toBitVec_inj.mp (by simpa using hR1 .rdx (by decide))
  have hRsp : s1.regs.rsp = dm.regs.rsp := UInt64.toBitVec_inj.mp (by simpa using hR1 .rsp (by decide))
  have hR10 : s1.regs.r10 = dm.regs.r10 := UInt64.toBitVec_inj.mp (by simpa using hR1 .r10 (by decide))
  have e8r : s1.regs.r8.toNat = base := by rw [hR8]; exact hc.hbase
  have hm0 := seq_memRel (out := out) (hdrf := hdrf) (ctlf := ctlf) (hw := hw) hok hp hfit dm.regs hc.hbase m dm.dmem hm
  rw [← hs1] at hm0
  have hO1' : Only (seqLayout tab base out hdrf ctlf hw).T (seqLayout tab base out hdrf ctlf hw).tabEnd dm.dmem s1.dmem :=
    hO1.mono (by simp only [seqLayout_T]; omega) hSE
  have hcs := hc.hcs
  have hc1 : SeqCall tab base blen s1 ra := by
    refine ⟨hc.need, hc.fits, e8r, fun x h1 h2 => hO1.grows _ (hc.hmap x h1 h2), ?_, ?_, ?_, ?_⟩
    · rw [hRsp, ← hc.hra]
      refine rdW_congr fun j hj => ?_
      rw [A_add, hO1.same _ (by have := hc.hcs8; omega) ?_]
      rcases (hcs (dm.regs.rsp.toNat + j) (by omega) (by have := hc.hcs8; omega)).2 with h | h
      · left; omega
      · right; rw [hLen]; omega
    · intro x h1 h2
      rw [hRsp] at h1 h2
      obtain ⟨hmx, hreg⟩ := hcs x h1 h2
      exact ⟨hO1.grows _ hmx, hreg⟩
    · rw [hRsp]; exact hc.hcs24
    · rw [hRsp]; exact hc.hcs8
  have hl := Code.label (i := 0) hL3 rfl
  simp only [Nat.add_zero] at hl
  rw [← hl]
  refine eventually_weaken _ _ _ _ (fun st ⟨hpc, hRR, hfr, hout⟩ => ⟨hpc, ?_, MemFrame.only_tab (by rw [← hRsp]; exact hfr) hO1', ?_⟩)
    (abiSG_outcome q p hq tab hok hAX hwf mode plo phi out hdrf ctlf hw fz own hngm hngl hngh hp k0 hcode fd hentry hnp
      (seqMem0 m out hdrf ctlf hw) s1 ra hc1 hm0 ?_)
  · have := stores_rdW? dm.regs base _ dm.dmem 0 _ (seqVals_getElem? tab out hdrf ctlf hw).1 hend
    rw [addr_val _ _ (by rw [hc.hbase]; simp only [abiSlot, abiStack]; omega), hc.hbase, ← hs1] at this
    simpa only [Nat.mul_zero, Nat.add_zero] using this
  · obtain ⟨hsp, hbp, h14, h15, hbx, h12, h13⟩ := hRR
    refine ⟨by rw [hsp, hRsp], by rw [hbp]; exact UInt64.toBitVec_inj.mp (by simpa using hR1 .rbp (by decide)),
      by rw [h14]; exact UInt64.toBitVec_inj.mp (by simpa using hR1 .r14 (by decide)),
      by rw [h15]; exact UInt64.toBitVec_inj.mp (by simpa using hR1 .r15 (by decide)),
      by rw [hbx]; exact UInt64.toBitVec_inj.mp (by simpa using hR1 .rbx (by decide)),
      by rw [h12]; exact UInt64.toBitVec_inj.mp (by simpa using hR1 .r12 (by decide)),
      by rw [h13]; exact UInt64.toBitVec_inj.mp (by simpa using hR1 .r13 (by decide))⟩
  · rw [hR10, hRsi, hRdx] at hout; exact hout

/-- **From `ca_check_seq`**: on a region that holds `m` in the partition layout, the run of
`check` from `seqMem m … lo hi` (`lo`, `hi` from `rsi`, `rdx`; the mode word `2`) in
`ca_check_seq`'s layout. -/
theorem abiS_outcome [Host] (q p : Prog) (hq : Refines q p) (tab : Tab) (hok : abiTabOk tab = true)
    {X : AsmTab} (hAX : AsmOkT q tab X)
    (hwf : Prog.wf tab q = true) (mode plo phi : GVar) (out hdrf ctlf : ArrId) (hw : Nat)
    (fz own : List TieredArray) (hngm : mode.id < tab.ng) (hngl : plo.id < tab.ng) (hngh : phi.id < tab.ng)
    (hp : seqParamsOk tab out hdrf ctlf hw = true) (k0 : Nat)
    (hcode : Code (parStub tab mode plo phi out hdrf ctlf hw fz own ++ (abiStub tab ++ compileProgX X tab q "check")) k0)
    (fd : FunDecl) (hentry : p.lookup "check" = some fd) (hnp : fd.nparams = 0)
    {base blen inp n pins np : Nat} (m : Mem) (dm : MachineData) (ra : Word)
    (hc : SeqCall tab base blen dm ra) (hm : MemRel (abiLayout tab base inp n pins np) m dm.dmem) :
    Ev (EntryPost (seqLayout tab base out hdrf ctlf hw) dm ra
        (L.run p abiFuel "check" [] (seqMem m mode plo phi out hdrf ctlf hw dm.regs.rsi dm.regs.rdx)))
      dm (label abiCheckSL) := by
  have hcP := hcode.left
  simp only [parStub] at hcP
  replace hcP := hcP.left
  simp only [parStub0] at hcP
  have hL2 := hcP.left.left.right
  rw [Code.label (i := 7) hL2 rfl]
  refine ev_label (Code.get (i := 7) hL2 rfl) ?_
  refine ev_movRI (Code.get (i := 8) hL2 rfl) ?_
  rw [← Code.label (i := 9) hL2 rfl]
  have hc' : SeqCall tab base blen { dm with regs := dm.regs.set64 .r10 (2 : Word).toBitVec } ra :=
    ⟨hc.need, hc.fits, by simpa [Reg64s.set64_r10] using hc.hbase, hc.hmap, by simpa [Reg64s.set64_r10] using hc.hra,
      by simpa [Reg64s.set64_r10] using hc.hcs, by simpa [Reg64s.set64_r10] using hc.hcs24,
      by simpa [Reg64s.set64_r10] using hc.hcs8⟩
  refine eventually_weaken _ _ _ _ (fun st h => ?_) (abiSM_outcome q p hq tab hok hAX hwf mode plo phi out hdrf ctlf hw
    fz own hngm hngl hngh hp k0 hcode fd hentry hnp m _ ra hc' hm)
  simpa [EntryPost, RegsRestored, Reg64s.set64_r10, seqMem] using h

end ConAgua.Final
