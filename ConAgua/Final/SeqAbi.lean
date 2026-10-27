import ConAgua.Final.SeqLayout
import ConAgua.Final.ParAbi
import Kraken.X64.Registers

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

/-- **From `ca_check_seq`**: on a region that holds `m` in the partition layout, the run of
`check` from `seqMem m … lo hi` (`lo`, `hi` from `rsi`, `rdx`) in `ca_check_seq`'s layout. -/
theorem abiS_outcome [Host] (p : Prog) (tab : Tab) (hok : abiTabOk tab = true)
    (hwf : Prog.wf tab p = true) (mode plo phi : GVar) (out hdrf ctlf : ArrId) (hw : Nat)
    (fz own : List ArrId) (hngm : mode.id < tab.ng) (hngl : plo.id < tab.ng) (hngh : phi.id < tab.ng)
    (hp : seqParamsOk tab out hdrf ctlf hw = true) (k0 : Nat)
    (hcode : Code (parStub tab mode plo phi out hdrf ctlf hw fz own ++ (abiStub tab ++ compileProg tab p "check")) k0)
    (fd : FunDecl) (hentry : p.lookup "check" = some fd) (hnp : fd.nparams = 0)
    {base blen inp n pins np : Nat} (m : Mem) (dm : MachineData) (ra : Word)
    (hc : SeqCall tab base blen dm ra) (hm : MemRel (abiLayout tab base inp n pins np) m dm.dmem) :
    Ev (EntryPost (seqLayout tab base out hdrf ctlf hw) dm ra
        (L.run p abiFuel "check" [] (seqMem m mode plo phi out hdrf ctlf hw dm.regs.rsi dm.regs.rdx)))
      dm (label abiCheckSL) := by
  obtain ⟨hnb, htab, hneed64⟩ := abiTabOk_spec hok
  have hneed := hc.need
  have hfits := hc.fits
  have hn : abiNeed tab = abiSlot * (2 + tab.nw) := by simp [abiNeed, hnb]
  have hfit : base + abiNeed tab < 2 ^ 64 := by omega
  have hneed' := hneed
  simp only [hn, abiSlot] at hneed'
  have hG := seqLayout_ok (base := base) hok hp hfit
  have hcP := hcode.left
  have hcC := hcode.right.right
  simp only [parStub] at hcP
  have hL2 := hcP.left.left.right
  have hcQ := hcP
  rw [List.append_assoc] at hcQ
  have hS := hcQ.right.left
  have hL3 := hcQ.right.right
  have hLen := seqVals_length hnb out hdrf ctlf hw
  rw [abiVals_length tab hnb] at hLen
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
  rw [Code.label (i := 7) hL2 rfl]
  refine ev_label (Code.get (i := 7) hL2 rfl) ?_
  refine ev_congr (sim_stores _ dm.regs base hc.hbase (seqVals tab out hdrf ctlf hw) 0 _ dm hS (fun _ _ => rfl)
    (seqVals_noRax tab out hdrf ctlf hw hnb) (by rw [hLen]; omega) (by simpa using hend)
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
  have hRbp : s1.regs.rbp = dm.regs.rbp := UInt64.toBitVec_inj.mp (by simpa using hR1 .rbp (by decide))
  have hR14 : s1.regs.r14 = dm.regs.r14 := UInt64.toBitVec_inj.mp (by simpa using hR1 .r14 (by decide))
  have hR15 : s1.regs.r15 = dm.regs.r15 := UInt64.toBitVec_inj.mp (by simpa using hR1 .r15 (by decide))
  have e8r : s1.regs.r8.toNat = base := by rw [hR8]; exact hc.hbase
  have hgb : ∀ g : GVar, g.id < tab.ng → ∀ j < 8,
      (s1.dmem.get? (A ((s1.regs.get64 .r8).toNat + (tab.globOff g).toNat + j))).isSome := fun g hg j hj => by
    rw [e8, hgA g]
    obtain ⟨h1, h2⟩ := hgS g hg
    exact hO1.grows _ (hc.hmap _ (by simp only [Layout.globAddr, Layout.globStart, seqLayout_T] at h1 ⊢; omega) (by omega))
  refine ev_movMR (Code.get (i := 0) hL3 rfl) (hoffG plo hngl)
    (isSome_rdW fun j hj => by rw [A_add]; exact hgb plo hngl j hj) ?_
  refine ev_movMR (Code.get (i := 1) hL3 rfl) (hoffG phi hngh)
    (isSome_rdW fun j hj => by rw [A_add]; exact isSome_get?_storeInt (hgb phi hngh j hj)) ?_
  refine ev_movRI (Code.get (i := 2) hL3 rfl) ?_
  refine ev_movMR (Code.get (i := 3) hL3 rfl) (hoffG mode hngm)
    (isSome_rdW fun j hj => by
      rw [A_add]; exact isSome_get?_storeInt (isSome_get?_storeInt (hgb mode hngm j hj))) ?_
  refine ev_movRR (Code.get (i := 4) hL3 rfl) ?_
  refine ev_movRI (Code.get (i := 5) hL3 rfl) ?_
  refine ev_jmp (Code.get (i := 6) hL3 rfl) ?_
  simp only [Reg64s.set64_rax, Reg64s.set64_rdi, Reg64s.set64_rsi, Reg64s.get64_r8, Reg64s.get64_rax,
    Reg64s.get64_rsi, Reg64s.get64_rdx, UInt64.toNat_toBitVec]
  rw [e8r, hgA plo, hgA phi, hgA mode]
  have hOw : ∀ (d : DataMem) (g : GVar) (v : BitVec 64), g.id < tab.ng →
      Only (base + 16) (seqLayout tab base out hdrf ctlf hw).tabEnd d
        (wrW d (A ((seqLayout tab base out hdrf ctlf hw).globAddr g)) v) := fun d g v hg => by
    obtain ⟨h1, h2⟩ := hgS g hg
    refine (Only.wrW (by omega)).mono ?_ h2
    simp only [Layout.globAddr, Layout.globStart, seqLayout_T]; omega
  have hOg := ((hOw s1.dmem plo s1.regs.rsi.toBitVec hngl).union (hOw _ phi s1.regs.rdx.toBitVec hngh)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)).union (hOw _ mode (UInt64.toBitVec 2) hngm)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  have hOall := hO1.union (a := base) (b := (seqLayout tab base out hdrf ctlf hw).tabEnd) hOg
    (Nat.le_refl _) (by omega) hSE (Nat.le_refl _)
  have hm0 := seq_memRel (out := out) (hdrf := hdrf) (ctlf := ctlf) (hw := hw) hok hp hfit dm.regs hc.hbase m dm.dmem hm
  have hcs := hc.hcs
  refine eventually_weaken _ _ _ _ ?_ (compile_correct_frame p "check" _ hG hwf _ hcC fd hentry []
    (by simp [hnp]) rfl (seqMem m mode plo phi out hdrf ctlf hw dm.regs.rsi dm.regs.rdx) abiFuel _ ra ?_ ?_ ?_ ?_ ?_
    (fun i h => absurd h (by simp)) ?_ ?_ ?_ ?_ ?_ ?_)
  · intro st ⟨hpc, hsp, hbp, h14, h15, ⟨hbx, h12, h13⟩, hfr, hout⟩
    refine ⟨hpc, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, MemFrame.only_tab (show MemFrame _ dm.regs.rsp.toNat _ _ by rw [← hRsp]; exact hfr) hOall, hout⟩
    · rw [hsp]; show s1.regs.rsp.toNat + 8 = _; rw [hRsp]
    · rw [hbp]; exact hRbp
    · rw [h14]; exact hR14
    · rw [h15]; exact hR15
    · rw [hbx]; exact UInt64.toBitVec_inj.mp (by simpa using hR1 .rbx (by decide))
    · rw [h12]; exact UInt64.toBitVec_inj.mp (by simpa using hR1 .r12 (by decide))
    · rw [h13]; exact UInt64.toBitVec_inj.mp (by simpa using hR1 .r13 (by decide))
  · exact e8r
  · show (abiFuel.toUInt64).toNat = abiFuel
    simp [abiFuel]
  · show MemRel _ _ (wrW (wrW (wrW s1.dmem _ s1.regs.rsi.toBitVec) _ s1.regs.rdx.toBitVec) _ (UInt64.toBitVec 2))
    rw [hs1, hRsi, hRdx]
    exact ((hm0.storeG hG (g := plo) hngl dm.regs.rsi).storeG hG (g := phi) hngh dm.regs.rdx).storeG hG
      (g := mode) hngm 2
  · simp only [seqLayout_lo, seqLayout_hi, abiStack]; omega
  · show rdW (wrW (wrW (wrW s1.dmem _ _) _ _) _ _) _ = _
    rw [hOg.rdW_eq (by simp only [seqLayout_T]; omega) (Or.inl (by simp only [seqLayout_T]; omega))]
    have := stores_rdW? dm.regs base _ dm.dmem 0 _ (seqVals_getElem? hnb out hdrf ctlf hw).1 hend
    rw [addr_val _ _ (by rw [hc.hbase]; simp only [abiSlot, abiStack]; omega), hc.hbase, ← hs1] at this
    simpa only [seqLayout_T, seqLayout_hi, Nat.mul_zero, Nat.add_zero, Nat.add_assoc] using this
  · show rdW (wrW (wrW (wrW s1.dmem _ _) _ _) _ _) (A s1.regs.rsp.toNat) = some ra
    rw [hRsp, ← hc.hra]
    refine rdW_congr fun j hj => ?_
    rw [A_add, hOall.same _ (by have := hc.hcs8; omega) ?_]
    rcases (hcs (dm.regs.rsp.toNat + j) (by omega) (by have := hc.hcs8; omega)).2 with h | h
    · left; omega
    · right; omega
  · intro x h1 h2
    change s1.regs.rsp.toNat - 24 ≤ x at h1
    change x < s1.regs.rsp.toNat + 8 at h2
    rw [hRsp] at h1 h2
    obtain ⟨hmx, hreg⟩ := hcs x h1 h2
    exact ⟨hOall.grows _ hmx, seq_out hok hp hneed hreg⟩
  · show 24 ≤ s1.regs.rsp.toNat
    rw [hRsp]; exact hc.hcs24
  · show s1.regs.rsp.toNat + 8 < 2 ^ 64
    rw [hRsp]; exact hc.hcs8
  · intro x h1 h2
    obtain ⟨q0, q1, q2, q3⟩ := seq_save hok hp h1 h2
    refine ⟨hOall.grows _ (hc.hmap x q0 q1), q2, q3, ?_⟩
    show x < s1.regs.rsp.toNat - 24 ∨ s1.regs.rsp.toNat + 8 ≤ x
    rw [hRsp]
    refine Classical.byContradiction fun hn => ?_
    simp only [not_or, Nat.not_lt, Nat.not_le] at hn
    rcases (hcs x (by omega) (by omega)).2 with h | h <;> omega
  · have := seq_save (x := (seqLayout tab base out hdrf ctlf hw).tabEnd) hok hp (Nat.le_refl _) (by omega)
    omega

end ConAgua.Final
