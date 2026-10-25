import ConAgua.Final.SeqAbi

/-!
# The sequential driver `ca_start_drv` on the machine (lane parmode)

`drv_outcome`: the harness calls `ca_start_drv` as it calls `ca_start` (`AbiCall`; the region
must be 16 bytes larger, `drvNeed`). The driver saves the caller's `r15` and its return address
past `ca_start`'s region (`drvSave`), calls entry 1 (`ca_start_a0`, `abiA0_outcome`) on the region
without them, and if that run returns `2^63 + k`, calls `ca_check_seq` (`abiS_outcome`) on the
same region for `[0, k)`. It returns to the caller with the callee-saved registers restored, and
if it reports `rdx = 0`, `rax = ACCEPT`, the two L runs did (`DrvAccepts`).
-/

namespace ConAgua.Final

open L L.Compiler

/-- **What an accepting driver run means**: entry 1's run of `check` (mode word `3`) ends with
result `r₁`, and either `r₁ = ACCEPT` or `r₁ = 2^63 + k` and entry 2's run from its memory
(`seqMem m₁ … 0 k`) ends with `ACCEPT`. -/
def DrvAccepts (p : Prog) (tab : Tab) (mode plo phi : GVar) (out hdrf ctlf : ArrId) (hw : Nat)
    (b pb : ByteArray) : Prop :=
  ∃ rs1 m1, L.run p abiFuel "check" [] ((loadMem b pb [] (List.replicate tab.nw abiWords)).setG mode 3) =
      .ok (rs1, m1) ∧
    (rs1.getD 0 0 = ACCEPT ∨
      (2 ^ 63 ≤ (rs1.getD 0 0).toNat ∧ ∃ rs2 m2,
        L.run p abiFuel "check" [] (seqMem m1 mode plo phi out hdrf ctlf hw 0 (rs1.getD 0 0 - 2 ^ 63)) =
          .ok (rs2, m2) ∧ rs2.getD 0 0 = ACCEPT))

/-- Two runs in sequence. -/
theorem ev_seq [Host] {P Q : MachineState → Prop} {s : MachineData} {pc : Int64} (h : Ev P s pc)
    (k : ∀ st, P st → Ev Q st.data st.pc) : Ev Q s pc :=
  eventually_trans _ P Q ⟨s, pc⟩ h fun st hst => k st hst

/-- **`AbiCall` on a smaller region**: the same buffers, the region `[base, base + n9)` of the
caller's, a memory that differs from the caller's at most past `n9` in the region and in the
return-address slot, and a new return address. -/
theorem AbiCall.shrink {b pb : ByteArray} {dm : MachineData} {ra : Word} (hc : AbiCall b pb dm ra)
    (dm' : MachineData) (ra' : Word)
    (hdi : dm'.regs.rdi = dm.regs.rdi) (hsi : dm'.regs.rsi = dm.regs.rsi) (hdx : dm'.regs.rdx = dm.regs.rdx)
    (hcx : dm'.regs.rcx = dm.regs.rcx) (h8 : dm'.regs.r8 = dm.regs.r8) (hsp : dm'.regs.rsp = dm.regs.rsp)
    (h9 : dm'.regs.r9.toNat ≤ dm.regs.r9.toNat)
    (hgrow : ∀ y, (dm.dmem.get? y).isSome → (dm'.dmem.get? y).isSome)
    (hsame : ∀ x < 2 ^ 64, (x < dm.regs.r8.toNat + dm'.regs.r9.toNat ∨ dm.regs.r8.toNat + dm.regs.r9.toNat ≤ x) →
      (x < dm.regs.rsp.toNat ∨ dm.regs.rsp.toNat + 8 ≤ x) → dm'.dmem.get? (A x) = dm.dmem.get? (A x))
    (hra : rdW dm'.dmem (A dm.regs.rsp.toNat) = some ra') : AbiCall b pb dm' ra' := by
  have hfits := hc.hfits
  have hcs := hc.hcs
  have hcs8 := hc.hcs8
  -- a byte of a buffer is outside the region and outside the return-address slot
  have hbuf : ∀ x, (dm.regs.rdi.toNat ≤ x ∧ x < dm.regs.rdi.toNat + b.size) ∨
      (dm.regs.rdx.toNat ≤ x ∧ x < dm.regs.rdx.toNat + pb.size) → dm'.dmem.get? (A x) = dm.dmem.get? (A x) := by
    intro x hx
    have hreg : x < dm.regs.r8.toNat ∨ dm.regs.r8.toNat + dm.regs.r9.toNat ≤ x := by
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hc.hinDisj x h1 h2
      · exact hc.hpinsDisj x h1 h2
    have hx64 : x < 2 ^ 64 := by
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have := hc.hinEnd; omega
      · have := hc.hpinsEnd; omega
    refine hsame x hx64 (by omega) ?_
    refine Classical.byContradiction fun hn => ?_
    simp only [not_or, Nat.not_lt, Nat.not_le] at hn
    obtain ⟨-, -, hin, hpins⟩ := hcs x (by omega) (by omega)
    rcases hx with h | h
    · exact hin h
    · exact hpins h
  refine
    { hin := fun i hi => ?_
      hn := by rw [hsi]; exact hc.hn
      hpins := fun i hi => ?_
      hnp := by rw [hcx]; exact hc.hnp
      hzero := fun x h1 h2 => ?_
      hfits := by rw [h8]; omega
      hinEnd := by rw [hdi]; exact hc.hinEnd
      hpinsEnd := by rw [hdx]; exact hc.hpinsEnd
      hinDisj := fun x h1 h2 => ?_
      hpinsDisj := fun x h1 h2 => ?_
      hbufDisj := fun x h1 h2 => ?_
      hra := by rw [hsp]; exact hra
      hcs := fun x h1 h2 => ?_
      hcs24 := by rw [hsp]; exact hc.hcs24
      hcs8 := by rw [hsp]; exact hc.hcs8 }
  · rw [hdi] at *
    rw [hbuf _ (Or.inl ⟨by omega, by omega⟩)]; exact hc.hin i hi
  · rw [hdx] at *
    rw [hbuf _ (Or.inr ⟨by omega, by omega⟩)]; exact hc.hpins i hi
  · rw [h8] at h1 h2
    rw [hsame x (by omega) (Or.inl h2) ?_]
    · exact hc.hzero x h1 (by omega)
    · refine Classical.byContradiction fun hn => ?_
      simp only [not_or, Nat.not_lt, Nat.not_le] at hn
      rcases (hcs x (by omega) (by omega)).2.1 with h | h <;> omega
  · rw [hdi] at h1 h2; rw [h8]
    rcases hc.hinDisj x h1 h2 with h | h <;> omega
  · rw [hdx] at h1 h2; rw [h8]
    rcases hc.hpinsDisj x h1 h2 with h | h <;> omega
  · rw [hdi] at h1 h2; rw [hdx]; exact hc.hbufDisj x h1 h2
  · rw [hsp] at h1 h2
    obtain ⟨hm, hreg, hin, hpins⟩ := hcs x h1 h2
    refine ⟨hgrow _ hm, ?_, by rw [hdi]; exact hin, by rw [hdx]; exact hpins⟩
    rw [h8]; omega

set_option linter.unusedSimpArgs false

/-- The register-file simp set: writes as literals, reads as projections. -/
local macro "rsimp" : tactic => `(tactic| simp only [Reg64s.set64_rax, Reg64s.set64_rcx, Reg64s.set64_rdx,
  Reg64s.set64_rsi, Reg64s.set64_rdi, Reg64s.set64_rsp, Reg64s.set64_rbp, Reg64s.set64_r8, Reg64s.set64_r9,
  Reg64s.set64_r11, Reg64s.set64_r14, Reg64s.set64_r15, Reg64s.get64_rax, Reg64s.get64_rcx, Reg64s.get64_rdx,
  Reg64s.get64_rsi, Reg64s.get64_rdi, Reg64s.get64_rsp, Reg64s.get64_r8, Reg64s.get64_r9, Reg64s.get64_r11,
  Reg64s.get64_r14, Reg64s.get64_r15, Reg64s.get64_rbp, Reg64s.rax_mk, Reg64s.rcx_mk, Reg64s.rdx_mk,
  Reg64s.rsi_mk, Reg64s.rdi_mk, Reg64s.rsp_mk, Reg64s.rbp_mk, Reg64s.r8_mk, Reg64s.r9_mk, Reg64s.r10_mk,
  Reg64s.r11_mk, Reg64s.r12_mk, Reg64s.r13_mk, Reg64s.r14_mk, Reg64s.r15_mk, Reg64s.rbx_mk,
  UInt64.toNat_toBitVec, UInt64.ofBitVec_toBitVec, UInt64.toBitVec_ofBitVec])

attribute [local simp] Reg64s.set64_rax Reg64s.set64_rcx Reg64s.set64_rdx Reg64s.set64_rsi Reg64s.set64_rdi
  Reg64s.set64_rsp Reg64s.set64_rbp Reg64s.set64_r8 Reg64s.set64_r9 Reg64s.set64_r11 Reg64s.set64_r14
  Reg64s.set64_r15

/-- **The sequential driver**: from `ca_start_drv`, the machine returns to the caller with the
callee-saved registers restored, and if it reports `rdx = 0` with `rax = ACCEPT`, the driver's
two L runs accepted (`DrvAccepts`). -/
theorem drv_outcome [Host] (p : Prog) (tab : Tab) (hok : abiTabOk tab = true)
    (hwf : Prog.wf tab p = true) (hnres : 1 ≤ tab.nres) (mode plo phi : GVar) (out hdrf ctlf : ArrId)
    (hw : Nat) (fz own : List ArrId) (hngm : mode.id < tab.ng) (hngl : plo.id < tab.ng)
    (hngh : phi.id < tab.ng) (hp : seqParamsOk tab out hdrf ctlf hw = true) (k0 : Nat)
    (hcode : Code (parStub tab mode plo phi out hdrf ctlf hw fz own ++ (abiStub tab ++ compileProg tab p "check")) k0)
    (fd : FunDecl) (hentry : p.lookup "check" = some fd) (hnp : fd.nparams = 0)
    (b pb : ByteArray) (dm : MachineData) (ra : Word) (hc : AbiCall b pb dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ RegsRestored dm.regs st.data.regs ∧
        (st.data.regs.rdx = 0 → st.data.regs.rax = ACCEPT → DrvAccepts p tab mode plo phi out hdrf ctlf hw b pb))
      dm (label abiDrvL) := by
  obtain ⟨hnb, htab, hneed64⟩ := abiTabOk_spec hok
  have hfits := hc.hfits
  have hcs8 := hc.hcs8
  have hcs24 := hc.hcs24
  have hcP := hcode.left
  simp only [parStub] at hcP
  have hcQ := hcP
  rw [List.append_assoc] at hcQ
  have hL3 := hcQ.right.right
  obtain ⟨base, hbase⟩ : ∃ base, dm.regs.r8.toNat = base := ⟨_, rfl⟩
  obtain ⟨rsp0, hrsp0⟩ : ∃ rsp0, dm.regs.rsp.toNat = rsp0 := ⟨_, rfl⟩
  have hn : abiNeed tab = abiSlot * (2 + tab.nw) := by simp [abiNeed, hnb]
  -- the common exit: the caller's `r15` and the return address back from the save area
  have hdone : ∀ s : MachineData, s.regs.r15.toNat = base → s.regs.rsp.toNat = rsp0 + 8 →
      s.regs.rbp = dm.regs.rbp → s.regs.r14 = dm.regs.r14 →
      base + abiNeed tab + 16 < 2 ^ 64 →
      rdW s.dmem (A (base + abiNeed tab)) = some dm.regs.r15 →
      rdW s.dmem (A (base + abiNeed tab + 8)) = some ra → (rdW s.dmem (A rsp0)).isSome →
      (s.regs.rdx = 0 → s.regs.rax = ACCEPT → DrvAccepts p tab mode plo phi out hdrf ctlf hw b pb) →
      Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ RegsRestored dm.regs st.data.regs ∧
        (st.data.regs.rdx = 0 → st.data.regs.rax = ACCEPT → DrvAccepts p tab mode plo phi out hdrf ctlf hw b pb))
        s (label abiDrvDoneL) := by
    intro s h15 hsp hbp h14 hfitS hw15 hwra hmsp hacc
    rw [Code.label (i := 29) hL3 rfl]
    refine ev_label (Code.get (i := 29) hL3 rfl) ?_
    refine ev_movRR (Code.get (i := 30) hL3 rfl) ?_
    refine ev_movRI (Code.get (i := 31) hL3 rfl) ?_
    refine ev_binO (op := .add) (o := oR .r15) rfl (Code.get (i := 32) hL3 rfl)
      (Or.inr (Or.inr ⟨.r15, rfl, rfl⟩)) fun st => ?_
    have hsa : (BinOp.add.eval (drvSave tab).toUInt64 s.regs.r15).toNat = base + abiNeed tab := by
      simp only [BinOp.eval, UInt64.toNat_add, drvSave, h15, Nat.toUInt64]
      rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
      omega
    refine ev_movRM (Code.get (i := 33) hL3 rfl) ⟨by decide, by decide⟩ (v := ra) ?_ ?_
    · rsimp; rw [hsa]; exact hwra
    refine ev_movRM (Code.get (i := 34) hL3 rfl) ⟨by decide, by decide⟩ (v := dm.regs.r15) ?_ ?_
    · rsimp; rw [hsa]; exact hw15
    refine ev_movRR (Code.get (i := 35) hL3 rfl) ?_
    have e1 : s.regs.rsp.toBitVec - 8 = A rsp0 := by
      rw [toBitVec_eq_A, hsp, A_sub8 _ (by omega) (by omega)]; rfl
    refine ev_push (Code.get (i := 36) hL3 rfl) ?_ ?_
    · rsimp; rw [e1]; exact hmsp
    refine ev_ret (Code.get (i := 37) hL3 rfl) (ra := ra) ?_ ?_
    · rsimp; rw [rdW_wrW_same]
    refine Eventually.done _ ⟨rfl, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rsimp; rw [BitVec.sub_add_cancel]; show s.regs.rsp.toNat = _; rw [hsp, hrsp0]
    · rsimp; exact hbp
    · rsimp; exact h14
    · rsimp
    · rsimp; exact hacc
  rw [Code.label (i := 7) hL3 rfl]
  refine ev_label (Code.get (i := 7) hL3 rfl) ?_
  refine ev_movRI (Code.get (i := 8) hL3 rfl) ?_
  refine ev_cmpRO (r := .r9) (o := oR .rax) (v := (drvNeed tab).toUInt64) (Code.get (i := 9) hL3 rfl)
    (Or.inr (Or.inr ⟨.rax, rfl, rfl⟩)) ?_
  refine ev_jcc (Code.get (i := 10) hL3 rfl) (fun hlt => ?_) (fun hge => ?_)
  · -- declined
    rw [Code.label (i := 38) hL3 rfl]
    refine ev_label (Code.get (i := 38) hL3 rfl) ?_
    refine ev_movRI (Code.get (i := 39) hL3 rfl) ?_
    refine ev_movRI (Code.get (i := 40) hL3 rfl) ?_
    refine ev_ret (Code.get (i := 41) hL3 rfl) (ra := ra)
      (by show rdW dm.dmem dm.regs.rsp.toBitVec = some ra; rw [toBitVec_eq_A]; exact hc.hra) ?_
    refine Eventually.done _ ⟨rfl, ⟨?_, by simp, by simp, by simp⟩, fun h => absurd h (by simp <;> decide)⟩
    simp only [Reg64s.set64_rsp, Reg64s.set64_rax, Reg64s.set64_rdx, UInt64.toNat_ofBitVec, BitVec.toNat_add,
      UInt64.toNat_toBitVec, show (8 : BitVec 64).toNat = 8 from rfl]
    omega
  sorry

end ConAgua.Final
