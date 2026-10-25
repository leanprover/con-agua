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

end ConAgua.Final
