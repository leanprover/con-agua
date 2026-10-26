import ConAgua.Final.SeqAbi

/-!
# The sequential driver `ca_start` on the machine (lane parmode)

`drv_outcome`: the harness calls the driver `ca_start` (`AbiCall`; the region must be 16 bytes
larger than the setup stub's, `drvNeed`). The driver saves the caller's `r15` and its return
address past the setup stub's region (`drvSave`), calls entry 1 (`ca_start_a0`, `abiA0_outcome`) on the region
without them, and if that run returns `2^63 + k`, calls `ca_check_seq` (`abiS_outcome`) on the
same region for `[0, k)`. It returns to the caller with the callee-saved registers restored, and
if it reports `rdx = 0`, `rax = ACCEPT`, the two L runs did (`DrvAccepts`).
-/

namespace ConAgua.Final

open L L.Compiler

/-- **What an accepting driver run means**: both buffers are below `2^63` bytes (the setup stub
checked it), entry 1's run of `check` (mode word `3`) ends with result `r₁`, and either
`r₁ = ACCEPT` or `r₁ = 2^63 + k` (`9223372036854775808 = 2^63`) and entry 2's run from its memory
(`seqMem m₁ … 0 k`) ends with `ACCEPT`. -/
def DrvAccepts (p : Prog) (tab : Tab) (mode plo phi : GVar) (out hdrf ctlf : ArrId) (hw : Nat)
    (b pb : ByteArray) : Prop :=
  b.size < 2 ^ 63 ∧ pb.size < 2 ^ 63 ∧ ∃ rs1 m1, L.run p abiFuel "check" [] ((loadMem b pb [] (List.replicate tab.nw abiWords)).setG mode 3) =
      .ok (rs1, m1) ∧ m1.words.size = tab.nw ∧
    (rs1.getD 0 0 = ACCEPT ∨
      (2 ^ 63 ≤ (rs1.getD 0 0).toNat ∧ ∃ rs2 m2,
        L.run p abiFuel "check" [] (seqMem m1 mode plo phi out hdrf ctlf hw 0 (rs1.getD 0 0 - 9223372036854775808)) =
          .ok (rs2, m2) ∧ rs2.getD 0 0 = ACCEPT))

/-- **What a failing driver run means**: both buffers are below `2^63` bytes, and entry 1's run of
`check` fails with an error of code `k`, or it returns `2^63 + j` and entry 2's run from its memory
fails with an error of code `k`. -/
def DrvErr (p : Prog) (tab : Tab) (mode plo phi : GVar) (out hdrf ctlf : ArrId) (hw : Nat)
    (b pb : ByteArray) (k : Word) : Prop :=
  b.size < 2 ^ 63 ∧ pb.size < 2 ^ 63 ∧
  ((∃ e, L.run p abiFuel "check" [] ((loadMem b pb [] (List.replicate tab.nw abiWords)).setG mode 3) =
      .error e ∧ e.code = k) ∨
   (∃ rs1 m1, L.run p abiFuel "check" [] ((loadMem b pb [] (List.replicate tab.nw abiWords)).setG mode 3) =
      .ok (rs1, m1) ∧ m1.words.size = tab.nw ∧ 2 ^ 63 ≤ (rs1.getD 0 0).toNat ∧ ∃ e,
      L.run p abiFuel "check" [] (seqMem m1 mode plo phi out hdrf ctlf hw 0 (rs1.getD 0 0 - 9223372036854775808)) =
        .error e ∧ e.code = k))

/-- An entry's post with `rdx = 2`: the run failed, with the code in `rax`. -/
theorem err_of_entryOut {G : L.Compiler.Layout} {res : Except Err (List Word × Mem)} {s : MachineData}
    (h : s.regs.rdx = 1 ∨ OutcomeRel G res s) (h2 : s.regs.rdx = 2) :
    ∃ e, res = .error e ∧ s.regs.rax = e.code := by
  rcases h with h | h
  · rw [h2] at h; exact absurd h (by decide)
  rcases res with e | ⟨rs, m⟩
  · cases e with
    | outOfFuel => exact absurd h id
    | _ => exact ⟨_, rfl, h.2⟩
  · rw [h.1] at h2; exact absurd h2 (by decide)

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

/-- An address outside the region and the buffers is in none of the partition layout's parts. -/
theorem abiLayout_out {tab : Tab} (hok : abiTabOk tab = true) {base blen inp n pins np x : Nat}
    (hneed : abiNeed tab ≤ blen) (hreg : x < base ∨ base + blen ≤ x)
    (hin : ¬ (inp ≤ x ∧ x < inp + n)) (hpins : ¬ (pins ≤ x ∧ x < pins + np)) :
    ¬ (abiLayout tab base inp n pins np).InStack x ∧ ¬ (abiLayout tab base inp n pins np).InArr x ∧
      ¬ (abiLayout tab base inp n pins np).InTab x := by
  obtain ⟨hnb, htab, -⟩ := abiTabOk_spec hok
  have hneed' := hneed
  simp only [abiNeed, hnb, abiSlot] at hneed'
  refine ⟨?_, ?_, ?_⟩
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
    simp only [Layout.tabEnd, abiLayout_T, abiLayout_tab, abiLayout_nargs] at h3 h4
    omega


/-- The register-file simp set: writes as literals, reads as projections. -/
local macro "rsimp" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [Reg64s.set64_rax, Reg64s.set64_rcx, Reg64s.set64_rdx,
  Reg64s.set64_rsi, Reg64s.set64_rdi, Reg64s.set64_rsp, Reg64s.set64_rbp, Reg64s.set64_r8, Reg64s.set64_r9,
  Reg64s.set64_r11, Reg64s.set64_r14, Reg64s.set64_r15, Reg64s.get64_rax, Reg64s.get64_rcx, Reg64s.get64_rdx,
  Reg64s.get64_rsi, Reg64s.get64_rdi, Reg64s.get64_rsp, Reg64s.get64_r8, Reg64s.get64_r9, Reg64s.get64_r11,
  Reg64s.get64_r14, Reg64s.get64_r15, Reg64s.get64_rbp, Reg64s.rax_mk, Reg64s.rcx_mk, Reg64s.rdx_mk,
  Reg64s.rsi_mk, Reg64s.rdi_mk, Reg64s.rsp_mk, Reg64s.rbp_mk, Reg64s.r8_mk, Reg64s.r9_mk, Reg64s.r10_mk,
  Reg64s.r11_mk, Reg64s.r12_mk, Reg64s.r13_mk, Reg64s.r14_mk, Reg64s.r15_mk, Reg64s.rbx_mk,
  UInt64.toNat_toBitVec, UInt64.ofBitVec_toBitVec, UInt64.toBitVec_ofBitVec] $[$loc]?)

attribute [local simp] Reg64s.set64_rax Reg64s.set64_rcx Reg64s.set64_rdx Reg64s.set64_rsi Reg64s.set64_rdi
  Reg64s.set64_rsp Reg64s.set64_rbp Reg64s.set64_r8 Reg64s.set64_r9 Reg64s.set64_r11 Reg64s.set64_r14
  Reg64s.set64_r15

/-- **The sequential driver**: from `ca_start`, the machine returns to the caller with the
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
        (st.data.regs.rdx = 0 → st.data.regs.rax = ACCEPT → DrvAccepts p tab mode plo phi out hdrf ctlf hw b pb) ∧
        (st.data.regs.rdx = 2 → DrvErr p tab mode plo phi out hdrf ctlf hw b pb st.data.regs.rax))
      dm (label abiStartL) := by
  obtain ⟨hnb, htab, hneed64⟩ := abiTabOk_spec hok
  have hfits := hc.hfits
  have hcs8 := hc.hcs8
  have hcs24 := hc.hcs24
  have hcP := hcode.left
  simp only [parStub] at hcP
  have hcQ := hcP
  rw [List.append_assoc] at hcQ
  obtain ⟨K, hL3⟩ : ∃ K, Code _ K := ⟨_, hcQ.right.right⟩
  obtain ⟨base, hbase⟩ : ∃ base, dm.regs.r8.toNat = base := ⟨_, rfl⟩
  obtain ⟨rsp0, hrsp0⟩ : ∃ rsp0, dm.regs.rsp.toNat = rsp0 := ⟨_, rfl⟩
  have hn : abiNeed tab = abiSlot * (2 + tab.nw) := by simp [abiNeed, hnb]
  have hN31 : 2 ^ 31 ≤ abiNeed tab := by rw [hn]; simp only [abiSlot]; omega
  -- the common exit: the caller's `r15` and the return address back from the save area
  have hdone : ∀ s : MachineData, s.regs.r15.toNat = base → s.regs.rsp.toNat = rsp0 + 8 →
      s.regs.rbp = dm.regs.rbp → s.regs.r14 = dm.regs.r14 →
      s.regs.rbx = dm.regs.rbx → s.regs.r12 = dm.regs.r12 → s.regs.r13 = dm.regs.r13 →
      base + abiNeed tab + 16 < 2 ^ 64 →
      rdW s.dmem (A (base + abiNeed tab)) = some dm.regs.r15 →
      rdW s.dmem (A (base + abiNeed tab + 8)) = some ra → (rdW s.dmem (A rsp0)).isSome →
      (s.regs.rdx = 0 → s.regs.rax = ACCEPT → DrvAccepts p tab mode plo phi out hdrf ctlf hw b pb) →
      (s.regs.rdx = 2 → DrvErr p tab mode plo phi out hdrf ctlf hw b pb s.regs.rax) →
      Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ RegsRestored dm.regs st.data.regs ∧
        (st.data.regs.rdx = 0 → st.data.regs.rax = ACCEPT → DrvAccepts p tab mode plo phi out hdrf ctlf hw b pb) ∧
        (st.data.regs.rdx = 2 → DrvErr p tab mode plo phi out hdrf ctlf hw b pb st.data.regs.rax))
        s (label abiDrvDoneL) := by
    intro s h15 hsp hbp h14 hbx h12 h13 hfitS hw15 hwra hmsp hacc herr
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
    refine Eventually.done _ ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rsimp; rw [BitVec.sub_add_cancel]; show s.regs.rsp.toNat = _; rw [hsp, hrsp0]
    · rsimp; exact hbp
    · rsimp; exact h14
    · rsimp
    · rsimp; exact hbx
    · rsimp; exact h12
    · rsimp; exact h13
    · rsimp; exact hacc
    · rsimp; exact herr
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
    refine Eventually.done _ ⟨rfl, ⟨?_, by simp, by simp, by simp, by simp, by simp, by simp⟩,
      fun h => absurd h (by simp <;> decide), fun h => absurd h (by simp <;> decide)⟩
    simp only [Reg64s.set64_rsp, Reg64s.set64_rax, Reg64s.set64_rdx, UInt64.toNat_ofBitVec, BitVec.toNat_add,
      UInt64.toNat_toBitVec, show (8 : BitVec 64).toNat = 8 from rfl]
    omega
  -- the region is big enough: save the caller's `r15` and the return address, call entry 1
  have hdn64 : drvNeed tab < 2 ^ 64 := by simp only [drvNeed, hn, abiSlot] at *; omega
  simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not, Reg64s.get64_r9, Reg64s.set64_rax,
    UInt64.toNat_toBitVec, Nat.not_lt] at hge
  have hge' : drvNeed tab ≤ dm.regs.r9.toNat := by
    simpa [Nat.toUInt64, UInt64.toNat_ofNat, Nat.mod_eq_of_lt hdn64] using hge
  have hge2 := hge'
  simp only [drvNeed] at hge2
  have hcs := hc.hcs
  have hz := hc.hzero
  rw [hbase, hrsp0] at hcs
  rw [hbase] at hz
  rw [hbase] at hfits
  rw [hrsp0] at hcs8 hcs24
  -- the save area is in the region, so apart from the return-address slot
  have hsvA : ∀ x, base + abiNeed tab ≤ x → x < base + abiNeed tab + 16 → x < rsp0 - 24 ∨ rsp0 + 8 ≤ x := by
    intro x h1 h2
    refine Classical.byContradiction fun hn' => ?_
    simp only [not_or, Nat.not_lt, Nat.not_le] at hn'
    rcases (hcs x (by omega) (by omega)).2.1 with h | h <;> omega
  have hsa0 : (BinOp.add.eval (drvSave tab).toUInt64 dm.regs.r8).toNat = base + abiNeed tab := by
    simp only [BinOp.eval, UInt64.toNat_add, drvSave, hbase, Nat.toUInt64]
    rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
    omega
  have hra0 : rdW dm.dmem (A rsp0) = some ra := by rw [← hrsp0]; exact hc.hra
  refine ev_movRI (Code.get (i := 11) hL3 rfl) ?_
  refine ev_binO (op := .add) (o := oR .r8) rfl (Code.get (i := 12) hL3 rfl)
    (Or.inr (Or.inr ⟨.r8, rfl, rfl⟩)) fun st0 => ?_
  refine ev_movMR (Code.get (i := 13) hL3 rfl) ⟨by decide, by decide⟩ ?_ ?_
  · rsimp; rw [hsa0]
    exact isSome_rdW fun j hj => by rw [A_add]; rw [hz _ (by omega) (by omega)]; rfl
  refine ev_pop (Code.get (i := 14) hL3 rfl) (v := ra) ?_ ?_
  · rsimp; rw [hsa0, toBitVec_eq_A dm.regs.rsp, hrsp0, Int.toNat_zero, Nat.add_zero,
      rdW_wrW_A (by omega) (by omega) (by rcases hsvA (base + abiNeed tab) (by omega) (by omega) with h | h <;> omega)]
    exact hra0
  refine ev_movMR (Code.get (i := 15) hL3 rfl) ⟨by decide, by decide⟩ ?_ ?_
  · rsimp; rw [hsa0]
    exact isSome_rdW fun j hj => by
      rw [A_add]; exact isSome_get?_storeInt (by rw [show base + abiNeed tab + Int.toNat 8 + j = base + abiNeed tab + 8 + j from rfl, hz _ (by omega) (by omega)]; rfl)
  refine ev_movRR (Code.get (i := 16) hL3 rfl) ?_
  refine ev_movRI (Code.get (i := 17) hL3 rfl) ?_
  have e1 : (UInt64.ofBitVec (dm.regs.rsp.toBitVec + 8)).toBitVec - 8 = A rsp0 := by
    rw [UInt64.toBitVec_ofBitVec, BitVec.add_sub_cancel, toBitVec_eq_A, hrsp0]
  refine ev_call (Code.get (i := 18) hL3 rfl) ?_ ?_
  · rsimp; rw [e1, hsa0, Int.toNat_zero, Nat.add_zero, show Int.toNat 8 = 8 from rfl,
      rdW_wrW_A (by omega) (by omega) (by rcases hsvA (base + abiNeed tab + 8) (by omega) (by omega) with h | h <;> omega),
      rdW_wrW_A (by omega) (by omega) (by rcases hsvA (base + abiNeed tab) (by omega) (by omega) with h | h <;> omega),
      hra0]; rfl
  rsimp
  rw [e1, hsa0, Int.toNat_zero, Nat.add_zero, show Int.toNat 8 = 8 from rfl]
  refine ev_seq (abiA0_outcome p tab hok hwf mode plo phi out hdrf ctlf hw fz own hngm k0 hcode fd hentry hnp
    b pb _ (UInt64.ofBitVec (at_ (K + 18 + 1)).toBitVec) ?_) ?_
  · have hneedN : ((abiNeed tab).toUInt64).toNat = abiNeed tab :=
      UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
    refine hc.shrink _ _ rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_
    · rw [← hrsp0, ← toBitVec_eq_A]
    · show ((abiNeed tab).toUInt64).toNat ≤ _
      rw [hneedN]; omega
    · exact fun y hy => isSome_get?_storeInt (isSome_get?_storeInt (isSome_get?_storeInt hy))
    · intro x hx h1 h2
      change x < dm.regs.r8.toNat + ((abiNeed tab).toUInt64).toNat ∨ _ at h1
      rw [hneedN, hbase] at h1
      rw [hbase, hrsp0] at *
      rw [get?_wrW_A (by omega) hx (by omega), get?_wrW_A (by omega) hx (by omega),
        get?_wrW_A (by omega) hx (by omega)]
    · rw [hrsp0, rdW_wrW_same]
  -- entry 1 returned
  intro st ⟨⟨hpc, hRR, hfr, hout⟩, hsz⟩
  obtain ⟨hsp1, hbp1, h141, h151, hbx1, h121, h131⟩ := hRR
  simp only at hsp1 hbp1 h141 h151 hbx1 h121 h131 hfr hout
  unfold SizesPost at hsz
  rw [hpc]
  simp only [Int64.ofBitVec_toBitVec]
  have hsp1' : st.data.regs.rsp.toNat = rsp0 + 8 := by
    rw [hsp1]; show (A rsp0).toNat + 8 = _; simp only [A, BitVec.toNat_ofNat]; omega
  rw [hbase] at hfr hout
  generalize st.data = s1 at *
  -- the save area is in no part of the layouts
  have hbufS : ∀ x, base + abiNeed tab ≤ x → x < base + abiNeed tab + 16 →
      ¬ (dm.regs.rdi.toNat ≤ x ∧ x < dm.regs.rdi.toNat + b.size) ∧
      ¬ (dm.regs.rdx.toNat ≤ x ∧ x < dm.regs.rdx.toNat + pb.size) := by
    intro x h1 h2
    refine ⟨fun ⟨h3, h4⟩ => ?_, fun ⟨h3, h4⟩ => ?_⟩
    · rcases hc.hinDisj x h3 h4 with h | h <;> omega
    · rcases hc.hpinsDisj x h3 h4 with h | h <;> omega
  have hsvL : ∀ x, base + abiNeed tab ≤ x → x < base + abiNeed tab + 16 →
      ¬ (abiLayout tab base dm.regs.rdi.toNat b.size dm.regs.rdx.toNat pb.size).InStack x ∧
      ¬ (abiLayout tab base dm.regs.rdi.toNat b.size dm.regs.rdx.toNat pb.size).InArr x ∧
      ¬ (abiLayout tab base dm.regs.rdi.toNat b.size dm.regs.rdx.toNat pb.size).InTab x :=
    fun x h1 h2 => abiLayout_out hok (blen := abiNeed tab) (Nat.le_refl _) (Or.inr h1) (hbufS x h1 h2).1
      (hbufS x h1 h2).2
  have hsv1 : ∀ y, base + abiNeed tab ≤ y → y + 8 ≤ base + abiNeed tab + 16 →
      rdW s1.dmem (A y) = rdW (wrW (wrW (wrW dm.dmem (A (base + abiNeed tab)) dm.regs.r15.toBitVec)
        (A (base + abiNeed tab + 8)) ra.toBitVec) (A rsp0) (at_ (K + 19)).toBitVec) (A y) := by
    intro y h1 h2
    refine rdW_congr fun j hj => ?_
    rw [A_add]
    obtain ⟨q1, q2, q3⟩ := hsvL (y + j) (by omega) (by omega)
    exact hfr.same _ (by omega) q1 q2 q3 (by rcases hsvA (y + j) (by omega) (by omega) with h | h <;> omega)
      (Or.inr (by simp only [Layout.tabEnd, abiLayout_T, abiLayout_tab, abiLayout_nargs]; omega))
  have hw15 : rdW s1.dmem (A (base + abiNeed tab)) = some dm.regs.r15 := by
    rw [hsv1 _ (Nat.le_refl _) (by omega),
      rdW_wrW_A (by omega) (by omega) (by rcases hsvA (base + abiNeed tab) (by omega) (by omega) with h | h <;> omega),
      rdW_wrW_A (by omega) (by omega) (by omega), rdW_wrW_same]
  have hwra : rdW s1.dmem (A (base + abiNeed tab + 8)) = some ra := by
    rw [hsv1 _ (by omega) (by omega),
      rdW_wrW_A (by omega) (by omega) (by rcases hsvA (base + abiNeed tab + 8) (by omega) (by omega) with h | h <;> omega),
      rdW_wrW_same]
  have hwin : ∀ x, rsp0 - 24 ≤ x → x < rsp0 + 8 → (s1.dmem.get? (A x)).isSome := fun x h1 h2 =>
    hfr.grows _ (isSome_get?_storeInt (isSome_get?_storeInt (isSome_get?_storeInt (hcs x h1 h2).1)))
  have hmsp : (rdW s1.dmem (A rsp0)).isSome :=
    isSome_rdW fun j hj => by rw [A_add]; exact hwin _ (by omega) (by omega)
  have h15b : s1.regs.r15.toNat = base := by rw [h151, hbase]
  refine ev_cmpRO (r := .rdx) (o := oI 0) (v := 0) (Code.get (i := 19) hL3 rfl) (Or.inl rfl) ?_
  refine ev_jcc (Code.get (i := 20) hL3 rfl) (fun hnz => ?_) (fun hz0 => ?_)
  · -- entry 1 reported an error or exhaustion
    refine hdone _ h15b hsp1' hbp1 h141 hbx1 h121 h131 (by omega) hw15 hwra hmsp (fun h0 => ?_) (fun h2 => ?_)
    · simp only [CondCode.interp, cmpFlags_zf, Reg64s.get64_rdx] at hnz
      exact absurd hnz (by rw [h0]; decide)
    · obtain ⟨hb, hpb⟩ := hsz.resolve_left (by rw [h2]; decide)
      obtain ⟨e, he, hk⟩ := err_of_entryOut hout h2
      exact ⟨hb, hpb, .inl ⟨e, he, hk.symm⟩⟩
  simp only [CondCode.interp, cmpFlags_zf, Reg64s.get64_rdx] at hz0
  have hrdx0 : s1.regs.rdx = 0 := by
    simp only [Bool.not_eq_false', beq_iff_eq] at hz0
    exact UInt64.toBitVec_inj.mp hz0
  have hout' := hout.resolve_left (by rw [hrdx0]; decide)
  obtain ⟨hb, hpb⟩ := hsz.resolve_left (by rw [hrdx0]; decide)
  rcases hres : L.run p abiFuel "check" [] ((loadMem b pb [] (List.replicate tab.nw abiWords)).setG mode 3)
    with e | ⟨rs1, m1⟩
  · rw [hres] at hout'
    cases e <;> simp only [OutcomeRel] at hout' <;> (rw [hrdx0] at hout'; exact absurd hout'.1 (by decide))
  rw [hres] at hout'
  obtain ⟨-, hRes, hMem⟩ := hout'
  have hrax : s1.regs.rax = rs1.getD 0 0 := hRes.1 0 (by simp only [abiLayout_tab]; omega) (by decide)
  have hnw1 : m1.words.size = tab.nw := by simpa only [abiLayout_tab] using hMem.nw
  refine ev_movRI (Code.get (i := 21) hL3 rfl) ?_
  refine ev_cmpRO (r := .rax) (o := oR .rcx) (v := (9223372036854775808 : Word)) (Code.get (i := 22) hL3 rfl)
    (Or.inr (Or.inr ⟨.rcx, rfl, rfl⟩)) ?_
  refine ev_jcc (Code.get (i := 23) hL3 rfl) (fun hlt => ?_) (fun hge3 => ?_)
  · -- entry 1 finished without pending work: its result is the result
    refine hdone _ h15b hsp1' hbp1 h141 hbx1 h121 h131 (by omega) hw15 hwra hmsp (fun _ hacc => ⟨hb, hpb, rs1, m1, hres, hnw1, Or.inl ?_⟩)
      (fun h2 => absurd (hrdx0 ▸ h2) (by decide))
    rw [← hrax]; exact hacc
  simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not, Nat.not_lt] at hge3
  rsimp at hge3
  refine ev_binO (op := .sub) (o := oR .rcx) rfl (Code.get (i := 24) hL3 rfl)
    (Or.inr (Or.inr ⟨.rcx, rfl, rfl⟩)) fun st1 => ?_
  refine ev_movRR (Code.get (i := 25) hL3 rfl) ?_
  refine ev_movRI (Code.get (i := 26) hL3 rfl) ?_
  refine ev_movRR (Code.get (i := 27) hL3 rfl) ?_
  have e2 : s1.regs.rsp.toBitVec - 8 = A rsp0 := by
    rw [toBitVec_eq_A s1.regs.rsp, hsp1', A_sub8 _ (by omega) (by omega)]; rfl
  refine ev_call (Code.get (i := 28) hL3 rfl) ?_ ?_
  · rsimp; rw [e2]; exact hmsp
  rsimp
  rw [e2]
  refine ev_seq (abiS_outcome p tab hok hwf mode plo phi out hdrf ctlf hw fz own hngm hngl hngh hp k0 hcode fd
    hentry hnp (base := base) (blen := abiNeed tab) (inp := dm.regs.rdi.toNat) (n := b.size) (pins := dm.regs.rdx.toNat)
    (np := pb.size) m1 _ (UInt64.ofBitVec (at_ (K + 28 + 1)).toBitVec) ?_ ?_) ?_
  · have hA0 : ({ toBitVec := A rsp0 } : UInt64).toNat = rsp0 := by
      show (A rsp0).toNat = rsp0; simp only [A, BitVec.toNat_ofNat]; omega
    refine ⟨Nat.le_refl _, by omega, h15b, fun x h1 h2 => ?_, ?_, fun x h1 h2 => ?_, ?_, ?_⟩
    · exact isSome_get?_storeInt (hfr.grows _ (isSome_get?_storeInt (isSome_get?_storeInt
        (isSome_get?_storeInt (by rw [hz x h1 (by simp only [hn, abiSlot] at hge2 ⊢; omega)]; rfl)))))
    · show rdW _ (A ({ toBitVec := A rsp0 } : UInt64).toNat) = _
      rw [hA0, rdW_wrW_same]
    · change ({ toBitVec := A rsp0 } : UInt64).toNat - 24 ≤ x at h1
      change x < ({ toBitVec := A rsp0 } : UInt64).toNat + 8 at h2
      rw [hA0] at h1 h2
      refine ⟨isSome_get?_storeInt (hwin x h1 h2), ?_⟩
      rcases (hcs x h1 h2).2.1 with h | h <;> omega
    · show 24 ≤ ({ toBitVec := A rsp0 } : UInt64).toNat
      rw [hA0]; omega
    · show ({ toBitVec := A rsp0 } : UInt64).toNat + 8 < 2 ^ 64
      rw [hA0]; omega
  · have hG1 := abiLayout_ok hok (abiCall_geom hc (tab := tab) (by omega))
    rw [hbase] at hG1
    refine hMem.only' hG1 (Only.wrW (x := rsp0) (by omega)) fun x h1 h2 => ?_
    obtain ⟨-, hreg, hin, hpins⟩ := hcs x (by omega) (by omega)
    obtain ⟨-, q2, q3⟩ := abiLayout_out hok (blen := dm.regs.r9.toNat) (by omega) hreg hin hpins
    exact ⟨q3, q2⟩
  -- entry 2 returned
  intro st ⟨hpc, hRR, hfr2, hout2⟩
  obtain ⟨hsp2, hbp2, h142, h152, hbx2, h122, h132⟩ := hRR
  simp only at hsp2 hbp2 h142 h152 hbx2 h122 h132 hfr2 hout2
  rw [hpc]
  simp only [Int64.ofBitVec_toBitVec]
  rw [show at_ (K + 28 + 1) = label abiDrvDoneL from (Code.label (i := 29) hL3 rfl).symm]
  have hA0 : ({ toBitVec := A rsp0 } : UInt64).toNat = rsp0 := by
    show (A rsp0).toNat = rsp0; simp only [A, BitVec.toNat_ofNat]; omega
  rw [hA0] at hsp2 hfr2
  generalize st.data = s2 at *
  have hsv2 : ∀ y, base + abiNeed tab ≤ y → y + 8 ≤ base + abiNeed tab + 16 →
      rdW s2.dmem (A y) = rdW s1.dmem (A y) := by
    intro y h1 h2
    refine rdW_congr fun j hj => ?_
    rw [A_add]
    obtain ⟨q1, q2, q3⟩ := seq_out (base := base) (out := out) (hdrf := hdrf) (ctlf := ctlf) (hw := hw) hok hp
      (blen := abiNeed tab) (Nat.le_refl _) (x := y + j) (Or.inr (by omega))
    have hw' := hsvA (y + j) (by omega) (by omega)
    rw [hfr2.same _ (by omega) q1 q2 q3 (by rcases hw' with h | h <;> omega)
      (Or.inr (by simp only [Layout.tabEnd, seqLayout_T, seqLayout_tab, seqLayout_nargs]; omega)),
      get?_wrW_A (by omega) (by omega) (by rcases hw' with h | h <;> omega)]
  refine hdone s2 (by rw [h152]; exact h15b) (by rw [hsp2]) (hbp2.trans hbp1) (h142.trans h141)
    (hbx2.trans hbx1) (h122.trans h121) (h132.trans h131) (by omega)
    (by rw [hsv2 _ (Nat.le_refl _) (by omega)]; exact hw15) (by rw [hsv2 _ (by omega) (by omega)]; exact hwra)
    (isSome_rdW fun j hj => by
      rw [A_add]; exact hfr2.grows _ (isSome_get?_storeInt (hwin _ (by omega) (by omega)))) (fun h0 hax => ?_)
    (fun h2 => ?_)
  rotate_left
  · obtain ⟨e, he, hk⟩ := err_of_entryOut hout2 h2
    refine ⟨hb, hpb, .inr ⟨rs1, m1, hres, hnw1, ?_, e, ?_, hk.symm⟩⟩
    · rw [← hrax]; simpa using hge3
    · rw [← hrax]; exact he
  have hout2' := hout2.resolve_left (by rw [h0]; decide)
  rcases hres2 : L.run p abiFuel "check" [] (seqMem m1 mode plo phi out hdrf ctlf hw 0
      (BinOp.sub.eval s1.regs.rax 9223372036854775808)) with e | ⟨rs2, m2⟩
  · rw [hres2] at hout2'
    cases e <;> simp only [OutcomeRel] at hout2' <;> (rw [h0] at hout2'; exact absurd hout2'.1 (by decide))
  rw [hres2] at hout2'
  obtain ⟨-, hRes2, -⟩ := hout2'
  have hrax2 : s2.regs.rax = rs2.getD 0 0 := hRes2.1 0 (by simp only [seqLayout_tab]; omega) (by decide)
  refine ⟨hb, hpb, rs1, m1, hres, hnw1, Or.inr ⟨?_, rs2, m2, ?_, by rw [← hrax2]; exact hax⟩⟩
  · rw [← hrax]; simpa using hge3
  · rw [← hrax]; exact hres2

end ConAgua.Final
