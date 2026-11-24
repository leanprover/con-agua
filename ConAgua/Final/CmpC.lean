module

public import ConAgua.Final.CmpMain
public import ConAgua.Final.SeqAbi
import ConAgua.Final.DrvAbi
import Kraken.X64.Registers

@[expose] public section

/-!
# `ca_start_c` on the machine: the sequential compared run (lane compare2)

`cmpC_outcome_regs`: the harness calls `ca_start_c` (`CmpCall`). The front (`cmp_front`: modes
`4`, `5`), mode `6` on the region as mode `5` left it (`cmp_modeR`), then entry 2 in place with the
mode word `8` over the solution's jobs `[0, kS)` (`ca_check_seq_m`, `abiSM_outcome`) and, unless
that does not accept, with the mode word `9` over the challenge's jobs `[0, kC)` on the region as
that run left it (`ca_check_seq_g`, `abiSG_outcome`). The return: the caller's registers, and an
accept or an error as `CmpAccS`, `CmpErrS` say.
-/

namespace ConAgua.Final

open L L.Compiler L.Arena

/-- The register-file simp set: writes as literals, reads as projections. -/
local macro "rsimp" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [Reg64s.set64_rax,
  Reg64s.set64_rcx, Reg64s.set64_rdx, Reg64s.set64_rsi, Reg64s.set64_rdi, Reg64s.set64_rsp, Reg64s.set64_rbp,
  Reg64s.set64_r8, Reg64s.set64_r9, Reg64s.set64_r10, Reg64s.set64_r11, Reg64s.set64_r14, Reg64s.set64_r15,
  Reg64s.get64_rax, Reg64s.get64_rcx, Reg64s.get64_rdx, Reg64s.get64_rsi, Reg64s.get64_rdi, Reg64s.get64_rsp,
  Reg64s.get64_r8, Reg64s.get64_r9, Reg64s.get64_r10, Reg64s.get64_r11, Reg64s.get64_r14, Reg64s.get64_r15,
  Reg64s.get64_rbp, Reg64s.rax_mk,
  Reg64s.rcx_mk, Reg64s.rdx_mk, Reg64s.rsi_mk, Reg64s.rdi_mk, Reg64s.rsp_mk, Reg64s.rbp_mk, Reg64s.r8_mk,
  Reg64s.r9_mk, Reg64s.r10_mk, Reg64s.r11_mk, Reg64s.r12_mk, Reg64s.r13_mk, Reg64s.r14_mk, Reg64s.r15_mk,
  Reg64s.rbx_mk, UInt64.toNat_toBitVec, UInt64.ofBitVec_toBitVec, UInt64.toBitVec_ofBitVec] $[$loc]?)

section
variable [Host] {tab : Tab}

omit [Host] in
/-- A store inside the setup stub's region (below the save area) keeps the frame. -/
theorem CmpFrame.wrR {dm : MachineData} {ra sa : Word} {nS base rsp0 : Nat} {s : MachineData}
    (hf : CmpFrame tab dm ra sa nS base rsp0 s) (hfit : base + abiNeed tab + 64 < 2 ^ 64) {y : Nat}
    {v : BitVec 64} (hy' : y + 8 ≤ base + abiNeed tab) :
    CmpFrame tab dm ra sa nS base rsp0 { s with dmem := wrW s.dmem (A y) v } := by
  have hsv : ∀ o, o + 8 ≤ 48 → rdW (wrW s.dmem (A y) v) (A (base + abiNeed tab + o)) =
      rdW s.dmem (A (base + abiNeed tab + o)) := fun o ho => rdW_wrW_A (by omega) (by omega) (by omega)
  refine ⟨hf.r15, hf.rsp, hf.rbp, hf.r14, hf.rbx, hf.r12, hf.r13,
    by rw [show base + abiNeed tab = base + abiNeed tab + 0 by rfl]; dsimp only; rw [hsv 0 (by omega)]; exact hf.sv0,
    by dsimp only; rw [hsv 8 (by omega)]; exact hf.sv1, by dsimp only; rw [hsv 16 (by omega)]; exact hf.sv2,
    by dsimp only; rw [hsv 24 (by omega)]; exact hf.sv3, by dsimp only; rw [hsv 32 (by omega)]; exact hf.sv4,
    by dsimp only; rw [hsv 40 (by omega)]; exact hf.sv5, fun x h1 h2 => isSome_get?_storeInt (hf.win x h1 h2),
    fun x h1 h2 => isSome_get?_storeInt (hf.map x h1 h2)⟩

omit [Host] in
/-- A write of `r10` keeps the frame. -/
theorem CmpFrame.setR10 {dm : MachineData} {ra sa : Word} {nS base rsp0 : Nat} {s : MachineData}
    (hf : CmpFrame tab dm ra sa nS base rsp0 s) (v : BitVec 64) :
    CmpFrame tab dm ra sa nS base rsp0 { s with regs := s.regs.set64 .r10 v } :=
  ⟨by simpa only [Reg64s.set64_r10] using hf.r15, by simpa only [Reg64s.set64_r10] using hf.rsp,
    by simpa only [Reg64s.set64_r10] using hf.rbp, by simpa only [Reg64s.set64_r10] using hf.r14,
    by simpa only [Reg64s.set64_r10] using hf.rbx, by simpa only [Reg64s.set64_r10] using hf.r12,
    by simpa only [Reg64s.set64_r10] using hf.r13, hf.sv0, hf.sv1, hf.sv2, hf.sv3, hf.sv4, hf.sv5, hf.win, hf.map⟩

set_option maxHeartbeats 3200000 in
/-- **`ca_start_c` on the machine.** From `ca_start_c`, called as `CmpCall` says, the machine
returns to `ra` with the callee-saved registers restored; an accept and an error mean the L runs
`CmpAccS`, `CmpErrS` say. -/
theorem cmpC_outcome_regs (q p : Prog) (hq : Refines q p) (tab : Tab) (hok : abiTabOk tab = true)
    {X : AsmTab} (hAX : AsmOkT q tab X) (hio : abiIO tab = true) (hwf : Prog.wf tab q = true)
    (hnres : 1 ≤ tab.nres) (mode plo phi : GVar) (out hdrf ctlf : ArrId) (hw : Nat) (fz own : List TieredArray)
    (hngm : mode.id < tab.ng) (hngl : plo.id < tab.ng) (hngh : phi.id < tab.ng)
    (hp : seqParamsOk tab out hdrf ctlf hw = true) (hdn : drvNeed tab < 2 ^ 64) (k0 : Nat)
    (hcode : Code (parStub tab mode plo phi out hdrf ctlf hw fz own ++ (abiStub tab ++ compileProgX X tab q "check")) k0)
    {Kc : Nat} (hC : Code (cmpStubL tab mode) Kc)
    (fd : FunDecl) (hentry : p.lookup "check" = some fd) (hnp : fd.nparams = 0)
    (bC bS pb : ByteArray) (sa : Word) (dm : MachineData) (ra : Word) (hc : CmpCall bC bS pb sa dm ra) :
    Ev (CmpPostH dm ra (CmpAccS tab p mode plo phi out hdrf ctlf hw bC bS pb)
      (CmpErrS tab p mode plo phi out hdrf ctlf hw bC bS pb) (fun _ _ => True)) dm (label abiStartCL) := by
  have hcodeO := hcode.right
  rw [Code.label (i := 28) hC rfl]
  refine ev_label (hC.get (i := 28) rfl) ?_
  refine ev_movRI (hC.get (i := 29) rfl) ?_
  refine ev_jmp (hC.get (i := 30) rfl) ?_
  have hc1 : CmpCall bC bS pb sa { dm with regs := dm.regs.set64 .r10 (0 : Word).toBitVec } ra :=
    { hin := hc.hin, hn := hc.hn, hpins := hc.hpins, hnp := hc.hnp, hzero := hc.hzero, hfits := hc.hfits,
      hinEnd := hc.hinEnd, hpinsEnd := hc.hpinsEnd, hinDisj := hc.hinDisj, hpinsDisj := hc.hpinsDisj,
      hbufDisj := hc.hbufDisj, hra := hc.hra, hcs := hc.hcs, hcs24 := hc.hcs24, hcs8 := hc.hcs8, hsa := hc.hsa,
      hsn := hc.hsn, hS := hc.hS, hSEnd := hc.hSEnd, hSDisj := hc.hSDisj, hsEnd := hc.hsEnd, hsArgs := hc.hsArgs }
  refine eventually_weaken _ _ _ _ (fun st h => ?_)
    (cmp_front q p hq tab hok hAX hio hwf hnres mode hngm hdn _ hcodeO hC fd hentry hnp bC bS pb sa _ ra hc1
      (CmpAccS tab p mode plo phi out hdrf ctlf hw bC bS pb) (CmpErrS tab p mode plo phi out hdrf ctlf hw bC bS pb)
      (fun _ _ => True) (fun h => .inl h) (fun k h => .inl h) ?_)
  · obtain ⟨⟨hpc, hRR, hacc, herr⟩, hhi⟩ := h
    exact ⟨⟨hpc, hRR, hacc, herr⟩, hhi⟩
  intro rs5 m5 s hfr hf hm hneed h48 h56 hrax
  have h10 : ({ dm with regs := dm.regs.set64 .r10 (0 : Word).toBitVec } : MachineData).regs.r10 = 0 := rfl
  rw [h10] at h56
  generalize hd1 : ({ dm with regs := dm.regs.set64 .r10 (0 : Word).toBitVec } : MachineData) = dm1 at hf hneed h56 hc1 h48 hrax hm ⊢
  obtain ⟨hnb, htab, hneed64⟩ := abiTabOk_spec hok
  obtain ⟨base, hbase⟩ : ∃ base, dm1.regs.r8.toNat = base := ⟨_, rfl⟩
  obtain ⟨rsp0, hrsp0⟩ : ∃ rsp0, dm1.regs.rsp.toNat = rsp0 := ⟨_, rfl⟩
  have hfits := hc1.hfits
  have hcs8 := hc1.hcs8
  have hcs24 := hc1.hcs24
  have hn := abiNeed_ge hok
  have hneedC := hneed
  simp only [drvNeed] at hneedC
  have hcs := hc1.hcs
  rw [hbase, hrsp0] at hcs
  rw [hbase] at hfits
  rw [hrsp0] at hcs8 hcs24
  have hside : rsp0 + 8 ≤ base ∨ base + dm1.regs.r9.toNat ≤ rsp0 - 24 := by
    rcases Nat.lt_or_ge (rsp0 - 24) base with h | h
    · by_cases h' : rsp0 + 8 ≤ base
      · exact .inl h'
      · exfalso; rcases (hcs base (by omega) (by omega)).2.1 with h2 | h2 <;> omega
    · rcases (hcs (rsp0 - 24) (by omega) (by omega)).2.1 with h2 | h2
      · omega
      · exact .inr h2
  have hS0 : ∀ x, sa.toNat ≤ x → x < sa.toNat + bS.size → x < base ∨ base + dm1.regs.r9.toNat ≤ x :=
    fun x h1 h2 => by have := (hc1.hSDisj x h1 h2).1; rwa [hbase] at this
  have hpR : ∀ x, dm1.regs.rdx.toNat ≤ x → x < dm1.regs.rdx.toNat + pb.size → x < base ∨ base + dm1.regs.r9.toNat ≤ x :=
    fun x h1 h2 => by have := hc1.hpinsDisj x h1 h2; rwa [hbase] at this
  have hwR : ∀ x, base ≤ x → x < base + abiNeed tab + 64 → x < rsp0 - 24 ∨ rsp0 + 8 ≤ x := fun x h1 h2 => by
    rcases hside with h | h <;> omega
  have hexit := fun (s' : MachineData) (hf' : CmpFrame tab dm1 ra sa bS.size base rsp0 s') hacc herr =>
    cmp_exit hC dm1 ra sa (by omega) ⟨hcs24, hcs8⟩ hrsp0 (CmpAccS tab p mode plo phi out hdrf ctlf hw bC bS pb)
      (CmpErrS tab p mode plo phi out hdrf ctlf hw bC bS pb) (fun _ _ => True) s' hf' hacc herr
      (fun _ _ _ => trivial)
  rw [hbase, hrsp0] at hf
  rw [hbase] at h48 h56 hrax
  -- 76–78: the flag, `0`: no jump
  refine ev_movRM (hC.get (i := 76) rfl) ⟨by decide, by decide⟩ (v := 0) ?_ ?_
  · rsimp; rw [hrax]; exact h56
  refine ev_cmpRO (r := .r11) (o := oI 0) (v := 0) (hC.get (i := 77) rfl) (Or.inl rfl) ?_
  refine ev_jcc (hC.get (i := 78) rfl) (fun hnz => ?_) (fun _ => ?_)
  · exfalso
    simp only [CondCode.interp, cmpFlags_zf, Reg64s.get64_r11, Reg64s.set64_r11] at hnz
    exact absurd hnz (by decide)
  have hf1 : CmpFrame tab dm1 ra sa bS.size dm1.regs.r8.toNat dm1.regs.rsp.toNat
      { s with regs := s.regs.set64 .r11 (0 : Word).toBitVec, status := cmpFlags (0 : Word).toBitVec (0 : Word).toBitVec } := by
    rw [hbase, hrsp0]
    exact hf.regs rfl fun r h1 h2 h3 h4 h5 h6 h7 h8 => by
      cases r <;> first | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd rfl h3 | exact absurd rfl h4 |
        exact absurd rfl h5 | exact absurd rfl h6 | exact absurd rfl h7 | exact absurd rfl h8 | rfl
  refine cmp_modeR q p hq hok hAX hio hwf hngm _ hcodeO fd hentry hnp hC 79 14 6 abiStartA6L
    (fun t ht => match t, ht with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl | 7, _ => rfl | 8, _ => rfl | _ + 9, h => absurd h (by omega))
    (fun t ht => match t, ht with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl | _ + 7, h => absurd h (by omega))
    bC bS pb sa dm1 ra hc1 hneed _ _ _ m5 _ hf1 hm ?_
  intro s4 hf4 hsame4 hout6
  rw [hbase, hrsp0] at hf4 hsame4
  rw [hbase] at hout6
  have h48' : rdW s4.dmem (A (base + abiNeed tab + 48)) = some (rs5.getD 0 0 - 9223372036854775808) := by
    rw [← h48]
    refine rdW_congr fun j hj => ?_
    rw [A_add]
    exact hsame4 _ (by omega) (.inr (by omega))
      (fun ⟨h3, h4⟩ => by rcases hS0 _ h3 h4 with h | h <;> omega)
      (fun ⟨h3, h4⟩ => by rcases hpR _ h3 h4 with h | h <;> omega)
      (by rcases hside with h | h <;> omega)
  have hfr0 := hfr
  obtain ⟨hbC, hpb, hbS, rs4, m4, hres4, hge4, hres5, hge5⟩ := hfr0
  refine ev_congr (cmp_okGe (i := 88) hC rfl rfl rfl rfl rfl s4 (fun s' hm' hr hbad => ?_) (fun hrdx6 hge6 st6 => ?_))
    (by omega)
  · have erax : s'.regs.rax = s4.regs.rax := by
      have := hr .rax (by decide); simpa using congrArg UInt64.ofBitVec this
    have erdx : s'.regs.rdx = s4.regs.rdx := by
      have := hr .rdx (by decide); simpa using congrArg UInt64.ofBitVec this
    refine hexit s' (hf4.regs hm' fun r _ h2 _ _ _ _ _ _ => hr r h2) (fun h0 hacc => ?_) (fun h2 => ?_)
    · rw [erdx] at h0; rw [erax] at hacc
      have hout' := hout6.resolve_left (by rw [h0]; decide)
      rcases hres : cmpRun p (m5.setG mode 6) with e | ⟨rs6, m6⟩
      · rw [hres] at hout'
        cases e <;> simp only [OutcomeRel] at hout' <;> (rw [h0] at hout'; exact absurd hout'.1 (by decide))
      rw [hres] at hout'
      obtain ⟨-, hRes, -⟩ := hout'
      have hrax6 : s4.regs.rax = rs6.getD 0 0 := hRes.1 0 (by simp only [abiLayout_tab]; omega) (by decide)
      exact .inr ⟨rs5, m5, hfr, rs6, m6, hres, .inl (by rw [← hrax6]; exact hacc)⟩
    · rw [erdx] at h2; rw [erax]
      obtain ⟨e, he, hk⟩ := err_of_entryOut hout6 h2
      exact .inr ⟨rs5, m5, hfr, .inl ⟨e, he, hk.symm⟩⟩
  -- mode `6` returned `2^63 + kC`
  have hout' := hout6.resolve_left (by rw [hrdx6]; decide)
  rcases hres6 : cmpRun p (m5.setG mode 6) with e | ⟨rs6, m6⟩
  · rw [hres6] at hout'
    cases e <;> simp only [OutcomeRel] at hout' <;> (rw [hrdx6] at hout'; exact absurd hout'.1 (by decide))
  rw [hres6] at hout'
  obtain ⟨-, hRes6, hMem6⟩ := hout'
  have hrax6 : s4.regs.rax = rs6.getD 0 0 := hRes6.1 0 (by simp only [abiLayout_tab]; omega) (by decide)
  have hge6' : 2 ^ 63 ≤ (rs6.getD 0 0).toNat := by rw [← hrax6]; exact hge6
  have hG5 : (abiLayout tab base sa.toNat bS.size dm1.regs.rdx.toNat pb.size).Ok :=
    abiLayout_ok hok ⟨Nat.le_refl _, by omega, hc1.hSEnd, hc1.hpinsEnd,
      fun x h1 h2 => by rcases hS0 x h1 h2 with h | h <;> omega,
      fun x h1 h2 => by rcases hpR x h1 h2 with h | h <;> omega,
      fun x h1 h2 => (hc1.hSDisj x h1 h2).2.2.1⟩
  -- the save area and the window are outside the stub's layout
  have hOutL : ∀ x, ((base + abiNeed tab ≤ x ∧ x < base + abiNeed tab + 64) ∨ (rsp0 - 24 ≤ x ∧ x < rsp0 + 8)) →
      ¬ (abiLayout tab base sa.toNat bS.size dm1.regs.rdx.toNat pb.size).InTab x ∧
      ¬ (abiLayout tab base sa.toNat bS.size dm1.regs.rdx.toNat pb.size).InArr x := by
    intro x hx
    have hw := fun (h : rsp0 - 24 ≤ x ∧ x < rsp0 + 8) => hcs x h.1 h.2
    obtain ⟨-, q2, q3⟩ := abiLayout_out hok (blen := abiNeed tab) (base := base) (inp := sa.toNat)
      (n := bS.size) (pins := dm1.regs.rdx.toNat) (np := pb.size) (x := x) (Nat.le_refl _)
      (by rcases hx with h | h
          · exact .inr h.1
          · rcases (hw h).2.1 with h' | h' <;> omega)
      (fun ⟨h3, h4⟩ => by
        rcases hx with h | h
        · rcases hS0 x h3 h4 with h' | h' <;> omega
        · rcases (hc1.hSDisj x h3 h4).2.2.2 with h' | h' <;> rw [hrsp0] at h' <;> omega)
      (fun ⟨h3, h4⟩ => by
        rcases hx with h | h
        · rcases hpR x h3 h4 with h' | h' <;> omega
        · exact (hw h).2.2.2 ⟨h3, h4⟩)
    exact ⟨q3, q2⟩
  have hsa4 : (BinOp.add.eval (cmpSave tab).toUInt64 s4.regs.r15).toNat = base + abiNeed tab := by
    simp only [BinOp.eval, UInt64.toNat_add, cmpSave, hf4.r15, Nat.toUInt64]
    rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
    omega
  have hkC : BinOp.sub.eval s4.regs.rax 9223372036854775808 = rs6.getD 0 0 - 9223372036854775808 := by
    rw [hrax6]; rfl
  refine ev_binO (op := .sub) (o := oR .rcx) (v := 9223372036854775808) rfl (hC.get (i := 93) rfl)
    (Or.inr (Or.inr ⟨.rcx, rfl, rfl⟩)) fun st7 => ?_
  refine ev_movRR (hC.get (i := 94) rfl) ?_
  refine ev_movRI (hC.get (i := 95) rfl) ?_
  refine ev_binO (op := .add) (o := oR .r15) rfl (hC.get (i := 96) rfl)
    (Or.inr (Or.inr ⟨.r15, rfl, rfl⟩)) fun st8 => ?_
  refine ev_movMR (hC.get (i := 97) rfl) ⟨by decide, by decide⟩ ?_ ?_
  · rsimp; rw [hsa4]; exact isSome_rdW fun j hj => by rw [A_add]; exact hf4.map _ (by omega) (by omega)
  refine ev_movRI (hC.get (i := 98) rfl) ?_
  refine ev_movRI (hC.get (i := 99) rfl) ?_
  refine ev_movRM (hC.get (i := 100) rfl) ⟨by decide, by decide⟩ (v := rs5.getD 0 0 - 9223372036854775808) ?_ ?_
  · rsimp; rw [hsa4, show Int.toNat 56 = 56 from rfl, show Int.toNat 48 = 48 from rfl,
      rdW_wrW_A (by omega) (by omega) (by omega)]; exact h48'
  refine ev_movRR (hC.get (i := 101) rfl) ?_
  rsimp
  rw [hsa4, show Int.toNat 56 = 56 from rfl, hkC]
  -- the frame and the memory before the first call
  generalize hd7 : wrW s4.dmem (A (base + abiNeed tab + 56)) (rs6.getD 0 0 - 9223372036854775808).toBitVec = d7
  have hf7 : CmpFrame tab dm1 ra sa bS.size base rsp0 { s4 with dmem := d7 } := by
    rw [← hd7]; exact hf4.wr (by omega) hside (by omega) (by omega)
  have hm7 : MemRel (abiLayout tab base sa.toNat bS.size dm1.regs.rdx.toNat pb.size) m6 d7 := by
    rw [← hd7]
    exact hMem6.only' hG5 (Only.wrW (by omega)) fun x h1 h2 => hOutL x (.inl ⟨by omega, by omega⟩)
  have h7_48 : rdW d7 (A (base + abiNeed tab + 48)) = some (rs5.getD 0 0 - 9223372036854775808) := by
    rw [← hd7, rdW_wrW_A (by omega) (by omega) (by omega)]; exact h48'
  have h7_56 : rdW d7 (A (base + abiNeed tab + 56)) = some (rs6.getD 0 0 - 9223372036854775808) := by
    rw [← hd7, rdW_wrW_same]
  have hA0 : ({ toBitVec := A rsp0 } : UInt64).toNat = rsp0 := by
    show (A rsp0).toNat = rsp0; simp only [A, BitVec.toNat_ofNat]; omega
  have e1 : s4.regs.rsp.toBitVec - 8 = A rsp0 := by
    rw [toBitVec_eq_A, hf4.rsp, A_sub8 _ (by omega) (by omega)]; rfl
  have hG := seqLayout_ok (base := base) (out := out) (hdrf := hdrf) (ctlf := ctlf) (hw := hw) hok hp (by omega)
  -- the solution's jobs: `ca_check_seq_m` with the mode word `8` over `[0, kS)`
  refine ev_call (hC.get (i := 102) rfl) ?_ ?_
  · rsimp; rw [e1]; exact isSome_rdW fun j hj => by rw [A_add]; rw [← hd7]; exact isSome_get?_storeInt (hf4.win _ (by omega) (by omega))
  rsimp
  rw [e1]
  refine ev_seq (abiSM_outcome q p hq tab hok hAX hwf mode plo phi out hdrf ctlf hw fz own hngm hngl hngh hp k0
    hcode fd hentry hnp (base := base) (blen := abiNeed tab) (inp := sa.toNat) (n := bS.size)
    (pins := dm1.regs.rdx.toNat) (np := pb.size) m6 _ (UInt64.ofBitVec (at_ (Kc + 102 + 1)).toBitVec) ?_ ?_) ?_
  · refine ⟨Nat.le_refl _, by omega, ?_, fun x h1 h2 => ?_, ?_, fun x h1 h2 => ?_, ?_, ?_⟩ <;> dsimp only <;>
      (try rsimp)
    · exact hf4.r15
    · exact isSome_get?_storeInt (hf7.map x h1 (by omega))
    · rw [hA0, rdW_wrW_same]
    · rw [hA0] at h1 h2
      exact ⟨isSome_get?_storeInt (hf7.win x h1 h2), by rcases (hcs x h1 h2).2.1 with h | h <;> omega⟩
    · rw [hA0]; omega
    · rw [hA0]; omega
  · dsimp only
    exact hm7.only' hG5 (Only.wrW (x := rsp0) (by omega)) fun x h1 h2 => hOutL x (.inr ⟨by omega, by omega⟩)
  intro st ⟨hpc, hRR, hfr8, hout8⟩
  dsimp only at hRR hfr8 hout8
  simp only [hA0] at hfr8
  rw [hpc]
  simp only [Int64.ofBitVec_toBitVec]
  try rsimp at hout8
  generalize st.data = s8 at *
  have hsv8 : ∀ x, base + abiNeed tab ≤ x → x < base + abiNeed tab + 64 → s8.dmem.get? (A x) = d7.get? (A x) := by
    intro x h1 h2
    obtain ⟨q1, q2, q3⟩ := seq_out (base := base) (out := out) (hdrf := hdrf) (ctlf := ctlf) (hw := hw) hok hp
      (blen := abiNeed tab) (Nat.le_refl _) (x := x) (Or.inr h1)
    rw [hfr8.same x (by omega) q1 q2 q3 (by rcases hside with h | h <;> omega)
      (Or.inr (by simp only [Layout.tabEnd, seqLayout_T, seqLayout_tab, seqLayout_nargs]; omega)),
      get?_wrW_A (by omega) (by omega) (by rcases hside with h | h <;> omega)]
  have hf8 : CmpFrame tab dm1 ra sa bS.size base rsp0 s8 :=
    (hf7.setR10 (8 : Word).toBitVec).ret (by omega) (by omega) (by rsimp; exact hA0) (fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 => by
        cases r <;> first | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd rfl h3 | exact absurd rfl h4 |
          exact absurd rfl h5 | exact absurd rfl h6 | exact absurd rfl h7 | exact absurd rfl h8 | exact absurd rfl h9 |
          (rsimp; try rfl))
      hRR hsv8 fun y hy => hfr8.grows _ (isSome_get?_storeInt hy)
  have h8_56 : rdW s8.dmem (A (base + abiNeed tab + 56)) = some (rs6.getD 0 0 - 9223372036854775808) := by
    rw [← h7_56]; exact rdW_congr fun j hj => by rw [A_add]; exact hsv8 _ (by omega) (by omega)
  refine ev_cmpRO (r := .rdx) (o := oI 0) (v := 0) (hC.get (i := 103) rfl) (Or.inl rfl) ?_
  refine ev_jcc (hC.get (i := 104) rfl) (fun hnz => ?_) (fun hz0 => ?_)
  · refine hexit _ (hf8.regs rfl fun r _ _ _ _ _ _ _ _ => rfl) (fun h0 => ?_) (fun h2 => ?_)
    · simp only [CondCode.interp, cmpFlags_zf, Reg64s.get64_rdx] at hnz
      exact absurd hnz (by rw [h0]; decide)
    · obtain ⟨e, he, hk'⟩ := err_of_entryOut hout8 h2
      rw [hk']
      exact .inr ⟨rs5, m5, hfr, .inr ⟨rs6, m6, hres6, hge6', .inl ⟨e, he, rfl⟩⟩⟩
  simp only [CondCode.interp, cmpFlags_zf, Reg64s.get64_rdx] at hz0
  have hrdx8 : s8.regs.rdx = 0 := by
    simp only [Bool.not_eq_false', beq_iff_eq] at hz0
    exact UInt64.toBitVec_inj.mp hz0
  have hout8' := hout8.resolve_left (by rw [hrdx8]; decide)
  rcases hres8 : L.run p abiFuel "check" [] (seqMemW m6 mode plo phi out hdrf ctlf hw 8 0
      (rs5.getD 0 0 - 9223372036854775808)) with e | ⟨rs8, m8⟩
  · rw [hres8] at hout8'
    cases e <;> simp only [OutcomeRel] at hout8' <;> (rw [hrdx8] at hout8'; exact absurd hout8'.1 (by decide))
  rw [hres8] at hout8'
  obtain ⟨-, hRes8, hMem8⟩ := hout8'
  have hrax8 : s8.regs.rax = rs8.getD 0 0 := hRes8.1 0 (by simp only [seqLayout_tab]; omega) (by decide)
  refine ev_movRI (hC.get (i := 105) rfl) ?_
  refine ev_cmpRO (r := .rax) (o := oR .rcx) (v := 71757147230292) (hC.get (i := 106) rfl)
    (Or.inr (Or.inr ⟨.rcx, rfl, rfl⟩)) ?_
  refine ev_jcc (hC.get (i := 107) rfl) (fun hne => ?_) (fun heq => ?_)
  · refine hexit _ (hf8.regs rfl fun r h1 h2 _ _ _ _ _ _ => by
        cases r <;> first | exact absurd rfl h2 | rfl) (fun _ hacc => ?_) (fun h2 => ?_)
    · simp only [CondCode.interp, cmpFlags_zf] at hne
      rsimp at hne hacc
      exact absurd hne (by rw [hacc]; simp [ACCEPT])
    · rsimp at h2; rw [hrdx8] at h2; exact absurd h2 (by decide)
  simp only [CondCode.interp, cmpFlags_zf] at heq
  rsimp at heq
  have hacc8 : rs8.getD 0 0 = ACCEPT := by
    rw [← hrax8]
    simp only [Bool.not_eq_false', beq_iff_eq] at heq
    exact UInt64.toBitVec_inj.mp heq
  -- the challenge's jobs: `ca_check_seq_g` with the mode word `9` over `[0, kC)`
  have hsa8 : (BinOp.add.eval (cmpSave tab).toUInt64 s8.regs.r15).toNat = base + abiNeed tab := by
    simp only [BinOp.eval, UInt64.toNat_add, cmpSave, hf8.r15, Nat.toUInt64]
    rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
    omega
  have htopv : (BinOp.add.eval (abiSlot + abiStack).toUInt64 s8.regs.r15).toNat = base + (abiSlot + abiStack) := by
    simp only [BinOp.eval, UInt64.toNat_add, hf8.r15, Nat.toUInt64]
    rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size, abiSlot, abiStack]; omega)]
    simp only [abiSlot, abiStack] at *; omega
  refine ev_movRI (hC.get (i := 108) rfl) ?_
  refine ev_binO (op := .add) (o := oR .r15) rfl (hC.get (i := 109) rfl)
    (Or.inr (Or.inr ⟨.r15, rfl, rfl⟩)) fun st9 => ?_
  refine ev_movRM (hC.get (i := 110) rfl) ⟨by decide, by decide⟩ (v := rs6.getD 0 0 - 9223372036854775808) ?_ ?_
  · rsimp; rw [hsa8]; exact h8_56
  refine ev_movRI (hC.get (i := 111) rfl) ?_
  refine ev_movRI (hC.get (i := 112) rfl) ?_
  refine ev_movRR (hC.get (i := 113) rfl) ?_
  refine ev_movRI (hC.get (i := 114) rfl) ?_
  refine ev_binO (op := .add) (o := oR .r15) rfl (hC.get (i := 115) rfl)
    (Or.inr (Or.inr ⟨.r15, rfl, rfl⟩)) fun st10 => ?_
  refine ev_movMR (hC.get (i := 116) rfl) ⟨by decide, by decide⟩ ?_ ?_
  · rsimp; simp only [Tab.stackTop, Int.toNat_zero, Nat.add_zero, hf8.r15]
    exact isSome_rdW fun j hj => by rw [A_add]; exact hf8.map _ (by omega) (by omega)
  rsimp
  simp only [Tab.stackTop, Int.toNat_zero, Nat.add_zero, hf8.r15]
  generalize hd9 : wrW s8.dmem (A base) (BinOp.add.eval (abiSlot + abiStack).toUInt64 s8.regs.r15).toBitVec = d9
  have hf9 : CmpFrame tab dm1 ra sa bS.size base rsp0 { s8 with dmem := d9 } := by
    rw [← hd9]; exact hf8.wrR (by omega) (by omega)
  have hm9 : MemRel (seqLayout tab base out hdrf ctlf hw) m8 d9 := by
    rw [← hd9]
    have := MemRel.wrTop hG hMem8 (BinOp.add.eval (abiSlot + abiStack).toUInt64 s8.regs.r15).toBitVec
    simpa only [seqLayout_T] using this
  have htop9 : rdW d9 (A base) = some (UInt64.ofNat (base + (abiSlot + abiStack))) := by
    rw [← hd9, rdW_wrW_same]
    simp only [UInt64.ofBitVec_toBitVec, Option.some.injEq]
    apply UInt64.toNat_inj.mp
    rw [htopv, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size, abiSlot, abiStack]; omega)]
  have e2 : s8.regs.rsp.toBitVec - 8 = A rsp0 := by
    rw [toBitVec_eq_A, hf8.rsp, A_sub8 _ (by omega) (by omega)]; rfl
  refine ev_call (hC.get (i := 117) rfl) ?_ ?_
  · rsimp; rw [e2]; exact isSome_rdW fun j hj => by rw [A_add]; rw [← hd9]; exact isSome_get?_storeInt (hf8.win _ (by omega) (by omega))
  rsimp
  rw [e2]
  refine ev_seq (abiSG_outcome q p hq tab hok hAX hwf mode plo phi out hdrf ctlf hw fz own hngm hngl hngh hp k0
    hcode fd hentry hnp (base := base) (blen := abiNeed tab) m8 _ (UInt64.ofBitVec (at_ (Kc + 117 + 1)).toBitVec)
    ?_ ?_ ?_) ?_
  · refine ⟨Nat.le_refl _, by omega, ?_, fun x h1 h2 => ?_, ?_, fun x h1 h2 => ?_, ?_, ?_⟩ <;> dsimp only <;>
      (try rsimp)
    · exact hf8.r15
    · exact isSome_get?_storeInt (hf9.map x h1 (by omega))
    · rw [hA0, rdW_wrW_same]
    · rw [hA0] at h1 h2
      exact ⟨isSome_get?_storeInt (hf9.win x h1 h2), by rcases (hcs x h1 h2).2.1 with h | h <;> omega⟩
    · rw [hA0]; omega
    · rw [hA0]; omega
  · dsimp only
    refine hm9.only' hG (Only.wrW (x := rsp0) (by omega)) fun x h1 h2 => ?_
    obtain ⟨-, q2, q3⟩ := seq_out (base := base) (out := out) (hdrf := hdrf) (ctlf := ctlf) (hw := hw) hok hp
      (blen := abiNeed tab) (Nat.le_refl _) (x := x) (by rcases hside with h | h <;> omega)
    exact ⟨q3, q2⟩
  · dsimp only
    rw [rdW_wrW_A (by omega) (by omega) (by rcases hside with h | h <;> omega)]; exact htop9
  intro st ⟨hpc9, hRR9, hfr9, hout9⟩
  dsimp only at hRR9 hfr9 hout9
  simp only [hA0] at hfr9
  rw [hpc9]
  simp only [Int64.ofBitVec_toBitVec]
  try rsimp at hout9
  generalize st.data = s10 at *
  have hsv10 : ∀ x, base + abiNeed tab ≤ x → x < base + abiNeed tab + 64 → s10.dmem.get? (A x) = d9.get? (A x) := by
    intro x h1 h2
    obtain ⟨q1, q2, q3⟩ := seq_out (base := base) (out := out) (hdrf := hdrf) (ctlf := ctlf) (hw := hw) hok hp
      (blen := abiNeed tab) (Nat.le_refl _) (x := x) (Or.inr h1)
    rw [hfr9.same x (by omega) q1 q2 q3 (by rcases hside with h | h <;> omega)
      (Or.inr (by simp only [Layout.tabEnd, seqLayout_T, seqLayout_tab, seqLayout_nargs]; omega)),
      get?_wrW_A (by omega) (by omega) (by rcases hside with h | h <;> omega)]
  have hf10 : CmpFrame tab dm1 ra sa bS.size base rsp0 s10 :=
    (hf9.setR10 (9 : Word).toBitVec).ret (by omega) (by omega) (by rsimp; exact hA0) (fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 => by
        cases r <;> first | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd rfl h3 | exact absurd rfl h4 |
          exact absurd rfl h5 | exact absurd rfl h6 | exact absurd rfl h7 | exact absurd rfl h8 | exact absurd rfl h9 |
          (rsimp; try rfl))
      hRR9 hsv10 fun y hy => hfr9.grows _ (isSome_get?_storeInt hy)
  refine ev_jmp (hC.get (i := 118) rfl) ?_
  refine hexit s10 hf10 (fun h0 hacc => ?_) (fun h2 => ?_)
  · have hout' := hout9.resolve_left (by rw [h0]; decide)
    rcases hres9 : L.run p abiFuel "check" [] (seqNext m8 mode plo phi 9 0 (rs6.getD 0 0 - 9223372036854775808))
      with e | ⟨rs9, m9⟩
    · rw [hres9] at hout'
      cases e <;> simp only [OutcomeRel] at hout' <;> (rw [h0] at hout'; exact absurd hout'.1 (by decide))
    rw [hres9] at hout'
    obtain ⟨-, hRes, -⟩ := hout'
    have hrax : s10.regs.rax = rs9.getD 0 0 := hRes.1 0 (by simp only [seqLayout_tab]; omega) (by decide)
    exact .inr ⟨rs5, m5, hfr, rs6, m6, hres6, .inr ⟨hge6', rs8, m8, hres8, hacc8, rs9, m9, hres9,
      by rw [← hrax]; exact hacc⟩⟩
  · obtain ⟨e, he, hk'⟩ := err_of_entryOut hout9 h2
    rw [hk']
    exact .inr ⟨rs5, m5, hfr, .inr ⟨rs6, m6, hres6, hge6', .inr ⟨rs8, m8, hres8, hacc8, e, he, rfl⟩⟩⟩

end

end ConAgua.Final
