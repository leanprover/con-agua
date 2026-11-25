module

public import ConAgua.Final.CmpMain
import ConAgua.Final.DrvAbi
import Kraken.X64.Registers
public import ConAgua.Checker.CmpCall

@[expose] public section

/-!
# `ca_start_ac` on the machine: entry 1 of the threaded compared run (lane compare2)

`cmpA_outcome_regs`: the harness calls `ca_start_ac` (`CmpCall`). The front (`cmp_front`: modes
`4`, `5`), then mode `7` on the region as mode `5` left it (`cmp_modeR`), and the return: the
caller's registers, an accept or an error of a mode (`CmpAccT`, `CmpErrT`), and on `rdx = 0`,
`rax ≥ 2^63`, the job count `kS + kC` in `rax` and the region holding mode `7`'s final memory
(`CmpHiT`).
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
variable [Host]

omit [Host] in
/-- `rax` is `kS + kC` below `2^63` plus `2^63`: not `ACCEPT`. -/
theorem cmpA_ne_accept {K c : Word} (hK : K < c) (hc : c = 9223372036854775808) :
    K + c ≠ ACCEPT := by
  intro e
  subst hc
  have e2 := congrArg UInt64.toNat e
  rw [UInt64.toNat_add] at e2
  rw [UInt64.lt_iff_toNat_lt] at hK
  simp only [ACCEPT, UInt64.reduceToNat] at e2 hK
  omega

/-- **`ca_start_ac` on the machine.** From `ca_start_ac`, called as `CmpCall` says, the machine
returns to `ra` with the callee-saved registers restored; an accept, an error, and a return with
`rdx = 0`, `rax ≥ 2^63` mean the L runs `CmpAccT`, `CmpErrT`, `CmpHiT` say. -/
theorem cmpA_outcome_regs (q p : Prog) (hq : Refines q p) (tab : Tab) (hok : abiTabOk tab = true)
    {X : AsmTab} (hAX : AsmOkT q tab X) (hio : abiIO tab = true) (hwf : Prog.wf tab q = true)
    (hnres : 1 ≤ tab.nres) (mode : GVar) (hngm : mode.id < tab.ng) (hdn : drvNeed tab < 2 ^ 64) (k0 : Nat)
    (hcodeO : Code (abiStub tab ++ compileProgX X tab q "check") k0) {Kc : Nat} (hC : Code (cmpStubL tab mode) Kc)
    (fd : FunDecl) (hentry : p.lookup "check" = some fd) (hnp : fd.nparams = 0)
    (bC bS pb : ByteArray) (sa : Word) (dm : MachineData) (ra : Word) (hc : CmpCall bC bS pb sa dm ra) :
    Ev (CmpPostH dm ra (CmpAccT tab p mode bC bS pb) (CmpErrT tab p mode bC bS pb)
      (CmpHiT tab p mode bC bS pb dm.regs.r8.toNat sa.toNat dm.regs.rdx.toNat)) dm (label abiStartACL) := by
  rw [Code.label (i := 31) hC rfl]
  refine ev_label (hC.get (i := 31) rfl) ?_
  refine ev_movRI (hC.get (i := 32) rfl) ?_
  refine ev_congr (j := Kc + 33) ?_ (by omega)
  rw [← Code.label (i := 33) hC rfl]
  have hc1 : CmpCall bC bS pb sa { dm with regs := dm.regs.set64 .r10 (1 : Word).toBitVec } ra :=
    { hin := hc.hin, hn := hc.hn, hpins := hc.hpins, hnp := hc.hnp, hzero := hc.hzero, hfits := hc.hfits,
      hinEnd := hc.hinEnd, hpinsEnd := hc.hpinsEnd, hinDisj := hc.hinDisj, hpinsDisj := hc.hpinsDisj,
      hbufDisj := hc.hbufDisj, hra := hc.hra, hcs := hc.hcs, hcs24 := hc.hcs24, hcs8 := hc.hcs8, hsa := hc.hsa,
      hsn := hc.hsn, hS := hc.hS, hSEnd := hc.hSEnd, hSDisj := hc.hSDisj, hsEnd := hc.hsEnd, hsArgs := hc.hsArgs }
  have e8 : ({ dm with regs := dm.regs.set64 .r10 (1 : Word).toBitVec } : MachineData).regs.r8 = dm.regs.r8 := rfl
  have ex : ({ dm with regs := dm.regs.set64 .r10 (1 : Word).toBitVec } : MachineData).regs.rdx = dm.regs.rdx := rfl
  refine eventually_weaken _ _ _ _ (fun st h => ?_)
    (cmp_front q p hq tab hok hAX hio hwf hnres mode hngm hdn k0 hcodeO hC fd hentry hnp bC bS pb sa _ ra hc1
      (CmpAccT tab p mode bC bS pb) (CmpErrT tab p mode bC bS pb)
      (CmpHiT tab p mode bC bS pb dm.regs.r8.toNat sa.toNat dm.regs.rdx.toNat) (fun h => .inl h)
      (fun k h => .inl h) ?_)
  · obtain ⟨⟨hpc, hRR, hacc, herr⟩, hhi⟩ := h
    exact ⟨⟨hpc, hRR, hacc, herr⟩, hhi⟩
  intro rs5 m5 s hfr hf hm hneed h48 h56 hrax
  have h10 : ({ dm with regs := dm.regs.set64 .r10 (1 : Word).toBitVec } : MachineData).regs.r10 = 1 := rfl
  rw [h10] at h56
  rw [← e8, ← ex]
  generalize hd1 : ({ dm with regs := dm.regs.set64 .r10 (1 : Word).toBitVec } : MachineData) = dm1 at hf hneed h56 hc1 h48 hrax hm e8 ex ⊢
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
  have hexit := fun (s' : MachineData) (hf' : CmpFrame tab dm1 ra sa bS.size base rsp0 s') hacc herr hhi =>
    cmp_exit hC dm1 ra sa (by omega) ⟨hcs24, hcs8⟩ hrsp0 (CmpAccT tab p mode bC bS pb) (CmpErrT tab p mode bC bS pb)
      (CmpHiT tab p mode bC bS pb dm1.regs.r8.toNat sa.toNat dm1.regs.rdx.toNat) s' hf' hacc herr hhi
  rw [hbase, hrsp0] at hf
  rw [hbase] at h48 h56 hrax
  -- 76–78: the flag, `1`: on to mode `7`
  refine ev_movRM (hC.get (i := 76) rfl) ⟨by decide, by decide⟩ (v := 1) ?_ ?_
  · rsimp; rw [hrax]; exact h56
  refine ev_cmpRO (r := .r11) (o := oI 0) (v := 0) (hC.get (i := 77) rfl) (Or.inl rfl) ?_
  refine ev_jcc (hC.get (i := 78) rfl) (fun _ => ?_) (fun hz => ?_)
  rotate_left
  · exfalso
    simp only [CondCode.interp, cmpFlags_zf, Reg64s.get64_r11, Reg64s.set64_r11] at hz
    exact absurd hz (by decide)
  rw [Code.label (i := 119) hC rfl]
  refine ev_label (hC.get (i := 119) rfl) ?_
  have hf1 : CmpFrame tab dm1 ra sa bS.size dm1.regs.r8.toNat dm1.regs.rsp.toNat
      { s with regs := s.regs.set64 .r11 (1 : Word).toBitVec, status := cmpFlags (1 : Word).toBitVec (0 : Word).toBitVec } := by
    rw [hbase, hrsp0]
    exact hf.regs rfl fun r h1 h2 h3 h4 h5 h6 h7 h8 => by
      cases r <;> first | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd rfl h3 | exact absurd rfl h4 |
        exact absurd rfl h5 | exact absurd rfl h6 | exact absurd rfl h7 | exact absurd rfl h8 | rfl
  refine cmp_modeR q p hq hok hAX hio hwf hngm k0 hcodeO fd hentry hnp hC 120 21 7 abiStartA7L
    (fun t ht => match t, ht with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl | 7, _ => rfl | 8, _ => rfl | _ + 9, h => absurd h (by omega))
    (fun t ht => match t, ht with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl | _ + 7, h => absurd h (by omega))
    bC bS pb sa dm1 ra hc1 hneed _ _ _ m5 _ hf1 hm ?_
  intro s4 hf4 hsame4 hout7
  rw [hbase, hrsp0] at hf4 hsame4
  rw [hbase] at hout7
  -- the solution's job count survived the call
  have h48' : rdW s4.dmem (A (base + abiNeed tab + 48)) = some (rs5.getD 0 0 - 9223372036854775808) := by
    rw [← h48]
    refine rdW_congr fun j hj => ?_
    rw [A_add]
    exact hsame4 _ (by omega) (.inr (by omega))
      (fun ⟨h3, h4⟩ => by rcases hS0 _ h3 h4 with h | h <;> omega)
      (fun ⟨h3, h4⟩ => by rcases hpR _ h3 h4 with h | h <;> omega)
      (by rcases hside with h | h <;> omega)
  obtain ⟨hbC, hpb, hbS, rs4, m4, hres4, hge4, hres5, hge5⟩ := hfr
  have hfr : CmpFront45 tab p mode bC bS pb rs5 m5 := ⟨hbC, hpb, hbS, rs4, m4, hres4, hge4, hres5, hge5⟩
  refine ev_congr (cmp_okGe (i := 129) hC rfl rfl rfl rfl rfl s4 (fun s' hm' hr hbad => ?_) (fun hrdx7 hge7 st7 => ?_))
    (by omega)
  · have erax : s'.regs.rax = s4.regs.rax := by
      have := hr .rax (by decide); simpa using congrArg UInt64.ofBitVec this
    have erdx : s'.regs.rdx = s4.regs.rdx := by
      have := hr .rdx (by decide); simpa using congrArg UInt64.ofBitVec this
    refine hexit s' (hf4.regs hm' fun r _ h2 _ _ _ _ _ _ => hr r h2) (fun h0 hacc => ?_) (fun h2 => ?_)
      (fun h0 h1 => ?_)
    · rw [erdx] at h0; rw [erax] at hacc
      have hout' := hout7.resolve_left (by rw [h0]; decide)
      rcases hres : cmpRun p (m5.setG mode 7) with e | ⟨rs7, m7⟩
      · rw [hres] at hout'
        cases e <;> simp only [OutcomeRel] at hout' <;> (rw [h0] at hout'; exact absurd hout'.1 (by decide))
      rw [hres] at hout'
      obtain ⟨-, hRes, -⟩ := hout'
      have hrax7 : s4.regs.rax = rs7.getD 0 0 := hRes.1 0 (by simp only [abiLayout_tab]; omega) (by decide)
      exact .inr ⟨rs5, m5, hfr, rs7, m7, hres, by rw [← hrax7]; exact hacc⟩
    · rw [erdx] at h2; rw [erax]
      obtain ⟨e, he, hk⟩ := err_of_entryOut hout7 h2
      exact .inr ⟨rs5, m5, hfr, e, he, hk.symm⟩
    · rw [erdx] at h0; rw [erax] at h1
      rcases hbad with h | h
      · exact absurd h0 h
      · omega
  -- mode `7` returned `2^63 + kC`
  have hout' := hout7.resolve_left (by rw [hrdx7]; decide)
  rcases hres7 : cmpRun p (m5.setG mode 7) with e | ⟨rs7, m7⟩
  · rw [hres7] at hout'
    cases e <;> simp only [OutcomeRel] at hout' <;> (rw [hrdx7] at hout'; exact absurd hout'.1 (by decide))
  rw [hres7] at hout'
  obtain ⟨-, hRes7, hMem7⟩ := hout'
  have hrax7 : s4.regs.rax = rs7.getD 0 0 := hRes7.1 0 (by simp only [abiLayout_tab]; omega) (by decide)
  have hge7' : 2 ^ 63 ≤ (rs7.getD 0 0).toNat := by rw [← hrax7]; exact hge7
  have hMemF : ∀ v, MemRel (abiLayout tab base sa.toNat bS.size dm1.regs.rdx.toNat pb.size) m7
      (wrW s4.dmem (A rsp0) v) := by
    intro v
    have hG7 : (abiLayout tab base sa.toNat bS.size dm1.regs.rdx.toNat pb.size).Ok :=
      abiLayout_ok hok ⟨Nat.le_refl _, by omega, hc1.hSEnd, hc1.hpinsEnd,
        fun x h1 h2 => by rcases hS0 x h1 h2 with h | h <;> omega,
        fun x h1 h2 => by rcases hpR x h1 h2 with h | h <;> omega,
        fun x h1 h2 => (hc1.hSDisj x h1 h2).2.2.1⟩
    refine hMem7.only' hG7 (Only.wrW (x := rsp0) (by omega)) fun x h1 h2 => ?_
    have hw := hcs x (by omega) (by omega)
    obtain ⟨-, q2, q3⟩ := abiLayout_out hok (blen := abiNeed tab) (base := base) (inp := sa.toNat)
      (n := bS.size) (pins := dm1.regs.rdx.toNat) (np := pb.size) (x := x) (Nat.le_refl _)
      (by rcases hw.2.1 with h | h <;> omega)
      (fun ⟨h3, h4⟩ => by rcases (hc1.hSDisj x h3 h4).2.2.2 with h | h <;> rw [hrsp0] at h <;> omega)
      (fun ⟨h3, h4⟩ => hw.2.2.2 ⟨h3, h4⟩)
    exact ⟨q3, q2⟩
  have hsa4 : (BinOp.add.eval (cmpSave tab).toUInt64 s4.regs.r15).toNat = base + abiNeed tab := by
    simp only [BinOp.eval, UInt64.toNat_add, cmpSave, hf4.r15, Nat.toUInt64]
    rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
    omega
  refine ev_binO (op := .sub) (o := oR .rcx) (v := 9223372036854775808) rfl (hC.get (i := 134) rfl)
    (Or.inr (Or.inr ⟨.rcx, rfl, rfl⟩)) fun st8 => ?_
  refine ev_movRR (hC.get (i := 135) rfl) ?_
  refine ev_movRI (hC.get (i := 136) rfl) ?_
  refine ev_binO (op := .add) (o := oR .r15) rfl (hC.get (i := 137) rfl)
    (Or.inr (Or.inr ⟨.r15, rfl, rfl⟩)) fun st9 => ?_
  refine ev_movRM (hC.get (i := 138) rfl) ⟨by decide, by decide⟩ (v := rs5.getD 0 0 - 9223372036854775808) ?_ ?_
  · rsimp; rw [hsa4]; exact h48'
  refine ev_binO (op := .add) (o := oR .rdx) (v := rs7.getD 0 0 - 9223372036854775808) rfl (hC.get (i := 139) rfl)
    (Or.inr (Or.inr ⟨.rdx, rfl, by rsimp; rw [hrax7]; rfl⟩)) fun st10 => ?_
  refine ev_cmpRO (r := .rax) (o := oR .rcx) (v := 9223372036854775808) (hC.get (i := 140) rfl)
    (Or.inr (Or.inr ⟨.rcx, rfl, rfl⟩)) ?_
  have hfE : ∀ (R : Reg64s) (fl : StatusFlags) (d : DataMem), d = s4.dmem → R.rbp = s4.regs.rbp →
      R.rbx = s4.regs.rbx → R.r12 = s4.regs.r12 → R.r13 = s4.regs.r13 → R.r14 = s4.regs.r14 →
      R.r15 = s4.regs.r15 → R.rsp = s4.regs.rsp → R.r10 = s4.regs.r10 →
      CmpFrame tab dm1 ra sa bS.size base rsp0 { s4 with regs := R, status := fl, dmem := d } := by
    intro R fl d hd h1 h2 h3 h4 h5 h6 h7 h8
    refine hf4.regs hd fun r a b c d' e f g h => ?_
    cases r <;> first | exact absurd rfl a | exact absurd rfl b | exact absurd rfl c | exact absurd rfl d' |
      exact absurd rfl e | exact absurd rfl f | exact absurd rfl g | exact absurd rfl h |
      (simp only [Reg64s.get64_rbp, Reg64s.get64_rbx, Reg64s.get64_r12, Reg64s.get64_r13, Reg64s.get64_r14,
        Reg64s.get64_r15, Reg64s.get64_rsp, Reg64s.get64_r10]
       first | rw [h1] | rw [h2] | rw [h3] | rw [h4] | rw [h5] | rw [h6] | rw [h7] | rw [h8])
  refine ev_jcc (hC.get (i := 141) rfl) (fun hlt => ?_) (fun _ => ?_)
  · -- `kS + kC < 2^63`: `2^63 + kS + kC`
    rw [Code.label (i := 144) hC rfl]
    refine ev_label (hC.get (i := 144) rfl) ?_
    refine ev_binO (op := .add) (o := oR .rcx) (v := 9223372036854775808) rfl (hC.get (i := 145) rfl)
      (Or.inr (Or.inr ⟨.rcx, rfl, rfl⟩)) fun st11 => ?_
    refine ev_movRI (hC.get (i := 146) rfl) ?_
    refine ev_congr (j := Kc + 147) (Eq.mp (congrArg (Ev _ _) (Code.label (i := 147) hC rfl)) ?_) (by omega)
    rw [interp_c] at hlt
    simp only [decide_eq_true_eq] at hlt
    rsimp at hlt
    refine hexit _ (hfE _ _ _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (fun _ hacc => ?_) (fun h2 => ?_) (fun _ _ v => ?_)
    iterate 8 (· rsimp)
    · exfalso; rsimp at hacc
      exact cmpA_ne_accept hlt rfl hacc
    · rsimp at h2; exact absurd h2 (by decide)
    · rsimp
      refine ⟨rs5, m5, rs7, m7, hfr, hres7, hge7', ?_, ?_⟩
      · simp only [BinOp.eval]
        rw [UInt64.add_comm _ (rs7.getD 0 0 - _), UInt64.add_comm]
      · rw [hbase]; exact hMemF v
  · -- `kS + kC ≥ 2^63`: a decline
    refine ev_movRI (hC.get (i := 142) rfl) ?_
    refine ev_jmp (hC.get (i := 143) rfl) ?_
    refine hexit _ (hfE _ _ _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      (fun h0 _ => ?_) (fun h2 => ?_) (fun h0 _ _ => ?_)
    iterate 8 (· rsimp)
    · rsimp at h0; exact absurd h0 (by decide)
    · rsimp at h2; exact absurd h2 (by decide)
    · rsimp at h0; exact absurd h0 (by decide)

end

end ConAgua.Final
