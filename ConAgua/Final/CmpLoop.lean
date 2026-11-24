module

public import ConAgua.Final.CmpOutcome
public import ConAgua.Final.CmpAbi
import ConAgua.Final.BufAbi
import ConAgua.Final.DrvAbi
import Kraken.X64.Registers

@[expose] public section

/-!
# `ca_compare`'s loop over the solution's jobs (lane compare)

`cmp_loop`: from the loop head `ca_cmp_loop` with the job counter `j` (save word `7`) below the job
count `k` (save word `6`), the driver calls `ca_check_b(OUT, OUT[1], j, W, workerNeed)`
(`abiB_outcome`); a call that does not accept ends the run with its result (to the exit), an
accepting one is the next job's start (the worker memory it ends with, `RegionRel`, and the region
`R` as mode `5` left it but the buffer, which holds the job's frozen arrays, `CmpAgree` at
`bufNext`); at `j = k`, on to `ca_cmp_after`.
-/

namespace ConAgua.Final

open L L.Compiler L.Arena

/-- The register-file simp set: writes as literals, reads as projections. -/
local macro "rsimp" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [Reg64s.set64_rax,
  Reg64s.set64_rcx, Reg64s.set64_rdx, Reg64s.set64_rsi, Reg64s.set64_rdi, Reg64s.set64_rsp, Reg64s.set64_rbp,
  Reg64s.set64_r8, Reg64s.set64_r9, Reg64s.set64_r11, Reg64s.set64_r14, Reg64s.set64_r15, Reg64s.get64_rax,
  Reg64s.get64_rcx, Reg64s.get64_rdx, Reg64s.get64_rsi, Reg64s.get64_rdi, Reg64s.get64_rsp, Reg64s.get64_r8,
  Reg64s.get64_r9, Reg64s.get64_r11, Reg64s.get64_r14, Reg64s.get64_r15, Reg64s.get64_rbp, Reg64s.rax_mk,
  Reg64s.rcx_mk, Reg64s.rdx_mk, Reg64s.rsi_mk, Reg64s.rdi_mk, Reg64s.rsp_mk, Reg64s.rbp_mk, Reg64s.r8_mk,
  Reg64s.r9_mk, Reg64s.r10_mk, Reg64s.r11_mk, Reg64s.r12_mk, Reg64s.r13_mk, Reg64s.r14_mk, Reg64s.r15_mk,
  Reg64s.rbx_mk, UInt64.toNat_toBitVec, UInt64.ofBitVec_toBitVec, UInt64.toBitVec_ofBitVec] $[$loc]?)

section
variable [Host] {tab : Tab} {mode : GVar} {out : ArrId} {own : List TieredArray}

/-- **The jobs' loop.** -/
theorem cmp_loop (q p : Prog) (hq : Refines q p) (hok : abiTabOk tab = true)
    {X : AsmTab} (hAX : AsmOkT q tab X) (hwf : Prog.wf tab q = true) (hnres : 1 ≤ tab.nres)
    (plo phi : GVar) (hdrf ctlf : ArrId) (hw : Nat) (fz : List TieredArray)
    (hngm : mode.id < tab.ng) (hngl : plo.id < tab.ng) (hngh : phi.id < tab.ng)
    (h12 : plo ≠ phi) (h13 : plo ≠ mode) (h23 : phi ≠ mode) (hfzl : fz.length < 2 ^ 20) (k0 : Nat)
    (hcode : Code (parStub tab mode plo phi out hdrf ctlf hw fz own ++ (abiStub tab ++ compileProgX X tab q "check")) k0)
    (fd : FunDecl) (hentry : p.lookup "check" = some fd) (hnp : fd.nparams = 0)
    (hmo : bufMinOk tab fz own = true) (hdisj : ∀ a ∈ own, a ∉ fz)
    (hnd : fz.Nodup) (hdom : ∀ a ∈ fz, tab.dom64 a = true)
    (hfz0 : 0 < fz.length) (hwn2 : 2 * workerNeed own < 2 ^ 64)
    {Kc : Nat} (hC : Code (cmpStubL tab mode out own) Kc)
    (dm : MachineData) (ra sa : Word) {nS base rsp0 : Nat} (B : Array Word) (k : Nat) (hk : k < 2 ^ 63)
    (hgeo : CmpGeo tab own base dm.regs.r9.toNat rsp0 (base + abiSlot * abiSlot64 tab out) B.size)
    (hg : BufGeom tab fz own B (base + abiSlot * abiSlot64 tab out) (base + cmpW tab) (workerNeed own))
    (hBok : BufOk fz.length B) (hh : CmpHdrKeep p mode plo phi fz own)
    (hrsp0 : dm.regs.rsp.toNat = rsp0)
    (d5 : DataMem) (Acc : Prop) (Err : Word → Prop)
    (hErr : ∀ rm : Nat → Mem, rm 0 = zeroMem tab → ∀ j < k, CmpJobs p mode plo phi fz own B rm j → ∀ e,
      cmpRun p (bufMemG fz own plo phi mode (bufSeq fz B rm j) (rm j) (UInt64.ofNat j)) = .error e → Err e.code)
    (hAfter : ∀ (rm : Nat → Mem) (s : MachineData), rm 0 = zeroMem tab → CmpJobs p mode plo phi fz own B rm k →
      CmpFrame tab dm ra sa nS base rsp0 s →
      CmpAgree (bufSeq fz B rm k) (base + abiSlot * abiSlot64 tab out) (base + cmpW tab) (base + cmpNeed tab own)
        (base + abiNeed tab) (base + abiNeed tab + 64) rsp0 d5 s.dmem →
      Ev (CmpPost dm ra Acc Err) s (label abiCmpAfterL)) :
    ∀ n j (rm : Nat → Mem) (s : MachineData), j + n = k → rm 0 = zeroMem tab →
      CmpJobs p mode plo phi fz own B rm j → CmpFrame tab dm ra sa nS base rsp0 s →
      rdW s.dmem (A (base + abiNeed tab + 48)) = some (UInt64.ofNat k) →
      rdW s.dmem (A (base + abiNeed tab + 56)) = some (UInt64.ofNat j) →
      CmpAgree (bufSeq fz B rm j) (base + abiSlot * abiSlot64 tab out) (base + cmpW tab) (base + cmpNeed tab own)
        (base + abiNeed tab) (base + abiNeed tab + 64) rsp0 d5 s.dmem →
      RegionRel tab (base + cmpW tab) own (rm j) s.dmem →
      Ev (CmpPost dm ra Acc Err) s (label abiCmpLoopL) := by
  obtain ⟨hnb, htab, hneed64⟩ := abiTabOk_spec hok
  have hfits := hgeo.fits
  have hneed := hgeo.need
  have hr24 := hgeo.r24
  have hr8 := hgeo.r8
  have hbufLo := hgeo.bufLo
  have hbufHi := hgeo.bufHi
  have hb16 := hgeo.buf16
  have hn := abiNeed_ge hok
  have hwn : workerNeed own < 2 ^ 64 := by
    have : cmpNeed tab own < 2 ^ 64 := by omega
    simp only [cmpNeed, L.Compiler.cmpW] at this; omega
  simp only [cmpNeed, L.Compiler.cmpW] at hneed
  have hab : abiSlot = 2 ^ 35 := rfl
  have hcode' := hcode
  intro n
  induction n with
  | zero =>
    intro j rm s hjk h0 hjobs hf hsk hsj hag hreg
    simp only [Nat.add_zero] at hjk
    subst hjk
    rw [Code.label (i := 65) hC rfl]
    refine ev_label (hC.get (i := 65) rfl) ?_
    refine ev_movRI (hC.get (i := 66) rfl) ?_
    refine ev_binO (op := .add) (o := oR .r15) rfl (hC.get (i := 67) rfl)
      (Or.inr (Or.inr ⟨.r15, rfl, rfl⟩)) fun st => ?_
    have hsa : (BinOp.add.eval (cmpSave tab).toUInt64 s.regs.r15).toNat = base + abiNeed tab := by
      simp only [BinOp.eval, UInt64.toNat_add, cmpSave, hf.r15, Nat.toUInt64]
      rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
      omega
    refine ev_movRM (hC.get (i := 68) rfl) ⟨by decide, by decide⟩ (v := UInt64.ofNat j) ?_ ?_
    · rsimp; rw [hsa]; exact hsj
    refine ev_cmpRO (r := .rdx) (o := oM (mb .rax 48)) (v := UInt64.ofNat j) (hC.get (i := 69) rfl)
      (Or.inr (Or.inl ⟨.rax, 48, rfl, ⟨by decide, by decide⟩, ?_⟩)) ?_
    · rsimp; rw [hsa]; exact hsk
    refine ev_jcc (hC.get (i := 70) rfl) (fun _ => ?_) (fun hc' => ?_)
    · refine hAfter rm _ h0 hjobs (hf.regs rfl fun r h1 h2 h3 h4 h5 h6 h7 h8 => ?_) hag
      cases r <;> first | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd rfl h3 | rfl
    · rsimp at hc'
      rw [interp_nc] at hc'
      simp at hc'
  | succ n ih =>
    intro j rm s hjk h0 hjobs hf hsk hsj hag hreg
    have hjk' : j < k := by omega
    have hBs := bufSeq_size fz B rm j
    have hgj : BufGeom tab fz own (bufSeq fz B rm j) (base + abiSlot * abiSlot64 tab out) (base + cmpW tab)
        (workerNeed own) := hg.of_ok (bufSeq_ok hBok hh j hjobs j (Nat.le_refl _)) hBs
    rw [Code.label (i := 65) hC rfl]
    refine ev_label (hC.get (i := 65) rfl) ?_
    refine ev_movRI (hC.get (i := 66) rfl) ?_
    refine ev_binO (op := .add) (o := oR .r15) rfl (hC.get (i := 67) rfl)
      (Or.inr (Or.inr ⟨.r15, rfl, rfl⟩)) fun st => ?_
    have hsa : (BinOp.add.eval (cmpSave tab).toUInt64 s.regs.r15).toNat = base + abiNeed tab := by
      simp only [BinOp.eval, UInt64.toNat_add, cmpSave, hf.r15, Nat.toUInt64]
      rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
      omega
    refine ev_movRM (hC.get (i := 68) rfl) ⟨by decide, by decide⟩ (v := UInt64.ofNat j) ?_ ?_
    · rsimp; rw [hsa]; exact hsj
    refine ev_cmpRO (r := .rdx) (o := oM (mb .rax 48)) (v := UInt64.ofNat k) (hC.get (i := 69) rfl)
      (Or.inr (Or.inl ⟨.rax, 48, rfl, ⟨by decide, by decide⟩, ?_⟩)) ?_
    · rsimp; rw [hsa]; exact hsk
    refine ev_jcc (hC.get (i := 70) rfl) (fun hc' => ?_) (fun _ => ?_)
    · exfalso
      rsimp at hc'
      rw [interp_nc] at hc'
      simp only [decide_eq_true_eq, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' (show k < 2 ^ 64 by omega),
        UInt64.toNat_ofNat_of_lt' (show j < 2 ^ 64 by omega)] at hc'
      omega
    -- the call `ca_check_b(OUT, OUT[1], j, W, workerNeed)`
    refine ev_movRI (hC.get (i := 71) rfl) ?_
    refine ev_addR15 (hC.get (i := 72) rfl) fun st1 => ?_
    have hbufN : (((abiSlot * abiSlot64 tab out).toUInt64).toBitVec + s.regs.r15.toBitVec).toNat =
        base + abiSlot * abiSlot64 tab out := by
      rw [toNat_add_reg' _ _ (by rw [hf.r15]; omega), hf.r15]; omega
    obtain ⟨v8, hv8⟩ : ∃ v8, rdW s.dmem (A (base + abiSlot * abiSlot64 tab out + 8)) = some v8 :=
      Option.isSome_iff_exists.mp (isSome_rdW fun j hj => by
        rw [A_add]; exact hf.map _ (by omega) (by omega))
    refine ev_movRM (hC.get (i := 73) rfl) ⟨by decide, by decide⟩ (v := v8) ?_ ?_
    · rsimp; rw [hbufN]; exact hv8
    refine ev_movRI (hC.get (i := 74) rfl) ?_
    refine ev_addR15 (hC.get (i := 75) rfl) fun st2 => ?_
    refine ev_movRI (hC.get (i := 76) rfl) ?_
    have e1 : s.regs.rsp.toBitVec - 8 = A rsp0 := by
      rw [toBitVec_eq_A, hf.rsp, A_sub8 _ (by omega) (by omega)]; rfl
    refine ev_call (hC.get (i := 77) rfl) ?_ ?_
    · rsimp; rw [e1]; exact isSome_rdW fun j hj => by rw [A_add]; exact hf.win _ (by omega) (by omega)
    rsimp
    rw [e1]
    have hbufN' : ({ toBitVec := ((abiSlot * abiSlot64 tab out).toUInt64).toBitVec + s.regs.r15.toBitVec } : UInt64).toNat =
        base + abiSlot * abiSlot64 tab out := hbufN
    have hWN : ({ toBitVec := ((L.Compiler.cmpW tab).toUInt64).toBitVec + s.regs.r15.toBitVec } : UInt64).toNat =
        base + L.Compiler.cmpW tab := by
      show (((L.Compiler.cmpW tab).toUInt64).toBitVec + s.regs.r15.toBitVec).toNat = _
      rw [toNat_add_reg' _ _ (by rw [hf.r15]; simp only [L.Compiler.cmpW]; omega), hf.r15]; omega
    have hwN : ((workerNeed own).toUInt64).toNat = workerNeed own := UInt64.toNat_ofNat_of_lt' (by omega)
    have hA0 : ({ toBitVec := A rsp0 } : UInt64).toNat = rsp0 := by
      show (A rsp0).toNat = rsp0; simp only [A, BitVec.toNat_ofNat]; omega
    have hwin := hgeo.win
    -- the window is apart from the region (so from `W`, the buffer and the save area)
    have hwr : ∀ x, base ≤ x → x < base + dm.regs.r9.toNat → x < rsp0 - 24 ∨ rsp0 + 8 ≤ x := by
      intro x h1 h2
      refine Classical.byContradiction fun hn => ?_
      simp only [not_or, Nat.not_lt, Nat.not_le] at hn
      rcases hwin x hn.1 hn.2 with h | h <;> omega
    have hside : rsp0 + 8 ≤ base ∨ base + dm.regs.r9.toNat ≤ rsp0 - 24 := by
      rcases Nat.lt_or_ge (rsp0 - 24) base with h | h
      · by_cases h' : rsp0 + 8 ≤ base
        · exact .inl h'
        · exfalso; rcases hwin base (by omega) (by omega) with h2 | h2 <;> omega
      · rcases hwin (rsp0 - 24) (by omega) (by omega) with h2 | h2
        · omega
        · exact .inr h2
    refine ev_seq (abiB_outcome_w q p hq tab hok hAX hwf mode plo phi out hdrf ctlf hw fz own hngm hngl hngh h12 h13 h23
      hfzl k0 hcode fd hentry hnp (bufSeq fz B rm j) (rm j) _ (UInt64.ofBitVec (at_ (Kc + 77 + 1)).toBitVec) ?_ ?_ hmo
      (by rw [hBs]; have := hg.hdr 0 hfz0; omega)
      (by rsimp; rw [hwN]; have : 0 < workerNeed own := by simp only [workerNeed, abiSlot]; omega
          omega) hwn2) ?_
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only <;> (try rsimp)
      · rw [hbufN', hWN, hwN]; exact hgj
      · intro i hi
        rw [hBs] at hi
        rw [hbufN', rdW_wrW_A (by omega) (by omega) (by
          rcases hwr (base + abiSlot * abiSlot64 tab out + 8 * i) (by omega) (by omega) with h | h <;> omega)]
        exact hag.words i (by rw [hBs]; exact hi)
      · intro x h1 h2
        rw [hWN, hwN] at *
        exact isSome_get?_storeInt (hf.map x (by simp only [L.Compiler.cmpW] at h1; omega)
          (by simp only [L.Compiler.cmpW] at h2; omega))
      · rw [hA0, rdW_wrW_same]
      · intro x h1 h2
        rw [hA0] at h1 h2
        rw [hWN, hwN, hbufN']
        refine ⟨isSome_get?_storeInt (hf.win x h1 h2), ?_, ?_⟩
        · rcases hwin x h1 h2 with h | h
          · left; omega
          · right; simp only [L.Compiler.cmpW]; omega
        · intro ⟨h3, h4⟩; rcases hwin x h1 h2 with h | h <;> omega
      · rw [hA0]; omega
      · rw [hA0]; omega
    · dsimp only; (try rsimp)
      rw [hWN]
      exact hreg.transfer hok (Nat.le_refl _) fun x h1 h2 => by
        simp only [L.Compiler.cmpW] at h1 h2
        exact get?_wrW_A (by omega) (by omega) (by rcases hwr x (by omega) (by omega) with h | h <;> omega)
    · intro st ⟨hpc, hRR, hfr, hout⟩
      dsimp only at hRR hfr hout
      simp only [hbufN', hWN, hA0] at hfr hout
      rw [hpc]
      simp only [Int64.ofBitVec_toBitVec]
      generalize st.data = s1 at *
      -- the save area and everything below `W` but the buffer are in none of the call's layout's parts
      have hnot : ∀ x, x < base + abiNeed tab + 64 →
          ¬ (base + abiSlot * abiSlot64 tab out ≤ x ∧ x < base + abiSlot * abiSlot64 tab out + 8 * (bufSeq fz B rm j).size) →
          ¬ (bufLayout tab (base + abiSlot * abiSlot64 tab out) (bufSeq fz B rm j) (base + L.Compiler.cmpW tab) fz own).InStack x ∧
          ¬ (bufLayout tab (base + abiSlot * abiSlot64 tab out) (bufSeq fz B rm j) (base + L.Compiler.cmpW tab) fz own).InArr x ∧
          ¬ (bufLayout tab (base + abiSlot * abiSlot64 tab out) (bufSeq fz B rm j) (base + L.Compiler.cmpW tab) fz own).InTab x ∧
          x < (bufLayout tab (base + abiSlot * abiSlot64 tab out) (bufSeq fz B rm j) (base + L.Compiler.cmpW tab) fz own).tabEnd := by
        intro x h1 h2
        refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, ?_⟩
        · have := (buf_inStack h).region hgj (by omega); simp only [L.Compiler.cmpW] at this; omega
        · rcases buf_part hok hgj (.inr (.inl h)) with h | h
          · simp only [L.Compiler.cmpW] at h; omega
          · exact h2 h
        · have := (buf_inTab hok h).1.region hgj (by omega); simp only [L.Compiler.cmpW] at this; omega
        · simp only [Layout.tabEnd, bufLayout_T, L.Compiler.cmpW]; omega
      have hsv1 : ∀ x, base + abiNeed tab ≤ x → x < base + abiNeed tab + 64 →
          s1.dmem.get? (A x) = s.dmem.get? (A x) := by
        intro x h1 h2
        obtain ⟨q1, q2, q3, q4⟩ := hnot x h2 (by rw [hBs]; omega)
        rw [hfr.same x (by omega) q1 q2 q3 (by rcases hwr x (by omega) (by omega) with h | h <;> omega)
          (Or.inl q4), get?_wrW_A (by omega) (by omega) (by rcases hwr x (by omega) (by omega) with h | h <;> omega)]
      have hgrow1 : ∀ y, (s.dmem.get? y).isSome → (s1.dmem.get? y).isSome :=
        fun y hy => hfr.grows _ (isSome_get?_storeInt hy)
      have hf1 : CmpFrame tab dm ra sa nS base rsp0 s1 :=
        hf.ret (by omega) hr8 hA0 (fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 => by
          cases r <;> first | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd rfl h3 | exact absurd rfl h4 |
            exact absurd rfl h5 | exact absurd rfl h6 | exact absurd rfl h7 | exact absurd rfl h8 | exact absurd rfl h9 | rfl)
          hRR hsv1 hgrow1
      have hsk1 : rdW s1.dmem (A (base + abiNeed tab + 48)) = some (UInt64.ofNat k) := by
        rw [← hsk]; exact rdW_congr fun j hj => by rw [A_add]; exact hsv1 _ (by omega) (by omega)
      have hsj1 : rdW s1.dmem (A (base + abiNeed tab + 56)) = some (UInt64.ofNat j) := by
        rw [← hsj]; exact rdW_congr fun j hj => by rw [A_add]; exact hsv1 _ (by omega) (by omega)
      have hexit := fun (s' : MachineData) (hf' : CmpFrame tab dm ra sa nS base rsp0 s') hacc herr =>
        cmp_exit hC dm ra sa (by omega) ⟨hr24, hr8⟩ hrsp0 Acc Err s' hf' hacc herr
      show Ev _ s1 (at_ (Kc + 78))
      refine ev_cmpRO (r := .rdx) (o := oI 0) (v := 0) (hC.get (i := 78) rfl) (Or.inl rfl) ?_
      refine ev_jcc (hC.get (i := 79) rfl) (fun hnz => ?_) (fun hz0 => ?_)
      · refine hexit _ (hf1.regs rfl fun r _ _ _ _ _ _ _ _ => rfl) (fun h0 => ?_) (fun h2 => ?_)
        · simp only [CondCode.interp, cmpFlags_zf, Reg64s.get64_rdx] at hnz
          exact absurd hnz (by rw [h0]; decide)
        · obtain ⟨e, he, hk'⟩ := err_of_entryOut hout h2
          rw [hk']
          exact hErr rm h0 j hjk' hjobs e he
      simp only [CondCode.interp, cmpFlags_zf, Reg64s.get64_rdx] at hz0
      have hrdx0 : s1.regs.rdx = 0 := by
        simp only [Bool.not_eq_false', beq_iff_eq] at hz0
        exact UInt64.toBitVec_inj.mp hz0
      have hout' := hout.resolve_left (by rw [hrdx0]; decide)
      rcases hres : L.run p abiFuel "check" [] (bufMemG fz own plo phi mode (bufSeq fz B rm j) (rm j) (UInt64.ofNat j)) with e | ⟨rs, r'⟩
      · rw [hres] at hout'
        cases e <;> simp only [OutcomeRel] at hout' <;> (rw [hrdx0] at hout'; exact absurd hout'.1 (by decide))
      rw [hres] at hout'
      obtain ⟨-, hRes, hMem⟩ := hout'
      have hrax : s1.regs.rax = rs.getD 0 0 := hRes.1 0 (by simp only [bufLayout_tab]; omega) (by decide)
      refine ev_movRI (hC.get (i := 80) rfl) ?_
      refine ev_cmpRO (r := .rax) (o := oR .rcx) (v := ACCEPT) (hC.get (i := 81) rfl)
        (Or.inr (Or.inr ⟨.rcx, rfl, rfl⟩)) ?_
      refine ev_jcc (hC.get (i := 82) rfl) (fun hne => ?_) (fun heq => ?_)
      · refine hexit _ (hf1.regs rfl fun r h1 h2 _ _ _ _ _ _ => by
            cases r <;> first | exact absurd rfl h2 | rfl) (fun _ hacc => ?_) (fun h2 => ?_)
        · simp only [CondCode.interp, cmpFlags_zf] at hne
          rsimp at hne hacc
          exact absurd hne (by rw [hacc]; simp [ACCEPT])
        · rsimp at h2; rw [hrdx0] at h2; exact absurd h2 (by decide)
      simp only [CondCode.interp, cmpFlags_zf] at heq
      rsimp at heq
      have hacc : rs.getD 0 0 = ACCEPT := by
        rw [← hrax]
        simp only [Bool.not_eq_false', beq_iff_eq] at heq
        exact UInt64.toBitVec_inj.mp heq
      -- the job accepted: the next job's start
      have hag0 := hag.wrW (y := rsp0) (v := (at_ (Kc + 65 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)).toBitVec)
        (by omega) (fun x h1 h2 => .inl ⟨by omega, by omega⟩)
        (by omega) (by omega)
      have hag1 := hag0.job hok hnd hdom hgj (by simp only [cmpNeed, L.Compiler.cmpW]; omega) (fun x h1 h2 => ⟨fun ⟨h3, h4⟩ => by
          simp only [L.Compiler.cmpW] at h3; omega, by rw [hBs] at h2; omega⟩)
        hfr hMem
      have hreg1 : RegionRel tab (base + L.Compiler.cmpW tab) own r' s1.dmem := RegionRel.of_memRel hdisj hMem
      have hsa1 : (BinOp.add.eval (cmpSave tab).toUInt64 s1.regs.r15).toNat = base + abiNeed tab := by
        simp only [BinOp.eval, UInt64.toNat_add, cmpSave, hf1.r15, Nat.toUInt64]
        rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
        omega
      refine ev_movRI (hC.get (i := 83) rfl) ?_
      refine ev_binO (op := .add) (o := oR .r15) rfl (hC.get (i := 84) rfl)
        (Or.inr (Or.inr ⟨.r15, rfl, rfl⟩)) fun st3 => ?_
      refine ev_movRM (hC.get (i := 85) rfl) ⟨by decide, by decide⟩ (v := UInt64.ofNat j) ?_ ?_
      · rsimp; rw [hsa1]; exact hsj1
      refine ev_addRI (hC.get (i := 86) rfl) fun st4 => ?_
      refine ev_movMR (hC.get (i := 87) rfl) ⟨by decide, by decide⟩ ?_ ?_
      · rsimp; rw [hsa1]
        exact isSome_rdW fun i hi => by rw [A_add]; exact hf1.map _ (by omega) (by omega)
      refine ev_jmp (hC.get (i := 88) rfl) ?_
      rsimp
      rw [hsa1]
      have hj1 : (UInt64.ofNat j).toBitVec + (Int64.ofInt 1).toBitVec = (UInt64.ofNat (j + 1)).toBitVec := by
        apply BitVec.eq_of_toNat_eq
        have h1 : (Int64.ofInt 1).toBitVec.toNat = 1 := by decide
        simp only [BitVec.toNat_add, UInt64.toNat_toBitVec, UInt64.toNat_ofNat_of_lt' (show j < 2 ^ 64 by omega),
          UInt64.toNat_ofNat_of_lt' (show j + 1 < 2 ^ 64 by omega), h1]
        omega
      have hcg : ∀ i ≤ j, bufSeq fz B (fun i => if i ≤ j then rm i else r') i = bufSeq fz B rm i :=
        fun i hi => bufSeq_congr i fun i' hi' => by simp only [show i' ≤ j by omega, ite_true]
      have hnext : bufSeq fz B (fun i => if i ≤ j then rm i else r') (j + 1) = bufNext fz (bufSeq fz B rm j) r' := by
        show bufNext fz (bufSeq fz B _ j) (if j + 1 ≤ j then rm (j + 1) else r') = _
        rw [hcg j (Nat.le_refl _), ite_eq_right (by omega)]
      refine ih (j + 1) (fun i => if i ≤ j then rm i else r') _ (by omega) (by simp [h0]) ?_ ?_ ?_ ?_ ?_ ?_
      · intro i hi
        by_cases hij : i < j
        · obtain ⟨rs', h1, h2⟩ := hjobs i hij
          refine ⟨rs', ?_, h2⟩
          rw [hcg i (by omega)]
          simp only [show i ≤ j by omega, show i + 1 ≤ j by omega, ite_true]
          exact h1
        · obtain rfl : i = j := by omega
          refine ⟨rs, ?_, hacc⟩
          rw [hcg i (Nat.le_refl _)]
          simp only [Nat.le_refl, ite_true, show ¬ i + 1 ≤ i by omega, ite_false]
          exact hres
      · exact (hf1.regs (s' := { s1 with regs := _, status := st4 }) rfl fun r h1 h2 h3 _ _ _ _ _ => by
          cases r <;> first | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd rfl h3 | rfl).wr (by omega)
          hside (by omega) (by omega)
      · show rdW (wrW s1.dmem _ _) _ = _
        rw [rdW_wrW_A (by omega) (by omega) (by omega)]; exact hsk1
      · show rdW (wrW s1.dmem (A (base + abiNeed tab + 56)) _) _ = _
        rw [rdW_wrW_same, hj1]
      · rw [hnext]
        exact hag1.wrW (by omega) (fun x h1 h2 => .inr ⟨by omega, by omega⟩) (by rw [bufNext_size, hBs]; omega)
          (by rw [bufNext_size, hBs]; omega)
      · simp only [show ¬ j + 1 ≤ j by omega, ite_false]
        exact hreg1.transfer hok (Nat.le_refl _) fun x h1 h2 => by
          simp only [L.Compiler.cmpW] at h1 h2
          exact get?_wrW_A (by omega) (by omega) (by omega)

end

end ConAgua.Final
