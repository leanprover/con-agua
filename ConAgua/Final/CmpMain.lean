module

public import ConAgua.Final.CmpLoop
import ConAgua.Compiler.Sim32
import Kraken.X64.Registers

@[expose] public section

/-!
# `ca_compare` on the machine: the theorem (lane compare)

`cmp_modeM`: the driver's call of a mode entry on a region that holds an L memory (modes `5`, `6`:
the arguments from the save area, `abiModeM_outcome`). `cmp_outcome`: the whole driver, from
`CmpCall` and the L-level facts `CmpGuard`.
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

/-- **A mode entry's call on a region that holds an L memory** (`cmpArgsS`, then `call lab`, nine
directives at `i`; the entry's seven directives at `e`): the solution's buffer `bs` at `sa` (from
the save area), the pin data `pb` at the caller's `rdx`, the region `[base, base + abiNeed)`
holding `m` in the stub's layout for some old input. The continuation gets the frame back, the
memory outside the region's first `abiNeed` bytes, the two buffers and the window unchanged, and
`rdx = 1` or the run of `check` from `m` with the input `bs` and the mode word `w`. -/
theorem cmp_modeM (q p : Prog) (hq : Refines q p) (hok : abiTabOk tab = true)
    {X : AsmTab} (hAX : AsmOkT q tab X) (hio : abiIO tab = true)
    (hwf : Prog.wf tab q = true) (hng : mode.id < tab.ng) (k0 : Nat)
    (hcR : Code (abiStub tab ++ compileProgX X tab q "check") k0)
    (fd : FunDecl) (hentry : p.lookup "check" = some fd) (hnp : fd.nparams = 0)
    {Kc : Nat} (hC : Code (cmpStubL tab mode out own) Kc) (i e : Nat) (w : Word) (lab : Label)
    (hblk : ∀ t (_ : t < 9), (cmpStubL tab mode out own)[i + t]? = (cmpArgsS tab ++ [callL lab])[t]?)
    (hen : ∀ t (_ : t < 7), (cmpStubL tab mode out own)[e + t]? =
      [.label lab, movRI .rax (abiNeed tab).toUInt64, i64 (.cmp (.reg (rr .r9)) (oR .rax)), jccL .c abiSetupL,
       movRI .rax w, movMR (mb .r8 (tab.globOff mode)) .rax, jmpL abiSetupL][t]?)
    (dm : MachineData) (ra sa : Word) {nS base rsp0 : Nat} (bs pb : ByteArray) (hnS : nS = bs.size)
    {buf0 nB0 : Nat} (hgeo : CmpGeo tab own base dm.regs.r9.toNat rsp0 buf0 nB0)
    (hside : rsp0 + 8 ≤ base ∨ base + dm.regs.r9.toNat ≤ rsp0 - 24)
    (hnP : dm.regs.rcx.toNat = pb.size)
    (hSend : sa.toNat + bs.size < 2 ^ 64) (hPend : dm.regs.rdx.toNat + pb.size < 2 ^ 64)
    (hSg : ∀ x, sa.toNat ≤ x → x < sa.toNat + bs.size → (x < base ∨ base + dm.regs.r9.toNat ≤ x) ∧
      (x < rsp0 - 24 ∨ rsp0 + 8 ≤ x) ∧ ¬ (dm.regs.rdx.toNat ≤ x ∧ x < dm.regs.rdx.toNat + pb.size))
    (hPg : ∀ x, dm.regs.rdx.toNat ≤ x → x < dm.regs.rdx.toNat + pb.size → (x < base ∨ base + dm.regs.r9.toNat ≤ x) ∧
      (x < rsp0 - 24 ∨ rsp0 + 8 ≤ x))
    (Acc : Prop) (Err : Word → Prop) (s : MachineData) (hf : CmpFrame tab dm ra sa nS base rsp0 s)
    (hS : ∀ i (h : i < bs.size), s.dmem.get? (A (sa.toNat + i)) = some bs[i])
    (hP : ∀ i (h : i < pb.size), s.dmem.get? (A (dm.regs.rdx.toNat + i)) = some pb[i])
    {m : Mem} {inp0 n0 : Nat}
    (hG0 : (abiLayout tab base inp0 n0 dm.regs.rdx.toNat pb.size).Ok)
    (h0g : ∀ x, inp0 ≤ x → x < inp0 + n0 → x < rsp0 - 24 ∨ rsp0 + 8 ≤ x)
    (hm : MemRel (abiLayout tab base inp0 n0 dm.regs.rdx.toNat pb.size) m s.dmem)
    (hk : ∀ s' : MachineData, CmpFrame tab dm ra sa nS base rsp0 s' →
      (∀ x < 2 ^ 64, (x < base ∨ base + abiNeed tab ≤ x) → ¬ (sa.toNat ≤ x ∧ x < sa.toNat + bs.size) →
        ¬ (dm.regs.rdx.toNat ≤ x ∧ x < dm.regs.rdx.toNat + pb.size) → (x < rsp0 - 24 ∨ rsp0 + 8 ≤ x) →
        s'.dmem.get? (A x) = s.dmem.get? (A x)) →
      (s'.regs.rdx = 1 ∨ OutcomeRel (abiLayout tab base sa.toNat bs.size dm.regs.rdx.toNat pb.size)
        (cmpRun p ((cmpIn m bs).setG mode w)) s') →
      (s'.regs.rdx = 1 ∨ (bs.size < 2 ^ 63 ∧ pb.size < 2 ^ 63)) →
      Ev (CmpPost dm ra Acc Err) s' (at_ (Kc + i + 9))) :
    Ev (CmpPost dm ra Acc Err) s (at_ (Kc + i)) := by
  obtain ⟨hnb, htab, hneed64⟩ := abiTabOk_spec hok
  have hfits := hgeo.fits
  have hneed := hgeo.need
  have hr24 := hgeo.r24
  have hr8 := hgeo.r8
  have hwin := hgeo.win
  have hn := abiNeed_ge hok
  simp only [cmpNeed, L.Compiler.cmpW] at hneed
  have hab : abiSlot = 2 ^ 35 := rfl
  have hsa : (BinOp.add.eval (cmpSave tab).toUInt64 s.regs.r15).toNat = base + abiNeed tab := by
    simp only [BinOp.eval, UInt64.toNat_add, cmpSave, hf.r15, Nat.toUInt64]
    rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
    omega
  refine ev_movRI (hC.get (i := i + 0) ((hblk 0 (by omega)).trans rfl)) ?_
  refine ev_binO (op := .add) (o := oR .r15) rfl (hC.get (i := i + 1) ((hblk 1 (by omega)).trans rfl))
    (Or.inr (Or.inr ⟨.r15, rfl, rfl⟩)) fun st => ?_
  refine ev_movRM (hC.get (i := i + 2) ((hblk 2 (by omega)).trans rfl)) ⟨by decide, by decide⟩ (v := sa) ?_ ?_
  · rsimp; rw [hsa]; exact hf.sv2
  refine ev_movRM (hC.get (i := i + 3) ((hblk 3 (by omega)).trans rfl)) ⟨by decide, by decide⟩
    (v := UInt64.ofNat nS) ?_ ?_
  · rsimp; rw [hsa]; exact hf.sv3
  refine ev_movRM (hC.get (i := i + 4) ((hblk 4 (by omega)).trans rfl)) ⟨by decide, by decide⟩
    (v := dm.regs.rdx) ?_ ?_
  · rsimp; rw [hsa]; exact hf.sv4
  refine ev_movRM (hC.get (i := i + 5) ((hblk 5 (by omega)).trans rfl)) ⟨by decide, by decide⟩
    (v := dm.regs.rcx) ?_ ?_
  · rsimp; rw [hsa]; exact hf.sv5
  refine ev_movRR (hC.get (i := i + 6) ((hblk 6 (by omega)).trans rfl)) ?_
  refine ev_movRI (hC.get (i := i + 7) ((hblk 7 (by omega)).trans rfl)) ?_
  have e1 : s.regs.rsp.toBitVec - 8 = A rsp0 := by
    rw [toBitVec_eq_A, hf.rsp, A_sub8 _ (by omega) (by omega)]; rfl
  refine ev_call (hC.get (i := i + 8) ((hblk 8 (by omega)).trans rfl)) ?_ ?_
  · rsimp; rw [e1]; exact isSome_rdW fun j hj => by rw [A_add]; exact hf.win _ (by omega) (by omega)
  rsimp
  rw [e1]
  have hbN : s.regs.r15.toNat = base := hf.r15
  have hneedN : ((abiNeed tab).toUInt64).toNat = abiNeed tab :=
    UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
  have hA0 : ({ toBitVec := A rsp0 } : UInt64).toNat = rsp0 := by
    show (A rsp0).toNat = rsp0; simp only [A, BitVec.toNat_ofNat]; omega
  have hnSN : (UInt64.ofNat nS).toNat = bs.size := by
    rw [hnS]; exact UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
  -- the window is apart from the region, the buffers
  have hwS : ∀ x, sa.toNat ≤ x → x < sa.toNat + bs.size → x < rsp0 ∨ rsp0 + 8 ≤ x := fun x h1 h2 => by
    rcases (hSg x h1 h2).2.1 with h | h <;> omega
  have hwP : ∀ x, dm.regs.rdx.toNat ≤ x → x < dm.regs.rdx.toNat + pb.size → x < rsp0 ∨ rsp0 + 8 ≤ x :=
    fun x h1 h2 => by rcases (hPg x h1 h2).2 with h | h <;> omega
  refine ev_seq (abiModeM_outcome q p hq tab hok hAX hio hwf mode hng w lab (Kc + e) k0
    (Code.label (i := e + 0) hC ((hen 0 (by omega)).trans rfl))
    (hC.get (i := e + 0) ((hen 0 (by omega)).trans rfl)) (hC.get (i := e + 1) ((hen 1 (by omega)).trans rfl))
    (hC.get (i := e + 2) ((hen 2 (by omega)).trans rfl)) (hC.get (i := e + 3) ((hen 3 (by omega)).trans rfl))
    (hC.get (i := e + 4) ((hen 4 (by omega)).trans rfl)) (hC.get (i := e + 5) ((hen 5 (by omega)).trans rfl))
    (hC.get (i := e + 6) ((hen 6 (by omega)).trans rfl)) hcR fd hentry hnp bs pb _
    (UInt64.ofBitVec (at_ (Kc + i + 9)).toBitVec) ?_ (m := m) (inp0 := inp0) (n0 := n0) ?_) ?_
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only <;> (try rsimp)
    · intro j hj
      rw [get?_wrW_A (by omega) (by omega) (by rcases hwS (sa.toNat + j) (by omega) (by omega) with h | h <;> omega)]
      exact hS j hj
    · exact hnSN
    · intro j hj
      rw [get?_wrW_A (by omega) (by omega) (by rcases hwP (dm.regs.rdx.toNat + j) (by omega) (by omega) with h | h <;> omega)]
      exact hP j hj
    · exact hnP
    · intro x h1 h2
      rw [hbN, hneedN] at *
      exact isSome_get?_storeInt (hf.map x h1 (by omega))
    · rw [hbN, hneedN]; omega
    · exact hSend
    · exact hPend
    · intro x h1 h2
      rw [hbN, hneedN]
      rcases (hSg x h1 h2).1 with h | h
      · exact .inl h
      · exact .inr (by omega)
    · intro x h1 h2
      rw [hbN, hneedN]
      rcases (hPg x h1 h2).1 with h | h
      · exact .inl h
      · exact .inr (by omega)
    · intro x h1 h2; exact (hSg x h1 h2).2.2
    · rw [hA0, rdW_wrW_same]
    · intro x h1 h2
      rw [hA0] at h1 h2
      rw [hbN, hneedN]
      refine ⟨isSome_get?_storeInt (hf.win x h1 h2), by omega, fun ⟨h3, h4⟩ => ?_, fun ⟨h3, h4⟩ => ?_⟩
      · rcases (hSg x h3 h4).2.1 with h | h <;> omega
      · rcases (hPg x h3 h4).2 with h | h <;> omega
    · rw [hA0]; omega
    · rw [hA0]; omega
  · intro _
    dsimp only; (try rsimp)
    rw [hbN]
    refine hm.only' hG0 (Only.wrW (x := rsp0) (by omega)) fun x h1 h2 => ?_
    obtain ⟨-, q2, q3⟩ := abiLayout_out hok (blen := abiNeed tab) (base := base) (inp := inp0) (n := n0)
      (pins := dm.regs.rdx.toNat) (np := pb.size) (x := x) (Nat.le_refl _)
      (by rcases hside with h | h <;> omega) (fun ⟨h3, h4⟩ => by rcases h0g x h3 h4 with h | h <;> omega)
      (fun ⟨h3, h4⟩ => by rcases (hPg x h3 h4).2 with h | h <;> omega)
    exact ⟨q3, q2⟩
  · intro st ⟨⟨hpc, hRR, hfr, hout⟩, hsz⟩
    dsimp only at hRR hfr hout
    simp only [hbN, hA0] at hfr hout
    rw [hpc]
    simp only [Int64.ofBitVec_toBitVec]
    unfold SizesPost at hsz
    generalize st.data = s1 at *
    -- outside the region's first `abiNeed` bytes, the buffers and the window, nothing changed
    have hsame : ∀ x < 2 ^ 64, (x < base ∨ base + abiNeed tab ≤ x) → ¬ (sa.toNat ≤ x ∧ x < sa.toNat + bs.size) →
        ¬ (dm.regs.rdx.toNat ≤ x ∧ x < dm.regs.rdx.toNat + pb.size) → (x < rsp0 - 24 ∨ rsp0 + 8 ≤ x) →
        s1.dmem.get? (A x) = s.dmem.get? (A x) := by
      intro x hx hreg hs hp hw
      obtain ⟨q1, q2, q3⟩ := abiLayout_out hok (blen := abiNeed tab) (Nat.le_refl _) hreg hs hp
      rw [hfr.same x hx q1 q2 q3 (by omega) (by
        rcases hreg with h | h
        · left; simp only [Layout.tabEnd, abiLayout_T, abiLayout_tab, abiLayout_nargs]; omega
        · right; simp only [Layout.tabEnd, abiLayout_T, abiLayout_tab, abiLayout_nargs]; omega),
        get?_wrW_A (by omega) hx (by omega)]
    have hsv1 : ∀ x, base + abiNeed tab ≤ x → x < base + abiNeed tab + 64 → s1.dmem.get? (A x) = s.dmem.get? (A x) :=
      fun x h1 h2 => hsame x (by omega) (.inr h1)
        (fun ⟨h3, h4⟩ => by rcases (hSg x h3 h4).1 with h | h <;> omega)
        (fun ⟨h3, h4⟩ => by rcases (hPg x h3 h4).1 with h | h <;> omega)
        (by rcases hside with h | h <;> omega)
    have hf1 : CmpFrame tab dm ra sa nS base rsp0 s1 :=
      hf.ret (by omega) hr8 hA0 (fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 => by
          cases r <;> first | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd rfl h3 | exact absurd rfl h4 |
            exact absurd rfl h5 | exact absurd rfl h6 | exact absurd rfl h7 | exact absurd rfl h8 | exact absurd rfl h9 | rfl)
        hRR hsv1 fun y hy => hfr.grows _ (isSome_get?_storeInt hy)
    exact hk s1 hf1 hsame hout hsz

omit [Host] in
/-- `out`'s array in the stub's layout: at its slot (`abiSlot64`), `abiWords` long. -/
theorem cmp_out_pos (hok : abiTabOk tab = true) {hdrf ctlf : ArrId} {hw : Nat}
    (hp : seqParamsOk tab out hdrf ctlf hw = true) (base inp n pins np : Nat) :
    (abiLayout tab base inp n pins np).b (tab.pos64 (TieredArray.t0 out)) = base + abiSlot * abiSlot64 tab out ∧
    (abiLayout tab base inp n pins np).s (tab.pos64 (TieredArray.t0 out)) = abiWords ∧
    2 ≤ abiSlot64 tab out ∧ abiSlot64 tab out < tab.nslot := by
  obtain ⟨hnb, -, -⟩ := abiTabOk_spec hok
  obtain ⟨h2, hlt, he⟩ := seq_out_slot hok hp
  obtain ⟨dout, -⟩ := seqParamsOk_spec hp
  have hw := tab.wAt_pos64 dout
  have htb := (seqParamsOk_tbl hp).1
  refine ⟨?_, ?_, by omega, by omega⟩
  · rw [abiLayout_b64 _ _ _ _ _ _ h2, abiOff_slot (by rw [hw]; exact htb), Tab.slotOf_eq hnb, he]
  · rw [abiLayout_s64 _ _ _ _ _ _ h2, hw]; simp only [abiSz]; rw [show tab.tbl64 (TieredArray.t0 out) = none from htb]

omit [Host] in
/-- **The buffer's words** in a memory that holds `m` in the stub's layout. -/
theorem cmp_buf_words (hok : abiTabOk tab = true) {hdrf ctlf : ArrId} {hw : Nat}
    (hp : seqParamsOk tab out hdrf ctlf hw = true) {base inp n pins np : Nat} {m : Mem} {d : DataMem}
    (hm : MemRel (abiLayout tab base inp n pins np) m d)
    (hlen : ((m.arr64 out).getD 1 0).toNat ≤ (m.arr64 out).size) :
    (cmpBuf out m).size ≤ abiWords ∧ ∀ i (h : i < (cmpBuf out m).size),
      rdW d (A (base + abiSlot * abiSlot64 tab out + 8 * i)) = some (cmpBuf out m)[i] := by
  obtain ⟨dout, -⟩ := seqParamsOk_spec hp
  obtain ⟨hb, hs, -, -⟩ := cmp_out_pos hok hp base inp n pins np
  have hsz := hm.size64 _ dout
  simp only [abiLayout_tab] at hsz
  rw [hs] at hsz
  have hbs : (cmpBuf out m).size = ((m.arr64 out).getD 1 0).toNat := by
    simp only [cmpBuf, Array.size_extract]; omega
  refine ⟨by rw [hbs]; change _ ≤ (m.arr64 (TieredArray.t0 out)).size at hlen; omega, fun i hi => ?_⟩
  have hi' : i < (m.arr64 (TieredArray.t0 out)).size := by rw [hbs] at hi; change _ ≤ (m.arr64 (TieredArray.t0 out)).size at hlen; omega
  have := hm.get64 _ dout i hi'
  simp only [abiLayout_tab] at this
  rw [hb] at this
  rw [this]
  simp only [cmpBuf, Array.getElem_extract, Nat.zero_add]

omit [Host] in
/-- **After the jobs, the region still holds mode `5`'s memory** (`CmpAgree`, `MemRel.congrW`). -/
theorem cmp_agree_memRel (hok : abiTabOk tab = true) {hdrf ctlf : ArrId} {hw : Nat}
    (hp : seqParamsOk tab out hdrf ctlf hw = true) {base blen rsp0 sa n pins np : Nat} {m5 : Mem}
    {d5 d : DataMem} (hneedC : cmpNeed tab own ≤ blen) (hfit : base + blen < 2 ^ 64)
    (hG : (abiLayout tab base sa n pins np).Ok) (hm : MemRel (abiLayout tab base sa n pins np) m5 d5)
    (hlen : ((m5.arr64 out).getD 1 0).toNat ≤ (m5.arr64 out).size)
    (hSa : ∀ x, sa ≤ x → x < sa + n → (x < base ∨ base + blen ≤ x) ∧ (x < rsp0 - 24 ∨ rsp0 + 8 ≤ x))
    (hPa : ∀ x, pins ≤ x → x < pins + np → (x < base ∨ base + blen ≤ x) ∧ (x < rsp0 - 24 ∨ rsp0 + 8 ≤ x))
    (hwin : ∀ x, rsp0 - 24 ≤ x → x < rsp0 + 8 → x < base ∨ base + blen ≤ x)
    (hA : CmpAgree (cmpBuf out m5) (base + abiSlot * abiSlot64 tab out) (base + L.Compiler.cmpW tab)
      (base + cmpNeed tab own) (base + abiNeed tab) (base + abiNeed tab + 64) rsp0 d5 d) :
    MemRel (abiLayout tab base sa n pins np) m5 d := by
  obtain ⟨hnb, htab, hneed64⟩ := abiTabOk_spec hok
  obtain ⟨hbo, hso, h2, hlt⟩ := cmp_out_pos hok hp base sa n pins np
  obtain ⟨hBs, hBw⟩ := cmp_buf_words hok hp hm hlen
  obtain ⟨dout, -⟩ := seqParamsOk_spec hp
  have hpo := (tab.pos64_lt dout)
  have hn := abiNeed_ge hok
  simp only [cmpNeed, L.Compiler.cmpW] at hneedC
  have hab : abiSlot = 2 ^ 35 := rfl
  have hwd : abiWords = 2 ^ 32 := rfl
  have hslot : abiSlot * abiSlot64 tab out + abiSlot ≤ abiNeed tab := by
    rw [abiNeed_eq, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
  have h2s : abiSlot * 2 ≤ abiSlot * abiSlot64 tab out := Nat.mul_le_mul_left _ h2
  -- inside the stub's part of the region, off the buffer: unchanged
  have hreg : ∀ x, base ≤ x → x < base + abiNeed tab →
      ¬ (base + abiSlot * abiSlot64 tab out ≤ x ∧ x < base + abiSlot * abiSlot64 tab out + 8 * (cmpBuf out m5).size) →
      d.get? (A x) = d5.get? (A x) := fun x h1 h2 hb =>
    hA.same x (by omega) (fun ⟨h3, _⟩ => by simp only [L.Compiler.cmpW] at h3; omega)
      (by
        refine Classical.byContradiction fun hn => ?_
        simp only [not_or, Nat.not_lt, Nat.not_le] at hn
        rcases hwin x hn.1 hn.2 with h | h <;> omega)
      (fun ⟨h3, _⟩ => by omega) hb
  -- outside the region and the window: unchanged
  have hout : ∀ x, x < 2 ^ 64 → (x < base ∨ base + blen ≤ x) → (x < rsp0 - 24 ∨ rsp0 + 8 ≤ x) →
      d.get? (A x) = d5.get? (A x) := fun x hx h1 h2 =>
    hA.same x hx (fun ⟨h3, h4⟩ => by simp only [cmpNeed, L.Compiler.cmpW] at h3 h4; omega) h2 (fun ⟨h3, h4⟩ => by omega)
      (fun ⟨h3, h4⟩ => by omega)
  refine MemRel.congrW hG hm hA.grows (fun x hx => ?_) (fun q hq x hx => ?_) (fun q hq1 hq2 i hi => ?_)
  · have ht := hx.2
    simp only [Layout.tabEnd, abiLayout_T, abiLayout_tab, abiLayout_nargs] at ht
    have := hx.1
    simp only [abiLayout_T] at this
    exact hreg x this (by omega) (fun ⟨h3, _⟩ => by omega)
  · unfold Layout.In8 at hx
    simp only [abiLayout_tab] at hq
    rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl
    · simp only [abiLayout_b8_0, abiLayout_s8_0] at hx
      obtain ⟨h1, h2⟩ := hSa x hx.1 hx.2
      have := hG.end8 0 (by simp [hnb])
      simp only [abiLayout_b8_0, abiLayout_s8_0] at this
      exact hout x (by omega) h1 h2
    · simp only [abiLayout_b8_1, abiLayout_s8_1] at hx
      obtain ⟨h1, h2⟩ := hPa x hx.1 hx.2
      have := hG.end8 1 (by simp [hnb])
      simp only [abiLayout_b8_1, abiLayout_s8_1] at this
      exact hout x (by omega) h1 h2
  · simp only [abiLayout_tab] at hq1 hq2
    by_cases hc : q = tab.pos64 (TieredArray.t0 out) ∧ i < (cmpBuf out m5).size
    · obtain ⟨rfl, hi'⟩ := hc
      rw [hbo, hA.words i hi', hBw i hi']
    · refine rdW_congr fun j hj => ?_
      rw [A_add]
      have hin : (abiLayout tab base sa n pins np).In64 q ((abiLayout tab base sa n pins np).b q + 8 * i + j) :=
        ⟨by omega, by omega⟩
      have hb := abiLayout_in64_bounds hok (by omega) hq2 hin
      refine hreg _ (by omega) hb.2 fun ⟨h3, h4⟩ => ?_
      by_cases hq : q = tab.pos64 (TieredArray.t0 out)
      · subst hq
        rw [hbo] at h3 h4
        exact hc ⟨rfl, by omega⟩
      · refine hG.arr64_disj q ⟨by simp [abiLayout_tab]; omega, by simp [abiLayout_tab]; omega⟩
          (tab.pos64 (TieredArray.t0 out)) ⟨hpo.1, hpo.2⟩ hq _ hin ⟨?_, ?_⟩
        · rw [hbo]; omega
        · rw [hbo, hso]; omega

/-- **The compared run's driver on the machine**: from `ca_compare`, called as `CmpCall` says, the
machine returns to the caller with the callee-saved registers restored; `rdx = 0`, `rax = ACCEPT`
means the runs accepted (`CmpAccepts`), `rdx = 2` that one failed with the code in `rax`
(`CmpErr`). `CmpGuard`: the L-level facts the proof needs (the buffer's geometry after mode `5`,
the jobs keep the frozen arrays). -/
theorem cmp_outcome_regs (q p : Prog) (hq : Refines q p) (tab : Tab) (hok : abiTabOk tab = true)
    {X : AsmTab} (hAX : AsmOkT q tab X) (hio : abiIO tab = true) (hwf : Prog.wf tab q = true)
    (hnres : 1 ≤ tab.nres) (mode plo phi : GVar) (out hdrf ctlf : ArrId) (hw : Nat) (fz own : List TieredArray)
    (hngm : mode.id < tab.ng) (hngl : plo.id < tab.ng) (hngh : phi.id < tab.ng)
    (h12 : plo ≠ phi) (h13 : plo ≠ mode) (h23 : phi ≠ mode) (hfzl : fz.length < 2 ^ 20)
    (hp : seqParamsOk tab out hdrf ctlf hw = true) (hmo : bufMinOk tab fz own = true)
    (hdisj : ∀ a ∈ own, a ∉ fz) (hcn : cmpNeed tab own < 2 ^ 64) (k0 : Nat)
    (hcode : Code (parStub tab mode plo phi out hdrf ctlf hw fz own ++
      (abiStub tab ++ (compileProgX X tab q "check" ++ cmpStub tab mode out own))) k0)
    (fd : FunDecl) (hentry : p.lookup "check" = some fd) (hnp : fd.nparams = 0)
    (bC bS pb : ByteArray) (sa : Word) (dm : MachineData) (ra : Word) (hc : CmpCall bC bS pb sa dm ra)
    (hG : CmpGuard tab p mode plo phi out fz own bC bS pb) :
    Ev (CmpPost dm ra (CmpAccepts tab p mode plo phi out hdrf ctlf hw fz own bC bS pb)
      (CmpErr tab p mode plo phi out hdrf ctlf hw fz own bC bS pb)) dm (label abiCompareL) := by
  obtain ⟨hnb, htab, hneed64⟩ := abiTabOk_spec hok
  have hcodeO : Code (parStub tab mode plo phi out hdrf ctlf hw fz own ++
      (abiStub tab ++ compileProgX X tab q "check")) k0 := by
    have h := hcode
    rw [← List.append_assoc (abiStub tab), ← List.append_assoc] at h
    exact h.left
  obtain ⟨Kc, hC⟩ : ∃ Kc, Code (cmpStubL tab mode out own) Kc :=
    ⟨_, by have h := hcode.right.right.right; rwa [cmpStub_lit] at h⟩
  obtain ⟨base, hbase⟩ : ∃ base, dm.regs.r8.toNat = base := ⟨_, rfl⟩
  obtain ⟨rsp0, hrsp0⟩ : ∃ rsp0, dm.regs.rsp.toNat = rsp0 := ⟨_, rfl⟩
  have hfits := hc.hfits
  have hcs8 := hc.hcs8
  have hcs24 := hc.hcs24
  have hsEnd := hc.hsEnd
  have hn := abiNeed_ge hok
  have hab : abiSlot = 2 ^ 35 := rfl
  rw [Code.label (i := 21) hC rfl]
  refine ev_label (hC.get (i := 21) rfl) ?_
  refine ev_movRI (hC.get (i := 22) rfl) ?_
  refine ev_cmpRO (r := .r9) (o := oR .rax) (v := (cmpNeed tab own).toUInt64) (hC.get (i := 23) rfl)
    (Or.inr (Or.inr ⟨.rax, rfl, rfl⟩)) ?_
  refine ev_jcc (hC.get (i := 24) rfl) (fun hlt => ?_) (fun hge => ?_)
  · -- declined
    rw [Code.label (i := 118) hC rfl]
    refine ev_label (hC.get (i := 118) rfl) ?_
    refine ev_movRI (hC.get (i := 119) rfl) ?_
    refine ev_movRI (hC.get (i := 120) rfl) ?_
    refine ev_ret (hC.get (i := 121) rfl) (ra := ra)
      (by rsimp; rw [toBitVec_eq_A]; exact hc.hra) ?_
    refine Eventually.done _ ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun h => ?_, fun h => ?_⟩ <;> dsimp only at * <;>
      (try rsimp at *)
    · simp only [UInt64.toNat_ofBitVec, BitVec.toNat_add, UInt64.toNat_toBitVec, show (8 : BitVec 64).toNat = 8 from rfl]
      omega
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  rsimp at hge
  rw [interp_c] at hge
  have hge' : cmpNeed tab own ≤ dm.regs.r9.toNat := by
    simp only [decide_eq_false_iff_not, UInt64.lt_iff_toNat_lt, Nat.not_lt] at hge
    rw [show ((cmpNeed tab own).toUInt64).toNat = cmpNeed tab own from UInt64.toNat_ofNat_of_lt' hcn] at hge
    exact hge
  have hneedC := hge'
  simp only [cmpNeed, L.Compiler.cmpW] at hneedC
  have hcs := hc.hcs
  have hz := hc.hzero
  rw [hbase, hrsp0] at hcs
  rw [hbase] at hz hfits
  rw [hrsp0] at hcs8 hcs24 hsEnd
  have hside : rsp0 + 8 ≤ base ∨ base + dm.regs.r9.toNat ≤ rsp0 - 24 := by
    rcases Nat.lt_or_ge (rsp0 - 24) base with h | h
    · by_cases h' : rsp0 + 8 ≤ base
      · exact .inl h'
      · exfalso; rcases (hcs base (by omega) (by omega)).2.1 with h2 | h2 <;> omega
    · rcases (hcs (rsp0 - 24) (by omega) (by omega)).2.1 with h2 | h2
      · omega
      · exact .inr h2
  -- mode 4: the call of `ca_start_a4` from a state with the frame
  have key4 : ∀ s0 : MachineData, CmpFrame tab dm ra sa bS.size base rsp0 s0 →
      s0.regs.rdi = dm.regs.rdi → s0.regs.rsi = dm.regs.rsi → s0.regs.rdx = dm.regs.rdx →
      s0.regs.rcx = dm.regs.rcx → s0.regs.r8 = dm.regs.r8 → s0.regs.r9.toNat = abiNeed tab →
      Only (base + abiNeed tab) (base + abiNeed tab + 48) dm.dmem s0.dmem →
      Ev (CmpPost dm ra (CmpAccepts tab p mode plo phi out hdrf ctlf hw fz own bC bS pb)
        (CmpErr tab p mode plo phi out hdrf ctlf hw fz own bC bS pb)) s0 (at_ (Kc + 38)) := by
    intro s0 hf0 hdi hsi hdx hcx h8 h9 honly
    have e1 : s0.regs.rsp.toBitVec - 8 = A rsp0 := by
      rw [toBitVec_eq_A, hf0.rsp, A_sub8 _ (by omega) (by omega)]; rfl
    have hA0 : ({ toBitVec := A rsp0 } : UInt64).toNat = rsp0 := by
      show (A rsp0).toNat = rsp0; simp only [A, BitVec.toNat_ofNat]; omega
    refine ev_call (hC.get (i := 38) rfl) ?_ ?_
    · rw [e1]; exact isSome_rdW fun j hj => by rw [A_add]; exact hf0.win _ (by omega) (by omega)
    rw [e1]
    refine ev_seq (abiMode_outcome q p hq tab hok hAX hio hwf mode hngm 4 abiStartA4L Kc _
      (Code.label (i := 0) hC rfl) (hC.get (i := 0) rfl) (hC.get (i := 1) rfl) (hC.get (i := 2) rfl)
      (hC.get (i := 3) rfl) (hC.get (i := 4) rfl) (hC.get (i := 5) rfl) (hC.get (i := 6) rfl)
      hcodeO.right fd hentry hnp bC pb _ (UInt64.ofBitVec (at_ (Kc + 38 + 1)).toBitVec) ?_) ?_
    · refine hc.toAbiCall.shrink _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> dsimp only <;> (try rsimp)
      · exact hdi
      · exact hsi
      · exact hdx
      · exact hcx
      · exact h8
      · exact UInt64.toBitVec_inj.mp (by rw [toBitVec_eq_A dm.regs.rsp, hrsp0])
      · rw [h9]; omega
      · exact fun y hy => isSome_get?_storeInt (honly.grows y hy)
      · intro x hx h1 h2
        rw [hbase, h9] at h1
        rw [hrsp0] at h2
        rw [get?_wrW_A (by omega) hx (by omega), honly.same x hx (by omega)]
      · rw [hrsp0, rdW_wrW_same]
    intro st ⟨⟨hpc, hRR, hfr, hout⟩, hsz⟩
    dsimp only at hRR hfr hout
    simp only [Reg64s.set64_rsp, hdi, hdx, h8, hbase, hA0] at hfr hout
    rw [hpc]
    simp only [Int64.ofBitVec_toBitVec]
    unfold SizesPost at hsz
    generalize st.data = s1 at *
    have hcsW : ∀ x, rsp0 - 24 ≤ x → x < rsp0 + 8 → x < base ∨ base + dm.regs.r9.toNat ≤ x :=
      fun x h1 h2 => (hcs x h1 h2).2.1
    -- outside the stub's part of the region, the buffers, the window and the save area: the caller's
    have hsame1 : ∀ x < 2 ^ 64, (x < base ∨ base + abiNeed tab ≤ x) →
        ¬ (dm.regs.rdi.toNat ≤ x ∧ x < dm.regs.rdi.toNat + bC.size) →
        ¬ (dm.regs.rdx.toNat ≤ x ∧ x < dm.regs.rdx.toNat + pb.size) → (x < rsp0 - 24 ∨ rsp0 + 8 ≤ x) →
        s1.dmem.get? (A x) = s0.dmem.get? (A x) := by
      intro x hx hreg hi hp hw
      obtain ⟨q1, q2, q3⟩ := abiLayout_out hok (blen := abiNeed tab) (Nat.le_refl _) hreg hi hp
      rw [hfr.same x hx q1 q2 q3 (by omega) (by
        rcases hreg with h | h
        · left; simp only [Layout.tabEnd, abiLayout_T, abiLayout_tab, abiLayout_nargs]; omega
        · right; simp only [Layout.tabEnd, abiLayout_T, abiLayout_tab, abiLayout_nargs]; omega),
        get?_wrW_A (by omega) hx (by omega)]
    have hinR : ∀ x, dm.regs.rdi.toNat ≤ x → x < dm.regs.rdi.toNat + bC.size → x < base ∨ base + dm.regs.r9.toNat ≤ x :=
      fun x h1 h2 => by have := hc.hinDisj x h1 h2; rwa [hbase] at this
    have hpR : ∀ x, dm.regs.rdx.toNat ≤ x → x < dm.regs.rdx.toNat + pb.size → x < base ∨ base + dm.regs.r9.toNat ≤ x :=
      fun x h1 h2 => by have := hc.hpinsDisj x h1 h2; rwa [hbase] at this
    have hsv1 : ∀ x, base + abiNeed tab ≤ x → x < base + abiNeed tab + 64 → s1.dmem.get? (A x) = s0.dmem.get? (A x) :=
      fun x h1 h2 => hsame1 x (by omega) (.inr h1) (fun ⟨h3, h4⟩ => by rcases hinR x h3 h4 with h | h <;> omega)
        (fun ⟨h3, h4⟩ => by rcases hpR x h3 h4 with h | h <;> omega) (by rcases hside with h | h <;> omega)
    have hf1 : CmpFrame tab dm ra sa bS.size base rsp0 s1 :=
      hf0.ret (by omega) (by omega) (by rsimp; exact hA0) (fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 => by
          cases r <;> first | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd rfl h3 | exact absurd rfl h4 |
            exact absurd rfl h5 | exact absurd rfl h6 | exact absurd rfl h7 | exact absurd rfl h8 | exact absurd rfl h9 | rfl)
        hRR hsv1 fun y hy => hfr.grows _ (isSome_get?_storeInt hy)
    have hexit := fun (s' : MachineData) (hf' : CmpFrame tab dm ra sa bS.size base rsp0 s') hacc herr =>
      cmp_exit hC dm ra sa (by omega) ⟨hcs24, hcs8⟩ hrsp0
        (CmpAccepts tab p mode plo phi out hdrf ctlf hw fz own bC bS pb)
        (CmpErr tab p mode plo phi out hdrf ctlf hw fz own bC bS pb) s' hf' hacc herr
    refine cmp_okGe (i := 39) hC rfl rfl rfl rfl rfl s1 (fun s' hm hr hbad => ?_) (fun hrdx hge4 st4 => ?_)
    · have erax : s'.regs.rax = s1.regs.rax := by
        have := hr .rax (by decide); simpa using congrArg UInt64.ofBitVec this
      have erdx : s'.regs.rdx = s1.regs.rdx := by
        have := hr .rdx (by decide); simpa using congrArg UInt64.ofBitVec this
      refine hexit s' (hf1.regs hm fun r _ h2 _ _ _ _ _ _ => hr r h2) (fun h0 hacc => ?_) (fun h2 => ?_)
      · rw [erdx] at h0; rw [erax] at hacc
        have hout' := hout.resolve_left (by rw [h0]; decide)
        obtain ⟨hb, hpb⟩ := hsz.resolve_left (by rw [h0]; decide)
        rcases hres : L.run p abiFuel "check" [] ((loadMem bC pb (abiSz tab)).setG mode 4) with e | ⟨rs4, m4⟩
        · rw [hres] at hout'
          cases e <;> simp only [OutcomeRel] at hout' <;> (rw [h0] at hout'; exact absurd hout'.1 (by decide))
        rw [hres] at hout'
        obtain ⟨-, hRes, -⟩ := hout'
        have hrax : s1.regs.rax = rs4.getD 0 0 := hRes.1 0 (by simp only [abiLayout_tab]; omega) (by decide)
        exact ⟨hb, hpb, rs4, m4, hres, .inl (by rw [← hrax]; exact hacc)⟩
      · rw [erdx] at h2; rw [erax]
        obtain ⟨hb, hpb⟩ := hsz.resolve_left (by rw [h2]; decide)
        obtain ⟨e, he, hk⟩ := err_of_entryOut hout h2
        exact ⟨hb, hpb, .inl ⟨e, he, hk.symm⟩⟩
    -- mode 4 returned `2^63 + _`: its memory `m4`
    have hout' := hout.resolve_left (by rw [hrdx]; decide)
    obtain ⟨hbC, hpb⟩ := hsz.resolve_left (by rw [hrdx]; decide)
    rcases hres4 : L.run p abiFuel "check" [] ((loadMem bC pb (abiSz tab)).setG mode 4) with e | ⟨rs4, m4⟩
    · rw [hres4] at hout'
      cases e <;> simp only [OutcomeRel] at hout' <;> (rw [hrdx] at hout'; exact absurd hout'.1 (by decide))
    rw [hres4] at hout'
    obtain ⟨-, hRes4, hMem4⟩ := hout'
    have hrax4 : s1.regs.rax = rs4.getD 0 0 := hRes4.1 0 (by simp only [abiLayout_tab]; omega) (by decide)
    have hio' := hio
    simp only [abiIO, Bool.and_eq_true, beq_iff_eq] at hio'
    obtain ⟨⟨⟨hdIN, hpIN⟩, hdPB⟩, hpPB⟩ := hio'
    have hPBs : (m4.arr8 Rom.PB).size = pb.size := by
      have := hMem4.size8 _ hdPB; simp only [abiLayout_tab, hpPB, abiLayout_s8_1] at this; exact this
    have hcx : dm.regs.rcx.toNat = (⟨m4.arr8 Rom.PB⟩ : ByteArray).size := by rw [hc.hnp]; exact hPBs.symm
    have hpbE : (⟨m4.arr8 Rom.PB⟩ : ByteArray).size = pb.size := hPBs
    have hgeoM : CmpGeo tab own base dm.regs.r9.toNat rsp0 (base + abiSlot * abiSlot64 tab out) 0 := by
      obtain ⟨-, -, h2, hlt⟩ := cmp_out_pos hok hp base 0 0 0 0
      have hslot : abiSlot * abiSlot64 tab out + abiSlot ≤ abiNeed tab := by
        rw [abiNeed_eq, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
      have h2s : abiSlot * 2 ≤ abiSlot * abiSlot64 tab out := Nat.mul_le_mul_left _ h2
      exact ⟨hfits, hge', hcsW, hcs24, hcs8, by omega, by omega, by omega⟩
    refine cmp_modeM q p hq hok hAX hio hwf hngm _ hcodeO.right fd hentry hnp hC 44 7 5 abiStartA5L
      (fun t ht => match t, ht with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl | 7, _ => rfl | 8, _ => rfl | _ + 9, h => absurd h (by omega))
      (fun t ht => match t, ht with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl | _ + 7, h => absurd h (by omega))
      dm ra sa bS ⟨m4.arr8 Rom.PB⟩ rfl hgeoM hside hcx hc.hSEnd (by rw [hpbE]; exact hc.hpinsEnd)
      (fun x h1 h2 => ?_) (fun x h1 h2 => ?_) _ _ _
      (hf1.regs rfl fun r _ h2 _ _ _ _ _ _ => by cases r <;> first | exact absurd rfl h2 | rfl) (fun i hi => ?_)
      (fun i hi => ?_) (m := m4) (inp0 := dm.regs.rdi.toNat) (n0 := bC.size) ?_ (fun x h1 h2 => ?_) ?_ ?_
    · -- hSg
      obtain ⟨q1, q2, q3, q4⟩ := hc.hSDisj x h1 h2
      rw [hbase] at q1
      exact ⟨q1, by rw [hrsp0] at q4; omega, by rw [hpbE]; exact q3⟩
    · -- hPg
      rw [hpbE] at h2
      refine ⟨hpR x h1 h2, ?_⟩
      refine Classical.byContradiction fun hn => ?_
      simp only [not_or, Nat.not_lt, Nat.not_le] at hn
      exact (hcs x (by omega) (by omega)).2.2.2 ⟨h1, h2⟩
    · -- the solution's bytes
      obtain ⟨q1, q2, q3, q4⟩ := hc.hSDisj (sa.toNat + i) (by omega) (by omega)
      rw [hbase] at q1; rw [hrsp0] at q4
      rw [hsame1 _ (by have := hc.hSEnd; omega) (by rcases q1 with h | h <;> omega) q2 q3 q4,
        honly.same _ (by have := hc.hSEnd; omega) (by rcases q1 with h | h <;> omega)]
      exact hc.hS i hi
    · -- the pin data as mode 4 left it
      have hg := hMem4.get8 _ hdPB i hi
      simp only [abiLayout_tab, hpPB, abiLayout_b8_1] at hg
      exact hg
    · rw [hpbE]
      exact abiLayout_ok hok ⟨Nat.le_refl _, by omega, hc.hinEnd, hc.hpinsEnd,
        fun x h1 h2 => by rcases hinR x h1 h2 with h | h <;> omega,
        fun x h1 h2 => by rcases hpR x h1 h2 with h | h <;> omega, hc.hbufDisj⟩
    · refine Classical.byContradiction fun hn => ?_
      simp only [not_or, Nat.not_lt, Nat.not_le] at hn
      exact (hcs x (by omega) (by omega)).2.2.1 ⟨h1, h2⟩
    · rw [hpbE]; exact hMem4
    intro s2 hf2 hsame2 hout5 hsz5
    have hge4' : 2 ^ 63 ≤ (rs4.getD 0 0).toNat := by rw [← hrax4]; exact hge4
    refine ev_congr (cmp_okGe (i := 53) hC rfl rfl rfl rfl rfl s2 (fun s' hm hr hbad => ?_) (fun hrdx5 hge5 st5 => ?_)) (by omega)
    · have erax : s'.regs.rax = s2.regs.rax := by
        have := hr .rax (by decide); simpa using congrArg UInt64.ofBitVec this
      have erdx : s'.regs.rdx = s2.regs.rdx := by
        have := hr .rdx (by decide); simpa using congrArg UInt64.ofBitVec this
      refine hexit s' (hf2.regs hm fun r _ h2 _ _ _ _ _ _ => hr r h2) (fun h0 hacc => ?_) (fun h2 => ?_)
      · rw [erdx] at h0; rw [erax] at hacc
        have hout' := hout5.resolve_left (by rw [h0]; decide)
        obtain ⟨hbS, -⟩ := hsz5.resolve_left (by rw [h0]; decide)
        rcases hres : cmpRun p ((cmpIn m4 bS).setG mode 5) with e | ⟨rs5, m5⟩
        · rw [hres] at hout'
          cases e <;> simp only [OutcomeRel] at hout' <;> (rw [h0] at hout'; exact absurd hout'.1 (by decide))
        rw [hres] at hout'
        obtain ⟨-, hRes, -⟩ := hout'
        have hrax : s2.regs.rax = rs5.getD 0 0 := hRes.1 0 (by simp only [abiLayout_tab]; omega) (by decide)
        exact ⟨hbC, hpb, rs4, m4, hres4, .inr ⟨hge4', hbS, rs5, m5, hres, .inl (by rw [← hrax]; exact hacc)⟩⟩
      · rw [erdx] at h2; rw [erax]
        obtain ⟨hbS, -⟩ := hsz5.resolve_left (by rw [h2]; decide)
        obtain ⟨e, he, hk⟩ := err_of_entryOut hout5 h2
        exact ⟨hbC, hpb, .inr ⟨rs4, m4, hres4, hge4', hbS, .inl ⟨e, he, hk.symm⟩⟩⟩
    -- mode 5 returned `2^63 + k`: its memory `m5`, the jobs
    have hout' := hout5.resolve_left (by rw [hrdx5]; decide)
    obtain ⟨hbS, -⟩ := hsz5.resolve_left (by rw [hrdx5]; decide)
    rcases hres5 : cmpRun p ((cmpIn m4 bS).setG mode 5) with e | ⟨rs5, m5⟩
    · rw [hres5] at hout'
      cases e <;> simp only [OutcomeRel] at hout' <;> (rw [hrdx5] at hout'; exact absurd hout'.1 (by decide))
    rw [hres5] at hout'
    obtain ⟨-, hRes5, hMem5⟩ := hout'
    have hrax5 : s2.regs.rax = rs5.getD 0 0 := hRes5.1 0 (by simp only [abiLayout_tab]; omega) (by decide)
    have hge5' : 2 ^ 63 ≤ (rs5.getD 0 0).toNat := by rw [← hrax5]; exact hge5
    obtain ⟨hBok, hkeep⟩ := hG rs4 m4 rs5 m5 hres4 hge4' hres5 hge5'
    have hk63 : (rs5.getD 0 0 - 9223372036854775808).toNat < 2 ^ 63 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simpa using hge5')]
      have := (rs5.getD 0 0).toNat_lt; simp at this ⊢; omega
    have hsa2 : (BinOp.add.eval (cmpSave tab).toUInt64 s2.regs.r15).toNat = base + abiNeed tab := by
      simp only [BinOp.eval, UInt64.toNat_add, cmpSave, hf2.r15, Nat.toUInt64]
      rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
      omega
    refine ev_binO (op := .sub) (o := oR .rcx) (v := 9223372036854775808) rfl (hC.get (i := 58) rfl)
      (Or.inr (Or.inr ⟨.rcx, rfl, rfl⟩)) fun st6 => ?_
    refine ev_movRR (hC.get (i := 59) rfl) ?_
    refine ev_movRI (hC.get (i := 60) rfl) ?_
    refine ev_binO (op := .add) (o := oR .r15) rfl (hC.get (i := 61) rfl)
      (Or.inr (Or.inr ⟨.r15, rfl, rfl⟩)) fun st7 => ?_
    refine ev_movMR (hC.get (i := 62) rfl) ⟨by decide, by decide⟩ ?_ ?_
    · rsimp; rw [hsa2]; exact isSome_rdW fun j hj => by rw [A_add]; exact hf2.map _ (by omega) (by omega)
    refine ev_movRI (hC.get (i := 63) rfl) ?_
    refine ev_movMR (hC.get (i := 64) rfl) ⟨by decide, by decide⟩ ?_ ?_
    · rsimp; rw [hsa2]
      exact isSome_rdW fun j hj => by rw [A_add]; exact isSome_get?_storeInt (hf2.map _ (by omega) (by omega))
    rsimp
    rw [hsa2]
    refine ev_congr (j := Kc + 65) ?_ (by omega)
    rw [← Code.label (i := 65) hC rfl]
    obtain ⟨hBw, hBwords⟩ := cmp_buf_words hok hp hMem5 hBok.1
    obtain ⟨-, -, h2o, hlto⟩ := cmp_out_pos hok hp base 0 0 0 0
    have hslot : abiSlot * abiSlot64 tab out + abiSlot ≤ abiNeed tab := by
      rw [abiNeed_eq, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlto
    have h2s : abiSlot * 2 ≤ abiSlot * abiSlot64 tab out := Nat.mul_le_mul_left _ h2o
    have hwd : abiWords = 2 ^ 32 := rfl
    have hgeoB : CmpGeo tab own base dm.regs.r9.toNat rsp0 (base + abiSlot * abiSlot64 tab out)
        (cmpBuf out m5).size := ⟨hfits, hge', hcsW, hcs24, hcs8, by omega, by omega, by omega⟩
    have hgB : BufGeom tab fz own (cmpBuf out m5) (base + abiSlot * abiSlot64 tab out) (base + L.Compiler.cmpW tab)
        (workerNeed own) :=
      ⟨Nat.le_refl _, by simp only [L.Compiler.cmpW]; omega, by omega, hBok.2.1, hBok.2.2.1, hBok.2.2.2,
        fun x h1 h2 => .inl (by simp only [L.Compiler.cmpW]; omega)⟩
    have hS0 : ∀ x, sa.toNat ≤ x → x < sa.toNat + bS.size → x < base ∨ base + dm.regs.r9.toNat ≤ x :=
      fun x h1 h2 => by have := (hc.hSDisj x h1 h2).1; rwa [hbase] at this
    refine cmp_loop q p hq hok hAX hwf hnres plo phi hdrf ctlf hw fz hngm hngl hngh h12 h13 h23 hfzl k0 hcodeO fd
      hentry hnp hmo hdisj hC dm ra sa (nS := bS.size) (cmpBuf out m5) _ hk63 hgeoB hgB
      hkeep hrsp0 s2.dmem _ _ ?_ ?_ (rs5.getD 0 0 - 9223372036854775808).toNat 0 (fun _ => zeroMem tab) _ (Nat.zero_add _) rfl
      (fun j hj => absurd hj (by omega)) ?_ ?_ ?_ ?_ ?_
    · intro rm h0 j hj hjobs e he
      exact ⟨hbC, hpb, .inr ⟨rs4, m4, hres4, hge4', hbS, .inr ⟨rs5, m5, hres5, hge5', rm, h0,
        .inl ⟨j, hj, hjobs, e, he, rfl⟩⟩⟩⟩
    · -- after the jobs: mode 6
      intro rm s3 h0 hjobs hf3 hag3
      rw [Code.label (i := 89) hC rfl]
      refine ev_label (hC.get (i := 89) rfl) ?_
      have hIN : (m5.arr8 IN).size = bS.size := by
        have := hMem5.size8 _ hdIN; simp only [abiLayout_tab, hpIN, abiLayout_s8_0] at this; exact this
      have hPB5 : (m5.arr8 Rom.PB).size = pb.size := by
        have := hMem5.size8 _ hdPB; simp only [abiLayout_tab, hpPB, abiLayout_s8_1] at this; rw [this]; exact hpbE
      have hpb5 : (⟨m5.arr8 Rom.PB⟩ : ByteArray).size = pb.size := hPB5
      have hin5 : (⟨m5.arr8 IN⟩ : ByteArray).size = bS.size := hIN
      have hSa : ∀ x, sa.toNat ≤ x → x < sa.toNat + bS.size →
          (x < base ∨ base + dm.regs.r9.toNat ≤ x) ∧ (x < rsp0 - 24 ∨ rsp0 + 8 ≤ x) := fun x h1 h2 => by
        obtain ⟨q1, -, -, q4⟩ := hc.hSDisj x h1 h2
        rw [hbase] at q1; rw [hrsp0] at q4; exact ⟨q1, q4⟩
      have hPa : ∀ x, dm.regs.rdx.toNat ≤ x → x < dm.regs.rdx.toNat + pb.size →
          (x < base ∨ base + dm.regs.r9.toNat ≤ x) ∧ (x < rsp0 - 24 ∨ rsp0 + 8 ≤ x) := fun x h1 h2 => by
        refine ⟨hpR x h1 h2, Classical.byContradiction fun hn => ?_⟩
        simp only [not_or, Nat.not_lt, Nat.not_le] at hn
        exact (hcs x (by omega) (by omega)).2.2.2 ⟨h1, h2⟩
      have hG5 : (abiLayout tab base sa.toNat bS.size dm.regs.rdx.toNat pb.size).Ok :=
        abiLayout_ok hok ⟨Nat.le_refl _, by omega, hc.hSEnd, hc.hpinsEnd,
          fun x h1 h2 => by rcases (hSa x h1 h2).1 with h | h <;> omega,
          fun x h1 h2 => by rcases hpR x h1 h2 with h | h <;> omega,
          fun x h1 h2 => (hc.hSDisj x h1 h2).2.2.1⟩
      rw [hpbE] at hMem5
      have hMem5' := cmp_agree_memRel hok hp hge' hfits hG5 hMem5 hBok.1 hSa hPa hcsW hag3
      refine ev_congr (j := Kc + 90) ?_ (by omega)
      refine cmp_modeM q p hq hok hAX hio hwf hngm _ hcodeO.right fd hentry hnp hC 90 14 6 abiStartA6L
        (fun t ht => match t, ht with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl | 7, _ => rfl | 8, _ => rfl | _ + 9, h => absurd h (by omega))
        (fun t ht => match t, ht with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl | _ + 7, h => absurd h (by omega))
        dm ra sa (nS := bS.size) ⟨m5.arr8 IN⟩ ⟨m5.arr8 Rom.PB⟩ hin5.symm hgeoB hside (by rw [hpb5, hc.hnp])
        (by rw [hin5]; exact hc.hSEnd) (by rw [hpb5]; exact hc.hpinsEnd)
        (fun x h1 h2 => ?_) (fun x h1 h2 => ?_) _ _ s3 hf3 (fun i hi => ?_) (fun i hi => ?_)
        (m := m5) (inp0 := sa.toNat) (n0 := bS.size) (by rw [hpb5]; exact hG5)
        (fun x h1 h2 => (hSa x h1 h2).2) (by rw [hpb5]; exact hMem5') ?_
      · rw [hin5] at h2
        obtain ⟨q1, q2⟩ := hSa x h1 h2
        exact ⟨q1, q2, by rw [hpb5]; exact (hc.hSDisj x h1 h2).2.2.1⟩
      · rw [hpb5] at h2; exact hPa x h1 h2
      · have hg := hMem5'.get8 _ hdIN i hi
        simp only [abiLayout_tab, hpIN, abiLayout_b8_0] at hg
        exact hg
      · have hg := hMem5'.get8 _ hdPB i hi
        simp only [abiLayout_tab, hpPB, abiLayout_b8_1] at hg
        exact hg
      intro s4 hf4 hsame4 hout6 hsz6
      rw [cmpIn_self] at hout6
      simp only [hin5, hpb5] at hout6
      refine ev_congr (cmp_okGe (i := 99) hC rfl rfl rfl rfl rfl s4 (fun s' hm hr hbad => ?_)
        (fun hrdx6 hge6 st8 => ?_)) (by omega)
      · have erax : s'.regs.rax = s4.regs.rax := by
          have := hr .rax (by decide); simpa using congrArg UInt64.ofBitVec this
        have erdx : s'.regs.rdx = s4.regs.rdx := by
          have := hr .rdx (by decide); simpa using congrArg UInt64.ofBitVec this
        refine hexit s' (hf4.regs hm fun r _ h2 _ _ _ _ _ _ => hr r h2) (fun h0' hacc => ?_) (fun h2 => ?_)
        · rw [erdx] at h0'; rw [erax] at hacc
          have hout' := hout6.resolve_left (by rw [h0']; decide)
          rcases hres : cmpRun p (m5.setG mode 6) with e | ⟨rs6, m6⟩
          · rw [hres] at hout'
            cases e <;> simp only [OutcomeRel] at hout' <;> (rw [h0'] at hout'; exact absurd hout'.1 (by decide))
          rw [hres] at hout'
          obtain ⟨-, hRes, -⟩ := hout'
          have hrax : s4.regs.rax = rs6.getD 0 0 := hRes.1 0 (by simp only [abiLayout_tab]; omega) (by decide)
          exact ⟨hbC, hpb, rs4, m4, hres4, .inr ⟨hge4', hbS, rs5, m5, hres5, .inr ⟨hge5', rm, h0, hjobs,
            rs6, m6, hres, .inl (by rw [← hrax]; exact hacc)⟩⟩⟩
        · rw [erdx] at h2; rw [erax]
          obtain ⟨e, he, hk⟩ := err_of_entryOut hout6 h2
          exact ⟨hbC, hpb, .inr ⟨rs4, m4, hres4, hge4', hbS, .inr ⟨rs5, m5, hres5, hge5', rm, h0,
            .inr ⟨hjobs, .inl ⟨e, he, hk.symm⟩⟩⟩⟩⟩
      -- mode 6 returned `2^63 + k'`: `ca_check_seq` for `[0, k')`
      have hout' := hout6.resolve_left (by rw [hrdx6]; decide)
      rcases hres6 : cmpRun p (m5.setG mode 6) with e | ⟨rs6, m6⟩
      · rw [hres6] at hout'
        cases e <;> simp only [OutcomeRel] at hout' <;> (rw [hrdx6] at hout'; exact absurd hout'.1 (by decide))
      rw [hres6] at hout'
      obtain ⟨-, hRes6, hMem6⟩ := hout'
      have hrax6 : s4.regs.rax = rs6.getD 0 0 := hRes6.1 0 (by simp only [abiLayout_tab]; omega) (by decide)
      have hge6' : 2 ^ 63 ≤ (rs6.getD 0 0).toNat := by rw [← hrax6]; exact hge6
      refine ev_binO (op := .sub) (o := oR .rcx) (v := 9223372036854775808) rfl (hC.get (i := 104) rfl)
        (Or.inr (Or.inr ⟨.rcx, rfl, rfl⟩)) fun st9 => ?_
      refine ev_movRR (hC.get (i := 105) rfl) ?_
      refine ev_movRI (hC.get (i := 106) rfl) ?_
      refine ev_movRR (hC.get (i := 107) rfl) ?_
      have e1 : s4.regs.rsp.toBitVec - 8 = A rsp0 := by
        rw [toBitVec_eq_A, hf4.rsp, A_sub8 _ (by omega) (by omega)]; rfl
      have hA0 : ({ toBitVec := A rsp0 } : UInt64).toNat = rsp0 := by
        show (A rsp0).toNat = rsp0; simp only [A, BitVec.toNat_ofNat]; omega
      refine ev_call (hC.get (i := 108) rfl) ?_ ?_
      · rsimp; rw [e1]; exact isSome_rdW fun j hj => by rw [A_add]; exact hf4.win _ (by omega) (by omega)
      rsimp
      rw [e1]
      refine ev_seq (abiS_outcome q p hq tab hok hAX hwf mode plo phi out hdrf ctlf hw fz own hngm hngl hngh hp k0
        hcodeO fd hentry hnp (base := base) (blen := abiNeed tab) (inp := sa.toNat) (n := bS.size)
        (pins := dm.regs.rdx.toNat) (np := pb.size) m6 _ (UInt64.ofBitVec (at_ (Kc + 108 + 1)).toBitVec) ?_ ?_) ?_
      · refine ⟨Nat.le_refl _, by omega, ?_, fun x h1 h2 => ?_, ?_, fun x h1 h2 => ?_, ?_, ?_⟩ <;> dsimp only <;>
          (try rsimp)
        · exact hf4.r15
        · exact isSome_get?_storeInt (hf4.map x h1 (by omega))
        · rw [hA0, rdW_wrW_same]
        · rw [hA0] at h1 h2
          exact ⟨isSome_get?_storeInt (hf4.win x h1 h2), by rcases hcsW x h1 h2 with h | h <;> omega⟩
        · rw [hA0]; omega
        · rw [hA0]; omega
      · dsimp only
        refine hMem6.only' hG5 (Only.wrW (x := rsp0) (by omega)) fun x h1 h2 => ?_
        obtain ⟨-, q2, q3⟩ := abiLayout_out hok (blen := abiNeed tab) (base := base) (inp := sa.toNat)
          (n := bS.size) (pins := dm.regs.rdx.toNat) (np := pb.size) (x := x) (Nat.le_refl _)
          (by rcases hside with h | h <;> omega) (fun ⟨h3, h4⟩ => by rcases (hSa x h3 h4).2 with h | h <;> omega)
          (fun ⟨h3, h4⟩ => by rcases (hPa x h3 h4).2 with h | h <;> omega)
        exact ⟨q3, q2⟩
      intro st ⟨hpc, hRR, hfr, hout7⟩
      dsimp only at hRR hfr hout7
      simp only [hA0] at hfr
      rw [hpc]
      simp only [Int64.ofBitVec_toBitVec]
      generalize st.data = s5 at *
      have hsv5 : ∀ x, base + abiNeed tab ≤ x → x < base + abiNeed tab + 64 →
          s5.dmem.get? (A x) = s4.dmem.get? (A x) := by
        intro x h1 h2
        obtain ⟨q1, q2, q3⟩ := seq_out (base := base) (out := out) (hdrf := hdrf) (ctlf := ctlf) (hw := hw) hok hp
          (blen := abiNeed tab) (Nat.le_refl _) (x := x) (Or.inr h1)
        rw [hfr.same x (by omega) q1 q2 q3 (by rcases hside with h | h <;> omega)
          (Or.inr (by simp only [Layout.tabEnd, seqLayout_T, seqLayout_tab, seqLayout_nargs]; omega)),
          get?_wrW_A (by omega) (by omega) (by rcases hside with h | h <;> omega)]
      have hf5 : CmpFrame tab dm ra sa bS.size base rsp0 s5 :=
        hf4.ret (by omega) (by omega) (by rsimp; exact hA0) (fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 => by
            cases r <;> first | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd rfl h3 | exact absurd rfl h4 |
              exact absurd rfl h5 | exact absurd rfl h6 | exact absurd rfl h7 | exact absurd rfl h8 | exact absurd rfl h9 | rfl)
          hRR hsv5 fun y hy => hfr.grows _ (isSome_get?_storeInt hy)
      have hseq : seqMem m6 mode plo phi out hdrf ctlf hw (UInt64.ofBitVec (0 : Word).toBitVec)
          (BinOp.sub.eval s4.regs.rax 9223372036854775808) =
          seqMem m6 mode plo phi out hdrf ctlf hw 0 (rs6.getD 0 0 - 9223372036854775808) := by
        rw [hrax6]; rfl
      refine ev_congr (j := Kc + 109) ?_ (by omega)
      rw [← Code.label (i := 109) hC rfl]
      rw [hrax6] at hout7
      have hsub : BinOp.sub.eval (rs6.getD 0 0) 9223372036854775808 = rs6.getD 0 0 - 9223372036854775808 := rfl
      rw [hsub] at hout7
      refine hexit s5 hf5 (fun h0' hacc => ?_) (fun h2 => ?_)
      · have hout' := hout7.resolve_left (by rw [h0']; decide)
        rcases hres7 : L.run p abiFuel "check" [] (seqMem m6 mode plo phi out hdrf ctlf hw 0
            (rs6.getD 0 0 - 9223372036854775808)) with e | ⟨rs7, m7⟩
        · rw [hres7] at hout'
          cases e <;> simp only [OutcomeRel] at hout' <;> (rw [h0'] at hout'; exact absurd hout'.1 (by decide))
        rw [hres7] at hout'
        obtain ⟨-, hRes, -⟩ := hout'
        have hrax : s5.regs.rax = rs7.getD 0 0 := hRes.1 0 (by simp only [seqLayout_tab]; omega) (by decide)
        exact ⟨hbC, hpb, rs4, m4, hres4, .inr ⟨hge4', hbS, rs5, m5, hres5, .inr ⟨hge5', rm, h0, hjobs,
          rs6, m6, hres6, .inr ⟨hge6', rs7, m7, hres7, by rw [← hrax]; exact hacc⟩⟩⟩⟩
      · obtain ⟨e, he, hk⟩ := err_of_entryOut hout7 h2
        exact ⟨hbC, hpb, .inr ⟨rs4, m4, hres4, hge4', hbS, .inr ⟨rs5, m5, hres5, hge5', rm, h0,
          .inr ⟨hjobs, .inr ⟨rs6, m6, hres6, hge6', e, he, hk.symm⟩⟩⟩⟩⟩

    · exact ((hf2.regs (s' := { s2 with regs := _, status := st7 }) rfl fun r h1 h2 h3 _ _ _ _ _ => by
          cases r <;> first | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd rfl h3 | rfl).wr (by omega)
          hside (by omega) (by omega)).wr (by omega) hside (by omega) (by omega)
    · dsimp only
      rw [show Int.toNat 48 = 48 from rfl, show Int.toNat 56 = 56 from rfl]
      rw [rdW_wrW_A (by omega) (by omega) (by omega), rdW_wrW_same, hrax5]
      congr 1
      simp only [BinOp.eval, UInt64.ofBitVec_toBitVec, UInt64.ofNat_toNat]
    · dsimp only
      rw [show Int.toNat 56 = 56 from rfl, rdW_wrW_same]; rfl
    · have hag0 : CmpAgree (cmpBuf out m5) (base + abiSlot * abiSlot64 tab out) (base + L.Compiler.cmpW tab)
          (base + cmpNeed tab own) (base + abiNeed tab) (base + abiNeed tab + 64) rsp0 s2.dmem s2.dmem :=
        ⟨fun y h => h, fun _ _ _ _ _ _ => rfl, hBwords⟩
      exact (hag0.wrW (by omega) (fun x h1 h2 => .inr ⟨by omega, by omega⟩) (by omega) (by omega)).wrW (by omega)
        (fun x h1 h2 => .inr ⟨by omega, by omega⟩) (by omega) (by omega)
    · refine regionRel_zero hok (Nat.le_refl _) (by simp only [L.Compiler.cmpW]; omega) _ fun x h1 h2 => ?_
      simp only [L.Compiler.cmpW] at h1 h2
      rw [get?_wrW_A (by omega) (by omega) (by omega), get?_wrW_A (by omega) (by omega) (by omega)]
      have hw : x < rsp0 - 24 ∨ rsp0 + 8 ≤ x := by rcases hside with h | h <;> omega
      rw [hsame2 x (by omega) (.inr (by omega)) (fun ⟨h3, h4⟩ => by rcases hS0 x h3 h4 with h | h <;> omega)
          (fun ⟨h3, h4⟩ => by rw [hpbE] at h4; rcases hpR x h3 h4 with h | h <;> omega) hw,
        hsame1 x (by omega) (.inr (by omega)) (fun ⟨h3, h4⟩ => by rcases hinR x h3 h4 with h | h <;> omega)
          (fun ⟨h3, h4⟩ => by rcases hpR x h3 h4 with h | h <;> omega) hw,
        honly.same x (by omega) (by omega)]
      exact hz x (by omega) (by omega)
  -- the prologue: the save area, the return address popped, `r15 := base`, `r9 := abiNeed`
  have hsa0 : (BinOp.add.eval (cmpSave tab).toUInt64 dm.regs.r8).toNat = base + abiNeed tab := by
    simp only [BinOp.eval, UInt64.toNat_add, cmpSave, hbase, Nat.toUInt64]
    rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
    omega
  have hsvR : ∀ x, base + abiNeed tab ≤ x → x < base + abiNeed tab + 48 → x < rsp0 - 24 ∨ rsp0 + 24 ≤ x := by
    intro x h1 h2
    rcases hside with h | h
    · omega
    · refine Classical.byContradiction fun hn => ?_
      simp only [not_or, Nat.not_lt, Nat.not_le] at hn
      by_cases hx : x < rsp0 + 8
      · rcases (hcs x (by omega) hx).2.1 with h' | h' <;> omega
      · have := hc.hsArgs x (by omega) (by omega); rw [hbase] at this; omega
  have hmap0 : ∀ x, base + abiNeed tab ≤ x → x < base + abiNeed tab + 48 → (dm.dmem.get? (A x)).isSome :=
    fun x h1 h2 => by rw [hz x (by omega) (by omega)]; rfl
  refine ev_movRI (hC.get (i := 25) rfl) ?_
  refine ev_binO (op := .add) (o := oR .r8) rfl (hC.get (i := 26) rfl)
    (Or.inr (Or.inr ⟨.r8, rfl, rfl⟩)) fun st0 => ?_
  refine ev_movMR (hC.get (i := 27) rfl) ⟨by decide, by decide⟩ ?_ ?_
  · rsimp; rw [hsa0]; exact isSome_rdW fun j hj => by rw [A_add]; exact hmap0 _ (by omega) (by omega)
  refine ev_pop (hC.get (i := 28) rfl) (v := ra) ?_ ?_
  · rsimp; rw [hsa0, toBitVec_eq_A dm.regs.rsp, hrsp0, show Int.toNat 0 = 0 from rfl, Nat.add_zero,
      rdW_wrW_A (by omega) (by omega) (by rcases hsvR (base + abiNeed tab) (by omega) (by omega) with h | h <;> omega)]
    rw [← hrsp0]; exact hc.hra
  refine ev_movMR (hC.get (i := 29) rfl) ⟨by decide, by decide⟩ ?_ ?_
  · rsimp; rw [hsa0]
    exact isSome_rdW fun j hj => by rw [A_add]; exact isSome_get?_storeInt (hmap0 _ (by omega) (by omega))
  have hr8 : (dm.regs.rsp.toBitVec + 8).toNat = rsp0 + 8 := by
    simp only [BitVec.toNat_add, UInt64.toNat_toBitVec, show (8 : BitVec 64).toNat = 8 from rfl, hrsp0]; omega
  have hr8' : ({ toBitVec := dm.regs.rsp.toBitVec + 8 } : UInt64).toNat = rsp0 + 8 := hr8
  refine ev_movRM (hC.get (i := 30) rfl) ⟨by decide, by decide⟩ (v := sa) ?_ ?_
  · rsimp; rw [hsa0, hr8]
    rw [show Int.toNat 0 = 0 from rfl, show Int.toNat 8 = 8 from rfl,
      rdW_wrW_A (by omega) (by omega) (by rcases hsvR (base + abiNeed tab + 8) (by omega) (by omega) with h | h <;> omega),
      rdW_wrW_A (by omega) (by omega) (by rcases hsvR (base + abiNeed tab) (by omega) (by omega) with h | h <;> omega)]
    have := hc.hsa; rw [hrsp0] at this; exact this
  refine ev_movMR (hC.get (i := 31) rfl) ⟨by decide, by decide⟩ ?_ ?_
  · rsimp; rw [hsa0]
    exact isSome_rdW fun j hj => by rw [A_add]; exact isSome_get?_storeInt (isSome_get?_storeInt (hmap0 _ (by omega) (by omega)))
  refine ev_movRM (hC.get (i := 32) rfl) ⟨by decide, by decide⟩ (v := UInt64.ofNat bS.size) ?_ ?_
  · rsimp; rw [hsa0, hr8]
    rw [show Int.toNat 0 = 0 from rfl, show Int.toNat 8 = 8 from rfl, show Int.toNat 16 = 16 from rfl,
      rdW_wrW_A (by omega) (by omega) (by rcases hsvR (base + abiNeed tab + 16) (by omega) (by omega) with h | h <;> omega),
      rdW_wrW_A (by omega) (by omega) (by rcases hsvR (base + abiNeed tab + 8) (by omega) (by omega) with h | h <;> omega),
      rdW_wrW_A (by omega) (by omega) (by rcases hsvR (base + abiNeed tab) (by omega) (by omega) with h | h <;> omega)]
    have := hc.hsn; rw [hrsp0] at this; exact this
  refine ev_movMR (hC.get (i := 33) rfl) ⟨by decide, by decide⟩ ?_ ?_
  · rsimp; rw [hsa0]
    exact isSome_rdW fun j hj => by
      rw [A_add]; exact isSome_get?_storeInt (isSome_get?_storeInt (isSome_get?_storeInt (hmap0 _ (by omega) (by omega))))
  refine ev_movMR (hC.get (i := 34) rfl) ⟨by decide, by decide⟩ ?_ ?_
  · rsimp; rw [hsa0]
    exact isSome_rdW fun j hj => by
      rw [A_add]; exact isSome_get?_storeInt (isSome_get?_storeInt (isSome_get?_storeInt (isSome_get?_storeInt
        (hmap0 _ (by omega) (by omega)))))
  refine ev_movMR (hC.get (i := 35) rfl) ⟨by decide, by decide⟩ ?_ ?_
  · rsimp; rw [hsa0]
    exact isSome_rdW fun j hj => by
      rw [A_add]; exact isSome_get?_storeInt (isSome_get?_storeInt (isSome_get?_storeInt (isSome_get?_storeInt
        (isSome_get?_storeInt (hmap0 _ (by omega) (by omega))))))
  refine ev_movRR (hC.get (i := 36) rfl) ?_
  refine ev_movRI (hC.get (i := 37) rfl) ?_
  rsimp
  rw [hsa0]
  simp only [show Int.toNat 0 = 0 from rfl, show Int.toNat 8 = 8 from rfl, show Int.toNat 16 = 16 from rfl,
    show Int.toNat 24 = 24 from rfl, show Int.toNat 32 = 32 from rfl, show Int.toNat 40 = 40 from rfl, Nat.add_zero]
  have hW : ∀ o (v : BitVec 64) (d : DataMem), o + 8 ≤ 48 → ∀ o', o' + 8 ≤ 48 → (o' + 8 ≤ o ∨ o + 8 ≤ o') →
      rdW (wrW d (A (base + abiNeed tab + o)) v) (A (base + abiNeed tab + o')) = rdW d (A (base + abiNeed tab + o')) :=
    fun o v d ho o' ho' h => rdW_wrW_A (by omega) (by omega) (by omega)
  refine key4 _ ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun x h1 h2 => ?_, fun x h1 h2 => ?_⟩
    rfl rfl rfl rfl rfl ?_ ?_
  · rsimp; exact hbase
  · exact hr8'
  · dsimp only
    rw [show base + abiNeed tab = base + abiNeed tab + 0 from rfl, hW 40 _ _ (by omega) 0 (by omega) (by omega),
      hW 32 _ _ (by omega) 0 (by omega) (by omega), hW 24 _ _ (by omega) 0 (by omega) (by omega),
      hW 16 _ _ (by omega) 0 (by omega) (by omega), hW 8 _ _ (by omega) 0 (by omega) (by omega)]
    rw [Nat.add_zero, rdW_wrW_same]
  · dsimp only
    rw [hW 40 _ _ (by omega) 8 (by omega) (by omega), hW 32 _ _ (by omega) 8 (by omega) (by omega),
      hW 24 _ _ (by omega) 8 (by omega) (by omega), hW 16 _ _ (by omega) 8 (by omega) (by omega), rdW_wrW_same]
  · dsimp only
    rw [hW 40 _ _ (by omega) 16 (by omega) (by omega), hW 32 _ _ (by omega) 16 (by omega) (by omega),
      hW 24 _ _ (by omega) 16 (by omega) (by omega), rdW_wrW_same]
  · dsimp only
    rw [hW 40 _ _ (by omega) 24 (by omega) (by omega), hW 32 _ _ (by omega) 24 (by omega) (by omega), rdW_wrW_same]
  · dsimp only
    rw [hW 40 _ _ (by omega) 32 (by omega) (by omega), rdW_wrW_same]
  · dsimp only
    rw [rdW_wrW_same]
  · dsimp only
    rcases (hcs x h1 h2).2.1 with h | h <;>
    exact isSome_get?_storeInt (isSome_get?_storeInt (isSome_get?_storeInt (isSome_get?_storeInt
        (isSome_get?_storeInt (isSome_get?_storeInt (hcs x h1 h2).1)))))
  · dsimp only
    exact isSome_get?_storeInt (isSome_get?_storeInt (isSome_get?_storeInt (isSome_get?_storeInt
        (isSome_get?_storeInt (isSome_get?_storeInt (by rw [hz x h1 h2]; rfl))))))
  · rsimp; exact UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
  · dsimp only
    refine ⟨fun y hy => isSome_get?_storeInt (isSome_get?_storeInt (isSome_get?_storeInt (isSome_get?_storeInt
      (isSome_get?_storeInt (isSome_get?_storeInt hy))))), fun x hx h => ?_⟩
    rw [get?_wrW_A (by omega) hx (by omega), get?_wrW_A (by omega) hx (by omega), get?_wrW_A (by omega) hx (by omega),
      get?_wrW_A (by omega) hx (by omega), get?_wrW_A (by omega) hx (by omega), get?_wrW_A (by omega) hx (by omega)]

/-- **The compared run's driver on the machine** (without the registers). -/
theorem cmp_outcome (q p : Prog) (hq : Refines q p) (tab : Tab) (hok : abiTabOk tab = true)
    {X : AsmTab} (hAX : AsmOkT q tab X) (hio : abiIO tab = true) (hwf : Prog.wf tab q = true)
    (hnres : 1 ≤ tab.nres) (mode plo phi : GVar) (out hdrf ctlf : ArrId) (hw : Nat) (fz own : List TieredArray)
    (hngm : mode.id < tab.ng) (hngl : plo.id < tab.ng) (hngh : phi.id < tab.ng)
    (h12 : plo ≠ phi) (h13 : plo ≠ mode) (h23 : phi ≠ mode) (hfzl : fz.length < 2 ^ 20)
    (hp : seqParamsOk tab out hdrf ctlf hw = true) (hmo : bufMinOk tab fz own = true)
    (hdisj : ∀ a ∈ own, a ∉ fz) (hcn : cmpNeed tab own < 2 ^ 64) (k0 : Nat)
    (hcode : Code (parStub tab mode plo phi out hdrf ctlf hw fz own ++
      (abiStub tab ++ (compileProgX X tab q "check" ++ cmpStub tab mode out own))) k0)
    (fd : FunDecl) (hentry : p.lookup "check" = some fd) (hnp : fd.nparams = 0)
    (bC bS pb : ByteArray) (sa : Word) (dm : MachineData) (ra : Word) (hc : CmpCall bC bS pb sa dm ra)
    (hG : CmpGuard tab p mode plo phi out fz own bC bS pb) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧
        (st.data.regs.rdx = 0 → st.data.regs.rax = ACCEPT → CmpAccepts tab p mode plo phi out hdrf ctlf hw fz own bC bS pb) ∧
        (st.data.regs.rdx = 2 → CmpErr tab p mode plo phi out hdrf ctlf hw fz own bC bS pb st.data.regs.rax))
      dm (label abiCompareL) :=
  eventually_weaken _ _ _ _ (fun _ ⟨hpc, _, h1, h2⟩ => ⟨hpc, h1, h2⟩)
    (cmp_outcome_regs q p hq tab hok hAX hio hwf hnres mode plo phi out hdrf ctlf hw fz own hngm hngl hngh h12 h13
      h23 hfzl hp hmo hdisj hcn k0 hcode fd hentry hnp bC bS pb sa dm ra hc hG)

end



/-- info: 'ConAgua.Final.cmp_outcome_regs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cmp_outcome_regs

/-- info: 'ConAgua.Final.cmp_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cmp_outcome


end ConAgua.Final
