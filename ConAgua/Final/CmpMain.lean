module

import ConAgua.Final.DrvAbi
import ConAgua.Final.SeqAbi
import Kraken.X64.Registers
public import ConAgua.Final.CmpOutcome
public import ConAgua.Final.CmpAbi

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
variable [Host] {tab : Tab} {mode : GVar} {out : ArrId}

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
    {Kc : Nat} (hC : Code (cmpStubL tab mode) Kc) (i e : Nat) (w : Word) (lab : Label)
    (hblk : ∀ t (_ : t < 9), (cmpStubL tab mode)[i + t]? = (cmpArgsS tab ++ [callL lab])[t]?)
    (hen : ∀ t (_ : t < 7), (cmpStubL tab mode)[e + t]? =
      [.label lab, movRI .rax (abiNeed tab).toUInt64, i64 (.cmp (.reg (rr .r9)) (oR .rax)), jccL .c abiSetupL,
       movRI .rax w, movMR (mb .r8 (tab.globOff mode)) .rax, jmpL abiSetupL][t]?)
    (dm : MachineData) (ra sa : Word) {nS base rsp0 : Nat} (bs pb : ByteArray) (hnS : nS = bs.size)
    (hgeo : CmpGeo tab base dm.regs.r9.toNat rsp0)
    (hside : rsp0 + 8 ≤ base ∨ base + dm.regs.r9.toNat ≤ rsp0 - 24)
    (hnP : dm.regs.rcx.toNat = pb.size)
    (hSend : sa.toNat + bs.size < 2 ^ 64) (hPend : dm.regs.rdx.toNat + pb.size < 2 ^ 64)
    (hSg : ∀ x, sa.toNat ≤ x → x < sa.toNat + bs.size → (x < base ∨ base + dm.regs.r9.toNat ≤ x) ∧
      (x < rsp0 - 24 ∨ rsp0 + 8 ≤ x) ∧ ¬ (dm.regs.rdx.toNat ≤ x ∧ x < dm.regs.rdx.toNat + pb.size))
    (hPg : ∀ x, dm.regs.rdx.toNat ≤ x → x < dm.regs.rdx.toNat + pb.size → (x < base ∨ base + dm.regs.r9.toNat ≤ x) ∧
      (x < rsp0 - 24 ∨ rsp0 + 8 ≤ x))
    (Acc : Prop) (Err : Word → Prop) (Hi : Word → DataMem → Prop) (s : MachineData) (hf : CmpFrame tab dm ra sa nS base rsp0 s)
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
      Ev (CmpPostH dm ra Acc Err Hi) s' (at_ (Kc + i + 9))) :
    Ev (CmpPostH dm ra Acc Err Hi) s (at_ (Kc + i)) := by
  obtain ⟨hnb, htab, hneed64⟩ := abiTabOk_spec hok
  have hfits := hgeo.fits
  have hneed := hgeo.need
  have hr24 := hgeo.r24
  have hr8 := hgeo.r8
  have hwin := hgeo.win
  have hn := abiNeed_ge hok
  simp only [drvNeed] at hneed
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

/-- **The compared run's front on the machine** (`ca_cmp_front`, shared by `ca_start_c` and
`ca_start_ac`, the flag in `r10`): the region's size test, the save area, modes `4` and `5`. Unless
the front stops (an accept, `CmpFrontAcc45`; an error, `CmpFrontErr45`; a decline), the run goes on
at directive `76` with the frame, the region holding mode `5`'s final memory in the stub's layout
for the solution's bytes, `kS` in save word `6`, the flag in save word `7` and `rax` the save area. -/
theorem cmp_front (q p : Prog) (hq : Refines q p) (tab : Tab) (hok : abiTabOk tab = true)
    {X : AsmTab} (hAX : AsmOkT q tab X) (hio : abiIO tab = true) (hwf : Prog.wf tab q = true)
    (hnres : 1 ≤ tab.nres) (mode : GVar) (hngm : mode.id < tab.ng) (hdn : drvNeed tab < 2 ^ 64) (k0 : Nat)
    (hcodeO : Code (abiStub tab ++ compileProgX X tab q "check") k0) {Kc : Nat} (hC : Code (cmpStubL tab mode) Kc)
    (fd : FunDecl) (hentry : p.lookup "check" = some fd) (hnp : fd.nparams = 0)
    (bC bS pb : ByteArray) (sa : Word) (dm : MachineData) (ra : Word) (hc : CmpCall bC bS pb sa dm ra)
    (Acc : Prop) (Err : Word → Prop) (Hi : Word → DataMem → Prop)
    (hA45 : CmpFrontAcc45 tab p mode bC bS pb → Acc) (hE45 : ∀ k, CmpFrontErr45 tab p mode bC bS pb k → Err k)
    (hk : ∀ (rs5 : List Word) (m5 : Mem) (s : MachineData), CmpFront45 tab p mode bC bS pb rs5 m5 →
      CmpFrame tab dm ra sa bS.size dm.regs.r8.toNat dm.regs.rsp.toNat s →
      MemRel (abiLayout tab dm.regs.r8.toNat sa.toNat bS.size dm.regs.rdx.toNat pb.size) m5 s.dmem →
      drvNeed tab ≤ dm.regs.r9.toNat →
      rdW s.dmem (A (dm.regs.r8.toNat + abiNeed tab + 48)) = some (rs5.getD 0 0 - 9223372036854775808) →
      rdW s.dmem (A (dm.regs.r8.toNat + abiNeed tab + 56)) = some dm.regs.r10 →
      s.regs.rax.toNat = dm.regs.r8.toNat + abiNeed tab →
      Ev (CmpPostH dm ra Acc Err Hi) s (at_ (Kc + 76))) :
    Ev (CmpPostH dm ra Acc Err Hi) dm (label abiCmpFrontL) := by
  obtain ⟨hnb, htab, hneed64⟩ := abiTabOk_spec hok
  obtain ⟨base, hbase⟩ : ∃ base, dm.regs.r8.toNat = base := ⟨_, rfl⟩
  obtain ⟨rsp0, hrsp0⟩ : ∃ rsp0, dm.regs.rsp.toNat = rsp0 := ⟨_, rfl⟩
  have hfits := hc.hfits
  have hcs8 := hc.hcs8
  have hcs24 := hc.hcs24
  have hsEnd := hc.hsEnd
  have hn := abiNeed_ge hok
  have hab : abiSlot = 2 ^ 35 := rfl
  rw [Code.label (i := 33) hC rfl]
  refine ev_label (hC.get (i := 33) rfl) ?_
  refine ev_movRI (hC.get (i := 34) rfl) ?_
  refine ev_cmpRO (r := .r9) (o := oR .rax) (v := (drvNeed tab).toUInt64) (hC.get (i := 35) rfl)
    (Or.inr (Or.inr ⟨.rax, rfl, rfl⟩)) ?_
  refine ev_jcc (hC.get (i := 36) rfl) (fun hlt => ?_) (fun hge => ?_)
  · -- declined
    rw [Code.label (i := 152) hC rfl]
    refine ev_label (hC.get (i := 152) rfl) ?_
    refine ev_movRI (hC.get (i := 153) rfl) ?_
    refine ev_movRI (hC.get (i := 154) rfl) ?_
    refine ev_ret (hC.get (i := 155) rfl) (ra := ra)
      (by rsimp; rw [toBitVec_eq_A]; exact hc.hra) ?_
    refine Eventually.done _ ⟨⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun h => ?_, fun h => ?_⟩, fun h => ?_⟩ <;>
      dsimp only at * <;> (try rsimp at *)
    · simp only [UInt64.toNat_ofBitVec, BitVec.toNat_add, UInt64.toNat_toBitVec, show (8 : BitVec 64).toNat = 8 from rfl]
      omega
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  rsimp at hge
  rw [interp_c] at hge
  have hge' : drvNeed tab ≤ dm.regs.r9.toNat := by
    simp only [decide_eq_false_iff_not, UInt64.lt_iff_toNat_lt, Nat.not_lt] at hge
    rw [show ((drvNeed tab).toUInt64).toNat = drvNeed tab from UInt64.toNat_ofNat_of_lt' hdn] at hge
    exact hge
  have hneedC := hge'
  simp only [drvNeed] at hneedC
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
      Only (base + abiNeed tab) (base + abiNeed tab + 64) dm.dmem s0.dmem →
      rdW s0.dmem (A (base + abiNeed tab + 56)) = some dm.regs.r10 →
      Ev (CmpPostH dm ra Acc Err Hi) s0 (at_ (Kc + 51)) := by
    intro s0 hf0 hdi hsi hdx hcx h8 h9 honly hfl0
    have e1 : s0.regs.rsp.toBitVec - 8 = A rsp0 := by
      rw [toBitVec_eq_A, hf0.rsp, A_sub8 _ (by omega) (by omega)]; rfl
    have hA0 : ({ toBitVec := A rsp0 } : UInt64).toNat = rsp0 := by
      show (A rsp0).toNat = rsp0; simp only [A, BitVec.toNat_ofNat]; omega
    refine ev_call (hC.get (i := 51) rfl) ?_ ?_
    · rw [e1]; exact isSome_rdW fun j hj => by rw [A_add]; exact hf0.win _ (by omega) (by omega)
    rw [e1]
    refine ev_seq (abiMode_outcome q p hq tab hok hAX hio hwf mode hngm 4 abiStartA4L Kc _
      (Code.label (i := 0) hC rfl) (hC.get (i := 0) rfl) (hC.get (i := 1) rfl) (hC.get (i := 2) rfl)
      (hC.get (i := 3) rfl) (hC.get (i := 4) rfl) (hC.get (i := 5) rfl) (hC.get (i := 6) rfl)
      hcodeO fd hentry hnp bC pb _ (UInt64.ofBitVec (at_ (Kc + 51 + 1)).toBitVec) ?_) ?_
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
    have hfl1 : rdW s1.dmem (A (base + abiNeed tab + 56)) = some dm.regs.r10 := by
      rw [← hfl0]; exact rdW_congr fun j hj => by rw [A_add]; exact hsv1 _ (by omega) (by omega)
    have hexit := fun (s' : MachineData) (hf' : CmpFrame tab dm ra sa bS.size base rsp0 s') hacc herr
        (hbad : s'.regs.rdx ≠ 0 ∨ s'.regs.rax.toNat < 2 ^ 63) =>
      cmp_exit hC dm ra sa (by omega) ⟨hcs24, hcs8⟩ hrsp0 Acc Err Hi s' hf' hacc herr
        (fun h0 h1 => by
          rcases hbad with h | h
          · exact absurd h0 h
          · omega)
    refine cmp_okGe (i := 52) hC rfl rfl rfl rfl rfl s1 (fun s' hm hr hbad => ?_) (fun hrdx hge4 st4 => ?_)
    · have erax : s'.regs.rax = s1.regs.rax := by
        have := hr .rax (by decide); simpa using congrArg UInt64.ofBitVec this
      have erdx : s'.regs.rdx = s1.regs.rdx := by
        have := hr .rdx (by decide); simpa using congrArg UInt64.ofBitVec this
      refine hexit s' (hf1.regs hm fun r _ h2 _ _ _ _ _ _ => hr r h2) (fun h0 hacc => ?_) (fun h2 => ?_)
        (by rw [erdx, erax]; exact hbad)
      · rw [erdx] at h0; rw [erax] at hacc
        have hout' := hout.resolve_left (by rw [h0]; decide)
        obtain ⟨hb, hpb⟩ := hsz.resolve_left (by rw [h0]; decide)
        rcases hres : L.run p abiFuel "check" [] ((loadMem bC pb (abiSz tab)).setG mode 4) with e | ⟨rs4, m4⟩
        · rw [hres] at hout'
          cases e <;> simp only [OutcomeRel] at hout' <;> (rw [h0] at hout'; exact absurd hout'.1 (by decide))
        rw [hres] at hout'
        obtain ⟨-, hRes, -⟩ := hout'
        have hrax : s1.regs.rax = rs4.getD 0 0 := hRes.1 0 (by simp only [abiLayout_tab]; omega) (by decide)
        exact hA45 ⟨hb, hpb, rs4, m4, hres, .inl (by rw [← hrax]; exact hacc)⟩
      · rw [erdx] at h2; rw [erax]
        obtain ⟨hb, hpb⟩ := hsz.resolve_left (by rw [h2]; decide)
        obtain ⟨e, he, hk⟩ := err_of_entryOut hout h2
        exact hE45 _ ⟨hb, hpb, .inl ⟨e, he, hk.symm⟩⟩
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
    have hgeoM : CmpGeo tab base dm.regs.r9.toNat rsp0 := ⟨hfits, hge', hcsW, hcs24, hcs8⟩
    refine cmp_modeM q p hq hok hAX hio hwf hngm _ hcodeO fd hentry hnp hC 57 7 5 abiStartA5L
      (fun t ht => match t, ht with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl | 7, _ => rfl | 8, _ => rfl | _ + 9, h => absurd h (by omega))
      (fun t ht => match t, ht with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl | _ + 7, h => absurd h (by omega))
      dm ra sa bS ⟨m4.arr8 Rom.PB⟩ rfl hgeoM hside hcx hc.hSEnd (by rw [hpbE]; exact hc.hpinsEnd)
      (fun x h1 h2 => ?_) (fun x h1 h2 => ?_) _ _ _ _
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
    refine ev_congr (cmp_okGe (i := 66) hC rfl rfl rfl rfl rfl s2 (fun s' hm hr hbad => ?_) (fun hrdx5 hge5 st5 => ?_)) (by omega)
    · have erax : s'.regs.rax = s2.regs.rax := by
        have := hr .rax (by decide); simpa using congrArg UInt64.ofBitVec this
      have erdx : s'.regs.rdx = s2.regs.rdx := by
        have := hr .rdx (by decide); simpa using congrArg UInt64.ofBitVec this
      refine hexit s' (hf2.regs hm fun r _ h2 _ _ _ _ _ _ => hr r h2) (fun h0 hacc => ?_) (fun h2 => ?_)
        (by rw [erdx, erax]; exact hbad)
      · rw [erdx] at h0; rw [erax] at hacc
        have hout' := hout5.resolve_left (by rw [h0]; decide)
        obtain ⟨hbS, -⟩ := hsz5.resolve_left (by rw [h0]; decide)
        rcases hres : cmpRun p ((cmpIn m4 bS).setG mode 5) with e | ⟨rs5, m5⟩
        · rw [hres] at hout'
          cases e <;> simp only [OutcomeRel] at hout' <;> (rw [h0] at hout'; exact absurd hout'.1 (by decide))
        rw [hres] at hout'
        obtain ⟨-, hRes, -⟩ := hout'
        have hrax : s2.regs.rax = rs5.getD 0 0 := hRes.1 0 (by simp only [abiLayout_tab]; omega) (by decide)
        exact hA45 ⟨hbC, hpb, rs4, m4, hres4, .inr ⟨hge4', hbS, rs5, m5, hres, by rw [← hrax]; exact hacc⟩⟩
      · rw [erdx] at h2; rw [erax]
        obtain ⟨hbS, -⟩ := hsz5.resolve_left (by rw [h2]; decide)
        obtain ⟨e, he, hk⟩ := err_of_entryOut hout5 h2
        exact hE45 _ ⟨hbC, hpb, .inr ⟨rs4, m4, hres4, hge4', hbS, e, he, hk.symm⟩⟩
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
    have hsa2 : (BinOp.add.eval (cmpSave tab).toUInt64 s2.regs.r15).toNat = base + abiNeed tab := by
      simp only [BinOp.eval, UInt64.toNat_add, cmpSave, hf2.r15, Nat.toUInt64]
      rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
      omega
    refine ev_binO (op := .sub) (o := oR .rcx) (v := 9223372036854775808) rfl (hC.get (i := 71) rfl)
      (Or.inr (Or.inr ⟨.rcx, rfl, rfl⟩)) fun st6 => ?_
    refine ev_movRR (hC.get (i := 72) rfl) ?_
    refine ev_movRI (hC.get (i := 73) rfl) ?_
    refine ev_binO (op := .add) (o := oR .r15) rfl (hC.get (i := 74) rfl)
      (Or.inr (Or.inr ⟨.r15, rfl, rfl⟩)) fun st7 => ?_
    refine ev_movMR (hC.get (i := 75) rfl) ⟨by decide, by decide⟩ ?_ ?_
    · rsimp; rw [hsa2]; exact isSome_rdW fun j hj => by rw [A_add]; exact hf2.map _ (by omega) (by omega)
    rsimp
    rw [hsa2]
    have hS0 : ∀ x, sa.toNat ≤ x → x < sa.toNat + bS.size → x < base ∨ base + dm.regs.r9.toNat ≤ x :=
      fun x h1 h2 => by have := (hc.hSDisj x h1 h2).1; rwa [hbase] at this
    -- the flag word survived mode `5`'s call
    have hfl2 : rdW s2.dmem (A (base + abiNeed tab + 56)) = some dm.regs.r10 := by
      rw [← hfl1]
      refine rdW_congr fun j hj => ?_
      rw [A_add]
      exact hsame2 _ (by omega) (.inr (by omega))
        (fun ⟨h3, h4⟩ => by rcases hS0 _ h3 h4 with h | h <;> omega)
        (fun ⟨h3, h4⟩ => by rw [hpbE] at h4; rcases hpR _ h3 h4 with h | h <;> omega)
        (by rcases hside with h | h <;> omega)
    refine hk rs5 m5 _ ⟨hbC, hpb, hbS, rs4, m4, hres4, hge4', hres5, hge5'⟩ ?_ ?_ hge' ?_ ?_ ?_
    · rw [hbase, hrsp0]
      exact (hf2.regs (s' := { s2 with regs := _, status := st7 }) rfl fun r h1 h2 h3 _ _ _ _ _ => by
          cases r <;> first | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd rfl h3 | rfl).wr (by omega)
          hside (by omega) (by omega)
    · rw [hbase]
      dsimp only
      rw [hpbE] at hMem5
      refine hMem5.only' (abiLayout_ok hok ⟨Nat.le_refl _, by omega, hc.hSEnd, hc.hpinsEnd,
          fun x h1 h2 => by rcases hS0 x h1 h2 with h | h <;> omega,
          fun x h1 h2 => by rcases hpR x h1 h2 with h | h <;> omega,
          fun x h1 h2 => (hc.hSDisj x h1 h2).2.2.1⟩) (Only.wrW (by omega)) fun x h1 h2 => ?_
      obtain ⟨-, q2, q3⟩ := abiLayout_out hok (blen := abiNeed tab) (base := base) (inp := sa.toNat)
        (n := bS.size) (pins := dm.regs.rdx.toNat) (np := pb.size) (x := x) (Nat.le_refl _) (.inr (by omega))
        (fun ⟨h3, h4⟩ => by rcases hS0 x h3 h4 with h | h <;> omega)
        (fun ⟨h3, h4⟩ => by rcases hpR x h3 h4 with h | h <;> omega)
      exact ⟨q3, q2⟩
    · rw [hbase]; dsimp only
      rw [show Int.toNat 48 = 48 from rfl, rdW_wrW_same, hrax5]
      congr 1
    · rw [hbase]; dsimp only
      rw [show Int.toNat 48 = 48 from rfl, rdW_wrW_A (by omega) (by omega) (by omega)]; exact hfl2
    · rw [hbase]; exact hsa2
  -- the prologue: the save area, the return address popped, `r15 := base`, `r9 := abiNeed`
  have hsa0 : (BinOp.add.eval (cmpSave tab).toUInt64 dm.regs.r8).toNat = base + abiNeed tab := by
    simp only [BinOp.eval, UInt64.toNat_add, cmpSave, hbase, Nat.toUInt64]
    rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
    omega
  have hsvR : ∀ x, base + abiNeed tab ≤ x → x < base + abiNeed tab + 64 → x < rsp0 - 24 ∨ rsp0 + 24 ≤ x := by
    intro x h1 h2
    rcases hside with h | h
    · omega
    · refine Classical.byContradiction fun hn => ?_
      simp only [not_or, Nat.not_lt, Nat.not_le] at hn
      by_cases hx : x < rsp0 + 8
      · rcases (hcs x (by omega) hx).2.1 with h' | h' <;> omega
      · have := hc.hsArgs x (by omega) (by omega); rw [hbase] at this; omega
  have hmap0 : ∀ x, base + abiNeed tab ≤ x → x < base + abiNeed tab + 64 → (dm.dmem.get? (A x)).isSome :=
    fun x h1 h2 => by rw [hz x (by omega) (by omega)]; rfl
  refine ev_movRI (hC.get (i := 37) rfl) ?_
  refine ev_binO (op := .add) (o := oR .r8) rfl (hC.get (i := 38) rfl)
    (Or.inr (Or.inr ⟨.r8, rfl, rfl⟩)) fun st0 => ?_
  refine ev_movMR (hC.get (i := 39) rfl) ⟨by decide, by decide⟩ ?_ ?_
  · rsimp; rw [hsa0]; exact isSome_rdW fun j hj => by rw [A_add]; exact hmap0 _ (by omega) (by omega)
  refine ev_pop (hC.get (i := 40) rfl) (v := ra) ?_ ?_
  · rsimp; rw [hsa0, toBitVec_eq_A dm.regs.rsp, hrsp0, show Int.toNat 0 = 0 from rfl, Nat.add_zero,
      rdW_wrW_A (by omega) (by omega) (by rcases hsvR (base + abiNeed tab) (by omega) (by omega) with h | h <;> omega)]
    rw [← hrsp0]; exact hc.hra
  refine ev_movMR (hC.get (i := 41) rfl) ⟨by decide, by decide⟩ ?_ ?_
  · rsimp; rw [hsa0]
    exact isSome_rdW fun j hj => by rw [A_add]; exact isSome_get?_storeInt (hmap0 _ (by omega) (by omega))
  have hr8 : (dm.regs.rsp.toBitVec + 8).toNat = rsp0 + 8 := by
    simp only [BitVec.toNat_add, UInt64.toNat_toBitVec, show (8 : BitVec 64).toNat = 8 from rfl, hrsp0]; omega
  have hr8' : ({ toBitVec := dm.regs.rsp.toBitVec + 8 } : UInt64).toNat = rsp0 + 8 := hr8
  refine ev_movRM (hC.get (i := 42) rfl) ⟨by decide, by decide⟩ (v := sa) ?_ ?_
  · rsimp; rw [hsa0, hr8]
    rw [show Int.toNat 0 = 0 from rfl, show Int.toNat 8 = 8 from rfl,
      rdW_wrW_A (by omega) (by omega) (by rcases hsvR (base + abiNeed tab + 8) (by omega) (by omega) with h | h <;> omega),
      rdW_wrW_A (by omega) (by omega) (by rcases hsvR (base + abiNeed tab) (by omega) (by omega) with h | h <;> omega)]
    have := hc.hsa; rw [hrsp0] at this; exact this
  refine ev_movMR (hC.get (i := 43) rfl) ⟨by decide, by decide⟩ ?_ ?_
  · rsimp; rw [hsa0]
    exact isSome_rdW fun j hj => by rw [A_add]; exact isSome_get?_storeInt (isSome_get?_storeInt (hmap0 _ (by omega) (by omega)))
  refine ev_movRM (hC.get (i := 44) rfl) ⟨by decide, by decide⟩ (v := UInt64.ofNat bS.size) ?_ ?_
  · rsimp; rw [hsa0, hr8]
    rw [show Int.toNat 0 = 0 from rfl, show Int.toNat 8 = 8 from rfl, show Int.toNat 16 = 16 from rfl,
      rdW_wrW_A (by omega) (by omega) (by rcases hsvR (base + abiNeed tab + 16) (by omega) (by omega) with h | h <;> omega),
      rdW_wrW_A (by omega) (by omega) (by rcases hsvR (base + abiNeed tab + 8) (by omega) (by omega) with h | h <;> omega),
      rdW_wrW_A (by omega) (by omega) (by rcases hsvR (base + abiNeed tab) (by omega) (by omega) with h | h <;> omega)]
    have := hc.hsn; rw [hrsp0] at this; exact this
  refine ev_movMR (hC.get (i := 45) rfl) ⟨by decide, by decide⟩ ?_ ?_
  · rsimp; rw [hsa0]
    exact isSome_rdW fun j hj => by
      rw [A_add]; exact isSome_get?_storeInt (isSome_get?_storeInt (isSome_get?_storeInt (hmap0 _ (by omega) (by omega))))
  refine ev_movMR (hC.get (i := 46) rfl) ⟨by decide, by decide⟩ ?_ ?_
  · rsimp; rw [hsa0]
    exact isSome_rdW fun j hj => by
      rw [A_add]; exact isSome_get?_storeInt (isSome_get?_storeInt (isSome_get?_storeInt (isSome_get?_storeInt
        (hmap0 _ (by omega) (by omega)))))
  refine ev_movMR (hC.get (i := 47) rfl) ⟨by decide, by decide⟩ ?_ ?_
  · rsimp; rw [hsa0]
    exact isSome_rdW fun j hj => by
      rw [A_add]; exact isSome_get?_storeInt (isSome_get?_storeInt (isSome_get?_storeInt (isSome_get?_storeInt
        (isSome_get?_storeInt (hmap0 _ (by omega) (by omega))))))
  refine ev_movMR (hC.get (i := 48) rfl) ⟨by decide, by decide⟩ ?_ ?_
  · rsimp; rw [hsa0]
    exact isSome_rdW fun j hj => by
      rw [A_add]; exact isSome_get?_storeInt (isSome_get?_storeInt (isSome_get?_storeInt (isSome_get?_storeInt
        (isSome_get?_storeInt (isSome_get?_storeInt (hmap0 _ (by omega) (by omega)))))))
  refine ev_movRR (hC.get (i := 49) rfl) ?_
  refine ev_movRI (hC.get (i := 50) rfl) ?_
  rsimp
  rw [hsa0]
  simp only [show Int.toNat 0 = 0 from rfl, show Int.toNat 8 = 8 from rfl, show Int.toNat 16 = 16 from rfl,
    show Int.toNat 24 = 24 from rfl, show Int.toNat 32 = 32 from rfl, show Int.toNat 40 = 40 from rfl, show Int.toNat 56 = 56 from rfl,
    Nat.add_zero]
  have hW : ∀ o (v : BitVec 64) (d : DataMem), o + 8 ≤ 64 → ∀ o', o' + 8 ≤ 64 → (o' + 8 ≤ o ∨ o + 8 ≤ o') →
      rdW (wrW d (A (base + abiNeed tab + o)) v) (A (base + abiNeed tab + o')) = rdW d (A (base + abiNeed tab + o')) :=
    fun o v d ho o' ho' h => rdW_wrW_A (by omega) (by omega) (by omega)
  refine key4 _ ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun x h1 h2 => ?_, fun x h1 h2 => ?_⟩
    rfl rfl rfl rfl rfl ?_ ?_ ?_
  · rsimp; exact hbase
  · exact hr8'
  · dsimp only
    rw [show base + abiNeed tab = base + abiNeed tab + 0 from rfl, hW 56 _ _ (by omega) 0 (by omega) (by omega), hW 40 _ _ (by omega) 0 (by omega) (by omega),
      hW 32 _ _ (by omega) 0 (by omega) (by omega), hW 24 _ _ (by omega) 0 (by omega) (by omega),
      hW 16 _ _ (by omega) 0 (by omega) (by omega), hW 8 _ _ (by omega) 0 (by omega) (by omega)]
    rw [Nat.add_zero, rdW_wrW_same]
  · dsimp only
    rw [hW 56 _ _ (by omega) 8 (by omega) (by omega), hW 40 _ _ (by omega) 8 (by omega) (by omega), hW 32 _ _ (by omega) 8 (by omega) (by omega),
      hW 24 _ _ (by omega) 8 (by omega) (by omega), hW 16 _ _ (by omega) 8 (by omega) (by omega), rdW_wrW_same]
  · dsimp only
    rw [hW 56 _ _ (by omega) 16 (by omega) (by omega), hW 40 _ _ (by omega) 16 (by omega) (by omega), hW 32 _ _ (by omega) 16 (by omega) (by omega),
      hW 24 _ _ (by omega) 16 (by omega) (by omega), rdW_wrW_same]
  · dsimp only
    rw [hW 56 _ _ (by omega) 24 (by omega) (by omega), hW 40 _ _ (by omega) 24 (by omega) (by omega), hW 32 _ _ (by omega) 24 (by omega) (by omega), rdW_wrW_same]
  · dsimp only
    rw [hW 56 _ _ (by omega) 32 (by omega) (by omega), hW 40 _ _ (by omega) 32 (by omega) (by omega), rdW_wrW_same]
  · dsimp only
    rw [hW 56 _ _ (by omega) 40 (by omega) (by omega), rdW_wrW_same]
  · dsimp only
    rcases (hcs x h1 h2).2.1 with h | h <;>
    exact isSome_get?_storeInt (isSome_get?_storeInt (isSome_get?_storeInt (isSome_get?_storeInt
        (isSome_get?_storeInt (isSome_get?_storeInt (isSome_get?_storeInt (hcs x h1 h2).1))))))
  · dsimp only
    exact isSome_get?_storeInt (isSome_get?_storeInt (isSome_get?_storeInt (isSome_get?_storeInt
        (isSome_get?_storeInt (isSome_get?_storeInt (isSome_get?_storeInt (by rw [hz x h1 h2]; rfl)))))))
  · rsimp; exact UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
  · dsimp only
    refine ⟨fun y hy => isSome_get?_storeInt (isSome_get?_storeInt (isSome_get?_storeInt (isSome_get?_storeInt
      (isSome_get?_storeInt (isSome_get?_storeInt (isSome_get?_storeInt hy)))))), fun x hx h => ?_⟩
    rw [get?_wrW_A (by omega) hx (by omega), get?_wrW_A (by omega) hx (by omega), get?_wrW_A (by omega) hx (by omega),
      get?_wrW_A (by omega) hx (by omega), get?_wrW_A (by omega) hx (by omega), get?_wrW_A (by omega) hx (by omega),
      get?_wrW_A (by omega) hx (by omega)]
  · dsimp only
    rw [rdW_wrW_same]; rfl


end





end ConAgua.Final
