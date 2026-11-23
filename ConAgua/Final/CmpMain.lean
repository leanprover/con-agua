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
    (hgeo : CmpGeo tab own base dm.regs.r9.toNat rsp0 0 0)
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

end

end ConAgua.Final
