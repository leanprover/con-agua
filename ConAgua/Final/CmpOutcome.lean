module

public import ConAgua.Compiler.AbiCmp
public import ConAgua.Final.Statement
import ConAgua.Compiler.Main
import ConAgua.L.Logic
import Kraken.X64.Registers

@[expose] public section

/-!
# The compared run's entries `ca_start_ac`, `ca_start_c` on the machine: the pieces (lanes compare, compare2)

The entries' code as one list literal (`cmpStubL`), the frame between the front's calls
(`CmpFrame`: the save area, the callee-saved registers, the stack window), the exit
(`cmp_exit`), the test after a mode entry's call (`cmp_okGe`), and what a return means
(`CmpPost`, `CmpPostH`). The theorems: `ConAgua/Final/CmpMain.lean`.
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

/-- **The driver's frame between its calls**: `r15` the region, `rsp` one word above the call's
(the return address popped), the callee-saved registers the caller's, the save area's first six
words (the caller's `r15`, the return address, the solution's buffer and length, the pin data's),
the stack window and the region mapped. -/
structure CmpFrame (tab : Tab) (dm : MachineData) (ra sa : Word) (nS base rsp0 : Nat) (s : MachineData) : Prop where
  r15 : s.regs.r15.toNat = base
  rsp : s.regs.rsp.toNat = rsp0 + 8
  rbp : s.regs.rbp = dm.regs.rbp
  r14 : s.regs.r14 = dm.regs.r14
  rbx : s.regs.rbx = dm.regs.rbx
  r12 : s.regs.r12 = dm.regs.r12
  r13 : s.regs.r13 = dm.regs.r13
  sv0 : rdW s.dmem (A (base + abiNeed tab)) = some dm.regs.r15
  sv1 : rdW s.dmem (A (base + abiNeed tab + 8)) = some ra
  sv2 : rdW s.dmem (A (base + abiNeed tab + 16)) = some sa
  sv3 : rdW s.dmem (A (base + abiNeed tab + 24)) = some (UInt64.ofNat nS)
  sv4 : rdW s.dmem (A (base + abiNeed tab + 32)) = some dm.regs.rdx
  sv5 : rdW s.dmem (A (base + abiNeed tab + 40)) = some dm.regs.rcx
  win : ∀ x, rsp0 - 24 ≤ x → x < rsp0 + 8 → (s.dmem.get? (A x)).isSome
  map : ∀ x, base ≤ x → x < base + dm.regs.r9.toNat → (s.dmem.get? (A x)).isSome

/-- What `ca_compare` leaves: the return to `ra`, the caller's registers, and the meaning of an
accept and of an error. -/
def CmpPost (dm : MachineData) (ra : Word) (Acc : Prop) (Err : Word → Prop) (st : MachineState) : Prop :=
  st.pc = Int64.ofBitVec ra.toBitVec ∧ RegsRestored dm.regs st.data.regs ∧
    (st.data.regs.rdx = 0 → st.data.regs.rax = ACCEPT → Acc) ∧ (st.data.regs.rdx = 2 → Err st.data.regs.rax)

/-- `CmpPost`, and what a return with `rdx = 0`, `rax ≥ 2^63` means (`Hi`, of `rax` and the
memory; the threaded run's entry 1). -/
def CmpPostH (dm : MachineData) (ra : Word) (Acc : Prop) (Err : Word → Prop) (Hi : Word → DataMem → Prop)
    (st : MachineState) : Prop :=
  CmpPost dm ra Acc Err st ∧
    (st.data.regs.rdx = 0 → 2 ^ 63 ≤ st.data.regs.rax.toNat → Hi st.data.regs.rax st.data.dmem)

section
variable [Host] {tab : Tab} {mode : GVar}

/-- `cmpStub` as one list literal (directive `i` at index `i`). -/
def cmpStubL (tab : Tab) (mode : GVar) : Program :=
  [.label abiStartA4L,
   movRI .rax (abiNeed tab).toUInt64,
   i64 (.cmp (.reg (rr .r9)) (oR .rax)),
   jccL .c abiSetupL,
   movRI .rax 4,
   movMR (mb .r8 (tab.globOff mode)) .rax,
   jmpL abiSetupL,
   .label abiStartA5L,
   movRI .rax (abiNeed tab).toUInt64,
   i64 (.cmp (.reg (rr .r9)) (oR .rax)),
   jccL .c abiSetupL,
   movRI .rax 5,
   movMR (mb .r8 (tab.globOff mode)) .rax,
   jmpL abiSetupL,
   .label abiStartA6L,
   movRI .rax (abiNeed tab).toUInt64,
   i64 (.cmp (.reg (rr .r9)) (oR .rax)),
   jccL .c abiSetupL,
   movRI .rax 6,
   movMR (mb .r8 (tab.globOff mode)) .rax,
   jmpL abiSetupL,
   .label abiStartA7L,
   movRI .rax (abiNeed tab).toUInt64,
   i64 (.cmp (.reg (rr .r9)) (oR .rax)),
   jccL .c abiSetupL,
   movRI .rax 7,
   movMR (mb .r8 (tab.globOff mode)) .rax,
   jmpL abiSetupL,
   .label abiStartCL,
   movRI .r10 0,
   jmpL abiCmpFrontL,
   .label abiStartACL,
   movRI .r10 1,
   .label abiCmpFrontL,
   movRI .rax (drvNeed tab).toUInt64,
   i64 (.cmp (.reg (rr .r9)) (oR .rax)),
   jccL .c abiCmpDeclineL,
   movRI .rax (cmpSave tab).toUInt64,
   i64 (.add (.reg (rr .rax)) (oR .r8)),
   movMR (mb .rax 0) .r15,
   i64 (.pop (.reg (rr .r11))),
   movMR (mb .rax 8) .r11,
   movRM .r11 (mb .rsp 0),
   movMR (mb .rax 16) .r11,
   movRM .r11 (mb .rsp 8),
   movMR (mb .rax 24) .r11,
   movMR (mb .rax 32) .rdx,
   movMR (mb .rax 40) .rcx,
   movMR (mb .rax 56) .r10,
   movRR .r15 .r8,
   movRI .r9 (abiNeed tab).toUInt64,
   callL abiStartA4L,
   i64 (.cmp (.reg (rr .rdx)) (oI 0)),
   jccL .nz abiCmpDoneL,
   movRI .rcx 9223372036854775808,
   i64 (.cmp (.reg (rr .rax)) (oR .rcx)),
   jccL .c abiCmpDoneL,
   movRI .rax (cmpSave tab).toUInt64,
   i64 (.add (.reg (rr .rax)) (oR .r15)),
   movRM .rdi (mb .rax 16),
   movRM .rsi (mb .rax 24),
   movRM .rdx (mb .rax 32),
   movRM .rcx (mb .rax 40),
   movRR .r8 .r15,
   movRI .r9 (abiNeed tab).toUInt64,
   callL abiStartA5L,
   i64 (.cmp (.reg (rr .rdx)) (oI 0)),
   jccL .nz abiCmpDoneL,
   movRI .rcx 9223372036854775808,
   i64 (.cmp (.reg (rr .rax)) (oR .rcx)),
   jccL .c abiCmpDoneL,
   i64 (.sub (.reg (rr .rax)) (oR .rcx)),
   movRR .rdx .rax,
   movRI .rax (cmpSave tab).toUInt64,
   i64 (.add (.reg (rr .rax)) (oR .r15)),
   movMR (mb .rax 48) .rdx,
   movRM .r11 (mb .rax 56),
   i64 (.cmp (.reg (rr .r11)) (oI 0)),
   jccL .nz abiCmpThrL,
   movRI .rax (cmpSave tab).toUInt64,
   i64 (.add (.reg (rr .rax)) (oR .r15)),
   movRM .rdi (mb .rax 16),
   movRM .rsi (mb .rax 24),
   movRM .rdx (mb .rax 32),
   movRM .rcx (mb .rax 40),
   movRR .r8 .r15,
   movRI .r9 (abiNeed tab).toUInt64,
   callL abiStartA6L,
   i64 (.cmp (.reg (rr .rdx)) (oI 0)),
   jccL .nz abiCmpDoneL,
   movRI .rcx 9223372036854775808,
   i64 (.cmp (.reg (rr .rax)) (oR .rcx)),
   jccL .c abiCmpDoneL,
   i64 (.sub (.reg (rr .rax)) (oR .rcx)),
   movRR .rdx .rax,
   movRI .rax (cmpSave tab).toUInt64,
   i64 (.add (.reg (rr .rax)) (oR .r15)),
   movMR (mb .rax 56) .rdx,
   movRI .r10 8,
   movRI .rsi 0,
   movRM .rdx (mb .rax 48),
   movRR .r8 .r15,
   callL abiCheckSML,
   i64 (.cmp (.reg (rr .rdx)) (oI 0)),
   jccL .nz abiCmpDoneL,
   movRI .rcx 71757147230292,
   i64 (.cmp (.reg (rr .rax)) (oR .rcx)),
   jccL .nz abiCmpDoneL,
   movRI .rax (cmpSave tab).toUInt64,
   i64 (.add (.reg (rr .rax)) (oR .r15)),
   movRM .rdx (mb .rax 56),
   movRI .r10 9,
   movRI .rsi 0,
   movRR .r8 .r15,
   movRI .rax (abiSlot + abiStack).toUInt64,
   i64 (.add (.reg (rr .rax)) (oR .r15)),
   movMR (mb .r15 Tab.stackTop) .rax,
   callL abiCheckSGL,
   jmpL abiCmpDoneL,
   .label abiCmpThrL,
   movRI .rax (cmpSave tab).toUInt64,
   i64 (.add (.reg (rr .rax)) (oR .r15)),
   movRM .rdi (mb .rax 16),
   movRM .rsi (mb .rax 24),
   movRM .rdx (mb .rax 32),
   movRM .rcx (mb .rax 40),
   movRR .r8 .r15,
   movRI .r9 (abiNeed tab).toUInt64,
   callL abiStartA7L,
   i64 (.cmp (.reg (rr .rdx)) (oI 0)),
   jccL .nz abiCmpDoneL,
   movRI .rcx 9223372036854775808,
   i64 (.cmp (.reg (rr .rax)) (oR .rcx)),
   jccL .c abiCmpDoneL,
   i64 (.sub (.reg (rr .rax)) (oR .rcx)),
   movRR .rdx .rax,
   movRI .rax (cmpSave tab).toUInt64,
   i64 (.add (.reg (rr .rax)) (oR .r15)),
   movRM .r11 (mb .rax 48),
   i64 (.add (.reg (rr .rdx)) (oR .r11)),
   movRI .rax 9223372036854775808,
   i64 (.add (.reg (rr .rax)) (oR .rdx)),
   movRI .rdx 0,
   .label abiCmpDoneL,
   movRR .rcx .rax,
   movRI .rax (cmpSave tab).toUInt64,
   i64 (.add (.reg (rr .rax)) (oR .r15)),
   movRM .rsi (mb .rax 8),
   movRM .r15 (mb .rax 0),
   movRR .rax .rcx,
   i64 (.push (oR .rsi)),
   i64 .ret,
   .label abiCmpDeclineL,
   movRI .rax 0,
   movRI .rdx 1,
   i64 .ret]

set_option maxRecDepth 20000 in
omit [Host] in
/-- `cmpStub` as one list literal. -/
theorem cmpStub_lit : cmpStub tab mode = cmpStubL tab mode := by
  simp only [cmpStub, cmpEntries, cmpFront, cmpSeqTail, cmpThrTail, cmpExit, cmpModeEntry, cmpOkGe, cmpArgsS,
    cmpSaveRax, List.cons_append, List.nil_append, List.append_assoc, cmpStubL]

/-- **The exit** (`ca_cmp_done`): the caller's `r15` and the return address back from the save
area, the return. -/
theorem cmp_exit {Kc : Nat} (hC : Code (cmpStubL tab mode) Kc) (dm : MachineData) (ra sa : Word)
    {nS base rsp0 : Nat} (hfit : base + abiNeed tab + 64 < 2 ^ 64) (hrsp : 24 ≤ rsp0 ∧ rsp0 + 8 < 2 ^ 64)
    (hrsp0 : dm.regs.rsp.toNat = rsp0)
    (Acc : Prop) (Err : Word → Prop) (Hi : Word → DataMem → Prop) (s : MachineData)
    (hf : CmpFrame tab dm ra sa nS base rsp0 s)
    (hacc : s.regs.rdx = 0 → s.regs.rax = ACCEPT → Acc) (herr : s.regs.rdx = 2 → Err s.regs.rax)
    (hhi : s.regs.rdx = 0 → 2 ^ 63 ≤ s.regs.rax.toNat → ∀ v, Hi s.regs.rax (wrW s.dmem (A rsp0) v)) :
    Ev (CmpPostH dm ra Acc Err Hi) s (label abiCmpDoneL) := by
  rw [Code.label (i := 143) hC rfl]
  refine ev_label (hC.get (i := 143) rfl) ?_
  refine ev_movRR (hC.get (i := 144) rfl) ?_
  refine ev_movRI (hC.get (i := 145) rfl) ?_
  refine ev_binO (op := .add) (o := oR .r15) rfl (hC.get (i := 146) rfl)
    (Or.inr (Or.inr ⟨.r15, rfl, rfl⟩)) fun st => ?_
  have hsa : (BinOp.add.eval (cmpSave tab).toUInt64 s.regs.r15).toNat = base + abiNeed tab := by
    simp only [BinOp.eval, UInt64.toNat_add, cmpSave, hf.r15, Nat.toUInt64]
    rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
    omega
  refine ev_movRM (hC.get (i := 147) rfl) ⟨by decide, by decide⟩ (v := ra) ?_ ?_
  · rsimp; rw [hsa]; exact hf.sv1
  refine ev_movRM (hC.get (i := 148) rfl) ⟨by decide, by decide⟩ (v := dm.regs.r15) ?_ ?_
  · rsimp; rw [hsa]; exact hf.sv0
  refine ev_movRR (hC.get (i := 149) rfl) ?_
  have e1 : s.regs.rsp.toBitVec - 8 = A rsp0 := by
    rw [toBitVec_eq_A, hf.rsp, A_sub8 _ (by omega) (by omega)]; rfl
  refine ev_push (hC.get (i := 150) rfl) ?_ ?_
  · rsimp; rw [e1]; exact isSome_rdW fun j hj => by rw [A_add]; exact hf.win _ (by omega) (by omega)
  refine ev_ret (hC.get (i := 151) rfl) (ra := ra) ?_ ?_
  · rsimp; rw [rdW_wrW_same]
  refine Eventually.done _ ⟨⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · rsimp; rw [BitVec.sub_add_cancel]; show s.regs.rsp.toNat = _; rw [hf.rsp, hrsp0]
  · rsimp; exact hf.rbp
  · rsimp; exact hf.r14
  · rsimp
  · rsimp; exact hf.rbx
  · rsimp; exact hf.r12
  · rsimp; exact hf.r13
  · rsimp; exact hacc
  · rsimp; exact herr
  · rsimp; rw [e1]; exact fun h0 h1 => hhi h0 h1 _

omit [Host] in
/-- A frame survives a change of registers other than the frame's and of no memory. -/
theorem CmpFrame.regs {dm : MachineData} {ra sa : Word} {nS base rsp0 : Nat} {s s' : MachineData}
    (hf : CmpFrame tab dm ra sa nS base rsp0 s) (hm : s'.dmem = s.dmem)
    (hr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .rdi → r ≠ .r8 → r ≠ .r9 → r ≠ .r11 →
      s'.regs.get64 r = s.regs.get64 r) : CmpFrame tab dm ra sa nS base rsp0 s' := by
  have e : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .rdi → r ≠ .r8 → r ≠ .r9 → r ≠ .r11 →
      UInt64.ofBitVec (s'.regs.get64 r) = UInt64.ofBitVec (s.regs.get64 r) := fun r a b c d e f g h => by
    rw [hr r a b c d e f g h]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := e .r15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    simp only [Reg64s.get64_r15, UInt64.ofBitVec_toBitVec] at this; rw [this]; exact hf.r15
  · have := e .rsp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    simp only [Reg64s.get64_rsp, UInt64.ofBitVec_toBitVec] at this; rw [this]; exact hf.rsp
  · have := e .rbp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    simp only [Reg64s.get64_rbp, UInt64.ofBitVec_toBitVec] at this; rw [this]; exact hf.rbp
  · have := e .r14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    simp only [Reg64s.get64_r14, UInt64.ofBitVec_toBitVec] at this; rw [this]; exact hf.r14
  · have := e .rbx (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    simp only [Reg64s.get64_rbx, UInt64.ofBitVec_toBitVec] at this; rw [this]; exact hf.rbx
  · have := e .r12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    simp only [Reg64s.get64_r12, UInt64.ofBitVec_toBitVec] at this; rw [this]; exact hf.r12
  · have := e .r13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    simp only [Reg64s.get64_r13, UInt64.ofBitVec_toBitVec] at this; rw [this]; exact hf.r13
  all_goals first
    | (rw [hm]; first | exact hf.sv0 | exact hf.sv1 | exact hf.sv2 | exact hf.sv3 | exact hf.sv4 | exact hf.sv5)
    | (intro x h1 h2; rw [hm]; first | exact hf.win x h1 h2 | exact hf.map x h1 h2)

/-- **A mode entry's verdict** (`cmpOkGe`, five instructions at `i`): unless `rdx = 0` and
`rax ≥ 2^63`, to the exit with the registers but `rcx` and the flags; else on, `rcx = 2^63`. -/
theorem cmp_okGe {Kc i : Nat} (hC : Code (cmpStubL tab mode) Kc)
    (h0 : (cmpStubL tab mode)[i]? = some (i64 (.cmp (.reg (rr .rdx)) (oI 0))))
    (h1 : (cmpStubL tab mode)[i + 1]? = some (jccL .nz abiCmpDoneL))
    (h2 : (cmpStubL tab mode)[i + 2]? = some (movRI .rcx 9223372036854775808))
    (h3 : (cmpStubL tab mode)[i + 3]? = some (i64 (.cmp (.reg (rr .rax)) (oR .rcx))))
    (h4 : (cmpStubL tab mode)[i + 4]? = some (jccL .c abiCmpDoneL))
    {Q : MachineState → Prop} (s : MachineData)
    (hbad : ∀ s' : MachineData, s'.dmem = s.dmem → (∀ r, r ≠ .rcx → s'.regs.get64 r = s.regs.get64 r) →
      (s.regs.rdx ≠ 0 ∨ s.regs.rax.toNat < 2 ^ 63) → Ev Q s' (label abiCmpDoneL))
    (hgood : s.regs.rdx = 0 → 2 ^ 63 ≤ s.regs.rax.toNat → ∀ st,
      Ev Q { s with regs := s.regs.set64 .rcx (9223372036854775808 : Word).toBitVec, status := st } (at_ (Kc + i + 5))) :
    Ev Q s (at_ (Kc + i)) := by
  refine ev_cmpRO (r := .rdx) (o := oI 0) (v := 0) (hC.get h0) (Or.inl rfl) ?_
  refine ev_jcc (hC.get h1) (fun hnz => ?_) (fun hz0 => ?_)
  · refine hbad _ rfl (fun r _ => rfl) (Or.inl fun h0 => ?_)
    simp only [CondCode.interp, cmpFlags_zf, Reg64s.get64_rdx] at hnz
    rw [h0] at hnz; exact absurd hnz (by decide)
  simp only [CondCode.interp, cmpFlags_zf, Reg64s.get64_rdx] at hz0
  have hrdx0 : s.regs.rdx = 0 := by
    simp only [Bool.not_eq_false', beq_iff_eq] at hz0
    exact UInt64.toBitVec_inj.mp hz0
  refine ev_movRI (hC.get h2) ?_
  refine ev_cmpRO (r := .rax) (o := oR .rcx) (v := (9223372036854775808 : Word)) (hC.get h3)
    (Or.inr (Or.inr ⟨.rcx, rfl, rfl⟩)) ?_
  refine ev_jcc (hC.get h4) (fun hlt => ?_) (fun hge => ?_)
  · refine hbad _ rfl (fun r hr => ?_) (Or.inr ?_)
    · cases r <;> first | exact absurd rfl hr | rfl
    · simp only [CondCode.interp, cmpFlags_cf, decide_eq_true_eq] at hlt
      rsimp at hlt; simpa using hlt
  · simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not, Nat.not_lt] at hge
    rsimp at hge
    exact hgood hrdx0 (by simpa using hge) _

/-- **The driver's geometry**: the region `[base, base + blen)` in the address space and large
enough (`drvNeed`), the stack window around `rsp0` apart from it. -/
structure CmpGeo (tab : Tab) (base blen rsp0 : Nat) : Prop where
  fits : base + blen < 2 ^ 64
  need : drvNeed tab ≤ blen
  win : ∀ x, rsp0 - 24 ≤ x → x < rsp0 + 8 → x < base ∨ base + blen ≤ x
  r24 : 24 ≤ rsp0
  r8 : rsp0 + 8 < 2 ^ 64

omit [Host] in
/-- `a + r` as the code computes it (`movRI`, then `add r15`). -/
theorem toNat_add_reg (a : Nat) (b : UInt64) (h : a + b.toNat < 2 ^ 64) :
    (UInt64.ofBitVec ((a.toUInt64).toBitVec + b.toBitVec)).toNat = a + b.toNat := by
  simp only [UInt64.toNat_ofBitVec, BitVec.toNat_add, UInt64.toNat_toBitVec, Nat.toUInt64,
    UInt64.toNat_ofNat_of_lt' (show a < 2 ^ 64 by omega)]
  omega

omit [Host] in
/-- `a + r` as the code computes it, as a bit vector. -/
theorem toNat_add_reg' (a : Nat) (b : UInt64) (h : a + b.toNat < 2 ^ 64) :
    ((a.toUInt64).toBitVec + b.toBitVec).toNat = a + b.toNat := by
  simp only [BitVec.toNat_add, UInt64.toNat_toBitVec, Nat.toUInt64,
    UInt64.toNat_ofNat_of_lt' (show a < 2 ^ 64 by omega)]
  omega

omit [Host] in
/-- **The frame after a call** made from a frame (the return address pushed at `rsp0`): the callee
restored the caller's registers and left the save area alone. -/
theorem CmpFrame.ret {dm : MachineData} {ra sa : Word} {nS base rsp0 : Nat} {s st : MachineData}
    (hf : CmpFrame tab dm ra sa nS base rsp0 s) (_hfit : base + abiNeed tab + 64 < 2 ^ 64)
    (_hr8 : rsp0 + 8 < 2 ^ 64) {R : Reg64s} (hRsp : R.rsp.toNat = rsp0)
    (hR : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .rdi → r ≠ .r8 → r ≠ .r9 → r ≠ .r11 → r ≠ .rsp →
      R.get64 r = s.regs.get64 r) (hrr : RegsRestored R st.regs)
    (hsave : ∀ x, base + abiNeed tab ≤ x → x < base + abiNeed tab + 64 → st.dmem.get? (A x) = s.dmem.get? (A x))
    (hgrow : ∀ y, (s.dmem.get? y).isSome → (st.dmem.get? y).isSome) : CmpFrame tab dm ra sa nS base rsp0 st := by
  obtain ⟨hsp, hbp, h14, h15, hbx, h12, h13⟩ := hrr
  have e : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .rdi → r ≠ .r8 → r ≠ .r9 → r ≠ .r11 → r ≠ .rsp →
      UInt64.ofBitVec (R.get64 r) = UInt64.ofBitVec (s.regs.get64 r) := fun r a b c d e f g h i => by
    rw [hR r a b c d e f g h i]
  have e15 := e .r15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have ebp := e .rbp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have e14 := e .r14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have ebx := e .rbx (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have e12 := e .r12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have e13 := e .r13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  simp only [Reg64s.get64_r15, Reg64s.get64_rbp, Reg64s.get64_r14, Reg64s.get64_rbx, Reg64s.get64_r12,
    Reg64s.get64_r13, UInt64.ofBitVec_toBitVec] at e15 ebp e14 ebx e12 e13
  have hsv : ∀ o, o + 8 ≤ 64 → rdW st.dmem (A (base + abiNeed tab + o)) = rdW s.dmem (A (base + abiNeed tab + o)) :=
    fun o ho => rdW_congr fun j hj => by rw [A_add]; exact hsave _ (by omega) (by omega)
  refine ⟨by rw [h15, e15]; exact hf.r15, by rw [hsp, hRsp], by rw [hbp, ebp]; exact hf.rbp,
    by rw [h14, e14]; exact hf.r14, by rw [hbx, ebx]; exact hf.rbx, by rw [h12, e12]; exact hf.r12,
    by rw [h13, e13]; exact hf.r13,
    by rw [show base + abiNeed tab = base + abiNeed tab + 0 by rfl, hsv 0 (by omega)]; exact hf.sv0,
    by rw [hsv 8 (by omega)]; exact hf.sv1, by rw [hsv 16 (by omega)]; exact hf.sv2,
    by rw [hsv 24 (by omega)]; exact hf.sv3, by rw [hsv 32 (by omega)]; exact hf.sv4,
    by rw [hsv 40 (by omega)]; exact hf.sv5, fun x h1 h2 => hgrow _ (hf.win x h1 h2),
    fun x h1 h2 => hgrow _ (hf.map x h1 h2)⟩

omit [Host] in
/-- A store into the save area past its first six words keeps the frame. -/
theorem CmpFrame.wr {dm : MachineData} {ra sa : Word} {nS base rsp0 : Nat} {s : MachineData}
    (hf : CmpFrame tab dm ra sa nS base rsp0 s) (hfit : base + abiNeed tab + 64 < 2 ^ 64)
    (_hwin : rsp0 + 8 ≤ base ∨ base + dm.regs.r9.toNat ≤ rsp0 - 24) {y : Nat} {v : BitVec 64}
    (hy : base + abiNeed tab + 48 ≤ y) (hy' : y + 8 ≤ base + abiNeed tab + 64) :
    CmpFrame tab dm ra sa nS base rsp0 { s with dmem := wrW s.dmem (A y) v } := by
  have hsv : ∀ o, o + 8 ≤ 48 → rdW (wrW s.dmem (A y) v) (A (base + abiNeed tab + o)) =
      rdW s.dmem (A (base + abiNeed tab + o)) := fun o ho => rdW_wrW_A (by omega) (by omega) (by omega)
  refine ⟨hf.r15, hf.rsp, hf.rbp, hf.r14, hf.rbx, hf.r12, hf.r13,
    by rw [show base + abiNeed tab = base + abiNeed tab + 0 by rfl]; dsimp only; rw [hsv 0 (by omega)]; exact hf.sv0,
    by dsimp only; rw [hsv 8 (by omega)]; exact hf.sv1, by dsimp only; rw [hsv 16 (by omega)]; exact hf.sv2,
    by dsimp only; rw [hsv 24 (by omega)]; exact hf.sv3, by dsimp only; rw [hsv 32 (by omega)]; exact hf.sv4,
    by dsimp only; rw [hsv 40 (by omega)]; exact hf.sv5, fun x h1 h2 => isSome_get?_storeInt (hf.win x h1 h2),
    fun x h1 h2 => isSome_get?_storeInt (hf.map x h1 h2)⟩

end

end ConAgua.Final
