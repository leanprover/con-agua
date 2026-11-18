module

public import ConAgua.Compiler.Step
import Kraken.X64.Registers
import Kraken.X64.WP.Basic

@[expose] public section

/-!
# Step lemmas for hand-written code

The compiler's step lemmas (`ConAgua/Compiler/Step.lean`, `StepGen.lean`) cover the forms the code
generator emits. Hand-written bodies (`AsmTab`) use a few more: `add`/`sub` of two registers with
their carry, `adc`, `add r, [b + 8 i]` with its carry, `lea d, [b + 8 i]`.
Each is one lemma in the same continuation-passing style.
-/

namespace L.Compiler

variable [Host]

section
variable {k : Nat} {s : MachineData} {Q : MachineState → Prop}

local macro "run_instr" : tactic =>
  `(tactic| (refine ev_instr (by assumption) (by rintro ⟨⟩) ?_;
             simp only [Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
               RelRegOrMem.interp, ConstExpr.interp, MachineData.load, MachineData.store,
               MachineData.set, MachineData.setReg, Reg64s.set_low_W64, Reg64s.get_low_W64,
               AddrExpr.zeroExtend_interp_base_disp, Width.bytes, Effects.All]))

omit [Host] in
theorem cf_add (a b : BitVec 64) :
    (BitVec.unsigned (a + b) != a.unsigned + b.unsigned) = decide (2 ^ 64 ≤ a.toNat + b.toNat) := by
  simp only [BitVec.unsigned_eq, BitVec.toNat_add]
  have := a.isLt; have := b.isLt
  by_cases h : 2 ^ 64 ≤ a.toNat + b.toNat
  · simp only [h, decide_true, bne_iff_ne, ne_eq]
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]; omega
  · simp only [h, decide_false, bne_eq_false_iff_eq]
    rw [Nat.mod_eq_of_lt (by omega)]; push_cast; rfl

omit [Host] in
theorem cf_add' (a b : BitVec 64) :
    (BitVec.unsigned (a + b) != b.unsigned + a.unsigned) = decide (2 ^ 64 ≤ a.toNat + b.toNat) := by
  rw [Int.add_comm]; exact cf_add a b

/-- `add d, r`, with the carry. -/
theorem ev_addRR {d r : Reg64} (hk : Host.prog[k]? = some (i64 (.add (.reg (rr d)) (oR r))))
    (h : ∀ st : StatusFlags, st.cf = decide (2 ^ 64 ≤ (s.regs.get64 d).toNat + (s.regs.get64 r).toNat) →
      Ev Q { s with regs := s.regs.set64 d (s.regs.get64 d + s.regs.get64 r), status := st } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  refine ev_of_regs (h _ ?_) ?_
  · simp only [Width.bits, StatusFlags.cf_from_result]
    rw [BitVec.add_comm]; first | exact cf_add' _ _ | exact cf_add _ _
  · simp [BitVec.add_comm]

/-- `sub d, r`, with the borrow. -/
theorem ev_subRR {d r : Reg64} (hk : Host.prog[k]? = some (i64 (.sub (.reg (rr d)) (oR r))))
    (h : ∀ st : StatusFlags, st.cf = decide ((s.regs.get64 d).toNat < (s.regs.get64 r).toNat) →
      Ev Q { s with regs := s.regs.set64 d (s.regs.get64 d - s.regs.get64 r), status := st } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  refine h _ ?_
  simp only [Width.bits, StatusFlags.cf_from_result, cf_cmp]

/-- `adc d, r`: `d := d + r + CF`. -/
theorem ev_adcRR {d r : Reg64} (hk : Host.prog[k]? = some (i64 (.adc (.reg (rr d)) (oR r))))
    (h : ∀ st, Ev Q { s with
      regs := s.regs.set64 d (s.regs.get64 d + s.regs.get64 r + (if s.status.cf then 1 else 0)),
      status := st } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  refine ev_flags h ?_
  congr 1
  cases s.status.cf <;> simp [BitVec.add_comm]

/-- `add d, [b + 8 i]`, with the carry. -/
theorem ev_addRS {d b i : Reg64} (hk : Host.prog[k]? = some (i64 (.add (.reg (rr d)) (oM (mbi b i .W64)))))
    {v : Word} (hv : rdW s.dmem (s.regs.get64 b + s.regs.get64 i * 8) = some v)
    (h : ∀ st : StatusFlags, st.cf = decide (2 ^ 64 ≤ (s.regs.get64 d).toNat + v.toNat) →
      Ev Q { s with regs := s.regs.set64 d (s.regs.get64 d + v.toBitVec), status := st } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  rw [addr_sib8]
  simp only [rdW, Option.map_eq_some_iff] at hv
  obtain ⟨j, hj, rfl⟩ := hv
  simp only [hj, Effects.All]
  refine ev_of_regs (h _ ?_) ?_
  · simp only [Width.bits, StatusFlags.cf_from_result]
    rw [BitVec.add_comm]; first | exact cf_add' _ _ | exact cf_add _ _
  · simp [BitVec.add_comm]

/-- `lea d, [b + 8 i]`. -/
theorem ev_leaX {d b i : Reg64} (hk : Host.prog[k]? = some (i64 (.lea (rr d) (mbi b i .W64))))
    (h : Ev Q { s with regs := s.regs.set64 d (s.regs.get64 b + s.regs.get64 i * 8) } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  rw [addr_sib8]
  exact h

end

end L.Compiler
