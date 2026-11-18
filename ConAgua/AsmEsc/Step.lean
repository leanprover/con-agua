module

public import ConAgua.Compiler.Step
import Kraken.X64.Registers
import Kraken.X64.WP.Basic

@[expose] public section

/-!
# Step lemmas for hand-written code

The compiler's step lemmas (`ConAgua/Compiler/Step.lean`, `StepGen.lean`) cover the forms the code
generator emits. Hand-written bodies (`AsmTab`) use a few more: `add`/`sub` of two registers with
their carry, `adc`, `add`/`sub r, [b + 8 i]` with the carry or borrow, `lea d, [b + 8 i]`.
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

/-- `sub d, [b + 8 i]`, with the borrow. -/
theorem ev_subRS {d b i : Reg64} (hk : Host.prog[k]? = some (i64 (.sub (.reg (rr d)) (oM (mbi b i .W64)))))
    {v : Word} (hv : rdW s.dmem (s.regs.get64 b + s.regs.get64 i * 8) = some v)
    (h : ∀ st : StatusFlags, st.cf = decide ((s.regs.get64 d).toNat < v.toNat) →
      Ev Q { s with regs := s.regs.set64 d (s.regs.get64 d - v.toBitVec), status := st } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  rw [addr_sib8]
  simp only [rdW, Option.map_eq_some_iff] at hv
  obtain ⟨j, hj, rfl⟩ := hv
  simp only [hj, Effects.All]
  refine h _ ?_
  simp only [Width.bits, StatusFlags.cf_from_result, cf_cmp]
  rfl

/-- The carry flag as a number. -/
abbrev cfN (st : StatusFlags) : Nat := if st.cf then 1 else 0

/-- The carry flag as a word. -/
abbrev cfW (st : StatusFlags) : BitVec 64 := if st.cf then 1 else 0

omit [Host] in
theorem cf_adc (a b : BitVec 64) (c : Bool) :
    (BitVec.unsigned (a + b + BitVec.ofNat 64 c.toNat) != a.unsigned + b.unsigned + (c.toNat : Int)) =
      decide (2 ^ 64 ≤ b.toNat + a.toNat + (if c then 1 else 0)) := by
  have := a.isLt; have := b.isLt
  cases c <;> simp only [BitVec.unsigned_eq, BitVec.toNat_add, Bool.toNat_false, Bool.toNat_true,
    BitVec.toNat_ofNat, Bool.false_eq_true, reduceIte] <;>
    (rw [Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_iff]; omega)

omit [Host] in
theorem adc_val (a b : BitVec 64) (st : StatusFlags) :
    a + b + BitVec.ofNat 64 st.cf.toNat = b + a + cfW st := by
  cases h : st.cf <;> simp [cfW, h, BitVec.add_comm]

/-- `adc d, [b + 8 i]`, with the carry. -/
theorem ev_adcRS {d b i : Reg64} (hk : Host.prog[k]? = some (i64 (.adc (.reg (rr d)) (oM (mbi b i .W64)))))
    {v : Word} (hv : rdW s.dmem (s.regs.get64 b + s.regs.get64 i * 8) = some v)
    (h : ∀ st : StatusFlags, st.cf = decide (2 ^ 64 ≤ (s.regs.get64 d).toNat + v.toNat + cfN s.status) →
      Ev Q { s with
        regs := s.regs.set64 d (s.regs.get64 d + v.toBitVec + cfW s.status),
        status := st } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  rw [addr_sib8]
  simp only [rdW, Option.map_eq_some_iff] at hv
  obtain ⟨j, hj, rfl⟩ := hv
  simp only [hj, Effects.All]
  refine ev_of_regs (h _ ?_) ?_
  · simp only [Width.bits, StatusFlags.cf_from_result, cf_adc]; rfl
  · simp only [Width.bits, adc_val]


/-- `and d, [b + 8 i]` (the flags are not used afterwards). -/
theorem ev_andRS {d b i : Reg64} (hk : Host.prog[k]? = some (i64 (.and (.reg (rr d)) (oM (mbi b i .W64)))))
    {v : Word} (hv : rdW s.dmem (s.regs.get64 b + s.regs.get64 i * 8) = some v)
    (h : ∀ st : StatusFlags, Ev Q { s with
        regs := s.regs.set64 d (BinOp.and.eval (UInt64.ofBitVec (s.regs.get64 d)) v).toBitVec,
        status := st } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  rw [addr_sib8]
  simp only [rdW, Option.map_eq_some_iff] at hv
  obtain ⟨j, hj, rfl⟩ := hv
  simp only [hj, Effects.All]
  intro _
  exact ev_of_regs (h _) rfl

/-- `or d, [b + 8 i]` (the flags are not used afterwards). -/
theorem ev_orRS {d b i : Reg64} (hk : Host.prog[k]? = some (i64 (.or (.reg (rr d)) (oM (mbi b i .W64)))))
    {v : Word} (hv : rdW s.dmem (s.regs.get64 b + s.regs.get64 i * 8) = some v)
    (h : ∀ st : StatusFlags, Ev Q { s with
        regs := s.regs.set64 d (BinOp.or.eval (UInt64.ofBitVec (s.regs.get64 d)) v).toBitVec,
        status := st } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  rw [addr_sib8]
  simp only [rdW, Option.map_eq_some_iff] at hv
  obtain ⟨j, hj, rfl⟩ := hv
  simp only [hj, Effects.All]
  intro _
  exact ev_of_regs (h _) rfl

/-- `xor d, [b + 8 i]` (the flags are not used afterwards). -/
theorem ev_xorRS {d b i : Reg64} (hk : Host.prog[k]? = some (i64 (.xor (.reg (rr d)) (oM (mbi b i .W64)))))
    {v : Word} (hv : rdW s.dmem (s.regs.get64 b + s.regs.get64 i * 8) = some v)
    (h : ∀ st : StatusFlags, Ev Q { s with
        regs := s.regs.set64 d (BinOp.xor.eval (UInt64.ofBitVec (s.regs.get64 d)) v).toBitVec,
        status := st } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  rw [addr_sib8]
  simp only [rdW, Option.map_eq_some_iff] at hv
  obtain ⟨j, hj, rfl⟩ := hv
  simp only [hj, Effects.All]
  intro _
  exact ev_of_regs (h _) rfl

omit [Host] in
theorem cf_sbb (a b : BitVec 64) (c : Bool) :
    (BitVec.unsigned (b - a - BitVec.ofNat 64 c.toNat) != b.unsigned - a.unsigned - (c.toNat : Int)) =
      decide (b.toNat < a.toNat + (if c then 1 else 0)) := by
  have := a.isLt; have := b.isLt
  cases c <;> simp only [BitVec.unsigned_eq, BitVec.toNat_sub, Bool.toNat_false, Bool.toNat_true,
    BitVec.toNat_ofNat, Bool.false_eq_true, reduceIte] <;>
    (rw [Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_iff]; omega)

omit [Host] in
theorem sbb_val (a b : BitVec 64) (st : StatusFlags) :
    b - a - BitVec.ofNat 64 st.cf.toNat = b - a - cfW st := by
  cases h : st.cf <;> simp [cfW, h]

/-- `sbb d, [b + 8 i]`, with the borrow. -/
theorem ev_sbbRS {d b i : Reg64} (hk : Host.prog[k]? = some (i64 (.sbb (.reg (rr d)) (oM (mbi b i .W64)))))
    {v : Word} (hv : rdW s.dmem (s.regs.get64 b + s.regs.get64 i * 8) = some v)
    (h : ∀ st : StatusFlags, st.cf = decide ((s.regs.get64 d).toNat < v.toNat + cfN s.status) →
      Ev Q { s with
        regs := s.regs.set64 d (s.regs.get64 d - v.toBitVec - cfW s.status),
        status := st } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  rw [addr_sib8]
  simp only [rdW, Option.map_eq_some_iff] at hv
  obtain ⟨j, hj, rfl⟩ := hv
  simp only [hj, Effects.All]
  refine ev_of_regs (h _ ?_) ?_
  · simp only [Width.bits, StatusFlags.cf_from_result, cf_sbb]; rfl
  · simp only [Width.bits, sbb_val]

/-- `adc d, r`, with the carry. -/
theorem ev_adcRRc {d r : Reg64} (hk : Host.prog[k]? = some (i64 (.adc (.reg (rr d)) (oR r))))
    (h : ∀ st : StatusFlags, st.cf = decide (2 ^ 64 ≤ (s.regs.get64 d).toNat + (s.regs.get64 r).toNat + cfN s.status) →
      Ev Q { s with
        regs := s.regs.set64 d (s.regs.get64 d + s.regs.get64 r + cfW s.status),
        status := st } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  refine ev_of_regs (h _ ?_) ?_
  · simp only [Width.bits, StatusFlags.cf_from_result, cf_adc]
  · simp only [Width.bits, adc_val]

/-- `sbb d, r`, with the borrow. -/
theorem ev_sbbRRc {d r : Reg64} (hk : Host.prog[k]? = some (i64 (.sbb (.reg (rr d)) (oR r))))
    (h : ∀ st : StatusFlags, st.cf = decide ((s.regs.get64 d).toNat < (s.regs.get64 r).toNat + cfN s.status) →
      Ev Q { s with
        regs := s.regs.set64 d (s.regs.get64 d - s.regs.get64 r - cfW s.status),
        status := st } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  refine ev_of_regs (h _ ?_) ?_
  · simp only [Width.bits, StatusFlags.cf_from_result, cf_sbb]
  · simp only [Width.bits, sbb_val]

/-- `inc r`: the carry flag stays. -/
theorem ev_incR {r : Reg64} (hk : Host.prog[k]? = some (i64 (.inc (.reg (rr r)))))
    (h : ∀ st : StatusFlags, st.cf = s.status.cf →
      Ev Q { s with regs := s.regs.set64 r (s.regs.get64 r + 1), status := st } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  exact h _ (by simp [StatusFlags.cf_from_result])

/-- `dec r`: the carry flag stays; the zero flag says whether the result is zero. -/
theorem ev_decR {r : Reg64} (hk : Host.prog[k]? = some (i64 (.dec (.reg (rr r)))))
    (h : ∀ st : StatusFlags, st.cf = s.status.cf → st.zf = decide (s.regs.get64 r - 1 = 0) →
      Ev Q { s with regs := s.regs.set64 r (s.regs.get64 r - 1), status := st } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  exact h _ (by simp [StatusFlags.cf_from_result])
    (by simp only [StatusFlags.zf_from_result, BitVec.zero_eq]; rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]; rfl)

/-- `add r, imm`, with the carry. -/
theorem ev_addRIc {r : Reg64} {i : Int} (hk : Host.prog[k]? = some (i64 (.add (.reg (rr r)) (oI i))))
    (h : ∀ st : StatusFlags,
      st.cf = decide (2 ^ 64 ≤ (s.regs.get64 r).toNat + (Int64.ofInt i).toBitVec.toNat) →
      Ev Q { s with regs := s.regs.set64 r (s.regs.get64 r + (Int64.ofInt i).toBitVec), status := st }
        (at_ (k + 1))) : Ev Q s (at_ k) := by
  run_instr
  refine ev_of_regs (h _ ?_) ?_
  · simp only [Width.bits, StatusFlags.cf_from_result, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq]
    rw [BitVec.add_comm]; first | exact cf_add' _ _ | exact cf_add _ _
  · simp [BitVec.add_comm]

/-- `mul [b + 8 i]`: `rdx:rax := rax * v`, unsigned. -/
theorem ev_mulS {b i : Reg64} (hk : Host.prog[k]? = some (i64 (.mul (.mem (mbi b i .W64)))))
    {v : Word} (hv : rdW s.dmem (s.regs.get64 b + s.regs.get64 i * 8) = some v)
    (h : ∀ st, Ev Q { s with
      regs := ((s.regs.set64 .rax (s.regs.rax * v).toBitVec).set64 .rdx (BinOp.mulhi.eval s.regs.rax v).toBitVec),
      status := st } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  rw [addr_sib8]
  simp only [rdW, Option.map_eq_some_iff] at hv
  obtain ⟨j, hj, rfl⟩ := hv
  simp only [hj, Effects.All]
  intro _ _ _ _
  simp only [show (Width.W64 == Width.W8) = false from rfl, Bool.false_eq_true, ite_false]
  refine ev_flags h ?_
  congr 1
  simp only [BinOp.eval, Width.bits, Reg64s.get64_rax, BitVec.unsigned, UInt64.toNat_toBitVec,
    UInt64.toNat_ofBitVec]
  generalize BitVec.ofInt 64 j = w
  rw [show ((s.regs.rax.toNat : Int) * (w.toNat : Int)) =
      ((s.regs.rax.toNat * w.toNat : Nat) : Int) by push_cast; rfl, Int.shiftRight_eq_div_pow]
  apply BitVec.eq_of_toNat_eq
  simp
  omega

/-- `lea d, [b + 8 i]`. -/
theorem ev_leaX {d b i : Reg64} (hk : Host.prog[k]? = some (i64 (.lea (rr d) (mbi b i .W64))))
    (h : Ev Q { s with regs := s.regs.set64 d (s.regs.get64 b + s.regs.get64 i * 8) } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  rw [addr_sib8]
  exact h

end

end L.Compiler
