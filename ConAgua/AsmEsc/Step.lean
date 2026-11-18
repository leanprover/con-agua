module

public import ConAgua.Compiler.Step
import Kraken.X64.Registers
import Kraken.X64.WP.Basic

@[expose] public section

/-!
# Step lemmas for hand-written code

The compiler's step lemmas (`ConAgua/Compiler/Step.lean`) cover the forms the code generator
emits. Hand-written bodies (`AsmTab`) use a few more: two-register ALU forms with their carry,
`adc`, `mul r`, `shr r, n`, loads, stores and `lea` with a scaled index register, `add r, [b + 8 i]`.
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

/-- `and d, r`. -/
theorem ev_andRR {d r : Reg64} (hk : Host.prog[k]? = some (i64 (.and (.reg (rr d)) (oR r))))
    (h : ∀ st, Ev Q { s with regs := s.regs.set64 d (s.regs.get64 d &&& s.regs.get64 r), status := st }
      (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  intros; refine ev_flags h ?_; simp [BitVec.and_comm]

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

/-- `mul r`: `rdx:rax := rax * r`, unsigned. -/
theorem ev_mulR {r : Reg64} (hk : Host.prog[k]? = some (i64 (.mul (.reg (rr r)))))
    (h : ∀ st, Ev Q { s with
      regs := ((s.regs.set64 .rax (s.regs.rax.toBitVec * s.regs.get64 r)).set64 .rdx
        (BinOp.mulhi.eval s.regs.rax (UInt64.ofBitVec (s.regs.get64 r))).toBitVec),
      status := st } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  intro _ _ _ _
  simp only [show (Width.W64 == Width.W8) = false from rfl, Bool.false_eq_true, ite_false]
  refine ev_flags h ?_
  congr 1
  · simp only [BinOp.eval, Width.bits, Reg64s.get64_rax, BitVec.unsigned,
      UInt64.toNat_toBitVec, UInt64.toNat_ofBitVec]
    rw [show ((s.regs.rax.toNat : Int) * ((s.regs.get64 r).toNat : Int)) =
        ((s.regs.rax.toNat * (s.regs.get64 r).toNat : Nat) : Int) by push_cast; rfl, Int.shiftRight_eq_div_pow]
    apply BitVec.eq_of_toNat_eq
    simp
    omega

/-- `shr r, n` with an immediate count. -/
theorem ev_shrRI {n : Nat} (hn : n < 64) {r : Reg64}
    (hk : Host.prog[k]? = some (i64 (.shr (.reg (rr r)) (.imm8 (.int64 (Int64.ofInt n))))))
    (h : ∀ st, Ev Q { s with regs := s.regs.set64 r ((UInt64.ofBitVec (s.regs.get64 r)) >>> (UInt64.ofNat n)).toBitVec, status := st } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  rw [imm8_count hn]
  split
  · simp only [Effects.All]
    refine ev_flags h ?_
    simp_all [UInt64.toBitVec_shiftRight, Nat.mod_eq_of_lt hn]
  · simp only [Effects.All]
    intro af
    (try split) <;> (try split) <;> simp only [Effects.All] <;> intros <;>
      (refine ev_flags h ?_
       simp_all [UInt64.toBitVec_shiftRight, Nat.mod_eq_of_lt hn])

/-- `mov d, [b + 8 i]`. -/
theorem ev_ldS {d b i : Reg64} (hk : Host.prog[k]? = some (movRM d (mbi b i .W64)))
    {v : Word} (hv : rdW s.dmem (s.regs.get64 b + s.regs.get64 i * 8) = some v)
    (h : Ev Q { s with regs := s.regs.set64 d v.toBitVec } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  rw [addr_sib8]
  simp only [rdW, Option.map_eq_some_iff] at hv
  obtain ⟨j, hj, rfl⟩ := hv
  simp only [hj, Effects.All]
  simpa using h

/-- `mov [b + 8 i], r`. -/
theorem ev_stS {b i r : Reg64} (hk : Host.prog[k]? = some (movMR (mbi b i .W64) r))
    (hm : (rdW s.dmem (s.regs.get64 b + s.regs.get64 i * 8)).isSome)
    (h : Ev Q { s with dmem := wrW s.dmem (s.regs.get64 b + s.regs.get64 i * 8) (s.regs.get64 r) }
      (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  rw [addr_sib8]
  simp only [rdW, Option.isSome_map] at hm
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hm
  simp only [hj, Effects.All]
  exact h

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

omit [Host] in
theorem addr_sib8' [Labels] (b i : Reg64) (regs : Reg64s) (rng : Std.Rco Int64) :
    ((AddrExpr.interp (address_size := .mk .W64) (a := mbi b i .W64) regs rng).zeroExtend 64)
      = regs.get64 b + regs.get64 i * 8 := addr_sib8 b i regs rng

/-- `lea d, [b + 8 i]`. -/
theorem ev_leaS {d b i : Reg64} (hk : Host.prog[k]? = some (i64 (.lea (rr d) (mbi b i .W64))))
    (h : Ev Q { s with regs := s.regs.set64 d (s.regs.get64 b + s.regs.get64 i * 8) } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  rw [addr_sib8]
  exact h

end

end L.Compiler
