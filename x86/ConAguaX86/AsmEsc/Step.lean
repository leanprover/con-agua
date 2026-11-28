module

public import ConAguaX86.Compiler.Step
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


omit [Host] in
set_option linter.unusedSimpArgs false in
/-- `shld`'s value: the top half of `(a ++ b) << c`. -/
theorem shld_val (a b : BitVec 64) (c : Nat) (_hc0 : c ≠ 0) (hc : c < 64) :
    BitVec.setWidth 64 (((a.append b) <<< c).drop 64) = (a <<< c) ||| (b >>> (64 - c)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.drop, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight]
  by_cases h1 : i < c <;> simp [h1, hi] <;> (try split) <;> simp_all <;> (try omega)
  all_goals
    rw [BitVec.getLsbD_append]
    split
  all_goals first
    | omega
    | (try (have e1 : 64 + i < 128 := by omega
            simp only [e1, decide_true, Bool.true_and]))
      (try (have e2 : ¬ 64 + i < c := by omega
            simp only [e2, decide_false, Bool.not_false, Bool.true_and]))
      (try rw [BitVec.getLsbD_of_ge a (c + i) (by omega), Bool.false_or])
      (try rw [BitVec.getLsbD_of_ge b (64 - c + i) (by omega), Bool.or_false])
      (try rw [BitVec.getLsbD_of_ge b (i - (64 - c)) (by omega)])
      first | rfl | (congr 1; omega) | (simp only [Bool.or_eq_left_iff_imp]; intro; trivial) | skip

omit [Host] in
set_option linter.unusedSimpArgs false in
/-- `shrd`'s value: the bottom half of `(b ++ a) >> c`. -/
theorem shrd_val (a b : BitVec 64) (c : Nat) (_hc0 : c ≠ 0) (hc : c < 64) :
    BitVec.setWidth 64 (((b.append a) >>> c).take 64) = (a >>> c) ||| (b <<< (64 - c)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.take, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight]
  by_cases h1 : i < 64 - c <;> simp [h1, hi] <;> (try split) <;> simp_all <;> (try omega)
  all_goals
    rw [BitVec.getLsbD_append]
    split
  all_goals first
    | omega
    | (try (have e1 : 64 + i < 128 := by omega
            simp only [e1, decide_true, Bool.true_and]))
      (try (have e2 : ¬ 64 + i < c := by omega
            simp only [e2, decide_false, Bool.not_false, Bool.true_and]))
      (try rw [BitVec.getLsbD_of_ge a (c + i) (by omega), Bool.false_or])
      (try rw [BitVec.getLsbD_of_ge b (64 - c + i) (by omega), Bool.or_false])
      (try rw [BitVec.getLsbD_of_ge b (i - (64 - c)) (by omega)])
      first | rfl | (congr 1; omega) | (simp only [Bool.or_eq_left_iff_imp]; intro; trivial) | skip

omit [Host] in
theorem cl_count (s : MachineData) :
    (s.regs.rcx.toBitVec.take 8).toNat &&& 63 = s.regs.rcx.toNat % 64 := by
  rw [show (63 : Nat) = 2 ^ 6 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp only [BitVec.take, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  show s.regs.rcx.toNat % 2 ^ 8 % 2 ^ 6 = s.regs.rcx.toNat % 64
  omega

/-- The double left shift by `c` (mod 64): `a`'s bits move up, `b`'s top bits fill in; `a` for `c = 0`. -/
def dshl (a b c : Word) : Word := if c.toNat % 64 = 0 then a else (a <<< c) ||| (b >>> (64 - c % 64))

/-- The double right shift by `c` (mod 64): `a`'s bits move down, `b`'s low bits fill in; `a` for
`c = 0`. -/
def dshr (a b c : Word) : Word := if c.toNat % 64 = 0 then a else (a >>> c) ||| (b <<< (64 - c % 64))

/-- `shld d, r, cl`. -/
theorem ev_shldCl {d r : Reg64} (hk : Host.prog[k]? = some (i64 (.shld (.reg (rr d)) (rr r) .cl)))
    (h : ∀ st : StatusFlags, Ev Q { s with
        regs := s.regs.set64 d (dshl (UInt64.ofBitVec (s.regs.get64 d)) (UInt64.ofBitVec (s.regs.get64 r))
          s.regs.rcx).toBitVec,
        status := st } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  simp only [Reg.interp, Reg64s.get_low_W64, ShiftCountExpr.interpMasked, ShiftCountExpr.interp]
  rw [cl_count]
  have hc := Nat.mod_lt s.regs.rcx.toNat (by decide : 0 < 64)
  have hv : ∀ c : Nat, c ≠ 0 → c = s.regs.rcx.toNat % 64 →
      BitVec.setWidth 64 (((s.regs.get64 d).append (s.regs.get64 r) <<< c).drop 64) =
        (dshl (UInt64.ofBitVec (s.regs.get64 d)) (UInt64.ofBitVec (s.regs.get64 r)) s.regs.rcx).toBitVec := by
    intro c hc0 hcv
    rw [shld_val _ _ c hc0 (by omega)]
    simp only [dshl, ← hcv, hc0, reduceIte, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft,
      UInt64.toBitVec_shiftRight]
    rw [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq']
    have e1 : (s.regs.rcx.toBitVec % 64).toNat = c := by
      rw [BitVec.toNat_umod]; simp only [UInt64.toNat_toBitVec]; exact hcv.symm
    have e2 : ((64 - s.regs.rcx % 64).toBitVec % 64).toNat = 64 - c := by
      rw [BitVec.toNat_umod, UInt64.toNat_toBitVec, UInt64.toNat_sub_of_le _ _ (by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]; simp; omega), UInt64.toNat_mod]
      have e64 : (64 : BitVec 64).toNat = 64 := rfl
      simp only [UInt64.reduceToNat, e64]
      omega
    rw [e1, e2]
  by_cases h0 : s.regs.rcx.toNat % 64 = 0
  · simp only [h0, beq_self_eq_true, reduceIte]
    refine ev_flags (fun st => (h st)) ?_
    simp only [dshl, h0, reduceIte]
  · have hgt : ¬ s.regs.rcx.toNat % 64 > 64 := by omega
    simp only [Width.bits, hgt, reduceIte]
    simp only [show (s.regs.rcx.toNat % 64 == 0) = false from by simp [h0], Bool.false_eq_true, reduceIte]
    intro af
    (try split) <;> simp only [Effects.All] <;> intros <;> (refine ev_flags h ?_) <;>
      rw [hv _ h0 rfl]

/-- `shrd d, r, cl`. -/
theorem ev_shrdCl {d r : Reg64} (hk : Host.prog[k]? = some (i64 (.shrd (.reg (rr d)) (rr r) .cl)))
    (h : ∀ st : StatusFlags, Ev Q { s with
        regs := s.regs.set64 d (dshr (UInt64.ofBitVec (s.regs.get64 d)) (UInt64.ofBitVec (s.regs.get64 r))
          s.regs.rcx).toBitVec,
        status := st } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  simp only [Reg.interp, Reg64s.get_low_W64, ShiftCountExpr.interpMasked, ShiftCountExpr.interp]
  rw [cl_count]
  have hc := Nat.mod_lt s.regs.rcx.toNat (by decide : 0 < 64)
  have hv : ∀ c : Nat, c ≠ 0 → c = s.regs.rcx.toNat % 64 →
      BitVec.setWidth 64 (((s.regs.get64 r).append (s.regs.get64 d) >>> c).take 64) =
        (dshr (UInt64.ofBitVec (s.regs.get64 d)) (UInt64.ofBitVec (s.regs.get64 r)) s.regs.rcx).toBitVec := by
    intro c hc0 hcv
    rw [shrd_val _ _ c hc0 (by omega)]
    simp only [dshr, ← hcv, hc0, reduceIte, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft,
      UInt64.toBitVec_shiftRight]
    rw [BitVec.ushiftRight_eq', BitVec.shiftLeft_eq']
    have e1 : (s.regs.rcx.toBitVec % 64).toNat = c := by
      rw [BitVec.toNat_umod]; simp only [UInt64.toNat_toBitVec]; exact hcv.symm
    have e2 : ((64 - s.regs.rcx % 64).toBitVec % 64).toNat = 64 - c := by
      rw [BitVec.toNat_umod, UInt64.toNat_toBitVec, UInt64.toNat_sub_of_le _ _ (by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]; simp; omega), UInt64.toNat_mod]
      have e64 : (64 : BitVec 64).toNat = 64 := rfl
      simp only [UInt64.reduceToNat, e64]
      omega
    rw [e1, e2]
  by_cases h0 : s.regs.rcx.toNat % 64 = 0
  · simp only [h0, beq_self_eq_true, reduceIte]
    refine ev_flags (fun st => (h st)) ?_
    simp only [dshr, h0, reduceIte]
  · have hgt : ¬ s.regs.rcx.toNat % 64 > 64 := by omega
    simp only [Width.bits, hgt, reduceIte]
    simp only [show (s.regs.rcx.toNat % 64 == 0) = false from by simp [h0], Bool.false_eq_true, reduceIte]
    intro af
    (try split) <;> simp only [Effects.All] <;> intros <;> (refine ev_flags h ?_) <;>
      rw [hv _ h0 rfl]

/-- `shl d, cl` (UInt64's shift is mod 64, as the masked count; a zero count keeps `d`). -/
theorem ev_shlCl {d : Reg64} (hk : Host.prog[k]? = some (i64 (.shl (.reg (rr d)) .cl)))
    (h : ∀ st : StatusFlags, Ev Q { s with
        regs := s.regs.set64 d (UInt64.ofBitVec (s.regs.get64 d) <<< s.regs.rcx).toBitVec,
        status := st } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  simp only [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, cl_count]
  have hv : (UInt64.ofBitVec (s.regs.get64 d) <<< s.regs.rcx).toBitVec = s.regs.get64 d <<< (s.regs.rcx.toNat % 64) := by
    rw [UInt64.toBitVec_shiftLeft, BitVec.shiftLeft_eq', BitVec.toNat_umod]
    rfl
  split
  · rename_i h0
    simp only [beq_iff_eq] at h0
    refine ev_flags h ?_
    rw [hv, h0, BitVec.shiftLeft_zero]
  · intro af
    (try split) <;> (try split) <;> simp only [Effects.All] <;> intros <;> (refine ev_flags h ?_) <;> (rw [hv]; try rfl)

/-- `shr d, cl`. -/
theorem ev_shrCl {d : Reg64} (hk : Host.prog[k]? = some (i64 (.shr (.reg (rr d)) .cl)))
    (h : ∀ st : StatusFlags, Ev Q { s with
        regs := s.regs.set64 d (UInt64.ofBitVec (s.regs.get64 d) >>> s.regs.rcx).toBitVec,
        status := st } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  simp only [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, cl_count]
  have hv : (UInt64.ofBitVec (s.regs.get64 d) >>> s.regs.rcx).toBitVec = s.regs.get64 d >>> (s.regs.rcx.toNat % 64) := by
    rw [UInt64.toBitVec_shiftRight, BitVec.ushiftRight_eq', BitVec.toNat_umod]
    rfl
  split
  · rename_i h0
    simp only [beq_iff_eq] at h0
    refine ev_flags h ?_
    rw [hv, h0, BitVec.ushiftRight_zero]
  · intro af
    (try split) <;> (try split) <;> simp only [Effects.All] <;> intros <;> (refine ev_flags h ?_) <;> (rw [hv]; try rfl)

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
