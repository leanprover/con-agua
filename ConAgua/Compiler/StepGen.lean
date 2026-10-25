module

public import ConAgua.Compiler.Rel

@[expose] public section

/-!
# One instruction at a time: the forms of the register-stack code generator

The instruction forms `gen` (lane leafgen, step G2, `Compile.lean`) emits, for any registers:
`Step.lean`'s lemmas for the forms the expression compiler emits with `rax`, `rcx`, `rdx`.
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

/-! ### The register-stack code generator (lane leafgen, step G2): any registers -/

/-- The address `m` (`[b + off]`, or a tiered descriptor word `[r15 + 8 r + off]`) holds the
mapped word `v`. -/
def MemW (s : MachineData) (m : AddrExpr) (v : Word) : Prop :=
  (∃ b off, m = mb b off ∧ SmallOff off ∧ rdW s.dmem (A ((s.regs.get64 b).toNat + off.toNat)) = some v) ∨
  (∃ r off, m = tdesc r off ∧ SmallOff off ∧
    rdW s.dmem (A (s.regs.r15.toNat + 8 * (s.regs.get64 r).toNat + off.toNat)) = some v)

/-- `cmp r, [r15 + 8 t + off]`, any register `r`. -/
theorem ev_cmpRMt' {r t : Reg64} {off : Int} (hk : Host.prog[k]? = some (i64 (.cmp (.reg (rr r)) (oM (tdesc t off)))))
    (hoff : SmallOff off) {v : Word}
    (hv : rdW s.dmem (A (s.regs.r15.toNat + 8 * (s.regs.get64 t).toNat + off.toNat)) = some v)
    (h : Ev Q { s with status := cmpFlags (s.regs.get64 r) v.toBitVec } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  rw [AddrExpr.zeroExtend_interp_sib, addr_tdesc _ _ _ hoff.1 (by omega)]
  simp only [rdW, Option.map_eq_some_iff] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  simp only [Reg64s.get64_r15, UInt64.toNat_toBitVec, hi, Effects.All]
  exact h

/-- `cmp [r15 + 8 t + off], imm`. -/
theorem ev_cmpMtI {t : Reg64} {off : Int} {i : Int} (hk : Host.prog[k]? = some (i64 (.cmp (.mem (tdesc t off)) (oI i))))
    (hoff : SmallOff off) {v : Word}
    (hv : rdW s.dmem (A (s.regs.r15.toNat + 8 * (s.regs.get64 t).toNat + off.toNat)) = some v)
    (h : Ev Q { s with status := cmpFlags v.toBitVec (Int64.ofInt i).toBitVec } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  rw [AddrExpr.zeroExtend_interp_sib, addr_tdesc _ _ _ hoff.1 (by omega)]
  simp only [rdW, Option.map_eq_some_iff] at hv
  obtain ⟨j, hj, rfl⟩ := hv
  simp only [Reg64s.get64_r15, UInt64.toNat_toBitVec, hj, Effects.All, Width.bits,
    BitVec.truncate_eq_setWidth, BitVec.setWidth_eq]
  exact h

/-- `cmp r, imm`, any register. -/
theorem ev_cmpRIg {r : Reg64} {i : Int} (hk : Host.prog[k]? = some (i64 (.cmp (.reg (rr r)) (oI i))))
    (h : Ev Q { s with status := cmpFlags (s.regs.get64 r) (Int64.ofInt i).toBitVec } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  simp only [Width.bits, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq]
  exact h

/-- `mov d, [m]`. -/
theorem ev_movRA {d : Reg64} {m : AddrExpr} (hk : Host.prog[k]? = some (movRM d m)) {v : Word}
    (hv : MemW s m v) (h : Ev Q { s with regs := s.regs.set64 d v.toBitVec } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  rcases hv with ⟨b, off, rfl, hoff, hv⟩ | ⟨r, off, rfl, hoff, hv⟩
  · exact ev_movRM hk hoff hv h
  · exact ev_movRMt hk hoff hv h

/-- `cmp r, [m]`. -/
theorem ev_cmpRA {r : Reg64} {m : AddrExpr} (hk : Host.prog[k]? = some (i64 (.cmp (.reg (rr r)) (oM m))))
    {v : Word} (hv : MemW s m v)
    (h : Ev Q { s with status := cmpFlags (s.regs.get64 r) v.toBitVec } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  rcases hv with ⟨b, off, rfl, hoff, hv⟩ | ⟨t, off, rfl, hoff, hv⟩
  · exact ev_cmpRO hk (.inr (.inl ⟨b, off, rfl, hoff, hv⟩)) h
  · exact ev_cmpRMt' hk hoff hv h

/-- `cmp [m], imm`. -/
theorem ev_cmpAI {m : AddrExpr} {i : Int} (hk : Host.prog[k]? = some (i64 (.cmp (.mem m) (oI i))))
    {v : Word} (hv : MemW s m v)
    (h : Ev Q { s with status := cmpFlags v.toBitVec (Int64.ofInt i).toBitVec } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  rcases hv with ⟨b, off, rfl, hoff, hv⟩ | ⟨t, off, rfl, hoff, hv⟩
  · exact ev_cmpG (va := v) (vb := Int64.ofInt i |>.toUInt64) hk (.inr (.inl ⟨b, off, rfl, hoff, hv⟩))
      (.inl (by simp)) (by simpa using h)
  · exact ev_cmpMtI hk hoff hv h

/-- `d := d op o` (`aluOp`). -/
theorem ev_aluOp {op : BinOp} {d : Reg64} {o : Operand .W64} {i : Directive} {v : Word}
    (hd : aluOp op d o = some i) (hk : Host.prog[k]? = some i) (hr : OpReads s o v)
    (h : ∀ st, Ev Q { s with regs := s.regs.set64 d (op.eval (UInt64.ofBitVec (s.regs.get64 d)) v).toBitVec, status := st }
      (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  rcases hr with rfl | ⟨b, off, rfl, hoff, hv⟩ | ⟨r, rfl, hv⟩
  · cases op <;> simp only [aluOp, aluDirect, Option.some.injEq, reduceCtorEq] at hd <;> subst hd <;> run_instr <;>
      (intros; refine ev_flags h ?_; simp [BinOp.eval, BitVec.add_comm])
  · simp only [rdW, Option.map_eq_some_iff] at hv
    obtain ⟨j, hj, rfl⟩ := hv
    cases op <;> simp only [aluOp, aluDirect, Option.some.injEq, reduceCtorEq] at hd <;> subst hd <;> run_instr <;>
      (rw [addr_disp _ _ hoff.1 (by omega)]; simp only [hj, Effects.All]
       intros; refine ev_flags h ?_; simp [BinOp.eval, BitVec.add_comm])
  · cases op <;> simp only [aluOp, aluDirect, Option.some.injEq, reduceCtorEq] at hd <;> subst hd <;> run_instr <;>
      (intros; refine ev_flags h ?_; simp [BinOp.eval, BitVec.add_comm, hv])

/-- `shl/shr r, n` with an immediate count, any register. -/
theorem ev_shiftR {n : Nat} (hn : n < 64) {op : BinOp} (hop : op = .shl ∨ op = .shr) {r : Reg64}
    (hk : Host.prog[k]? = some (match op with
      | .shl => i64 (.shl (.reg (rr r)) (.imm8 (.int64 (Int64.ofInt n))))
      | _ => i64 (.shr (.reg (rr r)) (.imm8 (.int64 (Int64.ofInt n))))))
    (h : ∀ st, Ev Q { s with regs := s.regs.set64 r (op.eval (UInt64.ofBitVec (s.regs.get64 r)) (UInt64.ofNat n)).toBitVec, status := st }
      (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  rcases hop with rfl | rfl <;> simp only at hk <;> run_instr <;> rw [imm8_count hn] <;>
    (split
     · simp only [Effects.All]
       refine ev_flags h ?_
       simp_all [BinOp.eval, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight, Nat.mod_eq_of_lt hn]
     · simp only [Effects.All]
       intro af
       (try split) <;> (try split) <;> simp only [Effects.All] <;> intros <;>
         (refine ev_flags h ?_
          simp_all [BinOp.eval, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight, Nat.mod_eq_of_lt hn]))

/-- `lea d, [b + off]` with a signed 32-bit offset. -/
theorem ev_leaS {d b : Reg64} {off : Int} (hk : Host.prog[k]? = some (i64 (.lea (rr d) (mb b off))))
    (h : Ev Q { s with regs := s.regs.set64 d (s.regs.get64 b + BitVec.ofInt 64 (Int64.ofInt off).toInt) } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  exact h

/-- `lea d, [b + i]`. -/
theorem ev_leaRR {d b i : Reg64} (hk : Host.prog[k]? = some (i64 (.lea (rr d) (mbi b i .W8))))
    (h : Ev Q { s with regs := s.regs.set64 d (s.regs.get64 b + s.regs.get64 i) } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  rw [addr_sib1]
  exact h

/-- `mov d, [b + 8 i]`, any registers. -/
theorem ev_ldX {d b i : Reg64} (hk : Host.prog[k]? = some (movRM d (mbi b i .W64)))
    {v : Word} (hv : rdW s.dmem (s.regs.get64 b + s.regs.get64 i * 8) = some v)
    (h : Ev Q { s with regs := s.regs.set64 d v.toBitVec } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  rw [addr_sib8]
  simp only [rdW, Option.map_eq_some_iff] at hv
  obtain ⟨j, hj, rfl⟩ := hv
  simp only [hj, Effects.All]
  simpa using h

/-- `movzx d, byte [b + i]`, any registers. -/
theorem ev_movzxX {d b i : Reg64} (hk : Host.prog[k]? = some
      (i64 (.movzx (.reg (rr d)) (w' := .W8) (.mem (mbi b i .W8)))))
    {v : UInt8} (hv : s.dmem.get? (s.regs.get64 b + s.regs.get64 i) = some v)
    (h : Ev Q { s with regs := s.regs.set64 d (v.toUInt64.toBitVec) } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  rw [addr_sib1]
  simp only [loadInt_one_of hv, Effects.All]
  refine ev_of_regs h ?_
  congr 1; apply BitVec.eq_of_toNat_eq; simp

/-- `mul t`: `rdx:rax := rax * t`. -/
theorem ev_mulR {t : Reg64} (hk : Host.prog[k]? = some (i64 (.mul (.reg (rr t)))))
    (h : ∀ st, Ev Q { s with
      regs := ((s.regs.set64 .rax (s.regs.rax * UInt64.ofBitVec (s.regs.get64 t)).toBitVec).set64 .rdx
        (BinOp.mulhi.eval s.regs.rax (UInt64.ofBitVec (s.regs.get64 t))).toBitVec),
      status := st } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  intro _ _ _ _
  simp only [show (Width.W64 == Width.W8) = false from rfl, Bool.false_eq_true, ite_false]
  refine ev_flags h ?_
  congr 1
  simp only [BinOp.eval, Width.bits, Reg64s.get64_rax, BitVec.unsigned, UInt64.toNat_toBitVec,
    UInt64.toNat_ofBitVec]
  rw [show ((s.regs.rax.toNat : Int) * ((s.regs.get64 t).toNat : Int)) =
      ((s.regs.rax.toNat * (s.regs.get64 t).toNat : Nat) : Int) by push_cast; rfl, Int.shiftRight_eq_div_pow]
  apply BitVec.eq_of_toNat_eq
  simp
  omega

/-- `setcc d8; movzx d, d8`: `d := cc`. -/
theorem ev_setcc {cc : CondCode} {d : Reg64} (hk : Host.prog[k]? = some (i8 (.setcc cc (.reg (.low d .W8)))))
    (hk' : Host.prog[k + 1]? = some (i64 (.movzx (.reg (rr d)) (w' := .W8) (.reg (.low d .W8)))))
    (h : Ev Q { s with regs := s.regs.set64 d (if cc.interp s.status then (1 : Word) else 0).toBitVec }
      (at_ (k + 1 + 1))) :
    Ev Q s (at_ k) := by
  refine ev_instr hk (by rintro ⟨⟩) ?_
  simp only [Instr.interp, Operation.interp, MachineData.set, RegOrMem.interp, Effects.All]
  refine ev_instr hk' (by rintro ⟨⟩) ?_
  simp only [Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp, MachineData.setReg,
    Reg64s.set_low_W64, Effects.All]
  refine ev_of_regs h ?_
  simp only [Reg64s.set_low_W8, Reg64s.get_low_W8, rget_set, ite_true, Reg64s.set_low_W64,
    BitVec.take_replaceLow_8]
  rw [show ∀ (R : Reg64s) (a b : BitVec 64), (R.set64 d a).set64 d b = R.set64 d b from
    fun R a b => by cases d <;> rfl]
  congr 1
  cases cc.interp s.status <;> decide

end

end L.Compiler
