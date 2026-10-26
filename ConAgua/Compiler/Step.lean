module

public import ConAgua.Compiler.Compile
public import ConAgua.Compiler.Mem
public import Kraken.X64.WP.Basic
public import Kraken.X64.Registers

@[expose] public section

/-!
# One instruction at a time

The compiler proof is a forward simulation on Kraken's own judgment
`Eventually (step1 Host.exe) Q ⟨d, pc⟩` ("every run from `d` at `pc` reaches `Q`"), for an
arbitrary `Host` program that contains the compiled code. Each lemma here steps over one
instruction form the compiler emits, in continuation-passing style: the hypothesis is the
`Eventually` at the next state, the conclusion the `Eventually` at this one.
-/

namespace L.Compiler

variable [Host]

/-- Every run from `d` at `pc` reaches `Q`. -/
abbrev Ev (Q : MachineState → Prop) (d : MachineData) (pc : Int64) : Prop :=
  Eventually (step1 Host.exe) Q ⟨d, pc⟩

/-- The code `c` sits at index `k` of the host program. -/
abbrev Code (c : Program) (k : Nat) : Prop := c.IsInfixAt Host.prog k

/-- The address of directive `k`. -/
abbrev at_ (k : Nat) : Int64 := Host.addrOf k

theorem Code.app {a b : Program} {k : Nat} (h : Code (a ++ b) k) : Code a k ∧ Code b (k + a.length) :=
  List.IsInfixAt.append h

theorem Code.left {a b : Program} {k : Nat} (h : Code (a ++ b) k) : Code a k := h.app.1
theorem Code.right {a b : Program} {k : Nat} (h : Code (a ++ b) k) : Code b (k + a.length) := h.app.2

theorem Code.get {c : Program} {k i : Nat} {x : Directive} (h : Code c k) (hi : c[i]? = some x) :
    Host.prog[k + i]? = some x := by
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  exact List.isInfixAt_iff_getElem?.mp h i hlt

theorem Code.head {x : Directive} {c : Program} {k : Nat} (h : Code (x :: c) k) : Host.prog[k]? = some x :=
  (List.IsInfixAt.cons h).1

theorem Code.tail {x : Directive} {c : Program} {k : Nat} (h : Code (x :: c) k) : Code c (k + 1) :=
  (List.IsInfixAt.cons h).2

theorem Code.label {c : Program} {k i : Nat} {l : Label} (h : Code c k) (hi : c[i]? = some (.label l)) :
    label l = at_ (k + i) :=
  Host.label_eq h hi

theorem ev_congr {Q : MachineState → Prop} {d : MachineData} {j k : Nat} (h : Ev Q d (at_ j)) (hjk : j = k) :
    Ev Q d (at_ k) := hjk ▸ h

theorem ev_instr {k : Nat} {i : Instr} (hk : Host.prog[k]? = some (.instr i)) (hpad : ¬ i.IsPadding)
    {s : MachineData} {Q : MachineState → Prop}
    (h : (i.interp s ⟨at_ k, at_ (k + 1)⟩ (fun s' => .done ⟨s', at_ (k + 1)⟩)
      (fun a s' => .done ⟨s', a⟩)).All (Eventually (step1 Host.exe) Q)) :
    Ev Q s (at_ k) :=
  Eventually.step _ _ (Host.step1_addrOf (c := ⟨.instr i, Kraken.Layout.size Directive k⟩)
    (by rw [Host.exe_getElem?, hk]; rfl) (Host.instr_size_pos _ _ hk hpad) h) (fun _ h => h)

theorem ev_label {k : Nat} {l : Label} (hk : Host.prog[k]? = some (.label l)) {s : MachineData}
    {Q : MachineState → Prop} (h : Ev Q s (at_ (k + 1))) : Ev Q s (at_ k) := by
  have : at_ (k + 1) = at_ k := by
    rw [at_, Host.addrOf_succ hk, Host.label_size _ _ hk]; simp
  rwa [this] at h

/-! ## Addresses -/

omit [Host] in
theorem addr_disp (x : BitVec 64) (off : Int) (h0 : 0 ≤ off) (h1 : off < 2 ^ 63) :
    x + BitVec.ofInt 64 (Int64.ofInt off).toInt = A (x.toNat + off.toNat) := by
  have : (Int64.ofInt off).toInt = off := by
    simp only [Int64.toInt_ofInt]; rw [Int.bmod_eq_of_le] <;> simp [Int64.size] <;> omega
  rw [this]
  apply BitVec.eq_of_toNat_eq
  simp [A, BitVec.toNat_add, BitVec.toNat_ofInt]
  omega

/-- A displacement the compiler emits: a natural number below `2^31`. -/
abbrev SmallOff (off : Int) : Prop := 0 ≤ off ∧ off < 2 ^ 31

/-! ## Register moves and arithmetic -/

section
variable {k : Nat} {s : MachineData} {Q : MachineState → Prop}

local macro "run_instr" : tactic =>
  `(tactic| (refine ev_instr (by assumption) (by rintro ⟨⟩) ?_;
             simp only [Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
               RelRegOrMem.interp, ConstExpr.interp, MachineData.load, MachineData.store,
               MachineData.set, MachineData.setReg, Reg64s.set_low_W64, Reg64s.get_low_W64,
               AddrExpr.zeroExtend_interp_base_disp, Width.bytes, Effects.All]))

theorem ev_movRI {r : Reg64} {w : Word} (hk : Host.prog[k]? = some (movRI r w))
    (h : Ev Q { s with regs := s.regs.set64 r w.toBitVec } (at_ (k + 1))) : Ev Q s (at_ k) := by
  run_instr
  simpa using h

theorem ev_movRR {d r : Reg64} (hk : Host.prog[k]? = some (movRR d r))
    (h : Ev Q { s with regs := s.regs.set64 d (s.regs.get64 r) } (at_ (k + 1))) : Ev Q s (at_ k) := by
  run_instr
  exact h

theorem ev_movRM {d b : Reg64} {off : Int} (hk : Host.prog[k]? = some (movRM d (mb b off)))
    (hoff : SmallOff off) {v : Word} (hv : rdW s.dmem (A ((s.regs.get64 b).toNat + off.toNat)) = some v)
    (h : Ev Q { s with regs := s.regs.set64 d v.toBitVec } (at_ (k + 1))) : Ev Q s (at_ k) := by
  run_instr
  rw [addr_disp _ _ hoff.1 (by omega)]
  simp only [rdW, Option.map_eq_some_iff] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  simp only [hi, Effects.All]
  simpa using h

theorem ev_movMR {b r : Reg64} {off : Int} (hk : Host.prog[k]? = some (movMR (mb b off) r))
    (hoff : SmallOff off) (hm : (rdW s.dmem (A ((s.regs.get64 b).toNat + off.toNat))).isSome)
    (h : Ev Q { s with dmem := wrW s.dmem (A ((s.regs.get64 b).toNat + off.toNat)) (s.regs.get64 r) }
      (at_ (k + 1))) : Ev Q s (at_ k) := by
  run_instr
  rw [addr_disp _ _ hoff.1 (by omega)]
  simp only [rdW, Option.isSome_map] at hm
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hm
  simp only [hi, Effects.All]
  exact h

omit [Host] in
theorem shift_count (c : UInt64) : (c.toBitVec.take 8).toNat &&& 0x3f = c.toNat % 64 := by
  simp only [BitVec.take, BitVec.extractLsb', Nat.shiftRight_zero, UInt64.toNat_toBitVec,
    BitVec.toNat_ofNat]
  rw [show (0x3f : Nat) = 2 ^ 6 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem ev_of_regs {z : RegZmms} {d : DataMem} {pc : Int64} {R R' : Reg64s} {S : StatusFlags}
    (h : Ev Q ⟨R, z, S, d⟩ pc) (hR : R = R') : Ev Q ⟨R', z, S, d⟩ pc := hR ▸ h

/-- Close a goal whose flags are anything: the continuation takes all flags. -/
theorem ev_flags {z : RegZmms} {d : DataMem} {pc : Int64} {R R' : Reg64s}
    {S : StatusFlags} (h : ∀ st, Ev Q ⟨R, z, st, d⟩ pc) (hR : R = R') : Ev Q ⟨R', z, S, d⟩ pc :=
  hR ▸ h S

theorem ev_bin {op : BinOp} (hop : op ≠ .mulhi) (hk : Host.prog[k]? = some (binInstr op))
    (h : ∀ st, Ev Q { s with regs := s.regs.set64 .rax (op.eval s.regs.rax s.regs.rcx).toBitVec, status := st } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  cases op <;> simp only [binInstr] at hk
  case mulhi => exact absurd rfl hop
  all_goals run_instr
  case shl | shr =>
    simp only [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, shift_count]
    split
    · simp only [Effects.All]
      refine ev_flags h ?_
      simp_all [BinOp.eval, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight]
    · simp only [Effects.All]
      intro af
      split <;> split <;> simp only [Effects.All] <;> intros <;>
        (refine ev_flags h ?_
         simp_all [BinOp.eval, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight])
  all_goals intros <;>
    (refine ev_flags h ?_
     simp_all [BinOp.eval, BitVec.add_comm])

/-- `mul rcx`: `rdx:rax := rax * rcx`, unsigned. -/
theorem ev_mul (hk : Host.prog[k]? = some (binInstr .mulhi))
    (h : ∀ st, Ev Q { s with
      regs := ((s.regs.set64 .rax (s.regs.rax * s.regs.rcx).toBitVec).set64 .rdx
        (BinOp.mulhi.eval s.regs.rax s.regs.rcx).toBitVec),
      status := st } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  simp only [binInstr] at hk
  run_instr
  intro _ _ _ _
  simp only [show (Width.W64 == Width.W8) = false from rfl, Bool.false_eq_true, ite_false]
  refine ev_flags h ?_
  congr 1
  simp only [BinOp.eval, Width.bits, Reg64s.get64_rax, Reg64s.get64_rcx, BitVec.unsigned,
      UInt64.toNat_toBitVec]
  rw [show ((s.regs.rax.toNat : Int) * (s.regs.rcx.toNat : Int)) =
      ((s.regs.rax.toNat * s.regs.rcx.toNat : Nat) : Int) by push_cast; rfl, Int.shiftRight_eq_div_pow]
  apply BitVec.eq_of_toNat_eq
  simp
  omega

/-- `cmovcc rax, rdx`. -/
theorem ev_cmov {cc : CondCode} (hk : Host.prog[k]? = some (i64 (.cmovcc cc (rr .rax) (.reg (rr .rdx)))))
    (h : Ev Q { s with regs := s.regs.set64 .rax (if cc.interp s.status then s.regs.rdx else s.regs.rax).toBitVec }
      (at_ (k + 1))) : Ev Q s (at_ k) := by
  run_instr
  refine ev_of_regs h ?_
  congr 1
  split <;> simp_all

/-- The flags of `cmp a, b`. -/
def cmpFlags (a b : BitVec 64) : StatusFlags :=
  StatusFlags.from_result (a - b)
    { cf := BitVec.unsigned (a - b) != a.unsigned - b.unsigned,
      af := (BitVec.take (a - b) 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
      of := BitVec.signed (a - b) != a.signed - b.signed }

theorem ev_cmpRR (hk : Host.prog[k]? = some (i64 (.cmp (.reg (rr .rax)) (oR .rcx))))
    (h : Ev Q { s with status := cmpFlags s.regs.rax.toBitVec s.regs.rcx.toBitVec } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  exact h

theorem ev_cmpRM {off : Int} (hk : Host.prog[k]? = some (i64 (.cmp (.reg (rr .rax)) (oM (mb .r15 off)))))
    (hoff : SmallOff off) {v : Word} (hv : rdW s.dmem (A (s.regs.r15.toNat + off.toNat)) = some v)
    (h : Ev Q { s with status := cmpFlags s.regs.rax.toBitVec v.toBitVec } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  rw [Reg64s.get64_r15, addr_disp _ _ hoff.1 (by omega)]
  simp only [rdW, Option.map_eq_some_iff] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  simp only [UInt64.toNat_toBitVec, hi, Effects.All]
  exact h

theorem ev_cmpRI {i : Int} (hk : Host.prog[k]? = some (i64 (.cmp (.reg (rr .rax)) (oI i))))
    (h : Ev Q { s with status := cmpFlags s.regs.rax.toBitVec (Int64.ofInt i).toBitVec } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  simp only [Width.bits, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq]
  exact h

theorem ev_jcc {cc : CondCode} {l : Label} (hk : Host.prog[k]? = some (jccL cc l))
    (ht : cc.interp s.status = true → Ev Q s (label l))
    (hf : cc.interp s.status = false → Ev Q s (at_ (k + 1))) : Ev Q s (at_ k) := by
  run_instr
  cases hc : cc.interp s.status
  · simpa [hc, Effects.All] using hf hc
  · simpa [hc, Effects.All] using ht hc

theorem ev_jmp {l : Label} (hk : Host.prog[k]? = some (jmpL l)) (h : Ev Q s (label l)) :
    Ev Q s (at_ k) := by
  run_instr
  rwa [show ∀ a b : Int64, a + (b - a) = b from fun a b => by
    apply Int64.toBitVec_inj.mp; simp only [Int64.toBitVec_add, Int64.toBitVec_sub]
    rw [BitVec.add_comm, BitVec.sub_add_cancel]]

omit [Host] in
theorem int64_add_sub_cancel (a b : Int64) : a + (b - a) = b := by
  apply Int64.toBitVec_inj.mp; simp only [Int64.toBitVec_add, Int64.toBitVec_sub]
  rw [BitVec.add_comm, BitVec.sub_add_cancel]

omit [Host] in
theorem addr_sib1 [Labels] (b i : Reg64) (regs : Reg64s) (rng : Std.Rco Int64) :
    ((AddrExpr.interp (address_size := .mk .W64) (a := mbi b i .W8) regs rng).zeroExtend 64)
      = regs.get64 b + regs.get64 i := by
  simp only [AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize, Reg64s.get64]
  have htake : ∀ x : BitVec 64, x.take Width.W64.bits = x := by
    intro x; simp [BitVec.take, BitVec.extractLsb']
  rw [htake, htake]
  have hsigned : ∀ x : BitVec 64, x.signed = x.toInt := fun _ => rfl
  rw [hsigned, hsigned,
    show ∀ y : BitVec Width.W64.bits, BitVec.zeroExtend 64 y = y from fun _ => rfl]
  apply BitVec.eq_of_toInt_eq
  simp [BitVec.toInt_add, BitVec.toInt_ofInt]

omit [Host] in
theorem addr_sib8 [Labels] (b i : Reg64) (regs : Reg64s) (rng : Std.Rco Int64) :
    ((AddrExpr.interp (address_size := .mk .W64) (a := mbi b i .W64) regs rng).zeroExtend 64)
      = regs.get64 b + regs.get64 i * 8 := by
  rw [show mbi b i .W64 = ⟨some (.reg b), some ⟨i, .W64⟩, .int64 0⟩ from rfl,
    AddrExpr.zeroExtend_interp_sib]
  simp

theorem ev_movzx {k} {s : MachineData} {Q} (hk : Host.prog[k]? = some
      (i64 (.movzx (.reg (rr .rax)) (w' := .W8) (.mem (mbi .rcx .rax .W8)))))
    {b : UInt8} (hb : s.dmem.get? (s.regs.rcx.toBitVec + s.regs.rax.toBitVec) = some b)
    (h : Ev Q { s with regs := s.regs.set64 .rax (b.toUInt64.toBitVec) } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  rw [addr_sib1]
  simp only [Reg64s.get64_rax, Reg64s.get64_rcx, loadInt_one_of hb, Effects.All]
  refine ev_of_regs h ?_
  congr 1; apply BitVec.eq_of_toNat_eq; simp

theorem ev_ld64 {k} {s : MachineData} {Q}
    (hk : Host.prog[k]? = some (movRM .rax (mbi .rcx .rax .W64)))
    {v : Word} (hv : rdW s.dmem (s.regs.rcx.toBitVec + s.regs.rax.toBitVec * 8) = some v)
    (h : Ev Q { s with regs := s.regs.set64 .rax v.toBitVec } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  rw [addr_sib8]
  simp only [rdW, Option.map_eq_some_iff] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  simp only [Reg64s.get64_rax, Reg64s.get64_rcx, hi, Effects.All]
  exact h

theorem ev_st8 {k} {s : MachineData} {Q}
    (hk : Host.prog[k]? = some (i8 (.mov (.mem (mbi .rcx .rax .W8)) (.regOrMem (.reg (.low .rdx .W8))))))
    (hm : (s.dmem.get? (s.regs.rcx.toBitVec + s.regs.rax.toBitVec)).isSome)
    (h : Ev Q { s with dmem := Mem.storeInt s.dmem (s.regs.rcx.toBitVec + s.regs.rax.toBitVec) 1 (s.regs.get (.low .rdx .W8)).toInt } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  rw [addr_sib1]
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hm
  simp only [Reg64s.get64_rax, Reg64s.get64_rcx, loadInt_one_of hb, Effects.All]
  exact h

theorem ev_st64 {k} {s : MachineData} {Q}
    (hk : Host.prog[k]? = some (movMR (mbi .rcx .rax .W64) .rdx))
    (hm : (rdW s.dmem (s.regs.rcx.toBitVec + s.regs.rax.toBitVec * 8)).isSome)
    (h : Ev Q { s with dmem := wrW s.dmem (s.regs.rcx.toBitVec + s.regs.rax.toBitVec * 8) s.regs.rdx.toBitVec }
      (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  rw [addr_sib8]
  simp only [rdW, Option.isSome_map] at hm
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hm
  simp only [Reg64s.get64_rax, Reg64s.get64_rcx, hi, Effects.All]
  exact h

theorem ev_lea {d b : Reg64} {off : Int} (hk : Host.prog[k]? = some (i64 (.lea (rr d) (mb b off))))
    (hoff : SmallOff off)
    (h : Ev Q { s with regs := s.regs.set64 d (A ((s.regs.get64 b).toNat + off.toNat)) } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  rw [addr_disp _ _ hoff.1 (by omega)]
  exact h

theorem ev_subRI {r : Reg64} {i : Int} (hk : Host.prog[k]? = some (i64 (.sub (.reg (rr r)) (oI i))))
    (h : ∀ st, Ev Q { s with regs := s.regs.set64 r (s.regs.get64 r - (Int64.ofInt i).toBitVec), status := st }
      (at_ (k + 1))) : Ev Q s (at_ k) := by
  run_instr
  refine ev_flags h ?_
  simp

/-- `sub r14, 1` with the flag that `jb` tests. -/
theorem ev_sub1 {r : Reg64} (hk : Host.prog[k]? = some (i64 (.sub (.reg (rr r)) (oI 1))))
    (h : ∀ st : StatusFlags, st.cf = decide (s.regs.get64 r = 0) →
      Ev Q { s with regs := s.regs.set64 r (s.regs.get64 r - 1), status := st } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  refine h _ ?_
  simp only [Width.bits, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq, StatusFlags.cf_from_result,
    BitVec.unsigned_eq]
  generalize s.regs.get64 r = x
  by_cases hx : x = 0
  · subst hx; decide
  · have : (Int64.ofInt 1).toBitVec = 1#64 := rfl
    rw [this]
    have h1 : 1 ≤ x.toNat := by
      rcases Nat.eq_zero_or_pos x.toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hx
      · exact h
    rw [show decide (x = 0) = false from decide_eq_false hx]
    simp [BitVec.toNat_sub]
    omega

theorem ev_addRI {r : Reg64} {i : Int} (hk : Host.prog[k]? = some (i64 (.add (.reg (rr r)) (oI i))))
    (h : ∀ st, Ev Q { s with regs := s.regs.set64 r (s.regs.get64 r + (Int64.ofInt i).toBitVec), status := st }
      (at_ (k + 1))) : Ev Q s (at_ k) := by
  run_instr
  refine ev_flags h ?_
  simp [BitVec.add_comm]

theorem ev_subRM {r : Reg64} {off : Int} (hk : Host.prog[k]? = some (i64 (.sub (.reg (rr r)) (oM (mb .r15 off)))))
    (hoff : SmallOff off) {v : Word} (hv : rdW s.dmem (A (s.regs.r15.toNat + off.toNat)) = some v)
    (h : ∀ st, Ev Q { s with regs := s.regs.set64 r (s.regs.get64 r - v.toBitVec), status := st }
      (at_ (k + 1))) : Ev Q s (at_ k) := by
  run_instr
  rw [Reg64s.get64_r15, addr_disp _ _ hoff.1 (by omega)]
  simp only [rdW, Option.map_eq_some_iff] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  simp only [UInt64.toNat_toBitVec, hi, Effects.All]
  refine ev_flags h ?_
  simp

theorem ev_movMI {b : Reg64} {off i : Int} (hk : Host.prog[k]? = some (i64 (.mov (.mem (mb b off)) (oI i))))
    (hoff : SmallOff off) (hm : (rdW s.dmem (A ((s.regs.get64 b).toNat + off.toNat))).isSome)
    (h : Ev Q { s with dmem := wrW s.dmem (A ((s.regs.get64 b).toNat + off.toNat)) (Int64.ofInt i).toBitVec }
      (at_ (k + 1))) : Ev Q s (at_ k) := by
  run_instr
  rw [addr_disp _ _ hoff.1 (by omega)]
  simp only [rdW, Option.isSome_map] at hm
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hm
  simp only [hj, Effects.All, Width.bits, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq]
  exact h

theorem ev_call {l : Label} (hk : Host.prog[k]? = some (i64 (.call (.rel (.sub (.label l) .after_current_instruction)))))
    (hm : (rdW s.dmem (s.regs.rsp.toBitVec - 8)).isSome)
    (h : Ev Q { s with regs := s.regs.set64 .rsp (s.regs.rsp.toBitVec - 8), dmem := wrW s.dmem (s.regs.rsp.toBitVec - 8) (at_ (k + 1)).toBitVec } (label l)) :
    Ev Q s (at_ k) := by
  run_instr
  simp only [rdW, Option.isSome_map] at hm
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hm
  simp only [Width.bytesv, Width.bytes, Reg64s.get64_rsp]
  simp only [BitVec.ofNat_eq_ofNat] at hj h
  simp only [hj, Effects.All]
  rwa [int64_add_sub_cancel, Int64.ofBitVec_toBitVec]

theorem ev_ret (hk : Host.prog[k]? = some (i64 .ret)) {ra : Word} (hv : rdW s.dmem s.regs.rsp.toBitVec = some ra)
    (h : Ev Q { s with regs := s.regs.set64 .rsp (s.regs.rsp.toBitVec + 8) } (Int64.ofBitVec ra.toBitVec)) :
    Ev Q s (at_ k) := by
  run_instr
  simp only [rdW, Option.map_eq_some_iff] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  simp only [Reg64s.get64_rsp, hi, Effects.All]
  exact h

theorem ev_push {r : Reg64} (hk : Host.prog[k]? = some (i64 (.push (oR r))))
    (hm : (rdW s.dmem (s.regs.rsp.toBitVec - 8)).isSome)
    (h : Ev Q { s with regs := s.regs.set64 .rsp (s.regs.rsp.toBitVec - 8), dmem := wrW s.dmem (s.regs.rsp.toBitVec - 8) (s.regs.get64 r) } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  simp only [rdW, Option.isSome_map] at hm
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hm
  simp only [Width.bytesv, Width.bytes, Reg64s.get64_rsp]
  simp only [BitVec.ofNat_eq_ofNat] at hj h
  simp only [hj, Effects.All]
  exact h

theorem ev_pop {r : Reg64} (hk : Host.prog[k]? = some (i64 (.pop (.reg (rr r)))))
    {v : Word} (hv : rdW s.dmem s.regs.rsp.toBitVec = some v)
    (h : Ev Q { s with regs := (s.regs.set64 .rsp (s.regs.rsp.toBitVec + 8)).set64 r v.toBitVec } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  simp only [rdW, Option.map_eq_some_iff] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  simp only [Width.bytesv, Width.bytes, Reg64s.get64_rsp]
  simp only [BitVec.ofNat_eq_ofNat] at h
  simp only [hi, Effects.All]
  exact h


/-! ## The flags of `cmp` -/

omit [Host] in
theorem cf_cmp (a b : BitVec 64) :
    (BitVec.unsigned (a - b) != a.unsigned - b.unsigned) = decide (a.toNat < b.toNat) := by
  simp only [BitVec.unsigned_eq, BitVec.toNat_sub]
  by_cases h : a.toNat < b.toNat <;> simp [h] <;> omega

omit [Host] in
theorem zf_cmp (a b : BitVec 64) : (a - b == BitVec.zero 64) = (a == b) := by
  have h : a - b = 0#64 ↔ a = b := by
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      simp [BitVec.toNat_sub] at this
      apply BitVec.eq_of_toNat_eq; omega
    · intro h; subst h; simp
  simp only [BitVec.zero_eq]
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; exact h

omit [Host] in
theorem of_cmp (a b : BitVec 64) :
    (BitVec.signed (a - b) != a.signed - b.signed) = BitVec.ssubOverflow a b := by
  simp only [BitVec.signed]
  by_cases h : BitVec.ssubOverflow a b
  · rw [h]
    simp only [BitVec.ssubOverflow, Bool.or_eq_true, decide_eq_true_eq] at h
    have h1 := BitVec.toInt_lt (x := a - b)
    have h2 := BitVec.le_toInt (x := a - b)
    simp only [bne_iff_ne, ne_eq]
    omega
  · rw [BitVec.toInt_sub_of_not_ssubOverflow h]; simp_all

omit [Host] in
theorem lt_cmp (a b : BitVec 64) :
    ((a - b).msb != (BitVec.signed (a - b) != a.signed - b.signed)) = decide (a.toInt < b.toInt) := by
  rw [of_cmp]
  have h1 := BitVec.toInt_lt (x := a)
  have h2 := BitVec.le_toInt (x := a)
  have h3 := BitVec.toInt_lt (x := b)
  have h4 := BitVec.le_toInt (x := b)
  rw [BitVec.msb_eq_toInt, BitVec.toInt_sub, Int.bmod_def]
  simp only [BitVec.ssubOverflow]
  simp at h1 h2 h3 h4 ⊢
  by_cases hp : 9223372036854775808 ≤ a.toInt - b.toInt
  · have hn : ¬ a.toInt - b.toInt < -9223372036854775808 := by omega
    have hl : ¬ a.toInt < b.toInt := by omega
    split <;> simp [hp, hn, hl] <;> omega
  · by_cases hn : a.toInt - b.toInt < -9223372036854775808
    · have hl : a.toInt < b.toInt := by omega
      split <;> simp [hp, hn, hl] <;> omega
    · split <;> simp [hp, hn] <;> omega

omit [Host] in
theorem cmpFlags_cf (a b : BitVec 64) : (cmpFlags a b).cf = decide (a.toNat < b.toNat) := by
  simp only [cmpFlags, StatusFlags.cf_from_result]; exact cf_cmp a b

omit [Host] in
theorem cmpFlags_zf (a b : BitVec 64) : (cmpFlags a b).zf = (a == b) := by
  simp only [cmpFlags, StatusFlags.zf_from_result, zf_cmp]

omit [Host] in
theorem cmpFlags_sf_of (a b : BitVec 64) :
    ((cmpFlags a b).sf != (cmpFlags a b).of) = decide (a.toInt < b.toInt) := by
  simp only [cmpFlags, StatusFlags.from_result, lt_cmp]

omit [Host] in
/-- After `cmp a, b`, the condition code of a comparison is the comparison. -/
theorem cmpCC_interp (op : Cmp) (a b : UInt64) :
    (cmpCC op).interp (cmpFlags a.toBitVec b.toBitVec) = op.eval a b := by
  have hz := cmpFlags_zf a.toBitVec b.toBitVec
  have hc := cmpFlags_cf a.toBitVec b.toBitVec
  have hl := cmpFlags_sf_of a.toBitVec b.toBitVec
  cases op <;> simp only [cmpCC, CondCode.interp, Cmp.eval] <;> simp only [hz, hc, hl] <;>
    rw [Bool.eq_iff_iff] <;>
    simp [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, Int64.lt_iff_toInt_lt, Int64.le_iff_toInt_le,
      UInt64.toBitVec_inj]
  · constructor
    · rintro (h | rfl) <;> omega
    · intro h
      rcases Nat.lt_or_eq_of_le h with h | h
      · exact Or.inl h
      · exact Or.inr (UInt64.toNat_inj.mp h)
  · exact Iff.rfl
  · show _ ↔ a.toBitVec.toInt ≤ b.toBitVec.toInt
    constructor
    · rintro (h | rfl) <;> omega
    · intro h
      rcases Int.lt_or_eq_of_le h with h | h
      · exact Or.inl h
      · exact Or.inr (UInt64.toBitVec_inj.mp (BitVec.eq_of_toInt_eq h))

omit [Host] in
theorem neg_interp (cc : CondCode) (st : StatusFlags) : (CondCode.neg cc).interp st = !cc.interp st := by
  obtain ⟨cf, pf, af, zf, sf, of⟩ := st
  cases cc <;> cases cf <;> cases pf <;> cases zf <;> cases sf <;> cases of <;> rfl

/-- Operand `o` reads the word `v` in `s`: an immediate `v`, a mapped `[b + off]` holding `v`, or
a register holding `v`. -/
def OpReads (s : MachineData) (o : Operand .W64) (v : Word) : Prop :=
  o = .imm (.int64 v.toInt64) ∨
  (∃ b off, o = oM (mb b off) ∧ SmallOff off ∧ rdW s.dmem (A ((s.regs.get64 b).toNat + off.toNat)) = some v) ∨
  ∃ r, o = oR r ∧ s.regs.get64 r = v.toBitVec

/-! ## Simple operands: memory and immediate operands, immediate shift counts -/

theorem ev_movRO {r : Reg64} {o : Operand .W64} {v : Word}
    (hk : Host.prog[k]? = some (i64 (.mov (.reg (rr r)) o))) (hr : OpReads s o v)
    (h : Ev Q { s with regs := s.regs.set64 r v.toBitVec } (at_ (k + 1))) : Ev Q s (at_ k) := by
  rcases hr with rfl | ⟨b, off, rfl, hoff, hv⟩ | ⟨r', rfl, hv⟩
  · exact ev_movRI hk h
  · exact ev_movRM hk hoff hv h
  · refine ev_movRR hk ?_
    rw [hv]; exact h

/-- `op rax, o` for the forms of `binDirect`. -/
theorem ev_binO {op : BinOp} {o : Operand .W64} {d : Directive} {v : Word}
    (hd : binDirect op o = some d) (hk : Host.prog[k]? = some d) (hr : OpReads s o v)
    (h : ∀ st, Ev Q { s with regs := s.regs.set64 .rax (op.eval s.regs.rax v).toBitVec, status := st } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  rcases hr with rfl | ⟨b, off, rfl, hoff, hv⟩ | ⟨r, rfl, hv⟩
  · cases op <;> simp only [binDirect, aluDirect, Option.some.injEq, reduceCtorEq] at hd <;> subst hd <;> run_instr <;>
      (intros; refine ev_flags h ?_; simp [BinOp.eval, BitVec.add_comm])
  · simp only [rdW, Option.map_eq_some_iff] at hv
    obtain ⟨i, hi, rfl⟩ := hv
    cases op <;> simp only [binDirect, aluDirect, Option.some.injEq, reduceCtorEq] at hd <;> subst hd <;> run_instr <;>
      (rw [addr_disp _ _ hoff.1 (by omega)]; simp only [hi, Effects.All]
       intros; refine ev_flags h ?_; simp [BinOp.eval, BitVec.add_comm])
  · cases op <;> simp only [binDirect, aluDirect, Option.some.injEq, reduceCtorEq] at hd <;> subst hd <;> run_instr <;>
      (intros; refine ev_flags h ?_; simp [BinOp.eval, BitVec.add_comm, hv])

/-- `cmp r, o`. -/
theorem ev_cmpRO {r : Reg64} {o : Operand .W64} {v : Word}
    (hk : Host.prog[k]? = some (i64 (.cmp (.reg (rr r)) o))) (hr : OpReads s o v)
    (h : Ev Q { s with status := cmpFlags (s.regs.get64 r) v.toBitVec } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  rcases hr with rfl | ⟨b, off, rfl, hoff, hv⟩ | ⟨r', rfl, hv⟩
  · run_instr
    simp only [Width.bits, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq]
    exact h
  · simp only [rdW, Option.map_eq_some_iff] at hv
    obtain ⟨i, hi, rfl⟩ := hv
    run_instr
    rw [addr_disp _ _ hoff.1 (by omega)]
    simp only [hi, Effects.All]
    exact h
  · run_instr
    rw [hv]; exact h

theorem ev_cmpO {o : Operand .W64} {v : Word}
    (hk : Host.prog[k]? = some (i64 (.cmp (.reg (rr .rax)) o))) (hr : OpReads s o v)
    (h : Ev Q { s with status := cmpFlags s.regs.rax.toBitVec v.toBitVec } (at_ (k + 1))) :
    Ev Q s (at_ k) :=
  ev_cmpRO hk hr h

/-- `cmp m, o` (conditions in place, `cmpIn`): `m` a register or a mapped memory word. -/
theorem ev_cmpG {m : RegOrMem .W64} {o : Operand .W64} {va vb : Word}
    (hk : Host.prog[k]? = some (i64 (.cmp m o))) (ha : OpReads s (.regOrMem m) va) (hb : OpReads s o vb)
    (h : Ev Q { s with status := cmpFlags va.toBitVec vb.toBitVec } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  rcases ha with hm | ⟨b, off, hm, hoff, hv⟩ | ⟨r, hm, hv⟩
  · cases hm
  · cases hm
    simp only [rdW, Option.map_eq_some_iff] at hv
    obtain ⟨i, hi, rfl⟩ := hv
    rcases hb with rfl | ⟨b', off', rfl, hoff', hv'⟩ | ⟨r', rfl, hv'⟩
    · run_instr
      rw [addr_disp _ _ hoff.1 (by omega)]
      simp only [hi, Effects.All, Width.bits, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq]
      exact h
    · simp only [rdW, Option.map_eq_some_iff] at hv'
      obtain ⟨i', hi', rfl⟩ := hv'
      run_instr
      rw [addr_disp _ _ hoff.1 (by omega), addr_disp _ _ hoff'.1 (by omega)]
      simp only [hi, hi', Effects.All]
      exact h
    · run_instr
      rw [addr_disp _ _ hoff.1 (by omega)]
      simp only [hi, Effects.All]
      rw [hv']; exact h
  · cases hm
    refine ev_cmpRO hk hb ?_
    rw [hv]; exact h

omit [Host] in
/-- After `cmp b, a` (swapped), `swapCC op` is the comparison `a op b`. -/
theorem swapCC_interp (op : Cmp) (a b : UInt64) :
    (swapCC op).interp (cmpFlags b.toBitVec a.toBitVec) = op.eval a b := by
  cases op
  · have := cmpCC_interp .eq b a
    simp only [cmpCC, swapCC, Cmp.eval] at this ⊢; rw [this]; exact BEq.comm
  · have := cmpCC_interp .ne b a
    simp only [cmpCC, swapCC, Cmp.eval] at this ⊢; rw [this]; simp only [bne, BEq.comm (a := a)]
  · have h1 := neg_interp .be (cmpFlags b.toBitVec a.toBitVec)
    have h2 := cmpCC_interp .ule b a
    simp only [CondCode.neg, cmpCC] at h1 h2
    simp only [swapCC, Cmp.eval]; rw [h1, h2]; simp only [Cmp.eval, UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le]
    rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]; omega
  · have h1 := neg_interp .c (cmpFlags b.toBitVec a.toBitVec)
    have h2 := cmpCC_interp .ult b a
    simp only [CondCode.neg, cmpCC] at h1 h2
    simp only [swapCC, Cmp.eval]; rw [h1, h2]; simp only [Cmp.eval, UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le]
    rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]; omega
  · have h1 := neg_interp .le (cmpFlags b.toBitVec a.toBitVec)
    have h2 := cmpCC_interp .sle b a
    simp only [CondCode.neg, cmpCC] at h1 h2
    simp only [swapCC, Cmp.eval]; rw [h1, h2]; simp only [Cmp.eval, Int64.lt_iff_toInt_lt, Int64.le_iff_toInt_le]
    rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]; omega
  · have h1 := neg_interp .l (cmpFlags b.toBitVec a.toBitVec)
    have h2 := cmpCC_interp .slt b a
    simp only [CondCode.neg, cmpCC] at h1 h2
    simp only [swapCC, Cmp.eval]; rw [h1, h2]; simp only [Cmp.eval, Int64.lt_iff_toInt_lt, Int64.le_iff_toInt_le]
    rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]; omega

/-- `op r, w` for the forms of `aluDirect`. -/
theorem ev_aluRI {op : BinOp} {r : Reg64} {w : Word} {d : Directive}
    (hd : aluDirect op (.reg (rr r)) (.imm (.int64 w.toInt64)) = some d) (hk : Host.prog[k]? = some d)
    (h : ∀ st, Ev Q { s with regs := s.regs.set64 r (op.eval (UInt64.ofBitVec (s.regs.get64 r)) w).toBitVec, status := st }
      (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  cases op <;> simp only [aluDirect, Option.some.injEq, reduceCtorEq] at hd <;> subst hd <;> run_instr <;>
    (intros; refine ev_flags h ?_; simp [BinOp.eval, BitVec.add_comm])

/-- `mov [b + off], w` with a sign-extended immediate. -/
theorem ev_movMW {b : Reg64} {off : Int} {w : Word}
    (hk : Host.prog[k]? = some (i64 (.mov (.mem (mb b off)) (.imm (.int64 w.toInt64)))))
    (hoff : SmallOff off) (hm : (rdW s.dmem (A ((s.regs.get64 b).toNat + off.toNat))).isSome)
    (h : Ev Q { s with dmem := wrW s.dmem (A ((s.regs.get64 b).toNat + off.toNat)) w.toBitVec }
      (at_ (k + 1))) : Ev Q s (at_ k) := by
  run_instr
  rw [addr_disp _ _ hoff.1 (by omega)]
  simp only [rdW, Option.isSome_map] at hm
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hm
  simp only [hj, Effects.All, Width.bits, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq]
  exact h

theorem ev_flags_mem {z : RegZmms} {d d' : DataMem} {pc : Int64} {R : Reg64s}
    {S : StatusFlags} (h : ∀ st, Ev Q ⟨R, z, st, d⟩ pc) (hd : d = d') : Ev Q ⟨R, z, S, d'⟩ pc :=
  hd ▸ h S

/-- `op [b + off], w` (read-modify-write) for the forms of `aluDirect`. -/
theorem ev_aluMI {op : BinOp} {b : Reg64} {off : Int} {w v : Word} {d : Directive}
    (hd : aluDirect op (.mem (mb b off)) (.imm (.int64 w.toInt64)) = some d) (hk : Host.prog[k]? = some d)
    (hoff : SmallOff off) (hv : rdW s.dmem (A ((s.regs.get64 b).toNat + off.toNat)) = some v)
    (h : ∀ st, Ev Q { s with dmem := wrW s.dmem (A ((s.regs.get64 b).toNat + off.toNat)) (op.eval v w).toBitVec, status := st }
        (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  simp only [rdW, Option.map_eq_some_iff] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  cases op <;> simp only [aluDirect, Option.some.injEq, reduceCtorEq] at hd <;> subst hd <;> run_instr <;>
    (rw [addr_disp _ _ hoff.1 (by omega)]; simp only [hi, Effects.All]
     intros; refine ev_flags_mem h ?_; simp [wrW, BinOp.eval, BitVec.add_comm])

omit [Host] in
theorem imm8_count [Labels] {n : Nat} (hn : n < 64) (s : MachineData) (p : Std.Rco Int64) :
    (ShiftCountExpr.imm8 (.int64 (Int64.ofInt n))).interpMasked s p .W64 = n := by
  simp only [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, ConstExpr.interp]
  rw [show (0x3f : Nat) = 2 ^ 6 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp [BitVec.take, Int64.toBitVec_ofInt]
  omega

/-- `shl rax, n` / `shr rax, n` with an immediate count. -/
theorem ev_shiftI {n : Nat} (hn : n < 64) {op : BinOp} (hop : op = .shl ∨ op = .shr)
    (hk : Host.prog[k]? = some (match op with
      | .shl => i64 (.shl (.reg (rr .rax)) (.imm8 (.int64 (Int64.ofInt n))))
      | _ => i64 (.shr (.reg (rr .rax)) (.imm8 (.int64 (Int64.ofInt n))))))
    (h : ∀ st, Ev Q { s with regs := s.regs.set64 .rax (op.eval s.regs.rax (UInt64.ofNat n)).toBitVec, status := st } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  rcases hop with rfl | rfl <;> simp only at hk <;> run_instr <;> rw [imm8_count hn] <;>
  · split
    · simp only [Effects.All]
      refine ev_flags h ?_
      simp_all [BinOp.eval, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight, Nat.mod_eq_of_lt hn]
    · simp only [Effects.All]
      intro af
      (try split) <;> (try split) <;> simp only [Effects.All] <;> intros <;>
        (refine ev_flags h ?_
         simp_all [BinOp.eval, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight, Nat.mod_eq_of_lt hn])

/-- `shl r, n` with an immediate count, for any register (tiered accesses: `tierDesc`). -/
theorem ev_shlRI {n : Nat} (hn : n < 64) {r : Reg64}
    (hk : Host.prog[k]? = some (i64 (.shl (.reg (rr r)) (.imm8 (.int64 (Int64.ofInt n))))))
    (h : ∀ st, Ev Q { s with regs := s.regs.set64 r ((UInt64.ofBitVec (s.regs.get64 r)) <<< (UInt64.ofNat n)).toBitVec, status := st } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  rw [imm8_count hn]
  split
  · simp only [Effects.All]
    refine ev_flags h ?_
    simp_all [UInt64.toBitVec_shiftLeft, Nat.mod_eq_of_lt hn]
  · simp only [Effects.All]
    intro af
    (try split) <;> (try split) <;> simp only [Effects.All] <;> intros <;>
      (refine ev_flags h ?_
       simp_all [UInt64.toBitVec_shiftLeft, Nat.mod_eq_of_lt hn])

/-- `add r, r15`. -/
theorem ev_addR15 {r : Reg64} (hk : Host.prog[k]? = some (i64 (.add (.reg (rr r)) (oR .r15))))
    (h : ∀ st, Ev Q { s with regs := s.regs.set64 r (s.regs.get64 r + s.regs.r15.toBitVec), status := st } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  intros; refine ev_flags h ?_; simp [BitVec.add_comm]

/-- `cmp rax, [b + off]`, for any base register. -/
theorem ev_cmpRMb {b : Reg64} {off : Int} (hk : Host.prog[k]? = some (i64 (.cmp (.reg (rr .rax)) (oM (mb b off)))))
    (hoff : SmallOff off) {v : Word} (hv : rdW s.dmem (A ((s.regs.get64 b).toNat + off.toNat)) = some v)
    (h : Ev Q { s with status := cmpFlags s.regs.rax.toBitVec v.toBitVec } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  rw [addr_disp _ _ hoff.1 (by omega)]
  simp only [rdW, Option.map_eq_some_iff] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  simp only [hi, Effects.All]
  exact h


/-! ### Blocks (lane blkcopy) -/

omit [Host] in
theorem addr_sib1d [Labels] (b i : Reg64) (off : Int) (regs : Reg64s) (rng : Std.Rco Int64) :
    ((AddrExpr.interp (address_size := .mk .W64) (a := ⟨some (.reg b), some ⟨i, .W8⟩, .int64 (Int64.ofInt off)⟩)
      regs rng).zeroExtend 64) = regs.get64 b + regs.get64 i + BitVec.ofInt 64 (Int64.ofInt off).toInt := by
  simp only [AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize, Reg64s.get64]
  have htake : ∀ x : BitVec 64, x.take Width.W64.bits = x := by
    intro x; simp [BitVec.take, BitVec.extractLsb']
  rw [htake, htake]
  have hsigned : ∀ x : BitVec 64, x.signed = x.toInt := fun _ => rfl
  rw [hsigned, hsigned,
    show ∀ y : BitVec Width.W64.bits, BitVec.zeroExtend 64 y = y from fun _ => rfl]
  apply BitVec.eq_of_toInt_eq
  simp [BitVec.toInt_add, BitVec.toInt_ofInt]

/-- `movzx r, byte [b + off]`. -/
theorem ev_movzxM {d b : Reg64} {off : Int}
    (hk : Host.prog[k]? = some (i64 (.movzx (.reg (rr d)) (w' := .W8) (.mem (mb b off)))))
    (hoff : SmallOff off) {v : UInt8} (hv : s.dmem.get? (A ((s.regs.get64 b).toNat + off.toNat)) = some v)
    (h : Ev Q { s with regs := s.regs.set64 d v.toUInt64.toBitVec } (at_ (k + 1))) : Ev Q s (at_ k) := by
  run_instr
  rw [addr_disp _ _ hoff.1 (by omega)]
  simp only [loadInt_one_of hv, Effects.All]
  refine ev_of_regs h ?_
  congr 1; apply BitVec.eq_of_toNat_eq; simp

/-- `movzx r, byte [b + i + off]`. -/
theorem ev_movzxS {d b i : Reg64} {off : Int}
    (hk : Host.prog[k]? = some (i64 (.movzx (.reg (rr d)) (w' := .W8)
      (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 (Int64.ofInt off)⟩))))
    {v : UInt8}
    (hv : s.dmem.get? (s.regs.get64 b + s.regs.get64 i + BitVec.ofInt 64 (Int64.ofInt off).toInt) = some v)
    (h : Ev Q { s with regs := s.regs.set64 d v.toUInt64.toBitVec } (at_ (k + 1))) : Ev Q s (at_ k) := by
  run_instr
  rw [addr_sib1d]
  simp only [loadInt_one_of hv, Effects.All]
  refine ev_of_regs h ?_
  congr 1; apply BitVec.eq_of_toNat_eq; simp

/-- `movzx r, byte [rcx + rax]`. -/
theorem ev_movzxR {d : Reg64} (hk : Host.prog[k]? = some
      (i64 (.movzx (.reg (rr d)) (w' := .W8) (.mem (mbi .rcx .rax .W8)))))
    {b : UInt8} (hb : s.dmem.get? (s.regs.rcx.toBitVec + s.regs.rax.toBitVec) = some b)
    (h : Ev Q { s with regs := s.regs.set64 d (b.toUInt64.toBitVec) } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  rw [addr_sib1]
  simp only [Reg64s.get64_rax, Reg64s.get64_rcx, loadInt_one_of hb, Effects.All]
  refine ev_of_regs h ?_
  congr 1; apply BitVec.eq_of_toNat_eq; simp

/-- `mov rax, [rcx + rax]`: an 8-byte load at a byte address. -/
theorem ev_ld64b
    (hk : Host.prog[k]? = some (movRM .rax (mbi .rcx .rax .W8)))
    {v : Word} (hv : rdW s.dmem (s.regs.rcx.toBitVec + s.regs.rax.toBitVec) = some v)
    (h : Ev Q { s with regs := s.regs.set64 .rax v.toBitVec } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  rw [addr_sib1]
  simp only [rdW, Option.map_eq_some_iff] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  simp only [Reg64s.get64_rax, Reg64s.get64_rcx, hi, Effects.All]
  exact h


omit [Host] in
/-- The address `[r15 + 8 r + off]` of a tiered descriptor word (`tdesc`). -/
theorem addr_tdesc (x y : BitVec 64) (off : Int) (h0 : 0 ≤ off) (h1 : off < 2 ^ 63) :
    x + y * 8 + BitVec.ofInt 64 (Int64.ofInt off).toInt = A (x.toNat + 8 * y.toNat + off.toNat) := by
  have : (Int64.ofInt off).toInt = off := by
    simp only [Int64.toInt_ofInt]; rw [Int.bmod_eq_of_le] <;> simp [Int64.size] <;> omega
  rw [this]
  apply BitVec.eq_of_toNat_eq
  simp [A, BitVec.toNat_add, BitVec.toNat_ofInt, BitVec.toNat_mul]
  omega

/-- `mov d, [r15 + 8 r + off]`. -/
theorem ev_movRMt {d r : Reg64} {off : Int} (hk : Host.prog[k]? = some (movRM d (tdesc r off)))
    (hoff : SmallOff off) {v : Word}
    (hv : rdW s.dmem (A (s.regs.r15.toNat + 8 * (s.regs.get64 r).toNat + off.toNat)) = some v)
    (h : Ev Q { s with regs := s.regs.set64 d v.toBitVec } (at_ (k + 1))) : Ev Q s (at_ k) := by
  run_instr
  rw [AddrExpr.zeroExtend_interp_sib, addr_tdesc _ _ _ hoff.1 (by omega)]
  simp only [rdW, Option.map_eq_some_iff] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  simp only [Reg64s.get64_r15, UInt64.toNat_toBitVec, hi, Effects.All]
  simpa using h

/-- `cmp rax, [r15 + 8 r + off]`. -/
theorem ev_cmpRMt {r : Reg64} {off : Int} (hk : Host.prog[k]? = some (i64 (.cmp (.reg (rr .rax)) (oM (tdesc r off)))))
    (hoff : SmallOff off) {v : Word}
    (hv : rdW s.dmem (A (s.regs.r15.toNat + 8 * (s.regs.get64 r).toNat + off.toNat)) = some v)
    (h : Ev Q { s with status := cmpFlags s.regs.rax.toBitVec v.toBitVec } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  run_instr
  rw [AddrExpr.zeroExtend_interp_sib, addr_tdesc _ _ _ hoff.1 (by omega)]
  simp only [rdW, Option.map_eq_some_iff] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  simp only [Reg64s.get64_r15, UInt64.toNat_toBitVec, hi, Effects.All]
  exact h


end

end L.Compiler
