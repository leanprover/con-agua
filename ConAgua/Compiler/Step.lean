module

public import ConAgua.Compiler.Compile
public import ConAgua.Compiler.Mem
public import Kraken.X64.WP.Basic
public import Kraken.X64.Registers
public import Std.Tactic.BVDecide

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

theorem ev_bin {op : BinOp} (hk : Host.prog[k]? = some (binInstr op))
    (h : ∀ st, Ev Q { s with regs := s.regs.set64 .rax (op.eval s.regs.rax s.regs.rcx).toBitVec, status := st } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  cases op <;> simp only [binInstr] at hk <;> run_instr
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

end

/-! ## The flags of `cmp` -/

omit [Host] in
theorem cf_cmp (a b : BitVec 64) :
    (BitVec.unsigned (a - b) != a.unsigned - b.unsigned) = decide (a.toNat < b.toNat) := by
  simp only [BitVec.unsigned_eq, BitVec.toNat_sub]
  by_cases h : a.toNat < b.toNat <;> simp [h] <;> omega

omit [Host] in
theorem zf_cmp (a b : BitVec 64) : (a - b == BitVec.zero 64) = (a == b) := by
  simp only [BitVec.zero_eq]; bv_decide

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
  rw [of_cmp, BitVec.ssubOverflow_eq]
  have : decide (a.toInt < b.toInt) = a.slt b := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff, BitVec.slt_iff_toInt_lt]
  rw [this]
  bv_decide

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

end L.Compiler
