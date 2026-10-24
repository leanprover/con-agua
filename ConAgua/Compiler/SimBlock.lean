module

public import ConAgua.Compiler.SimStore
public import ConAgua.L.Blocks

@[expose] public section

/-!
# Blocks: `copy64`, `copy8w`, `scan8` (lane blkcopy, docs/design/blkcopy.md)

Each block is a machine loop with no L loop around it: the simulation is an induction on the
iterations inside one statement (`scan_loop`, `copy64_loop`, `copy8w_loop`), with the memory
relation (`Inv`) carried through the stores of the copies (`Inv.store64`).
-/

namespace L.Compiler

open L

attribute [local simp] Reg64s.set64_rax Reg64s.set64_rcx Reg64s.set64_rdx Reg64s.set64_rsi
  Reg64s.set64_rsp Reg64s.set64_r14

/-- The registers but `rax`, `rcx`, `rdx` agree. -/
def KeepR (s s0 : MachineData) : Prop :=
  ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → s.regs.get64 r = s0.regs.get64 r

theorem KeepR.refl (s : MachineData) : KeepR s s := fun _ _ _ _ => rfl

theorem KeepR.trans {s s1 s0 : MachineData} (h : KeepR s s1) (h1 : KeepR s1 s0) : KeepR s s0 :=
  fun r a b c => (h r a b c).trans (h1 r a b c)

theorem KeepR.set {s s0 : MachineData} (h : KeepR s s0) {r : Reg64} (hr : r = .rax ∨ r = .rcx ∨ r = .rdx)
    (v : BitVec 64) (st : StatusFlags) : KeepR { s with regs := s.regs.set64 r v, status := st } s0 :=
  fun r' a b c => by
    rw [← h r' a b c]
    exact get64_set64_scratch hr v r' a b c

theorem KeepR.ofEq {s' s s0 : MachineData} (h : KeepR s s0)
    (h' : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → s'.regs.get64 r = s.regs.get64 r) : KeepR s' s0 :=
  fun r a b c => (h' r a b c).trans (h r a b c)

theorem add_swap (x y z : BitVec 64) : x + y + z = x + z + y := by
  rw [BitVec.add_assoc, BitVec.add_comm y, ← BitVec.add_assoc]

theorem KeepR.flags {s s0 : MachineData} (h : KeepR s s0) (st : StatusFlags) :
    KeepR { s with status := st } s0 := h

theorem KeepR.r15 {s s0 : MachineData} (h : KeepR s s0) : s.regs.r15 = s0.regs.r15 := by
  have := h .r15 (by decide) (by decide) (by decide)
  simp only [Reg64s.get64_r15] at this
  exact UInt64.toBitVec_inj.mp this

theorem KeepR.rsp {s s0 : MachineData} (h : KeepR s s0) : s.regs.rsp = s0.regs.rsp := by
  have := h .rsp (by decide) (by decide) (by decide)
  simp only [Reg64s.get64_rsp] at this
  exact UInt64.toBitVec_inj.mp this

theorem KeepR.rbp {s s0 : MachineData} (h : KeepR s s0) : s.regs.rbp = s0.regs.rbp := by
  have := h .rbp (by decide) (by decide) (by decide)
  simp only [Reg64s.get64_rbp] at this
  exact UInt64.toBitVec_inj.mp this

theorem KeepR.r14 {s s0 : MachineData} (h : KeepR s s0) : s.regs.r14 = s0.regs.r14 := by
  have := h .r14 (by decide) (by decide) (by decide)
  simp only [Reg64s.get64_r14] at this
  exact UInt64.toBitVec_inj.mp this

theorem KeepR.rsi {s s0 : MachineData} (h : KeepR s s0) : s.regs.rsi = s0.regs.rsi := by
  have := h .rsi (by decide) (by decide) (by decide)
  simp only [Reg64s.get64_rsi] at this
  exact UInt64.toBitVec_inj.mp this

/-- `Inv` with the same memory and the registers but the scratch ones. -/
theorem Inv.keepR {G : Layout} {ctx : Ctx} {F : Nat} {σ : St} {s s0 : MachineData} (hI : Inv G ctx F σ s0)
    (hd : s.dmem = s0.dmem) (hK : KeepR s s0) : Inv G ctx F σ s :=
  hI.of_regs hd hK.rsp hK.r15 fun r hr =>
    hK r (allocRegs_ne hr).1 (allocRegs_ne hr).2.1 (allocRegs_ne hr).2.2.1

theorem one_toBitVec : (Int64.ofInt 1).toBitVec = (1 : Word).toBitVec := rfl
theorem eight_toBitVec : (Int64.ofInt 8).toBitVec = (8 : Word).toBitVec := rfl

section
variable [Host]

/-- **The scan loop**: from `rax = j < e`, with the source at `rcx`, every iteration reads a
byte and its class; the loop leaves at `X` with `rax = scanN b c j e`. -/
theorem scan_loop {G : Layout} {b : Array UInt8} {c : List UInt8} {B TT : Nat} {off : Int}
    {eo : Operand .W64} {ve : Word} {kL : Nat} {Lb Xb : Label} {Q : MachineState → Prop}
    {D : DataMem} {s0 : MachineData}
    (hcode : Code [.label Lb,
      i64 (.movzx (.reg (rr .rdx)) (w' := .W8) (.mem (mbi .rcx .rax .W8))),
      i64 (.movzx (.reg (rr .rdx)) (w' := .W8) (.mem (tblAddr off))),
      i64 (.cmp (.reg (rr .rdx)) (oI 0)), jccL .nz Xb,
      i64 (.add (.reg (rr .rax)) (oI 1)), i64 (.cmp (.reg (rr .rax)) eo), jccL .c Lb] kL)
    (hL : label Lb = at_ kL) (hX : label Xb = at_ (kL + 8))
    (hsrc : SrcAt G b D B) (hve : ve.toNat ≤ b.size)
    (hTT : s0.regs.get64 .r15 + BitVec.ofInt 64 (Int64.ofInt off).toInt = A TT)
    (htbl : ∀ y < 256, D.get? (A (TT + y)) = some c[y]!) (hTT2 : TT + 256 < 2 ^ 64)
    (he : ∀ s, s.dmem = D → KeepR s s0 → OpReads s eo ve) :
    ∀ n (jj : Word) (s : MachineData), s.dmem = D → KeepR s s0 → s.regs.get64 .rcx = A B →
      s.regs.get64 .rax = jj.toBitVec → jj < ve → ve.toNat - jj.toNat = n →
      (∀ s', s'.dmem = D → KeepR s' s0 →
        s'.regs.get64 .rax = (UInt64.ofNat (scanN b c jj.toNat ve.toNat)).toBitVec → Ev Q s' (at_ (kL + 8))) →
      Ev Q s (at_ kL) := by
  intro n
  induction n with
  | zero =>
    intro jj s _ _ _ _ hlt hn _
    have := UInt64.lt_iff_toNat_lt.mp hlt; omega
  | succ n ih =>
    intro jj s hD hK hrcx hrax hlt hn hexit
    have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
    have hjb : jj.toNat < b.size := by omega
    have hfit := hsrc.fit
    refine ev_label hcode.head ?_
    refine ev_movzxR (d := .rdx) hcode.tail.head (b := b[jj.toNat]!) ?_ ?_
    · rw [hD, show s.regs.rcx.toBitVec + s.regs.rax.toBitVec = A (B + jj.toNat) by
        rw [← Reg64s.get64_rcx, ← Reg64s.get64_rax, hrcx, hrax]
        apply BitVec.eq_of_toNat_eq; simp [A, BitVec.toNat_add]]
      exact hsrc.get _ hjb
    have hy : (b[jj.toNat]!).toNat < 256 := (b[jj.toNat]!).toNat_lt
    refine ev_movzxS hcode.tail.tail.head (v := c[(b[jj.toNat]!).toNat]!) ?_ ?_
    · rw [hD]
      have h15 : (s.regs.set64 .rdx (b[jj.toNat]!).toUInt64.toBitVec).get64 .r15 = s0.regs.get64 .r15 := by
        rw [rget_set]; simp only [reduceCtorEq, ↓reduceIte]; exact hK .r15 (by decide) (by decide) (by decide)
      rw [h15, rget_set, if_pos rfl, add_swap, hTT]
      rw [show A TT + (b[jj.toNat]!).toUInt64.toBitVec = A (TT + (b[jj.toNat]!).toNat) by
        apply BitVec.eq_of_toNat_eq; simp [A, BitVec.toNat_add]]
      exact htbl _ hy
    refine ev_cmpRO (v := 0) hcode.tail.tail.tail.head (.inl rfl) ?_
    simp only [rget_set, ↓reduceIte]
    refine ev_jcc hcode.tail.tail.tail.tail.head (fun hcc => ?_) (fun hcc => ?_)
    · rw [interp_nz] at hcc
      have hc0 : c[(b[jj.toNat]!).toNat]! ≠ 0 := by
        intro h0; simp [h0] at hcc
      rw [hX]
      refine hexit _ hD (hK.ofEq (by keep_tac)) ?_
      rw [scanN_hit b c _ _ hlt' hc0]
      simp only [rget_set, reduceCtorEq, ↓reduceIte, hrax, UInt64.ofNat_toNat]
    · rw [interp_nz] at hcc
      have hc0 : c[(b[jj.toNat]!).toNat]! = 0 := by
        have h1 : (c[(b[jj.toNat]!).toNat]!).toUInt64 = 0 := by simpa using hcc
        have h2 := congrArg UInt64.toNat h1
        simp only [UInt8.toNat_toUInt64, UInt64.toNat_zero] at h2
        exact UInt8.toNat_inj.mp (by simpa using h2)
      have hj1 : (jj + 1).toNat = jj.toNat + 1 := by
        rw [UInt64.toNat_add]; simp; have := ve.toNat_lt; omega
      refine ev_addRI hcode.tail.tail.tail.tail.tail.head fun st => ?_
      have hrax2 : ∀ (R : Reg64s), R = (s.regs.set64 .rdx (b[jj.toNat]!).toUInt64.toBitVec).set64 .rdx
          (c[(b[jj.toNat]!).toNat]!).toUInt64.toBitVec → R.get64 .rax = jj.toBitVec := by
        intro R hR; subst hR; simp only [rget_set, reduceCtorEq, ↓reduceIte, hrax]
      rw [hrax2 _ rfl, one_toBitVec, ← UInt64.toBitVec_add]
      refine ev_cmpRO (v := ve) hcode.tail.tail.tail.tail.tail.tail.head
        (he _ hD (hK.ofEq (by keep_tac))) ?_
      simp only [rget_set, ↓reduceIte]
      refine ev_jcc hcode.tail.tail.tail.tail.tail.tail.tail.head (fun hcc2 => ?_) (fun hcc2 => ?_)
      · rw [interp_c] at hcc2
        have hlt2 : jj + 1 < ve := by simpa using hcc2
        rw [hL]
        refine ih (jj + 1) _ hD (hK.ofEq (by keep_tac)) (by simp only [rget_set, reduceCtorEq, ↓reduceIte, hrcx])
          (by simp only [rget_set, ↓reduceIte]) hlt2 (by rw [hj1]; omega) fun s' h1 h2 h3 => hexit s' h1 h2 ?_
        rw [h3, scanN_miss b c _ _ hlt' hc0, hj1]
      · rw [interp_c] at hcc2
        have hge : ¬ (jj + 1 < ve) := by simpa using hcc2
        have hge' : ¬ (jj + 1).toNat < ve.toNat := fun h => hge (UInt64.lt_iff_toNat_lt.mpr h)
        refine ev_congr (hexit _ hD (hK.ofEq (by keep_tac)) ?_) (by omega)
        rw [scanN_miss b c _ _ hlt' hc0, scanN_end b c _ _ (by rw [hj1] at hge'; omega)]
        simp only [rget_set, ↓reduceIte]
        congr 1
end

end L.Compiler
