module

public import ConAguaX86.AsmEsc.MulRowAsm
import Kraken.X64.Registers

@[expose] public section

/-!
# A template: the carry chain over two pool windows

`chain2Asm tab f sub`: a hand-written body for a leaf `f(o, oa, ob, n, c)` whose L code computes
`P[o + i] := A[oa + i] ± B[ob + i] ± carry` for `i < n` and returns the carry (`add_n` with
`sub = false`, `sub_n` with `sub = true`). The windows are tagged pool addresses (tier in bit 40).
Up front: a carry in above 1, a window outside its tier or too little fuel go to `ca_exhausted`
(the contract always allows it); `n = 0` returns the carry. The loop keeps the carry in the carry
flag, 6 instructions per limb: load, `adc`/`sbb` from memory, store, `inc`, `dec`, `jne`.

`chain2Asm_sim` proves the per-function contract (`FnSimAt`) for any L function whose run is the
pure model `ch2Rows` (`Chain2Spec`); each leaf's L-side proof supplies that.
-/

namespace L.AsmEsc

open L L.Arena L.Compiler

/-- A local label of a chain body. -/
abbrev chL (f : FnName) (m : String) : Label := ".Lasm_" ++ f ++ "_" ++ m

/-- The carry as a word. -/
abbrev bw (c : Bool) : Word := if c then 1 else 0

/-- `adc` or `sbb` of a register and a scaled memory operand. -/
abbrev chOp (sub : Bool) (d : Reg64) (a : AddrExpr) : Directive :=
  if sub then i64 (.sbb (.reg (rr d)) (oM a)) else i64 (.adc (.reg (rr d)) (oM a))

/-- The template, for the table `tab` (the descriptor offsets of `POOL` = 0). Arguments: `rdi o`,
`r8 oa`, `r9 ob`, `r10 n`, `r11 c`. -/
def chain2Asm (tab : Tab) (f : FnName) (sub : Bool) : Program :=
  [ .label (fnL f),                                                    -- 0
    i64 (.cmp (.reg (rr .r11)) (.imm (.int64 (1 : Word).toInt64))),    -- 1
    jccL .a exhaustedL,                                                -- 2  c > 1
    i64 (.cmp (.reg (rr .r10)) (.imm (.int64 (0 : Word).toInt64))),    -- 3
    jccL .z (chL f "Z"),                                               -- 4  n = 0
    movRI .rax idxMask,                                                -- 5
    movRR .rcx .rdi,                                                   -- 6
    i64 (.shr (.reg (rr .rcx)) (.imm8 (.int64 (Int64.ofInt 40)))),    -- 7
    i64 (.and (.reg (rr .rcx)) (.imm (.int64 (1 : Word).toInt64))),    -- 8  out tier bit
    i64 (.and (.reg (rr .rdi)) (oR .rax)),                             -- 9  ob
    movRR .rdx .r8,                                                    -- 10
    i64 (.shr (.reg (rr .rdx)) (.imm8 (.int64 (Int64.ofInt 40)))),    -- 11
    i64 (.and (.reg (rr .rdx)) (.imm (.int64 (1 : Word).toInt64))),    -- 12 a tier bit
    i64 (.and (.reg (rr .r8)) (oR .rax)),                              -- 13 qa
    movRR .r12 .r9,                                                    -- 14
    i64 (.shr (.reg (rr .r12)) (.imm8 (.int64 (Int64.ofInt 40)))),    -- 15
    i64 (.and (.reg (rr .r12)) (.imm (.int64 (1 : Word).toInt64))),    -- 16 b tier bit
    i64 (.and (.reg (rr .r9)) (oR .rax)),                              -- 17 qb
    movRM .rax (tdesc .rdx (tab.len64 (0 : ArrId))),                   -- 18
    i64 (.sub (.reg (rr .rax)) (oR .r8)),                              -- 19
    jccL .c exhaustedL,                                                -- 20
    i64 (.cmp (.reg (rr .rax)) (oR .r10)),                             -- 21
    jccL .c exhaustedL,                                                -- 22
    movRM .rsi (tdesc .rdx (tab.base64 (0 : ArrId))),                  -- 23
    i64 (.lea (rr .rsi) (mbi .rsi .r8 .W64)),                          -- 24 rsi := &a[qa]
    movRM .rax (tdesc .r12 (tab.len64 (0 : ArrId))),                   -- 25
    i64 (.sub (.reg (rr .rax)) (oR .r9)),                              -- 26
    jccL .c exhaustedL,                                                -- 27
    i64 (.cmp (.reg (rr .rax)) (oR .r10)),                             -- 28
    jccL .c exhaustedL,                                                -- 29
    movRM .rbx (tdesc .r12 (tab.base64 (0 : ArrId))),                  -- 30
    i64 (.lea (rr .rbx) (mbi .rbx .r9 .W64)),                          -- 31 rbx := &b[qb]
    movRM .rax (tdesc .rcx (tab.len64 (0 : ArrId))),                   -- 32
    i64 (.sub (.reg (rr .rax)) (oR .rdi)),                             -- 33
    jccL .c exhaustedL,                                                -- 34
    i64 (.cmp (.reg (rr .rax)) (oR .r10)),                             -- 35
    jccL .c exhaustedL,                                                -- 36
    movRM .rcx (tdesc .rcx (tab.base64 (0 : ArrId))),                  -- 37
    i64 (.lea (rr .rdi) (mbi .rcx .rdi .W64)),                         -- 38 rdi := &out[ob]
    i64 (.sub (.reg (rr .r14)) (oR .r10)),                             -- 39
    jccL .c exhaustedL,                                                -- 40 fuel < n
    movRI .r13 0,                                                      -- 41 i := 0
    movRR .rcx .r10,                                                   -- 42 count := n
    movRI .rdx 0,                                                      -- 43
    movRR .rax .r11,                                                   -- 44
    i64 (.add (.reg (rr .rax)) (oI (-1))),                             -- 45 CF := c
    .label (chL f "L"),                                                -- 46
    movRM .rax (mbi .rsi .r13 .W64),                                   -- 47
    chOp sub .rax (mbi .rbx .r13 .W64),                                -- 48
    movMR (mbi .rdi .r13 .W64) .rax,                                   -- 49
    i64 (.inc (.reg (rr .r13))),                                       -- 50
    i64 (.dec (.reg (rr .rcx))),                                       -- 51
    jccL .nz (chL f "L"),                                              -- 52
    movRI .rax 0,                                                      -- 53
    i64 (.adc (.reg (rr .rax)) (oR .rdx)),                             -- 54 the carry out
    i64 .ret,                                                          -- 55
    .label (chL f "Z"),                                                -- 56
    movRR .rax .r11,                                                   -- 57
    i64 .ret ]                                                         -- 58

section
variable [Host] {kf : Nat} {tab : Tab} {f : FnName} {sub : Bool}

theorem c2_code (hc : Code (chain2Asm tab f sub) kf) {i : Nat} {x : Directive}
    (hi : (chain2Asm tab f sub)[i]? = some x) : Host.prog[kf + i]? = some x := Code.get hc hi

end

/-! ## The model -/

/-- One limb: `x ± y ± c` and the carry (or borrow) out. -/
def chStep (sub : Bool) (x y : Word) (c : Bool) : Word × Bool :=
  if sub then (x - y - bw c, decide (x.toNat < y.toNat + (bw c).toNat))
  else (x + y + bw c, decide (2 ^ 64 ≤ x.toNat + y.toNat + (bw c).toNat))

/-- `r` limbs from index `i` with carry `c`. -/
def ch2Rows (sub : Bool) (TA TB TO : TieredArray) (qa qb ob : Word) : Nat → Mem → Word → Bool → Mem × Bool
  | 0, m, _, c => (m, c)
  | r + 1, m, i, c =>
    let s := chStep sub (m.arr64 TA)[(qa + i).toNat]! (m.arr64 TB)[(qb + i).toNat]! c
    ch2Rows sub TA TB TO qa qb ob r (m.set64 TO (ob + i) s.1) (i + 1) s.2

theorem ch2Rows_succ (sub : Bool) (TA TB TO : TieredArray) (qa qb ob : Word) :
    ∀ (r : Nat) (m : Mem) (i : Word) (c : Bool), ch2Rows sub TA TB TO qa qb ob (r + 1) m i c =
      let R := ch2Rows sub TA TB TO qa qb ob r m i c
      let s := chStep sub (R.1.arr64 TA)[(qa + (i + UInt64.ofNat r)).toNat]!
        (R.1.arr64 TB)[(qb + (i + UInt64.ofNat r)).toNat]! R.2
      (R.1.set64 TO (ob + (i + UInt64.ofNat r)) s.1, s.2)
  | 0, m, i, c => by simp [ch2Rows]
  | r + 1, m, i, c => by
    rw [ch2Rows, ch2Rows_succ sub TA TB TO qa qb ob r, ch2Rows]
    have e : i + 1 + UInt64.ofNat r = i + UInt64.ofNat (r + 1) := by
      rw [UInt64.add_assoc, UInt64.ofNat_add, UInt64.add_comm 1]; rfl
    simp only [e]

theorem cfN_bw {st : StatusFlags} {c : Bool} (h : st.cf = c) : cfN st = (bw c).toNat := by
  unfold cfN bw; rw [h]; cases c <;> rfl

theorem cfW_bw {st : StatusFlags} {c : Bool} (h : st.cf = c) : cfW st = (bw c).toBitVec := by
  unfold cfW bw; rw [h]; cases c <;> rfl

/-- `adc`/`sbb rax, [b + 8 i]` with the carry `c` in the flag: the model's limb and carry. -/
theorem ev_chOp [Host] {k : Nat} {s : MachineData} {Q : MachineState → Prop} {sub : Bool} {b i : Reg64}
    (hk : Host.prog[k]? = some (chOp sub .rax (mbi b i .W64)))
    {v : Word} (hv : rdW s.dmem (s.regs.get64 b + s.regs.get64 i * 8) = some v) {c : Bool} (hcf : s.status.cf = c)
    (h : ∀ st : StatusFlags, st.cf = (chStep sub s.regs.rax v c).2 →
      Ev Q { s with regs := s.regs.set64 .rax (chStep sub s.regs.rax v c).1.toBitVec, status := st }
        (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  cases sub
  · refine ev_adcRS hk hv fun st hst => ?_
    have e : (chStep false s.regs.rax v c).1.toBitVec = s.regs.get64 .rax + v.toBitVec + cfW s.status := by
      rw [cfW_bw hcf]; rfl
    have := h st (by rw [hst, cfN_bw hcf]; rfl)
    rwa [e] at this
  · refine ev_sbbRS hk hv fun st hst => ?_
    have e : (chStep true s.regs.rax v c).1.toBitVec = s.regs.get64 .rax - v.toBitVec - cfW s.status := by
      rw [cfW_bw hcf]; rfl
    have := h st (by rw [hst, cfN_bw hcf]; rfl)
    rwa [e] at this

/-- **What the L function must do**: with the carry in `c ≤ 1`, at fuel `F > n`, when `n = 0` or
the windows lie in their tiers, the run returns the model's carry and memory. -/
def Chain2Spec (p : Prog) (f : FnName) (sub : Bool) : Prop :=
  ∀ (σ : St) (o oa ob n : Word) (c : Bool) (F : Nat), n.toNat < F →
    (n = 0 ∨ ((oa &&& idxMask).toNat + n.toNat ≤ (σ.mem.arr64 (tierA 0 (oa >>> 40))).size ∧
      (ob &&& idxMask).toNat + n.toNat ≤ (σ.mem.arr64 (tierA 0 (ob >>> 40))).size ∧
      (o &&& idxMask).toNat + n.toNat ≤ (σ.mem.arr64 (tierA 0 (o >>> 40))).size ∧
      (σ.mem.arr64 (tierA 0 (oa >>> 40))).size < 2 ^ 64 ∧ (σ.mem.arr64 (tierA 0 (ob >>> 40))).size < 2 ^ 64 ∧
      (σ.mem.arr64 (tierA 0 (o >>> 40))).size < 2 ^ 64)) →
    (invoke p (exec p F) f [o, oa, ob, n, bw c]).run σ =
      let R := ch2Rows sub (tierA 0 (oa >>> 40)) (tierA 0 (ob >>> 40)) (tierA 0 (o >>> 40))
        (oa &&& idxMask) (ob &&& idxMask) (o &&& idxMask) n.toNat σ.mem 0 c
      .ok ([bw R.2], { σ with mem := R.1 })

/-- A `ret` from a state that kept the entry state's frame: the return address is where it was. -/
theorem frame_ret [Host] {G : L.Compiler.Layout} (hG : G.Ok) {d s : MachineData} {ra : Word} {k : Nat}
    {Q : MachineState → Prop} (hra : rdW d.dmem (A d.regs.rsp.toNat) = some ra)
    (hlo : G.lo ≤ d.regs.rsp.toNat) (hhi : d.regs.rsp.toNat + 8 ≤ G.hi) (hF : MrFr G d s)
    (hk : Host.prog[k]? = some (i64 .ret))
    (hc : ∀ s', s'.dmem = s.dmem → s'.regs.rsp.toNat = d.regs.rsp.toNat + 8 → s'.regs.rbp = d.regs.rbp →
      s'.regs.r15 = d.regs.r15 → s'.regs.r14 = s.regs.r14 → s'.regs.rax = s.regs.rax →
      Ev Q s' (Int64.ofBitVec ra.toBitVec)) :
    Ev Q s (at_ k) := by
  have hh := hG.hi_le
  refine ev_ret hk (ra := ra) ?_ ?_
  · have e : d.regs.rsp.toBitVec = A d.regs.rsp.toNat := by simp [A]
    rw [hF.rsp, e, rdW_of_pres hG hF.pres hlo (Nat.le_refl _) hhi]
    exact hra
  · refine hc _ rfl ?_ ?_ ?_ rfl rfl <;>
      simp only [Reg64s.set64_rsp, Reg64s.rsp_mk, Reg64s.rbp_mk, Reg64s.r15_mk, hF.rsp, hF.rbp, hF.r15]
    simp only [UInt64.toNat_ofBitVec, BitVec.toNat_add, UInt64.toNat_toBitVec]
    rw [show (8 : BitVec 64).toNat = 8 from rfl]; omega

section
variable [Host] {G : L.Compiler.Layout} (hG : G.Ok) {kf : Nat} {f : FnName} {sub : Bool}
  (hc : Code (chain2Asm G.tab f sub) kf) {d : MachineData} {Q : MachineState → Prop}
include hG hc

/-- One limb (`.L`), at index `j < n`: the next limb (`hnext`) or, after the last, the carry out
(`hE`). -/
theorem c2_step (TA TB TO : TieredArray) (hTA : G.tab.dom64 TA = true) (hTB : G.tab.dom64 TB = true)
    (hTO : G.tab.dom64 TO = true) (qa qb ob n : Word) (R14 : UInt64) (m0 : Mem) (c0 : Bool)
    (hqa : qa.toNat + n.toNat ≤ G.s (G.tab.pos64 TA)) (hqb : qb.toNat + n.toNat ≤ G.s (G.tab.pos64 TB))
    (hoa : ob.toNat + n.toNat ≤ G.s (G.tab.pos64 TO))
    (s : MachineData) (j : Word) (hF : MrFr G d s)
    (hm : MemRel G (ch2Rows sub TA TB TO qa qb ob j.toNat m0 0 c0).1 s.dmem)
    (hcf : s.status.cf = (ch2Rows sub TA TB TO qa qb ob j.toNat m0 0 c0).2)
    (hrsi : s.regs.rsi = UInt64.ofNat (G.b (G.tab.pos64 TA) + 8 * qa.toNat))
    (hrbx : s.regs.rbx = UInt64.ofNat (G.b (G.tab.pos64 TB) + 8 * qb.toNat))
    (hrdi : s.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TO) + 8 * ob.toNat))
    (hr13 : s.regs.r13 = j) (hrcx : s.regs.rcx = n - j) (hrdx : s.regs.rdx = 0)
    (hr14 : s.regs.r14 = R14) (hj : j.toNat < n.toNat)
    (hnext : ∀ s', MrFr G d s' → MemRel G (ch2Rows sub TA TB TO qa qb ob (j + 1).toNat m0 0 c0).1 s'.dmem →
      s'.status.cf = (ch2Rows sub TA TB TO qa qb ob (j + 1).toNat m0 0 c0).2 →
      s'.regs.rsi = UInt64.ofNat (G.b (G.tab.pos64 TA) + 8 * qa.toNat) →
      s'.regs.rbx = UInt64.ofNat (G.b (G.tab.pos64 TB) + 8 * qb.toNat) →
      s'.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TO) + 8 * ob.toNat) →
      s'.regs.r13 = j + 1 → s'.regs.rcx = n - (j + 1) → s'.regs.rdx = 0 → s'.regs.r14 = R14 →
      (j + 1).toNat < n.toNat → Ev Q s' (at_ (kf + 46)))
    (hE : ∀ s', MrFr G d s' → MemRel G (ch2Rows sub TA TB TO qa qb ob n.toNat m0 0 c0).1 s'.dmem →
      s'.status.cf = (ch2Rows sub TA TB TO qa qb ob n.toNat m0 0 c0).2 → s'.regs.rdx = 0 →
      s'.regs.r14 = R14 → Ev Q s' (at_ (kf + 53))) :
    Ev Q s (at_ (kf + 46)) := by
  have hpA := G.tab.pos64_lt hTA
  have hpB := G.tab.pos64_lt hTB
  have hpO := G.tab.pos64_lt hTO
  have heA := hG.end64 _ hpA
  have heB := hG.end64 _ hpB
  have heO := hG.end64 _ hpO
  generalize hMc : ch2Rows sub TA TB TO qa qb ob j.toNat m0 0 c0 = Mc at hm hcf
  obtain ⟨M, c⟩ := Mc
  simp only at hm hcf
  have hszA := hm.size64 TA hTA
  have hszB := hm.size64 TB hTB
  have hszO := hm.size64 TO hTO
  generalize hBA : G.b (G.tab.pos64 TA) = BA at *
  generalize hBB : G.b (G.tab.pos64 TB) = BB at *
  generalize hBO : G.b (G.tab.pos64 TO) = BO at *
  have hqj : (qa + j).toNat = qa.toNat + j.toNat := L.toNat_add_of_lt _ _ (by omega)
  have hbj : (qb + j).toNat = qb.toNat + j.toNat := L.toNat_add_of_lt _ _ (by omega)
  have hoj : (ob + j).toNat = ob.toNat + j.toNat := L.toNat_add_of_lt _ _ (by omega)
  have hinA : (qa + j).toNat < (M.arr64 TA).size := by rw [hqj, hszA]; omega
  have hinB : (qb + j).toNat < (M.arr64 TB).size := by rw [hbj, hszB]; omega
  have hinO : (ob + j).toNat < (M.arr64 TO).size := by rw [hoj, hszO]; omega
  have haA : s.regs.rsi.toBitVec + s.regs.r13.toBitVec * 8 = A (BA + 8 * (qa + j).toNat) := by
    rw [hrsi, hr13, addr_idx BA qa.toNat j (by omega), hqj]
  have haB : s.regs.rbx.toBitVec + s.regs.r13.toBitVec * 8 = A (BB + 8 * (qb + j).toNat) := by
    rw [hrbx, hr13, addr_idx BB qb.toNat j (by omega), hbj]
  have haO : s.regs.rdi.toBitVec + s.regs.r13.toBitVec * 8 = A (BO + 8 * (ob + j).toNat) := by
    rw [hrdi, hr13, addr_idx BO ob.toNat j (by omega), hoj]
  have hrA : rdW s.dmem (A (BA + 8 * (qa + j).toNat)) = some (M.arr64 TA)[(qa + j).toNat] := by
    have := hm.get64 TA hTA (qa + j).toNat hinA; rw [hBA] at this; exact this
  have hrB : rdW s.dmem (A (BB + 8 * (qb + j).toNat)) = some (M.arr64 TB)[(qb + j).toNat] := by
    have := hm.get64 TB hTB (qb + j).toNat hinB; rw [hBB] at this; exact this
  have hrO : rdW s.dmem (A (BO + 8 * (ob + j).toNat)) = some (M.arr64 TO)[(ob + j).toNat] := by
    have := hm.get64 TO hTO (ob + j).toNat hinO; rw [hBO] at this; exact this
  refine ev_label (c2_code hc (i := 46) rfl) ?_
  refine ev_ldX (c2_code hc (i := 47) rfl) (v := (M.arr64 TA)[(qa + j).toNat]) (by rs; rw [haA]; exact hrA) ?_
  refine ev_chOp (c2_code hc (i := 48) rfl) (v := (M.arr64 TB)[(qb + j).toNat]) (by rs; rw [haB]; exact hrB)
    (c := c) hcf fun st1 hcf1 => ?_
  refine ev_stX (c2_code hc (i := 49) rfl) (by rs; rw [haO, hrO]; rfl) ?_
  refine ev_incR (c2_code hc (i := 50) rfl) fun st2 hcf2 => ?_
  refine ev_decR (c2_code hc (i := 51) rfl) fun st3 hcf3 hzf3 => ?_
  have hj1 : (j + 1).toNat = j.toNat + 1 := L.toNat_add_one_of_lt (by omega)
  have hrow : ch2Rows sub TA TB TO qa qb ob (j + 1).toNat m0 0 c0 =
      (M.set64 TO (ob + j) (chStep sub (M.arr64 TA)[(qa + j).toNat] (M.arr64 TB)[(qb + j).toNat] c).1,
       (chStep sub (M.arr64 TA)[(qa + j).toNat] (M.arr64 TB)[(qb + j).toNat] c).2) := by
    rw [hj1, ch2Rows_succ, hMc, UInt64.zero_add, L.ofNat_toNat]
    simp only [getElem!_pos, hinA, hinB]
  rw [hrow] at hnext
  have hm' := MemRel.store64 hG hm hTO hinO
    (chStep sub (M.arr64 TA)[(qa + j).toNat] (M.arr64 TB)[(qb + j).toNat] c).1
  rw [hBO] at hm'
  have hpres := hF.pres.trans (Pres.store64 hG (top := d.regs.rsp.toNat) (d := s.dmem) hTO
    (j := (ob + j).toNat) (by omega) (chStep sub (M.arr64 TA)[(qa + j).toNat] (M.arr64 TB)[(qb + j).toNat] c).1.toBitVec)
  rw [hBO] at hpres
  have haO' : (UInt64.ofNat (BO + 8 * ob.toNat)).toBitVec + j.toBitVec * 8 = A (BO + 8 * (ob + j).toNat) := by
    have := haO; rw [hrdi, hr13] at this; exact this
  rs [hrcx] at hzf3
  rs at hcf1
  simp only [] at hcf2 hcf3
  have hcnt : (n - j).toBitVec - 1 = (n - (j + 1)).toBitVec := by grind
  refine ev_jcc (c2_code hc (i := 52) rfl) (fun hcc => ?_) (fun hcc => ?_)
  · refine ev_lbl (Code.label hc (i := 46) rfl) ?_
    have hne : (j + 1).toNat < n.toNat := by
      simp only [CondCode.interp, hzf3, Bool.not_eq_true', decide_eq_false_iff_not] at hcc
      rw [hcnt] at hcc
      have : n - (j + 1) ≠ 0 := fun h => hcc (by rw [h]; rfl)
      have h1 := UInt64.toNat_sub_of_le n (j + 1) (UInt64.le_iff_toNat_le.mpr (by omega))
      have h2 := L.toNat_ne_zero_of_ne _ this
      omega
    refine hnext _ ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hne
    all_goals try rs [hF.rsp, hF.rbp, hF.r15, hrsi, hrbx, hrdi, hr13, hrcx, hrdx, hr14]
    · rw [← hr14]; exact hF.r14
    · rw [haO']; exact hpres
    · rw [haO']; exact hm'
    · rw [hcf3, hcf2, hcf1]
    · rfl
    · exact UInt64.toBitVec_inj.mp hcnt
  · have hlast : j + 1 = n := by
      simp only [CondCode.interp, hzf3, Bool.not_eq_false', decide_eq_true_eq] at hcc
      rw [hcnt] at hcc
      have h0 : n - (j + 1) = 0 := UInt64.toBitVec_inj.mp hcc
      have h1 := UInt64.toNat_sub_of_le n (j + 1) (UInt64.le_iff_toNat_le.mpr (by omega))
      rw [h0] at h1
      exact UInt64.toNat_inj.mp (by simp at h1; omega)
    rw [← hlast, hrow] at hE
    refine hE _ ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_
    all_goals try rs [hF.rsp, hF.rbp, hF.r15, hrsi, hrbx, hrdi, hr13, hrcx, hrdx, hr14]
    · rw [← hr14]; exact hF.r14
    · rw [haO']; exact hpres
    · rw [haO']; exact hm'
    · rw [hcf3, hcf2, hcf1]

/-- The limbs from `.L`, by induction on the limbs left. -/
theorem c2_loop (TA TB TO : TieredArray) (hTA : G.tab.dom64 TA = true) (hTB : G.tab.dom64 TB = true)
    (hTO : G.tab.dom64 TO = true) (qa qb ob n : Word) (R14 : UInt64) (m0 : Mem) (c0 : Bool)
    (hqa : qa.toNat + n.toNat ≤ G.s (G.tab.pos64 TA)) (hqb : qb.toNat + n.toNat ≤ G.s (G.tab.pos64 TB))
    (hoa : ob.toNat + n.toNat ≤ G.s (G.tab.pos64 TO))
    (hE : ∀ s', MrFr G d s' → MemRel G (ch2Rows sub TA TB TO qa qb ob n.toNat m0 0 c0).1 s'.dmem →
      s'.status.cf = (ch2Rows sub TA TB TO qa qb ob n.toNat m0 0 c0).2 → s'.regs.rdx = 0 →
      s'.regs.r14 = R14 → Ev Q s' (at_ (kf + 53))) :
    ∀ (r : Nat) (s : MachineData) (j : Word), n.toNat = j.toNat + r → MrFr G d s →
      MemRel G (ch2Rows sub TA TB TO qa qb ob j.toNat m0 0 c0).1 s.dmem →
      s.status.cf = (ch2Rows sub TA TB TO qa qb ob j.toNat m0 0 c0).2 →
      s.regs.rsi = UInt64.ofNat (G.b (G.tab.pos64 TA) + 8 * qa.toNat) →
      s.regs.rbx = UInt64.ofNat (G.b (G.tab.pos64 TB) + 8 * qb.toNat) →
      s.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TO) + 8 * ob.toNat) →
      s.regs.r13 = j → s.regs.rcx = n - j → s.regs.rdx = 0 → s.regs.r14 = R14 →
      j.toNat < n.toNat → Ev Q s (at_ (kf + 46)) := by
  intro r
  induction r with
  | zero => intro s j hr _ _ _ _ _ _ _ _ _ _ hj; omega
  | succ r ih =>
    intro s j hr hF hm hcf h1 h2 h3 h4 h5 h6 h7 hj
    refine c2_step hG hc TA TB TO hTA hTB hTO qa qb ob n R14 m0 c0 hqa hqb hoa s j hF hm hcf h1 h2 h3 h4 h5
      h6 h7 hj ?_ hE
    intro s' g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11
    have := n.toNat_lt
    exact ih s' (j + 1) (by rw [L.toNat_add_one_of_lt (by omega)]; omega) g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11

end

end L.AsmEsc

namespace L.AsmEsc

open L L.Arena L.Compiler

theorem resOut_zero' {G : L.Compiler.Layout} {s : MachineData} {w : Word} (h : s.regs.rax = w) :
    ResOut G 1 [w] s :=
  ⟨fun i hi _ => by
    obtain rfl : i = 0 := by omega
    exact h, fun i h6 h1 => absurd h1 (by simp [maxRes] at h6; omega), by simp⟩

theorem bw_of_le_one {w : Word} (h : ¬ 1 < w) : bw (w == 1) = w := by
  by_cases h1 : w = 1
  · subst h1; rfl
  · have : w = 0 := by
      have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp h)
      have h1' : w.toNat ≠ 1 := fun e => h1 (UInt64.toNat_inj.mp e)
      have e1 : (1 : Word).toNat = 1 := rfl
      exact UInt64.toNat_inj.mp (by simp; omega)
    subst this; rfl

/-- **The template meets the compiler's per-function contract**, for any L function `f` with five
parameters and one result whose run is the model (`Chain2Spec`), in any table where `POOL` (0)
is a tiered word array with small descriptor offsets, at every fuel. -/
theorem chain2Asm_sim [Host] (p : Prog) (G : L.Compiler.Layout) (hG : G.Ok) (f : FnName) (sub : Bool)
    (fd : FunDecl) (hspec : Chain2Spec p f sub) (hnp : fd.nparams = 5) (hnr : Stmt.nret fd.body = 1)
    (hdom : G.tab.dom64 (tier1 0) = true)
    (hoffL : SmallOff (G.tab.len64 (0 : ArrId))) (hoffB : SmallOff (G.tab.base64 (0 : ArrId)))
    (kf : Nat) (hc : Code (chain2Asm G.tab f sub) kf) (sk : NTree) (n : Nat) :
    FnSimAt p G sk n f fd kf := by
  intro vs σ d ra Q hlen hra hargs hlo8 hhi h15 hmem h14 hok herr habrt hexh
  have hlo : G.lo ≤ d.regs.rsp.toNat := by omega
  rw [hnp] at hlen
  obtain ⟨o, oa, ob, nn, cw, rfl⟩ : ∃ o oa ob nn cw, vs = [o, oa, ob, nn, cw] := by
    match vs, hlen with
    | [o, oa, ob, nn, cw], _ => exact ⟨o, oa, ob, nn, cw, rfl⟩
  have hA := hargs.1 (by simp [argRegs])
  have hrdi : d.regs.rdi = o := UInt64.toBitVec_inj.mp (hA 0 (by simp))
  have hr8 : d.regs.r8 = oa := UInt64.toBitVec_inj.mp (hA 1 (by simp))
  have hr9 : d.regs.r9 = ob := UInt64.toBitVec_inj.mp (hA 2 (by simp))
  have hr10 : d.regs.r10 = nn := UInt64.toBitVec_inj.mp (hA 3 (by simp))
  have hr11 : d.regs.r11 = cw := UInt64.toBitVec_inj.mp (hA 4 (by simp))
  have hn0 : 0 < n := by omega
  have hh := hG.hi_le
  refine ev_label (c2_code hc (i := 0) rfl) ?_
  refine ev_cmpRO (c2_code hc (i := 1) rfl) (v := 1) (Or.inl rfl) ?_
  refine ev_jcc (c2_code hc (i := 2) rfl) (fun hcc => ?_) (fun hcc => ?_)
  · exact hexh _ ⟨rfl, Pres.refl _ _⟩
  have hc1 : ¬ 1 < cw := by
    intro h
    simp only [CondCode.interp, cmpFlags_cf, cmpFlags_zf, Bool.and_eq_false_iff, Bool.not_eq_false',
      decide_eq_true_eq, beq_iff_eq] at hcc
    rs [hr11] at hcc
    rcases hcc with h' | h'
    · exact absurd (UInt64.lt_iff_toNat_lt.mpr h') (UInt64.not_lt.mpr (UInt64.le_of_lt h))
    · exact absurd (UInt64.toBitVec_inj.mp h') (fun e => by rw [e] at h; exact UInt64.lt_irrefl _ h)
  generalize hcdef : (cw == 1) = c
  have hbw : bw c = cw := by rw [← hcdef]; exact bw_of_le_one hc1
  subst hbw
  refine ev_cmpRO (c2_code hc (i := 3) rfl) (v := 0) (Or.inl rfl) ?_
  refine ev_jcc (c2_code hc (i := 4) rfl) (fun hcc => ?_) (fun hcc => ?_)
  · -- `n = 0`: return the carry
    simp only [CondCode.interp, cmpFlags_zf, beq_iff_eq] at hcc
    rs [hr10] at hcc
    have hn0' : nn = 0 := UInt64.toBitVec_inj.mp hcc
    subst hn0'
    refine ev_lbl (Code.label hc (i := 56) rfl) ?_
    refine ev_label (c2_code hc (i := 56) rfl) ?_
    refine ev_movRR (c2_code hc (i := 57) rfl) ?_
    refine frame_ret hG hra hlo hhi ⟨rfl, rfl, rfl, Nat.le_refl _, Pres.refl _ _⟩ (c2_code hc (i := 58) rfl)
      fun s' e1 e2 e3 e4 e5 e6 => ?_
    have hrun := hspec σ o oa ob 0 c n (by simp; omega) (Or.inl rfl)
    simp only [UInt64.toNat_zero, ch2Rows] at hrun
    refine hok [bw c] σ s' (by rw [hrun]) (by rw [e1]; exact hmem) rfl e2 e3 e4
      (by rw [e5]; rs; exact Nat.le_refl _) ?_ (by rw [e1]; exact Pres.refl _ _)
    rw [hnr]; exact resOut_zero' (by rw [e6]; rs [hr11])
  simp only [CondCode.interp, cmpFlags_zf, beq_eq_false_iff_ne] at hcc
  rs [hr10] at hcc
  have hnz : nn ≠ 0 := fun h => hcc (by rw [h])
  refine ev_movRI (c2_code hc (i := 5) rfl) ?_
  refine ev_movRR (c2_code hc (i := 6) rfl) ?_
  refine ev_shiftR (n := 40) (op := .shr) (by decide) (Or.inr rfl) (c2_code hc (i := 7) rfl) fun st => ?_
  refine ev_aluRI (op := .and) (w := 1) rfl (c2_code hc (i := 8) rfl) fun st => ?_
  refine ev_aluOp (op := .and) (v := idxMask) rfl (c2_code hc (i := 9) rfl) (Or.inr (Or.inr ⟨.rax, rfl, by rs⟩))
    fun st => ?_
  refine ev_movRR (c2_code hc (i := 10) rfl) ?_
  refine ev_shiftR (n := 40) (op := .shr) (by decide) (Or.inr rfl) (c2_code hc (i := 11) rfl) fun st => ?_
  refine ev_aluRI (op := .and) (w := 1) rfl (c2_code hc (i := 12) rfl) fun st => ?_
  refine ev_aluOp (op := .and) (v := idxMask) rfl (c2_code hc (i := 13) rfl) (Or.inr (Or.inr ⟨.rax, rfl, by rs⟩))
    fun st => ?_
  refine ev_movRR (c2_code hc (i := 14) rfl) ?_
  refine ev_shiftR (n := 40) (op := .shr) (by decide) (Or.inr rfl) (c2_code hc (i := 15) rfl) fun st => ?_
  refine ev_aluRI (op := .and) (w := 1) rfl (c2_code hc (i := 16) rfl) fun st => ?_
  refine ev_aluOp (op := .and) (v := idxMask) rfl (c2_code hc (i := 17) rfl) (Or.inr (Or.inr ⟨.rax, rfl, by rs⟩))
    fun st => ?_
  refine ev_gen (fun s1 => s1.regs.rcx = (o >>> 40) &&& 1 ∧ s1.regs.rdi = o &&& idxMask ∧
      s1.regs.rdx = (oa >>> 40) &&& 1 ∧ s1.regs.r8 = oa &&& idxMask ∧
      s1.regs.r12 = (ob >>> 40) &&& 1 ∧ s1.regs.r9 = ob &&& idxMask ∧ s1.regs.r10 = nn ∧
      s1.regs.r11 = bw c ∧ s1.regs.r14 = d.regs.r14 ∧ s1.regs.r15 = d.regs.r15 ∧
      s1.regs.rsp = d.regs.rsp ∧ s1.regs.rbp = d.regs.rbp ∧ s1.dmem = d.dmem)
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rs [hrdi, hr8, hr9, hr10, hr11, BinOp.eval]
        all_goals rfl)
    fun s1 ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩ => ?_
  have hTA := G.tab.dom64_tierA hdom (oa >>> 40)
  have hTB := G.tab.dom64_tierA hdom (ob >>> 40)
  have hTO := G.tab.dom64_tierA hdom (o >>> 40)
  have heA := hG.end64 _ (G.tab.pos64_lt hTA)
  have heB := hG.end64 _ (G.tab.pos64_lt hTB)
  have heO := hG.end64 _ (G.tab.pos64_lt hTO)
  have hm1 : MemRel G σ.mem s1.dmem := by rw [g13]; exact hmem
  have h15' : s1.regs.r15.toNat = G.T := by rw [g10]; exact h15
  have hdA := pool_desc hm1 hdom (oa >>> 40) (r := .rdx) (by rs [g3]) h15'
  have hdB := pool_desc hm1 hdom (ob >>> 40) (r := .r12) (by rs [g5]) h15'
  have hdO := pool_desc hm1 hdom (o >>> 40) (r := .rcx) (by rs [g1]) h15'
  have hszA := hmem.size64 _ hTA
  have hszB := hmem.size64 _ hTB
  have hszO := hmem.size64 _ hTO
  generalize hSA : G.s (G.tab.pos64 (tierA 0 (oa >>> 40))) = SA at *
  generalize hSB : G.s (G.tab.pos64 (tierA 0 (ob >>> 40))) = SB at *
  generalize hSO : G.s (G.tab.pos64 (tierA 0 (o >>> 40))) = SO at *
  generalize hBA : G.b (G.tab.pos64 (tierA 0 (oa >>> 40))) = BA at *
  generalize hBB : G.b (G.tab.pos64 (tierA 0 (ob >>> 40))) = BB at *
  generalize hBO : G.b (G.tab.pos64 (tierA 0 (o >>> 40))) = BO at *
  have hSAn : (UInt64.ofNat SA).toNat = SA := L.toNat_ofNat_of_lt (by omega)
  have hSBn : (UInt64.ofNat SB).toNat = SB := L.toNat_ofNat_of_lt (by omega)
  have hSOn : (UInt64.ofNat SO).toNat = SO := L.toNat_ofNat_of_lt (by omega)
  have hsub : ∀ (S : Nat) (w : Word), S < 2 ^ 64 → w.toNat ≤ S →
      ((UInt64.ofNat S).toBitVec - w.toBitVec).toNat = S - w.toNat := by
    intro S w h1 h2
    rw [BitVec.toNat_sub, UInt64.toNat_toBitVec, show (UInt64.ofNat S).toBitVec.toNat = S from
      L.toNat_ofNat_of_lt h1]
    have := w.toNat_lt; omega
  have hX : ∀ s', s'.regs.rbp = d.regs.rbp → s'.dmem = s1.dmem → Ev Q s' (label exhaustedL) :=
    fun s' e1 e2 => hexh _ ⟨e1, by rw [e2, g13]; exact Pres.refl _ _⟩
  -- the window of `a`
  refine ev_movRMt (c2_code hc (i := 18) rfl) hoffL (v := UInt64.ofNat SA) hdA.1 ?_
  refine ev_subRR (c2_code hc (i := 19) rfl) fun st hcf => ?_
  rs [g4, hSAn] at hcf
  refine ev_jcc (c2_code hc (i := 20) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc => ?_)
  simp only [CondCode.interp, hcf, decide_eq_false_iff_not, UInt64.toNat_toBitVec, hSAn] at hcc
  refine ev_cmpRO (c2_code hc (i := 21) rfl) (v := nn) (Or.inr (Or.inr ⟨.r10, rfl, by rs [g7]⟩)) ?_
  refine ev_jcc (c2_code hc (i := 22) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc2 => ?_)
  simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not] at hcc2
  rs [g4] at hcc2
  rw [hsub SA _ (by omega) (by omega)] at hcc2
  simp only [UInt64.toNat_toBitVec] at hcc2
  have hqa : (oa &&& idxMask).toNat + nn.toNat ≤ SA := by omega
  refine ev_movRMt (c2_code hc (i := 23) rfl) hoffB (v := UInt64.ofNat BA) (by rs; exact hdA.2) ?_
  refine ev_leaX (c2_code hc (i := 24) rfl) ?_
  -- the window of `b`
  refine ev_movRMt (c2_code hc (i := 25) rfl) hoffL (v := UInt64.ofNat SB) (by rs; exact hdB.1) ?_
  refine ev_subRR (c2_code hc (i := 26) rfl) fun st hcf => ?_
  rs [g6, hSBn] at hcf
  refine ev_jcc (c2_code hc (i := 27) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc3 => ?_)
  simp only [CondCode.interp, hcf, decide_eq_false_iff_not, UInt64.toNat_toBitVec, hSBn] at hcc3
  refine ev_cmpRO (c2_code hc (i := 28) rfl) (v := nn) (Or.inr (Or.inr ⟨.r10, rfl, by rs [g7]⟩)) ?_
  refine ev_jcc (c2_code hc (i := 29) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc4 => ?_)
  simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not] at hcc4
  rs [g6] at hcc4
  rw [hsub SB _ (by omega) (by omega)] at hcc4
  simp only [UInt64.toNat_toBitVec] at hcc4
  have hqb : (ob &&& idxMask).toNat + nn.toNat ≤ SB := by omega
  refine ev_movRMt (c2_code hc (i := 30) rfl) hoffB (v := UInt64.ofNat BB) (by rs; exact hdB.2) ?_
  refine ev_leaX (c2_code hc (i := 31) rfl) ?_
  -- the output window
  refine ev_movRMt (c2_code hc (i := 32) rfl) hoffL (v := UInt64.ofNat SO) (by rs; exact hdO.1) ?_
  refine ev_subRR (c2_code hc (i := 33) rfl) fun st hcf => ?_
  rs [g2, hSOn] at hcf
  refine ev_jcc (c2_code hc (i := 34) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc5 => ?_)
  simp only [CondCode.interp, hcf, decide_eq_false_iff_not, UInt64.toNat_toBitVec, hSOn] at hcc5
  refine ev_cmpRO (c2_code hc (i := 35) rfl) (v := nn) (Or.inr (Or.inr ⟨.r10, rfl, by rs [g7]⟩)) ?_
  refine ev_jcc (c2_code hc (i := 36) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc6 => ?_)
  simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not] at hcc6
  rs [g2] at hcc6
  rw [hsub SO _ (by omega) (by omega)] at hcc6
  simp only [UInt64.toNat_toBitVec] at hcc6
  have hoa : (o &&& idxMask).toNat + nn.toNat ≤ SO := by omega
  refine ev_movRMt (c2_code hc (i := 37) rfl) hoffB (v := UInt64.ofNat BO) (by rs; exact hdO.2) ?_
  refine ev_leaX (c2_code hc (i := 38) rfl) ?_
  -- the fuel
  refine ev_subRR (c2_code hc (i := 39) rfl) fun st hcf => ?_
  rs [g7, g9] at hcf
  refine ev_jcc (c2_code hc (i := 40) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc7 => ?_)
  simp only [CondCode.interp, hcf, decide_eq_false_iff_not, UInt64.toNat_toBitVec] at hcc7
  refine ev_movRI (c2_code hc (i := 41) rfl) ?_
  refine ev_movRR (c2_code hc (i := 42) rfl) ?_
  refine ev_movRI (c2_code hc (i := 43) rfl) ?_
  refine ev_movRR (c2_code hc (i := 44) rfl) ?_
  refine ev_addRIc (c2_code hc (i := 45) rfl) fun st hcf => ?_
  rs [g8] at hcf
  have hcfc : st.cf = c := by rw [hcf]; cases c <;> decide
  have hl14 : nn.toNat ≤ d.regs.r14.toNat := by omega
  have hR14 : (d.regs.r14 - nn).toNat = d.regs.r14.toNat - nn.toNat := UInt64.toNat_sub_of_le _ _
    (UInt64.le_iff_toNat_le.mpr hl14)
  have hnF : nn.toNat < n := by omega
  have hrun := hspec σ o oa ob nn c n hnF (Or.inr ⟨by rw [hszA]; exact hqa, by rw [hszB]; exact hqb,
    by rw [hszO]; exact hoa, by rw [hszA]; omega, by rw [hszB]; omega, by rw [hszO]; omega⟩)
  simp only [] at hrun
  rw [← hSA] at hqa
  rw [← hSB] at hqb
  rw [← hSO] at hoa
  refine c2_loop (d := d) hG hc _ _ _ hTA hTB hTO (oa &&& idxMask) (ob &&& idxMask) (o &&& idxMask) nn
    (d.regs.r14 - nn) σ.mem c hqa hqb hoa ?_ nn.toNat _ 0 (by simp) ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ (by have := L.toNat_ne_zero_of_ne _ hnz; simp only [UInt64.toNat_zero]; omega)
  all_goals try rs [g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13]
  · intro s' fr hm' hcf' hrdx' hr14'
    refine ev_movRI (c2_code hc (i := 53) rfl) ?_
    refine ev_adcRRc (c2_code hc (i := 54) rfl) fun st' _ => ?_
    refine frame_ret hG hra hlo hhi ⟨?_, ?_, ?_, ?_, ?_⟩ (c2_code hc (i := 55) rfl)
      fun s'' e1 e2 e3 e4 e5 e6 => ?_
    all_goals try rs [fr.rsp, fr.rbp, fr.r15]
    · exact fr.r14
    · exact fr.pres
    refine hok _ _ s'' hrun
      (by rw [e1]; exact hm') rfl e2 e3 e4 (by rw [e5]; rs; exact fr.r14) ?_ (by rw [e1]; exact fr.pres)
    rw [hnr]
    refine resOut_zero' ?_
    rw [e6]; rs [hrdx']
    rw [cfW_bw hcf']
    simp
  · show (d.regs.r14 - nn).toNat ≤ _; omega
  · exact Pres.refl _ _
  · simpa [ch2Rows] using hmem
  · simp only [UInt64.toNat_zero, ch2Rows]; exact hcfc
  · apply UInt64.toBitVec_inj.mp
    rw [hBA]
    have := addr_idx BA 0 (oa &&& idxMask) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at this
    rw [this]; rfl
  · apply UInt64.toBitVec_inj.mp
    rw [hBB]
    have := addr_idx BB 0 (ob &&& idxMask) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at this
    rw [this]; rfl
  · apply UInt64.toBitVec_inj.mp
    rw [hBO]
    have := addr_idx BO 0 (o &&& idxMask) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at this
    rw [this]; rfl
  · simp
  · rfl

end L.AsmEsc
