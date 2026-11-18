module

public import ConAgua.AsmEsc.MulRowAsm
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

end

end L.AsmEsc
