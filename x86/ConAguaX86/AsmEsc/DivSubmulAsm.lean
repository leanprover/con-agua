module

public import ConAguaX86.AsmEsc.Chain2
public import ConAguaX86.AsmEsc.DivSubmulL
import Kraken.X64.Registers

@[expose] public section

/-!
# Hand-written `div_submul` and its simulation contract

`divSubmulAsm tab` is a hand-written body for `div_submul(r, n, ob, q)` (`L.Arena.divSubmul`):
`R := R - q · b` in place on the `n + 1` limbs at `r`, `b` the `n` limbs at `ob`, returning the
borrow out of the top limb (Knuth's step D4). Up front: both windows inside their tiers and below
`2^40` (so that the tagged address `r + i` keeps `r`'s tier, as L's per-limb decode reads it) and
fuel for the row, else `ca_exhausted`. The row is 12 instructions per limb: `mul` from memory,
`add`/`adc` of the carry, `sub`/`adc` of the product from the limb, the store. `divSubmulAsm_sim`
proves the per-function contract (`FnSimAt`) against `divSubmul_run` (`DivSubmulL.lean`).

Registers: `rdi r`, `r8 n`, `r9 ob`, `r10 q`; in the row `rdi` the address of `R[0]`, `rbx` that of
`b[0]`, `r13` the index, `r12` the carry, `rcx` zero.
-/

namespace L.AsmEsc

open L L.Arena L.Compiler

/-- A local label of the hand-written `div_submul`. -/
abbrev dsL (m : String) : Label := ".Lasm_div_submul_" ++ m

/-- The hand-written `div_submul`, for the table `tab` (the descriptor offsets of `POOL` = 0). -/
def divSubmulAsm (tab : Tab) : Program :=
  [ .label (fnL "div_submul"),                                         -- 0
    movRI .rax idxMask,                                                -- 1
    movRR .rcx .rdi,                                                   -- 2
    i64 (.shr (.reg (rr .rcx)) (.imm8 (.int64 (Int64.ofInt 40)))),    -- 3
    i64 (.and (.reg (rr .rcx)) (.imm (.int64 (1 : Word).toInt64))),    -- 4  R tier bit
    i64 (.and (.reg (rr .rdi)) (oR .rax)),                             -- 5  rb
    movRR .rdx .r9,                                                    -- 6
    i64 (.shr (.reg (rr .rdx)) (.imm8 (.int64 (Int64.ofInt 40)))),    -- 7
    i64 (.and (.reg (rr .rdx)) (.imm (.int64 (1 : Word).toInt64))),    -- 8  b tier bit
    i64 (.and (.reg (rr .r9)) (oR .rax)),                              -- 9  qb
    movRR .r11 .rax,                                                   -- 10
    i64 (.sub (.reg (rr .r11)) (oR .rdi)),                             -- 11
    i64 (.cmp (.reg (rr .r11)) (oR .r8)),                              -- 12
    jccL .c exhaustedL,                                                -- 13 rb + n ≥ 2^40
    movRR .r11 .rax,                                                   -- 14
    i64 (.sub (.reg (rr .r11)) (oR .r9)),                              -- 15
    i64 (.cmp (.reg (rr .r11)) (oR .r8)),                              -- 16
    jccL .c exhaustedL,                                                -- 17 qb + n ≥ 2^40
    movRM .rax (tdesc .rcx (tab.len64 (0 : ArrId))),                   -- 18
    i64 (.sub (.reg (rr .rax)) (oR .rdi)),                             -- 19
    jccL .c exhaustedL,                                                -- 20
    i64 (.cmp (.reg (rr .rax)) (oR .r8)),                              -- 21
    jccL .be exhaustedL,                                               -- 22 len - rb ≤ n
    movRM .rcx (tdesc .rcx (tab.base64 (0 : ArrId))),                  -- 23
    i64 (.lea (rr .rdi) (mbi .rcx .rdi .W64)),                         -- 24 rdi := &R[0]
    movRM .rax (tdesc .rdx (tab.len64 (0 : ArrId))),                   -- 25
    i64 (.sub (.reg (rr .rax)) (oR .r9)),                              -- 26
    jccL .c exhaustedL,                                                -- 27
    i64 (.cmp (.reg (rr .rax)) (oR .r8)),                              -- 28
    jccL .c exhaustedL,                                                -- 29 len - qb < n
    movRM .rbx (tdesc .rdx (tab.base64 (0 : ArrId))),                  -- 30
    i64 (.lea (rr .rbx) (mbi .rbx .r9 .W64)),                          -- 31 rbx := &b[0]
    i64 (.sub (.reg (rr .r14)) (oR .r8)),                              -- 32
    jccL .c exhaustedL,                                                -- 33 fuel < n
    movRI .r13 0,                                                      -- 34 i := 0
    movRI .r12 0,                                                      -- 35 c := 0
    movRI .rcx 0,                                                      -- 36
    i64 (.cmp (.reg (rr .r8)) (.imm (.int64 (0 : Word).toInt64))),     -- 37
    jccL .z (dsL "T"),                                                 -- 38 n = 0
    .label (dsL "L"),                                                  -- 39
    movRR .rax .r10,                                                   -- 40
    i64 (.mul (.mem (mbi .rbx .r13 .W64))),                            -- 41 rdx:rax := q * b[i]
    i64 (.add (.reg (rr .rax)) (oR .r12)),                             -- 42 lo := + c
    i64 (.adc (.reg (rr .rdx)) (oR .rcx)),                             -- 43
    movRM .r11 (mbi .rdi .r13 .W64),                                   -- 44 x
    i64 (.sub (.reg (rr .r11)) (oR .rax)),                             -- 45 x - lo
    i64 (.adc (.reg (rr .rdx)) (oR .rcx)),                             -- 46
    movMR (mbi .rdi .r13 .W64) .r11,                                   -- 47
    movRR .r12 .rdx,                                                   -- 48 c := the carry
    i64 (.add (.reg (rr .r13)) (oI 1)),                                -- 49
    i64 (.cmp (.reg (rr .r13)) (oR .r8)),                              -- 50
    jccL .c (dsL "L"),                                                 -- 51
    .label (dsL "T"),                                                  -- 52
    movRM .r11 (mbi .rdi .r13 .W64),                                   -- 53 x := R[n]
    i64 (.sub (.reg (rr .r11)) (oR .r12)),                             -- 54
    movMR (mbi .rdi .r13 .W64) .r11,                                   -- 55
    movRI .rax 0,                                                      -- 56
    i64 (.adc (.reg (rr .rax)) (oR .rcx)),                             -- 57 the borrow
    i64 .ret ]                                                         -- 58

section
variable [Host] {kf : Nat} {tab : Tab}

theorem ds_code (hc : Code (divSubmulAsm tab) kf) {i : Nat} {x : Directive}
    (hi : (divSubmulAsm tab)[i]? = some x) : Host.prog[kf + i]? = some x := Code.get hc hi

end

theorem ds_word (h a b x : Word) :
    ({ toBitVec := (h.toBitVec + 0 + (if decide (2 ^ 64 ≤ a.toNat + b.toNat) = true then 1 else 0)) + 0 +
        (if decide (x.toNat < (a + b).toNat) = true then 1 else 0) } : UInt64) =
      h + Cmp.evalW .ult (a + b) b + Cmp.evalW .ult x (a + b) := by
  rw [carry_eq]; simp only [Cmp.evalW, Cmp.eval, ← UInt64.lt_iff_toNat_lt]
  by_cases h1 : a + b < b <;> by_cases h2 : x < a + b <;> simp [h1, h2] <;> rfl

theorem borrow_word (x c : Word) :
    UInt64.ofBitVec (0 + 0 + (if decide (x.toNat < c.toNat) = true then 1 else 0)) = Cmp.evalW .ult x c := by
  simp only [Cmp.evalW, Cmp.eval, ← UInt64.lt_iff_toNat_lt]
  by_cases h : x < c <;> simp [h] <;> rfl

section
variable [Host] {G : L.Compiler.Layout} (hG : G.Ok) {kf : Nat} (hc : Code (divSubmulAsm G.tab) kf)
  {d : MachineData} {Q : MachineState → Prop}
include hG hc

/-- One step of the row (`.L`), at index `j < n`: the next step (`hnext`) or, after the last, the
top limb (`hT`). -/
theorem ds_row_step (TR TB : TieredArray) (hTR : G.tab.dom64 TR = true) (hTB : G.tab.dom64 TB = true)
    (rb qb q n : Word) (R14 : UInt64) (m0 : Mem)
    (hqa : rb.toNat + n.toNat ≤ G.s (G.tab.pos64 TR)) (hqb : qb.toNat + n.toNat ≤ G.s (G.tab.pos64 TB))
    (s : MachineData) (j : Word) (hF : MrFr G d s)
    (hm : MemRel G (dsRows TR TB rb qb q j.toNat m0 0 0).1 s.dmem)
    (hrdi : s.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TR) + 8 * rb.toNat))
    (hrbx : s.regs.rbx = UInt64.ofNat (G.b (G.tab.pos64 TB) + 8 * qb.toNat))
    (hr8 : s.regs.r8 = n) (hr10 : s.regs.r10 = q) (hr13 : s.regs.r13 = j)
    (hr12 : s.regs.r12 = (dsRows TR TB rb qb q j.toNat m0 0 0).2) (hrcx : s.regs.rcx = 0)
    (hr14 : s.regs.r14 = R14) (hj : j.toNat < n.toNat)
    (hnext : ∀ s', MrFr G d s' → MemRel G (dsRows TR TB rb qb q (j + 1).toNat m0 0 0).1 s'.dmem →
      s'.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TR) + 8 * rb.toNat) →
      s'.regs.rbx = UInt64.ofNat (G.b (G.tab.pos64 TB) + 8 * qb.toNat) →
      s'.regs.r8 = n → s'.regs.r10 = q → s'.regs.r13 = j + 1 →
      s'.regs.r12 = (dsRows TR TB rb qb q (j + 1).toNat m0 0 0).2 → s'.regs.rcx = 0 →
      s'.regs.r14 = R14 → (j + 1).toNat < n.toNat → Ev Q s' (at_ (kf + 39)))
    (hT : ∀ s', MrFr G d s' → MemRel G (dsRows TR TB rb qb q n.toNat m0 0 0).1 s'.dmem →
      s'.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TR) + 8 * rb.toNat) →
      s'.regs.r13 = n → s'.regs.r12 = (dsRows TR TB rb qb q n.toNat m0 0 0).2 → s'.regs.rcx = 0 →
      s'.regs.r14 = R14 → Ev Q s' (at_ (kf + 52))) :
    Ev Q s (at_ (kf + 39)) := by
  have hpA := G.tab.pos64_lt hTR
  have hpB := G.tab.pos64_lt hTB
  have heA := hG.end64 _ hpA
  have heB := hG.end64 _ hpB
  generalize hMc : dsRows TR TB rb qb q j.toNat m0 0 0 = Mc at hm hr12
  obtain ⟨M, c⟩ := Mc
  simp only at hm hr12
  have hszA := hm.size64 TR hTR
  have hszB := hm.size64 TB hTB
  generalize hBA : G.b (G.tab.pos64 TR) = BA at *
  generalize hBB : G.b (G.tab.pos64 TB) = BB at *
  have hqj : (rb + j).toNat = rb.toNat + j.toNat := L.toNat_add_of_lt _ _ (by omega)
  have hbj : (qb + j).toNat = qb.toNat + j.toNat := L.toNat_add_of_lt _ _ (by omega)
  have hinA : (rb + j).toNat < (M.arr64 TR).size := by rw [hqj, hszA]; omega
  have hinB : (qb + j).toNat < (M.arr64 TB).size := by rw [hbj, hszB]; omega
  have haA : s.regs.rdi.toBitVec + s.regs.r13.toBitVec * 8 = A (BA + 8 * (rb + j).toNat) := by
    rw [hrdi, hr13, addr_idx BA rb.toNat j (by omega), hqj]
  have haB : s.regs.rbx.toBitVec + s.regs.r13.toBitVec * 8 = A (BB + 8 * (qb + j).toNat) := by
    rw [hrbx, hr13, addr_idx BB qb.toNat j (by omega), hbj]
  have hrA : rdW s.dmem (A (BA + 8 * (rb + j).toNat)) = some (M.arr64 TR)[(rb + j).toNat] := by
    have := hm.get64 TR hTR (rb + j).toNat hinA; rw [hBA] at this; exact this
  have hrB : rdW s.dmem (A (BB + 8 * (qb + j).toNat)) = some (M.arr64 TB)[(qb + j).toNat] := by
    have := hm.get64 TB hTB (qb + j).toNat hinB; rw [hBB] at this; exact this
  refine ev_label (ds_code hc (i := 39) rfl) ?_
  refine ev_movRR (ds_code hc (i := 40) rfl) ?_
  refine ev_mulS (ds_code hc (i := 41) rfl) (v := (M.arr64 TB)[(qb + j).toNat]) (by rs; rw [haB]; exact hrB)
    fun st1 => ?_
  refine ev_addRR (ds_code hc (i := 42) rfl) fun st2 hcf2 => ?_
  refine ev_adcRR (ds_code hc (i := 43) rfl) fun st3 => ?_
  refine ev_ldX (ds_code hc (i := 44) rfl) (v := (M.arr64 TR)[(rb + j).toNat]) (by rs; rw [haA]; exact hrA) ?_
  refine ev_subRR (ds_code hc (i := 45) rfl) fun st4 hcf4 => ?_
  refine ev_adcRR (ds_code hc (i := 46) rfl) fun st5 => ?_
  refine ev_stX (ds_code hc (i := 47) rfl) (by rs; rw [haA, hrA]; rfl) ?_
  refine ev_movRR (ds_code hc (i := 48) rfl) ?_
  refine ev_addRI (ds_code hc (i := 49) rfl) fun st6 => ?_
  refine ev_cmpRO (ds_code hc (i := 50) rfl) (v := n) (Or.inr (Or.inr ⟨.r8, rfl, by rs [hr8]⟩)) ?_
  have hj1 : (j + 1).toNat = j.toNat + 1 := L.toNat_add_one_of_lt (by omega)
  have hrow : dsRows TR TB rb qb q (j + 1).toNat m0 0 0 = dsStep TR TB rb qb q M j c := by
    rw [hj1, dsRows_succ, hMc, UInt64.zero_add, L.ofNat_toNat]
  have hstep : dsStep TR TB rb qb q M j c =
      (M.set64 TR (rb + j) ((M.arr64 TR)[(rb + j).toNat] - (q * (M.arr64 TB)[(qb + j).toNat] + c)),
       BinOp.mulhi.eval q (M.arr64 TB)[(qb + j).toNat] +
         Cmp.evalW .ult (q * (M.arr64 TB)[(qb + j).toNat] + c) c +
         Cmp.evalW .ult (M.arr64 TR)[(rb + j).toNat] (q * (M.arr64 TB)[(qb + j).toNat] + c)) := by
    simp only [dsStep, getElem!_pos, hinA, hinB]
  rw [hrow, hstep] at hnext
  have hm' := MemRel.store64 hG hm hTR hinA
    ((M.arr64 TR)[(rb + j).toNat] - (q * (M.arr64 TB)[(qb + j).toNat] + c))
  rw [hBA] at hm'
  have hpres := hF.pres.trans (Pres.store64 hG (top := d.regs.rsp.toNat) (d := s.dmem) hTR
    (j := (rb + j).toNat) (by omega)
    ((M.arr64 TR)[(rb + j).toNat] - (q * (M.arr64 TB)[(qb + j).toNat] + c)).toBitVec)
  rw [hBA] at hpres
  rs [hr10, hr12, hr13, hrcx] at hcf2 hcf4
  have haA' : (UInt64.ofNat (BA + 8 * rb.toNat)).toBitVec + j.toBitVec * 8 = A (BA + 8 * (rb + j).toNat) := by
    have := haA; rw [hrdi, hr13] at this; exact this
  have hval : (M.arr64 TR)[(rb + j).toNat].toBitVec - ((q * (M.arr64 TB)[(qb + j).toNat]).toBitVec + c.toBitVec) =
      ((M.arr64 TR)[(rb + j).toNat] - (q * (M.arr64 TB)[(qb + j).toNat] + c)).toBitVec := by
    rw [UInt64.toBitVec_sub, UInt64.toBitVec_add]
  refine ev_jcc (ds_code hc (i := 51) rfl) (fun hcc => ?_) (fun hcc => ?_)
  · refine ev_lbl (Code.label hc (i := 39) rfl) ?_
    refine hnext _ ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals try rs [hF.rsp, hF.rbp, hF.r15, hrdi, hrbx, hr8, hr10, hr12, hr13, hrcx, hr14]
    · rw [← hr14]; exact hF.r14
    · rw [haA', hval]; exact hpres
    · rw [haA', hval]; exact hm'
    · rfl
    · rw [hcf2, hcf4]
      simp only [UInt64.toNat_toBitVec, ← UInt64.toBitVec_add]
      exact ds_word _ _ _ _
    · simp only [CondCode.interp, cmpFlags_cf, decide_eq_true_eq] at hcc
      rs [hr13] at hcc
      exact hcc
  · simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not] at hcc
    rs [hr13] at hcc
    have e1 : (j + 1).toNat = (j.toBitVec + (Int64.ofInt 1).toBitVec).toNat := rfl
    have e2 : n.toNat = n.toBitVec.toNat := rfl
    have hla : j + 1 = n := UInt64.toNat_inj.mp (by omega)
    rw [← hla] at hT
    rw [hrow, hstep] at hT
    refine hT _ ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals try rs [hF.rsp, hF.rbp, hF.r15, hrdi, hrbx, hr8, hr10, hr12, hr13, hrcx, hr14]
    · rw [← hr14]; exact hF.r14
    · rw [haA', hval]; exact hpres
    · rw [haA', hval]; exact hm'
    · rfl
    · rw [hcf2, hcf4]
      simp only [UInt64.toNat_toBitVec, ← UInt64.toBitVec_add]
      exact ds_word _ _ _ _

/-- The row from `.L`, by induction on the steps left. -/
theorem ds_row (TR TB : TieredArray) (hTR : G.tab.dom64 TR = true) (hTB : G.tab.dom64 TB = true)
    (rb qb q n : Word) (R14 : UInt64) (m0 : Mem)
    (hqa : rb.toNat + n.toNat ≤ G.s (G.tab.pos64 TR)) (hqb : qb.toNat + n.toNat ≤ G.s (G.tab.pos64 TB))
    (hT : ∀ s', MrFr G d s' → MemRel G (dsRows TR TB rb qb q n.toNat m0 0 0).1 s'.dmem →
      s'.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TR) + 8 * rb.toNat) →
      s'.regs.r13 = n → s'.regs.r12 = (dsRows TR TB rb qb q n.toNat m0 0 0).2 → s'.regs.rcx = 0 →
      s'.regs.r14 = R14 → Ev Q s' (at_ (kf + 52))) :
    ∀ (r : Nat) (s : MachineData) (j : Word), n.toNat = j.toNat + r → MrFr G d s →
      MemRel G (dsRows TR TB rb qb q j.toNat m0 0 0).1 s.dmem →
      s.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TR) + 8 * rb.toNat) →
      s.regs.rbx = UInt64.ofNat (G.b (G.tab.pos64 TB) + 8 * qb.toNat) →
      s.regs.r8 = n → s.regs.r10 = q → s.regs.r13 = j →
      s.regs.r12 = (dsRows TR TB rb qb q j.toNat m0 0 0).2 → s.regs.rcx = 0 →
      s.regs.r14 = R14 → j.toNat < n.toNat → Ev Q s (at_ (kf + 39)) := by
  intro r
  induction r with
  | zero => intro s j hr _ _ _ _ _ _ _ _ _ _ hj; omega
  | succ r ih =>
    intro s j hr hF hm h1 h2 h3 h4 h5 h6 h7 h8 hj
    refine ds_row_step hG hc TR TB hTR hTB rb qb q n R14 m0 hqa hqb s j hF hm h1 h2 h3 h4 h5 h6 h7 h8 hj ?_ hT
    intro s' g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11
    have := n.toNat_lt
    exact ih s' (j + 1) (by rw [L.toNat_add_one_of_lt (by omega)]; omega) g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11

/-- The top limb (`.T`): `R[n] - c`, the borrow, the return. -/
theorem ds_tail (TR : TieredArray) (hTR : G.tab.dom64 TR = true) (rb n : Word) {ra : Word}
    (hra : rdW d.dmem (A d.regs.rsp.toNat) = some ra) (hlo : G.lo ≤ d.regs.rsp.toNat)
    (hhi : d.regs.rsp.toNat + 8 ≤ G.hi) (hrn : rb.toNat + n.toNat < G.s (G.tab.pos64 TR))
    (s : MachineData) (M : Mem) (c : Word) (hF : MrFr G d s) (hm : MemRel G M s.dmem)
    (hrdi : s.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TR) + 8 * rb.toNat))
    (hr13 : s.regs.r13 = n) (hr12 : s.regs.r12 = c) (hrcx : s.regs.rcx = 0)
    (hok : ∀ s', MemRel G (dsEnd TR rb n M c).1 s'.dmem → s'.regs.rsp.toNat = d.regs.rsp.toNat + 8 →
      s'.regs.rbp = d.regs.rbp → s'.regs.r15 = d.regs.r15 → s'.regs.r14.toNat ≤ d.regs.r14.toNat →
      s'.regs.rax = (dsEnd TR rb n M c).2 → Pres G d.regs.rsp.toNat d.dmem s'.dmem →
      Ev Q s' (Int64.ofBitVec ra.toBitVec)) :
    Ev Q s (at_ (kf + 52)) := by
  have hpA := G.tab.pos64_lt hTR
  have heA := hG.end64 _ hpA
  have hszA := hm.size64 TR hTR
  generalize hBA : G.b (G.tab.pos64 TR) = BA at *
  have hrn' : (rb + n).toNat = rb.toNat + n.toNat := L.toNat_add_of_lt _ _ (by omega)
  have hin : (rb + n).toNat < (M.arr64 TR).size := by rw [hrn', hszA]; omega
  have haA : s.regs.rdi.toBitVec + s.regs.r13.toBitVec * 8 = A (BA + 8 * (rb + n).toNat) := by
    rw [hrdi, hr13, addr_idx BA rb.toNat n (by omega), hrn']
  have hrA : rdW s.dmem (A (BA + 8 * (rb + n).toNat)) = some (M.arr64 TR)[(rb + n).toNat] := by
    have := hm.get64 TR hTR (rb + n).toNat hin; rw [hBA] at this; exact this
  refine ev_label (ds_code hc (i := 52) rfl) ?_
  refine ev_ldX (ds_code hc (i := 53) rfl) (v := (M.arr64 TR)[(rb + n).toNat]) (by rs; rw [haA]; exact hrA) ?_
  refine ev_subRR (ds_code hc (i := 54) rfl) fun st hcf => ?_
  refine ev_stX (ds_code hc (i := 55) rfl) (by rs; rw [haA, hrA]; rfl) ?_
  refine ev_movRI (ds_code hc (i := 56) rfl) ?_
  refine ev_adcRR (ds_code hc (i := 57) rfl) fun st2 => ?_
  have hm' := MemRel.store64 hG hm hTR hin ((M.arr64 TR)[(rb + n).toNat] - c)
  rw [hBA] at hm'
  have hpres := hF.pres.trans (Pres.store64 hG (top := d.regs.rsp.toNat) (d := s.dmem) hTR
    (j := (rb + n).toNat) (by omega) ((M.arr64 TR)[(rb + n).toNat] - c).toBitVec)
  rw [hBA] at hpres
  rs [hr12] at hcf
  have haA' : s.regs.rdi.toBitVec + n.toBitVec * 8 = A (BA + 8 * (rb + n).toNat) := by
    have := haA; rw [hr13] at this; exact this
  refine frame_ret hG hra hlo hhi ⟨?_, ?_, ?_, ?_, ?_⟩ (ds_code hc (i := 58) rfl) fun s' e1 e2 e3 e4 e5 e6 => ?_
  all_goals try rs [hF.rsp, hF.rbp, hF.r15, hr12, hr13, hrcx]
  · exact hF.r14
  · rw [haA']; exact hpres
  · have hE : (dsEnd TR rb n M c).1 = M.set64 TR (rb + n) ((M.arr64 TR)[(rb + n).toNat] - c) := by
      simp only [dsEnd, getElem!_pos, hin]
    refine hok s' (by rw [e1, hE]; rs [hr12, hr13]; rw [haA']; exact hm') e2 e3 e4
      (by rw [e5]; rs; exact hF.r14) ?_ (by rw [e1]; rs [hr12, hr13]; rw [haA']; exact hpres)
    rw [e6]; rs [hrcx]
    rw [hcf]
    simp only [dsEnd, getElem!_pos, hin, UInt64.toNat_toBitVec]
    exact borrow_word _ _

end

end L.AsmEsc

namespace L.AsmEsc

open L L.Arena L.Compiler

/-- **The hand-written `div_submul` meets the compiler's per-function contract**, for any table in
which `POOL` (0) is a tiered word array with small descriptor offsets, at every fuel. -/
theorem divSubmulAsm_sim [Host] (p : Prog) (G : L.Compiler.Layout) (hG : G.Ok)
    (hp : p.lookup "div_submul" = some divSubmul) (hdom : G.tab.dom64 (tier1 0) = true)
    (hoffL : SmallOff (G.tab.len64 (0 : ArrId))) (hoffB : SmallOff (G.tab.base64 (0 : ArrId)))
    (kf : Nat) (hc : Code (divSubmulAsm G.tab) kf) (sk : NTree) (n : Nat) :
    FnSimAt p G sk n "div_submul" divSubmul kf := by
  intro vs σ d ra Q hlen hra hargs hlo8 hhi h15 hmem h14 hok herr habrt hexh
  have hlo : G.lo ≤ d.regs.rsp.toNat := by omega
  rw [divSubmul_nparams] at hlen
  obtain ⟨r, nn, ob, q, rfl⟩ : ∃ r nn ob q, vs = [r, nn, ob, q] := by
    match vs, hlen with
    | [r, nn, ob, q], _ => exact ⟨r, nn, ob, q, rfl⟩
  have hA := hargs.1 (by simp [argRegs])
  have hrdi : d.regs.rdi = r := UInt64.toBitVec_inj.mp (hA 0 (by simp))
  have hr8 : d.regs.r8 = nn := UInt64.toBitVec_inj.mp (hA 1 (by simp))
  have hr9 : d.regs.r9 = ob := UInt64.toBitVec_inj.mp (hA 2 (by simp))
  have hr10 : d.regs.r10 = q := UInt64.toBitVec_inj.mp (hA 3 (by simp))
  have hh := hG.hi_le
  have hnr : Stmt.nret divSubmul.body = 1 := by rw [divSubmul_body]; rfl
  refine ev_label (ds_code hc (i := 0) rfl) ?_
  refine ev_movRI (ds_code hc (i := 1) rfl) ?_
  refine ev_movRR (ds_code hc (i := 2) rfl) ?_
  refine ev_shiftR (n := 40) (op := .shr) (by decide) (Or.inr rfl) (ds_code hc (i := 3) rfl) fun st => ?_
  refine ev_aluRI (op := .and) (w := 1) rfl (ds_code hc (i := 4) rfl) fun st => ?_
  refine ev_aluOp (op := .and) (v := idxMask) rfl (ds_code hc (i := 5) rfl) (Or.inr (Or.inr ⟨.rax, rfl, by rs⟩))
    fun st => ?_
  refine ev_movRR (ds_code hc (i := 6) rfl) ?_
  refine ev_shiftR (n := 40) (op := .shr) (by decide) (Or.inr rfl) (ds_code hc (i := 7) rfl) fun st => ?_
  refine ev_aluRI (op := .and) (w := 1) rfl (ds_code hc (i := 8) rfl) fun st => ?_
  refine ev_aluOp (op := .and) (v := idxMask) rfl (ds_code hc (i := 9) rfl) (Or.inr (Or.inr ⟨.rax, rfl, by rs⟩))
    fun st => ?_
  refine ev_gen (fun s1 => s1.regs.rcx = (r >>> 40) &&& 1 ∧ s1.regs.rdi = r &&& idxMask ∧
      s1.regs.rdx = (ob >>> 40) &&& 1 ∧ s1.regs.r9 = ob &&& idxMask ∧ s1.regs.rax = idxMask ∧
      s1.regs.r8 = nn ∧ s1.regs.r10 = q ∧ s1.regs.r14 = d.regs.r14 ∧ s1.regs.r15 = d.regs.r15 ∧
      s1.regs.rsp = d.regs.rsp ∧ s1.regs.rbp = d.regs.rbp ∧ s1.dmem = d.dmem)
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rs [hrdi, hr8, hr9, hr10, BinOp.eval]
        all_goals rfl)
    fun s1 ⟨g1, g2, g3, g4, g5, g6, g7, g9, g10, g11, g12, g13⟩ => ?_
  have hTR := G.tab.dom64_tierA hdom (r >>> 40)
  have hTB := G.tab.dom64_tierA hdom (ob >>> 40)
  have heA := hG.end64 _ (G.tab.pos64_lt hTR)
  have heB := hG.end64 _ (G.tab.pos64_lt hTB)
  have hm1 : MemRel G σ.mem s1.dmem := by rw [g13]; exact hmem
  have h15' : s1.regs.r15.toNat = G.T := by rw [g10]; exact h15
  have hdA := pool_desc hm1 hdom (r >>> 40) (r := .rcx) (by rs [g1]) h15'
  have hdB := pool_desc hm1 hdom (ob >>> 40) (r := .rdx) (by rs [g3]) h15'
  have hszA := hmem.size64 _ hTR
  have hszB := hmem.size64 _ hTB
  generalize hSA : G.s (G.tab.pos64 (tierA 0 (r >>> 40))) = SA at *
  generalize hSB : G.s (G.tab.pos64 (tierA 0 (ob >>> 40))) = SB at *
  generalize hBA : G.b (G.tab.pos64 (tierA 0 (r >>> 40))) = BA at *
  generalize hBB : G.b (G.tab.pos64 (tierA 0 (ob >>> 40))) = BB at *
  have hSAn : (UInt64.ofNat SA).toNat = SA := L.toNat_ofNat_of_lt (by omega)
  have hSBn : (UInt64.ofNat SB).toNat = SB := L.toNat_ofNat_of_lt (by omega)
  have hsub : ∀ (S : Nat) (w : Word), S < 2 ^ 64 → w.toNat ≤ S →
      ((UInt64.ofNat S).toBitVec - w.toBitVec).toNat = S - w.toNat := by
    intro S w h1 h2
    rw [BitVec.toNat_sub, UInt64.toNat_toBitVec, show (UInt64.ofNat S).toBitVec.toNat = S from
      L.toNat_ofNat_of_lt h1]
    have := w.toNat_lt; omega
  have hrb : (r &&& idxMask).toNat < 2 ^ 40 := by
    rw [UInt64.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hqb : (ob &&& idxMask).toNat < 2 ^ 40 := by
    rw [UInt64.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hmask : (idxMask : Word).toNat = 2 ^ 40 - 1 := rfl
  have hX : ∀ s', s'.regs.rbp = d.regs.rbp → s'.dmem = s1.dmem → Ev Q s' (label exhaustedL) :=
    fun s' e1 e2 => hexh _ ⟨e1, by rw [e2, g13]; exact Pres.refl _ _⟩
  -- the indices stay below `2^40`
  refine ev_movRR (ds_code hc (i := 10) rfl) ?_
  refine ev_subRR (ds_code hc (i := 11) rfl) fun _ _ => ?_
  refine ev_cmpRO (ds_code hc (i := 12) rfl) (v := nn) (Or.inr (Or.inr ⟨.r8, rfl, by rs [g6]⟩)) ?_
  refine ev_jcc (ds_code hc (i := 13) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc1 => ?_)
  simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not] at hcc1
  rs [g2, g5] at hcc1
  rw [BitVec.toNat_sub] at hcc1
  simp only [UInt64.toNat_toBitVec, hmask] at hcc1
  have hr40 : (r &&& idxMask).toNat + nn.toNat < 2 ^ 40 := by omega
  refine ev_movRR (ds_code hc (i := 14) rfl) ?_
  refine ev_subRR (ds_code hc (i := 15) rfl) fun _ _ => ?_
  refine ev_cmpRO (ds_code hc (i := 16) rfl) (v := nn) (Or.inr (Or.inr ⟨.r8, rfl, by rs [g6]⟩)) ?_
  refine ev_jcc (ds_code hc (i := 17) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc2 => ?_)
  simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not] at hcc2
  rs [g4, g5] at hcc2
  rw [BitVec.toNat_sub] at hcc2
  simp only [UInt64.toNat_toBitVec, hmask] at hcc2
  have hb40 : (ob &&& idxMask).toNat + nn.toNat ≤ 2 ^ 40 := by omega
  -- the window of `R` (with its top limb)
  refine ev_movRMt (ds_code hc (i := 18) rfl) hoffL (v := UInt64.ofNat SA) (by rs; exact hdA.1) ?_
  refine ev_subRR (ds_code hc (i := 19) rfl) fun st hcf => ?_
  rs [g2, hSAn] at hcf
  refine ev_jcc (ds_code hc (i := 20) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc3 => ?_)
  simp only [CondCode.interp, hcf, decide_eq_false_iff_not, UInt64.toNat_toBitVec, hSAn] at hcc3
  refine ev_cmpRO (ds_code hc (i := 21) rfl) (v := nn) (Or.inr (Or.inr ⟨.r8, rfl, by rs [g6]⟩)) ?_
  refine ev_jcc (ds_code hc (i := 22) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc4 => ?_)
  simp only [CondCode.interp, cmpFlags_cf, cmpFlags_zf, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    beq_eq_false_iff_ne] at hcc4
  rs [g2] at hcc4
  obtain ⟨hcc4, hcc4'⟩ := hcc4
  rw [hsub SA _ (by omega) (by omega)] at hcc4
  simp only [UInt64.toNat_toBitVec] at hcc4
  have hne : SA - (r &&& idxMask).toNat ≠ nn.toNat := by
    intro e; apply hcc4'
    apply BitVec.eq_of_toNat_eq
    rw [hsub SA _ (by omega) (by omega), e]; rfl
  have hqa : (r &&& idxMask).toNat + nn.toNat < SA := by omega
  refine ev_movRMt (ds_code hc (i := 23) rfl) hoffB (v := UInt64.ofNat BA) (by rs; exact hdA.2) ?_
  refine ev_leaX (ds_code hc (i := 24) rfl) ?_
  -- the window of `b`
  refine ev_movRMt (ds_code hc (i := 25) rfl) hoffL (v := UInt64.ofNat SB) (by rs; exact hdB.1) ?_
  refine ev_subRR (ds_code hc (i := 26) rfl) fun st hcf => ?_
  rs [g4, hSBn] at hcf
  refine ev_jcc (ds_code hc (i := 27) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc5 => ?_)
  simp only [CondCode.interp, hcf, decide_eq_false_iff_not, UInt64.toNat_toBitVec, hSBn] at hcc5
  refine ev_cmpRO (ds_code hc (i := 28) rfl) (v := nn) (Or.inr (Or.inr ⟨.r8, rfl, by rs [g6]⟩)) ?_
  refine ev_jcc (ds_code hc (i := 29) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc6 => ?_)
  simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not] at hcc6
  rs [g4] at hcc6
  rw [hsub SB _ (by omega) (by omega)] at hcc6
  simp only [UInt64.toNat_toBitVec] at hcc6
  have hqb' : (ob &&& idxMask).toNat + nn.toNat ≤ SB := by omega
  refine ev_movRMt (ds_code hc (i := 30) rfl) hoffB (v := UInt64.ofNat BB) (by rs; exact hdB.2) ?_
  refine ev_leaX (ds_code hc (i := 31) rfl) ?_
  -- the fuel
  refine ev_subRR (ds_code hc (i := 32) rfl) fun st hcf => ?_
  rs [g6, g9] at hcf
  refine ev_jcc (ds_code hc (i := 33) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc7 => ?_)
  simp only [CondCode.interp, hcf, decide_eq_false_iff_not, UInt64.toNat_toBitVec] at hcc7
  refine ev_movRI (ds_code hc (i := 34) rfl) ?_
  refine ev_movRI (ds_code hc (i := 35) rfl) ?_
  refine ev_movRI (ds_code hc (i := 36) rfl) ?_
  have hl14 : nn.toNat ≤ d.regs.r14.toNat := by omega
  have hR14 : (d.regs.r14 - nn).toNat = d.regs.r14.toNat - nn.toNat := UInt64.toNat_sub_of_le _ _
    (UInt64.le_iff_toNat_le.mpr hl14)
  have hnF : nn.toNat < n := by omega
  have hrun := divSubmul_run p hp σ r nn ob q n hnF hr40 hb40 (by rw [hszA]; exact hqa)
    (by rw [hszB]; exact hqb')
  simp only [] at hrun
  rw [← hSA] at hqa
  rw [← hSB] at hqb'
  have hT : ∀ s', MrFr G d s' →
      MemRel G (dsRows (tierA 0 (r >>> 40)) (tierA 0 (ob >>> 40)) (r &&& idxMask) (ob &&& idxMask) q nn.toNat
        σ.mem 0 0).1 s'.dmem →
      s'.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 (tierA 0 (r >>> 40))) + 8 * (r &&& idxMask).toNat) →
      s'.regs.r13 = nn →
      s'.regs.r12 = (dsRows (tierA 0 (r >>> 40)) (tierA 0 (ob >>> 40)) (r &&& idxMask) (ob &&& idxMask) q
        nn.toNat σ.mem 0 0).2 → s'.regs.rcx = 0 → s'.regs.r14 = d.regs.r14 - nn → Ev Q s' (at_ (kf + 52)) := by
    intro s' fr hm' hrdi' hr13 hr12 hrcx _
    refine ds_tail hG hc _ hTR (r &&& idxMask) nn hra hlo hhi (by rw [hSA] at *; omega) s' _ _ fr hm' hrdi'
      hr13 hr12 hrcx fun s'' e1 e2 e3 e4 e5 e6 e7 => ?_
    refine hok _ _ s'' hrun e1 rfl e2 e3 e4 e5 ?_ e7
    rw [hnr]; exact resOut_zero' e6
  refine ev_cmpRO (ds_code hc (i := 37) rfl) (v := 0) (Or.inl rfl) ?_
  have hrdi0 : (UInt64.ofNat BA).toBitVec + (r &&& idxMask).toBitVec * 8 =
      (UInt64.ofNat (BA + 8 * (r &&& idxMask).toNat)).toBitVec := by
    have := addr_idx BA 0 (r &&& idxMask) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at this
    rw [this]; rfl
  have hrbx0 : (UInt64.ofNat BB).toBitVec + (ob &&& idxMask).toBitVec * 8 =
      (UInt64.ofNat (BB + 8 * (ob &&& idxMask).toNat)).toBitVec := by
    have := addr_idx BB 0 (ob &&& idxMask) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at this
    rw [this]; rfl
  refine ev_jcc (ds_code hc (i := 38) rfl) (fun hcc => ?_) (fun hcc => ?_)
  · simp only [CondCode.interp, cmpFlags_zf, beq_iff_eq] at hcc
    rs [g6] at hcc
    have hn0 : nn = 0 := UInt64.toBitVec_inj.mp hcc
    subst hn0
    refine ev_lbl (Code.label hc (i := 52) rfl) ?_
    refine hT _ ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals try rs [g1, g2, g3, g4, g5, g6, g7, g9, g10, g11, g12, g13]
    · show (d.regs.r14 - 0).toNat ≤ _; simp
    · exact Pres.refl _ _
    · simpa [dsRows] using hmem
    · apply UInt64.toBitVec_inj.mp; rw [hBA]; exact hrdi0
    · simp [dsRows]
    · rfl
  simp only [CondCode.interp, cmpFlags_zf, beq_eq_false_iff_ne] at hcc
  rs [g6] at hcc
  have hnz : nn ≠ 0 := fun h => hcc (by rw [h])
  refine ds_row (d := d) hG hc _ _ hTR hTB (r &&& idxMask) (ob &&& idxMask) q nn (d.regs.r14 - nn) σ.mem
    (by omega) (by omega) hT nn.toNat _ 0 (by simp) ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (by have := L.toNat_ne_zero_of_ne _ hnz; simp only [UInt64.toNat_zero]; omega)
  all_goals try rs [g1, g2, g3, g4, g5, g6, g7, g9, g10, g11, g12, g13]
  · show (d.regs.r14 - nn).toNat ≤ _; omega
  · exact Pres.refl _ _
  · simpa [dsRows] using hmem
  · apply UInt64.toBitVec_inj.mp; rw [hBA]; exact hrdi0
  · apply UInt64.toBitVec_inj.mp; rw [hBB]; exact hrbx0
  · simp [dsRows]
  · rfl

end L.AsmEsc
