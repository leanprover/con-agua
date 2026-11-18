module

public import ConAgua.AsmEsc.Chain2
public import ConAgua.AsmEsc.DivSubmulL
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

end

end L.AsmEsc
