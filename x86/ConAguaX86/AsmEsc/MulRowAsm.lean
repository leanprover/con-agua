module

public import ConAguaX86.AsmEsc.Step
public import ConAguaX86.AsmEsc.MulRowL
import Kraken.X64.Registers

@[expose] public section

/-!
# Hand-written `mul_row` and its simulation contract

`mulRowAsm tab` is a hand-written x64 body for `mul_row(o, n, oa, la, y)` (`L.Arena.mulRow`):
`P[o, o + n) += a * y` for `a = P[oa, oa + la)`. It checks up front that both windows lie in their
tiers and that the fuel covers the row (else `ca_exhausted`, which the contract always allows),
then runs the row with no checks, 11 instructions per limb (`mul`, `add`/`adc` into the
accumulator, the store, the index counting up to `la`), then the carry ripple with L's checks and
fuel per step. `mulRowAsm_sim` proves that it meets the compiler's per-function contract
(`FnSimAt`) against the L code's own semantics (`mulRow_run`, `MulRowL.lean`).

Registers: `rdi o`, `r8 n`, `r9 oa`, `r10 la`, `r11 y` on entry; in the row `rsi` the address of
`a[0]`, `rdi` that of `out[0]`, `r13` the index `i`, `r12` the carry, `rcx` zero (for `adc`), `rbx`
the room `len(out tier) - ob` (the ripple's bound), `rax:rdx` the product.
-/

namespace L.AsmEsc

open L L.Arena L.Compiler

/-- Register-file simplification: writes as structure updates, reads as projections. -/
syntax "rs" ("[" Lean.Parser.Tactic.simpLemma,* "]")? (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| rs $[[$xs,*]]? $[$loc]?) => do
    let xs := xs.map (·.getElems) |>.getD #[]
    `(tactic| simp only [Reg64s.set64_rax, Reg64s.set64_rbx, Reg64s.set64_rcx, Reg64s.set64_rdx,
      Reg64s.set64_rsi, Reg64s.set64_rdi, Reg64s.set64_r8, Reg64s.set64_r9, Reg64s.set64_r10,
      Reg64s.set64_r11, Reg64s.set64_r12, Reg64s.set64_r13, Reg64s.set64_r14,
      Reg64s.rax_mk, Reg64s.rbx_mk, Reg64s.rcx_mk, Reg64s.rdx_mk, Reg64s.rsi_mk, Reg64s.rdi_mk,
      Reg64s.rsp_mk, Reg64s.rbp_mk, Reg64s.r8_mk, Reg64s.r9_mk, Reg64s.r10_mk, Reg64s.r11_mk,
      Reg64s.r12_mk, Reg64s.r13_mk, Reg64s.r14_mk, Reg64s.r15_mk,
      Reg64s.get64_rax, Reg64s.get64_rbx, Reg64s.get64_rcx, Reg64s.get64_rdx, Reg64s.get64_rsi,
      Reg64s.get64_rdi, Reg64s.get64_r8, Reg64s.get64_r9, Reg64s.get64_r10, Reg64s.get64_r11,
      Reg64s.get64_r12, Reg64s.get64_r13, Reg64s.get64_r14, Reg64s.get64_r15,
      UInt64.ofBitVec_toBitVec, $xs,*] $[$loc]?)

/-- A local label of the hand-written `mul_row`. -/
abbrev mrL (m : String) : Label := ".Lasm_mul_row_" ++ m

/-- The hand-written `mul_row`, for the table `tab` (the descriptor offsets of `POOL` = 0). -/
def mulRowAsm (tab : Tab) : Program :=
  [ .label (fnL "mul_row"),                                           -- 0
    i64 (.cmp (.reg (rr .r8)) (oR .r10)),                             -- 1  n - la
    jccL .c errorL,                                                   -- 2  n < la: abort 0
    movRI .r12 0,                                                     -- 3  c := 0
    i64 (.cmp (.reg (rr .r10)) (.imm (.int64 (0 : Word).toInt64))),   -- 4
    jccL .z (mrL "R"),                                                -- 5  la = 0: return
    movRR .rcx .rdi,                                                  -- 6
    i64 (.shr (.reg (rr .rcx)) (.imm8 (.int64 (Int64.ofInt 40)))),   -- 7
    i64 (.and (.reg (rr .rcx)) (.imm (.int64 (1 : Word).toInt64))),   -- 8  rcx := out tier bit
    movRI .rax idxMask,                                               -- 9
    i64 (.and (.reg (rr .rdi)) (oR .rax)),                            -- 10 rdi := ob
    movRR .rdx .r9,                                                   -- 11
    i64 (.shr (.reg (rr .rdx)) (.imm8 (.int64 (Int64.ofInt 40)))),   -- 12
    i64 (.and (.reg (rr .rdx)) (.imm (.int64 (1 : Word).toInt64))),   -- 13 rdx := a tier bit
    i64 (.and (.reg (rr .r9)) (oR .rax)),                             -- 14 r9 := qb
    movRM .rax (tdesc .rdx (tab.len64 (0 : ArrId))),                            -- 15 len(a tier)
    i64 (.sub (.reg (rr .rax)) (oR .r9)),                             -- 16
    jccL .c exhaustedL,                                               -- 17 qb > len
    i64 (.cmp (.reg (rr .rax)) (oR .r10)),                            -- 18
    jccL .c exhaustedL,                                               -- 19 len - qb < la
    movRM .rsi (tdesc .rdx (tab.base64 (0 : ArrId))),                           -- 20
    i64 (.lea (rr .rsi) (mbi .rsi .r9 .W64)),                         -- 21 rsi := &a[qb]
    movRM .rbx (tdesc .rcx (tab.len64 (0 : ArrId))),                            -- 22 len(out tier)
    i64 (.sub (.reg (rr .rbx)) (oR .rdi)),                            -- 23
    jccL .c exhaustedL,                                               -- 24 ob > len
    i64 (.cmp (.reg (rr .rbx)) (oR .r10)),                            -- 25
    jccL .c exhaustedL,                                               -- 26 len - ob < la
    movRM .rcx (tdesc .rcx (tab.base64 (0 : ArrId))),                           -- 27
    i64 (.lea (rr .rdi) (mbi .rcx .rdi .W64)),                        -- 28 rdi := &out[ob]
    i64 (.sub (.reg (rr .r14)) (oR .r10)),                            -- 29
    jccL .c exhaustedL,                                               -- 30 fuel < la
    movRI .r13 0,                                                     -- 31 i := 0
    movRI .rcx 0,                                                     -- 32
    .label (mrL "L"),                                                 -- 33
    movRM .rax (mbi .rsi .r13 .W64),                                  -- 34 x
    i64 (.mul (.reg (rr .r11))),                                      -- 35 rdx:rax := x * y
    i64 (.add (.reg (rr .rax)) (oM (mbi .rdi .r13 .W64))),            -- 36 + t
    i64 (.adc (.reg (rr .rdx)) (oR .rcx)),                            -- 37
    i64 (.add (.reg (rr .rax)) (oR .r12)),                            -- 38 + c
    i64 (.adc (.reg (rr .rdx)) (oR .rcx)),                            -- 39
    movMR (mbi .rdi .r13 .W64) .rax,                                  -- 40 out[i] := lo
    movRR .r12 .rdx,                                                  -- 41 c := hi
    i64 (.add (.reg (rr .r13)) (oI 1)),                               -- 42
    i64 (.cmp (.reg (rr .r13)) (oR .r10)),                            -- 43
    jccL .c (mrL "L"),                                                -- 44
    .label (mrL "T"),                                                 -- 45
    i64 (.cmp (.reg (rr .r12)) (.imm (.int64 (0 : Word).toInt64))),   -- 46
    jccL .z (mrL "R"),                                                -- 47 c = 0: done
    i64 (.cmp (.reg (rr .r8)) (oR .r13)),                             -- 48
    jccL .be errorL,                                                  -- 49 n ≤ i: abort 0
    i64 (.cmp (.reg (rr .r13)) (oR .rbx)),                            -- 50
    jccL .nc errorL,                                                  -- 51 ob + i ≥ len: oob
    movRM .rax (mbi .rdi .r13 .W64),                                  -- 52
    i64 (.add (.reg (rr .rax)) (oR .r12)),                            -- 53 t := out[i] + c
    movMR (mbi .rdi .r13 .W64) .rax,                                  -- 54
    movRI .r12 0,                                                     -- 55
    i64 (.adc (.reg (rr .r12)) (oR .rcx)),                            -- 56 c := u64(t < c)
    i64 (.add (.reg (rr .r13)) (oI 1)),                               -- 57
    i64 (.sub (.reg (rr .r14)) (oI 1)),                               -- 58
    jccL .c exhaustedL,                                               -- 59
    jmpL (mrL "T"),                                                   -- 60
    .label (mrL "R"),                                                 -- 61
    movRI .rax 0,                                                     -- 62
    i64 .ret ]                                                        -- 63

section
variable [Host] {kf : Nat} {tab : Tab}

theorem mr_code (hc : Code (mulRowAsm tab) kf) {i : Nat} {x : Directive}
    (hi : (mulRowAsm tab)[i]? = some x) : Host.prog[kf + i]? = some x := Code.get hc hi

end

/-! ## Words -/

theorem carry_eq (a b : Word) : decide (2 ^ 64 ≤ a.toNat + b.toNat) = decide (a + b < b) := by
  have ha := a.toNat_lt; have hb := b.toNat_lt
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, UInt64.lt_iff_toNat_lt, UInt64.toNat_add]
  constructor
  · intro h; rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]; omega
  · intro h
    rcases Nat.lt_or_ge (a.toNat + b.toNat) (2 ^ 64) with h' | h'
    · rw [Nat.mod_eq_of_lt h'] at h; omega
    · exact h'

theorem adc_word (h a b : Word) :
    UInt64.ofBitVec (h.toBitVec + 0 + (if decide (2 ^ 64 ≤ a.toNat + b.toNat) then 1 else 0)) =
      h + Cmp.evalW .ult (a + b) b := by
  rw [carry_eq]; simp only [Cmp.evalW, Cmp.eval]
  by_cases hc : a + b < b <;> simp [hc] <;> rfl

theorem adc2_word (h a b c : Word) :
    ({ toBitVec := (h.toBitVec + 0 + (if decide (2 ^ 64 ≤ a.toNat + b.toNat) = true then 1 else 0)) + 0 +
        (if decide (2 ^ 64 ≤ (a + b).toNat + c.toNat) = true then 1 else 0) } : UInt64) =
      h + Cmp.evalW .ult (a + b) b + Cmp.evalW .ult (a + b + c) c := by
  rw [carry_eq, carry_eq]; simp only [Cmp.evalW, Cmp.eval]
  by_cases h1 : a + b < b <;> by_cases h2 : a + b + c < c <;> simp [h1, h2] <;> rfl

theorem carry_word (a b : Word) :
    UInt64.ofBitVec (0 + 0 + (if decide (2 ^ 64 ≤ a.toNat + b.toNat) then 1 else 0)) = Cmp.evalW .ult (a + b) b := by
  rw [carry_eq]; simp only [Cmp.evalW, Cmp.eval]
  by_cases h : a + b < b <;> simp [h] <;> rfl

theorem addr_idx (B j : Nat) (i : Word) (h : B + 8 * j + 8 * i.toNat < 2 ^ 64) :
    (UInt64.ofNat (B + 8 * j)).toBitVec + i.toBitVec * 8 = A (B + 8 * (j + i.toNat)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, UInt64.toNat_toBitVec, BitVec.toNat_ofNat, A]
  rw [L.toNat_ofNat_of_lt (by omega)]
  have := i.toNat_lt
  rw [show (8 : BitVec 64).toNat = 8 from rfl, Nat.mod_eq_of_lt (a := i.toNat * 8) (by omega)]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega

/-- A checkpoint: forget the shape of the state, keep `P` of it. -/
theorem ev_gen [Host] {Q : MachineState → Prop} {s : MachineData} {pc : Int64} (P : MachineData → Prop)
    (hP : P s) (h : ∀ s', P s' → Ev Q s' pc) : Ev Q s pc := h s hP

theorem ev_lbl [Host] {Q : MachineState → Prop} {s : MachineData} {l : Label} {k : Nat}
    (hl : label l = at_ k) (h : Ev Q s (at_ k)) : Ev Q s (label l) := hl ▸ h

/-- What the hand-written code keeps of the entry state `d` at every point: the stack and frame
registers, the table, the fuel not increased, and memory changed only in the arrays. -/
structure MrFr (G : L.Compiler.Layout) (d s : MachineData) : Prop where
  rsp : s.regs.rsp = d.regs.rsp
  rbp : s.regs.rbp = d.regs.rbp
  r15 : s.regs.r15 = d.regs.r15
  r14 : s.regs.r14.toNat ≤ d.regs.r14.toNat
  pres : Pres G d.regs.rsp.toNat d.dmem s.dmem

theorem MrFr.gpost {G : L.Compiler.Layout} {d s : MachineData} (h : MrFr G d s) :
    GPost G d.regs.rsp.toNat d s := ⟨h.rbp, h.pres⟩

theorem MrFr.refl (G : L.Compiler.Layout) (d : MachineData) : MrFr G d d :=
  ⟨rfl, rfl, rfl, Nat.le_refl _, Pres.refl _ _⟩

section
variable [Host] {G : L.Compiler.Layout} (hG : G.Ok) {kf : Nat} (hc : Code (mulRowAsm G.tab) kf)
  {d : MachineData} {ra : Word} (hra : rdW d.dmem (A d.regs.rsp.toNat) = some ra)
  (hlo : G.lo ≤ d.regs.rsp.toNat) (hhi : d.regs.rsp.toNat + 8 ≤ G.hi) {Q : MachineState → Prop}
include hG hc hra hlo hhi

/-- The return (`.R`): `rax := 0`, `ret`. -/
theorem mr_ret {s : MachineData} (hF : MrFr G d s)
    (hk : ∀ s', s'.dmem = s.dmem → s'.regs.rsp.toNat = d.regs.rsp.toNat + 8 → s'.regs.rbp = d.regs.rbp →
      s'.regs.r15 = d.regs.r15 → s'.regs.r14 = s.regs.r14 → s'.regs.rax = 0 →
      Ev Q s' (Int64.ofBitVec ra.toBitVec)) :
    Ev Q s (at_ (kf + 61)) := by
  have hh := hG.hi_le
  refine ev_label (mr_code hc (i := 61) rfl) ?_
  refine ev_movRI (mr_code hc (i := 62) rfl) ?_
  refine ev_ret (mr_code hc (i := 63) rfl) (ra := ra) ?_ ?_
  · have e : d.regs.rsp.toBitVec = A d.regs.rsp.toNat := by simp [A]
    simp only [Reg64s.set64_rax, Reg64s.rsp_mk, hF.rsp, e]
    rw [rdW_of_pres hG hF.pres hlo (Nat.le_refl _) hhi]
    exact hra
  · refine hk _ rfl ?_ ?_ ?_ rfl ?_ <;>
      simp only [Reg64s.set64_rax, Reg64s.set64_rsp, Reg64s.rsp_mk, Reg64s.rbp_mk, Reg64s.r15_mk,
        Reg64s.rax_mk, hF.rsp, hF.rbp, hF.r15]
    simp only [UInt64.toNat_ofBitVec, BitVec.toNat_add, UInt64.toNat_toBitVec]
    rw [show (8 : BitVec 64).toNat = 8 from rfl]; omega

/-- One step of the carry ripple (`.T`), from a state with `k` units of L fuel: the exits, or the
next state at `k - 1` (`hnext`). -/
theorem mr_tail_step (TO : TieredArray) (hTO : G.tab.dom64 TO = true) (ob n : Word) (target : Except Err Mem)
    (hob : ob.toNat ≤ G.s (G.tab.pos64 TO))
    (hok : ∀ M s', target = .ok M → MemRel G M s'.dmem → s'.regs.rsp.toNat = d.regs.rsp.toNat + 8 →
      s'.regs.rbp = d.regs.rbp → s'.regs.r15 = d.regs.r15 → s'.regs.r14.toNat ≤ d.regs.r14.toNat →
      s'.regs.rax = 0 → Pres G d.regs.rsp.toNat d.dmem s'.dmem → Ev Q s' (Int64.ofBitVec ra.toBitVec))
    (herr : ∀ s', (∃ x, target = .error x ∧ x.plain) → GPost G d.regs.rsp.toNat d s' → Ev Q s' (label errorL))
    (hexh : ∀ s', GPost G d.regs.rsp.toNat d s' → Ev Q s' (label exhaustedL))
    (k : Nat) (s : MachineData) (M : Mem) (i c : Word) (hF : MrFr G d s) (hm : MemRel G M s.dmem)
    (hrdi : s.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TO) + 8 * ob.toNat))
    (hrbx : s.regs.rbx = UInt64.ofNat (G.s (G.tab.pos64 TO) - ob.toNat)) (hr8 : s.regs.r8 = n)
    (hr13 : s.regs.r13 = i) (hr12 : s.regs.r12 = c) (hrcx : s.regs.rcx = 0)
    (hi : i.toNat ≤ G.s (G.tab.pos64 TO) - ob.toNat) (hk : s.regs.r14.toNat ≤ k)
    (ht : mcLoop TO ob n k M i c = target)
    (hnext : ∀ k', k = k' + 1 → ∀ (s : MachineData) (M : Mem) (i c : Word), MrFr G d s → MemRel G M s.dmem →
      s.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TO) + 8 * ob.toNat) →
      s.regs.rbx = UInt64.ofNat (G.s (G.tab.pos64 TO) - ob.toNat) → s.regs.r8 = n → s.regs.r13 = i →
      s.regs.r12 = c → s.regs.rcx = 0 → i.toNat ≤ G.s (G.tab.pos64 TO) - ob.toNat → s.regs.r14.toNat ≤ k' →
      mcLoop TO ob n k' M i c = target → Ev Q s (at_ (kf + 45))) :
    Ev Q s (at_ (kf + 45)) := by
  have hp := G.tab.pos64_lt hTO
  have hend := hG.end64 _ hp
  have hsz := hm.size64 TO hTO
  generalize hS : G.s (G.tab.pos64 TO) = S at *
  generalize hB : G.b (G.tab.pos64 TO) = B at *
  have hSn : (UInt64.ofNat (S - ob.toNat)).toNat = S - ob.toNat := L.toNat_ofNat_of_lt (by omega)
  refine ev_label (mr_code hc (i := 45) rfl) ?_
  refine ev_cmpRO (mr_code hc (i := 46) rfl) (v := 0) (Or.inl rfl) ?_
  refine ev_jcc (mr_code hc (i := 47) rfl) (fun hcc => ?_) (fun hcc => ?_)
  · -- `c = 0`: return
    simp only [CondCode.interp, cmpFlags_zf, Reg64s.get64_r12, hr12, beq_iff_eq] at hcc
    have hc0 : c = 0 := UInt64.toBitVec_inj.mp hcc
    have ht' : target = .ok M := by rw [← ht, mcLoop, ite_eq_left_iff.mpr (fun h => absurd hc0 h)]
    rw [Code.label hc (i := 61) rfl]
    refine mr_ret hG hc hra hlo hhi ⟨hF.rsp, hF.rbp, hF.r15, hF.r14, hF.pres⟩ fun s' e1 e2 e3 e4 e5 e6 => ?_
    exact hok M s' ht' (by rw [e1]; exact hm) e2 e3 e4 (by rw [e5]; exact hF.r14) e6 (by rw [e1]; exact hF.pres)
  simp only [CondCode.interp, cmpFlags_zf, Reg64s.get64_r12, hr12, beq_eq_false_iff_ne] at hcc
  have hc0 : c ≠ 0 := fun h => hcc (by rw [h])
  refine ev_cmpRO (mr_code hc (i := 48) rfl) (v := i) (Or.inr (Or.inr ⟨.r13, rfl, by rw [Reg64s.get64_r13, hr13]⟩)) ?_
  refine ev_jcc (mr_code hc (i := 49) rfl) (fun hcc => ?_) (fun hcc => ?_)
  · -- `n ≤ i`: abort
    simp only [CondCode.interp, cmpFlags_cf, cmpFlags_zf, Reg64s.get64_r8, hr8, Bool.or_eq_true,
      decide_eq_true_eq, beq_iff_eq, UInt64.toNat_toBitVec] at hcc
    have hni : n ≤ i := by
      rcases hcc with h | h
      · exact UInt64.le_of_lt (UInt64.lt_iff_toNat_lt.mpr h)
      · exact UInt64.le_of_eq (UInt64.toBitVec_inj.mp h)
    refine herr _ ⟨.abort 0, ?_, by simp⟩ ⟨hF.rbp, hF.pres⟩
    rw [← ht, mcLoop]; simp [hc0, hni]
  simp only [CondCode.interp, cmpFlags_cf, cmpFlags_zf, Reg64s.get64_r8, hr8, Bool.or_eq_false_iff,
    decide_eq_false_iff_not, beq_eq_false_iff_ne, UInt64.toNat_toBitVec] at hcc
  have hni : ¬ n ≤ i := by
    intro h
    rcases UInt64.le_iff_lt_or_eq.mp h with h' | h'
    · exact hcc.1 (UInt64.lt_iff_toNat_lt.mp h')
    · exact hcc.2 (by rw [h'])
  refine ev_cmpRO (mr_code hc (i := 50) rfl) (v := UInt64.ofNat (S - ob.toNat))
    (Or.inr (Or.inr ⟨.rbx, rfl, by rw [Reg64s.get64_rbx, hrbx]⟩)) ?_
  have hobi : (ob + i).toNat = ob.toNat + i.toNat := L.toNat_add_of_lt _ _ (by omega)
  refine ev_jcc (mr_code hc (i := 51) rfl) (fun hcc => ?_) (fun hcc => ?_)
  · -- `ob + i ≥ len`: oob
    simp only [CondCode.interp, cmpFlags_cf, Reg64s.get64_r13, hr13, UInt64.toNat_toBitVec, hSn,
      Bool.not_eq_true', decide_eq_false_iff_not] at hcc
    refine herr _ ⟨.oob, ?_, by simp⟩ ⟨hF.rbp, hF.pres⟩
    rw [← ht, mcLoop]
    have : ¬ (ob + i).toNat < (M.arr64 TO).size := by rw [hobi, hsz]; omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc0), ite_eq_right_of_eq_false _ _ (eq_false hni), dite_eq_right_of_eq_false (eq_false this)]
  simp only [CondCode.interp, cmpFlags_cf, Reg64s.get64_r13, hr13, UInt64.toNat_toBitVec, hSn,
    Bool.not_eq_false', decide_eq_true_eq] at hcc
  have hin : (ob + i).toNat < (M.arr64 TO).size := by rw [hobi, hsz]; omega
  have haddr : s.regs.rdi.toBitVec + s.regs.r13.toBitVec * 8 = A (B + 8 * (ob + i).toNat) := by
    rw [hrdi, hr13, addr_idx B ob.toNat i (by omega), hobi]
  have hrd : rdW s.dmem (A (B + 8 * (ob + i).toNat)) = some (M.arr64 TO)[(ob + i).toNat] := by
    have := hm.get64 TO hTO (ob + i).toNat hin
    rw [hB] at this; exact this
  refine ev_ldX (mr_code hc (i := 52) rfl) (v := (M.arr64 TO)[(ob + i).toNat]) (by rs; rw [haddr]; exact hrd) ?_
  refine ev_addRR (mr_code hc (i := 53) rfl) fun st hcf => ?_
  refine ev_stX (mr_code hc (i := 54) rfl) ?_ ?_
  · rs; rw [haddr, hrd]; rfl
  refine ev_movRI (mr_code hc (i := 55) rfl) ?_
  refine ev_adcRR (mr_code hc (i := 56) rfl) fun st2 => ?_
  refine ev_addRI (mr_code hc (i := 57) rfl) fun st3 => ?_
  refine ev_sub1 (mr_code hc (i := 58) rfl) fun st4 hcf4 => ?_
  have hpres : Pres G d.regs.rsp.toNat d.dmem (wrW s.dmem (A (B + 8 * (ob + i).toNat))
      ((M.arr64 TO)[(ob + i).toNat] + c).toBitVec) := by
    have := Pres.store64 hG (top := d.regs.rsp.toNat) (d := s.dmem) hTO (j := (ob + i).toNat) (by omega)
      ((M.arr64 TO)[(ob + i).toNat] + c).toBitVec
    rw [hB] at this
    exact hF.pres.trans this
  refine ev_jcc (mr_code hc (i := 59) rfl) (fun hcc => ?_) (fun hcc => ?_)
  · refine hexh _ ⟨?_, ?_⟩
    · rs [hF.rbp]
    · rs [haddr, hr12]; exact hpres
  -- the fuel was not zero: L has `k - 1` more
  simp only [CondCode.interp] at hcc
  rw [hcf4] at hcc
  rs at hcc
  have h14 : s.regs.r14 ≠ 0 := fun h => by simp [h] at hcc
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by
    have := L.toNat_ne_zero_of_ne _ h14; omega⟩
  refine ev_jmp (mr_code hc (i := 60) rfl) ?_
  refine ev_lbl (Code.label hc (i := 45) rfl) ?_
  have hm' := MemRel.store64 hG hm hTO hin ((M.arr64 TO)[(ob + i).toNat] + c)
  rw [hB] at hm'
  have ht' := ht
  rw [mcLoop, ite_eq_right_of_eq_false _ _ (eq_false hc0), ite_eq_right_of_eq_false _ _ (eq_false hni), dite_eq_left_of_eq_true (eq_true hin)] at ht'
  have hpos : 0 < s.regs.r14.toNat := Nat.pos_of_ne_zero (L.toNat_ne_zero_of_ne _ h14)
  have h14m : ({ toBitVec := s.regs.r14.toBitVec - 1 } : UInt64).toNat = s.regs.r14.toNat - 1 :=
    u64_sub_one_toNat hpos
  have haddr' : (UInt64.ofNat (B + 8 * ob.toNat)).toBitVec + i.toBitVec * 8 = A (B + 8 * (ob + i).toNat) := by
    have := haddr; rw [hrdi, hr13] at this; exact this
  have hval : (M.arr64 TO)[(ob + i).toNat].toBitVec + c.toBitVec = ((M.arr64 TO)[(ob + i).toNat] + c).toBitVec := rfl
  rs [hr12] at hcf
  refine hnext k' rfl _ (M.set64 TO (ob + i) ((M.arr64 TO)[(ob + i).toNat] + c)) (i + 1)
    (Cmp.evalW .ult ((M.arr64 TO)[(ob + i).toNat] + c) c) ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals try rs [hF.rsp, hF.rbp, hF.r15, hrdi, hrbx, hr8, hr13, hr12, hrcx]
  · rw [h14m]; have := hF.r14; omega
  · rw [haddr', hval]; exact hpres
  · rw [haddr', hval]; exact hm'
  · rfl
  · rw [hcf]; exact carry_word _ _
  · rw [L.toNat_add_one_of_lt (by omega)]; omega
  · rw [h14m]; omega
  · exact ht'

omit hra hlo hhi in
/-- One step of the row (`.L`), at index `j < la`: the next step (`hnext`) or, after the last, the
carry ripple (`hT`). -/
theorem mr_row_step (TA TO : TieredArray) (hTA : G.tab.dom64 TA = true) (hTO : G.tab.dom64 TO = true)
    (qb ob y la n X : Word) (R14 : UInt64) (m0 : Mem)
    (hqa : qb.toNat + la.toNat ≤ G.s (G.tab.pos64 TA)) (hoa : ob.toNat + la.toNat ≤ G.s (G.tab.pos64 TO))
    (s : MachineData) (j : Word) (hF : MrFr G d s)
    (hm : MemRel G (mrRows TA TO qb ob y j.toNat m0 0 0).1 s.dmem)
    (hrsi : s.regs.rsi = UInt64.ofNat (G.b (G.tab.pos64 TA) + 8 * qb.toNat))
    (hrdi : s.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TO) + 8 * ob.toNat))
    (hr10 : s.regs.r10 = la) (hr11 : s.regs.r11 = y) (hr13 : s.regs.r13 = j)
    (hr12 : s.regs.r12 = (mrRows TA TO qb ob y j.toNat m0 0 0).2) (hrcx : s.regs.rcx = 0)
    (hrbx : s.regs.rbx = X) (hr8 : s.regs.r8 = n) (hr14 : s.regs.r14 = R14) (hj : j.toNat < la.toNat)
    (hnext : ∀ s', MrFr G d s' → MemRel G (mrRows TA TO qb ob y (j + 1).toNat m0 0 0).1 s'.dmem →
      s'.regs.rsi = UInt64.ofNat (G.b (G.tab.pos64 TA) + 8 * qb.toNat) →
      s'.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TO) + 8 * ob.toNat) →
      s'.regs.r10 = la → s'.regs.r11 = y → s'.regs.r13 = j + 1 →
      s'.regs.r12 = (mrRows TA TO qb ob y (j + 1).toNat m0 0 0).2 → s'.regs.rcx = 0 → s'.regs.rbx = X →
      s'.regs.r8 = n → s'.regs.r14 = R14 → (j + 1).toNat < la.toNat → Ev Q s' (at_ (kf + 33)))
    (hT : ∀ s', MrFr G d s' → MemRel G (mrRows TA TO qb ob y la.toNat m0 0 0).1 s'.dmem →
      s'.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TO) + 8 * ob.toNat) →
      s'.regs.r13 = la → s'.regs.r12 = (mrRows TA TO qb ob y la.toNat m0 0 0).2 → s'.regs.rcx = 0 →
      s'.regs.rbx = X → s'.regs.r8 = n → s'.regs.r14 = R14 → Ev Q s' (at_ (kf + 45))) :
    Ev Q s (at_ (kf + 33)) := by
  have hpA := G.tab.pos64_lt hTA
  have hpO := G.tab.pos64_lt hTO
  have heA := hG.end64 _ hpA
  have heO := hG.end64 _ hpO
  generalize hMc : mrRows TA TO qb ob y j.toNat m0 0 0 = Mc at hm hr12
  obtain ⟨M, c⟩ := Mc
  simp only at hm hr12
  have hszA := hm.size64 TA hTA
  have hszO := hm.size64 TO hTO
  generalize hBA : G.b (G.tab.pos64 TA) = BA at *
  generalize hBO : G.b (G.tab.pos64 TO) = BO at *
  have hqj : (qb + j).toNat = qb.toNat + j.toNat := L.toNat_add_of_lt _ _ (by omega)
  have hoj : (ob + j).toNat = ob.toNat + j.toNat := L.toNat_add_of_lt _ _ (by omega)
  have hinA : (qb + j).toNat < (M.arr64 TA).size := by rw [hqj, hszA]; omega
  have hinO : (ob + j).toNat < (M.arr64 TO).size := by rw [hoj, hszO]; omega
  have haA : s.regs.rsi.toBitVec + s.regs.r13.toBitVec * 8 = A (BA + 8 * (qb + j).toNat) := by
    rw [hrsi, hr13, addr_idx BA qb.toNat j (by omega), hqj]
  have haO : s.regs.rdi.toBitVec + s.regs.r13.toBitVec * 8 = A (BO + 8 * (ob + j).toNat) := by
    rw [hrdi, hr13, addr_idx BO ob.toNat j (by omega), hoj]
  have hrA : rdW s.dmem (A (BA + 8 * (qb + j).toNat)) = some (M.arr64 TA)[(qb + j).toNat] := by
    have := hm.get64 TA hTA (qb + j).toNat hinA; rw [hBA] at this; exact this
  have hrO : rdW s.dmem (A (BO + 8 * (ob + j).toNat)) = some (M.arr64 TO)[(ob + j).toNat] := by
    have := hm.get64 TO hTO (ob + j).toNat hinO; rw [hBO] at this; exact this
  refine ev_label (mr_code hc (i := 33) rfl) ?_
  refine ev_ldX (mr_code hc (i := 34) rfl) (v := (M.arr64 TA)[(qb + j).toNat]) (by rs; rw [haA]; exact hrA) ?_
  refine ev_mulR (mr_code hc (i := 35) rfl) fun st1 => ?_
  refine ev_addRS (mr_code hc (i := 36) rfl) (v := (M.arr64 TO)[(ob + j).toNat]) (by rs; rw [haO]; exact hrO)
    fun st2 hcf2 => ?_
  refine ev_adcRR (mr_code hc (i := 37) rfl) fun st3 => ?_
  refine ev_addRR (mr_code hc (i := 38) rfl) fun st4 hcf4 => ?_
  refine ev_adcRR (mr_code hc (i := 39) rfl) fun st5 => ?_
  refine ev_stX (mr_code hc (i := 40) rfl) (by rs; rw [haO, hrO]; rfl) ?_
  refine ev_movRR (mr_code hc (i := 41) rfl) ?_
  refine ev_addRI (mr_code hc (i := 42) rfl) fun st6 => ?_
  refine ev_cmpRO (mr_code hc (i := 43) rfl) (v := la) (Or.inr (Or.inr ⟨.r10, rfl, by rs [hr10]⟩)) ?_
  have hj1 : (j + 1).toNat = j.toNat + 1 := L.toNat_add_one_of_lt (by omega)
  have hrow : mrRows TA TO qb ob y (j + 1).toNat m0 0 0 = mrStep TA TO qb ob y M j c := by
    rw [hj1, mrRows_succ, hMc, UInt64.zero_add, L.ofNat_toNat]
  have hstep : mrStep TA TO qb ob y M j c =
      (M.set64 TO (ob + j) ((M.arr64 TA)[(qb + j).toNat] * y + (M.arr64 TO)[(ob + j).toNat] + c),
       BinOp.mulhi.eval (M.arr64 TA)[(qb + j).toNat] y +
         Cmp.evalW .ult ((M.arr64 TA)[(qb + j).toNat] * y + (M.arr64 TO)[(ob + j).toNat])
           (M.arr64 TO)[(ob + j).toNat] +
         Cmp.evalW .ult ((M.arr64 TA)[(qb + j).toNat] * y + (M.arr64 TO)[(ob + j).toNat] + c) c) := by
    simp only [mrStep, getElem!_pos, hinA, hinO]
  rw [hrow, hstep] at hnext
  have hm' := MemRel.store64 hG hm hTO hinO
    ((M.arr64 TA)[(qb + j).toNat] * y + (M.arr64 TO)[(ob + j).toNat] + c)
  rw [hBO] at hm'
  have hpres := hF.pres.trans (Pres.store64 hG (top := d.regs.rsp.toNat) (d := s.dmem) hTO
    (j := (ob + j).toNat) (by omega) ((M.arr64 TA)[(qb + j).toNat] * y + (M.arr64 TO)[(ob + j).toNat] + c).toBitVec)
  rw [hBO] at hpres
  rs [hr11, hr12, hr13, hrcx] at hcf2 hcf4
  have haO' : (UInt64.ofNat (BO + 8 * ob.toNat)).toBitVec + j.toBitVec * 8 = A (BO + 8 * (ob + j).toNat) := by
    have := haO; rw [hrdi, hr13] at this; exact this
  have hval : ((M.arr64 TA)[(qb + j).toNat] * y).toBitVec + (M.arr64 TO)[(ob + j).toNat].toBitVec + c.toBitVec =
      ((M.arr64 TA)[(qb + j).toNat] * y + (M.arr64 TO)[(ob + j).toNat] + c).toBitVec := rfl
  refine ev_jcc (mr_code hc (i := 44) rfl) (fun hcc => ?_) (fun hcc => ?_)
  · refine ev_lbl (Code.label hc (i := 33) rfl) ?_
    refine hnext _ ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals try rs [hF.rsp, hF.rbp, hF.r15, hrsi, hrdi, hr10, hr11, hr12, hr13, hrcx, hrbx, hr8, hr14]
    · rw [← hr14]; exact hF.r14
    · rw [haO', hval]; exact hpres
    · rw [haO', hval]; exact hm'
    · rfl
    · rw [hcf2, hcf4]
      simp only [UInt64.toNat_toBitVec, ← UInt64.toBitVec_add]
      exact adc2_word _ _ _ _
    · simp only [CondCode.interp, cmpFlags_cf, decide_eq_true_eq] at hcc
      rs [hr13] at hcc
      exact hcc
    all_goals done
  · simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not] at hcc
    rs [hr13] at hcc
    have e1 : (j + 1).toNat = (j.toBitVec + (Int64.ofInt 1).toBitVec).toNat := rfl
    have e2 : la.toNat = la.toBitVec.toNat := rfl
    have hla : j + 1 = la := UInt64.toNat_inj.mp (by omega)
    rw [← hla] at hT
    rw [hrow, hstep] at hT
    refine hT _ ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals try rs [hF.rsp, hF.rbp, hF.r15, hrsi, hrdi, hr10, hr11, hr12, hr13, hrcx, hrbx, hr8, hr14]
    · rw [← hr14]; exact hF.r14
    · rw [haO', hval]; exact hpres
    · rw [haO', hval]; exact hm'
    · rfl
    · rw [hcf2, hcf4]
      simp only [UInt64.toNat_toBitVec, ← UInt64.toBitVec_add]
      exact adc2_word _ _ _ _
    all_goals done

/-- The carry ripple from `.T`, by induction on L's fuel. -/
theorem mr_tail (TO : TieredArray) (hTO : G.tab.dom64 TO = true) (ob n : Word) (target : Except Err Mem)
    (hob : ob.toNat ≤ G.s (G.tab.pos64 TO))
    (hok : ∀ M s', target = .ok M → MemRel G M s'.dmem → s'.regs.rsp.toNat = d.regs.rsp.toNat + 8 →
      s'.regs.rbp = d.regs.rbp → s'.regs.r15 = d.regs.r15 → s'.regs.r14.toNat ≤ d.regs.r14.toNat →
      s'.regs.rax = 0 → Pres G d.regs.rsp.toNat d.dmem s'.dmem → Ev Q s' (Int64.ofBitVec ra.toBitVec))
    (herr : ∀ s', (∃ x, target = .error x ∧ x.plain) → GPost G d.regs.rsp.toNat d s' → Ev Q s' (label errorL))
    (hexh : ∀ s', GPost G d.regs.rsp.toNat d s' → Ev Q s' (label exhaustedL)) :
    ∀ (k : Nat) (s : MachineData) (M : Mem) (i c : Word), MrFr G d s → MemRel G M s.dmem →
      s.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TO) + 8 * ob.toNat) →
      s.regs.rbx = UInt64.ofNat (G.s (G.tab.pos64 TO) - ob.toNat) → s.regs.r8 = n → s.regs.r13 = i →
      s.regs.r12 = c → s.regs.rcx = 0 → i.toNat ≤ G.s (G.tab.pos64 TO) - ob.toNat → s.regs.r14.toNat ≤ k →
      mcLoop TO ob n k M i c = target → Ev Q s (at_ (kf + 45)) := by
  intro k
  induction k with
  | zero =>
    intro s M i c hF hm h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact mr_tail_step hG hc hra hlo hhi TO hTO ob n target hob hok herr hexh 0 s M i c hF hm h1 h2 h3 h4 h5 h6
      h7 h8 h9 (fun _ h => absurd h (by omega))
  | succ k ih =>
    intro s M i c hF hm h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact mr_tail_step hG hc hra hlo hhi TO hTO ob n target hob hok herr hexh (k + 1) s M i c hF hm h1 h2 h3 h4
      h5 h6 h7 h8 h9 (fun k' hk => by cases hk; exact ih)

omit hra hlo hhi in
/-- The row from `.L`, by induction on the steps left. -/
theorem mr_row (TA TO : TieredArray) (hTA : G.tab.dom64 TA = true) (hTO : G.tab.dom64 TO = true)
    (qb ob y la n X : Word) (R14 : UInt64) (m0 : Mem)
    (hqa : qb.toNat + la.toNat ≤ G.s (G.tab.pos64 TA)) (hoa : ob.toNat + la.toNat ≤ G.s (G.tab.pos64 TO))
    (hT : ∀ s', MrFr G d s' → MemRel G (mrRows TA TO qb ob y la.toNat m0 0 0).1 s'.dmem →
      s'.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TO) + 8 * ob.toNat) →
      s'.regs.r13 = la → s'.regs.r12 = (mrRows TA TO qb ob y la.toNat m0 0 0).2 → s'.regs.rcx = 0 →
      s'.regs.rbx = X → s'.regs.r8 = n → s'.regs.r14 = R14 → Ev Q s' (at_ (kf + 45))) :
    ∀ (r : Nat) (s : MachineData) (j : Word), la.toNat = j.toNat + r → MrFr G d s →
      MemRel G (mrRows TA TO qb ob y j.toNat m0 0 0).1 s.dmem →
      s.regs.rsi = UInt64.ofNat (G.b (G.tab.pos64 TA) + 8 * qb.toNat) →
      s.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TO) + 8 * ob.toNat) →
      s.regs.r10 = la → s.regs.r11 = y → s.regs.r13 = j →
      s.regs.r12 = (mrRows TA TO qb ob y j.toNat m0 0 0).2 → s.regs.rcx = 0 →
      s.regs.rbx = X → s.regs.r8 = n → s.regs.r14 = R14 → j.toNat < la.toNat → Ev Q s (at_ (kf + 33)) := by
  intro r
  induction r with
  | zero => intro s j hr _ _ _ _ _ _ _ _ _ _ _ _ hj; omega
  | succ r ih =>
    intro s j hr hF hm h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hj
    refine mr_row_step hG hc TA TO hTA hTO qb ob y la n X R14 m0 hqa hoa s j hF hm h1 h2 h3 h4 h5
      h6 h7 h8 h9 h10 hj ?_ hT
    intro s' g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13
    have := la.toNat_lt
    exact ih s' (j + 1) (by rw [L.toNat_add_one_of_lt (by omega)]; omega) g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11
      g12 g13

end

theorem mulRow_nret : Stmt.nret mulRow.body = 1 := by rw [mulRow_body]; rfl

theorem resOut_zero {G : L.Compiler.Layout} {s : MachineData} (h : s.regs.rax = 0) : ResOut G 1 [0] s :=
  ⟨fun i hi _ => by
    obtain rfl : i = 0 := by omega
    exact h, fun i h6 h1 => absurd h1 (by simp [maxRes] at h6; omega), by simp⟩

/-- The value of a tier descriptor word of `POOL`, read through the tier bit of `u` in a register. -/
theorem pool_desc [Host] {G : L.Compiler.Layout} {m : Mem} {s : MachineData} (hm : MemRel G m s.dmem)
    (hdom : G.tab.dom64 (tier1 0) = true) (u : Word) {r : Reg64} (hr : s.regs.get64 r = (u &&& 1).toBitVec)
    (h15 : s.regs.r15.toNat = G.T) :
    rdW s.dmem (A (s.regs.r15.toNat + 8 * (s.regs.get64 r).toNat + (G.tab.len64 (0 : ArrId)).toNat)) =
      some (UInt64.ofNat (G.s (G.tab.pos64 (tierA 0 u)))) ∧
    rdW s.dmem (A (s.regs.r15.toNat + 8 * (s.regs.get64 r).toNat + (G.tab.base64 (0 : ArrId)).toNat)) =
      some (UInt64.ofNat (G.b (G.tab.pos64 (tierA 0 u)))) := by
  have hta := G.tab.dom64_tierA hdom u
  have hoff := tier_off G.tab hdom u
  rw [hr, UInt64.toNat_toBitVec, h15]
  constructor
  · rw [show G.T + 8 * (u &&& 1).toNat + (G.tab.len64 (0 : ArrId)).toNat =
      G.T + (G.tab.len64 (tierA 0 u)).toNat by omega]
    exact hm.len64A hta
  · rw [show G.T + 8 * (u &&& 1).toNat + (G.tab.base64 (0 : ArrId)).toNat =
      G.T + (G.tab.base64 (tierA 0 u)).toNat by omega]
    exact hm.base64A hta

/-- **The hand-written `mul_row` meets the compiler's per-function contract**, for any table in
which `POOL` (0) is a tiered word array with small descriptor offsets, at every fuel. -/
theorem mulRowAsm_sim [Host] (p : Prog) (G : L.Compiler.Layout) (hG : G.Ok)
    (hp : p.lookup "mul_row" = some mulRow) (hdom : G.tab.dom64 (tier1 0) = true)
    (hoffL : SmallOff (G.tab.len64 (0 : ArrId))) (hoffB : SmallOff (G.tab.base64 (0 : ArrId)))
    (kf : Nat) (hc : Code (mulRowAsm G.tab) kf) (sk : NTree) (n : Nat) :
    FnSimAt p G sk n "mul_row" mulRow kf := by
  intro vs σ d ra Q hlen hra hargs hlo8 hhi h15 hmem h14 hok herr habrt hexh
  have hlo : G.lo ≤ d.regs.rsp.toNat := by omega
  rw [mulRow_nparams] at hlen
  obtain ⟨o, nn, oa, la, y, rfl⟩ : ∃ o nn oa la y, vs = [o, nn, oa, la, y] := by
    match vs, hlen with
    | [o, nn, oa, la, y], _ => exact ⟨o, nn, oa, la, y, rfl⟩
  have hA := hargs.1 (by simp [argRegs])
  have hrdi : d.regs.rdi = o := UInt64.toBitVec_inj.mp (hA 0 (by simp))
  have hr8 : d.regs.r8 = nn := UInt64.toBitVec_inj.mp (hA 1 (by simp))
  have hr9 : d.regs.r9 = oa := UInt64.toBitVec_inj.mp (hA 2 (by simp))
  have hr10 : d.regs.r10 = la := UInt64.toBitVec_inj.mp (hA 3 (by simp))
  have hr11 : d.regs.r11 = y := UInt64.toBitVec_inj.mp (hA 4 (by simp))
  have hn0 : 0 < n := by omega
  have hh := hG.hi_le
  refine ev_label (mr_code hc (i := 0) rfl) ?_
  refine ev_cmpRO (mr_code hc (i := 1) rfl) (v := la) (Or.inr (Or.inr ⟨.r10, rfl, by rs [hr10]⟩)) ?_
  refine ev_jcc (mr_code hc (i := 2) rfl) (fun hcc => ?_) (fun hcc => ?_)
  · -- `n < la`: abort
    simp only [CondCode.interp, cmpFlags_cf, decide_eq_true_eq] at hcc
    rs [hr8] at hcc
    refine herr _ ⟨.abort 0, ?_, by simp⟩ ⟨rfl, Pres.refl _ _⟩
    exact mulRow_run_abort p hp σ o nn oa la y n hn0 (UInt64.lt_iff_toNat_lt.mpr hcc)
  simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not] at hcc
  rs [hr8] at hcc
  have hnl : ¬ nn < la := fun h => hcc (UInt64.lt_iff_toNat_lt.mp h)
  refine ev_movRI (mr_code hc (i := 3) rfl) ?_
  refine ev_cmpRO (mr_code hc (i := 4) rfl) (v := 0) (Or.inl rfl) ?_
  refine ev_jcc (mr_code hc (i := 5) rfl) (fun hcc => ?_) (fun hcc => ?_)
  · -- `la = 0`: return 0
    simp only [CondCode.interp, cmpFlags_zf, beq_iff_eq] at hcc
    rs [hr10] at hcc
    have hl0 : la = 0 := UInt64.toBitVec_inj.mp hcc
    subst hl0
    refine ev_lbl (Code.label hc (i := 61) rfl) ?_
    refine mr_ret hG hc hra hlo hhi ⟨rfl, rfl, rfl, Nat.le_refl _, Pres.refl _ _⟩ fun s' e1 e2 e3 e4 e5 e6 => ?_
    refine hok [0] σ s' (mulRow_run_zero p hp σ o nn oa y n hn0) (by rw [e1]; exact hmem) rfl e2 e3 e4
      (by rw [e5]; rs; exact Nat.le_refl _) ?_ (by rw [e1]; exact Pres.refl _ _)
    rw [mulRow_nret]; exact resOut_zero e6
  simp only [CondCode.interp, cmpFlags_zf, beq_eq_false_iff_ne] at hcc
  rs [hr10] at hcc
  have hl0 : la ≠ 0 := fun h => hcc (by rw [h])
  refine ev_movRR (mr_code hc (i := 6) rfl) ?_
  refine ev_shiftR (n := 40) (op := .shr) (by decide) (Or.inr rfl) (mr_code hc (i := 7) rfl) fun st => ?_
  refine ev_aluRI (op := .and) (w := 1) rfl (mr_code hc (i := 8) rfl) fun st => ?_
  refine ev_movRI (mr_code hc (i := 9) rfl) ?_
  refine ev_aluOp (op := .and) (v := idxMask) rfl (mr_code hc (i := 10) rfl) (Or.inr (Or.inr ⟨.rax, rfl, by rs⟩))
    fun st => ?_
  refine ev_movRR (mr_code hc (i := 11) rfl) ?_
  refine ev_shiftR (n := 40) (op := .shr) (by decide) (Or.inr rfl) (mr_code hc (i := 12) rfl) fun st => ?_
  refine ev_aluRI (op := .and) (w := 1) rfl (mr_code hc (i := 13) rfl) fun st => ?_
  refine ev_aluOp (op := .and) (v := idxMask) rfl (mr_code hc (i := 14) rfl) (Or.inr (Or.inr ⟨.rax, rfl, by rs⟩))
    fun st => ?_
  refine ev_gen (fun s1 => s1.regs.rcx = (o >>> 40) &&& 1 ∧ s1.regs.rdi = o &&& idxMask ∧
      s1.regs.rdx = (oa >>> 40) &&& 1 ∧ s1.regs.r9 = oa &&& idxMask ∧ s1.regs.r8 = nn ∧ s1.regs.r10 = la ∧
      s1.regs.r11 = y ∧ s1.regs.r12 = 0 ∧ s1.regs.r14 = d.regs.r14 ∧ s1.regs.r15 = d.regs.r15 ∧
      s1.regs.rsp = d.regs.rsp ∧ s1.regs.rbp = d.regs.rbp ∧ s1.dmem = d.dmem)
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rs [hrdi, hr8, hr9, hr10, hr11, BinOp.eval]
        all_goals rfl)
    fun s1 ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩ => ?_
  -- the windows
  have hTA := G.tab.dom64_tierA hdom (oa >>> 40)
  have hTO := G.tab.dom64_tierA hdom (o >>> 40)
  have hpA := G.tab.pos64_lt hTA
  have hpO := G.tab.pos64_lt hTO
  have heA := hG.end64 _ hpA
  have heO := hG.end64 _ hpO
  have hm1 : MemRel G σ.mem s1.dmem := by rw [g13]; exact hmem
  have h15' : s1.regs.r15.toNat = G.T := by rw [g10]; exact h15
  have hdA := pool_desc hm1 hdom (oa >>> 40) (r := .rdx) (by rs [g3]) h15'
  have hdO := pool_desc hm1 hdom (o >>> 40) (r := .rcx) (by rs [g1]) h15'
  have hszA := hmem.size64 _ hTA
  have hszO := hmem.size64 _ hTO
  generalize hSA : G.s (G.tab.pos64 (tierA 0 (oa >>> 40))) = SA at *
  generalize hSO : G.s (G.tab.pos64 (tierA 0 (o >>> 40))) = SO at *
  generalize hBA : G.b (G.tab.pos64 (tierA 0 (oa >>> 40))) = BA at *
  generalize hBO : G.b (G.tab.pos64 (tierA 0 (o >>> 40))) = BO at *
  have hSAn : (UInt64.ofNat SA).toNat = SA := L.toNat_ofNat_of_lt (by omega)
  have hSOn : (UInt64.ofNat SO).toNat = SO := L.toNat_ofNat_of_lt (by omega)
  have hqb : (oa &&& idxMask).toNat < 2 ^ 40 := by
    rw [UInt64.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hob : (o &&& idxMask).toNat < 2 ^ 40 := by
    rw [UInt64.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  refine ev_movRMt (mr_code hc (i := 15) rfl) hoffL (v := UInt64.ofNat SA) hdA.1 ?_
  refine ev_subRR (mr_code hc (i := 16) rfl) fun st hcf => ?_
  rs [g4, hSAn] at hcf
  refine ev_jcc (mr_code hc (i := 17) rfl) (fun hcc => ?_) (fun hcc => ?_)
  · exact hexh _ ⟨by rs [g12], by rw [show _ = s1.dmem from rfl, g13]; exact Pres.refl _ _⟩
  simp only [CondCode.interp, hcf, decide_eq_false_iff_not] at hcc
  refine ev_cmpRO (mr_code hc (i := 18) rfl) (v := la) (Or.inr (Or.inr ⟨.r10, rfl, by rs [g6]⟩)) ?_
  refine ev_jcc (mr_code hc (i := 19) rfl) (fun hcc2 => ?_) (fun hcc2 => ?_)
  · exact hexh _ ⟨by rs [g12], by rw [show _ = s1.dmem from rfl, g13]; exact Pres.refl _ _⟩
  simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not] at hcc2
  rs [g4] at hcc2
  have hsub : ∀ (S : Nat) (w : Word), S < 2 ^ 64 → w.toNat ≤ S →
      ((UInt64.ofNat S).toBitVec - w.toBitVec).toNat = S - w.toNat := by
    intro S w h1 h2
    rw [BitVec.toNat_sub, UInt64.toNat_toBitVec, show (UInt64.ofNat S).toBitVec.toNat = S from
      L.toNat_ofNat_of_lt h1]
    have := w.toNat_lt; omega
  simp only [UInt64.toNat_toBitVec, hSAn] at hcc
  rw [hsub SA _ (by omega) (by omega)] at hcc2
  simp only [UInt64.toNat_toBitVec] at hcc2
  have hqa : (oa &&& idxMask).toNat + la.toNat ≤ SA := by omega
  refine ev_movRMt (mr_code hc (i := 20) rfl) hoffB (v := UInt64.ofNat BA) (by rs; exact hdA.2) ?_
  refine ev_leaX (mr_code hc (i := 21) rfl) ?_
  refine ev_movRMt (mr_code hc (i := 22) rfl) hoffL (v := UInt64.ofNat SO) (by rs; exact hdO.1) ?_
  refine ev_subRR (mr_code hc (i := 23) rfl) fun st2 hcf2 => ?_
  rs [g2, hSOn] at hcf2
  refine ev_jcc (mr_code hc (i := 24) rfl) (fun hcc => ?_) (fun hcc3 => ?_)
  · exact hexh _ ⟨by rs [g12], by rw [show _ = s1.dmem from rfl, g13]; exact Pres.refl _ _⟩
  simp only [CondCode.interp, hcf2, decide_eq_false_iff_not] at hcc3
  simp only [UInt64.toNat_toBitVec, hSOn] at hcc3
  refine ev_cmpRO (mr_code hc (i := 25) rfl) (v := la) (Or.inr (Or.inr ⟨.r10, rfl, by rs [g6]⟩)) ?_
  refine ev_jcc (mr_code hc (i := 26) rfl) (fun hcc => ?_) (fun hcc4 => ?_)
  · exact hexh _ ⟨by rs [g12], by rw [show _ = s1.dmem from rfl, g13]; exact Pres.refl _ _⟩
  simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not] at hcc4
  rs [g2] at hcc4
  rw [hsub SO _ (by omega) (by omega)] at hcc4
  simp only [UInt64.toNat_toBitVec] at hcc4
  have hoa : (o &&& idxMask).toNat + la.toNat ≤ SO := by omega
  refine ev_movRMt (mr_code hc (i := 27) rfl) hoffB (v := UInt64.ofNat BO) (by rs; exact hdO.2) ?_
  refine ev_leaX (mr_code hc (i := 28) rfl) ?_
  refine ev_subRR (mr_code hc (i := 29) rfl) fun st5 hcf5 => ?_
  rs [g6, g9] at hcf5
  refine ev_jcc (mr_code hc (i := 30) rfl) (fun hcc => ?_) (fun hcc5 => ?_)
  · exact hexh _ ⟨by rs [g12], by rw [show _ = s1.dmem from rfl, g13]; exact Pres.refl _ _⟩
  simp only [CondCode.interp, hcf5, decide_eq_false_iff_not, UInt64.toNat_toBitVec] at hcc5
  refine ev_movRI (mr_code hc (i := 31) rfl) ?_
  refine ev_movRI (mr_code hc (i := 32) rfl) ?_
  have hl14 : la.toNat ≤ d.regs.r14.toNat := by omega
  have hR14 : (d.regs.r14 - la).toNat = d.regs.r14.toNat - la.toNat := UInt64.toNat_sub_of_le _ _
    (UInt64.le_iff_toNat_le.mpr hl14)
  have hlaF : la.toNat < n := by omega
  have hrun := mulRow_run p hp σ o nn oa la y n hnl hlaF (by rw [hszA]; exact hqa) (by rw [hszO]; exact hoa)
    (by rw [hszA]; omega) (by rw [hszO]; omega)
  rw [← hSA] at hqa
  rw [← hSO] at hoa hcc3 hcc4 hSOn
  refine mr_row (d := d) hG hc (tierA 0 (oa >>> 40)) (tierA 0 (o >>> 40)) hTA hTO (oa &&& idxMask) (o &&& idxMask) y la
    nn (UInt64.ofNat (G.s (G.tab.pos64 (tierA 0 (o >>> 40))) - (o &&& idxMask).toNat)) (d.regs.r14 - la) σ.mem
    hqa hoa ?_ la.toNat _ 0 (by simp) ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (by have := L.toNat_ne_zero_of_ne _ hl0; simp only [UInt64.toNat_zero]; omega)
  all_goals try rs [g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13]
  · intro s' fr hm' hrdi' hr13 hr12 hrcx hrbx hr8' hr14'
    refine mr_tail hG hc hra hlo hhi (tierA 0 (o >>> 40)) hTO (o &&& idxMask) nn _ (by omega) ?_ ?_ hexh (n - 1)
      s' _ la _ fr hm' hrdi' hrbx hr8' hr13 hr12 hrcx (by omega) (by rw [hr14', hR14]; omega) rfl
    · intro M s'' ht e1 e2 e3 e4 e5 e6 e7
      refine hok [0] { σ with mem := M } s'' (by rw [hrun, ht]; rfl) e1 rfl e2 e3 e4 e5 ?_ e7
      rw [mulRow_nret]; exact resOut_zero e6
    · intro s'' ⟨x, hx, hpl⟩ g
      exact herr s'' ⟨x, by rw [hrun, hx]; rfl, hpl⟩ g
  · show (d.regs.r14 - la).toNat ≤ _; omega
  · exact Pres.refl _ _
  · simpa [mrRows] using hmem
  · apply UInt64.toBitVec_inj.mp
    rw [hBA]
    have := addr_idx BA 0 (oa &&& idxMask) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at this
    rw [this]; rfl
  · apply UInt64.toBitVec_inj.mp
    rw [hBO]
    have := addr_idx BO 0 (o &&& idxMask) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at this
    rw [this]; rfl
  · simp [mrRows]
  · apply UInt64.toNat_inj.mp
    rw [hSO, L.toNat_ofNat_of_lt (by omega)]
    exact hsub SO _ (by omega) (by omega)
  · rfl

end L.AsmEsc
