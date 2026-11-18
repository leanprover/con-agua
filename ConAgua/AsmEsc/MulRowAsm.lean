module

public import ConAgua.AsmEsc.Step
public import ConAgua.AsmEsc.MulRowL
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
    rw [if_neg hc0, if_neg hni, dif_neg this]
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
  rw [mcLoop, if_neg hc0, if_neg hni, dif_pos hin] at ht'
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

end

end L.AsmEsc
