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

end

end L.AsmEsc
