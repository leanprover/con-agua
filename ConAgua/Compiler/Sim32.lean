module

public import ConAgua.Compiler.StepGen
public import ConAgua.Compiler.Mem32
public import ConAgua.Compiler.Rel
import Kraken.X64.Registers

@[expose] public section

/-!
# The 32-bit load and store code (lane p32)

`ld32Code x t d ln bs` (`d := A.u32[x]`) and `st32Code` (`A.u32[rax] := edx`), for a word array
whose length and base the descriptor words `[ln]`, `[bs]` hold (`ArrW`): the bounds check compares
`x >> 1` with the length in words, the access is the 4-byte move at `base + 4 x`, which is half
`x % 2` of word `x / 2` (`load32_of_rdW`, `store32_eq`). The expression compiler (`SimExpr.lean`),
the register-stack generator (`SimGen.lean`) and the statement compiler (`SimStore.lean`) use
these two lemmas.
-/

namespace L.Compiler

open L

/-- `[ln]` holds the length of the word array `arr`, `[bs]` its base `B`, from which it lies in
memory. -/
structure ArrW (s : MachineData) (ln bs : AddrExpr) (arr : Array Word) : Prop where
  len : MemW s ln (UInt64.ofNat arr.size)
  base : ∃ B : Nat, MemW s bs (UInt64.ofNat B) ∧ B + 8 * arr.size < 2 ^ 64 ∧
    ∀ j (h : j < arr.size), rdW s.dmem (A (B + 8 * j)) = some arr[j]

theorem interp_c (a b : UInt64) : CondCode.c.interp (cmpFlags a.toBitVec b.toBitVec) = decide (a < b) := by
  have := cmpCC_interp .ult a b; simpa [cmpCC, Cmp.eval] using this

theorem interp_nc (a b : UInt64) : CondCode.nc.interp (cmpFlags a.toBitVec b.toBitVec) = decide (b ≤ a) := by
  have := neg_interp .c (cmpFlags a.toBitVec b.toBitVec)
  simp only [CondCode.neg] at this
  rw [this, interp_c]
  simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le]
  by_cases h : a.toNat < b.toNat <;> simp [h] <;> omega

/-- The byte address of 32-bit element `j` of an array at `B`: half `j % 2` of word `j / 2`. -/
theorem addr32 (B : Nat) (j : Word) (hB : B + 8 * (j.toNat / 2) + 8 ≤ 2 ^ 64) :
    (UInt64.ofNat B).toBitVec + j.toBitVec * 4 = A (B + 8 * (j.toNat / 2) + 4 * (j.toNat % 2)) := by
  apply BitVec.eq_of_toNat_eq
  have h4 : (4 : BitVec 64).toNat = 4 := rfl
  have hB' : (UInt64.ofNat B).toNat = B := UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  simp only [A, BitVec.toNat_add, BitVec.toNat_mul, UInt64.toNat_toBitVec, hB', h4, BitVec.toNat_ofNat]
  omega

theorem slot_addr (s : MachineData) (j : Nat) (off : Int) (h : off = 8 * (j : Int)) :
    A ((s.regs.get64 .rsp).toNat + off.toNat) = A (s.regs.rsp.toNat + 8 * j) := by
  subst h; simp only [Reg64s.get64_rsp, UInt64.toNat_toBitVec]; congr 1; (try omega)

variable [Host]

/-- **`d := A.u32[x]`** (`ld32Code`): from `x` = the index `j`, the value `half32` of word `j / 2`
in `d`, the scratch `t` and the flags clobbered; or `ca_error` when word `j / 2` does not exist. -/
theorem ld32Code_spec {x t d : Reg64} {ln bs : AddrExpr} {arr : Array Word} {k : Nat} {s : MachineData}
    {Q : MachineState → Prop} (hc : Code (ld32Code x t d ln bs) k) (htx : t ≠ x) {j : Word}
    (hx : s.regs.get64 x = j.toBitVec)
    (hA : ∀ s', s'.dmem = s.dmem → (∀ r, r ≠ t → s'.regs.get64 r = s.regs.get64 r) → ArrW s' ln bs arr)
    (hv : ∀ (h : (j / 2).toNat < arr.size) s', s'.regs.get64 d = (half32 arr[(j / 2).toNat] j).toBitVec →
      s'.dmem = s.dmem → (∀ r, r ≠ t → r ≠ d → s'.regs.get64 r = s.regs.get64 r) → Ev Q s' (at_ (k + 6)))
    (herr : ∀ s', ¬ (j / 2).toNat < arr.size → s'.dmem = s.dmem →
      (∀ r, r ≠ t → s'.regs.get64 r = s.regs.get64 r) → Ev Q s' (label errorL)) :
    Ev Q s (at_ k) := by
  simp only [ld32Code] at hc
  refine ev_movRR hc.head ?_
  refine ev_shiftR (n := 1) (by decide) (op := .shr) (.inr rfl) hc.tail.head fun st1 => ?_
  have hk2 : ∀ (R : Reg64s) (v1 v2 : BitVec 64) r, r ≠ t → ((R.set64 t v1).set64 t v2).get64 r = R.get64 r := by
    intro R v1 v2 r hr; simp only [rget_set, ite_eq_right hr]
  generalize hv2 : (BinOp.eval .shr (UInt64.ofBitVec ((s.regs.set64 t (s.regs.get64 x)).get64 t)) (UInt64.ofNat 1)).toBitVec = v2
  have hkeep1 := fun r hr => hk2 s.regs (s.regs.get64 x) v2 r hr
  obtain ⟨hlen, B, hB, hBs, hget⟩ := hA { s with regs := (s.regs.set64 t (s.regs.get64 x)).set64 t v2, status := st1 } rfl hkeep1
  have hsz : arr.size < 2 ^ 64 := by omega
  have hv2' : v2.toNat = j.toNat / 2 := by
    subst hv2
    simp only [rget_set, ite_true, hx, BinOp.eval, UInt64.ofBitVec_toBitVec, UInt64.toNat_toBitVec,
      UInt64.toNat_shiftRight]
    simp [Nat.shiftRight_eq_div_pow]
  have hj2 : (j / 2).toNat = j.toNat / 2 := by simp [UInt64.toNat_div]
  refine ev_cmpRA hc.tail.tail.head hlen ?_
  have hcmp : ∀ b, CondCode.nc.interp (cmpFlags (((s.regs.set64 t (s.regs.get64 x)).set64 t v2).get64 t)
      (UInt64.ofNat arr.size).toBitVec) = b → (b = true ↔ ¬ (j / 2).toNat < arr.size) := by
    intro b hb
    have e : ((s.regs.set64 t (s.regs.get64 x)).set64 t v2).get64 t = (UInt64.ofBitVec v2).toBitVec := by
      simp [rget_set]
    rw [e, interp_nc] at hb
    subst hb
    simp only [decide_eq_true_eq, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hsz, hj2,
      UInt64.toNat_ofBitVec, hv2']
    omega
  refine ev_jcc hc.tail.tail.tail.head (fun hcc => ?_) (fun hcc => ?_)
  · exact herr _ ((hcmp _ hcc).mp rfl) rfl hkeep1
  · have hj : (j / 2).toNat < arr.size := by
      have := hcmp _ hcc; simp at this; omega
    refine ev_movRA hc.tail.tail.tail.tail.head hB ?_
    refine ev_ld32X hc.tail.tail.tail.tail.tail.head (v := (half32 arr[(j / 2).toNat] j).toNat) ?_
      (by have := (arr[(j / 2).toNat]).toNat_lt; rw [half32_toNat]; split <;> omega) ?_
    · simp only [rget_set, ite_true, ite_eq_right htx.symm, hx]
      rw [addr32 B j (by rw [← hj2]; omega)]
      have := load32_of_rdW (hget _ hj) j
      rw [show B + 8 * (j / 2).toNat = B + 8 * (j.toNat / 2) by rw [hj2]] at this
      exact this
    · refine ev_congr (hv hj _ (by simp [rget_set]) rfl ?_) (by simp)
      intro r hr1 hr2
      simp only [rget_set, ite_eq_right hr1, ite_eq_right hr2]

/-- **`A.u32[rax] := v`** (`st32Code`): from `rax` = the index `j` and the value `v` in temporary
`0`, with the array's base `B` and length in its descriptor words: the memory with word `j / 2`
of the array replaced by `setHalf32` of it (the 4-byte store, `store32_eq`), `rcx`, `rdx` and the
flags clobbered; or `ca_error` when word `j / 2` does not exist. -/
theorem st32Code_spec {ctx : Ctx} {ln bs : AddrExpr} {arr : Array Word} {B : Nat} {k : Nat}
    {s : MachineData} {Q : MachineState → Prop} (hc : Code (st32Code ctx ln bs) k) {j v : Word}
    (hx : s.regs.rax = j) (hoff : SmallOff (8 * ((ctx.nl : Int) + ((0 : Nat) : Int))))
    (hslot : rdW s.dmem (A (s.regs.rsp.toNat + 8 * ctx.nl)) = some v)
    (hD : ∀ s', s'.dmem = s.dmem → (∀ r, r ≠ .rdx → s'.regs.get64 r = s.regs.get64 r) →
      MemW s' ln (UInt64.ofNat arr.size) ∧ MemW s' bs (UInt64.ofNat B))
    (hB : B + 8 * arr.size < 2 ^ 64) (hget : ∀ j (h : j < arr.size), rdW s.dmem (A (B + 8 * j)) = some arr[j])
    (hok : ∀ (h : (j / 2).toNat < arr.size) s',
      s'.dmem = wrW s.dmem (A (B + 8 * (j / 2).toNat)) (setHalf32 arr[(j / 2).toNat] j v).toBitVec →
      (∀ r, r ≠ .rcx → r ≠ .rdx → s'.regs.get64 r = s.regs.get64 r) → Ev Q s' (at_ (k + 7)))
    (herr : ∀ s', ¬ (j / 2).toNat < arr.size → s'.dmem = s.dmem →
      (∀ r, r ≠ .rdx → s'.regs.get64 r = s.regs.get64 r) → Ev Q s' (label errorL)) :
    Ev Q s (at_ k) := by
  simp only [st32Code] at hc
  refine ev_movRR hc.head ?_
  refine ev_shiftR (n := 1) (by decide) (op := .shr) (.inr rfl) hc.tail.head fun st1 => ?_
  have hk2 : ∀ (R : Reg64s) (v1 v2 : BitVec 64) r, r ≠ .rdx → ((R.set64 .rdx v1).set64 .rdx v2).get64 r = R.get64 r := by
    intro R v1 v2 r hr; simp only [rget_set, ite_eq_right hr]
  generalize hv2 : (BinOp.eval .shr (UInt64.ofBitVec ((s.regs.set64 .rdx (s.regs.get64 .rax)).get64 .rdx)) (UInt64.ofNat 1)).toBitVec = v2
  have hkeep1 := fun r hr => hk2 s.regs (s.regs.get64 .rax) v2 r hr
  obtain ⟨hlen, hbase⟩ := hD { s with regs := (s.regs.set64 .rdx (s.regs.get64 .rax)).set64 .rdx v2, status := st1 } rfl hkeep1
  have hsz : arr.size < 2 ^ 64 := by omega
  have hv2' : v2.toNat = j.toNat / 2 := by
    subst hv2
    simp only [rget_set, ite_true, Reg64s.get64_rax, hx, BinOp.eval, UInt64.ofBitVec_toBitVec, UInt64.toNat_toBitVec,
      UInt64.toNat_shiftRight]
    simp [Nat.shiftRight_eq_div_pow]
  have hj2 : (j / 2).toNat = j.toNat / 2 := by simp [UInt64.toNat_div]
  refine ev_cmpRA hc.tail.tail.head hlen ?_
  have hcmp : ∀ b, CondCode.nc.interp (cmpFlags (((s.regs.set64 .rdx (s.regs.get64 .rax)).set64 .rdx v2).get64 .rdx)
      (UInt64.ofNat arr.size).toBitVec) = b → (b = true ↔ ¬ (j / 2).toNat < arr.size) := by
    intro b hb
    have e : ((s.regs.set64 .rdx (s.regs.get64 .rax)).set64 .rdx v2).get64 .rdx = (UInt64.ofBitVec v2).toBitVec := by
      rw [rget_set, ite_eq_left rfl]
    rw [e, interp_nc] at hb
    subst hb
    simp only [decide_eq_true_eq, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hsz, hj2,
      UInt64.toNat_ofBitVec, hv2']
    omega
  refine ev_jcc hc.tail.tail.tail.head (fun hcc => ?_) (fun hcc => ?_)
  · exact herr _ ((hcmp _ hcc).mp rfl) rfl hkeep1
  have hj : (j / 2).toNat < arr.size := by
    have := hcmp _ hcc; simp at this; omega
  refine ev_movRA hc.tail.tail.tail.tail.head hbase ?_
  refine ev_movRM hc.tail.tail.tail.tail.tail.head hoff (v := v) ?_ ?_
  · rw [slot_addr _ (ctx.nl + 0) _ (by omega)]
    simp only
    exact hslot
  have hw := (arr[(j / 2).toNat]).toNat_lt
  have hX : B + 8 * (j.toNat / 2) + 8 ≤ 2 ^ 64 := by omega
  have hget' : rdW s.dmem (A (B + 8 * (j.toNat / 2))) = some arr[(j / 2).toNat] := by
    rw [← hj2]; exact hget _ hj
  have haddr : (UInt64.ofNat B).toBitVec + j.toBitVec * 4 = A (B + 8 * (j.toNat / 2) + 4 * (j.toNat % 2)) :=
    addr32 B j (by omega)
  have hxg : s.regs.get64 .rax = j.toBitVec := by simp [Reg64s.get64, hx]
  refine ev_st32X hc.tail.tail.tail.tail.tail.tail.head ?_ ?_
  · simp only [rget_set, reduceCtorEq, ite_true, ite_false, hxg, haddr, load32_of_rdW hget' j, Option.isSome_some]
  · simp only [rget_set, reduceCtorEq, ite_true, ite_false, hxg, haddr]
    rw [store32_eq hX hget' j]
    refine hok hj _ ?_ ?_
    · simp only [hj2]
      rw [low32_toInt]
      simp only [rget_set, ite_true, UInt64.toNat_toBitVec, setHalf32_mod]
    · intro r h1 h2
      simp only [rget_set, ite_eq_right h1, ite_eq_right h2]
