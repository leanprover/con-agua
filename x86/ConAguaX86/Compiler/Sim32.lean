module

public import ConAguaX86.Compiler.StepGen
import ConAguaX86.Compiler.Mem32
import ConAguaX86.Compiler.Rel
import Kraken.X64.Registers

@[expose] public section

/-!
# The 32-bit load and store code (lane p32)

`ld32Code x t d ln bs` (`d := A.u32[x]`) and `st32Code` (`A.u32[rax] := edx`), for a word array
whose length in 32-bit elements (`Tab.len32`) and base the descriptor words `[ln]`, `[bs]` hold
(`ArrW32`): the bounds check compares `x` with that length (one `cmp`, as for a word load), the
access is the 4-byte move at `base + 4 x`, which is half `x % 2` of word `x / 2`
(`load32_of_rdW`, `store32_eq`). The expression compiler (`SimExpr.lean`), the register-stack
generator (`SimGen.lean`) and the statement compiler (`SimStore.lean`) use these two lemmas.
-/

namespace L.Compiler

open L

/-- `[ln]` holds the length of the word array `arr`, `[bs]` its base `B`, from which it lies in
memory. -/
structure ArrW (s : MachineData) (ln bs : AddrExpr) (arr : Array Word) : Prop where
  len : MemW s ln (UInt64.ofNat arr.size)
  base : ∃ B : Nat, MemW s bs (UInt64.ofNat B) ∧ B + 8 * arr.size < 2 ^ 64 ∧
    ∀ j (h : j < arr.size), rdW s.dmem (A (B + 8 * j)) = some arr[j]

/-- As `ArrW`, with `[ln]` the length in 32-bit elements (twice the length in words,
`Tab.len32`). -/
structure ArrW32 (s : MachineData) (ln bs : AddrExpr) (arr : Array Word) : Prop where
  len : MemW s ln (UInt64.ofNat (2 * arr.size))
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

/-- **The optional bounds check** `chkR ck r ln`: with the index `j` in `r` and the length `n` at
`[ln]`, it falls through (the flags changed) when `j < n` and goes to `ca_error` otherwise. Without
the check (`ck = false`, the bounds-check analysis) `j < n` must be known. -/
theorem chkR_spec {ck : Bool} {r : Reg64} {ln : AddrExpr} {k : Nat} {s : MachineData}
    {Q : MachineState → Prop} (hc : Code (chkR ck r ln) k) {j : Word} {n : Nat} (hn : n < 2 ^ 64)
    (hx : s.regs.get64 r = j.toBitVec) (hlen : MemW s ln (UInt64.ofNat n))
    (hck : ck = false → j.toNat < n)
    (hok : j.toNat < n → ∀ st, Ev Q { s with status := st } (at_ (k + (chkR ck r ln).length)))
    (herr : ¬ j.toNat < n → ∀ st, Ev Q { s with status := st } (label errorL)) : Ev Q s (at_ k) := by
  cases ck
  · exact ev_congr (hok (hck rfl) s.status) (by simp [chkR])
  · simp only [chkR, ite_true] at hc ⊢
    refine ev_cmpRA hc.head hlen ?_
    rw [hx]
    refine ev_jcc hc.tail.head (fun hcc => ?_) (fun hcc => ?_)
    · rw [interp_nc] at hcc
      simp only [decide_eq_true_eq, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hn] at hcc
      exact herr (by omega) _
    · rw [interp_nc] at hcc
      simp only [decide_eq_false_iff_not, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hn] at hcc
      exact ev_congr (hok (by omega) _) (by simp [chkR])

/-- The bounds check `chkI`: on to the next instruction if `j < n` (or no check is emitted), to
`ca_error` otherwise; only the flags change. -/
theorem chkI_spec {ck : Bool} {r : Reg64} {n : Nat} {k : Nat} {s : MachineData}
    {Q : MachineState → Prop} (hc : Code (chkI ck r n) k) {j : Word} (hn : n < 2 ^ 31)
    (hx : s.regs.get64 r = j.toBitVec) (hck : ck = false → j.toNat < n)
    (hok : j.toNat < n → ∀ st, Ev Q { s with status := st } (at_ (k + (chkI ck r n).length)))
    (herr : ¬ j.toNat < n → ∀ st, Ev Q { s with status := st } (label errorL)) : Ev Q s (at_ k) := by
  cases ck
  · exact ev_congr (hok (hck rfl) s.status) (by simp only [chkI, Bool.false_eq_true, ite_false, List.length_nil, Nat.add_zero])
  · simp only [chkI, ite_true] at hc ⊢
    have hn' : (Int64.ofInt (n : Int)).toBitVec.toNat = n := by
      simp [Int64.toBitVec_ofInt]; omega
    refine ev_cmpRIg hc.head ?_
    refine ev_jcc hc.tail.head (fun hcc => ?_) (fun hcc => ?_)
    · simp only [CondCode.interp, cmpFlags_cf, Bool.not_eq_true', decide_eq_false_iff_not,
        hn', hx, UInt64.toNat_toBitVec] at hcc
      exact herr hcc _
    · simp only [CondCode.interp, cmpFlags_cf, Bool.not_eq_false', decide_eq_true_eq,
        hn', hx, UInt64.toNat_toBitVec] at hcc
      exact ev_congr (hok hcc _) (by simp [chkI])

/-- **`d := A.u32[x]`** (`ld32Code`): from `x` = the index `j`, the value `half32` of word `j / 2`
in `d`, the scratch `t` and the flags clobbered; or `ca_error` when word `j / 2` does not exist. -/
theorem ld32Code_spec {ck : Bool} {x t d : Reg64} {ln bs : AddrExpr} {arr : Array Word} {k : Nat} {s : MachineData}
    {Q : MachineState → Prop} (hc : Code (ld32Code ck x t d ln bs) k) (htx : t ≠ x) {j : Word}
    (hx : s.regs.get64 x = j.toBitVec)
    (hA : ∀ s', s'.dmem = s.dmem → (∀ r, r ≠ t → s'.regs.get64 r = s.regs.get64 r) → ArrW32 s' ln bs arr)
    (hck : ck = false → (j / 2).toNat < arr.size)
    (hv : ∀ (h : (j / 2).toNat < arr.size) s', s'.regs.get64 d = (half32 arr[(j / 2).toNat] j).toBitVec →
      s'.dmem = s.dmem → (∀ r, r ≠ t → r ≠ d → s'.regs.get64 r = s.regs.get64 r) →
      Ev Q s' (at_ (k + (ld32Code ck x t d ln bs).length)))
    (herr : ∀ s', ¬ (j / 2).toNat < arr.size → s'.dmem = s.dmem →
      (∀ r, r ≠ t → s'.regs.get64 r = s.regs.get64 r) → Ev Q s' (label errorL)) :
    Ev Q s (at_ k) := by
  simp only [ld32Code] at hc hv
  obtain ⟨hlen, B, hB, hBs, hget⟩ := hA s rfl (fun _ _ => rfl)
  have hsz : 2 * arr.size < 2 ^ 64 := by omega
  have hj2 : (j / 2).toNat = j.toNat / 2 := by simp [UInt64.toNat_div]
  refine chkR_spec hc.left hsz hx hlen (fun h => by have := hck h; omega) (fun hjn st => ?_)
    (fun hjn st => herr _ (by omega) rfl (fun _ _ => rfl))
  have hc' := hc.right
  · have hj : (j / 2).toNat < arr.size := by omega
    refine ev_movRA hc'.head hB ?_
    refine ev_ld32X hc'.tail.head (v := (half32 arr[(j / 2).toNat] j).toNat) ?_
      (by have := (arr[(j / 2).toNat]).toNat_lt; rw [half32_toNat]; split <;> omega) ?_
    · simp only [rget_set, ite_true, ite_eq_right htx.symm, hx]
      rw [addr32 B j (by rw [← hj2]; omega)]
      have := load32_of_rdW (hget _ hj) j
      rw [show B + 8 * (j / 2).toNat = B + 8 * (j.toNat / 2) by rw [hj2]] at this
      exact this
    · refine ev_congr (hv hj _ (by simp [rget_set]) rfl ?_) (by simp; omega)
      intro r hr1 hr2
      simp only [rget_set, ite_eq_right hr1, ite_eq_right hr2]

omit [Host] in
/-- One half of a word as `half32` reads it: the low half is element `0`, the high half element `1`. -/
theorem half32b_eq (hi : Bool) (w : Word) : half32b hi w = half32 w (if hi then 1 else 0) := by
  apply UInt64.toNat_inj.mp
  rw [half32_toNat]
  cases hi
  · simp only [half32b, Bool.false_eq_true, ite_false, UInt64.toNat_and]
    show w.toNat &&& 4294967295 = _
    rw [show (4294967295 : Nat) = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; simp
  · simp only [half32b, ite_true, UInt64.toNat_shiftRight]
    simp [Nat.shiftRight_eq_div_pow]

omit [Host] in
theorem half32b_lt (hi : Bool) (w : Word) : (half32b hi w).toNat < 2 ^ 32 := by
  rw [half32b_eq, half32_toNat]
  have := w.toNat_lt
  cases hi <;> simp <;> omega

/-- **`d := A[x]`'s half `hi`** (`ld32hCode`): from `x` = the index `j`, the value `half32b hi` of
word `j` in `d`, the scratch `t` and the flags clobbered; or `ca_error` when word `j` does not
exist. The bounds check is a word load's. -/
theorem ld32hCode_spec {ck : Bool} {x t d : Reg64} {ln bs : AddrExpr} {hi : Bool} {arr : Array Word} {k : Nat}
    {s : MachineData} {Q : MachineState → Prop} (hc : Code (ld32hCode ck x t d ln bs hi) k) (htx : t ≠ x) {j : Word}
    (hx : s.regs.get64 x = j.toBitVec)
    (hA : ∀ s', s'.dmem = s.dmem → (∀ r, r ≠ t → s'.regs.get64 r = s.regs.get64 r) → ArrW s' ln bs arr)
    (hck : ck = false → j.toNat < arr.size)
    (hv : ∀ (h : j.toNat < arr.size) s', s'.regs.get64 d = (half32b hi arr[j.toNat]).toBitVec →
      s'.dmem = s.dmem → (∀ r, r ≠ t → r ≠ d → s'.regs.get64 r = s.regs.get64 r) →
      Ev Q s' (at_ (k + (ld32hCode ck x t d ln bs hi).length)))
    (herr : ∀ s', ¬ j.toNat < arr.size → s'.dmem = s.dmem →
      (∀ r, r ≠ t → s'.regs.get64 r = s.regs.get64 r) → Ev Q s' (label errorL)) :
    Ev Q s (at_ k) := by
  simp only [ld32hCode] at hc hv
  obtain ⟨hlen, B, hB, hBs, hget⟩ := hA s rfl (fun _ _ => rfl)
  have hsz : arr.size < 2 ^ 64 := by omega
  refine chkR_spec hc.left hsz hx hlen hck (fun hj st => ?_) (fun hjn st => herr _ hjn rfl (fun _ _ => rfl))
  have hc' := hc.right
  · refine ev_movRA hc'.head hB ?_
    refine ev_ld32H hc'.tail.head (v := (half32b hi arr[j.toNat]).toNat) ?_
      (half32b_lt hi _) ?_
    · simp only [rget_set, ite_true, ite_eq_right htx.symm, hx, UInt64.toNat_toBitVec]
      have hBn : (UInt64.ofNat B).toNat = B := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
      rw [hBn]
      have := load32_of_rdW (hget _ hj) (if hi then 1 else 0)
      rw [half32b_eq]
      rw [show B + 8 * j.toNat + 4 * ((if hi then (1 : Word) else 0).toNat % 2) =
        B + 8 * j.toNat + (if hi then 4 else 0) by cases hi <;> rfl] at this
      exact this
    · refine ev_congr (hv hj _ (by simp [rget_set]) rfl ?_) (by simp; omega)
      intro r hr1 hr2
      simp only [rget_set, ite_eq_right hr1, ite_eq_right hr2]

/-- **`A.u32[rax] := v`** (`st32Code`): from `rax` = the index `j` and the value `v` in temporary
`0`, with the array's base `B` and length in its descriptor words: the memory with word `j / 2`
of the array replaced by `setHalf32` of it (the 4-byte store, `store32_eq`), `rcx`, `rdx` and the
flags clobbered; or `ca_error` when word `j / 2` does not exist. -/
theorem st32Code_spec {ln bs : AddrExpr} {arr : Array Word} {B : Nat} {k : Nat}
    {s : MachineData} {Q : MachineState → Prop} (hc : Code (st32Code ln bs) k) {j v : Word}
    (hx : s.regs.rax = j) (hv : s.regs.rdx = v)
    (hD : ∀ s', s'.dmem = s.dmem → s'.regs = s.regs →
      MemW s' ln (UInt64.ofNat (2 * arr.size)) ∧ MemW s' bs (UInt64.ofNat B))
    (hB : B + 8 * arr.size < 2 ^ 64) (hget : ∀ j (h : j < arr.size), rdW s.dmem (A (B + 8 * j)) = some arr[j])
    (hok : ∀ (h : (j / 2).toNat < arr.size) s',
      s'.dmem = wrW s.dmem (A (B + 8 * (j / 2).toNat)) (setHalf32 arr[(j / 2).toNat] j v).toBitVec →
      (∀ r, r ≠ .rcx → s'.regs.get64 r = s.regs.get64 r) → Ev Q s' (at_ (k + 4)))
    (herr : ∀ s', ¬ (j / 2).toNat < arr.size → s'.dmem = s.dmem →
      (∀ r, r ≠ .rcx → s'.regs.get64 r = s.regs.get64 r) → Ev Q s' (label errorL)) :
    Ev Q s (at_ k) := by
  simp only [st32Code] at hc
  obtain ⟨hlen, _⟩ := hD s rfl rfl
  have hsz : 2 * arr.size < 2 ^ 64 := by omega
  have hj2 : (j / 2).toNat = j.toNat / 2 := by simp [UInt64.toNat_div]
  have hxg : s.regs.get64 .rax = j.toBitVec := by simp [Reg64s.get64, hx]
  refine ev_cmpRA hc.head hlen ?_
  have hcmp : ∀ b, CondCode.nc.interp (cmpFlags (s.regs.get64 .rax) (UInt64.ofNat (2 * arr.size)).toBitVec) = b →
      (b = true ↔ ¬ (j / 2).toNat < arr.size) := by
    intro b hb
    rw [hxg, interp_nc] at hb
    subst hb
    simp only [decide_eq_true_eq, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hsz, hj2]
    omega
  refine ev_jcc hc.tail.head (fun hcc => ?_) (fun hcc => ?_)
  · exact herr _ ((hcmp _ hcc).mp rfl) rfl (fun _ _ => rfl)
  have hj : (j / 2).toNat < arr.size := by
    have := hcmp _ hcc; simp at this; omega
  obtain ⟨_, hbase⟩ := hD { s with status := cmpFlags (s.regs.get64 .rax) (UInt64.ofNat (2 * arr.size)).toBitVec }
    rfl rfl
  refine ev_movRA hc.tail.tail.head hbase ?_
  have hw := (arr[(j / 2).toNat]).toNat_lt
  have hX : B + 8 * (j.toNat / 2) + 8 ≤ 2 ^ 64 := by omega
  have hget' : rdW s.dmem (A (B + 8 * (j.toNat / 2))) = some arr[(j / 2).toNat] := by
    rw [← hj2]; exact hget _ hj
  have haddr : (UInt64.ofNat B).toBitVec + j.toBitVec * 4 = A (B + 8 * (j.toNat / 2) + 4 * (j.toNat % 2)) :=
    addr32 B j (by omega)
  refine ev_st32X hc.tail.tail.tail.head ?_ ?_
  · simp only [rget_set, reduceCtorEq, ite_true, ite_false, hxg, haddr, load32_of_rdW hget' j, Option.isSome_some]
  · simp only [rget_set, reduceCtorEq, ite_true, ite_false, hxg, haddr]
    rw [store32_eq hX hget' j]
    refine hok hj _ ?_ ?_
    · simp only [hj2]
      rw [low32_toInt]
      have e : (s.regs.set64 .rcx (UInt64.ofNat B).toBitVec).rdx = v := by
        have := rget_set (R := s.regs) (r := .rcx) (r' := .rdx) (v := (UInt64.ofNat B).toBitVec)
        simp only [reduceCtorEq, ite_false, Reg64s.get64_rdx] at this
        rw [← hv]; exact UInt64.toBitVec_inj.mp this
      simp only [Reg64s.get64_rdx, UInt64.toNat_toBitVec, setHalf32_mod, e]
    · intro r h1
      simp only [rget_set, ite_eq_right h1]
