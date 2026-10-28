module

meta import ConAgua.L.Semantics
public import ConAgua.L.LitWord
public import ConAgua.Front.Fields
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# The canonical-line fast path: `fast_line`

lean4export writes each line in one fixed form: no whitespace, the keys in one order, numbers
without leading zeros. `fast_line(i)` recognises that exact form for the common line shapes and
returns the record's fields `(next, pl, idx, a, c, d)`, the words `front_line` passes to
`apply_rec`/`apply_expr`. On anything else it returns `0` (it declines) and `front_line` runs the
generic scanner. It never rejects a line, so declining is always allowed: its spec
(`fastLine_spec`) says only that an accepted line has its shape (`Canon`), and
`ConAgua.Scan.FastSound` shows that on such a line the generic scanner's models give the same
fields.

The code compares a literal eight bytes at a time (`litB`: `le64!` and a mask, `le64_lit`) and
reads a number byte by byte (`numB`: 1–18 digits, `0` only alone). It calls nothing (a leaf, so
its locals stay in registers). The shapes so far:

| shape | line | `pl` |
|---|---|---|
| app | `{"app":{"arg":A,"fn":F},"ie":I}` | 10 |

A line with fewer than 160 bytes after its start declines, so no read leaves the buffer.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Scan.Fast

open L.Scan.Utf8 (byteW)

/-! ## Literals -/

/-- The bytes of an ASCII string. -/
def bytesOf (s : String) : List UInt8 := s.toList.map fun c => c.toNat.toUInt8

/-- `{"app":{` -/
def hApp : List UInt8 := bytesOf "{\"app\":{"
/-- `"arg":` -/
def kArg : List UInt8 := bytesOf "\"arg\":"
/-- `,"fn":` -/
def kFn : List UInt8 := bytesOf ",\"fn\":"
/-- `},"ie":` -/
def kIe : List UInt8 := bytesOf "},\"ie\":"
/-- `}` and the newline -/
def kEnd1 : List UInt8 := bytesOf "}\n"

/-! ## The code -/

/-- The literal `l` (at most seven bytes) at `p`, and `p` past it; else decline. -/
def litB (l : List UInt8) : Stmt := lblk (i, p) {
  if (le64!(IN.u8, p) & ⟪mskW l.length⟫) != ⟪litW l⟫ { return 0 };
  p += ⟪UInt64.ofNat l.length⟫
}

/-- The digits after the first: `x` accumulates, `p` moves on, `c` is the byte at `p`; a digit at
`n` declines. -/
def digB : Stmt := lblk (i, p, x, n, c) {
  while c - 48 < 10 {
    if p == n { return 0 };
    x := x * 10 + (c - 48);
    p += 1;
    c := IN.u8[p]
  }
}

/-- The number at `p` (1–18 digits, `0` only alone) into `x`, and `p` past it; else decline. -/
def numB : Stmt := lblk (i, p, x, n, c) {
  c := IN.u8[p];
  x := c - 48;
  if 9 < x { return 0 };
  if x == 0 { n := p + 1 } else { n := p + 18 };
  p += 1;
  c := IN.u8[p];
  ⟪digB⟫
}

/-- An app line: `{"app":{"arg":A,"fn":F},"ie":I}`. -/
def appS : Stmt := lblk (i, p, x, n, c, a, f, idx, w) {
  if w == ⟪litW hApp⟫ {
    p := i + 8;
    ⟪litB kArg⟫;
    ⟪numB⟫;
    a := x;
    ⟪litB kFn⟫;
    ⟪numB⟫;
    f := x;
    ⟪litB kIe⟫;
    ⟪numB⟫;
    idx := x;
    ⟪litB kEnd1⟫;
    return (p, 10, idx, f, a, a)
  }
}

/-- The fast path: `(next, pl, idx, a, c, d)` for a canonical line, `0` otherwise. -/
-- con-ron: none — a canonical-form fast path in front of `scan_line_fwd` (docs/deviations.md)
def fastLine : FunDecl := lfn (i) locals (p, x, n, c, a, f, idx, w) {
  if len(IN.u8) < i + 160 { return 0 };
  w := le64!(IN.u8, i);
  ⟪appS⟫;
  return 0
}

/-! ## The digit loop -/

/-- A step towards `n` shrinks the distance (the loops' measure). -/
theorem sub_succ_lt (p n : Word) (h : p ≠ n) : (n - (p + 1)).toNat < (n - p).toNat := by
  have h' : p.toNat ≠ n.toNat := fun e => h (UInt64.toNat_inj.mp e)
  have := p.toNat_lt; have := n.toNat_lt
  simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_one]
  omega

/-- The digit loop on words: from `p` with value `x`, digits until a non-digit or `n`. -/
def digN (b : Array UInt8) (p x n : Word) : Word × Word :=
  if byteW b p - 48 < 10 ∧ p ≠ n then digN b (p + 1) (x * 10 + (byteW b p - 48)) n else (p, x)
termination_by (n - p).toNat
decreasing_by exact sub_succ_lt p n ‹_ ∧ p ≠ n›.2

/-- The digit loop on the state (what `digB` leaves when it does not decline). -/
def digS (b : Array UInt8) (s : St) : St :=
  if s.loc 4 - 48 < 10 ∧ s.loc 1 ≠ s.loc 3 then
    digS b (((s.setLoc 2 (s.loc 2 * 10 + (s.loc 4 - 48))).setLoc 1 (s.loc 1 + 1)).setLoc 4
      (byteW b (s.loc 1 + 1)))
  else s
termination_by (s.loc 3 - s.loc 1).toNat
decreasing_by simp only [St.setLoc_loc]; simp; exact sub_succ_lt _ _ ‹_ ∧ s.loc 1 ≠ s.loc 3›.2

end L.Scan.Fast

namespace L.Scan.Fast
open L.Scan.Utf8 (byteW)

section
variable (b : Array UInt8) (s : St)
theorem digS_step (h : s.loc 4 - 48 < 10) (h1 : s.loc 1 ≠ s.loc 3) :
    digS b s = digS b (((s.setLoc 2 (s.loc 2 * 10 + (s.loc 4 - 48))).setLoc 1 (s.loc 1 + 1)).setLoc 4
      (byteW b (s.loc 1 + 1))) := by
  rw [digS, ite_eq_left ⟨h, h1⟩]
theorem digS_stop (h : ¬ (s.loc 4 - 48 < 10 ∧ s.loc 1 ≠ s.loc 3)) : digS b s = s := by
  rw [digS, ite_eq_right h]
end

/-- An in-bounds byte read is `byteW`. -/
theorem byteW_get (b : Array UInt8) (k : Word) (h : k.toNat < b.size) :
    byteW b k = b[k.toNat].toUInt64 := by
  simp [byteW, Array.getD, h]

/-! ### What the digit loop reads -/

/-- A digit, as the code tests it (a byte past the end reads `0`, no digit). -/
theorem dig_iff (b : Array UInt8) (k : Word) :
    byteW b k - 48 < 10 ↔ ∃ h : k.toNat < b.size, 48 ≤ b[k.toNat] ∧ b[k.toNat] ≤ 57 := by
  have hd : ∀ x : UInt8, x.toUInt64 - 48 < 10 ↔ 48 ≤ x ∧ x ≤ 57 := by decide
  by_cases h : k.toNat < b.size
  · simp [byteW, Array.getD, h, hd]
  · have h0 : byteW b k = 0 := by simp [byteW, Array.getD, h]
    rw [h0]
    exact ⟨fun h' => absurd h' (by decide), fun ⟨h', _⟩ => absurd h' h⟩

theorem and255 (y : Word) (h : y < 10) : y &&& 255 = y := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, show (255 : Word).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  rw [UInt64.lt_iff_toNat_lt] at h
  exact Nat.mod_eq_of_lt (by simp at h; omega)

/-- **The digit loop** from `q` (below the limit `lim`) with value `x`: it stops at `e` between
`q` and `lim`, reads digits up to `e`, stops at a non-digit unless it reached `lim`, and its value
is `read_nat`'s. -/
theorem digN_run (b : Array UInt8) (q x lim : Word) (hq : q.toNat ≤ lim.toNat) :
    q.toNat ≤ (digN b q x lim).1.toNat ∧ (digN b q x lim).1.toNat ≤ lim.toNat ∧
    (∀ k : Word, q.toNat ≤ k.toNat → k.toNat < (digN b q x lim).1.toNat → byteW b k - 48 < 10) ∧
    (¬ byteW b (digN b q x lim).1 - 48 < 10 ∨ (digN b q x lim).1 = lim) ∧
    (digN b q x lim).2 = L.Front.Fields.rdLoopN b q (digN b q x lim).1 x := by
  fun_induction digN b q x lim with
  | case1 q x hc ih =>
    have hne : q.toNat ≠ lim.toNat := fun e => hc.2 (UInt64.toNat_inj.mp e)
    have h1 : (q + 1).toNat = q.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; have := lim.toNat_lt; omega
    obtain ⟨a1, a2, a3, a4, a5⟩ := ih (by omega)
    refine ⟨by omega, a2, ?_, a4, ?_⟩
    · intro k hk1 hk2
      by_cases hk : k.toNat = q.toNat
      · rw [UInt64.toNat_inj.mp hk]; exact hc.1
      · exact a3 k (by omega) hk2
    · rw [a5, L.Front.Fields.rdLoopN_step b q _ x (by rw [UInt64.lt_iff_toNat_lt]; omega),
        and255 _ hc.1]
  | case2 q x hc =>
    simp only
    refine ⟨Nat.le_refl _, hq, fun k h1 h2 => absurd h2 (by omega), ?_, ?_⟩
    · by_cases h : byteW b q - 48 < 10
      · exact .inr (by simpa [h] using hc)
      · exact .inl h
    · rw [L.Front.Fields.rdLoopN_stop b q q x (UInt64.lt_irrefl _)]

theorem digN_step (b : Array UInt8) (p x n : Word) (h : byteW b p - 48 < 10 ∧ p ≠ n) :
    digN b p x n = digN b (p + 1) (x * 10 + (byteW b p - 48)) n := by
  rw [digN, ite_eq_left h]
theorem digN_stop (b : Array UInt8) (p x n : Word) (h : ¬ (byteW b p - 48 < 10 ∧ p ≠ n)) :
    digN b p x n = (p, x) := by
  rw [digN, ite_eq_right h]

/-- The loop's state after it: what `digN` says, the other locals unchanged. -/
theorem digS_loc (b : Array UInt8) (s : St) (hc : s.loc 4 = byteW b (s.loc 1)) (k : Var) :
    (digS b s).loc k =
      if k = 1 then (digN b (s.loc 1) (s.loc 2) (s.loc 3)).1
      else if k = 2 then (digN b (s.loc 1) (s.loc 2) (s.loc 3)).2
      else if k = 4 then byteW b (digN b (s.loc 1) (s.loc 2) (s.loc 3)).1
      else s.loc k := by
  induction s using digS.induct b with
  | case1 s h ih =>
    rw [digS_step b s h.1 h.2, ih (by simp [St.setLoc_loc])]
    rw [hc] at h
    rw [digN_step b _ _ _ h]
    simp only [St.setLoc_loc, hc]
    by_cases k = 1 <;> by_cases k = 2 <;> by_cases k = 4 <;> simp_all
  | case2 s h =>
    rw [digS_stop b s h]
    rw [hc] at h
    rw [digN_stop b _ _ _ h]
    by_cases k = 1 <;> by_cases k = 2 <;> by_cases k = 4 <;> simp_all

theorem digS_mem (b : Array UInt8) (s : St) : (digS b s).mem = s.mem := by
  induction s using digS.induct b with
  | case1 s h ih => rw [digS_step b s h.1 h.2, ih]; rfl
  | case2 s h => rw [digS_stop b s h]

/-! ## The number -/

/-- The digit limit after the first digit at `p`: a `0` stands alone, else 18 digits. -/
def numL (b : Array UInt8) (p : Word) : Word := if byteW b p - 48 = 0 then p + 1 else p + 18

/-- The number at `p`: its end and its value. -/
def numR (b : Array UInt8) (p : Word) : Word × Word :=
  digN b (p + 1) (byteW b p - 48) (numL b p)

/-- `numB` accepts the number at `p`: a digit, and a non-digit after the digits it read. -/
structure NumOK (b : Array UInt8) (p : Word) : Prop where
  first : byteW b p - 48 < 10
  stop : ¬ byteW b (numR b p).1 - 48 < 10

/-- The state after `numB` (when it accepts). -/
def numS (b : Array UInt8) (s : St) : St :=
  digS b (((((s.setLoc 4 (byteW b (s.loc 1))).setLoc 2 (byteW b (s.loc 1) - 48)).setLoc 3
    (numL b (s.loc 1))).setLoc 1 (s.loc 1 + 1)).setLoc 4 (byteW b (s.loc 1 + 1)))

theorem numS_loc (b : Array UInt8) (s : St) (k : Var) :
    (numS b s).loc k =
      if k = 1 then (numR b (s.loc 1)).1
      else if k = 2 then (numR b (s.loc 1)).2
      else if k = 3 then numL b (s.loc 1)
      else if k = 4 then byteW b (numR b (s.loc 1)).1
      else s.loc k := by
  rw [numS, digS_loc _ _ (by simp [St.setLoc_loc])]
  simp only [St.setLoc_loc, numR]
  by_cases k = 1 <;> by_cases k = 2 <;> by_cases k = 3 <;> by_cases k = 4 <;> simp_all

theorem numS_mem (b : Array UInt8) (s : St) : (numS b s).mem = s.mem := by
  rw [numS, digS_mem]; rfl

/-! ### The canonical number (L2) -/

/-- The number at `p` ends at `e` and has the value `x`, as the generic scanner reads it:
`num_end`'s end, at most 18 digits, `read_nat`'s value. -/
structure NumAt (b : Array UInt8) (p e x : Word) : Prop where
  first : byteW b p - 48 < 10
  lt : p < e
  short : e.toNat ≤ p.toNat + 18
  inb : e.toNat ≤ b.size
  endN : L.Scan.Leaves.numEndN b p.toNat = e.toNat
  val : x = L.Front.Fields.rdLoopN b p e 0

theorem skipDigitsN_run (b : Array UInt8) (i e : Nat) (hie : i ≤ e)
    (hd : ∀ k, i ≤ k → k < e → ∃ h : k < b.size, 48 ≤ b[k] ∧ b[k] ≤ 57)
    (hs : ∀ h : e < b.size, ¬ (48 ≤ b[e] ∧ b[e] ≤ 57)) : L.Scan.Leaves.skipDigitsN b i = e := by
  induction h : e - i generalizing i with
  | zero =>
    have : i = e := by omega
    subst this
    by_cases he : i < b.size
    · exact L.Scan.Leaves.skipDigitsN_other b i he (hs he)
    · exact L.Scan.Leaves.skipDigitsN_end b i (by omega)
  | succ m ih =>
    obtain ⟨hi, hdi⟩ := hd i (Nat.le_refl _) (by omega)
    rw [L.Scan.Leaves.skipDigitsN_digit b i (i + 1) rfl hi hdi]
    exact ih (i + 1) (by omega) (fun k h1 h2 => hd k (by omega) h2) (by omega)

/-- **The number `numB` accepts** is the generic scanner's number (L2). -/
theorem numAt_of_ok (b : Array UInt8) (hb : b.size < 2 ^ 63) (p : Word) (h : NumOK b p) :
    NumAt b p (numR b p).1 (numR b p).2 := by
  obtain ⟨hp, hd0⟩ := (dig_iff b p).mp h.first
  have hq : (p + 1).toNat = p.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  have hlim : (numL b p).toNat = if byteW b p - 48 = 0 then p.toNat + 1 else p.toNat + 18 := by
    unfold numL; split
    · exact hq
    · rw [UInt64.toNat_add]; simp; omega
  obtain ⟨a1, a2, a3, a4, a5⟩ := digN_run b (p + 1) (byteW b p - 48) (numL b p)
    (by rw [hq, hlim]; split <;> omega)
  have hstop := h.stop
  simp only [numR] at hstop ⊢
  generalize hE : digN b (p + 1) (byteW b p - 48) (numL b p) = E at *
  obtain ⟨e, x⟩ := E
  simp only at *
  have he : e.toNat ≤ p.toNat + 18 := by rw [hlim] at a2; split at a2 <;> omega
  have hsd : L.Scan.Leaves.skipDigitsN b p.toNat = e.toNat := by
    apply skipDigitsN_run b _ _ (by omega)
    · intro k h1 h2
      have hs : UInt64.size = 2 ^ 64 := rfl
      have hk : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by omega)
      by_cases hkp : k = p.toNat
      · exact hkp ▸ ⟨hp, hd0⟩
      · have := (dig_iff b (UInt64.ofNat k)).mp (a3 _ (by omega) (by omega))
        simp only [hk] at this
        exact this
    · intro he' hde
      exact hstop ((dig_iff b e).mpr ⟨he', hde⟩)
  refine ⟨h.first, ?_, he, ?_, ?_, ?_⟩
  · rw [UInt64.lt_iff_toNat_lt]; omega
  · rw [← hsd]; exact L.Scan.Leaves.skipDigitsN_le b _ (by omega)
  · unfold L.Scan.Leaves.numEndN
    simp only [hsd]
    rw [ite_eq_right (by omega)]
    rw [ite_eq_right]
    rintro ⟨h48, hne⟩
    apply hne
    have : byteW b p - 48 = 0 := by
      rw [byteW_get b p hp]; simp [Array.getD, hp] at h48; rw [h48]; rfl
    rw [hlim, ite_eq_left this] at a2
    omega
  · rw [L.Front.Fields.rdLoopN_step b p e 0 (by rw [UInt64.lt_iff_toNat_lt]; omega), a5,
      and255 _ h.first]
    simp

/-! ## The accepted shapes -/

/-- A literal `litB` can compare: one to eight bytes, none of them `0`. -/
structure LitOK (l : List UInt8) : Prop where
  short : l.length ≤ 8
  ne : l ≠ []
  nz : 0 ∉ l

/-- An app line at `i` with fields `(nx, idx, f, a)`: `{"app":{"arg":a,"fn":f},"ie":idx}` and
its newline, `nx` after it. -/
structure AppLine (b : Array UInt8) (i nx idx f a : Word) : Prop where
  head : LitAt b i hApp
  arg : LitAt b (i + 8) kArg
  na : NumAt b (i + 8 + 6) (numR b (i + 8 + 6)).1 a
  fn : LitAt b (numR b (i + 8 + 6)).1 kFn
  nf : NumAt b ((numR b (i + 8 + 6)).1 + 6) (numR b ((numR b (i + 8 + 6)).1 + 6)).1 f
  ie : LitAt b (numR b ((numR b (i + 8 + 6)).1 + 6)).1 kIe
  ni : NumAt b ((numR b ((numR b (i + 8 + 6)).1 + 6)).1 + 7)
    (numR b ((numR b ((numR b (i + 8 + 6)).1 + 6)).1 + 7)).1 idx
  tail : LitAt b (numR b ((numR b ((numR b (i + 8 + 6)).1 + 6)).1 + 7)).1 kEnd1
  next : nx = (numR b ((numR b ((numR b (i + 8 + 6)).1 + 6)).1 + 7)).1 + 2

/-- The lines `fast_line` accepts, with the words it returns. -/
inductive Canon (b : Array UInt8) (i : Word) : List Word → Prop
  | app {nx idx f a : Word} : AppLine b i nx idx f a → Canon b i [nx, 10, idx, f, a, a]

/-- What `fast_line(i)` returns: `0` (declined), or a canonical line's words. -/
def FastOK (b : Array UInt8) (i : Word) (v : List Word) : Prop := v.headD 0 ≠ 0 → Canon b i v

section spec
variable (p : Prog) (b : Array UInt8)

theorem digB_spec (n : Nat) (s₀ : St) (hc : s₀.loc 4 = byteW b (s₀.loc 1)) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n digB
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      (r = .normal → s' = digS b s₀ ∧ ¬ s'.loc 4 - 48 < 10) ∧
      (r ≠ .normal → r.retOr [0] = [0]); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := digB) rfl]
    vcgen [step, L.evalE_spec, L.evalC_spec, evalArgs, setLoc, setLocs, ld8, ih]
    all_goals subst_vars
    all_goals simp only [Cond.pval, Expr.pval, St.setLoc_loc, St.setLoc_mem, Cmp.eval, BinOp.eval,
      beq_iff_eq, bne_iff_ne, ne_eq, Nat.reduceEqDiff, reduceIte, decide_eq_true_eq,
      L.Scan.Key.rd8_byteW] at *
    all_goals grind [digS_step, digS_stop, byteW_get, Sig.retOr]

theorem litB_spec (l : List UInt8) (hl : LitOK l) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) (litB l)
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      (r = .normal → s' = s₀.setLoc 1 (s₀.loc 1 + UInt64.ofNat l.length) ∧ LitAt b (s₀.loc 1) l) ∧
      (r ≠ .normal → r.retOr [0] = [0]); ⊤⦄ := by
  dsimp only [litB]
  vcgen [step, L.evalE_spec, L.evalC_spec, evalArgs, setLoc, setLocs]
  all_goals subst_vars
  all_goals simp only [Cond.pval, Expr.pval, St.setLoc_loc, St.setLoc_mem, Cmp.eval, BinOp.eval,
      beq_iff_eq, bne_iff_ne, ne_eq, Nat.reduceEqDiff, reduceIte, Mem.src8, decide_eq_true_eq,
      Decidable.not_not] at *
  all_goals first
    | grind [Sig.retOr]
    | exact (le64_lit _ _ l hl.short hl.ne hl.nz).mp ‹_›

theorem numB_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) numB
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      (r = .normal → s' = numS b s₀ ∧ NumOK b (s₀.loc 1)) ∧
      (r ≠ .normal → r.retOr [0] = [0]); ⊤⦄ := by
  dsimp only [numB]
  vcgen [step, L.evalE_spec, L.evalC_spec, evalArgs, setLoc, setLocs,
    fun s₀ hc => Triple.step_exec (digB_spec p b (n + 1) s₀ hc)]
  all_goals subst_vars
  all_goals simp only [Cond.pval, Expr.pval, St.setLoc_loc, St.setLoc_mem, Cmp.eval, BinOp.eval,
      beq_iff_eq, Nat.reduceEqDiff, reduceIte, L.Scan.Key.rd8_byteW] at *
  all_goals first
    | grind [Sig.retOr]
    | (simp only [numS, numL, *, reduceIte]; done)
    | grind [NumOK, numR, numL, digS_loc, St.setLoc_loc]

end spec
end L.Scan.Fast

namespace L.Scan.Fast
open L.Scan.Utf8 (byteW)

theorem litOK_kArg : LitOK kArg := ⟨by decide, by decide, by decide⟩
theorem litOK_kFn : LitOK kFn := ⟨by decide, by decide, by decide⟩
theorem litOK_kIe : LitOK kIe := ⟨by decide, by decide, by decide⟩
theorem litOK_kEnd1 : LitOK kEnd1 := ⟨by decide, by decide, by decide⟩

theorem head_app {b : Array UInt8} {i : Word} (h : le64 b i.toNat = litW hApp) : LitAt b i hApp :=
  (le64_lit8 _ _ hApp (by decide) (by decide) (by decide)).mp h

/-- The literals' lengths, as the code adds them. -/
theorem lit_len : UInt64.ofNat kArg.length = 6 ∧ UInt64.ofNat kFn.length = 6 ∧
    UInt64.ofNat kIe.length = 7 ∧ UInt64.ofNat kEnd1.length = 2 := by decide

section spec2
variable (p : Prog) (b : Array UInt8)

theorem appS_spec (hb : b.size < 2 ^ 63) (n : Nat) (s₀ : St)
    (hw : s₀.loc 8 = le64 b (s₀.loc 0).toNat) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) appS
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ (r = .normal → s' = s₀) ∧
      (r ≠ .normal → FastOK b (s₀.loc 0) (r.retOr [])); ⊤⦄ := by
  dsimp only [appS]
  vcgen [step, L.evalE_spec, L.evalC_spec, evalArgs, setLoc, setLocs,
    fun l hl => litB_spec p b l hl n, numB_spec p b n]
  all_goals (try subst_vars)
  all_goals simp only [Cond.pval, Expr.pval, St.setLoc_loc, St.setLoc_mem, Cmp.eval, BinOp.eval,
      beq_iff_eq, bne_iff_ne, ne_eq, Nat.reduceEqDiff, reduceIte, Mem.src8, decide_eq_true_eq,
      Decidable.not_not, Sig.retOr, FastOK, List.headD_cons, true_implies, reduceCtorEq,
      not_false_eq_true, true_and, not_true, false_implies, and_true, lit_len] at *
  all_goals repeat (cases ‹_ ∧ _›)
  all_goals (try subst_vars)
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, numS_loc, numS_mem, Nat.reduceEqDiff,
    reduceIte, true_implies] at *)
  all_goals repeat (cases ‹_ ∧ _›)
  all_goals (try subst_vars)
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, numS_loc, numS_mem, Nat.reduceEqDiff,
    reduceIte, true_implies] at *)
  all_goals first
    | exact litOK_kArg
    | exact litOK_kFn
    | exact litOK_kIe
    | exact litOK_kEnd1
    | grind [Sig.retOr]
    | (intro _
       refine Canon.app ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
       all_goals first
         | (rw [hw] at *; exact head_app ‹_›)
         | rfl
         | assumption
         | exact numAt_of_ok _ hb _ ‹_›)

/-- **`fast_line(i)`**: it changes nothing, and what it returns is `0` or a canonical line's
words. -/
theorem fastLine_spec (hp : p.lookup "fast_line" = some fastLine) (hb : b.size < 2 ^ 63)
    (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "fast_line" [i]
    ⦃fun r s' => s' = s₀ ∧ FastOK b i r; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, fastLine]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, L.evalE_spec, L.evalC_spec, evalArgs, setLoc, setLocs,
      fun s₁ hw => appS_spec p b hb n s₁ hw]
    all_goals (try subst_vars)
    all_goals simp only [Cond.pval, Expr.pval, St.setLoc_loc, St.setLoc_mem, Cmp.eval, BinOp.eval,
      Mem.src8, Locals.init_cons_zero, Nat.reduceEqDiff, reduceIte, true_implies, reduceCtorEq,
      FastOK, Sig.retVal, Sig.retOr, List.headD_cons, List.headD_nil, ne_eq, not_true_eq_false,
      false_implies, implies_true] at *
    all_goals repeat (cases ‹_ ∧ _›)
    all_goals first
      | grind
      | (cases ‹St›; simp_all)

end spec2
end L.Scan.Fast
