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
| lam | `{"ie":I,"lam":{"binderInfo":"…","body":B,"name":N,"type":T}}` | 11 |
| forallE | `{"forallE":{"binderInfo":"…","body":B,"name":N,"type":T},"ie":I}` | 12 |

A line with fewer than 160 bytes after its start declines, so no read leaves the buffer.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Scan.Fast

open L.Scan.Utf8 (byteW)

/-! ## Literals -/

/-- `{"app":{` -/
def hApp : List UInt8 := [123, 34, 97, 112, 112, 34, 58, 123]
/-- `"arg":` -/
def kArg : List UInt8 := [34, 97, 114, 103, 34, 58]
/-- `,"fn":` -/
def kFn : List UInt8 := [44, 34, 102, 110, 34, 58]
/-- `},"ie":` -/
def kIe : List UInt8 := [125, 44, 34, 105, 101, 34, 58]
/-- `}` and the newline -/
def kEnd1 : List UInt8 := [125, 10]
/-- `{"ie":` -/
def hIe : List UInt8 := [123, 34, 105, 101, 34, 58]
/-- `,"lam":{` -/
def kLam : List UInt8 := [44, 34, 108, 97, 109, 34, 58, 123]
/-- `{"forall` -/
def hForall : List UInt8 := [123, 34, 102, 111, 114, 97, 108, 108]
/-- `E":{` -/
def kForallE : List UInt8 := [69, 34, 58, 123]
/-- `"binderI` -/
def kBinderI : List UInt8 := [34, 98, 105, 110, 100, 101, 114, 73]
/-- `nfo":"` -/
def kNfo : List UInt8 := [110, 102, 111, 34, 58, 34]
/-- `default"` -/
def biD : List UInt8 := [100, 101, 102, 97, 117, 108, 116, 34]
/-- `implicit` -/
def biI8 : List UInt8 := [105, 109, 112, 108, 105, 99, 105, 116]
/-- `"` -/
def kQ : List UInt8 := [34]
/-- `instImpl` -/
def biN8 : List UInt8 := [105, 110, 115, 116, 73, 109, 112, 108]
/-- `icit"` -/
def biN5 : List UInt8 := [105, 99, 105, 116, 34]
/-- `strictIm` -/
def biS8 : List UInt8 := [115, 116, 114, 105, 99, 116, 73, 109]
/-- `plicit"` -/
def biS7 : List UInt8 := [112, 108, 105, 99, 105, 116, 34]
/-- `,"body":` -/
def kBody : List UInt8 := [44, 34, 98, 111, 100, 121, 34, 58]
/-- `,"name":` -/
def kName : List UInt8 := [44, 34, 110, 97, 109, 101, 34, 58]
/-- `,"type":` -/
def kType : List UInt8 := [44, 34, 116, 121, 112, 101, 34, 58]
/-- `}}` and the newline -/
def kEnd2 : List UInt8 := [125, 125, 10]

/-! ## The code -/

/-- The literal `l` (at most seven bytes) at `p`, and `p` past it; else decline. -/
def litB (l : List UInt8) : Stmt := lblk (i, p) {
  if (le64!(IN.u8, p) & ⟪mskW l.length⟫) != ⟪litW l⟫ { return 0 };
  p += ⟪UInt64.ofNat l.length⟫
}

/-- The literal `l` of eight bytes at `p`, and `p` past it; else decline. -/
def litB8 (l : List UInt8) : Stmt := lblk (i, p) {
  if le64!(IN.u8, p) != ⟪litW l⟫ { return 0 };
  p += 8
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

/-- A binder's value after its opening quote, and the closing quote: `p` past it; else decline. -/
def biB : Stmt := lblk (i, p, x) {
  x := le64!(IN.u8, p);
  if x == ⟪litW biD⟫ { p += 8 }
  else if x == ⟪litW biI8⟫ && (le64!(IN.u8, p + 8) & ⟪mskW 1⟫) == ⟪litW kQ⟫ { p += 9 }
  else if x == ⟪litW biN8⟫ && (le64!(IN.u8, p + 8) & ⟪mskW 5⟫) == ⟪litW biN5⟫ { p += 13 }
  else if x == ⟪litW biS8⟫ && (le64!(IN.u8, p + 8) & ⟪mskW 7⟫) == ⟪litW biS7⟫ { p += 15 }
  else { return 0 }
}

/-- A binder object's members `"binderInfo":"…","body":B,"name":N,"type":T` at `p`: `a := B`,
`f := T`, `p` at its closing brace. -/
def bndB : Stmt := lblk (i, p, x, n, c, a, f) {
  ⟪litB8 kBinderI⟫;
  ⟪litB kNfo⟫;
  ⟪biB⟫;
  ⟪litB8 kBody⟫;
  ⟪numB⟫;
  a := x;
  ⟪litB8 kName⟫;
  ⟪numB⟫;
  ⟪litB8 kType⟫;
  ⟪numB⟫;
  f := x
}

/-- A lambda line: `{"ie":I,"lam":{…}}`. -/
def lamS : Stmt := lblk (i, p, x, n, c, a, f, idx, w) {
  if (w & ⟪mskW 6⟫) == ⟪litW hIe⟫ {
    p := i + 6;
    ⟪numB⟫;
    idx := x;
    ⟪litB8 kLam⟫;
    ⟪bndB⟫;
    ⟪litB kEnd2⟫;
    return (p, 11, idx, f, a, a)
  }
}

/-- A pi line: `{"forallE":{…},"ie":I}`. -/
def forallS : Stmt := lblk (i, p, x, n, c, a, f, idx, w) {
  if w == ⟪litW hForall⟫ {
    p := i + 8;
    ⟪litB kForallE⟫;
    ⟪bndB⟫;
    ⟪litB kIe⟫;
    ⟪numB⟫;
    idx := x;
    ⟪litB kEnd1⟫;
    return (p, 12, idx, f, a, a)
  }
}

/-- The fast path: `(next, pl, idx, a, c, d)` for a canonical line, `0` otherwise. -/
-- con-ron: none — a canonical-form fast path in front of `scan_line_fwd` (docs/deviations.md)
def fastLine : FunDecl := lfn (i) locals (p, x, n, c, a, f, idx, w) {
  if len(IN.u8) < i + 160 { return 0 };
  w := le64!(IN.u8, i);
  ⟪appS⟫;
  ⟪lamS⟫;
  ⟪forallS⟫;
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

/-- Where `biB` leaves `p`: past the binder's value and its closing quote (`p` if none). -/
def biEnd (b : Array UInt8) (p : Word) : Word :=
  if le64 b p.toNat = litW biD then p + 8
  else if le64 b p.toNat = litW biI8 ∧ le64 b (p + 8).toNat &&& mskW 1 = litW kQ then p + 9
  else if le64 b p.toNat = litW biN8 ∧ le64 b (p + 8).toNat &&& mskW 5 = litW biN5 then p + 13
  else if le64 b p.toNat = litW biS8 ∧ le64 b (p + 8).toNat &&& mskW 7 = litW biS7 then p + 15
  else p

/-- The state after `biB` (when it accepts). -/
def biS (b : Array UInt8) (s : St) : St :=
  (s.setLoc 2 (le64 b (s.loc 1).toNat)).setLoc 1 (biEnd b (s.loc 1))

/-- A binder's value at `p` (after its opening quote), its closing quote before `e`. -/
inductive BiAt (b : Array UInt8) (p : Word) : Word → Prop
  | dflt : LitAt b p biD → BiAt b p (p + 8)
  | impl : LitAt b p biI8 → LitAt b (p + 8) kQ → BiAt b p (p + 9)
  | inst : LitAt b p biN8 → LitAt b (p + 8) biN5 → BiAt b p (p + 13)
  | strict : LitAt b p biS8 → LitAt b (p + 8) biS7 → BiAt b p (p + 15)

/-- The positions in a binder object whose first key is at `p`: after the binder's value, and
after the `body`, `name` and `type` numbers. -/
abbrev bE1 (b : Array UInt8) (p : Word) : Word := biEnd b (p + 8 + 6)
abbrev bE2 (b : Array UInt8) (p : Word) : Word := (numR b (bE1 b p + 8)).1
abbrev bE3 (b : Array UInt8) (p : Word) : Word := (numR b (bE2 b p + 8)).1
abbrev bE4 (b : Array UInt8) (p : Word) : Word := (numR b (bE3 b p + 8)).1

/-- A binder object's members from its first key at `p`:
`"binderInfo":"…","body":bd,"name":…,"type":t`, its closing brace at `bE4 b p`. -/
structure BndAt (b : Array UInt8) (p bd t : Word) : Prop where
  k1 : LitAt b p kBinderI
  k2 : LitAt b (p + 8) kNfo
  bi : BiAt b (p + 8 + 6) (bE1 b p)
  body : LitAt b (bE1 b p) kBody
  nb : NumAt b (bE1 b p + 8) (bE2 b p) bd
  name : LitAt b (bE2 b p) kName
  nn : NumAt b (bE2 b p + 8) (bE3 b p) (numR b (bE2 b p + 8)).2
  type : LitAt b (bE3 b p) kType
  nt : NumAt b (bE3 b p + 8) (bE4 b p) t

/-- A lambda line at `i`: `{"ie":idx,"lam":{…}}` and its newline, `nx` after it. -/
structure LamLine (b : Array UInt8) (i nx idx t bd : Word) : Prop where
  head : LitAt b i hIe
  ni : NumAt b (i + 6) (numR b (i + 6)).1 idx
  lam : LitAt b (numR b (i + 6)).1 kLam
  bnd : BndAt b ((numR b (i + 6)).1 + 8) bd t
  tail : LitAt b (bE4 b ((numR b (i + 6)).1 + 8)) kEnd2
  next : nx = bE4 b ((numR b (i + 6)).1 + 8) + 3

/-- A pi line at `i`: `{"forallE":{…},"ie":idx}` and its newline, `nx` after it. -/
structure ForallLine (b : Array UInt8) (i nx idx t bd : Word) : Prop where
  head : LitAt b i hForall
  k : LitAt b (i + 8) kForallE
  bnd : BndAt b (i + 8 + 4) bd t
  ie : LitAt b (bE4 b (i + 8 + 4)) kIe
  ni : NumAt b (bE4 b (i + 8 + 4) + 7) (numR b (bE4 b (i + 8 + 4) + 7)).1 idx
  tail : LitAt b (numR b (bE4 b (i + 8 + 4) + 7)).1 kEnd1
  next : nx = (numR b (bE4 b (i + 8 + 4) + 7)).1 + 2

/-- The lines `fast_line` accepts, with the words it returns. -/
inductive Canon (b : Array UInt8) (i : Word) : List Word → Prop
  | app {nx idx f a : Word} : AppLine b i nx idx f a → Canon b i [nx, 10, idx, f, a, a]
  | lam {nx idx t bd : Word} : LamLine b i nx idx t bd → Canon b i [nx, 11, idx, t, bd, bd]
  | pi {nx idx t bd : Word} : ForallLine b i nx idx t bd → Canon b i [nx, 12, idx, t, bd, bd]

/-- What `fast_line(i)` returns: `0` (declined), or a canonical line's words. -/
def FastOK (b : Array UInt8) (i : Word) (v : List Word) : Prop := v.headD 0 ≠ 0 → Canon b i v

/-! ### The binder's value -/

section
variable {b : Array UInt8} {p : Word}

theorem lit8 (l : List UInt8) (hl : l.length = 8 := by decide) (hne : l ≠ [] := by decide)
    (h0 : 0 ∉ l := by decide) (h : le64 b p.toNat = litW l) : LitAt b p l :=
  (le64_lit8 b p l hl hne h0).mp h

theorem litm (l : List UInt8) (hl : l.length ≤ 8 := by decide) (hne : l ≠ [] := by decide)
    (h0 : 0 ∉ l := by decide) (h : le64 b p.toNat &&& mskW l.length = litW l) : LitAt b p l :=
  (le64_lit b p l hl hne h0).mp h

theorem biEnd_d (h : le64 b p.toNat = litW biD) : biEnd b p = p + 8 := by
  rw [biEnd, ite_eq_left h]
theorem biEnd_i (h0 : ¬ le64 b p.toNat = litW biD)
    (h : le64 b p.toNat = litW biI8 ∧ le64 b (p + 8).toNat &&& mskW 1 = litW kQ) :
    biEnd b p = p + 9 := by
  rw [biEnd, ite_eq_right h0, ite_eq_left h]
theorem biEnd_n (h0 : ¬ le64 b p.toNat = litW biD)
    (h1 : ¬ (le64 b p.toNat = litW biI8 ∧ le64 b (p + 8).toNat &&& mskW 1 = litW kQ))
    (h : le64 b p.toNat = litW biN8 ∧ le64 b (p + 8).toNat &&& mskW 5 = litW biN5) :
    biEnd b p = p + 13 := by
  rw [biEnd, ite_eq_right h0, ite_eq_right h1, ite_eq_left h]
theorem biEnd_s (h0 : ¬ le64 b p.toNat = litW biD)
    (h1 : ¬ (le64 b p.toNat = litW biI8 ∧ le64 b (p + 8).toNat &&& mskW 1 = litW kQ))
    (h2 : ¬ (le64 b p.toNat = litW biN8 ∧ le64 b (p + 8).toNat &&& mskW 5 = litW biN5))
    (h : le64 b p.toNat = litW biS8 ∧ le64 b (p + 8).toNat &&& mskW 7 = litW biS7) :
    biEnd b p = p + 15 := by
  rw [biEnd, ite_eq_right h0, ite_eq_right h1, ite_eq_right h2, ite_eq_left h]

theorem biAt_d (h : le64 b p.toNat = litW biD) : BiAt b p (biEnd b p) := by
  rw [biEnd, ite_eq_left h]; exact .dflt (lit8 biD (h := h))

theorem biAt_i (h0 : ¬ le64 b p.toNat = litW biD)
    (h : le64 b p.toNat = litW biI8 ∧ le64 b (p + 8).toNat &&& mskW 1 = litW kQ) :
    BiAt b p (biEnd b p) := by
  rw [biEnd, ite_eq_right h0, ite_eq_left h]
  exact .impl (lit8 biI8 (h := h.1)) (litm kQ (h := h.2))

theorem biAt_n (h0 : ¬ le64 b p.toNat = litW biD)
    (h1 : ¬ (le64 b p.toNat = litW biI8 ∧ le64 b (p + 8).toNat &&& mskW 1 = litW kQ))
    (h : le64 b p.toNat = litW biN8 ∧ le64 b (p + 8).toNat &&& mskW 5 = litW biN5) :
    BiAt b p (biEnd b p) := by
  rw [biEnd, ite_eq_right h0, ite_eq_right h1, ite_eq_left h]
  exact .inst (lit8 biN8 (h := h.1)) (litm biN5 (h := h.2))

theorem biAt_s (h0 : ¬ le64 b p.toNat = litW biD)
    (h1 : ¬ (le64 b p.toNat = litW biI8 ∧ le64 b (p + 8).toNat &&& mskW 1 = litW kQ))
    (h2 : ¬ (le64 b p.toNat = litW biN8 ∧ le64 b (p + 8).toNat &&& mskW 5 = litW biN5))
    (h : le64 b p.toNat = litW biS8 ∧ le64 b (p + 8).toNat &&& mskW 7 = litW biS7) :
    BiAt b p (biEnd b p) := by
  rw [biEnd, ite_eq_right h0, ite_eq_right h1, ite_eq_right h2, ite_eq_left h]
  exact .strict (lit8 biS8 (h := h.1)) (litm biS7 (h := h.2))

end

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

theorem litB8_spec (l : List UInt8) (hl : LitOK l) (h8 : l.length = 8) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) (litB8 l)
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      (r = .normal → s' = s₀.setLoc 1 (s₀.loc 1 + 8) ∧ LitAt b (s₀.loc 1) l) ∧
      (r ≠ .normal → r.retOr [0] = [0]); ⊤⦄ := by
  dsimp only [litB8]
  vcgen [step, L.evalE_spec, L.evalC_spec, evalArgs, setLoc, setLocs]
  all_goals subst_vars
  all_goals simp only [Cond.pval, Expr.pval, St.setLoc_loc, St.setLoc_mem, Cmp.eval, BinOp.eval,
      beq_iff_eq, bne_iff_ne, ne_eq, Nat.reduceEqDiff, reduceIte, Mem.src8, decide_eq_true_eq,
      Decidable.not_not] at *
  all_goals first
    | grind [Sig.retOr]
    | exact (le64_lit8 _ _ l h8 hl.ne hl.nz).mp ‹_›

theorem biB_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) biB
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      (r = .normal → s' = biS b s₀ ∧ BiAt b (s₀.loc 1) (biEnd b (s₀.loc 1))) ∧
      (r ≠ .normal → r.retOr [0] = [0]); ⊤⦄ := by
  dsimp only [biB]
  vcgen [step, L.evalE_spec, L.evalC_spec, evalArgs, setLoc, setLocs]
  all_goals subst_vars
  all_goals simp only [Cond.pval, Expr.pval, St.setLoc_loc, St.setLoc_mem, Cmp.eval, BinOp.eval,
      beq_iff_eq, bne_iff_ne, ne_eq, Nat.reduceEqDiff, reduceIte, Mem.src8, decide_eq_true_eq,
      Decidable.not_not, Bool.and_eq_true] at *
  all_goals first
    | grind [Sig.retOr]
    | (rw [biS, biEnd_d ‹_›])
    | (rw [biS, biEnd_i ‹_› ‹_›])
    | (rw [biS, biEnd_n ‹_› ‹_› ‹_›])
    | (rw [biS, biEnd_s ‹_› ‹_› ‹_› ‹_›])
    | exact biAt_d ‹_›
    | (apply biAt_i <;> assumption)
    | (apply biAt_n <;> assumption)
    | (apply biAt_s <;> assumption)

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
    UInt64.ofNat kIe.length = 7 ∧ UInt64.ofNat kEnd1.length = 2 ∧ UInt64.ofNat kNfo.length = 6 ∧
    UInt64.ofNat kEnd2.length = 3 ∧ UInt64.ofNat kForallE.length = 4 := by decide

theorem head_lam {b : Array UInt8} {i : Word} (h : le64 b i.toNat &&& mskW 6 = litW hIe) :
    LitAt b i hIe := litm hIe (h := h)

theorem head_forall {b : Array UInt8} {i : Word} (h : le64 b i.toNat = litW hForall) :
    LitAt b i hForall := lit8 hForall (h := h)

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
         | with_reducible assumption
         | with_reducible exact numAt_of_ok _ hb _ ‹_›)

-- the binder shapes are the longest straight-line code: about 60 paths after `vcgen`
set_option maxHeartbeats 1000000 in
theorem lamS_spec (hb : b.size < 2 ^ 63) (n : Nat) (s₀ : St)
    (hw : s₀.loc 8 = le64 b (s₀.loc 0).toNat) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) lamS
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ (r = .normal → s' = s₀) ∧
      (r ≠ .normal → FastOK b (s₀.loc 0) (r.retOr [])); ⊤⦄ := by
  dsimp only [lamS, bndB]
  vcgen [step, L.evalE_spec, L.evalC_spec, evalArgs, setLoc, setLocs,
    fun l hl => litB_spec p b l hl n, fun l hl h8 => litB8_spec p b l hl h8 n, numB_spec p b n,
    biB_spec p b n]
  all_goals (try subst_vars)
  all_goals simp only [Cond.pval, Expr.pval, St.setLoc_loc, St.setLoc_mem, Cmp.eval, BinOp.eval,
      beq_iff_eq, bne_iff_ne, ne_eq, Nat.reduceEqDiff, reduceIte, Mem.src8, decide_eq_true_eq,
      Decidable.not_not, Sig.retOr, FastOK, List.headD_cons, true_implies, reduceCtorEq,
      not_false_eq_true, true_and, not_true, false_implies, and_true, lit_len] at *
  all_goals repeat (cases ‹_ ∧ _›)
  all_goals (try subst_vars)
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, numS_loc, numS_mem, biS, Nat.reduceEqDiff,
    reduceIte, true_implies] at *)
  all_goals repeat (cases ‹_ ∧ _›)
  all_goals (try subst_vars)
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, numS_loc, numS_mem, biS, Nat.reduceEqDiff,
    reduceIte, true_implies] at *)
  all_goals first
    | (show LitOK _; exact ⟨by decide, by decide, by decide⟩)
    | (show List.length _ = 8; decide)
    | grind [Sig.retOr]
    | (intro _
       refine Canon.lam ⟨?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
       all_goals first
         | (rw [hw] at *; exact head_lam ‹_›)
         | rfl
         | with_reducible assumption
         | with_reducible exact numAt_of_ok _ hb _ ‹_›)

-- the binder shapes are the longest straight-line code: about 60 paths after `vcgen`
set_option maxHeartbeats 1000000 in
theorem forallS_spec (hb : b.size < 2 ^ 63) (n : Nat) (s₀ : St)
    (hw : s₀.loc 8 = le64 b (s₀.loc 0).toNat) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) forallS
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ (r = .normal → s' = s₀) ∧
      (r ≠ .normal → FastOK b (s₀.loc 0) (r.retOr [])); ⊤⦄ := by
  dsimp only [forallS, bndB]
  vcgen [step, L.evalE_spec, L.evalC_spec, evalArgs, setLoc, setLocs,
    fun l hl => litB_spec p b l hl n, fun l hl h8 => litB8_spec p b l hl h8 n, numB_spec p b n,
    biB_spec p b n]
  all_goals (try subst_vars)
  all_goals simp only [Cond.pval, Expr.pval, St.setLoc_loc, St.setLoc_mem, Cmp.eval, BinOp.eval,
      beq_iff_eq, bne_iff_ne, ne_eq, Nat.reduceEqDiff, reduceIte, Mem.src8, decide_eq_true_eq,
      Decidable.not_not, Sig.retOr, FastOK, List.headD_cons, true_implies, reduceCtorEq,
      not_false_eq_true, true_and, not_true, false_implies, and_true, lit_len] at *
  all_goals repeat (cases ‹_ ∧ _›)
  all_goals (try subst_vars)
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, numS_loc, numS_mem, biS, Nat.reduceEqDiff,
    reduceIte, true_implies] at *)
  all_goals repeat (cases ‹_ ∧ _›)
  all_goals (try subst_vars)
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, numS_loc, numS_mem, biS, Nat.reduceEqDiff,
    reduceIte, true_implies] at *)
  all_goals first
    | (show LitOK _; exact ⟨by decide, by decide, by decide⟩)
    | (show List.length _ = 8; decide)
    | grind [Sig.retOr]
    | (intro _
       refine Canon.pi ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
       all_goals first
         | (rw [hw] at *; exact head_forall ‹_›)
         | rfl
         | with_reducible assumption
         | with_reducible exact numAt_of_ok _ hb _ ‹_›)

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
      fun s₁ hw => appS_spec p b hb n s₁ hw, fun s₁ hw => lamS_spec p b hb n s₁ hw,
      fun s₁ hw => forallS_spec p b hb n s₁ hw]
    all_goals (try subst_vars)
    all_goals simp only [Cond.pval, Expr.pval, St.setLoc_loc, St.setLoc_mem, Cmp.eval, BinOp.eval,
      Mem.src8, Locals.init_cons_zero, Nat.reduceEqDiff, reduceIte, true_implies, reduceCtorEq,
      FastOK, Sig.retVal, Sig.retOr, List.headD_cons, List.headD_nil, ne_eq, not_true_eq_false,
      false_implies, implies_true] at *
    all_goals repeat (cases ‹_ ∧ _›)
    all_goals (try subst_vars)
    all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, Locals.init_cons_zero, reduceIte,
      Nat.reduceEqDiff] at *)
    all_goals first
      | grind
      | (cases ‹St›; simp_all)

end spec2
end L.Scan.Fast
