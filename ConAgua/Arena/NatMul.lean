module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.NatAdd
public import ConAgua.Arena.NatAdd
public import ConAgua.Arena.Word
public import ConAgua.Arena.NatOff
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.LocNF
import ConAgua.L.Records
import ConAgua.Arena.NatCmpFacts
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# `Nat.mul` on the limb pool

`nat_mul` (con-ron's `mul`/`mul_from`/`mul_u64`/`mul_u64_from`, `ron/nat.rs:490-545`) as the
in-place schoolbook product: zero the first `la` limbs at the top, then for each limb `y` of `b`
one multiply-accumulate pass of `a * y` into the result at offset `j`, then `nat_trim`. The
Rust builds `a * b[j]` and shift-adds it (only `Vec::push`, for its Aeneas proof); in L the
in-place form needs no second buffer.

The `u128` accumulator `t` of con-ron's `mul_u64_from` is a word pair: the low word is the
wrapping `x * y + t + c`, the high word `mac_hi(x, y, t, c)`, which uses L's `mulhi` and
comparisons as words (`u64(a < b)`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- `mac_hi(x, y, t, c)`: the high word of `x * y + t + c` (con-ron's `u128` accumulator `t` in
`mul_u64_from`). Straight-line: `mulhi` and two carries as `u64(…)` words. -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def macHi : FunDecl := lfn (x, y, t, c) locals (lo, hi) {
  lo := x * y + t;
  hi := mulhi(x, y) + u64(lo < t);
  lo := lo + c;
  return hi + u64(lo < c)
}

section mac
variable (p : Prog) (hph : p.lookup "mac_hi" = some macHi)

set_option maxHeartbeats 2000000 in
include hph in
theorem macHi_spec (n : Nat) (s₀ : St) (x y t c : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "mac_hi" [x, y, t, c]
    ⦃fun r s' => s' = s₀ ∧ (r.headD 0).toNat = macHiN x y t c; ⊤⦄ := by
  rw [invoke_eq _ hph]
  simp only [callFn, macHi]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] => vcgen [exec, step, evalE, evalArgs, setLoc] <;>
      finish [macHiN]

end mac

/-! ## The in-place passes: `mul_row`, `sub_row`, `mul_zeros`

Each works on a window `[o, o + n)` of the pool in place (con-ron's `mul_row`, `sub_row`,
`add_carry_at`, `sub_borrow_at`, `zeros`); the operand is read through its tier and index,
decoded once. A carry or borrow that would leave the window aborts (the callers' sums fit, so it
never happens; the proof then needs no bound on the sum). -/

/-- `P[o + i] += a[i] * y + c` for `i < la`. -/
def mrowLoop : Stmt := lblk (o, n, oa, la, y, i, c, x, t, lo, hi, ot, ob, qt, qb) {
  for i < la {
    x := POOL⟨qt⟩[qb + i];
    t := POOL⟨ot⟩[ob + i];
    lo := x * y + t;
    hi := mulhi(x, y) + u64(lo < t);
    lo := lo + c;
    POOL⟨ot⟩[ob + i] := lo;
    c := hi + u64(lo < c)
  }
}

/-- The carry ripple, inside the window. -/
def mcarryLoop : Stmt := lblk (o, n, oa, la, y, i, c, x, t, lo, hi, ot, ob, qt, qb) {
  while c != 0 {
    if n <= i { abort };
    t := POOL⟨ot⟩[ob + i] + c;
    POOL⟨ot⟩[ob + i] := t;
    c := u64(t < c);
    i += 1
  }
}

/-- `mul_row(o, n, oa, la, y)`: `P[o, o + n) += a * y` in place, `a = P[oa, oa + la)`, the window
not overlapping `a` (con-ron's `mul_row` and `add_carry_at`). With `y = 1` it is the in-place
addition of `a`. -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def mulRow : FunDecl := lfn (o, n, oa, la, y) locals (i, c, x, t, lo, hi, ot, ob, qt, qb) {
  if n < la { abort };
  ot := ⦃o⦄.tier;
  ob := ⦃o⦄.idx;
  qt := ⦃oa⦄.tier;
  qb := ⦃oa⦄.idx;
  ⟪mrowLoop⟫;
  ⟪mcarryLoop⟫;
  return 0
}

/-- `P[o + i] -= a[i] + c` for `i < la`. -/
def srowLoop : Stmt := lblk (o, n, oa, la, i, c, x, t, d, ot, ob, qt, qb) {
  for i < la {
    x := POOL⟨qt⟩[qb + i];
    t := POOL⟨ot⟩[ob + i];
    d := t - x;
    POOL⟨ot⟩[ob + i] := d - c;
    c := u64(t < x) + u64(d < c)
  }
}

/-- The borrow ripple, inside the window. -/
def sborrowLoop : Stmt := lblk (o, n, oa, la, i, c, x, t, d, ot, ob, qt, qb) {
  while c != 0 {
    if n <= i { abort };
    t := POOL⟨ot⟩[ob + i];
    POOL⟨ot⟩[ob + i] := t - 1;
    c := u64(t == 0);
    i += 1
  }
}

/-- `sub_row(o, n, oa, la)`: `P[o, o + n) -= a` in place (con-ron's `sub_row` and
`sub_borrow_at`). -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def subRow : FunDecl := lfn (o, n, oa, la) locals (i, c, x, t, d, ot, ob, qt, qb) {
  if n < la { abort };
  ot := ⦃o⦄.tier;
  ob := ⦃o⦄.idx;
  qt := ⦃oa⦄.tier;
  qb := ⦃oa⦄.idx;
  ⟪srowLoop⟫;
  ⟪sborrowLoop⟫;
  return 0
}

def zerosLoop : Stmt := lblk (o, n, i, ot, ob) {
  for i < n { POOL⟨ot⟩[ob + i] := 0 }
}

/-- `mul_zeros(o, n)`: `P[o, o + n) := 0` (con-ron's `zeros`). -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def mulZeros : FunDecl := lfn (o, n) locals (i, ot, ob) {
  ot := ⦃o⦄.tier;
  ob := ⦃o⦄.idx;
  ⟪zerosLoop⟫;
  return 0
}

/-! ## `mul_win`: the window product, accumulated in place -/

/-- `kara_mid(oa, la, ob, lb, s)`: the three products of a Karatsuba step on `a = a0 + a1 B^k`,
`b = b0 + b1 B^k` (`k = ceil(la / 2)`, `la / 2 < lb ≤ la`), into the scratch block from `s`:
`z0 = a0 b0` at `[s, s + 2k)`, `z2 = a1 b1` at `[s + 2k, s + la + lb)`, the sums `a0 + a1` and
`b0 + b1` (`k + 1` limbs each) above them, and `z1 = (a0 + a1)(b0 + b1) - z0 - z2` at
`sp = s + la + lb + 2k + 2`, of the length it returns (trimmed). The scratch of its own products
starts at `s2 = sp + 2k + 2`. -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def karaMid : FunDecl := lfn (oa, la, ob, lb, s) locals (k, z2, n2, sa, sb, sp, s2, u) {
  k := la - (la >> 1);
  z2 := s + 2 * k;
  n2 := la + lb - 2 * k;
  sa := s + la + lb;
  sb := sa + k + 1;
  sp := sb + k + 1;
  s2 := sp + 2 * k + 2;
  if ⟪2 ^ 41⟫ <= s2 { abort };
  u := call mul_zeros(s, s2 - s);
  u := call mul_win(oa, k, ob, k, s, 2 * k, s2);
  u := call mul_win(oa + k, la - k, ob + k, lb - k, z2, n2, s2);
  u := call mul_row(sa, k + 1, oa, k, 1);
  u := call mul_row(sa, k + 1, oa + k, la - k, 1);
  u := call mul_row(sb, k + 1, ob, k, 1);
  u := call mul_row(sb, k + 1, ob + k, lb - k, 1);
  u := call mul_win(sa, k + 1, sb, k + 1, sp, 2 * k + 2, s2);
  u := call sub_row(sp, 2 * k + 2, s, 2 * k);
  u := call sub_row(sp, 2 * k + 2, z2, n2);
  u := call nat_trim(sp, 2 * k + 2);
  return u
}

/-- The schoolbook rows: one `mul_row` per limb of the shorter operand `b`. -/
def rowsLoop : Stmt := lblk (oa, la, ob, lb, o, n, s, k, l, u, j, y) {
  for j < lb {
    y := POOL⦃ob + j⦄;
    u := call mul_row(o + j, n - j, oa, la, y)
  }
}

/-- `mul_win(oa, la, ob, lb, o, n, s)`: `P[o, o + n) += a * b` in place, for the windows
`a = P[oa, oa + la)` and `b = P[ob, ob + lb)` (con-ron's `mul_win`), with scratch space from `s`
up. Below `T` limbs in the shorter window: schoolbook rows; an operand at least twice as long
as the other is halved, both halves accumulating into the window; otherwise Karatsuba at
`k = ceil(la / 2)` (`kara_mid`), then `P[o, o + n) += z0 + z1 B^k + z2 B^2k`. -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def mulWinG (T : Word) : FunDecl :=
  lfn (oa, la, ob, lb, o, n, s) locals (k, l, u, j, y) {
  if n < la + lb { abort };
  if la < lb {
    u := call mul_win(ob, lb, oa, la, o, n, s);
    return 0
  };
  if lb < ⟪T⟫ {
    ⟪rowsLoop⟫;
    return 0
  };
  if lb <= la >> 1 {
    k := la >> 1;
    u := call mul_win(oa, k, ob, lb, o, n, s);
    u := call mul_win(oa + k, la - k, ob, lb, o + k, n - k, s);
    return 0
  };
  k := la - (la >> 1);
  l := call kara_mid(oa, la, ob, lb, s);
  u := call mul_row(o, n, s, 2 * k, 1);
  u := call mul_row(o + k, n - k, s + la + lb + 2 * k + 2, l, 1);
  u := call mul_row(o + 2 * k, n - 2 * k, s + 2 * k, la + lb - 2 * k, 1);
  return 0
}

/-- The Karatsuba threshold: below this many limbs in the shorter operand, schoolbook (measured,
docs/design/bigmul.md). -/
def karaT : Word := 48

/-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat` -/
@[no_expose] def mulWin : FunDecl := mulWinG karaT

/-! ## `nat_mul(oa, la, ob, lb)`: append `a * b` to the pool, return its length -/

/-- `nat_mul` at the threshold `T`. -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def natMulG (T : Word) : FunDecl := lfn (oa, la, ob, lb) locals (top, n, m, pt, pb, u) {
  top := CTL.u64[0];
  pt := ⦃top⦄.tier;
  pb := top - ⦃top⦄.base;
  n := la + lb;
  m := n;
  if ⟪T⟫ <= la && ⟪T⟫ <= lb { m := 9 * n + 1024 };
  if len(POOL⟨pt⟩) - pb < m { abort };
  u := call mul_zeros(top, n);
  u := call mul_win(oa, la, ob, lb, top, n, top + n);
  n := call nat_trim(top, n);
  CTL.u64[0] := top + n;
  return n
}

/-- con-ron: ConRon/Arena/Core.lean:1152-1185 ConRon.Arena.natBinOpResult -/
@[no_expose, l_impl ConRon.Arena.natBinOpResult]
def natMul : FunDecl := natMulG karaT

/-- The pool functions with `nat_mul`. -/
def natMulProg : Prog := natProg ++ [("mac_hi", macHi), ("mul_row", mulRow), ("sub_row", subRow),
  ("mul_zeros", mulZeros), ("kara_mid", karaMid), ("mul_win", mulWin), ("nat_mul", natMul)]

/-- `natMulProg` at another threshold (tests). -/
def natMulProgT (T : Word) : Prog := natProg ++ [("mac_hi", macHi), ("mul_row", mulRow),
  ("sub_row", subRow), ("mul_zeros", mulZeros), ("kara_mid", karaMid), ("mul_win", mulWinG T),
  ("nat_mul", natMulG T)]

/- `(2^64 - 1)^2 = 2^128 - 2^65 + 1`: limbs `[1, 2^64 - 2]`. -/
#guard (run natMulProg 1000 "nat_mul" [0, 1, 0, 1]
  (Mem.ofWords [(POOL, #[0xFFFFFFFFFFFFFFFF, 0, 0, 0]), (CTL, #[1])])).toOption.map (fun (r, m) => (r, m.arr64 POOL, m.arr64 CTL)) ==
  some ([2], #[0xFFFFFFFFFFFFFFFF, 1, 0xFFFFFFFFFFFFFFFE, 0], #[3])

/- `(2^64 + 3) * 5 = 5 * 2^64 + 15`, and `0 * a = 0` (length 0). -/
#guard (run natMulProg 1000 "nat_mul" [0, 2, 2, 1]
  (Mem.ofWords [(POOL, #[3, 1, 5, 0, 0, 0]), (CTL, #[3])])).toOption.map (fun (r, m) => (r, m.arr64 POOL, m.arr64 CTL)) ==
  some ([2], #[3, 1, 5, 15, 5, 0], #[5])
#guard (run natMulProg 1000 "nat_mul" [0, 2, 2, 0]
  (Mem.ofWords [(POOL, #[3, 1, 0, 0]), (CTL, #[2])])).toOption.map (·.1) == some [0]

/-! ## The passes' specs -/

section passes
variable (p : Prog) (P0 : Array Word) (C : Nat)

/-- The inline multiply-accumulate of `mul_row`: the low word `x * y + t + c` and the high word
`mulhi(x, y) + u64(lo < t) + u64(lo + c < c)` are `x * y + t + c` (the high word cannot
overflow: `(2^64 - 1)^2 + 2 (2^64 - 1) < 2^128`). -/
theorem mac_inl (x y t c : Word) :
    (x * y + t + c).toNat +
        (UInt64.ofNat (x.toNat * y.toNat / 2 ^ 64) + Cmp.ult.evalW (x * y + t) t +
          Cmp.ult.evalW (x * y + t + c) c).toNat * 2 ^ 64 =
      x.toNat * y.toNat + t.toNat + c.toNat := by
  have hm := mul_split x y
  have hl := mulHiN_le x y
  have hx := x.toNat_lt; have hy := y.toNat_lt; have ht := t.toNat_lt; have hc := c.toNat_lt
  have hh : (UInt64.ofNat (x.toNat * y.toNat / 2 ^ 64)).toNat = mulHiN x y := mulhi_toNat x y
  simp only [mulHiN] at hm hh
  generalize x.toNat * y.toNat = P at *
  simp only [Cmp.evalW, Cmp.eval, decide_eq_true_eq, UInt64.lt_iff_toNat_lt]
  have e1 : (x * y + t).toNat = ((x * y).toNat + t.toNat) % 2 ^ 64 := UInt64.toNat_add _ _
  have e2 : (x * y + t + c).toNat = ((x * y + t).toNat + c.toNat) % 2 ^ 64 := UInt64.toNat_add _ _
  split <;> split <;>
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat, UInt64.toNat_one, UInt64.toNat_zero, hh] <;>
    omega

/-- Word sums of positions below `2^41` do not wrap. -/
theorem w_add (a b : Word) (h : a.toNat + b.toNat < 2 ^ 64) : (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h

/-- Positions inside a window pass: `T + i < 2^41` once the store at `⦃T⦄.idx + i` is in bounds. -/
theorem win_lt (m : Mem) (T i : Word) (hT : T.toNat < 2 ^ 41) (hi : i.toNat < 2 ^ 41)
    (hs : (m.arr64 (tierA POOL (T >>> 40))).size ≤ 2 ^ 40)
    (hb : ((T &&& 1099511627775) + i).toNat < (m.arr64 (tierA POOL (T >>> 40))).size) :
    T.toNat + i.toNat < 2 ^ 41 := by
  have := tag_idx_lt T; have := tag_split T; have := tag_tier_le T hT
  rw [w_add _ _ (by omega)] at hb; omega

/-- A load at `⦃T⦄.tier`, `⦃T⦄.idx + i` that succeeds reads the virtual pool at `T + i`. -/
theorem ld_win (m : Mem) (T i : Word) (hT : T.toNat < 2 ^ 41) (hi : i.toNat < 2 ^ 41)
    (hs : (m.arr64 (tierA POOL (T >>> 40))).size ≤ 2 ^ 40)
    (hb : ((T &&& 1099511627775) + i).toNat < (m.arr64 (tierA POOL (T >>> 40))).size) :
    (m.arr64 (tierA POOL (T >>> 40)))[((T &&& 1099511627775) + i).toNat] =
      (vpool m)[T.toNat + i.toNat]'(by rw [vpool_size]; exact win_lt m T i hT hi hs hb) := by
  have hk : (T &&& 1099511627775).toNat + i.toNat < 2 ^ 40 := by
    have := tag_idx_lt T; rw [w_add _ _ (by omega)] at hb; omega
  have hk2 : (T.toNat + i.toNat) < 2 ^ 41 := by
    have := tag_split T; have := tag_tier_le T hT; omega
  rw [vpool_ldidx m T i hT hb hs hk (by rw [vpool_size, w_add _ _ (by omega)]; omega)]
  simp only [w_add T i (by omega)]

/-- A store at `⦃T⦄.tier`, `⦃T⦄.idx + i` that succeeds writes the virtual pool at `T + i`. -/
theorem st_win (m : Mem) (T i v : Word) (hT : T.toNat < 2 ^ 41) (hi : i.toNat < 2 ^ 41)
    (hs : (m.arr64 (tierA POOL (T >>> 40))).size ≤ 2 ^ 40)
    (hb : ((T &&& 1099511627775) + i).toNat < (m.arr64 (tierA POOL (T >>> 40))).size) :
    vpool (m.set64 (tierA POOL (T >>> 40)) ((T &&& 1099511627775) + i) v) =
      (vpool m).set! (T.toNat + i.toNat) v := by
  have hk : (T &&& 1099511627775).toNat + i.toNat < 2 ^ 40 := by
    have := tag_idx_lt T; rw [w_add _ _ (by omega)] at hb; omega
  rw [vpool_stidx m T i v hT hb hs hk, w_add T i (by omega)]

/-- One step of `mul_row`'s row loop, in the shape of its verification condition. -/
theorem mrow_step_goal (m : Mem) (P0 : Array Word) (o oa y i c T11 T12 T13 T14 : Word)
    (h11 : T11 = o >>> 40) (h12 : T12 = o &&& 1099511627775)
    (h13 : T13 = oa >>> 40) (h14 : T14 = oa &&& 1099511627775)
    (hP0 : P0.size = 2 ^ 41) (ho : o.toNat + i.toNat < 2 ^ 41) (hoa : oa.toNat + i.toNat < 2 ^ 41)
    (hdis : oa.toNat + i.toNat < o.toNat ∨ o.toNat ≤ oa.toNat)
    (hs11 : (m.arr64 (tierA POOL T11)).size ≤ 2 ^ 40) (hs13 : (m.arr64 (tierA POOL T13)).size ≤ 2 ^ 40)
    (hb13 : (T14 + i).toNat < (m.arr64 (tierA POOL T13)).size)
    (hb11 : (T12 + i).toNat < (m.arr64 (tierA POOL T11)).size)
    (hoff : Off (vpool m) P0 o.toNat i.toNat)
    (ih : pv (vpool m) o.toNat i.toNat + c.toNat * wt i.toNat =
      pv P0 o.toNat i.toNat + pv P0 oa.toNat i.toNat * y.toNat) :
    pv (vpool (m.set64 (tierA POOL T11) (T12 + i)
        ((m.arr64 (tierA POOL T13))[(T14 + i).toNat] * y + (m.arr64 (tierA POOL T11))[(T12 + i).toNat] + c)))
        o.toNat (i + 1).toNat +
      (UInt64.ofNat ((m.arr64 (tierA POOL T13))[(T14 + i).toNat].toNat * y.toNat / 2 ^ 64) +
          Cmp.ult.evalW ((m.arr64 (tierA POOL T13))[(T14 + i).toNat] * y +
            (m.arr64 (tierA POOL T11))[(T12 + i).toNat]) (m.arr64 (tierA POOL T11))[(T12 + i).toNat] +
          Cmp.ult.evalW ((m.arr64 (tierA POOL T13))[(T14 + i).toNat] * y +
            (m.arr64 (tierA POOL T11))[(T12 + i).toNat] + c) c).toNat * wt (i + 1).toNat =
    pv P0 o.toNat (i + 1).toNat + pv P0 oa.toNat (i + 1).toNat * y.toNat := by
  subst h11 h12 h13 h14
  have hi1 : (i + 1).toNat = i.toNat + 1 := w_add i 1 (by simp; omega)
  have ex := ld_win m oa i (by omega) (by omega) hs13 hb13
  have et := ld_win m o i (by omega) (by omega) hs11 hb11
  have hvs := vpool_size m
  have ex' : (vpool m)[oa.toNat + i.toNat]'(by omega) = P0[oa.toNat + i.toNat]'(by omega) := by
    have := hoff (oa.toNat + i.toNat) (by omega)
    simp only [Array.getElem?_eq_getElem (by omega : oa.toNat + i.toNat < (vpool m).size),
      Array.getElem?_eq_getElem (by omega : oa.toNat + i.toNat < P0.size), Option.some.injEq] at this
    exact this
  have et' : (vpool m)[o.toNat + i.toNat]'(by omega) = P0[o.toNat + i.toNat]'(by omega) :=
    Off.get _ _ _ _ _ hoff (by omega) (by omega) (by omega)
  rw [st_win m o i _ (by omega) (by omega) hs11 hb11, ex, et, ex', et']
  have hmac := mac_inl P0[oa.toNat + i.toNat] y P0[o.toNat + i.toNat] c
  generalize (UInt64.ofNat _ + _ + _ : Word) = c' at hmac ⊢
  rw [hi1, pv_set_succ (vpool m) o.toNat i.toNat (i.toNat + 1) (o.toNat + i.toNat) _ rfl rfl (by omega),
    pv_succ P0 o.toNat i.toNat (i.toNat + 1) (o.toNat + i.toNat) rfl rfl (by omega),
    pv_succ P0 oa.toNat i.toNat (i.toNat + 1) (oa.toNat + i.toNat) rfl rfl (by omega),
    wt_succ i.toNat (i.toNat + 1) rfl]
  generalize pv (vpool m) o.toNat i.toNat = A at *
  generalize pv P0 o.toNat i.toNat = B at *
  generalize pv P0 oa.toNat i.toNat = D at *
  generalize wt i.toNat = W at *
  grind

/-- A window pass's value, from its changed prefix to the whole window. -/
theorem win_close (p q : Array Word) (o i n X : Nat) (hoff : Off p q o i) (hi : i ≤ n)
    (h : pv p o i = pv q o i + X) : pv p o n = pv q o n + X := by
  have e1 := pv_append p o i (n - i); have e2 := pv_append q o i (n - i)
  rw [show i + (n - i) = n by omega] at e1 e2
  rw [e1, e2, Off.pv_disj p q o i (o + i) (n - i) hoff (Or.inr (Nat.le_refl _)), h]; omega

/-- `win_close` without the sum, for `grind`: a pass's changed prefix and the whole window. -/
theorem off_split (p q : Array Word) (o i n : Nat) (hoff : Off p q o i) (hi : i ≤ n) :
    pv p o n + pv q o i = pv q o n + pv p o i := by
  have e1 := pv_append p o i (n - i); have e2 := pv_append q o i (n - i)
  rw [show i + (n - i) = n by omega] at e1 e2
  rw [e1, e2, Off.pv_disj p q o i (o + i) (n - i) hoff (Or.inr (Nat.le_refl _))]; omega

/-- One step of a carry ripple (`t := P[o + i] + c`), in the shape of its verification
condition. -/
theorem carry_step_goal (m : Mem) (P0 : Array Word) (o i c T11 T12 : Word) (X : Nat)
    (h11 : T11 = o >>> 40) (h12 : T12 = o &&& 1099511627775)
    (hP0 : P0.size = 2 ^ 41) (ho : o.toNat + i.toNat < 2 ^ 41)
    (hs11 : (m.arr64 (tierA POOL T11)).size ≤ 2 ^ 40)
    (hb11 : (T12 + i).toNat < (m.arr64 (tierA POOL T11)).size)
    (hoff : Off (vpool m) P0 o.toNat i.toNat)
    (ih : pv (vpool m) o.toNat i.toNat + c.toNat * wt i.toNat = pv P0 o.toNat i.toNat + X) :
    pv (vpool (m.set64 (tierA POOL T11) (T12 + i) ((m.arr64 (tierA POOL T11))[(T12 + i).toNat] + c)))
        o.toNat (i + 1).toNat +
      (Cmp.ult.evalW ((m.arr64 (tierA POOL T11))[(T12 + i).toNat] + c) c).toNat * wt (i + 1).toNat =
    pv P0 o.toNat (i + 1).toNat + X := by
  subst h11 h12
  have hi1 : (i + 1).toNat = i.toNat + 1 := w_add i 1 (by simp; omega)
  have et := ld_win m o i (by omega) (by omega) hs11 hb11
  have hvs := vpool_size m
  have et' : (vpool m)[o.toNat + i.toNat]'(by omega) = P0[o.toNat + i.toNat]'(by omega) :=
    Off.get _ _ _ _ _ hoff (by omega) (by omega) (by omega)
  rw [st_win m o i _ (by omega) (by omega) hs11 hb11, et, et']
  have hc : (P0[o.toNat + i.toNat] + c).toNat + (Cmp.ult.evalW (P0[o.toNat + i.toNat] + c) c).toNat * 2 ^ 64 =
      P0[o.toNat + i.toNat].toNat + c.toNat := by
    have := (P0[o.toNat + i.toNat]).toNat_lt; have := c.toNat_lt
    simp only [Cmp.evalW, Cmp.eval, decide_eq_true_eq, UInt64.lt_iff_toNat_lt, UInt64.toNat_add]
    split <;> simp <;> omega
  generalize (Cmp.ult.evalW _ c : Word) = c' at hc ⊢
  rw [hi1, pv_set_succ (vpool m) o.toNat i.toNat (i.toNat + 1) (o.toNat + i.toNat) _ rfl rfl (by omega),
    pv_succ P0 o.toNat i.toNat (i.toNat + 1) (o.toNat + i.toNat) rfl rfl (by omega),
    wt_succ i.toNat (i.toNat + 1) rfl]
  generalize pv (vpool m) o.toNat i.toNat = A at *
  generalize pv P0 o.toNat i.toNat = B at *
  generalize wt i.toNat = W at *
  grind

/-- The inline subtract-with-borrow of `sub_row`: `d = t - x`, the limb `d - c`, the borrow
`u64(t < x) + u64(d < c)`. -/
theorem sbb_inl (t x c : Word) (hc : c.toNat ≤ 1) :
    (t - x - c).toNat + x.toNat + c.toNat =
      t.toNat + (Cmp.ult.evalW t x + Cmp.ult.evalW (t - x) c).toNat * 2 ^ 64 := by
  have hx := x.toNat_lt; have ht := t.toNat_lt
  simp only [Cmp.evalW, Cmp.eval, decide_eq_true_eq, UInt64.lt_iff_toNat_lt]
  have e1 : (t - x).toNat = (2 ^ 64 - x.toNat + t.toNat) % 2 ^ 64 := UInt64.toNat_sub _ _
  have e2 : (t - x - c).toNat = (2 ^ 64 - c.toNat + (t - x).toNat) % 2 ^ 64 := UInt64.toNat_sub _ _
  split <;> split <;> simp only [UInt64.toNat_add, UInt64.toNat_one, UInt64.toNat_zero] <;> omega

theorem sbb_inl_le (t x c : Word) (hc : c.toNat ≤ 1) :
    (Cmp.ult.evalW t x + Cmp.ult.evalW (t - x) c).toNat ≤ 1 := by
  have hx := x.toNat_lt; have ht := t.toNat_lt
  have e1 : (t - x).toNat = (2 ^ 64 - x.toNat + t.toNat) % 2 ^ 64 := UInt64.toNat_sub _ _
  simp only [Cmp.evalW, Cmp.eval, decide_eq_true_eq, UInt64.lt_iff_toNat_lt]
  split <;> split <;> simp only [UInt64.toNat_add, UInt64.toNat_one, UInt64.toNat_zero] <;> omega

/-- One step of `sub_row`'s loop, in the shape of its verification condition. -/
theorem srow_step_goal (m : Mem) (P0 : Array Word) (o oa i c T9 T10 T11 T12 : Word)
    (h9 : T9 = o >>> 40) (h10 : T10 = o &&& 1099511627775)
    (h11 : T11 = oa >>> 40) (h12 : T12 = oa &&& 1099511627775)
    (hP0 : P0.size = 2 ^ 41) (ho : o.toNat + i.toNat < 2 ^ 41) (hoa : oa.toNat + i.toNat < 2 ^ 41)
    (hdis : oa.toNat + i.toNat < o.toNat ∨ o.toNat ≤ oa.toNat) (hc : c.toNat ≤ 1)
    (hs9 : (m.arr64 (tierA POOL T9)).size ≤ 2 ^ 40) (hs11 : (m.arr64 (tierA POOL T11)).size ≤ 2 ^ 40)
    (hb11 : (T12 + i).toNat < (m.arr64 (tierA POOL T11)).size)
    (hb9 : (T10 + i).toNat < (m.arr64 (tierA POOL T9)).size)
    (hoff : Off (vpool m) P0 o.toNat i.toNat)
    (ih : pv (vpool m) o.toNat i.toNat + pv P0 oa.toNat i.toNat = pv P0 o.toNat i.toNat + c.toNat * wt i.toNat) :
    pv (vpool (m.set64 (tierA POOL T9) (T10 + i)
        ((m.arr64 (tierA POOL T9))[(T10 + i).toNat] - (m.arr64 (tierA POOL T11))[(T12 + i).toNat] - c)))
        o.toNat (i + 1).toNat + pv P0 oa.toNat (i + 1).toNat =
      pv P0 o.toNat (i + 1).toNat +
        (Cmp.ult.evalW (m.arr64 (tierA POOL T9))[(T10 + i).toNat] (m.arr64 (tierA POOL T11))[(T12 + i).toNat] +
          Cmp.ult.evalW ((m.arr64 (tierA POOL T9))[(T10 + i).toNat] - (m.arr64 (tierA POOL T11))[(T12 + i).toNat])
            c).toNat * wt (i + 1).toNat := by
  subst h9 h10 h11 h12
  have hi1 : (i + 1).toNat = i.toNat + 1 := w_add i 1 (by simp; omega)
  have ex := ld_win m oa i (by omega) (by omega) hs11 hb11
  have et := ld_win m o i (by omega) (by omega) hs9 hb9
  have hvs := vpool_size m
  have ex' : (vpool m)[oa.toNat + i.toNat]'(by omega) = P0[oa.toNat + i.toNat]'(by omega) := by
    have := hoff (oa.toNat + i.toNat) (by omega)
    simp only [Array.getElem?_eq_getElem (by omega : oa.toNat + i.toNat < (vpool m).size),
      Array.getElem?_eq_getElem (by omega : oa.toNat + i.toNat < P0.size), Option.some.injEq] at this
    exact this
  have et' : (vpool m)[o.toNat + i.toNat]'(by omega) = P0[o.toNat + i.toNat]'(by omega) :=
    Off.get _ _ _ _ _ hoff (by omega) (by omega) (by omega)
  rw [st_win m o i _ (by omega) (by omega) hs9 hb9, ex, et, ex', et']
  have hsb := sbb_inl P0[o.toNat + i.toNat] P0[oa.toNat + i.toNat] c hc
  generalize (Cmp.ult.evalW _ _ + _ : Word) = c' at hsb ⊢
  rw [hi1, pv_set_succ (vpool m) o.toNat i.toNat (i.toNat + 1) (o.toNat + i.toNat) _ rfl rfl (by omega),
    pv_succ P0 o.toNat i.toNat (i.toNat + 1) (o.toNat + i.toNat) rfl rfl (by omega),
    pv_succ P0 oa.toNat i.toNat (i.toNat + 1) (oa.toNat + i.toNat) rfl rfl (by omega),
    wt_succ i.toNat (i.toNat + 1) rfl]
  generalize pv (vpool m) o.toNat i.toNat = A at *
  generalize pv P0 o.toNat i.toNat = B at *
  generalize pv P0 oa.toNat i.toNat = D at *
  generalize wt i.toNat = W at *
  grind

/-- One step of a borrow ripple (`P[o + i] -= 1`), in the shape of its verification condition. -/
theorem borrow_step_goal (m : Mem) (P0 : Array Word) (o i T9 T10 : Word) (X : Nat)
    (h9 : T9 = o >>> 40) (h10 : T10 = o &&& 1099511627775)
    (hP0 : P0.size = 2 ^ 41) (ho : o.toNat + i.toNat < 2 ^ 41)
    (hs9 : (m.arr64 (tierA POOL T9)).size ≤ 2 ^ 40)
    (hb9 : (T10 + i).toNat < (m.arr64 (tierA POOL T9)).size)
    (hoff : Off (vpool m) P0 o.toNat i.toNat)
    (ih : pv (vpool m) o.toNat i.toNat + X = pv P0 o.toNat i.toNat + wt i.toNat) :
    pv (vpool (m.set64 (tierA POOL T9) (T10 + i) ((m.arr64 (tierA POOL T9))[(T10 + i).toNat] - 1)))
        o.toNat (i + 1).toNat + X =
      pv P0 o.toNat (i + 1).toNat +
        (Cmp.eq.evalW (m.arr64 (tierA POOL T9))[(T10 + i).toNat] 0).toNat * wt (i + 1).toNat := by
  subst h9 h10
  have hi1 : (i + 1).toNat = i.toNat + 1 := w_add i 1 (by simp; omega)
  have et := ld_win m o i (by omega) (by omega) hs9 hb9
  have hvs := vpool_size m
  have et' : (vpool m)[o.toNat + i.toNat]'(by omega) = P0[o.toNat + i.toNat]'(by omega) :=
    Off.get _ _ _ _ _ hoff (by omega) (by omega) (by omega)
  rw [st_win m o i _ (by omega) (by omega) hs9 hb9, et, et']
  have hb : (P0[o.toNat + i.toNat] - 1).toNat + 1 =
      P0[o.toNat + i.toNat].toNat + (Cmp.eq.evalW P0[o.toNat + i.toNat] 0).toNat * 2 ^ 64 := by
    have := (P0[o.toNat + i.toNat]).toNat_lt
    simp only [Cmp.evalW, Cmp.eval, beq_iff_eq]
    have e1 : (P0[o.toNat + i.toNat] - 1).toNat = (2 ^ 64 - 1 + P0[o.toNat + i.toNat].toNat) % 2 ^ 64 :=
      UInt64.toNat_sub _ _
    split
    · rename_i h; rw [h]; rfl
    · rename_i h
      have : P0[o.toNat + i.toNat].toNat ≠ 0 := fun h' => h (UInt64.toNat_inj.mp (by simpa using h'))
      simp only [UInt64.toNat_zero]; omega
  generalize (Cmp.eq.evalW _ 0 : Word) = c' at hb ⊢
  rw [hi1, pv_set_succ (vpool m) o.toNat i.toNat (i.toNat + 1) (o.toNat + i.toNat) _ rfl rfl (by omega),
    pv_succ P0 o.toNat i.toNat (i.toNat + 1) (o.toNat + i.toNat) rfl rfl (by omega),
    wt_succ i.toNat (i.toNat + 1) rfl]
  generalize pv (vpool m) o.toNat i.toNat = A at *
  generalize pv P0 o.toNat i.toNat = B at *
  generalize wt i.toNat = W at *
  grind

/-- The tier facts of a window pass over `[o, o + n)` reading `[oa, oa + la)`: locals `o`, `n`,
`oa`, `la` at `0`-`3`, the decoded tiers and indices at `ot`, `ob`, `qt`, `qb`. -/
def WinBase (P0 : Array Word) (C : Nat) (ot ob qt qb : Nat) (s : St) : Prop :=
  C < 2 ^ 64 ∧ P0.size = 2 ^ 41 ∧ pcap s.mem = C ∧
  (s.loc 0).toNat + (s.loc 1).toNat ≤ C ∧ (s.loc 2).toNat + (s.loc 3).toNat ≤ C ∧
  (s.loc 3).toNat ≤ (s.loc 1).toNat ∧
  ((s.loc 2).toNat + (s.loc 3).toNat ≤ (s.loc 0).toNat ∨
    (s.loc 0).toNat + (s.loc 1).toNat ≤ (s.loc 2).toNat) ∧
  s.loc ot = s.loc 0 >>> 40 ∧ s.loc ob = s.loc 0 &&& 1099511627775 ∧
  s.loc qt = s.loc 2 >>> 40 ∧ s.loc qb = s.loc 2 &&& 1099511627775 ∧
  (s.mem.arr64 (tierA POOL (s.loc ot))).size ≤ 2 ^ 40 ∧
  (s.mem.arr64 (tierA POOL (s.loc qt))).size ≤ 2 ^ 40

/-- `mul_row`'s row loop: locals `(o, n, oa, la, y, i, c, x, t, lo, hi, ot, ob, qt, qb)`. -/
def MRowInv (P0 : Array Word) (C : Nat) (s : St) : Prop :=
  WinBase P0 C 11 12 13 14 s ∧ (s.loc 5).toNat ≤ (s.loc 3).toNat ∧
  Off (vpool s.mem) P0 (s.loc 0).toNat (s.loc 5).toNat ∧
  pv (vpool s.mem) (s.loc 0).toNat (s.loc 5).toNat + (s.loc 6).toNat * wt (s.loc 5).toNat =
    pv P0 (s.loc 0).toNat (s.loc 5).toNat + pv P0 (s.loc 2).toNat (s.loc 5).toNat * (s.loc 4).toNat

def MRowPost (P0 : Array Word) (C : Nat) (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ PFrame s₀.mem s'.mem ∧ pcap s'.mem = C ∧
  s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧
  s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 3 ∧
  s'.loc 11 = s₀.loc 11 ∧ s'.loc 12 = s₀.loc 12 ∧ s'.loc 13 = s₀.loc 13 ∧ s'.loc 14 = s₀.loc 14 ∧
  Off (vpool s'.mem) P0 (s₀.loc 0).toNat (s₀.loc 3).toNat ∧
  pv (vpool s'.mem) (s₀.loc 0).toNat (s₀.loc 3).toNat + (s'.loc 6).toNat * wt (s₀.loc 3).toNat =
    pv P0 (s₀.loc 0).toNat (s₀.loc 3).toNat + pv P0 (s₀.loc 2).toNat (s₀.loc 3).toNat * (s₀.loc 4).toNat

set_option maxHeartbeats 2000000 in
theorem mrowLoop_spec (n : Nat) (s₀ : St) (h : MRowInv P0 C s₀) :
    ⦃fun s => s = s₀⦄ exec p n mrowLoop ⦃fun r s' => MRowPost P0 C s₀ r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [MRowInv, WinBase, MRowPost] at h ⊢
    rw [exec, step_while (w := mrowLoop) rfl]
    vcgen [step, evalE, evalC, setLoc, setLocs, ld64, st64, ih]
    all_goals clear ih
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, Cmp.eval, BinOp.eval,
      Nat.reduceEqDiff, reduceIte, decide_eq_true_eq] at *)
    all_goals (try simp only [MRowInv, MRowPost, WinBase] at *)
    all_goals (try subst_vars)
    all_goals (try and_intros)
    all_goals (try dsimp (config := { decide := true }) only [L.St.setLoc_mem, St.setLoc, reduceIte] at *)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, Cmp.eval, BinOp.eval, Mem.size64_set64,
      Nat.reduceEqDiff, reduceIte, decide_eq_true_eq] at *)
    all_goals first
      | (with_reducible apply mrow_step_goal <;> grind [pcap_eq])
      | grind (splits := 8) [arena_grind, lang_grind]

/-- `mul_row`'s carry ripple. -/
def MCarryInv (P0 : Array Word) (C : Nat) (s : St) : Prop :=
  WinBase P0 C 11 12 13 14 s ∧ (s.loc 5).toNat ≤ (s.loc 1).toNat ∧
  Off (vpool s.mem) P0 (s.loc 0).toNat (s.loc 5).toNat ∧
  pv (vpool s.mem) (s.loc 0).toNat (s.loc 5).toNat + (s.loc 6).toNat * wt (s.loc 5).toNat =
    pv P0 (s.loc 0).toNat (s.loc 5).toNat + pv P0 (s.loc 2).toNat (s.loc 3).toNat * (s.loc 4).toNat

def MCarryPost (P0 : Array Word) (C : Nat) (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ PFrame s₀.mem s'.mem ∧ pcap s'.mem = C ∧
  Off (vpool s'.mem) P0 (s₀.loc 0).toNat (s₀.loc 1).toNat ∧
  pv (vpool s'.mem) (s₀.loc 0).toNat (s₀.loc 1).toNat =
    pv P0 (s₀.loc 0).toNat (s₀.loc 1).toNat + pv P0 (s₀.loc 2).toNat (s₀.loc 3).toNat * (s₀.loc 4).toNat

set_option maxHeartbeats 2000000 in
theorem mcarryLoop_spec (n : Nat) (s₀ : St) (h : MCarryInv P0 C s₀) :
    ⦃fun s => s = s₀⦄ exec p n mcarryLoop ⦃fun r s' => MCarryPost P0 C s₀ r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [MCarryInv, WinBase, MCarryPost] at h ⊢
    rw [exec, step_while (w := mcarryLoop) rfl]
    vcgen [step, evalE, evalC, setLoc, setLocs, ld64, st64, ih]
    all_goals clear ih
    all_goals (try simp only [MCarryInv, MCarryPost, WinBase] at *)
    all_goals (try subst_vars)
    all_goals (try and_intros)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, Cmp.eval, BinOp.eval, Mem.size64_set64,
      Nat.reduceEqDiff, reduceIte, decide_eq_true_eq, bne_iff_ne, ne_eq] at *)
    all_goals first
      | (with_reducible apply carry_step_goal <;> grind [pcap_eq])
      | grind (splits := 8) [arena_grind, lang_grind, Off.mono, off_split]

theorem mrowLoop_step_spec (n : Nat) (s₀ : St) (h : MRowInv P0 C s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) mrowLoop ⦃fun r s' => MRowPost P0 C s₀ r s'; ⊤⦄ :=
  Triple.step_exec (mrowLoop_spec p P0 C (n + 1) s₀ h)

theorem mcarryLoop_step_spec (n : Nat) (s₀ : St) (h : MCarryInv P0 C s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) mcarryLoop ⦃fun r s' => MCarryPost P0 C s₀ r s'; ⊤⦄ :=
  Triple.step_exec (mcarryLoop_spec p P0 C (n + 1) s₀ h)

/-- `sub_row`'s loop: locals `(o, n, oa, la, i, c, x, t, d, ot, ob, qt, qb)`. -/
def SRowInv (P0 : Array Word) (C : Nat) (s : St) : Prop :=
  WinBase P0 C 9 10 11 12 s ∧ (s.loc 4).toNat ≤ (s.loc 3).toNat ∧ (s.loc 5).toNat ≤ 1 ∧
  Off (vpool s.mem) P0 (s.loc 0).toNat (s.loc 4).toNat ∧
  pv (vpool s.mem) (s.loc 0).toNat (s.loc 4).toNat + pv P0 (s.loc 2).toNat (s.loc 4).toNat =
    pv P0 (s.loc 0).toNat (s.loc 4).toNat + (s.loc 5).toNat * wt (s.loc 4).toNat

def SRowPost (P0 : Array Word) (C : Nat) (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ PFrame s₀.mem s'.mem ∧ pcap s'.mem = C ∧
  s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧
  s'.loc 4 = s₀.loc 3 ∧ (s'.loc 5).toNat ≤ 1 ∧
  s'.loc 9 = s₀.loc 9 ∧ s'.loc 10 = s₀.loc 10 ∧ s'.loc 11 = s₀.loc 11 ∧ s'.loc 12 = s₀.loc 12 ∧
  Off (vpool s'.mem) P0 (s₀.loc 0).toNat (s₀.loc 3).toNat ∧
  pv (vpool s'.mem) (s₀.loc 0).toNat (s₀.loc 3).toNat + pv P0 (s₀.loc 2).toNat (s₀.loc 3).toNat =
    pv P0 (s₀.loc 0).toNat (s₀.loc 3).toNat + (s'.loc 5).toNat * wt (s₀.loc 3).toNat

set_option maxHeartbeats 2000000 in
theorem srowLoop_spec (n : Nat) (s₀ : St) (h : SRowInv P0 C s₀) :
    ⦃fun s => s = s₀⦄ exec p n srowLoop ⦃fun r s' => SRowPost P0 C s₀ r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [SRowInv, WinBase, SRowPost] at h ⊢
    rw [exec, step_while (w := srowLoop) rfl]
    vcgen [step, evalE, evalC, setLoc, setLocs, ld64, st64, ih]
    all_goals clear ih
    all_goals (try simp only [SRowInv, SRowPost, WinBase] at *)
    all_goals (try subst_vars)
    all_goals (try and_intros)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, Cmp.eval, BinOp.eval, Mem.size64_set64,
      Nat.reduceEqDiff, reduceIte, decide_eq_true_eq] at *)
    all_goals first
      | (with_reducible apply srow_step_goal <;> grind [pcap_eq])
      | grind (splits := 8) [arena_grind, lang_grind, sbb_inl_le]

/-- `sub_row`'s borrow ripple. -/
def SBorrowInv (P0 : Array Word) (C : Nat) (s : St) : Prop :=
  WinBase P0 C 9 10 11 12 s ∧ (s.loc 4).toNat ≤ (s.loc 1).toNat ∧ (s.loc 5).toNat ≤ 1 ∧
  Off (vpool s.mem) P0 (s.loc 0).toNat (s.loc 4).toNat ∧
  pv (vpool s.mem) (s.loc 0).toNat (s.loc 4).toNat + pv P0 (s.loc 2).toNat (s.loc 3).toNat =
    pv P0 (s.loc 0).toNat (s.loc 4).toNat + (s.loc 5).toNat * wt (s.loc 4).toNat

def SBorrowPost (P0 : Array Word) (C : Nat) (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ PFrame s₀.mem s'.mem ∧ pcap s'.mem = C ∧
  Off (vpool s'.mem) P0 (s₀.loc 0).toNat (s₀.loc 1).toNat ∧
  pv (vpool s'.mem) (s₀.loc 0).toNat (s₀.loc 1).toNat + pv P0 (s₀.loc 2).toNat (s₀.loc 3).toNat =
    pv P0 (s₀.loc 0).toNat (s₀.loc 1).toNat

set_option maxHeartbeats 2000000 in
theorem sborrowLoop_spec (n : Nat) (s₀ : St) (h : SBorrowInv P0 C s₀) :
    ⦃fun s => s = s₀⦄ exec p n sborrowLoop ⦃fun r s' => SBorrowPost P0 C s₀ r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [SBorrowInv, WinBase, SBorrowPost] at h ⊢
    rw [exec, step_while (w := sborrowLoop) rfl]
    vcgen [step, evalE, evalC, setLoc, setLocs, ld64, st64, ih]
    all_goals clear ih
    all_goals (try simp only [SBorrowInv, SBorrowPost, WinBase] at *)
    all_goals (try subst_vars)
    all_goals (try and_intros)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, Cmp.eval, BinOp.eval, Mem.size64_set64,
      Nat.reduceEqDiff, reduceIte, decide_eq_true_eq, bne_iff_ne, ne_eq] at *)
    all_goals first
      | (with_reducible apply borrow_step_goal <;> grind [pcap_eq])
      | grind (splits := 8) [arena_grind, lang_grind, Off.mono, off_split]

theorem srowLoop_step_spec (n : Nat) (s₀ : St) (h : SRowInv P0 C s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) srowLoop ⦃fun r s' => SRowPost P0 C s₀ r s'; ⊤⦄ :=
  Triple.step_exec (srowLoop_spec p P0 C (n + 1) s₀ h)

theorem sborrowLoop_step_spec (n : Nat) (s₀ : St) (h : SBorrowInv P0 C s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) sborrowLoop ⦃fun r s' => SBorrowPost P0 C s₀ r s'; ⊤⦄ :=
  Triple.step_exec (sborrowLoop_spec p P0 C (n + 1) s₀ h)

/-- `mul_zeros`'s loop: locals `(o, n, i, ot, ob)`. -/
def ZerosInv (P0 : Array Word) (C : Nat) (s : St) : Prop :=
  C < 2 ^ 64 ∧ P0.size = 2 ^ 41 ∧ pcap s.mem = C ∧ (s.loc 0).toNat + (s.loc 1).toNat ≤ C ∧
  s.loc 3 = s.loc 0 >>> 40 ∧ s.loc 4 = s.loc 0 &&& 1099511627775 ∧
  (s.mem.arr64 (tierA POOL (s.loc 3))).size ≤ 2 ^ 40 ∧ (s.loc 2).toNat ≤ (s.loc 1).toNat ∧
  Off (vpool s.mem) P0 (s.loc 0).toNat (s.loc 2).toNat ∧ pv (vpool s.mem) (s.loc 0).toNat (s.loc 2).toNat = 0

def ZerosPost (P0 : Array Word) (C : Nat) (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ PFrame s₀.mem s'.mem ∧ pcap s'.mem = C ∧
  Off (vpool s'.mem) P0 (s₀.loc 0).toNat (s₀.loc 1).toNat ∧
  pv (vpool s'.mem) (s₀.loc 0).toNat (s₀.loc 1).toNat = 0

/-- One step of `mul_zeros`'s loop. -/
theorem zeros_step_goal (m : Mem) (P0 : Array Word) (o i T3 T4 : Word)
    (h3 : T3 = o >>> 40) (h4 : T4 = o &&& 1099511627775)
    (ho : o.toNat + i.toNat < 2 ^ 41)
    (hs3 : (m.arr64 (tierA POOL T3)).size ≤ 2 ^ 40)
    (hb3 : (T4 + i).toNat < (m.arr64 (tierA POOL T3)).size)
    (ih : pv (vpool m) o.toNat i.toNat = 0) :
    pv (vpool (m.set64 (tierA POOL T3) (T4 + i) 0)) o.toNat (i + 1).toNat = 0 := by
  subst h3 h4
  have hi1 : (i + 1).toNat = i.toNat + 1 := w_add i 1 (by simp; omega)
  have hvs := vpool_size m
  rw [st_win m o i _ (by omega) (by omega) hs3 hb3, hi1,
    pv_set_succ (vpool m) o.toNat i.toNat (i.toNat + 1) (o.toNat + i.toNat) _ rfl rfl (by omega), ih]
  simp

theorem zeros_off_goal (m : Mem) (P0 : Array Word) (o i T3 T4 : Word)
    (h3 : T3 = o >>> 40) (h4 : T4 = o &&& 1099511627775)
    (ho : o.toNat + i.toNat < 2 ^ 41)
    (hs3 : (m.arr64 (tierA POOL T3)).size ≤ 2 ^ 40)
    (hb3 : (T4 + i).toNat < (m.arr64 (tierA POOL T3)).size)
    (hoff : Off (vpool m) P0 o.toNat i.toNat) :
    Off (vpool (m.set64 (tierA POOL T3) (T4 + i) 0)) P0 o.toNat (i + 1).toNat := by
  subst h3 h4
  have hi1 : (i + 1).toNat = i.toNat + 1 := w_add i 1 (by simp; omega)
  rw [st_win m o i _ (by omega) (by omega) hs3 hb3, hi1]
  exact Off.set _ _ _ _ _ _ _ hoff rfl rfl

set_option maxHeartbeats 2000000 in
theorem zerosLoop_spec (n : Nat) (s₀ : St) (h : ZerosInv P0 C s₀) :
    ⦃fun s => s = s₀⦄ exec p n zerosLoop ⦃fun r s' => ZerosPost P0 C s₀ r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [ZerosInv, ZerosPost] at h ⊢
    rw [exec, step_while (w := zerosLoop) rfl]
    vcgen [step, evalE, evalC, setLoc, setLocs, ld64, st64, ih]
    all_goals clear ih
    all_goals (try simp only [ZerosInv, ZerosPost] at *)
    all_goals (try subst_vars)
    all_goals (try and_intros)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, Cmp.eval, BinOp.eval, Mem.size64_set64,
      Nat.reduceEqDiff, reduceIte, decide_eq_true_eq] at *)
    all_goals first
      | (with_reducible apply zeros_step_goal <;> grind [pcap_eq])
      | (with_reducible apply zeros_off_goal <;> grind [pcap_eq])
      | grind (splits := 8) [arena_grind, lang_grind]

theorem zerosLoop_step_spec (n : Nat) (s₀ : St) (h : ZerosInv P0 C s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) zerosLoop ⦃fun r s' => ZerosPost P0 C s₀ r s'; ⊤⦄ :=
  Triple.step_exec (zerosLoop_spec p P0 C (n + 1) s₀ h)

end passes

section passFns
variable (p : Prog)

set_option maxHeartbeats 2000000 in
/-- `mul_row(o, w, oa, la, y)`: `P[o, o + w) += a * y` in place (`a` off the window); only the
window changes. -/
theorem mulRow_spec (hp : p.lookup "mul_row" = some mulRow) (n : Nat) (s₀ : St) (o w oa la y : Word)
    (hs : pcap s₀.mem < 2 ^ 64) (ho : o.toNat + w.toNat ≤ pcap s₀.mem)
    (ha : oa.toNat + la.toNat ≤ pcap s₀.mem)
    (hd : oa.toNat + la.toNat ≤ o.toNat ∨ o.toNat + w.toNat ≤ oa.toNat) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "mul_row" [o, w, oa, la, y]
    ⦃fun _ s' => LocEq s' s₀ ∧ PFrame s₀.mem s'.mem ∧
      Off (vpool s'.mem) (vpool s₀.mem) o.toNat w.toNat ∧
      pv (vpool s'.mem) o.toNat w.toNat =
        pv (vpool s₀.mem) o.toNat w.toNat + pv (vpool s₀.mem) oa.toNat la.toNat * y.toNat; ⊤⦄ := by
  have h1 := pcap_tier s₀.mem (o >>> 40) hs
  have h2 := pcap_tier s₀.mem (oa >>> 40) hs
  rw [invoke_eq _ hp]
  simp only [callFn, mulRow]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      mrowLoop_step_spec p (vpool s₀.mem) (pcap s₀.mem) n,
      mcarryLoop_step_spec p (vpool s₀.mem) (pcap s₀.mem) n]
    all_goals (try simp only [MRowInv, MRowPost, MCarryInv, MCarryPost, WinBase] at *)
    all_goals (try subst_vars)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
      L.Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, BinOp.eval, Cmp.eval,
      reduceIte, Nat.reduceEqDiff, UInt64.toNat_zero] at *)
    all_goals (try and_intros)
    all_goals grind (splits := 8) [arena_grind, lang_grind, LocEq]

set_option maxHeartbeats 2000000 in
/-- `sub_row(o, w, oa, la)`: `P[o, o + w) -= a` in place (`a` off the window). -/
theorem subRow_spec (hp : p.lookup "sub_row" = some subRow) (n : Nat) (s₀ : St) (o w oa la : Word)
    (hs : pcap s₀.mem < 2 ^ 64) (ho : o.toNat + w.toNat ≤ pcap s₀.mem)
    (ha : oa.toNat + la.toNat ≤ pcap s₀.mem)
    (hd : oa.toNat + la.toNat ≤ o.toNat ∨ o.toNat + w.toNat ≤ oa.toNat) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "sub_row" [o, w, oa, la]
    ⦃fun _ s' => LocEq s' s₀ ∧ PFrame s₀.mem s'.mem ∧
      Off (vpool s'.mem) (vpool s₀.mem) o.toNat w.toNat ∧
      pv (vpool s'.mem) o.toNat w.toNat + pv (vpool s₀.mem) oa.toNat la.toNat =
        pv (vpool s₀.mem) o.toNat w.toNat; ⊤⦄ := by
  have h1 := pcap_tier s₀.mem (o >>> 40) hs
  have h2 := pcap_tier s₀.mem (oa >>> 40) hs
  rw [invoke_eq _ hp]
  simp only [callFn, subRow]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      srowLoop_step_spec p (vpool s₀.mem) (pcap s₀.mem) n,
      sborrowLoop_step_spec p (vpool s₀.mem) (pcap s₀.mem) n]
    all_goals (try simp only [SRowInv, SRowPost, SBorrowInv, SBorrowPost, WinBase] at *)
    all_goals (try subst_vars)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
      L.Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, BinOp.eval, Cmp.eval,
      reduceIte, Nat.reduceEqDiff, UInt64.toNat_zero] at *)
    all_goals (try and_intros)
    all_goals grind (splits := 8) [arena_grind, lang_grind, LocEq]

set_option maxHeartbeats 2000000 in
/-- `mul_zeros(o, w)`: `P[o, o + w) := 0`. -/
theorem mulZeros_spec (hp : p.lookup "mul_zeros" = some mulZeros) (n : Nat) (s₀ : St) (o w : Word)
    (hs : pcap s₀.mem < 2 ^ 64) (ho : o.toNat + w.toNat ≤ pcap s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "mul_zeros" [o, w]
    ⦃fun _ s' => LocEq s' s₀ ∧ PFrame s₀.mem s'.mem ∧
      Off (vpool s'.mem) (vpool s₀.mem) o.toNat w.toNat ∧ pv (vpool s'.mem) o.toNat w.toNat = 0; ⊤⦄ := by
  have h1 := pcap_tier s₀.mem (o >>> 40) hs
  rw [invoke_eq _ hp]
  simp only [callFn, mulZeros]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      zerosLoop_step_spec p (vpool s₀.mem) (pcap s₀.mem) n]
    all_goals (try simp only [ZerosInv, ZerosPost] at *)
    all_goals (try subst_vars)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
      L.Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, BinOp.eval, Cmp.eval,
      reduceIte, Nat.reduceEqDiff, UInt64.toNat_zero] at *)
    all_goals (try and_intros)
    all_goals grind (splits := 8) [arena_grind, lang_grind, LocEq]

end passFns

section mulFn
variable (p : Prog) (hph : p.lookup "mac_hi" = some macHi)
  (hpt : p.lookup "nat_trim" = some natTrim) (hpn : p.lookup "nat_mul" = some natMul)

set_option maxHeartbeats 2000000 in
include hph hpt hpn in
/-- `nat_mul` appends `a * b`, normalised, at the old top and moves the top past it; nothing
below the old top changes, and no other array but `CTL[0]`. -/
theorem natMul_spec (n : Nat) (s₀ : St) (oa la ob lb : Word) (hok : PoolOK s₀.mem)
    (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_mul" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧ PFrame (s₀.mem.set64 CTL 0 (s₀.mem.top + r.headD 0)) s'.mem ∧
      pcap s'.mem = pcap s₀.mem ∧
      s₀.mem.top.toNat + (r.headD 0).toNat ≤ pcap s'.mem ∧
      Agree (vpool s'.mem) (vpool s₀.mem) s₀.mem.top.toNat ∧
      pv (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat =
        pv (vpool s₀.mem) oa.toNat la.toNat * pv (vpool s₀.mem) ob.toNat lb.toNat ∧
      Norm (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat ∧ Grows s₀.mem s'.mem; ⊤⦄ := by
  sorry

end mulFn

end L.Arena
