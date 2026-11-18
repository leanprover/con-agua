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
import ConAgua.Arena.NatGrindAttr
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

/-- `kara_sum(o, oa, k, la)`: `P[o, o + k + 1) := a0 + a1` for `a0 = P[oa, oa + k)` and
`a1 = P[oa + k, oa + la)` (`la - k ≤ k`), the sums of a Karatsuba step. -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def karaSum : FunDecl := lfn (o, oa, k, la) locals (u) {
  u := call mul_zeros(o, k + 1);
  u := call mul_row(o, k + 1, oa, k, 1);
  u := call mul_row(o, k + 1, oa + k, la - k, 1);
  return 0
}

/-- `kara_prods(oa, la, ob, lb, s)`: the outer products of a Karatsuba step on
`a = a0 + a1 B^k`, `b = b0 + b1 B^k` (`k = ceil(la / 2)`): `z0 = a0 b0` at `[s, s + 2k)` and
`z2 = a1 b1` at `[s + 2k, s + la + lb)`, each into zeroed scratch; their own scratch from
`s2`. -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def karaProds : FunDecl := lfn (oa, la, ob, lb, s, k, s2) locals (u) {
  u := call mul_zeros(s, 2 * k);
  u := call mul_win(oa, k, ob, k, s, 2 * k, s2);
  u := call mul_zeros(s + 2 * k, la + lb - 2 * k);
  u := call mul_win(oa + k, la - k, ob + k, lb - k, s + 2 * k, la + lb - 2 * k, s2);
  return 0
}

/-- `kara_mid(oa, la, ob, lb, s)`: the three products of a Karatsuba step on `a = a0 + a1 B^k`,
`b = b0 + b1 B^k` (`k = ceil(la / 2)`, `la / 2 < lb ≤ la`), into the scratch block from `s`:
`z0 = a0 b0` at `[s, s + 2k)`, `z2 = a1 b1` at `[s + 2k, s + la + lb)` (`kara_prods`), the
sums `a0 + a1` and `b0 + b1` (`k + 1` limbs each) above them, and
`z1 = (a0 + a1)(b0 + b1) - z0 - z2` at `sp = s + la + lb + 2k + 2`, of the length it returns
(trimmed). The scratch of its own products starts at `s2 = sp + 2k + 2`. -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def karaMid : FunDecl := lfn (oa, la, ob, lb, s) locals (k, sa, sb, sp, s2, u) {
  k := la - (la >> 1);
  sa := s + la + lb;
  sb := sa + k + 1;
  sp := sb + k + 1;
  s2 := sp + 2 * k + 2;
  if ⟪2 ^ 41⟫ <= s2 { abort };
  u := call kara_prods(oa, la, ob, lb, s, k, s2);
  u := call kara_sum(sa, oa, k, la);
  u := call kara_sum(sb, ob, k, lb);
  u := call mul_zeros(sp, 2 * k + 2);
  u := call mul_win(sa, k + 1, sb, k + 1, sp, 2 * k + 2, s2);
  u := call sub_row(sp, 2 * k + 2, s, 2 * k);
  u := call sub_row(sp, 2 * k + 2, s + 2 * k, la + lb - 2 * k);
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
  ("mul_zeros", mulZeros), ("kara_sum", karaSum), ("kara_prods", karaProds), ("kara_mid", karaMid), ("mul_win", mulWin), ("nat_mul", natMul)]

/-- `natMulProg` at another threshold (tests). -/
def natMulProgT (T : Word) : Prog := natProg ++ [("mac_hi", macHi), ("mul_row", mulRow),
  ("sub_row", subRow), ("mul_zeros", mulZeros), ("kara_sum", karaSum), ("kara_prods", karaProds), ("kara_mid", karaMid), ("mul_win", mulWinG T),
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

/-- A window pass at an offset inside a larger window, lifted to that window. -/
theorem off_lift (p q : Array Word) (o k w X : Nat) (hk : k ≤ w)
    (hoff : Off p q (o + k) (w - k)) (h : pv p (o + k) (w - k) = pv q (o + k) (w - k) + X) :
    Off p q o w ∧ pv p o w = pv q o w + wt k * X := by
  refine ⟨fun j hj => hoff j (by omega), ?_⟩
  have e1 := pv_append p o k (w - k); have e2 := pv_append q o k (w - k)
  rw [show k + (w - k) = w by omega] at e1 e2
  rw [e1, e2, h, Off.pv_disj p q (o + k) (w - k) o k hoff (Or.inl (Nat.le_refl _))]
  grind

set_option maxHeartbeats 2000000 in
/-- `mul_row` on the window `[o + k, o + w)` of the window `[o, o + w)`: `P[o, o + w) += a y B^k`. -/
theorem mulRow_at_spec (hp : p.lookup "mul_row" = some mulRow) (n : Nat) (s₀ : St) (o k w oa la y : Word)
    (hs : pcap s₀.mem < 2 ^ 64) (hk : k.toNat ≤ w.toNat) (ho : o.toNat + w.toNat ≤ pcap s₀.mem)
    (ha : oa.toNat + la.toNat ≤ pcap s₀.mem)
    (hd : oa.toNat + la.toNat ≤ o.toNat + k.toNat ∨ o.toNat + w.toNat ≤ oa.toNat) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "mul_row" [BinOp.add.eval o k, BinOp.sub.eval w k, oa, la, y]
    ⦃fun _ s' => LocEq s' s₀ ∧ PFrame s₀.mem s'.mem ∧
      Off (vpool s'.mem) (vpool s₀.mem) o.toNat w.toNat ∧
      pv (vpool s'.mem) o.toNat w.toNat =
        pv (vpool s₀.mem) o.toNat w.toNat + wt k.toNat * (pv (vpool s₀.mem) oa.toNat la.toNat * y.toNat); ⊤⦄ := by
  have hC := pcap_eq s₀.mem hs
  have e1 : (o + k).toNat = o.toNat + k.toNat := w_add o k (by omega)
  have e2 : (w - k).toNat = w.toNat - k.toNat := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hk)
  have hw := mulRow_spec p hp n s₀ (o + k) (w - k) oa la y hs (by omega) ha (by omega)
  rw [e1, e2] at hw
  simp only [BinOp.eval]
  vcgen [hw]
  all_goals
    rename_i h
    obtain ⟨h1, h2, h3, h4⟩ := h
    have := off_lift _ (vpool s₀.mem) o.toNat k.toNat w.toNat _ hk h3 h4
    first | exact h1 | exact h2 | exact this.1 | exact this.2

set_option maxHeartbeats 2000000 in
/-- `kara_sum(o, oa, k, la)`: `P[o, o + k + 1) := a0 + a1`. -/
theorem karaSum_spec (hpz : p.lookup "mul_zeros" = some mulZeros) (hpr : p.lookup "mul_row" = some mulRow)
    (hp : p.lookup "kara_sum" = some karaSum) (n : Nat) (s₀ : St) (o oa k la : Word)
    (hs : pcap s₀.mem < 2 ^ 64) (ho : o.toNat + k.toNat + 1 ≤ pcap s₀.mem)
    (ha : oa.toNat + la.toNat ≤ o.toNat) (hk : k.toNat ≤ la.toNat) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "kara_sum" [o, oa, k, la]
    ⦃fun _ s' => LocEq s' s₀ ∧ PFrame s₀.mem s'.mem ∧
      Off (vpool s'.mem) (vpool s₀.mem) o.toNat (k.toNat + 1) ∧
      pv (vpool s'.mem) o.toNat (k.toNat + 1) =
        pv (vpool s₀.mem) oa.toNat k.toNat + pv (vpool s₀.mem) (oa.toNat + k.toNat) (la.toNat - k.toNat); ⊤⦄ := by
  have hC := pcap_eq s₀.mem hs
  have e1 : (k + 1).toNat = k.toNat + 1 := w_add k 1 (by simp; omega)
  have e2 : (oa + k).toNat = oa.toNat + k.toNat := w_add oa k (by omega)
  have e3 : (la - k).toNat = la.toNat - k.toNat := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hk)
  rw [invoke_eq _ hp]
  simp only [callFn, karaSum]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc, setLocs, mulZeros_spec p hpz n, mulRow_spec p hpr n] <;>
      finish

end passFns

section win
variable (p : Prog) (P0 : Array Word) (C : Nat)

/-- The window product's operands and window: `a`, `b` and the window below the scratch `s`,
both operands off the window. Locals `(oa, la, ob, lb, o, n, s)` at `0`-`6`. -/
def WinArgs (C : Nat) (s : St) : Prop :=
  C < 2 ^ 64 ∧ pcap s.mem = C ∧ (s.loc 6).toNat ≤ C ∧
  (s.loc 0).toNat + (s.loc 1).toNat ≤ (s.loc 6).toNat ∧
  (s.loc 2).toNat + (s.loc 3).toNat ≤ (s.loc 6).toNat ∧
  (s.loc 4).toNat + (s.loc 5).toNat ≤ (s.loc 6).toNat ∧
  ((s.loc 0).toNat + (s.loc 1).toNat ≤ (s.loc 4).toNat ∨
    (s.loc 4).toNat + (s.loc 5).toNat ≤ (s.loc 0).toNat) ∧
  ((s.loc 2).toNat + (s.loc 3).toNat ≤ (s.loc 4).toNat ∨
    (s.loc 4).toNat + (s.loc 5).toNat ≤ (s.loc 2).toNat)

/-- The schoolbook rows of `mul_win`: rows `[0, j)` are in. -/
def RowsInv (P0 : Array Word) (C : Nat) (s : St) : Prop :=
  WinArgs C s ∧ P0.size = 2 ^ 41 ∧ (s.loc 1).toNat + (s.loc 3).toNat ≤ (s.loc 5).toNat ∧
  (s.loc 10).toNat ≤ (s.loc 3).toNat ∧
  Off (vpool s.mem) P0 (s.loc 4).toNat (s.loc 5).toNat ∧
  pv (vpool s.mem) (s.loc 4).toNat (s.loc 5).toNat =
    pv P0 (s.loc 4).toNat (s.loc 5).toNat +
      pv P0 (s.loc 0).toNat (s.loc 1).toNat * pv P0 (s.loc 2).toNat (s.loc 10).toNat

def RowsPost (P0 : Array Word) (C : Nat) (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ PFrame s₀.mem s'.mem ∧ pcap s'.mem = C ∧
  s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧
  s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧ s'.loc 6 = s₀.loc 6 ∧
  Off (vpool s'.mem) P0 (s₀.loc 4).toNat (s₀.loc 5).toNat ∧
  pv (vpool s'.mem) (s₀.loc 4).toNat (s₀.loc 5).toNat =
    pv P0 (s₀.loc 4).toNat (s₀.loc 5).toNat +
      pv P0 (s₀.loc 0).toNat (s₀.loc 1).toNat * pv P0 (s₀.loc 2).toNat (s₀.loc 3).toNat

set_option maxHeartbeats 2000000 in
theorem rowsLoop_spec (hpr : p.lookup "mul_row" = some mulRow) (n : Nat) (s₀ : St)
    (h : RowsInv P0 C s₀) :
    ⦃fun s => s = s₀⦄ exec p n rowsLoop ⦃fun r s' => RowsPost P0 C s₀ r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [RowsInv, WinArgs, RowsPost] at h ⊢
    rw [exec, step_while (w := rowsLoop) rfl]
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih, mulRow_at_spec p hpr n]
    all_goals clear ih
    all_goals (try simp only [RowsInv, RowsPost, WinArgs] at *)
    all_goals (try subst_vars)
    all_goals (try and_intros)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Cmp.eval,
      BinOp.eval, Mem.size64_set64, Nat.reduceEqDiff, reduceIte, decide_eq_true_eq] at *)
    all_goals grind (splits := 8) [arena_grind, lang_grind, Off.trans, Off.pv_disj, pcap_eq]

theorem rowsLoop_step_spec (hpr : p.lookup "mul_row" = some mulRow) (n : Nat) (s₀ : St)
    (h : RowsInv P0 C s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) rowsLoop ⦃fun r s' => RowsPost P0 C s₀ r s'; ⊤⦄ :=
  Triple.step_exec (rowsLoop_spec p P0 C hpr (n + 1) s₀ h)

end win

/-! ## The recursion: `mul_win`, `kara_prods`, `kara_mid` -/

/-- `k = ceil(la / 2)`, Karatsuba's split. -/
def kh (la : Word) : Nat := la.toNat - la.toNat / 2

/-- The positions of a Karatsuba step, as numbers (no word wraps below `2^41`). -/
theorem kara_pos (s la lb oa ob : Word) (hs : s.toNat < 2 ^ 41) (hla : la.toNat < 2 ^ 41)
    (hlb : lb.toNat < 2 ^ 41) (hoa : oa.toNat < 2 ^ 41) (hob : ob.toNat < 2 ^ 41)
    (h1 : la.toNat / 2 < lb.toNat) (h2 : lb.toNat ≤ la.toNat) :
    (la - la >>> 1).toNat = kh la ∧ ((2 : Word) * (la - la >>> 1)).toNat = 2 * kh la ∧
    (s + (2 : Word) * (la - la >>> 1)).toNat = s.toNat + 2 * kh la ∧
    (la + lb - (2 : Word) * (la - la >>> 1)).toNat = la.toNat + lb.toNat - 2 * kh la ∧
    (s + la + lb).toNat = s.toNat + la.toNat + lb.toNat ∧
    (s + la + lb + (la - la >>> 1) + (1 : Word)).toNat = s.toNat + la.toNat + lb.toNat + kh la + 1 ∧
    (s + la + lb + (la - la >>> 1) + (1 : Word) + (la - la >>> 1) + (1 : Word)).toNat =
      s.toNat + la.toNat + lb.toNat + 2 * kh la + 2 ∧
    (s + la + lb + (la - la >>> 1) + (1 : Word) + (la - la >>> 1) + (1 : Word) + (2 : Word) * (la - la >>> 1) + (2 : Word)).toNat =
      s.toNat + la.toNat + lb.toNat + 4 * kh la + 4 ∧
    (s + la + lb + (2 : Word) * (la - la >>> 1) + (2 : Word)).toNat = s.toNat + la.toNat + lb.toNat + 2 * kh la + 2 ∧
    ((la - la >>> 1) + (1 : Word)).toNat = kh la + 1 ∧ ((2 : Word) * (la - la >>> 1) + (2 : Word)).toNat = 2 * kh la + 2 ∧
    (oa + (la - la >>> 1)).toNat = oa.toNat + kh la ∧ (la - (la - la >>> 1)).toNat = la.toNat - kh la ∧
    (ob + (la - la >>> 1)).toNat = ob.toNat + kh la ∧ (lb - (la - la >>> 1)).toNat = lb.toNat - kh la ∧
    kh la ≤ la.toNat ∧ kh la ≤ lb.toNat ∧ la.toNat - kh la ≤ kh la := by
  have e0 : (la >>> 1).toNat = la.toNat / 2 := by
    rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; rfl
  have ek : (la - la >>> 1).toNat = kh la := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [e0]; omega)), e0]; rfl
  have hk : kh la = la.toNat - la.toNat / 2 := rfl
  have hkl : kh la ≤ lb.toNat := by omega
  have hka : kh la ≤ la.toNat := by omega
  generalize la - la >>> 1 = k at ek ⊢
  generalize kh la = K at *
  have e2 : ((2 : Word) * k).toNat = 2 * K := by
    rw [UInt64.toNat_mul, ek]; simp only [UInt64.toNat_ofNat]; omega
  have a1 : (s + la).toNat = s.toNat + la.toNat := toNat_add_of_lt _ _ (by omega)
  have a2 : (s + la + lb).toNat = s.toNat + la.toNat + lb.toNat := by
    rw [toNat_add_of_lt _ _ (by omega), a1]
  have a3 : (s + la + lb + k).toNat = s.toNat + la.toNat + lb.toNat + K := by
    rw [toNat_add_of_lt _ _ (by omega), a2, ek]
  have a4 : (s + la + lb + k + (1 : Word)).toNat = s.toNat + la.toNat + lb.toNat + K + 1 := by
    rw [toNat_add_of_lt _ _ (by simp; omega), a3]; simp
  have a5 : (s + la + lb + k + (1 : Word) + k).toNat = s.toNat + la.toNat + lb.toNat + 2 * K + 1 := by
    rw [toNat_add_of_lt _ _ (by omega), a4, ek]; omega
  have a6 : (s + la + lb + k + (1 : Word) + k + (1 : Word)).toNat =
      s.toNat + la.toNat + lb.toNat + 2 * K + 2 := by
    rw [toNat_add_of_lt _ _ (by simp; omega), a5]; simp <;> omega
  have a7 : (s + la + lb + k + (1 : Word) + k + (1 : Word) + (2 : Word) * k).toNat =
      s.toNat + la.toNat + lb.toNat + 4 * K + 2 := by
    rw [toNat_add_of_lt _ _ (by omega), a6, e2]; omega
  have a8 : (s + la + lb + (2 : Word) * k).toNat = s.toNat + la.toNat + lb.toNat + 2 * K := by
    rw [toNat_add_of_lt _ _ (by omega), a2, e2]
  have b1 : (la + lb).toNat = la.toNat + lb.toNat := toNat_add_of_lt _ _ (by omega)
  refine ⟨ek, e2, ?_, ?_, a2, a4, a6, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hka, hkl, by omega⟩
  · rw [toNat_add_of_lt _ _ (by omega), e2]
  · rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), b1, e2]
  · rw [toNat_add_of_lt _ _ (by rw [a7]; simp; omega), a7]; simp <;> omega
  · rw [toNat_add_of_lt _ _ (by rw [a8]; simp; omega), a8]; simp <;> omega
  · rw [toNat_add_of_lt _ _ (by simp; omega), ek]; simp
  · rw [toNat_add_of_lt _ _ (by simp; omega), e2]; simp
  · rw [toNat_add_of_lt _ _ (by omega), ek]
  · rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), ek]
  · rw [toNat_add_of_lt _ _ (by omega), ek]
  · rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), ek]

open Lean Elab Tactic Meta in
/-- Split the conjunctions among the hypotheses, then clear every `s.loc = t` among them (the
unfolded `LocEq`s, once `simp_all` has used them to name the callers' locals): `grind` would case
on the `Locals.init` lists in them. -/
elab "split_clear_locs" : tactic => do
  liftMetaTactic fun g => do
    let mut g ← g.casesAnd
    for d in (← g.getDecl).lctx do
      if d.isImplementationDetail then continue
      let t ← instantiateMVars d.type
      if t.isAppOfArity ``Eq 3 && (t.getArg! 0).isConstOf ``L.Locals then
        try g ← g.clear d.fvarId catch _ => pure ()
    return [g]

section rec
variable (p : Prog) (hpz : p.lookup "mul_zeros" = some mulZeros) (hpr : p.lookup "mul_row" = some mulRow)
  (hps : p.lookup "sub_row" = some subRow) (hpt : p.lookup "nat_trim" = some natTrim)
  (hpu : p.lookup "kara_sum" = some karaSum) (hpp : p.lookup "kara_prods" = some karaProds)
  (hpm : p.lookup "kara_mid" = some karaMid) (hpw : p.lookup "mul_win" = some mulWin)

/-- The spec of `mul_win` at fuel `n`. -/
def MulWinSpec (n : Nat) : Prop := ∀ (s₀ : St) (oa la ob lb o w sc : Word),
    pcap s₀.mem < 2 ^ 64 → sc.toNat ≤ pcap s₀.mem →
    oa.toNat + la.toNat ≤ sc.toNat → ob.toNat + lb.toNat ≤ sc.toNat → o.toNat + w.toNat ≤ sc.toNat →
    (oa.toNat + la.toNat ≤ o.toNat ∨ o.toNat + w.toNat ≤ oa.toNat) →
    (ob.toNat + lb.toNat ≤ o.toNat ∨ o.toNat + w.toNat ≤ ob.toNat) →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "mul_win" [oa, la, ob, lb, o, w, sc]
    ⦃fun _ s' => LocEq s' s₀ ∧ PFrame s₀.mem s'.mem ∧
      OffB (vpool s'.mem) (vpool s₀.mem) o.toNat w.toNat sc.toNat ∧
      pv (vpool s'.mem) o.toNat w.toNat =
        pv (vpool s₀.mem) o.toNat w.toNat +
          pv (vpool s₀.mem) oa.toNat la.toNat * pv (vpool s₀.mem) ob.toNat lb.toNat; ⊤⦄

/-- The spec of `kara_prods` at fuel `n`. -/
def KaraProdsSpec (n : Nat) : Prop := ∀ (s₀ : St) (oa la ob lb sc k s2 : Word),
    pcap s₀.mem < 2 ^ 64 → s2.toNat ≤ pcap s₀.mem →
    oa.toNat + la.toNat ≤ sc.toNat → ob.toNat + lb.toNat ≤ sc.toNat →
    sc.toNat + la.toNat + lb.toNat ≤ s2.toNat → k.toNat ≤ la.toNat → k.toNat ≤ lb.toNat →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "kara_prods" [oa, la, ob, lb, sc, k, s2]
    ⦃fun _ s' => LocEq s' s₀ ∧ PFrame s₀.mem s'.mem ∧
      OffB (vpool s'.mem) (vpool s₀.mem) sc.toNat (la.toNat + lb.toNat) s2.toNat ∧
      pv (vpool s'.mem) sc.toNat (2 * k.toNat) =
        pv (vpool s₀.mem) oa.toNat k.toNat * pv (vpool s₀.mem) ob.toNat k.toNat ∧
      pv (vpool s'.mem) (sc.toNat + 2 * k.toNat) (la.toNat + lb.toNat - 2 * k.toNat) =
        pv (vpool s₀.mem) (oa.toNat + k.toNat) (la.toNat - k.toNat) *
          pv (vpool s₀.mem) (ob.toNat + k.toNat) (lb.toNat - k.toNat); ⊤⦄

/-- `kara_prods`'s frame: two zeroings and two products, inside `[s, s + w)` below `s2`. -/
theorem kp_frame (p0 p1 p2 p3 p4 : Array Word) (s k n2 w s2 : Nat) (h1 : Off p1 p0 s (2 * k))
    (h2 : OffB p2 p1 s (2 * k) s2) (h3 : Off p3 p2 (s + 2 * k) n2) (h4 : OffB p4 p3 (s + 2 * k) n2 s2)
    (hw : 2 * k + n2 ≤ w) : OffB p4 p0 s w s2 := fun j hj hw' =>
  (h4 j hj (by omega)).trans ((h3 j (by omega)).trans ((h2 j hj (by omega)).trans (h1 j (by omega))))

set_option maxHeartbeats 4000000 in
include hpz hpp in
theorem karaProds_step (n : Nat) (ih : MulWinSpec p n) : KaraProdsSpec p (n + 1) := by
  intro s₀ oa la ob lb sc k s2 hs h2 ha hb hsc hka hkb
  unfold MulWinSpec at ih
  have hC := pcap_eq s₀.mem hs
  have e1 : ((2 : Word) * k).toNat = 2 * k.toNat := by
    rw [UInt64.toNat_mul]; simp only [UInt64.toNat_ofNat]; omega
  have e2 : (sc + (2 : Word) * k).toNat = sc.toNat + 2 * k.toNat := by
    rw [toNat_add_of_lt _ _ (by omega), e1]
  have e3 : (la + lb - (2 : Word) * k).toNat = la.toNat + lb.toNat - 2 * k.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
      rw [toNat_add_of_lt _ _ (by omega), e1]; omega)), toNat_add_of_lt _ _ (by omega), e1]
  have e4 : (oa + k).toNat = oa.toNat + k.toNat := toNat_add_of_lt _ _ (by omega)
  have e5 : (ob + k).toNat = ob.toNat + k.toNat := toNat_add_of_lt _ _ (by omega)
  have e6 : (la - k).toNat = la.toNat - k.toNat := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hka)
  have e7 : (lb - k).toNat = lb.toNat - k.toNat := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hkb)
  rw [invoke_eq _ hpp]
  simp only [callFn, karaProds]
  vcgen [exec, step, evalE, evalArgs, setLoc, setLocs, mulZeros_spec p hpz n, ih]
  all_goals clear ih
  all_goals (try simp only [LocEq] at *)
  all_goals (try simp_all only [St.setLoc_loc, L.St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
      L.Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, BinOp.eval, Cmp.eval,
      reduceIte, Nat.reduceEqDiff, List.headD_cons])
  all_goals split_clear_locs
  all_goals (try and_intros)
  all_goals first
    | (with_reducible apply kp_frame <;> first | (with_reducible assumption) | omega)
    | grind (splits := 4) [arena_grind, lang_grind, winop_grind]

/-- The spec of `kara_mid` at fuel `n` (`K = kh la`, `a = a0 + a1 B^K`, `b = b0 + b1 B^K`). -/
def KaraMidSpec (n : Nat) : Prop := ∀ (s₀ : St) (oa la ob lb sc : Word),
    pcap s₀.mem < 2 ^ 64 → sc.toNat ≤ pcap s₀.mem →
    oa.toNat + la.toNat ≤ sc.toNat → ob.toNat + lb.toNat ≤ sc.toNat →
    la.toNat / 2 < lb.toNat → lb.toNat ≤ la.toNat →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "kara_mid" [oa, la, ob, lb, sc]
    ⦃fun r s' => LocEq s' s₀ ∧ PFrame s₀.mem s'.mem ∧ Agree (vpool s'.mem) (vpool s₀.mem) sc.toNat ∧
      sc.toNat + la.toNat + lb.toNat + 4 * kh la + 4 < 2 ^ 41 ∧ (r.headD 0).toNat ≤ 2 * kh la + 2 ∧
      pv (vpool s'.mem) sc.toNat (2 * kh la) =
        pv (vpool s₀.mem) oa.toNat (kh la) * pv (vpool s₀.mem) ob.toNat (kh la) ∧
      pv (vpool s'.mem) (sc.toNat + 2 * kh la) (la.toNat + lb.toNat - 2 * kh la) =
        pv (vpool s₀.mem) (oa.toNat + kh la) (la.toNat - kh la) *
          pv (vpool s₀.mem) (ob.toNat + kh la) (lb.toNat - kh la) ∧
      pv (vpool s'.mem) (sc.toNat + la.toNat + lb.toNat + 2 * kh la + 2) (r.headD 0).toNat =
        pv (vpool s₀.mem) oa.toNat (kh la) * pv (vpool s₀.mem) (ob.toNat + kh la) (lb.toNat - kh la) +
          pv (vpool s₀.mem) (oa.toNat + kh la) (la.toNat - kh la) * pv (vpool s₀.mem) ob.toNat (kh la); ⊤⦄

/-- `kara_mid`'s frame: its seven writers all work above `s`. -/
theorem kmid_frame (p0 p1 p2 p3 p4 p5 p6 p7 : Array Word)
    (s o1 w1 t1 o2 w2 o3 w3 o4 w4 o5 w5 t5 o6 w6 o7 w7 : Nat)
    (h1 : OffB p1 p0 o1 w1 t1) (h2 : Off p2 p1 o2 w2) (h3 : Off p3 p2 o3 w3) (h4 : Off p4 p3 o4 w4)
    (h5 : OffB p5 p4 o5 w5 t5) (h6 : Off p6 p5 o6 w6) (h7 : Off p7 p6 o7 w7)
    (c1 : s ≤ o1) (c1' : s ≤ t1) (c2 : s ≤ o2) (c3 : s ≤ o3) (c4 : s ≤ o4) (c5 : s ≤ o5)
    (c5' : s ≤ t5) (c6 : s ≤ o6) (c7 : s ≤ o7) : Agree p7 p0 s := fun j hj =>
  (h7 j (by omega)).trans <| (h6 j (by omega)).trans <| (h5 j (by omega) (by omega)).trans <|
    (h4 j (by omega)).trans <| (h3 j (by omega)).trans <| (h2 j (by omega)).trans <|
      h1 j (by omega) (by omega)

set_option maxHeartbeats 4000000 in
include hpz hpr hps hpt hpu hpm in
theorem karaMid_step (n : Nat) (ihw : MulWinSpec p n) (ihp : KaraProdsSpec p n) :
    KaraMidSpec p (n + 1) := by
  intro s₀ oa la ob lb sc hs h2 ha hb h1 hl
  unfold MulWinSpec at ihw
  unfold KaraProdsSpec at ihp
  have hC := pcap_eq s₀.mem hs
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, -, e10, e11, e12, e13, e14, e15, hk1, hk2, hk3⟩ :=
    kara_pos sc la lb oa ob (by omega) (by omega) (by omega) (by omega) (by omega) h1 hl
  rw [invoke_eq _ hpm]
  simp only [callFn, karaMid]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, mulZeros_spec p hpz n,
    karaSum_spec p hpz hpr hpu n, subRow_spec p hps n, natTrim_spec p hpt n, ihw, ihp]
  all_goals clear ihw ihp
  all_goals (try simp only [LocEq] at *)
  all_goals (try simp_all only [St.setLoc_loc, L.St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
      L.Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, BinOp.eval, Cmp.eval,
      reduceIte, Nat.reduceEqDiff, List.headD_cons])
  all_goals split_clear_locs
  all_goals (try and_intros)
  all_goals first
    | (with_reducible apply kmid_frame <;> first | (with_reducible assumption) | omega)
    | omega
    | grind (splits := 4) [arena_grind, lang_grind, winop_grind]

/-- The halving step's frame: the two halves' windows lie in the whole window. -/
theorem halve_frame (p0 p1 p2 : Array Word) (o w s a b : Nat) (h1 : OffB p1 p0 o w s)
    (h2 : OffB p2 p1 a b s) (ha : o ≤ a) (hb : a + b ≤ o + w) : OffB p2 p0 o w s :=
  OffB.trans _ _ _ _ _ _ (OffB.widen _ _ _ _ _ _ _ h2 ha hb) h1

/-- An `OffB` pass at an offset inside a larger window, lifted to that window. -/
theorem offb_lift (p q : Array Word) (o k w s X : Nat) (hk : k ≤ w) (hs : o + w ≤ s)
    (hoff : OffB p q (o + k) (w - k) s) (h : pv p (o + k) (w - k) = pv q (o + k) (w - k) + X) :
    pv p o w = pv q o w + wt k * X := by
  have e1 := pv_append p o k (w - k); have e2 := pv_append q o k (w - k)
  rw [show k + (w - k) = w by omega] at e1 e2
  rw [e1, e2, h, OffB.pv_disj p q (o + k) (w - k) s o k hoff (by omega) (Or.inl (Nat.le_refl _))]
  grind

/-- The halving step's value: `a = a0 + a1 B^k`, both halves accumulated. -/
theorem halve_val (p0 p1 p2 : Array Word) (o w oa la ob lb s k o' w' oa' la' : Nat)
    (h1 : OffB p1 p0 o w s) (v1 : pv p1 o w = pv p0 o w + pv p0 oa k * pv p0 ob lb)
    (h2 : OffB p2 p1 o' w' s) (v2 : pv p2 o' w' = pv p1 o' w' + pv p1 oa' la' * pv p1 ob lb)
    (ho' : o' = o + k) (hw' : w' = w - k) (hoa' : oa' = oa + k) (hla' : la' = la - k)
    (hk : k ≤ w) (hkl : k ≤ la) (hs : o + w ≤ s) (ha : oa + la ≤ s) (hb : ob + lb ≤ s)
    (hda : oa + la ≤ o ∨ o + w ≤ oa) (hdb : ob + lb ≤ o ∨ o + w ≤ ob) :
    pv p2 o w = pv p0 o w + pv p0 oa la * pv p0 ob lb := by
  subst ho' hw' hoa' hla'
  have l2 := offb_lift p2 p1 o k w s _ hk hs h2 v2
  rw [OffB.pv_disj p1 p0 o w s (oa + k) (la - k) h1 (by omega) (by omega),
    OffB.pv_disj p1 p0 o w s ob lb h1 hb hdb] at l2
  have e := pv_append p0 oa k (la - k)
  rw [show k + (la - k) = la by omega] at e
  rw [l2, v1, e]
  grind

/-- The Karatsuba step's frame: three additions inside the window, `kara_mid` above it. -/
theorem kara_frame (p0 p1 p2 p3 p4 : Array Word) (o w s a3 b3 a4 b4 : Nat) (h1 : Agree p1 p0 s)
    (h2 : Off p2 p1 o w) (h3 : Off p3 p2 a3 b3) (h4 : Off p4 p3 a4 b4) (hs : o + w ≤ s)
    (c3 : o ≤ a3) (c3' : a3 + b3 ≤ o + w) (c4 : o ≤ a4) (c4' : a4 + b4 ≤ o + w) :
    OffB p4 p0 o w s := fun j hj hw =>
  (h4 j (by omega)).trans <| (h3 j (by omega)).trans <| (h2 j hw).trans <| h1 j hj

/-- The Karatsuba step's value: `z0 + z1 B^K + z2 B^2K = (a0 + a1 B^K)(b0 + b1 B^K)`. -/
theorem kara_val (p0 p1 p2 p3 p4 : Array Word) (o w oa la ob lb s K z0l o3 w3 sp l o4 w4 z2p n2 : Nat)
    (g0 : Agree p1 p0 s)
    (h2 : Off p2 p1 o w) (v2 : pv p2 o w = pv p1 o w + pv p1 s z0l * (1 : Word).toNat)
    (h3 : Off p3 p2 o3 w3) (v3 : pv p3 o3 w3 = pv p2 o3 w3 + pv p2 sp l * (1 : Word).toNat)
    (h4 : Off p4 p3 o4 w4) (v4 : pv p4 o4 w4 = pv p3 o4 w4 + pv p3 z2p n2 * (1 : Word).toNat)
    (m0 : pv p1 s (2 * K) = pv p0 oa K * pv p0 ob K)
    (m2 : pv p1 (s + 2 * K) (la + lb - 2 * K) =
      pv p0 (oa + K) (la - K) * pv p0 (ob + K) (lb - K))
    (m1 : pv p1 (s + la + lb + 2 * K + 2) l =
      pv p0 oa K * pv p0 (ob + K) (lb - K) + pv p0 (oa + K) (la - K) * pv p0 ob K)
    (ez : z0l = 2 * K) (e3 : o3 = o + K) (e3' : w3 = w - K) (esp : sp = s + la + lb + 2 * K + 2)
    (e4 : o4 = o + 2 * K) (e4' : w4 = w - 2 * K) (ez2 : z2p = s + 2 * K) (en2 : n2 = la + lb - 2 * K)
    (hs : o + w ≤ s) (hw : la + lb ≤ w) (hkl : K ≤ la) (hkb : K ≤ lb) :
    pv p4 o w = pv p0 o w + pv p0 oa la * pv p0 ob lb := by
  subst ez e3 e3' esp e4 e4' ez2 en2
  simp only [UInt64.toNat_one] at v2 v3 v4
  have l3 := off_lift p3 p2 o K w _ (by omega) h3 v3
  have l4 := off_lift p4 p3 o (2 * K) w _ (by omega) h4 v4
  rw [Off.pv_disj p2 p1 o w (s + la + lb + 2 * K + 2) l h2 (by omega)] at l3
  rw [Off.pv_disj p3 p2 (o + K) (w - K) (s + 2 * K) (la + lb - 2 * K) h3 (by omega),
    Off.pv_disj p2 p1 o w (s + 2 * K) (la + lb - 2 * K) h2 (by omega)] at l4
  rw [Agree.pv p1 p0 s o w g0 hs, m0] at v2
  rw [m1] at l3
  rw [m2] at l4
  have ea := pv_append p0 oa K (la - K)
  have eb := pv_append p0 ob K (lb - K)
  rw [show K + (la - K) = la by omega] at ea
  rw [show K + (lb - K) = lb by omega] at eb
  have ew : wt (2 * K) = wt K * wt K := wt_add K K (2 * K) (by omega)
  rw [l4.2, l3.2, v2, ea, eb, ew]
  grind

set_option maxHeartbeats 4000000 in
include hpr hpm hpw in
theorem mulWin_step (n : Nat) (ihw : MulWinSpec p n) (ihm : KaraMidSpec p n) :
    MulWinSpec p (n + 1) := by
  intro s₀ oa la ob lb o w sc hs h2 ha hb ho hda hdb
  unfold MulWinSpec at ihw
  unfold KaraMidSpec at ihm
  have hC := pcap_eq s₀.mem hs
  have e0 : (la >>> 1).toNat = la.toNat / 2 := by
    rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; rfl
  rw [invoke_eq _ hpw]
  simp only [callFn, mulWin, mulWinG]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, mulRow_spec p hpr n, mulRow_at_spec p hpr n,
    rowsLoop_step_spec p (vpool s₀.mem) (pcap s₀.mem) hpr n, ihw, ihm]
  all_goals clear ihw ihm
  all_goals (try simp only [LocEq, RowsInv, RowsPost, WinArgs] at *)
  all_goals (try simp_all only [St.setLoc_loc, L.St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
      L.Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, BinOp.eval, Cmp.eval,
      reduceIte, Nat.reduceEqDiff, List.headD_cons])
  all_goals split_clear_locs
  all_goals (try and_intros)
  all_goals (try have hkp := kara_pos sc la lb oa ob (by omega) (by omega) (by omega) (by omega) (by omega) (by grind) (by grind))
  all_goals first
    | omega
    | (with_reducible apply OffB.of_off; assumption)
    | (with_reducible apply halve_frame <;> first | (with_reducible assumption) | grind)
    | (with_reducible apply halve_val <;> first | (with_reducible assumption) | grind)
    | (with_reducible apply kara_frame <;> first | (with_reducible assumption) | grind)
    | (with_reducible apply kara_val <;> first | (with_reducible assumption) | grind)
    | grind (splits := 4) [arena_grind, lang_grind, winop_grind]

end rec

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
