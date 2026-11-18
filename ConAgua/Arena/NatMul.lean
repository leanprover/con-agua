module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.NatAdd
public import ConAgua.Arena.NatAdd
public import ConAgua.Arena.Word
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
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

/-- The schoolbook rows: one `mul_row` per limb of the shorter operand `b`. -/
def rowsLoop : Stmt := lblk (oa, la, ob, lb, o, n, s, k, z2, n2, sa, sb, sp, s2, l, u, j, y) {
  for j < lb {
    y := POOL⦃ob + j⦄;
    u := call mul_row(o + j, n - j, oa, la, y)
  }
}

/-- `mul_win(oa, la, ob, lb, o, n, s)`: `P[o, o + n) += a * b` in place, for the windows
`a = P[oa, oa + la)` and `b = P[ob, ob + lb)` (con-ron's `mul_win`), with scratch space from `s`
up. Below `T` limbs in the shorter window: schoolbook rows; an operand at least twice as long
as the other is halved, both halves accumulating into the window; otherwise Karatsuba at
`k = ceil(la / 2)`: `z0 = a0 b0` and `z2 = a1 b1` into zeroed scratch, the sums `a0 + a1`,
`b0 + b1` and their product `s` too, `z1 = s - z0 - z2` in place in `s`, then
`P[o, o + n) += z0 + z1 B^k + z2 B^2k`. -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def mulWinG (T : Word) : FunDecl :=
  lfn (oa, la, ob, lb, o, n, s) locals (k, z2, n2, sa, sb, sp, s2, l, u, j, y) {
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
  z2 := s + 2 * k;
  n2 := la + lb - 2 * k;
  sa := z2 + n2;
  sb := sa + k + 1;
  sp := sb + k + 1;
  s2 := sp + 2 * k + 2;
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
  l := call nat_trim(sp, 2 * k + 2);
  u := call mul_row(o, n, s, 2 * k, 1);
  u := call mul_row(o + k, n - k, sp, l, 1);
  u := call mul_row(o + 2 * k, n - 2 * k, z2, n2, 1);
  return 0
}

/-- The Karatsuba threshold: below this many limbs in the shorter operand, schoolbook. -/
def karaT : Word := 32

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
  ("mul_zeros", mulZeros), ("mul_win", mulWin), ("nat_mul", natMul)]

/-- `natMulProg` at another threshold (tests). -/
def natMulProgT (T : Word) : Prog := natProg ++ [("mac_hi", macHi), ("mul_row", mulRow),
  ("sub_row", subRow), ("mul_zeros", mulZeros), ("mul_win", mulWinG T), ("nat_mul", natMulG T)]

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
