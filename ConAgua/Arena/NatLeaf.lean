module

meta import ConAgua.L.Semantics
meta import ConAgua.Layout
public import ConAgua.L.Notation
public import ConAgua.L.Logic
public import ConAgua.Arena.NatOff
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.NatGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.Records
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# The linear limb passes as leaf functions

`add_n`, `add_1`, `sub_n`, `sub_1`: one loop each over pool windows given as tagged pool
addresses (the tier in bit 40, as `POOL⦃x⦄` reads them), no call, one word out (the carry or the
borrow). The output window `[o, o + n)` lies above the operands (at the pool top, the operands
below it). Each resolves its windows to tier and index once, so the compiled loop keeps them in
registers; each is a leaf the asm escape can replace by a hand-written body. `nat_add` and
`nat_sub` (`NatAdd.lean`, `NatSub.lean`) call them and trim the result.

Their specs are in `NatMul`'s window style: the output window differs from the entry pool `P0`
only in `[o, o + n)` (`Off`), and its value plus the carry (or the operand `b` plus the borrow
times `wt n`) is the sum (the minuend) of the operand windows of the entry pool.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## Window reads and writes -/

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


/-! ## Word facts -/

/-- The inline add with carry of `add_n`: `x + c + y` and the carry `u64(x + c < c) + u64(x + c + y < y)`. -/
theorem adc_inl (x y c : Word) (hc : c.toNat ≤ 1) :
    (x + c + y).toNat + (Cmp.ult.evalW (x + c) c + Cmp.ult.evalW (x + c + y) y).toNat * 2 ^ 64 =
      x.toNat + y.toNat + c.toNat := by
  have hx := x.toNat_lt; have hy := y.toNat_lt
  have e1 : (x + c).toNat = (x.toNat + c.toNat) % 2 ^ 64 := UInt64.toNat_add _ _
  have e2 : (x + c + y).toNat = ((x + c).toNat + y.toNat) % 2 ^ 64 := UInt64.toNat_add _ _
  simp only [Cmp.evalW, Cmp.eval, decide_eq_true_eq, UInt64.lt_iff_toNat_lt]
  split <;> split <;> simp only [UInt64.toNat_add, UInt64.toNat_one, UInt64.toNat_zero] <;> omega

theorem adc_inl_le (x y c : Word) (hc : c.toNat ≤ 1) :
    (Cmp.ult.evalW (x + c) c + Cmp.ult.evalW (x + c + y) y).toNat ≤ 1 := by
  have hx := x.toNat_lt; have hy := y.toNat_lt
  have e1 : (x + c).toNat = (x.toNat + c.toNat) % 2 ^ 64 := UInt64.toNat_add _ _
  have e2 : (x + c + y).toNat = ((x + c).toNat + y.toNat) % 2 ^ 64 := UInt64.toNat_add _ _
  simp only [Cmp.evalW, Cmp.eval, decide_eq_true_eq, UInt64.lt_iff_toNat_lt]
  split <;> split <;> simp only [UInt64.toNat_add, UInt64.toNat_one, UInt64.toNat_zero] <;> omega

/-- The carry ripple of `add_1`: `x + c` and the carry `u64(x + c < c)`. -/
theorem adc1_inl (x c : Word) (hc : c.toNat ≤ 1) :
    (x + c).toNat + (Cmp.ult.evalW (x + c) c).toNat * 2 ^ 64 = x.toNat + c.toNat := by
  have hx := x.toNat_lt
  have e1 : (x + c).toNat = (x.toNat + c.toNat) % 2 ^ 64 := UInt64.toNat_add _ _
  simp only [Cmp.evalW, Cmp.eval, decide_eq_true_eq, UInt64.lt_iff_toNat_lt]
  split <;> simp only [UInt64.toNat_one, UInt64.toNat_zero] <;> omega

theorem evalW_le (c : Cmp) (a b : Word) : (Cmp.evalW c a b).toNat ≤ 1 := by
  simp only [Cmp.evalW]; split <;> simp

/-- The inline subtract-with-borrow of `sub_n` and `sub_row`: `d = t - x`, the limb `d - c`, the
borrow `u64(t < x) + u64(d < c)`. -/
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

/-- The borrow ripple of `sub_1`: `x - c` and the borrow `u64(x < c)`. -/
theorem sbb1_inl (x c : Word) (hc : c.toNat ≤ 1) :
    (x - c).toNat + c.toNat = x.toNat + (Cmp.ult.evalW x c).toNat * 2 ^ 64 := by
  have hx := x.toNat_lt
  have e1 : (x - c).toNat = (2 ^ 64 - c.toNat + x.toNat) % 2 ^ 64 := UInt64.toNat_sub _ _
  simp only [Cmp.evalW, Cmp.eval, decide_eq_true_eq, UInt64.lt_iff_toNat_lt]
  split <;> simp only [UInt64.toNat_one, UInt64.toNat_zero] <;> omega

/-- A read of a window in the entry pool: the pool differs from `P0` only in `[o, o + i)`, and
the operand window lies below `o` or from `o` on. -/
theorem ld_off (m : Mem) (P0 : Array Word) (T i o : Word) (hT : T.toNat < 2 ^ 41)
    (hi : i.toNat < 2 ^ 41) (hP0 : P0.size = 2 ^ 41)
    (hs : (m.arr64 (tierA POOL (T >>> 40))).size ≤ 2 ^ 40)
    (hb : ((T &&& 1099511627775) + i).toNat < (m.arr64 (tierA POOL (T >>> 40))).size)
    (hoff : Off (vpool m) P0 o.toNat i.toNat) (hd : T.toNat + i.toNat < o.toNat ∨ o.toNat ≤ T.toNat) :
    (m.arr64 (tierA POOL (T >>> 40)))[((T &&& 1099511627775) + i).toNat] =
      P0[T.toNat + i.toNat]'(by have := win_lt m T i hT hi hs hb; omega) := by
  rw [ld_win m T i hT hi hs hb]
  have hw := win_lt m T i hT hi hs hb
  have hvs := vpool_size m
  have := hoff (T.toNat + i.toNat) (by omega)
  simp only [Array.getElem?_eq_getElem (by omega : T.toNat + i.toNat < (vpool m).size),
    Array.getElem?_eq_getElem (by omega : T.toNat + i.toNat < P0.size), Option.some.injEq] at this
  exact this

/-- One step of `add_n`'s loop, in the shape of its verification condition. -/
theorem addn_step_goal (m : Mem) (P0 : Array Word) (o oa ob i c T8 T9 T10 T11 T12 T13 : Word) (c0 : Nat)
    (h8 : T8 = o >>> 40) (h9 : T9 = o &&& 1099511627775)
    (h10 : T10 = oa >>> 40) (h11 : T11 = oa &&& 1099511627775)
    (h12 : T12 = ob >>> 40) (h13 : T13 = ob &&& 1099511627775)
    (hP0 : P0.size = 2 ^ 41) (ho : o.toNat + i.toNat < 2 ^ 41) (hoa : oa.toNat + i.toNat < 2 ^ 41)
    (hob : ob.toNat + i.toNat < 2 ^ 41)
    (hda : oa.toNat + i.toNat < o.toNat ∨ o.toNat ≤ oa.toNat)
    (hdb : ob.toNat + i.toNat < o.toNat ∨ o.toNat ≤ ob.toNat) (hc : c.toNat ≤ 1)
    (hs8 : (m.arr64 (tierA POOL T8)).size ≤ 2 ^ 40) (hs10 : (m.arr64 (tierA POOL T10)).size ≤ 2 ^ 40)
    (hs12 : (m.arr64 (tierA POOL T12)).size ≤ 2 ^ 40)
    (hb10 : (T11 + i).toNat < (m.arr64 (tierA POOL T10)).size)
    (hb12 : (T13 + i).toNat < (m.arr64 (tierA POOL T12)).size)
    (hb8 : (T9 + i).toNat < (m.arr64 (tierA POOL T8)).size)
    (hoff : Off (vpool m) P0 o.toNat i.toNat)
    (ih : pv (vpool m) o.toNat i.toNat + c.toNat * wt i.toNat =
      pv P0 oa.toNat i.toNat + pv P0 ob.toNat i.toNat + c0) :
    pv (vpool (m.set64 (tierA POOL T8) (T9 + i)
        ((m.arr64 (tierA POOL T10))[(T11 + i).toNat] + c + (m.arr64 (tierA POOL T12))[(T13 + i).toNat])))
        o.toNat (i + 1).toNat +
      (Cmp.ult.evalW ((m.arr64 (tierA POOL T10))[(T11 + i).toNat] + c) c +
        Cmp.ult.evalW ((m.arr64 (tierA POOL T10))[(T11 + i).toNat] + c +
          (m.arr64 (tierA POOL T12))[(T13 + i).toNat]) (m.arr64 (tierA POOL T12))[(T13 + i).toNat]).toNat *
        wt (i + 1).toNat =
      pv P0 oa.toNat (i + 1).toNat + pv P0 ob.toNat (i + 1).toNat + c0 := by
  subst h8 h9 h10 h11 h12 h13
  have hi1 : (i + 1).toNat = i.toNat + 1 := w_add i 1 (by simp; omega)
  have hvs := vpool_size m
  rw [ld_off m P0 oa i o (by omega) (by omega) hP0 hs10 hb10 hoff hda,
    ld_off m P0 ob i o (by omega) (by omega) hP0 hs12 hb12 hoff hdb,
    st_win m o i _ (by omega) (by omega) hs8 hb8]
  have hsb := adc_inl P0[oa.toNat + i.toNat] P0[ob.toNat + i.toNat] c hc
  generalize (Cmp.ult.evalW _ _ + _ : Word) = c' at hsb ⊢
  rw [hi1, pv_set_succ (vpool m) o.toNat i.toNat (i.toNat + 1) (o.toNat + i.toNat) _ rfl rfl (by omega),
    pv_succ P0 oa.toNat i.toNat (i.toNat + 1) (oa.toNat + i.toNat) rfl rfl (by omega),
    pv_succ P0 ob.toNat i.toNat (i.toNat + 1) (ob.toNat + i.toNat) rfl rfl (by omega),
    wt_succ i.toNat (i.toNat + 1) rfl]
  generalize pv (vpool m) o.toNat i.toNat = A at *
  generalize pv P0 oa.toNat i.toNat = B at *
  generalize pv P0 ob.toNat i.toNat = D at *
  generalize wt i.toNat = W at *
  grind

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

/-! ## The leaves -/

/-- `P[o + i] := A[oa + i] + B[ob + i] + carry` for `i < n`; the carry in `c ≤ 1`, the carry out. -/
def addNLoop : Stmt := lblk (o, oa, ob, n, c, i, x, y, pt, pb, ta, qa, tb, qb) {
  for i < n {
    x := POOL⟨ta⟩[qa + i];
    y := POOL⟨tb⟩[qb + i];
    x := x + c;
    c := u64(x < c);
    x := x + y;
    c := c + u64(x < y);
    POOL⟨pt⟩[pb + i] := x
  }
}

-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def addN : FunDecl := lfn (o, oa, ob, n, c) locals (i, x, y, pt, pb, ta, qa, tb, qb) {
  pt := ⦃o⦄.tier;
  pb := ⦃o⦄.idx;
  ta := ⦃oa⦄.tier;
  qa := ⦃oa⦄.idx;
  tb := ⦃ob⦄.tier;
  qb := ⦃ob⦄.idx;
  ⟪addNLoop⟫;
  return c
}

/-- `P[o + i] := A[oa + i] + carry` for `i < n` (the carry ripple through the longer operand). -/
def add1Loop : Stmt := lblk (o, oa, n, c, i, x, pt, pb, ta, qa) {
  for i < n {
    x := POOL⟨ta⟩[qa + i];
    x := x + c;
    c := u64(x < c);
    POOL⟨pt⟩[pb + i] := x
  }
}

-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def add1 : FunDecl := lfn (o, oa, n, c) locals (i, x, pt, pb, ta, qa) {
  pt := ⦃o⦄.tier;
  pb := ⦃o⦄.idx;
  ta := ⦃oa⦄.tier;
  qa := ⦃oa⦄.idx;
  ⟪add1Loop⟫;
  return c
}

/-- `P[o + i] := A[oa + i] - B[ob + i] - borrow` for `i < n`; the borrow in `c ≤ 1`, the borrow
out. -/
def subNLoop : Stmt := lblk (o, oa, ob, n, c, i, x, y, d, pt, pb, ta, qa, tb, qb) {
  for i < n {
    x := POOL⟨ta⟩[qa + i];
    y := POOL⟨tb⟩[qb + i];
    d := x - y;
    POOL⟨pt⟩[pb + i] := d - c;
    c := u64(x < y) + u64(d < c)
  }
}

-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def subN : FunDecl := lfn (o, oa, ob, n, c) locals (i, x, y, d, pt, pb, ta, qa, tb, qb) {
  pt := ⦃o⦄.tier;
  pb := ⦃o⦄.idx;
  ta := ⦃oa⦄.tier;
  qa := ⦃oa⦄.idx;
  tb := ⦃ob⦄.tier;
  qb := ⦃ob⦄.idx;
  ⟪subNLoop⟫;
  return c
}

/-- `P[o + i] := A[oa + i] - borrow` for `i < n`. -/
def sub1Loop : Stmt := lblk (o, oa, n, c, i, x, pt, pb, ta, qa) {
  for i < n {
    x := POOL⟨ta⟩[qa + i];
    POOL⟨pt⟩[pb + i] := x - c;
    c := u64(x < c)
  }
}

-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def sub1 : FunDecl := lfn (o, oa, n, c) locals (i, x, pt, pb, ta, qa) {
  pt := ⦃o⦄.tier;
  pb := ⦃o⦄.idx;
  ta := ⦃oa⦄.tier;
  qa := ⦃oa⦄.idx;
  ⟪sub1Loop⟫;
  return c
}

/-- `P[o + i] := A[oa + i] op B[ob + i]` for `i < n`, `op` one of `&`, `|`, `^` (the bitwise
leaves `and_n`, `or_n`, `xor_n` share this loop; L has no operator parameter, so the loop is built
from `Stmt` with the operator as a Lean argument). Locals
`(o, oa, ob, n, i, x, pt, pb, ta, qa, tb, qb)`. -/
def bitNLoop (op : BinOp) : Stmt :=
  .while (.cmp .ult (.var 4) (.var 3))
    (.seq (.set 5 (.bin op (.ld64t POOL (.var 8) (.bin .add (.var 9) (.var 4)))
        (.ld64t POOL (.var 10) (.bin .add (.var 11) (.var 4)))))
      (.seq (.st64t POOL (.var 6) (.bin .add (.var 7) (.var 4)) (.var 5))
        (.set 4 (.bin .add (.var 4) (.const 1)))))

/-- The bitwise leaf with operator `op`.
con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat` -/
@[no_expose] def bitNG (op : BinOp) : FunDecl := lfn (o, oa, ob, n) locals (i, x, pt, pb, ta, qa, tb, qb) {
  pt := ⦃o⦄.tier;
  pb := ⦃o⦄.idx;
  ta := ⦃oa⦄.tier;
  qa := ⦃oa⦄.idx;
  tb := ⦃ob⦄.tier;
  qb := ⦃ob⦄.idx;
  ⟪bitNLoop op⟫;
  return 0
}

-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def andN : FunDecl := bitNG .and
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def orN : FunDecl := bitNG .or
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def xorN : FunDecl := bitNG .xor

theorem andN_eq : andN = bitNG .and := by rfl
theorem orN_eq : orN = bitNG .or := by rfl
theorem xorN_eq : xorN = bitNG .xor := by rfl

/-- `P[o + i] := A[oa + i]` for `i < n`. -/
def copyNLoop : Stmt := lblk (o, oa, n, i, x, pt, pb, ta, qa) {
  for i < n {
    x := POOL⟨ta⟩[qa + i];
    POOL⟨pt⟩[pb + i] := x
  }
}

-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def copyN : FunDecl := lfn (o, oa, n) locals (i, x, pt, pb, ta, qa) {
  pt := ⦃o⦄.tier;
  pb := ⦃o⦄.idx;
  ta := ⦃oa⦄.tier;
  qa := ⦃oa⦄.idx;
  ⟪copyNLoop⟫;
  return 0
}

/-- The leaves, as one program. -/
def natLeafProg : Prog := [("add_n", addN), ("add_1", add1), ("sub_n", subN), ("sub_1", sub1),
  ("and_n", andN), ("or_n", orN), ("xor_n", xorN), ("copy_n", copyN)]

/- `[max, 1] + [1, 2] + 1 = [1, 4]`, carry 0; `[max] + 1 = [0]`, carry 1. -/
#guard (run natLeafProg 100 "add_n" [4, 0, 2, 2, 1]
  (Mem.ofWords [(POOL, #[0xFFFFFFFFFFFFFFFF, 1, 1, 2, 0, 0])])).toOption.map (fun (r, m) => (r, m.arr64 POOL)) ==
  some ([0], #[0xFFFFFFFFFFFFFFFF, 1, 1, 2, 1, 4])
#guard (run natLeafProg 100 "add_1" [1, 0, 1, 1]
  (Mem.ofWords [(POOL, #[0xFFFFFFFFFFFFFFFF, 7])])).toOption.map (fun (r, m) => (r, m.arr64 POOL)) ==
  some ([1], #[0xFFFFFFFFFFFFFFFF, 0])
/- `[0, 1] - [1, 0] = [max, 0]`, borrow 0; `[0] - 1 = [max]`, borrow 1. -/
#guard (run natLeafProg 100 "sub_n" [4, 0, 2, 2, 0]
  (Mem.ofWords [(POOL, #[0, 1, 1, 0, 7, 7])])).toOption.map (fun (r, m) => (r, m.arr64 POOL)) ==
  some ([0], #[0, 1, 1, 0, 0xFFFFFFFFFFFFFFFF, 0])
/- `[0xF0, 0x0F] | [0x0F, 0xF0] = [0xFF, 0xFF]`; a copy. -/
#guard (run natLeafProg 100 "or_n" [4, 0, 2, 2]
  (Mem.ofWords [(POOL, #[0xF0, 0x0F, 0x0F, 0xF0, 0, 0])])).toOption.map (fun (r, m) => (r, m.arr64 POOL)) ==
  some ([0], #[0xF0, 0x0F, 0x0F, 0xF0, 0xFF, 0xFF])
#guard (run natLeafProg 100 "copy_n" [2, 0, 2]
  (Mem.ofWords [(POOL, #[5, 7, 0, 0])])).toOption.map (fun (r, m) => (r, m.arr64 POOL)) ==
  some ([0], #[5, 7, 5, 7])
#guard (run natLeafProg 100 "sub_1" [1, 0, 1, 1]
  (Mem.ofWords [(POOL, #[0, 7])])).toOption.map (fun (r, m) => (r, m.arr64 POOL)) ==
  some ([1], #[0, 0xFFFFFFFFFFFFFFFF])

/-! ## `add_n` -/

section addn
variable (p : Prog) (P0 : Array Word) (C c0 : Nat)

/-- `add_n`'s loop: locals `(o, oa, ob, n, c, i, x, y, pt, pb, ta, qa, tb, qb)`. -/
def AddNInv (P0 : Array Word) (C c0 : Nat) (s : St) : Prop :=
  C < 2 ^ 64 ∧ P0.size = 2 ^ 41 ∧ pcap s.mem = C ∧
  (s.loc 0).toNat + (s.loc 3).toNat ≤ C ∧ (s.loc 1).toNat + (s.loc 3).toNat ≤ C ∧
  (s.loc 2).toNat + (s.loc 3).toNat ≤ C ∧
  ((s.loc 1).toNat + (s.loc 3).toNat ≤ (s.loc 0).toNat ∨ (s.loc 0).toNat ≤ (s.loc 1).toNat) ∧
  ((s.loc 2).toNat + (s.loc 3).toNat ≤ (s.loc 0).toNat ∨ (s.loc 0).toNat ≤ (s.loc 2).toNat) ∧
  s.loc 8 = s.loc 0 >>> 40 ∧ s.loc 9 = s.loc 0 &&& 1099511627775 ∧
  s.loc 10 = s.loc 1 >>> 40 ∧ s.loc 11 = s.loc 1 &&& 1099511627775 ∧
  s.loc 12 = s.loc 2 >>> 40 ∧ s.loc 13 = s.loc 2 &&& 1099511627775 ∧
  (s.mem.arr64 (tierA POOL (s.loc 8))).size ≤ 2 ^ 40 ∧
  (s.mem.arr64 (tierA POOL (s.loc 10))).size ≤ 2 ^ 40 ∧
  (s.mem.arr64 (tierA POOL (s.loc 12))).size ≤ 2 ^ 40 ∧
  (s.loc 5).toNat ≤ (s.loc 3).toNat ∧ (s.loc 4).toNat ≤ 1 ∧
  Off (vpool s.mem) P0 (s.loc 0).toNat (s.loc 5).toNat ∧
  pv (vpool s.mem) (s.loc 0).toNat (s.loc 5).toNat + (s.loc 4).toNat * wt (s.loc 5).toNat =
    pv P0 (s.loc 1).toNat (s.loc 5).toNat + pv P0 (s.loc 2).toNat (s.loc 5).toNat + c0

def AddNPost (P0 : Array Word) (C c0 : Nat) (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ PFrame s₀.mem s'.mem ∧ pcap s'.mem = C ∧
  s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧
  (s'.loc 4).toNat ≤ 1 ∧
  Off (vpool s'.mem) P0 (s₀.loc 0).toNat (s₀.loc 3).toNat ∧
  pv (vpool s'.mem) (s₀.loc 0).toNat (s₀.loc 3).toNat + (s'.loc 4).toNat * wt (s₀.loc 3).toNat =
    pv P0 (s₀.loc 1).toNat (s₀.loc 3).toNat + pv P0 (s₀.loc 2).toNat (s₀.loc 3).toNat + c0

theorem addNLoop_spec (n : Nat) (s₀ : St) (h : AddNInv P0 C c0 s₀) :
    ⦃fun s => s = s₀⦄ exec p n addNLoop ⦃fun r s' => AddNPost P0 C c0 s₀ r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [AddNInv, AddNPost] at h ⊢
    rw [exec, step_while (w := addNLoop) rfl]
    vcgen [step, evalE, evalC, setLoc, setLocs, ld64, st64, ih]
    all_goals clear ih
    all_goals (try simp only [AddNInv, AddNPost] at *)
    all_goals (try subst_vars)
    all_goals (try and_intros)
    all_goals (try dsimp only at *)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, Cmp.eval, BinOp.eval, Mem.size64_set64,
      Nat.reduceEqDiff, reduceIte, decide_eq_true_eq] at *)
    all_goals first
      | (with_reducible apply addn_step_goal <;> grind [pcap_eq])
      | grind (splits := 8) [arena_grind, lang_grind, adc_inl_le]

theorem addNLoop_step_spec (n : Nat) (s₀ : St) (h : AddNInv P0 C c0 s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) addNLoop ⦃fun r s' => AddNPost P0 C c0 s₀ r s'; ⊤⦄ :=
  Triple.step_exec (addNLoop_spec p P0 C c0 (n + 1) s₀ h)

/-- `add_n(o, oa, ob, k, c)`: `P[o, o + k) := a + b + c` (low `k` limbs), the carry out; the
output window lies below or above each operand window. -/
theorem addN_spec (hp : p.lookup "add_n" = some addN) (n : Nat) (s₀ : St) (o oa ob k c : Word)
    (hs : pcap s₀.mem < 2 ^ 64) (ho : o.toNat + k.toNat ≤ pcap s₀.mem)
    (ha : oa.toNat + k.toNat ≤ pcap s₀.mem) (hb : ob.toNat + k.toNat ≤ pcap s₀.mem)
    (hda : oa.toNat + k.toNat ≤ o.toNat ∨ o.toNat ≤ oa.toNat)
    (hdb : ob.toNat + k.toNat ≤ o.toNat ∨ o.toNat ≤ ob.toNat) (hc : c.toNat ≤ 1) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "add_n" [o, oa, ob, k, c]
    ⦃fun r s' => LocEq s' s₀ ∧ PFrame s₀.mem s'.mem ∧ pcap s'.mem = pcap s₀.mem ∧
      Off (vpool s'.mem) (vpool s₀.mem) o.toNat k.toNat ∧ (r.headD 0).toNat ≤ 1 ∧
      pv (vpool s'.mem) o.toNat k.toNat + (r.headD 0).toNat * wt k.toNat =
        pv (vpool s₀.mem) oa.toNat k.toNat + pv (vpool s₀.mem) ob.toNat k.toNat + c.toNat; ⊤⦄ := by
  have h1 := pcap_tier s₀.mem (o >>> 40) hs
  have h2 := pcap_tier s₀.mem (oa >>> 40) hs
  have h3 := pcap_tier s₀.mem (ob >>> 40) hs
  rw [invoke_eq _ hp]
  simp only [callFn, addN]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      addNLoop_step_spec p (vpool s₀.mem) (pcap s₀.mem) c.toNat n]
    all_goals (try simp only [AddNInv, AddNPost] at *)
    all_goals (try subst_vars)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem,
      L.Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, BinOp.eval,
      reduceIte, Nat.reduceEqDiff, UInt64.toNat_zero] at *)
    all_goals (try and_intros)
    all_goals grind (splits := 8) [arena_grind, lang_grind, LocEq]

end addn

/-! ## `add_1`, `sub_n`, `sub_1` -/

/-- One step of `add_1`'s loop, in the shape of its verification condition. -/
theorem add1_step_goal (m : Mem) (P0 : Array Word) (o oa i c T6 T7 T8 T9 : Word) (c0 : Nat)
    (h6 : T6 = o >>> 40) (h7 : T7 = o &&& 1099511627775)
    (h8 : T8 = oa >>> 40) (h9 : T9 = oa &&& 1099511627775)
    (hP0 : P0.size = 2 ^ 41) (ho : o.toNat + i.toNat < 2 ^ 41) (hoa : oa.toNat + i.toNat < 2 ^ 41)
    (hda : oa.toNat + i.toNat < o.toNat ∨ o.toNat ≤ oa.toNat) (hc : c.toNat ≤ 1)
    (hs6 : (m.arr64 (tierA POOL T6)).size ≤ 2 ^ 40) (hs8 : (m.arr64 (tierA POOL T8)).size ≤ 2 ^ 40)
    (hb8 : (T9 + i).toNat < (m.arr64 (tierA POOL T8)).size)
    (hb6 : (T7 + i).toNat < (m.arr64 (tierA POOL T6)).size)
    (hoff : Off (vpool m) P0 o.toNat i.toNat)
    (ih : pv (vpool m) o.toNat i.toNat + c.toNat * wt i.toNat = pv P0 oa.toNat i.toNat + c0) :
    pv (vpool (m.set64 (tierA POOL T6) (T7 + i) ((m.arr64 (tierA POOL T8))[(T9 + i).toNat] + c)))
        o.toNat (i + 1).toNat +
      (Cmp.ult.evalW ((m.arr64 (tierA POOL T8))[(T9 + i).toNat] + c) c).toNat * wt (i + 1).toNat =
      pv P0 oa.toNat (i + 1).toNat + c0 := by
  subst h6 h7 h8 h9
  have hi1 : (i + 1).toNat = i.toNat + 1 := w_add i 1 (by simp; omega)
  have hvs := vpool_size m
  rw [ld_off m P0 oa i o (by omega) (by omega) hP0 hs8 hb8 hoff hda,
    st_win m o i _ (by omega) (by omega) hs6 hb6]
  have hsb := adc1_inl P0[oa.toNat + i.toNat] c hc
  generalize (Cmp.ult.evalW _ _ : Word) = c' at hsb ⊢
  rw [hi1, pv_set_succ (vpool m) o.toNat i.toNat (i.toNat + 1) (o.toNat + i.toNat) _ rfl rfl (by omega),
    pv_succ P0 oa.toNat i.toNat (i.toNat + 1) (oa.toNat + i.toNat) rfl rfl (by omega),
    wt_succ i.toNat (i.toNat + 1) rfl]
  generalize pv (vpool m) o.toNat i.toNat = A at *
  generalize pv P0 oa.toNat i.toNat = B at *
  generalize wt i.toNat = W at *
  grind

/-- One step of `sub_n`'s loop, in the shape of its verification condition. -/
theorem subn_step_goal (m : Mem) (P0 : Array Word) (o oa ob i c T9 T10 T11 T12 T13 T14 : Word) (c0 : Nat)
    (h9 : T9 = o >>> 40) (h10 : T10 = o &&& 1099511627775)
    (h11 : T11 = oa >>> 40) (h12 : T12 = oa &&& 1099511627775)
    (h13 : T13 = ob >>> 40) (h14 : T14 = ob &&& 1099511627775)
    (hP0 : P0.size = 2 ^ 41) (ho : o.toNat + i.toNat < 2 ^ 41) (hoa : oa.toNat + i.toNat < 2 ^ 41)
    (hob : ob.toNat + i.toNat < 2 ^ 41)
    (hda : oa.toNat + i.toNat < o.toNat ∨ o.toNat ≤ oa.toNat)
    (hdb : ob.toNat + i.toNat < o.toNat ∨ o.toNat ≤ ob.toNat) (hc : c.toNat ≤ 1)
    (hs9 : (m.arr64 (tierA POOL T9)).size ≤ 2 ^ 40) (hs11 : (m.arr64 (tierA POOL T11)).size ≤ 2 ^ 40)
    (hs13 : (m.arr64 (tierA POOL T13)).size ≤ 2 ^ 40)
    (hb11 : (T12 + i).toNat < (m.arr64 (tierA POOL T11)).size)
    (hb13 : (T14 + i).toNat < (m.arr64 (tierA POOL T13)).size)
    (hb9 : (T10 + i).toNat < (m.arr64 (tierA POOL T9)).size)
    (hoff : Off (vpool m) P0 o.toNat i.toNat)
    (ih : pv (vpool m) o.toNat i.toNat + pv P0 ob.toNat i.toNat + c0 =
      pv P0 oa.toNat i.toNat + c.toNat * wt i.toNat) :
    pv (vpool (m.set64 (tierA POOL T9) (T10 + i)
        ((m.arr64 (tierA POOL T11))[(T12 + i).toNat] - (m.arr64 (tierA POOL T13))[(T14 + i).toNat] - c)))
        o.toNat (i + 1).toNat + pv P0 ob.toNat (i + 1).toNat + c0 =
      pv P0 oa.toNat (i + 1).toNat +
        (Cmp.ult.evalW (m.arr64 (tierA POOL T11))[(T12 + i).toNat] (m.arr64 (tierA POOL T13))[(T14 + i).toNat] +
          Cmp.ult.evalW ((m.arr64 (tierA POOL T11))[(T12 + i).toNat] - (m.arr64 (tierA POOL T13))[(T14 + i).toNat])
            c).toNat * wt (i + 1).toNat := by
  subst h9 h10 h11 h12 h13 h14
  have hi1 : (i + 1).toNat = i.toNat + 1 := w_add i 1 (by simp; omega)
  have hvs := vpool_size m
  rw [ld_off m P0 oa i o (by omega) (by omega) hP0 hs11 hb11 hoff hda,
    ld_off m P0 ob i o (by omega) (by omega) hP0 hs13 hb13 hoff hdb,
    st_win m o i _ (by omega) (by omega) hs9 hb9]
  have hsb := sbb_inl P0[oa.toNat + i.toNat] P0[ob.toNat + i.toNat] c hc
  generalize (Cmp.ult.evalW _ _ + _ : Word) = c' at hsb ⊢
  rw [hi1, pv_set_succ (vpool m) o.toNat i.toNat (i.toNat + 1) (o.toNat + i.toNat) _ rfl rfl (by omega),
    pv_succ P0 oa.toNat i.toNat (i.toNat + 1) (oa.toNat + i.toNat) rfl rfl (by omega),
    pv_succ P0 ob.toNat i.toNat (i.toNat + 1) (ob.toNat + i.toNat) rfl rfl (by omega),
    wt_succ i.toNat (i.toNat + 1) rfl]
  generalize pv (vpool m) o.toNat i.toNat = A at *
  generalize pv P0 oa.toNat i.toNat = B at *
  generalize pv P0 ob.toNat i.toNat = D at *
  generalize wt i.toNat = W at *
  grind

/-- One step of `sub_1`'s loop, in the shape of its verification condition. -/
theorem sub1_step_goal (m : Mem) (P0 : Array Word) (o oa i c T6 T7 T8 T9 : Word) (c0 : Nat)
    (h6 : T6 = o >>> 40) (h7 : T7 = o &&& 1099511627775)
    (h8 : T8 = oa >>> 40) (h9 : T9 = oa &&& 1099511627775)
    (hP0 : P0.size = 2 ^ 41) (ho : o.toNat + i.toNat < 2 ^ 41) (hoa : oa.toNat + i.toNat < 2 ^ 41)
    (hda : oa.toNat + i.toNat < o.toNat ∨ o.toNat ≤ oa.toNat) (hc : c.toNat ≤ 1)
    (hs6 : (m.arr64 (tierA POOL T6)).size ≤ 2 ^ 40) (hs8 : (m.arr64 (tierA POOL T8)).size ≤ 2 ^ 40)
    (hb8 : (T9 + i).toNat < (m.arr64 (tierA POOL T8)).size)
    (hb6 : (T7 + i).toNat < (m.arr64 (tierA POOL T6)).size)
    (hoff : Off (vpool m) P0 o.toNat i.toNat)
    (ih : pv (vpool m) o.toNat i.toNat + c0 = pv P0 oa.toNat i.toNat + c.toNat * wt i.toNat) :
    pv (vpool (m.set64 (tierA POOL T6) (T7 + i) ((m.arr64 (tierA POOL T8))[(T9 + i).toNat] - c)))
        o.toNat (i + 1).toNat + c0 =
      pv P0 oa.toNat (i + 1).toNat +
        (Cmp.ult.evalW (m.arr64 (tierA POOL T8))[(T9 + i).toNat] c).toNat * wt (i + 1).toNat := by
  subst h6 h7 h8 h9
  have hi1 : (i + 1).toNat = i.toNat + 1 := w_add i 1 (by simp; omega)
  have hvs := vpool_size m
  rw [ld_off m P0 oa i o (by omega) (by omega) hP0 hs8 hb8 hoff hda,
    st_win m o i _ (by omega) (by omega) hs6 hb6]
  have hsb := sbb1_inl P0[oa.toNat + i.toNat] c hc
  generalize (Cmp.ult.evalW _ _ : Word) = c' at hsb ⊢
  rw [hi1, pv_set_succ (vpool m) o.toNat i.toNat (i.toNat + 1) (o.toNat + i.toNat) _ rfl rfl (by omega),
    pv_succ P0 oa.toNat i.toNat (i.toNat + 1) (oa.toNat + i.toNat) rfl rfl (by omega),
    wt_succ i.toNat (i.toNat + 1) rfl]
  generalize pv (vpool m) o.toNat i.toNat = A at *
  generalize pv P0 oa.toNat i.toNat = B at *
  generalize wt i.toNat = W at *
  grind

section add1
variable (p : Prog) (P0 : Array Word) (C c0 : Nat)

/-- `add_1`'s loop: locals `(o, oa, n, c, i, x, pt, pb, ta, qa)`. -/
def Add1Inv (P0 : Array Word) (C c0 : Nat) (s : St) : Prop :=
  C < 2 ^ 64 ∧ P0.size = 2 ^ 41 ∧ pcap s.mem = C ∧
  (s.loc 0).toNat + (s.loc 2).toNat ≤ C ∧ (s.loc 1).toNat + (s.loc 2).toNat ≤ C ∧
  ((s.loc 1).toNat + (s.loc 2).toNat ≤ (s.loc 0).toNat ∨ (s.loc 0).toNat ≤ (s.loc 1).toNat) ∧
  s.loc 6 = s.loc 0 >>> 40 ∧ s.loc 7 = s.loc 0 &&& 1099511627775 ∧
  s.loc 8 = s.loc 1 >>> 40 ∧ s.loc 9 = s.loc 1 &&& 1099511627775 ∧
  (s.mem.arr64 (tierA POOL (s.loc 6))).size ≤ 2 ^ 40 ∧
  (s.mem.arr64 (tierA POOL (s.loc 8))).size ≤ 2 ^ 40 ∧
  (s.loc 4).toNat ≤ (s.loc 2).toNat ∧ (s.loc 3).toNat ≤ 1 ∧
  Off (vpool s.mem) P0 (s.loc 0).toNat (s.loc 4).toNat ∧
  pv (vpool s.mem) (s.loc 0).toNat (s.loc 4).toNat + (s.loc 3).toNat * wt (s.loc 4).toNat =
    pv P0 (s.loc 1).toNat (s.loc 4).toNat + c0

def Add1Post (P0 : Array Word) (C c0 : Nat) (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ PFrame s₀.mem s'.mem ∧ pcap s'.mem = C ∧
  s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧
  (s'.loc 3).toNat ≤ 1 ∧
  Off (vpool s'.mem) P0 (s₀.loc 0).toNat (s₀.loc 2).toNat ∧
  pv (vpool s'.mem) (s₀.loc 0).toNat (s₀.loc 2).toNat + (s'.loc 3).toNat * wt (s₀.loc 2).toNat =
    pv P0 (s₀.loc 1).toNat (s₀.loc 2).toNat + c0

theorem add1Loop_spec (n : Nat) (s₀ : St) (h : Add1Inv P0 C c0 s₀) :
    ⦃fun s => s = s₀⦄ exec p n add1Loop ⦃fun r s' => Add1Post P0 C c0 s₀ r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [Add1Inv, Add1Post] at h ⊢
    rw [exec, step_while (w := add1Loop) rfl]
    vcgen [step, evalE, evalC, setLoc, setLocs, ld64, st64, ih]
    all_goals clear ih
    all_goals (try simp only [Add1Inv, Add1Post] at *)
    all_goals (try subst_vars)
    all_goals (try and_intros)
    all_goals (try dsimp only at *)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, Cmp.eval, BinOp.eval, Mem.size64_set64,
      Nat.reduceEqDiff, reduceIte, decide_eq_true_eq] at *)
    all_goals first
      | (with_reducible apply add1_step_goal <;> grind [pcap_eq])
      | grind (splits := 8) [arena_grind, lang_grind, evalW_le]

theorem add1Loop_step_spec (n : Nat) (s₀ : St) (h : Add1Inv P0 C c0 s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) add1Loop ⦃fun r s' => Add1Post P0 C c0 s₀ r s'; ⊤⦄ :=
  Triple.step_exec (add1Loop_spec p P0 C c0 (n + 1) s₀ h)

/-- `add_1(o, oa, k, c)`: `P[o, o + k) := a + c` (low `k` limbs), the carry out. -/
theorem add1_spec (hp : p.lookup "add_1" = some add1) (n : Nat) (s₀ : St) (o oa k c : Word)
    (hs : pcap s₀.mem < 2 ^ 64) (ho : o.toNat + k.toNat ≤ pcap s₀.mem)
    (ha : oa.toNat + k.toNat ≤ pcap s₀.mem)
    (hda : oa.toNat + k.toNat ≤ o.toNat ∨ o.toNat ≤ oa.toNat) (hc : c.toNat ≤ 1) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "add_1" [o, oa, k, c]
    ⦃fun r s' => LocEq s' s₀ ∧ PFrame s₀.mem s'.mem ∧ pcap s'.mem = pcap s₀.mem ∧
      Off (vpool s'.mem) (vpool s₀.mem) o.toNat k.toNat ∧ (r.headD 0).toNat ≤ 1 ∧
      pv (vpool s'.mem) o.toNat k.toNat + (r.headD 0).toNat * wt k.toNat =
        pv (vpool s₀.mem) oa.toNat k.toNat + c.toNat; ⊤⦄ := by
  have h1 := pcap_tier s₀.mem (o >>> 40) hs
  have h2 := pcap_tier s₀.mem (oa >>> 40) hs
  rw [invoke_eq _ hp]
  simp only [callFn, add1]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      add1Loop_step_spec p (vpool s₀.mem) (pcap s₀.mem) c.toNat n]
    all_goals (try simp only [Add1Inv, Add1Post] at *)
    all_goals (try subst_vars)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem,
      L.Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, BinOp.eval,
      reduceIte, Nat.reduceEqDiff, UInt64.toNat_zero] at *)
    all_goals (try and_intros)
    all_goals grind (splits := 8) [arena_grind, lang_grind, LocEq]

end add1

section subn
variable (p : Prog) (P0 : Array Word) (C c0 : Nat)

/-- `sub_n`'s loop: locals `(o, oa, ob, n, c, i, x, y, d, pt, pb, ta, qa, tb, qb)`. -/
def SubNInv (P0 : Array Word) (C c0 : Nat) (s : St) : Prop :=
  C < 2 ^ 64 ∧ P0.size = 2 ^ 41 ∧ pcap s.mem = C ∧
  (s.loc 0).toNat + (s.loc 3).toNat ≤ C ∧ (s.loc 1).toNat + (s.loc 3).toNat ≤ C ∧
  (s.loc 2).toNat + (s.loc 3).toNat ≤ C ∧
  ((s.loc 1).toNat + (s.loc 3).toNat ≤ (s.loc 0).toNat ∨ (s.loc 0).toNat ≤ (s.loc 1).toNat) ∧
  ((s.loc 2).toNat + (s.loc 3).toNat ≤ (s.loc 0).toNat ∨ (s.loc 0).toNat ≤ (s.loc 2).toNat) ∧
  s.loc 9 = s.loc 0 >>> 40 ∧ s.loc 10 = s.loc 0 &&& 1099511627775 ∧
  s.loc 11 = s.loc 1 >>> 40 ∧ s.loc 12 = s.loc 1 &&& 1099511627775 ∧
  s.loc 13 = s.loc 2 >>> 40 ∧ s.loc 14 = s.loc 2 &&& 1099511627775 ∧
  (s.mem.arr64 (tierA POOL (s.loc 9))).size ≤ 2 ^ 40 ∧
  (s.mem.arr64 (tierA POOL (s.loc 11))).size ≤ 2 ^ 40 ∧
  (s.mem.arr64 (tierA POOL (s.loc 13))).size ≤ 2 ^ 40 ∧
  (s.loc 5).toNat ≤ (s.loc 3).toNat ∧ (s.loc 4).toNat ≤ 1 ∧
  Off (vpool s.mem) P0 (s.loc 0).toNat (s.loc 5).toNat ∧
  pv (vpool s.mem) (s.loc 0).toNat (s.loc 5).toNat + pv P0 (s.loc 2).toNat (s.loc 5).toNat + c0 =
    pv P0 (s.loc 1).toNat (s.loc 5).toNat + (s.loc 4).toNat * wt (s.loc 5).toNat

def SubNPost (P0 : Array Word) (C c0 : Nat) (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ PFrame s₀.mem s'.mem ∧ pcap s'.mem = C ∧
  s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧
  (s'.loc 4).toNat ≤ 1 ∧
  Off (vpool s'.mem) P0 (s₀.loc 0).toNat (s₀.loc 3).toNat ∧
  pv (vpool s'.mem) (s₀.loc 0).toNat (s₀.loc 3).toNat + pv P0 (s₀.loc 2).toNat (s₀.loc 3).toNat + c0 =
    pv P0 (s₀.loc 1).toNat (s₀.loc 3).toNat + (s'.loc 4).toNat * wt (s₀.loc 3).toNat

theorem subNLoop_spec (n : Nat) (s₀ : St) (h : SubNInv P0 C c0 s₀) :
    ⦃fun s => s = s₀⦄ exec p n subNLoop ⦃fun r s' => SubNPost P0 C c0 s₀ r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [SubNInv, SubNPost] at h ⊢
    rw [exec, step_while (w := subNLoop) rfl]
    vcgen [step, evalE, evalC, setLoc, setLocs, ld64, st64, ih]
    all_goals clear ih
    all_goals (try simp only [SubNInv, SubNPost] at *)
    all_goals (try subst_vars)
    all_goals (try and_intros)
    all_goals (try dsimp only at *)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, Cmp.eval, BinOp.eval, Mem.size64_set64,
      Nat.reduceEqDiff, reduceIte, decide_eq_true_eq] at *)
    all_goals first
      | (with_reducible apply subn_step_goal <;> grind [pcap_eq])
      | grind (splits := 8) [arena_grind, lang_grind, sbb_inl_le]

theorem subNLoop_step_spec (n : Nat) (s₀ : St) (h : SubNInv P0 C c0 s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) subNLoop ⦃fun r s' => SubNPost P0 C c0 s₀ r s'; ⊤⦄ :=
  Triple.step_exec (subNLoop_spec p P0 C c0 (n + 1) s₀ h)

/-- `sub_n(o, oa, ob, k, c)`: `P[o, o + k) := a - b - c` (low `k` limbs), the borrow out. -/
theorem subN_spec (hp : p.lookup "sub_n" = some subN) (n : Nat) (s₀ : St) (o oa ob k c : Word)
    (hs : pcap s₀.mem < 2 ^ 64) (ho : o.toNat + k.toNat ≤ pcap s₀.mem)
    (ha : oa.toNat + k.toNat ≤ pcap s₀.mem) (hb : ob.toNat + k.toNat ≤ pcap s₀.mem)
    (hda : oa.toNat + k.toNat ≤ o.toNat ∨ o.toNat ≤ oa.toNat)
    (hdb : ob.toNat + k.toNat ≤ o.toNat ∨ o.toNat ≤ ob.toNat) (hc : c.toNat ≤ 1) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "sub_n" [o, oa, ob, k, c]
    ⦃fun r s' => LocEq s' s₀ ∧ PFrame s₀.mem s'.mem ∧ pcap s'.mem = pcap s₀.mem ∧
      Off (vpool s'.mem) (vpool s₀.mem) o.toNat k.toNat ∧ (r.headD 0).toNat ≤ 1 ∧
      pv (vpool s'.mem) o.toNat k.toNat + pv (vpool s₀.mem) ob.toNat k.toNat + c.toNat =
        pv (vpool s₀.mem) oa.toNat k.toNat + (r.headD 0).toNat * wt k.toNat; ⊤⦄ := by
  have h1 := pcap_tier s₀.mem (o >>> 40) hs
  have h2 := pcap_tier s₀.mem (oa >>> 40) hs
  have h3 := pcap_tier s₀.mem (ob >>> 40) hs
  rw [invoke_eq _ hp]
  simp only [callFn, subN]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      subNLoop_step_spec p (vpool s₀.mem) (pcap s₀.mem) c.toNat n]
    all_goals (try simp only [SubNInv, SubNPost] at *)
    all_goals (try subst_vars)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem,
      L.Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, BinOp.eval,
      reduceIte, Nat.reduceEqDiff, UInt64.toNat_zero] at *)
    all_goals (try and_intros)
    all_goals grind (splits := 8) [arena_grind, lang_grind, LocEq]

end subn

section sub1
variable (p : Prog) (P0 : Array Word) (C c0 : Nat)

/-- `sub_1`'s loop: locals `(o, oa, n, c, i, x, pt, pb, ta, qa)`. -/
def Sub1Inv (P0 : Array Word) (C c0 : Nat) (s : St) : Prop :=
  C < 2 ^ 64 ∧ P0.size = 2 ^ 41 ∧ pcap s.mem = C ∧
  (s.loc 0).toNat + (s.loc 2).toNat ≤ C ∧ (s.loc 1).toNat + (s.loc 2).toNat ≤ C ∧
  ((s.loc 1).toNat + (s.loc 2).toNat ≤ (s.loc 0).toNat ∨ (s.loc 0).toNat ≤ (s.loc 1).toNat) ∧
  s.loc 6 = s.loc 0 >>> 40 ∧ s.loc 7 = s.loc 0 &&& 1099511627775 ∧
  s.loc 8 = s.loc 1 >>> 40 ∧ s.loc 9 = s.loc 1 &&& 1099511627775 ∧
  (s.mem.arr64 (tierA POOL (s.loc 6))).size ≤ 2 ^ 40 ∧
  (s.mem.arr64 (tierA POOL (s.loc 8))).size ≤ 2 ^ 40 ∧
  (s.loc 4).toNat ≤ (s.loc 2).toNat ∧ (s.loc 3).toNat ≤ 1 ∧
  Off (vpool s.mem) P0 (s.loc 0).toNat (s.loc 4).toNat ∧
  pv (vpool s.mem) (s.loc 0).toNat (s.loc 4).toNat + c0 =
    pv P0 (s.loc 1).toNat (s.loc 4).toNat + (s.loc 3).toNat * wt (s.loc 4).toNat

def Sub1Post (P0 : Array Word) (C c0 : Nat) (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ PFrame s₀.mem s'.mem ∧ pcap s'.mem = C ∧
  s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧
  (s'.loc 3).toNat ≤ 1 ∧
  Off (vpool s'.mem) P0 (s₀.loc 0).toNat (s₀.loc 2).toNat ∧
  pv (vpool s'.mem) (s₀.loc 0).toNat (s₀.loc 2).toNat + c0 =
    pv P0 (s₀.loc 1).toNat (s₀.loc 2).toNat + (s'.loc 3).toNat * wt (s₀.loc 2).toNat

theorem sub1Loop_spec (n : Nat) (s₀ : St) (h : Sub1Inv P0 C c0 s₀) :
    ⦃fun s => s = s₀⦄ exec p n sub1Loop ⦃fun r s' => Sub1Post P0 C c0 s₀ r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [Sub1Inv, Sub1Post] at h ⊢
    rw [exec, step_while (w := sub1Loop) rfl]
    vcgen [step, evalE, evalC, setLoc, setLocs, ld64, st64, ih]
    all_goals clear ih
    all_goals (try simp only [Sub1Inv, Sub1Post] at *)
    all_goals (try subst_vars)
    all_goals (try and_intros)
    all_goals (try dsimp only at *)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, Cmp.eval, BinOp.eval, Mem.size64_set64,
      Nat.reduceEqDiff, reduceIte, decide_eq_true_eq] at *)
    all_goals first
      | (with_reducible apply sub1_step_goal <;> grind [pcap_eq])
      | grind (splits := 8) [arena_grind, lang_grind, evalW_le]

theorem sub1Loop_step_spec (n : Nat) (s₀ : St) (h : Sub1Inv P0 C c0 s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) sub1Loop ⦃fun r s' => Sub1Post P0 C c0 s₀ r s'; ⊤⦄ :=
  Triple.step_exec (sub1Loop_spec p P0 C c0 (n + 1) s₀ h)

/-- `sub_1(o, oa, k, c)`: `P[o, o + k) := a - c` (low `k` limbs), the borrow out. -/
theorem sub1_spec (hp : p.lookup "sub_1" = some sub1) (n : Nat) (s₀ : St) (o oa k c : Word)
    (hs : pcap s₀.mem < 2 ^ 64) (ho : o.toNat + k.toNat ≤ pcap s₀.mem)
    (ha : oa.toNat + k.toNat ≤ pcap s₀.mem)
    (hda : oa.toNat + k.toNat ≤ o.toNat ∨ o.toNat ≤ oa.toNat) (hc : c.toNat ≤ 1) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "sub_1" [o, oa, k, c]
    ⦃fun r s' => LocEq s' s₀ ∧ PFrame s₀.mem s'.mem ∧ pcap s'.mem = pcap s₀.mem ∧
      Off (vpool s'.mem) (vpool s₀.mem) o.toNat k.toNat ∧ (r.headD 0).toNat ≤ 1 ∧
      pv (vpool s'.mem) o.toNat k.toNat + c.toNat =
        pv (vpool s₀.mem) oa.toNat k.toNat + (r.headD 0).toNat * wt k.toNat; ⊤⦄ := by
  have h1 := pcap_tier s₀.mem (o >>> 40) hs
  have h2 := pcap_tier s₀.mem (oa >>> 40) hs
  rw [invoke_eq _ hp]
  simp only [callFn, sub1]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      sub1Loop_step_spec p (vpool s₀.mem) (pcap s₀.mem) c.toNat n]
    all_goals (try simp only [Sub1Inv, Sub1Post] at *)
    all_goals (try subst_vars)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem,
      L.Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, BinOp.eval,
      reduceIte, Nat.reduceEqDiff, UInt64.toNat_zero] at *)
    all_goals (try and_intros)
    all_goals grind (splits := 8) [arena_grind, lang_grind, LocEq]

end sub1

/-! ## The bitwise leaves and `copy_n` -/

/-- The first `k` limbs of two windows of `p` combined limb by limb with `f`. -/
def bwv (f : Word → Word → Word) (p : Array Word) (oa ob : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => bwv f p oa ob k + (f (p[oa + k]?.getD 0) (p[ob + k]?.getD 0)).toNat * wt k

/-- One step of a bitwise leaf's loop, in the shape of its verification condition. -/
theorem bitn_step_goal (op : BinOp) (m : Mem) (P0 : Array Word) (o oa ob i T6 T7 T8 T9 T10 T11 : Word)
    (h6 : T6 = o >>> 40) (h7 : T7 = o &&& 1099511627775)
    (h8 : T8 = oa >>> 40) (h9 : T9 = oa &&& 1099511627775)
    (h10 : T10 = ob >>> 40) (h11 : T11 = ob &&& 1099511627775)
    (hP0 : P0.size = 2 ^ 41) (ho : o.toNat + i.toNat < 2 ^ 41) (hoa : oa.toNat + i.toNat < 2 ^ 41)
    (hob : ob.toNat + i.toNat < 2 ^ 41)
    (hda : oa.toNat + i.toNat < o.toNat ∨ o.toNat ≤ oa.toNat)
    (hdb : ob.toNat + i.toNat < o.toNat ∨ o.toNat ≤ ob.toNat)
    (hs6 : (m.arr64 (tierA POOL T6)).size ≤ 2 ^ 40) (hs8 : (m.arr64 (tierA POOL T8)).size ≤ 2 ^ 40)
    (hs10 : (m.arr64 (tierA POOL T10)).size ≤ 2 ^ 40)
    (hb8 : (T9 + i).toNat < (m.arr64 (tierA POOL T8)).size)
    (hb10 : (T11 + i).toNat < (m.arr64 (tierA POOL T10)).size)
    (hb6 : (T7 + i).toNat < (m.arr64 (tierA POOL T6)).size)
    (hoff : Off (vpool m) P0 o.toNat i.toNat)
    (ih : pv (vpool m) o.toNat i.toNat = bwv (BinOp.eval op) P0 oa.toNat ob.toNat i.toNat) :
    pv (vpool (m.set64 (tierA POOL T6) (T7 + i)
        (BinOp.eval op (m.arr64 (tierA POOL T8))[(T9 + i).toNat] (m.arr64 (tierA POOL T10))[(T11 + i).toNat])))
        o.toNat (i + 1).toNat = bwv (BinOp.eval op) P0 oa.toNat ob.toNat (i + 1).toNat := by
  subst h6 h7 h8 h9 h10 h11
  have hi1 : (i + 1).toNat = i.toNat + 1 := w_add i 1 (by simp; omega)
  have hvs := vpool_size m
  rw [ld_off m P0 oa i o (by omega) (by omega) hP0 hs8 hb8 hoff hda,
    ld_off m P0 ob i o (by omega) (by omega) hP0 hs10 hb10 hoff hdb,
    st_win m o i _ (by omega) (by omega) hs6 hb6, hi1,
    pv_set_succ (vpool m) o.toNat i.toNat (i.toNat + 1) (o.toNat + i.toNat) _ rfl rfl (by omega), ih]
  simp only [bwv, Array.getElem?_eq_getElem (by omega : oa.toNat + i.toNat < P0.size),
    Array.getElem?_eq_getElem (by omega : ob.toNat + i.toNat < P0.size), Option.getD_some]

/-- One step of `copy_n`'s loop, in the shape of its verification condition. -/
theorem copyn_step_goal (m : Mem) (P0 : Array Word) (o oa i T5 T6 T7 T8 : Word)
    (h5 : T5 = o >>> 40) (h6 : T6 = o &&& 1099511627775)
    (h7 : T7 = oa >>> 40) (h8 : T8 = oa &&& 1099511627775)
    (hP0 : P0.size = 2 ^ 41) (ho : o.toNat + i.toNat < 2 ^ 41) (hoa : oa.toNat + i.toNat < 2 ^ 41)
    (hda : oa.toNat + i.toNat < o.toNat ∨ o.toNat ≤ oa.toNat)
    (hs5 : (m.arr64 (tierA POOL T5)).size ≤ 2 ^ 40) (hs7 : (m.arr64 (tierA POOL T7)).size ≤ 2 ^ 40)
    (hb7 : (T8 + i).toNat < (m.arr64 (tierA POOL T7)).size)
    (hb5 : (T6 + i).toNat < (m.arr64 (tierA POOL T5)).size)
    (hoff : Off (vpool m) P0 o.toNat i.toNat)
    (ih : pv (vpool m) o.toNat i.toNat = pv P0 oa.toNat i.toNat) :
    pv (vpool (m.set64 (tierA POOL T5) (T6 + i) (m.arr64 (tierA POOL T7))[(T8 + i).toNat]))
        o.toNat (i + 1).toNat = pv P0 oa.toNat (i + 1).toNat := by
  subst h5 h6 h7 h8
  have hi1 : (i + 1).toNat = i.toNat + 1 := w_add i 1 (by simp; omega)
  have hvs := vpool_size m
  rw [ld_off m P0 oa i o (by omega) (by omega) hP0 hs7 hb7 hoff hda,
    st_win m o i _ (by omega) (by omega) hs5 hb5, hi1,
    pv_set_succ (vpool m) o.toNat i.toNat (i.toNat + 1) (o.toNat + i.toNat) _ rfl rfl (by omega), ih,
    pv_succ P0 oa.toNat i.toNat (i.toNat + 1) (oa.toNat + i.toNat) rfl rfl (by omega)]

section bitn
variable (p : Prog) (P0 : Array Word) (C : Nat)

/-- A bitwise leaf's loop: locals `(o, oa, ob, n, i, x, pt, pb, ta, qa, tb, qb)`. -/
def BitNInv (op : BinOp) (P0 : Array Word) (C : Nat) (s : St) : Prop :=
  C < 2 ^ 64 ∧ P0.size = 2 ^ 41 ∧ pcap s.mem = C ∧
  (s.loc 0).toNat + (s.loc 3).toNat ≤ C ∧ (s.loc 1).toNat + (s.loc 3).toNat ≤ C ∧
  (s.loc 2).toNat + (s.loc 3).toNat ≤ C ∧
  ((s.loc 1).toNat + (s.loc 3).toNat ≤ (s.loc 0).toNat ∨ (s.loc 0).toNat ≤ (s.loc 1).toNat) ∧
  ((s.loc 2).toNat + (s.loc 3).toNat ≤ (s.loc 0).toNat ∨ (s.loc 0).toNat ≤ (s.loc 2).toNat) ∧
  s.loc 6 = s.loc 0 >>> 40 ∧ s.loc 7 = s.loc 0 &&& 1099511627775 ∧
  s.loc 8 = s.loc 1 >>> 40 ∧ s.loc 9 = s.loc 1 &&& 1099511627775 ∧
  s.loc 10 = s.loc 2 >>> 40 ∧ s.loc 11 = s.loc 2 &&& 1099511627775 ∧
  (s.mem.arr64 (tierA POOL (s.loc 6))).size ≤ 2 ^ 40 ∧
  (s.mem.arr64 (tierA POOL (s.loc 8))).size ≤ 2 ^ 40 ∧
  (s.mem.arr64 (tierA POOL (s.loc 10))).size ≤ 2 ^ 40 ∧
  (s.loc 4).toNat ≤ (s.loc 3).toNat ∧
  Off (vpool s.mem) P0 (s.loc 0).toNat (s.loc 4).toNat ∧
  pv (vpool s.mem) (s.loc 0).toNat (s.loc 4).toNat = bwv (BinOp.eval op) P0 (s.loc 1).toNat (s.loc 2).toNat (s.loc 4).toNat

def BitNPost (op : BinOp) (P0 : Array Word) (C : Nat) (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ PFrame s₀.mem s'.mem ∧ pcap s'.mem = C ∧
  s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧
  Off (vpool s'.mem) P0 (s₀.loc 0).toNat (s₀.loc 3).toNat ∧
  pv (vpool s'.mem) (s₀.loc 0).toNat (s₀.loc 3).toNat = bwv (BinOp.eval op) P0 (s₀.loc 1).toNat (s₀.loc 2).toNat (s₀.loc 3).toNat

theorem bitNLoop_spec (op : BinOp) (n : Nat) (s₀ : St) (h : BitNInv op P0 C s₀) :
    ⦃fun s => s = s₀⦄ exec p n (bitNLoop op) ⦃fun r s' => BitNPost op P0 C s₀ r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [BitNInv, BitNPost] at h ⊢
    rw [exec, step_while (w := bitNLoop op) rfl]
    vcgen [step, evalE, evalC, setLoc, setLocs, ld64, st64, ih]
    all_goals clear ih
    all_goals (try simp only [BitNInv, BitNPost] at *)
    all_goals (try subst_vars)
    all_goals (try and_intros)
    all_goals (try dsimp only at *)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, Cmp.eval, BinOp.eval.eq_1, Mem.size64_set64,
      Nat.reduceEqDiff, reduceIte, decide_eq_true_eq] at *)
    all_goals first
      | (with_reducible apply bitn_step_goal <;> grind [pcap_eq])
      | grind (splits := 8) [arena_grind, lang_grind]

theorem bitNLoop_step_spec (op : BinOp) (n : Nat) (s₀ : St) (h : BitNInv op P0 C s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) (bitNLoop op) ⦃fun r s' => BitNPost op P0 C s₀ r s'; ⊤⦄ :=
  Triple.step_exec (bitNLoop_spec p P0 C op (n + 1) s₀ h)

/-- A bitwise leaf `f(o, oa, ob, k)`: `P[o, o + k) := a op b` limb by limb. -/
theorem bitN_spec (op : BinOp) (f : FnName) (hp : p.lookup f = some (bitNG op)) (n : Nat) (s₀ : St)
    (o oa ob k : Word)
    (hs : pcap s₀.mem < 2 ^ 64) (ho : o.toNat + k.toNat ≤ pcap s₀.mem)
    (ha : oa.toNat + k.toNat ≤ pcap s₀.mem) (hb : ob.toNat + k.toNat ≤ pcap s₀.mem)
    (hda : oa.toNat + k.toNat ≤ o.toNat ∨ o.toNat ≤ oa.toNat)
    (hdb : ob.toNat + k.toNat ≤ o.toNat ∨ o.toNat ≤ ob.toNat) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) f [o, oa, ob, k]
    ⦃fun _ s' => LocEq s' s₀ ∧ PFrame s₀.mem s'.mem ∧ pcap s'.mem = pcap s₀.mem ∧
      Off (vpool s'.mem) (vpool s₀.mem) o.toNat k.toNat ∧
      pv (vpool s'.mem) o.toNat k.toNat = bwv (BinOp.eval op) (vpool s₀.mem) oa.toNat ob.toNat k.toNat; ⊤⦄ := by
  have h1 := pcap_tier s₀.mem (o >>> 40) hs
  have h2 := pcap_tier s₀.mem (oa >>> 40) hs
  have h3 := pcap_tier s₀.mem (ob >>> 40) hs
  rw [invoke_eq _ hp]
  simp only [callFn, bitNG]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      bitNLoop_step_spec p (vpool s₀.mem) (pcap s₀.mem) op n]
    all_goals (try simp only [BitNInv, BitNPost] at *)
    all_goals (try subst_vars)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem,
      L.Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, BinOp.eval.eq_4, BinOp.eval.eq_8,
      reduceIte, Nat.reduceEqDiff, UInt64.toNat_zero] at *)
    all_goals (try and_intros)
    all_goals grind (splits := 8) [arena_grind, lang_grind, LocEq, bwv]

end bitn

section copyn
variable (p : Prog) (P0 : Array Word) (C : Nat)

/-- `copy_n`'s loop: locals `(o, oa, n, i, x, pt, pb, ta, qa)`. -/
def CopyNInv (P0 : Array Word) (C : Nat) (s : St) : Prop :=
  C < 2 ^ 64 ∧ P0.size = 2 ^ 41 ∧ pcap s.mem = C ∧
  (s.loc 0).toNat + (s.loc 2).toNat ≤ C ∧ (s.loc 1).toNat + (s.loc 2).toNat ≤ C ∧
  ((s.loc 1).toNat + (s.loc 2).toNat ≤ (s.loc 0).toNat ∨ (s.loc 0).toNat ≤ (s.loc 1).toNat) ∧
  s.loc 5 = s.loc 0 >>> 40 ∧ s.loc 6 = s.loc 0 &&& 1099511627775 ∧
  s.loc 7 = s.loc 1 >>> 40 ∧ s.loc 8 = s.loc 1 &&& 1099511627775 ∧
  (s.mem.arr64 (tierA POOL (s.loc 5))).size ≤ 2 ^ 40 ∧
  (s.mem.arr64 (tierA POOL (s.loc 7))).size ≤ 2 ^ 40 ∧
  (s.loc 3).toNat ≤ (s.loc 2).toNat ∧
  Off (vpool s.mem) P0 (s.loc 0).toNat (s.loc 3).toNat ∧
  pv (vpool s.mem) (s.loc 0).toNat (s.loc 3).toNat = pv P0 (s.loc 1).toNat (s.loc 3).toNat

def CopyNPost (P0 : Array Word) (C : Nat) (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ PFrame s₀.mem s'.mem ∧ pcap s'.mem = C ∧
  s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧
  Off (vpool s'.mem) P0 (s₀.loc 0).toNat (s₀.loc 2).toNat ∧
  pv (vpool s'.mem) (s₀.loc 0).toNat (s₀.loc 2).toNat = pv P0 (s₀.loc 1).toNat (s₀.loc 2).toNat

theorem copyNLoop_spec (n : Nat) (s₀ : St) (h : CopyNInv P0 C s₀) :
    ⦃fun s => s = s₀⦄ exec p n copyNLoop ⦃fun r s' => CopyNPost P0 C s₀ r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [CopyNInv, CopyNPost] at h ⊢
    rw [exec, step_while (w := copyNLoop) rfl]
    vcgen [step, evalE, evalC, setLoc, setLocs, ld64, st64, ih]
    all_goals clear ih
    all_goals (try simp only [CopyNInv, CopyNPost] at *)
    all_goals (try subst_vars)
    all_goals (try and_intros)
    all_goals (try dsimp only at *)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, Cmp.eval, BinOp.eval, Mem.size64_set64,
      Nat.reduceEqDiff, reduceIte, decide_eq_true_eq] at *)
    all_goals first
      | (with_reducible apply copyn_step_goal <;> grind [pcap_eq])
      | grind (splits := 8) [arena_grind, lang_grind]

theorem copyNLoop_step_spec (n : Nat) (s₀ : St) (h : CopyNInv P0 C s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) copyNLoop ⦃fun r s' => CopyNPost P0 C s₀ r s'; ⊤⦄ :=
  Triple.step_exec (copyNLoop_spec p P0 C (n + 1) s₀ h)

/-- `copy_n(o, oa, k)`: `P[o, o + k) := A[oa, oa + k)`. -/
theorem copyN_spec (hp : p.lookup "copy_n" = some copyN) (n : Nat) (s₀ : St) (o oa k : Word)
    (hs : pcap s₀.mem < 2 ^ 64) (ho : o.toNat + k.toNat ≤ pcap s₀.mem)
    (ha : oa.toNat + k.toNat ≤ pcap s₀.mem)
    (hda : oa.toNat + k.toNat ≤ o.toNat ∨ o.toNat ≤ oa.toNat) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "copy_n" [o, oa, k]
    ⦃fun _ s' => LocEq s' s₀ ∧ PFrame s₀.mem s'.mem ∧ pcap s'.mem = pcap s₀.mem ∧
      Off (vpool s'.mem) (vpool s₀.mem) o.toNat k.toNat ∧
      pv (vpool s'.mem) o.toNat k.toNat = pv (vpool s₀.mem) oa.toNat k.toNat; ⊤⦄ := by
  have h1 := pcap_tier s₀.mem (o >>> 40) hs
  have h2 := pcap_tier s₀.mem (oa >>> 40) hs
  rw [invoke_eq _ hp]
  simp only [callFn, copyN]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      copyNLoop_step_spec p (vpool s₀.mem) (pcap s₀.mem) n]
    all_goals (try simp only [CopyNInv, CopyNPost] at *)
    all_goals (try subst_vars)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem,
      L.Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, BinOp.eval,
      reduceIte, Nat.reduceEqDiff, UInt64.toNat_zero] at *)
    all_goals (try and_intros)
    all_goals grind (splits := 8) [arena_grind, lang_grind, LocEq]

end copyn

end L.Arena
