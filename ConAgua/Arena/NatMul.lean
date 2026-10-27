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
def macHi : FunDecl := lfn (x, y, t, c) locals (lo, hi) {
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

/-! ## `nat_mul(oa, la, ob, lb)`: append `a * b` to the pool, return its length -/

def zeroLoop : Stmt := lblk (oa, la, ob, lb, top, n, i, j, c, x, y, t, pt, pb) {
  while i < la {
    POOL⟨pt⟩[pb + i] := 0;
    i += 1
  }
}

/-- One row: add `a * y`, shifted by `j` limbs, into the result (con-ron's `mul_u64_from`). -/
def colLoop : Stmt := lblk (oa, la, ob, lb, top, n, i, j, c, x, y, t, pt, pb) {
  while i < la {
    x := POOL⦃oa + i⦄;
    t := POOL⟨pt⟩[pb + (i + j)];
    POOL⟨pt⟩[pb + (i + j)] := x * y + t + c;
    c := call mac_hi(x, y, t, c);
    i += 1
  }
}

/-- All rows (con-ron's `mul_from`). -/
def rowLoop : Stmt := lblk (oa, la, ob, lb, top, n, i, j, c, x, y, t, pt, pb) {
  while j < lb {
    y := POOL⦃ob + j⦄;
    c := 0;
    i := 0;
    ⟪colLoop⟫;
    POOL⟨pt⟩[pb + (la + j)] := c;
    j += 1
  }
}

/-- con-ron: ConRon/Arena/Core.lean:994-1035 ConRon.Arena.natOpResult -/
@[l_impl ConRon.Arena.natOpResult]
def natMul : FunDecl := lfn (oa, la, ob, lb) locals (top, n, i, j, c, x, y, t, pt, pb) {
  top := CTL.u64[0];
  pt := ⦃top⦄.tier;
  pb := top - ⦃top⦄.base;
  n := la + lb;
  if len(POOL⟨pt⟩) - pb < n { abort };
  ⟪zeroLoop⟫;
  ⟪rowLoop⟫;
  n := call nat_trim(top, n);
  CTL.u64[0] := top + n;
  return n
}

/-- The pool functions with `nat_mul`. -/
def natMulProg : Prog := natProg ++ [("mac_hi", macHi), ("nat_mul", natMul)]

/- `(2^64 - 1)^2 = 2^128 - 2^65 + 1`: limbs `[1, 2^64 - 2]`. -/
#guard (run natMulProg 1000 "nat_mul" [0, 1, 0, 1]
  { words := #[#[0xFFFFFFFFFFFFFFFF, 0, 0, 0], #[1]] }).toOption.map (fun (r, m) => (r, m.words)) ==
  some ([2], #[#[0xFFFFFFFFFFFFFFFF, 1, 0xFFFFFFFFFFFFFFFE, 0], #[3]])

/- `(2^64 + 3) * 5 = 5 * 2^64 + 15`, and `0 * a = 0` (length 0). -/
#guard (run natMulProg 1000 "nat_mul" [0, 2, 2, 1]
  { words := #[#[3, 1, 5, 0, 0, 0], #[3]] }).toOption.map (fun (r, m) => (r, m.words)) ==
  some ([2], #[#[3, 1, 5, 15, 5, 0], #[5]])
#guard (run natMulProg 1000 "nat_mul" [0, 2, 2, 0]
  { words := #[#[3, 1, 0, 0], #[2]] }).toOption.map (·.1) == some [0]

section mul
variable (p : Prog) (hph : p.lookup "mac_hi" = some macHi)
  (Pg : Array Word) (C : Nat)

/-- What all three loops of `nat_mul` keep: the pool agrees with the entry pool `Pg` below
`top`, the operands lie below `top`, and the `la + lb` result limbs fit above it. -/
def MulBase (Pg : Array Word) (C : Nat) (s : St) : Prop :=
  C < 2 ^ 63 ∧ Pg.size = 2 ^ 41 ∧ pcap s.mem = C ∧
  Agree (vpool s.mem) Pg (s.loc 4).toNat ∧
  (s.loc 5).toNat = (s.loc 1).toNat + (s.loc 3).toNat ∧
  (s.loc 4).toNat + (s.loc 5).toNat ≤ C ∧
  s.loc 12 = s.loc 4 >>> 40 ∧ s.loc 13 = s.loc 4 - ((s.loc 4 >>> 40) <<< 40) ∧
  (s.loc 13).toNat + (s.loc 5).toNat ≤ (s.mem.arr64 (tierA POOL (s.loc 12))).size ∧
  (s.mem.arr64 (tierA POOL (s.loc 12))).size ≤ 2 ^ 40 ∧ (s.loc 12).toNat ≤ 1 ∧ (s.loc 4).toNat < 2 ^ 41 ∧
  (s.loc 0).toNat + (s.loc 1).toNat ≤ (s.loc 4).toNat ∧
  (s.loc 2).toNat + (s.loc 3).toNat ≤ (s.loc 4).toNat

def ZeroInv (Pg : Array Word) (C : Nat) (s : St) : Prop :=
  MulBase Pg C s ∧ (s.loc 6).toNat ≤ (s.loc 1).toNat ∧
  pv (vpool s.mem) (s.loc 4).toNat (s.loc 6).toNat = 0

/-- Row `j`, column `i`: the result so far plus the carry is `a * b[0..j) + a[0..i) * y`, with
`y = b[j]`. -/
def ColInv (Pg : Array Word) (C : Nat) (s : St) : Prop :=
  MulBase Pg C s ∧ (s.loc 6).toNat ≤ (s.loc 1).toNat ∧ (s.loc 7).toNat < (s.loc 3).toNat ∧
  (s.loc 10).toNat = lv Pg (s.loc 2).toNat (s.loc 3).toNat (s.loc 7).toNat ∧
  pv (vpool s.mem) (s.loc 4).toNat ((s.loc 1).toNat + (s.loc 7).toNat) +
      (s.loc 8).toNat * (wt (s.loc 6).toNat * wt (s.loc 7).toNat) =
    pv Pg (s.loc 0).toNat (s.loc 1).toNat * pv Pg (s.loc 2).toNat (s.loc 7).toNat +
      pv Pg (s.loc 0).toNat (s.loc 6).toNat * (s.loc 10).toNat * wt (s.loc 7).toNat

/-- Before row `j`: the result so far is `a * b[0..j)`. -/
def RowInv (Pg : Array Word) (C : Nat) (s : St) : Prop :=
  MulBase Pg C s ∧ (s.loc 7).toNat ≤ (s.loc 3).toNat ∧
  pv (vpool s.mem) (s.loc 4).toNat ((s.loc 1).toNat + (s.loc 7).toNat) =
    pv Pg (s.loc 0).toNat (s.loc 1).toNat * pv Pg (s.loc 2).toNat (s.loc 7).toNat

set_option maxHeartbeats 2000000 in
theorem zeroLoop_spec (n : Nat) (s₀ : St) (h : ZeroInv Pg C s₀) :
    ⦃fun s => s = s₀⦄
    exec p n zeroLoop
    ⦃fun r s' => r = .normal ∧ PFrame s₀.mem s'.mem ∧
      pcap s'.mem = C ∧ Agree (vpool s'.mem) Pg (s₀.loc 4).toNat ∧
      s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧
      s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧ s'.loc 12 = s₀.loc 12 ∧ s'.loc 13 = s₀.loc 13 ∧ s'.loc 7 = s₀.loc 7 ∧
      pv (vpool s'.mem) (s₀.loc 4).toNat (s₀.loc 1).toNat = 0; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [ZeroInv, MulBase] at h
    rw [exec, step_while (w := zeroLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, setLoc, setLocs, st64, ih] <;> finish [ZeroInv, MulBase]

/-- One multiply-accumulate step of the column loop, in the shape of `colLoop_spec`'s arithmetic
goal (applied, not E-matched: `grind` alone takes minutes here). -/
theorem mul_step_goal (m : Mem) (Pg : Array Word) (T T12 T13 o L ob i j y c r : Word)
    (h12 : T12 = T >>> 40) (h13 : T13 = T - ((T >>> 40) <<< 40))
    (hT : T.toNat < 2 ^ 41) (hs : (m.arr64 (tierA POOL T12)).size ≤ 2 ^ 40)
    (hst : (T13 + (i + j)).toNat < (m.arr64 (tierA POOL T12)).size)
    (hk : T13.toNat + i.toNat + j.toNat < 2 ^ 40)
    (hag : Agree (vpool m) Pg T.toNat) (hoi : o.toNat + i.toNat < T.toNat)
    (hil : i.toNat < L.toNat) (hwi : T.toNat + i.toNat + j.toNat < 2 ^ 41)
    (hPg : Pg.size = 2 ^ 41)
    (hld : ((o + i) &&& 1099511627775).toNat < (m.arr64 (tierA POOL ((o + i) >>> 40))).size)
    (hr : r.toNat = macHiN (m.arr64 (tierA POOL ((o + i) >>> 40)))[((o + i) &&& 1099511627775).toNat]
      y (m.arr64 (tierA POOL T12))[(T13 + (i + j)).toNat] c)
    (ih : pv (vpool m) T.toNat (L.toNat + j.toNat) + c.toNat * (wt i.toNat * wt j.toNat) =
      pv Pg o.toNat L.toNat * pv Pg ob.toNat j.toNat + pv Pg o.toNat i.toNat * y.toNat * wt j.toNat) :
    pv (vpool (m.set64 (tierA POOL T12) (T13 + (i + j))
        ((m.arr64 (tierA POOL ((o + i) >>> 40)))[((o + i) &&& 1099511627775).toNat] * y +
          (m.arr64 (tierA POOL T12))[(T13 + (i + j)).toNat] + c)))
        T.toNat (L.toNat + j.toNat) +
      r.toNat * (wt (i + 1).toNat * wt j.toNat) =
    pv Pg o.toNat L.toNat * pv Pg ob.toNat j.toNat + pv Pg o.toNat (i + 1).toNat * y.toNat * wt j.toNat := by
  subst h12 h13
  have hij : (i + j).toNat = i.toNat + j.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hi' : (i + 1).toNat = i.toNat + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_one]; exact Nat.mod_eq_of_lt (by omega)
  have hoi' : (o + i).toNat = o.toNat + i.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hTij : (T + (i + j)).toNat = T.toNat + (i.toNat + j.toNat) := by
    rw [UInt64.toNat_add, hij]; exact Nat.mod_eq_of_lt (by omega)
  have hvs := vpool_size m
  have hk' : (T - ((T >>> 40) <<< 40)).toNat + (i + j).toNat < 2 ^ 40 := by rw [hij]; omega
  have ex : (m.arr64 (tierA POOL ((o + i) >>> 40)))[((o + i) &&& 1099511627775).toNat] =
      Pg[o.toNat + i.toNat] := by
    rw [vpool_ld m (o + i) hld (by omega)]
    simp only [hoi']
    exact Agree.get _ _ _ _ hag hoi (by omega) (by omega)
  have et : (m.arr64 (tierA POOL (T >>> 40)))[(T - ((T >>> 40) <<< 40) + (i + j)).toNat] =
      (vpool m)[T.toNat + (i.toNat + j.toNat)] := by
    rw [vpool_ldrel m T (i + j) hT hst hs hk' (by omega)]
    simp only [hTij]
  rw [ex, et] at hr
  rw [ex, et, vpool_strel m T (i + j) _ hT hst hs hk', hTij, hi']
  have hmid := pv_set_mid (vpool m) T.toNat (L.toNat + j.toNat) i.toNat j.toNat
    (T.toNat + (i.toNat + j.toNat))
    (Pg[o.toNat + i.toNat] * y + (vpool m)[T.toNat + (i.toNat + j.toNat)] + c) (by omega) (by omega)
    (by omega)
  have hsp := mac_split Pg[o.toNat + i.toNat] y (vpool m)[T.toNat + (i.toNat + j.toNat)] c
  rw [← hr] at hsp
  rw [pv_succ Pg o.toNat i.toNat (i.toNat + 1) (o.toNat + i.toNat) rfl rfl (by omega),
    wt_succ i.toNat (i.toNat + 1) rfl]
  generalize pv (vpool m) T.toNat (L.toNat + j.toNat) = A at *
  generalize pv ((vpool m).set! (T.toNat + (i.toNat + j.toNat))
    (Pg[o.toNat + i.toNat] * y + (vpool m)[T.toNat + (i.toNat + j.toNat)] + c)) T.toNat
    (L.toNat + j.toNat) = A' at *
  generalize pv Pg o.toNat i.toNat = B at *
  generalize wt i.toNat = I at *
  generalize wt j.toNat = J at *
  grind

-- the multiply-accumulate step (see the proof) needs more than the default budget
set_option maxHeartbeats 2000000 in
include hph in
theorem colLoop_spec (n : Nat) (s₀ : St) (h : ColInv Pg C s₀) :
    ⦃fun s => s = s₀⦄
    exec p n colLoop
    ⦃fun r s' => r = .normal ∧ PFrame s₀.mem s'.mem ∧
      pcap s'.mem = C ∧ Agree (vpool s'.mem) Pg (s₀.loc 4).toNat ∧
      s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧
      s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧ s'.loc 12 = s₀.loc 12 ∧ s'.loc 13 = s₀.loc 13 ∧ s'.loc 7 = s₀.loc 7 ∧ s'.loc 10 = s₀.loc 10 ∧
      pv (vpool s'.mem) (s₀.loc 4).toNat ((s₀.loc 1).toNat + (s₀.loc 7).toNat) +
          (s'.loc 8).toNat * (wt (s₀.loc 1).toNat * wt (s₀.loc 7).toNat) =
        pv Pg (s₀.loc 0).toNat (s₀.loc 1).toNat * pv Pg (s₀.loc 2).toNat (s₀.loc 7).toNat +
          pv Pg (s₀.loc 0).toNat (s₀.loc 1).toNat * (s₀.loc 10).toNat * wt (s₀.loc 7).toNat; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [ColInv, MulBase] at h
    rw [exec, step_while (w := colLoop) rfl]
    -- Not the `sym => vcgen <;> finish` form: the column step is one multiply-accumulate, whose
    -- verification condition `grind` proves only with a raised split budget and only without
    -- the induction hypothesis (a `∀`-triple) and the unevaluated frame in its context. So:
    -- drop `ih` after `vcgen`, evaluate the frame with `simp`, split the invariant into its
    -- conjuncts, and give `grind` 40 case splits (DESIGN.md, arena findings).
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih, macHi_spec p hph n]
    all_goals clear ih
    all_goals (try simp only [ColInv, MulBase] at *)
    all_goals (try subst_vars)
    all_goals (try simp only [St.setLoc, St.setLocs, BinOp.eval, Cmp.eval, reduceIte, Nat.reduceEqDiff] at *)
    all_goals (try and_intros)
    all_goals first
      | (with_reducible apply mul_step_goal <;> grind)
      | grind (splits := 40) [arena_grind, lang_grind]

include hph in
theorem colLoop_step_spec (n : Nat) (s₀ : St) (h : ColInv Pg C s₀) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) colLoop
    ⦃fun r s' => r = .normal ∧ PFrame s₀.mem s'.mem ∧
      pcap s'.mem = C ∧ Agree (vpool s'.mem) Pg (s₀.loc 4).toNat ∧
      s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧
      s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧ s'.loc 12 = s₀.loc 12 ∧ s'.loc 13 = s₀.loc 13 ∧ s'.loc 7 = s₀.loc 7 ∧ s'.loc 10 = s₀.loc 10 ∧
      pv (vpool s'.mem) (s₀.loc 4).toNat ((s₀.loc 1).toNat + (s₀.loc 7).toNat) +
          (s'.loc 8).toNat * (wt (s₀.loc 1).toNat * wt (s₀.loc 7).toNat) =
        pv Pg (s₀.loc 0).toNat (s₀.loc 1).toNat * pv Pg (s₀.loc 2).toNat (s₀.loc 7).toNat +
          pv Pg (s₀.loc 0).toNat (s₀.loc 1).toNat * (s₀.loc 10).toNat * wt (s₀.loc 7).toNat; ⊤⦄ :=
  Triple.step_exec (colLoop_spec p hph Pg C (n + 1) s₀ h)

set_option maxHeartbeats 2000000 in
include hph in
theorem rowLoop_spec (n : Nat) (s₀ : St) (h : RowInv Pg C s₀) :
    ⦃fun s => s = s₀⦄
    exec p n rowLoop
    ⦃fun r s' => r = .normal ∧ PFrame s₀.mem s'.mem ∧
      pcap s'.mem = C ∧ Agree (vpool s'.mem) Pg (s₀.loc 4).toNat ∧
      s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧ s'.loc 12 = s₀.loc 12 ∧ s'.loc 13 = s₀.loc 13 ∧
      pv (vpool s'.mem) (s₀.loc 4).toNat ((s₀.loc 1).toNat + (s₀.loc 3).toNat) =
        pv Pg (s₀.loc 0).toNat (s₀.loc 1).toNat * pv Pg (s₀.loc 2).toNat (s₀.loc 3).toNat; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [RowInv, MulBase] at h
    rw [exec, step_while (w := rowLoop) rfl]
    -- the recipe of `colLoop_spec`
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih,
      colLoop_step_spec p hph Pg C n]
    all_goals clear ih
    all_goals (try simp only [ColInv, RowInv, MulBase] at *)
    all_goals (try subst_vars)
    all_goals (try simp only [St.setLoc, BinOp.eval, Cmp.eval, reduceIte, Nat.reduceEqDiff] at *)
    all_goals (try and_intros)
    all_goals grind (splits := 40) [arena_grind, lang_grind]

include hph in
theorem rowLoop_step_spec (n : Nat) (s₀ : St) (h : RowInv Pg C s₀) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) rowLoop
    ⦃fun r s' => r = .normal ∧ PFrame s₀.mem s'.mem ∧
      pcap s'.mem = C ∧ Agree (vpool s'.mem) Pg (s₀.loc 4).toNat ∧
      s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧ s'.loc 12 = s₀.loc 12 ∧ s'.loc 13 = s₀.loc 13 ∧
      pv (vpool s'.mem) (s₀.loc 4).toNat ((s₀.loc 1).toNat + (s₀.loc 3).toNat) =
        pv Pg (s₀.loc 0).toNat (s₀.loc 1).toNat * pv Pg (s₀.loc 2).toNat (s₀.loc 3).toNat; ⊤⦄ :=
  Triple.step_exec (rowLoop_spec p hph Pg C (n + 1) s₀ h)

theorem zeroLoop_step_spec (n : Nat) (s₀ : St) (h : ZeroInv Pg C s₀) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) zeroLoop
    ⦃fun r s' => r = .normal ∧ PFrame s₀.mem s'.mem ∧
      pcap s'.mem = C ∧ Agree (vpool s'.mem) Pg (s₀.loc 4).toNat ∧
      s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧
      s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧ s'.loc 12 = s₀.loc 12 ∧ s'.loc 13 = s₀.loc 13 ∧ s'.loc 7 = s₀.loc 7 ∧
      pv (vpool s'.mem) (s₀.loc 4).toNat (s₀.loc 1).toNat = 0; ⊤⦄ :=
  Triple.step_exec (zeroLoop_spec p Pg C (n + 1) s₀ h)

end mul

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
  have hok₀ := hok
  have hsm := hok.small
  have h41 := hok.top41
  have hsz := hsm.tier (s₀.mem.top >>> 40)
  -- the `ptop0` disjunct of `PoolOK` is dead here, and `grind` splits on it in every goal
  obtain ⟨hok1, hok2, hok3, hok4, -, hok6⟩ := hok
  replace ha := ha.1
  replace hb := hb.1
  rw [invoke_eq _ hpn]
  simp only [callFn, natMul]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      zeroLoop_step_spec p (vpool s₀.mem) (pcap s₀.mem) n,
      rowLoop_step_spec p hph (vpool s₀.mem) (pcap s₀.mem) n, natTrim_spec p hpt n]
    all_goals (try simp only [ZeroInv, RowInv, MulBase] at *)
    all_goals (try subst_vars)
    -- `setLoc` lemmas, not unfolding; no `and_intros` (one `grind` per goal: 12 goals, not 42)
    all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Locals.init_nil,
      Locals.init_cons_zero, Locals.init_cons_succ, BinOp.eval, Cmp.eval, reduceIte,
      Nat.reduceEqDiff, UInt64.toNat_zero] at *)
    all_goals grind (splits := 40) [arena_grind, lang_grind]

end mulFn

end L.Arena
