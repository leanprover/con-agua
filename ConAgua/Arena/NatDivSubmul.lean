module

meta import ConAgua.L.Semantics
import ConAgua.Census.Attr
public import ConAgua.Arena.NatAdd
import ConAgua.Arena.NatDivFacts
import ConAgua.Arena.NatCmpFacts
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.NatGrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# The in-place passes of `nat_divmod` (lane `bigdiv`)

`div_add(r, n, ob, lb)` adds `b` (zero-extended) to the `n` limbs at `r` in place and returns the
carry: the add-back of Knuth's step D6 (con-ron's `pp = sub(&pp, b)` in `dm_correct`).

`div_submul(r, n, ob, q)` subtracts `q · b` from the `n + 1` limbs at `r` in place (`b` the `n`
limbs at `ob`, below `r`), one multiply-accumulate per limb with the product's high word from
`mulhi`, and returns the borrow out of the top limb: Knuth's step D4, con-ron's `mul_u64` and the
comparison of `dm_correct` (`ron/nat.rs`) fused into one pass.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## The in-place passes -/

/-- `div_add(r, n, ob, lb)`: `R := R + b` in place (`b` zero-extended); returns the carry. The
leaves `add_n` (over `b`'s limbs, at most `n`) and `add_1` (the carry through the rest), with the
output window the first operand's (`NatLeaf.lean`).
con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat` -/
@[no_expose] def divAdd : FunDecl := lfn (r, n, ob, lb) locals (m, c) {
  m := lb;
  if n < lb { m := n };
  c := call add_n(r, r, ob, m, 0);
  c := call add_1(r + m, r + m, n - m, c);
  return c
}


/-- The zero-extended prefix of a slice is the slice cut at the prefix's length. -/
theorem xv_min (p : Array Word) (o l k m : Nat) (hm : m = min l k) : xv p o l k = pv p o m := by
  subst hm
  rcases Nat.le_total l k with h | h
  · rw [xv_full (p := p) (o := o) l k h, Nat.min_eq_left h]
  · rw [Nat.min_eq_right h]
    induction k with
    | zero => rfl
    | succ k ih => simp only [xv, pv, ih (by omega), lv, show k < l by omega, ite_true]

/-- The value `div_add` leaves on arrays: `add_n` wrote the `m` limbs at `r` (`P1`), `add_1` the
`k - m` after them (`P2`), both in place. -/
theorem dadd_pv (P0 P1 P2 : Array Word) (r m k c1 c2 B : Nat) (hm : m ≤ k)
    (h1 : Off P1 P0 r m) (h2 : Off P2 P1 (r + m) (k - m))
    (e1 : pv P1 r m + c1 * wt m = pv P0 r m + B)
    (e2 : pv P2 (r + m) (k - m) + c2 * wt (k - m) = pv P1 (r + m) (k - m) + c1) :
    pv P2 r k + c2 * wt k = pv P0 r k + B := by
  have a2 := pv_append P2 r m (k - m)
  have a0 := pv_append P0 r m (k - m)
  rw [show m + (k - m) = k by omega] at a2 a0
  have d2 : pv P2 r m = pv P1 r m := Off.pv_disj P2 P1 (r + m) (k - m) r m h2 (Or.inl (by omega))
  have d1 : pv P1 (r + m) (k - m) = pv P0 (r + m) (k - m) :=
    Off.pv_disj P1 P0 r m (r + m) (k - m) h1 (Or.inr (by omega))
  have w := wt_add m (k - m) k (by omega)
  rw [a2, a0, d2, w]
  rw [d1] at e2
  generalize pv P1 r m = A at *
  generalize pv P2 (r + m) (k - m) = D at *
  generalize pv P0 (r + m) (k - m) = E at *
  generalize wt m = W at *
  generalize wt (k - m) = W' at *
  have : W * (D + c2 * W') = W * (E + c1) := by rw [e2]
  grind

/-- `dadd_pv` in the shape of `div_add`'s goal. -/
theorem dadd_goal (m0 m1 m2 : Mem) (r k ob lb m c1 v R c0 : Word) (hR : R = v) (hc0 : c0 = 0)
    (hm : m.toNat = min lb.toNat k.toNat) (hr41 : r.toNat + k.toNat < 2 ^ 41)
    (h1 : Off (vpool m1) (vpool m0) r.toNat m.toNat)
    (h2 : Off (vpool m2) (vpool m1) (r + m).toNat (k - m).toNat)
    (e1 : pv (vpool m1) r.toNat m.toNat + c1.toNat * wt m.toNat =
      pv (vpool m0) r.toNat m.toNat + pv (vpool m0) ob.toNat m.toNat + c0.toNat)
    (e2 : pv (vpool m2) (r + m).toNat (k - m).toNat + v.toNat * wt (k - m).toNat =
      pv (vpool m1) (r + m).toNat (k - m).toNat + c1.toNat) :
    pv (vpool m2) r.toNat k.toNat + R.toNat * wt k.toNat =
      pv (vpool m0) r.toNat k.toNat + xv (vpool m0) ob.toNat lb.toNat k.toNat := by
  subst R c0
  have hmk : m.toNat ≤ k.toNat := by omega
  have hrm : (r + m).toNat = r.toNat + m.toNat := by rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hkm : (k - m).toNat = k.toNat - m.toNat :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hmk)
  rw [hrm, hkm] at h2 e2
  rw [xv_min _ _ _ _ _ hm]
  simp only [UInt64.toNat_zero, Nat.add_zero] at e1
  exact dadd_pv _ _ _ r.toNat m.toNat k.toNat c1.toNat v.toNat _ hmk h1 h2 e1 e2

/-- `div_add` wrote only its window. -/
theorem dadd_off (m0 m1 m2 : Mem) (r k m : Word) (hmk : m.toNat ≤ k.toNat)
    (hr41 : r.toNat + k.toNat < 2 ^ 41)
    (h1 : Off (vpool m1) (vpool m0) r.toNat m.toNat)
    (h2 : Off (vpool m2) (vpool m1) (r + m).toNat (k - m).toNat) :
    Off (vpool m2) (vpool m0) r.toNat k.toNat := by
  have hrm : (r + m).toNat = r.toNat + m.toNat := by rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hkm : (k - m).toNat = k.toNat - m.toNat :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hmk)
  rw [hrm, hkm] at h2
  intro j hj
  exact (h2 j (by omega)).trans (h1 j (by omega))

section passFns
variable (p : Prog) (hpN : p.lookup "add_n" = some addN) (hp1 : p.lookup "add_1" = some add1)

include hpN hp1 in
theorem divAdd_spec (hp : p.lookup "div_add" = some divAdd) (n : Nat) (s₀ : St)
    (r k ob lb : Word) (hs : pcap s₀.mem < 2 ^ 64)
    (hr : r.toNat + k.toNat ≤ pcap s₀.mem) (hb : ob.toNat + lb.toNat ≤ r.toNat) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "div_add" [r, k, ob, lb]
    ⦃fun res s' => LocEq s' s₀ ∧ PFrame s₀.mem s'.mem ∧
      pcap s'.mem = pcap s₀.mem ∧ (res.headD 0).toNat ≤ 1 ∧
      Off (vpool s'.mem) (vpool s₀.mem) r.toNat k.toNat ∧
      pv (vpool s'.mem) r.toNat k.toNat + (res.headD 0).toNat * wt k.toNat =
        pv (vpool s₀.mem) r.toNat k.toNat + xv (vpool s₀.mem) ob.toNat lb.toNat k.toNat; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, divAdd]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      addN_spec p hpN n, add1_spec p hp1 n]
    all_goals (try simp only [LocEq] at *)
    all_goals (try simp_all only [St.setLoc_loc, L.St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
      L.Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, BinOp.eval, Cmp.eval,
      reduceIte, Nat.reduceEqDiff])
    all_goals split_clear_locs
    all_goals (try and_intros)
    all_goals first
      | (grind [arena_grind, lang_grind]; done)
      | (with_reducible apply dadd_goal
         case h2 => with_reducible assumption
         case h1 => with_reducible assumption
         case e1 => with_reducible assumption
         case e2 => with_reducible assumption
         all_goals first | rfl | grind [pcap_eq])
      | (with_reducible apply dadd_off
         case h2 => with_reducible assumption
         case h1 => with_reducible assumption
         all_goals grind [pcap_eq])

end passFns

def dsmLoop : Stmt := lblk (r, n, ob, q, i, c, x, y, lo, rt, rb) {
  for i < n {
    x := POOL⦃r + i⦄;
    y := POOL⦃ob + i⦄;
    lo := q * y + c;
    c := mulhi(q, y) + u64(lo < c);
    POOL⟨rt⟩[rb + i] := x - lo;
    c := c + u64(x < lo)
  }
}

/-- `div_submul(r, n, ob, q)`: `R := R - q · b` in place, `R` the `n + 1` limbs at `r` and `b`
the `n` limbs at `ob`; returns the borrow out of the top limb (con-ron's `mul_u64` and the
comparison `blt(t, p)` of `dm_correct`). -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def divSubmul : FunDecl := lfn (r, n, ob, q) locals (i, c, x, y, lo, rt, rb) {
  rt := ⦃r⦄.tier;
  rb := ⦃r⦄.idx;
  ⟪dsmLoop⟫;
  x := POOL⦃r + n⦄;
  POOL⟨rt⟩[rb + n] := x - c;
  return u64(x < c)
}

/-- One step of `div_submul`'s pass, in the shape of its verification condition: the two loads
read the entry pool (`R`'s limb is not yet written, `b` lies below `R`), the store extends the
written prefix, and `submul_step` is the digit equation. -/
theorem dsm_step_goal (m : Mem) (P0 : Array Word) (r ob q c i rt rb : Word)
    (hrt : rt = r >>> 40) (hrb : rb = r &&& 1099511627775)
    (hT : r.toNat < 2 ^ 41) (hs : (m.arr64 (tierA POOL (r >>> 40))).size ≤ 2 ^ 40)
    (hst : ((r &&& 1099511627775) + i).toNat < (m.arr64 (tierA POOL (r >>> 40))).size)
    (hk : (r &&& 1099511627775).toNat + i.toNat < 2 ^ 40)
    (hlx : ((r + i) &&& 1099511627775).toNat < (m.arr64 (tierA POOL ((r + i) >>> 40))).size)
    (hly : ((ob + i) &&& 1099511627775).toNat < (m.arr64 (tierA POOL ((ob + i) >>> 40))).size)
    (hri : r.toNat + i.toNat < 2 ^ 41) (hob : ob.toNat + i.toNat < r.toNat)
    (hP0 : P0.size = 2 ^ 41) (hoff : Off (vpool m) P0 r.toNat i.toNat)
    (ih : pv (vpool m) r.toNat i.toNat + q.toNat * pv P0 ob.toNat i.toNat =
      pv P0 r.toNat i.toNat + c.toNat * wt i.toNat) :
    pv (vpool (m.set64 (tierA POOL rt) (rb + i)
        ((m.arr64 (tierA POOL ((r + i) >>> 40)))[((r + i) &&& 1099511627775).toNat] -
          (q * (m.arr64 (tierA POOL ((ob + i) >>> 40)))[((ob + i) &&& 1099511627775).toNat] + c))))
        r.toNat (i + 1).toNat +
      q.toNat * pv P0 ob.toNat (i + 1).toNat =
    pv P0 r.toNat (i + 1).toNat +
      (UInt64.ofNat (q.toNat *
          (m.arr64 (tierA POOL ((ob + i) >>> 40)))[((ob + i) &&& 1099511627775).toNat].toNat /
            2 ^ 64) +
        (if q * (m.arr64 (tierA POOL ((ob + i) >>> 40)))[((ob + i) &&& 1099511627775).toNat] + c <
            c then 1 else 0) +
        (if (m.arr64 (tierA POOL ((r + i) >>> 40)))[((r + i) &&& 1099511627775).toNat] <
            q * (m.arr64 (tierA POOL ((ob + i) >>> 40)))[((ob + i) &&& 1099511627775).toNat] + c
          then 1 else 0)).toNat * wt (i + 1).toNat := by
  subst hrt hrb
  have hvs := vpool_size m
  have hi1 : (i + 1).toNat = i.toNat + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_one]; exact Nat.mod_eq_of_lt (by omega)
  have hri' : (r + i).toNat = r.toNat + i.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hobi : (ob + i).toNat = ob.toNat + i.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have ex : (m.arr64 (tierA POOL ((r + i) >>> 40)))[((r + i) &&& 1099511627775).toNat] =
      P0[r.toNat + i.toNat] := by
    rw [vpool_ld m (r + i) hlx (by omega)]
    simp only [hri']
    exact Off.get _ _ _ _ _ hoff (by omega) (by omega) (by omega)
  have ey : (m.arr64 (tierA POOL ((ob + i) >>> 40)))[((ob + i) &&& 1099511627775).toNat] =
      P0[ob.toNat + i.toNat] := by
    rw [vpool_ld m (ob + i) hly (by omega)]
    simp only [hobi]
    have := hoff (ob.toNat + i.toNat) (Or.inl hob)
    simp only [Array.getElem?_eq_getElem (by omega : ob.toNat + i.toNat < (vpool m).size),
      Array.getElem?_eq_getElem (by omega : ob.toNat + i.toNat < P0.size), Option.some.injEq] at this
    exact this
  rw [ex, ey, vpool_stidx m r i _ hT hst hs hk, hri', hi1,
    pv_set_succ (vpool m) r.toNat i.toNat (i.toNat + 1) (r.toNat + i.toNat) _ rfl rfl (by omega),
    pv_succ P0 ob.toNat i.toNat (i.toNat + 1) (ob.toNat + i.toNat) rfl rfl (by omega),
    pv_succ P0 r.toNat i.toNat (i.toNat + 1) (r.toNat + i.toNat) rfl rfl (by omega),
    wt_succ i.toNat (i.toNat + 1) rfl]
  have hsub := submul_step P0[r.toNat + i.toNat] P0[ob.toNat + i.toNat] q c
  generalize P0[r.toNat + i.toNat] = X at *
  generalize P0[ob.toNat + i.toNat] = Y at *
  generalize (UInt64.ofNat (q.toNat * Y.toNat / 2 ^ 64) + (if q * Y + c < c then 1 else 0) +
    (if X < q * Y + c then 1 else 0)) = c' at *
  generalize pv (vpool m) r.toNat i.toNat = A at *
  generalize pv P0 ob.toNat i.toNat = Bv at *
  generalize pv P0 r.toNat i.toNat = Cv at *
  generalize wt i.toNat = W at *
  generalize (X - (q * Y + c)).toNat = e at *
  have hW := congrArg (· * W) hsub
  clear hsub hT hs hst hk hlx hly hri hob hP0 hoff hvs hi1 hri' hobi ex ey
  generalize q.toNat = Q at *
  generalize c.toNat = C at *
  generalize X.toNat = Xn at *
  generalize Y.toNat = Yn at *
  generalize c'.toNat = Cn at *
  grind

/-- The top limb of `div_submul`: the carry left by the pass is subtracted from it, and the
borrow out is the sign of the result. -/
theorem dsm_top_goal (m : Mem) (P : Array Word) (r ob q c k rt rb r0 k0 : Word)
    (hr0 : r = r0) (hk0 : k = k0) (hrt : rt = r >>> 40) (hrb : rb = r &&& 1099511627775)
    (hT : r.toNat < 2 ^ 41) (hs : (m.arr64 (tierA POOL (r >>> 40))).size ≤ 2 ^ 40)
    (hst : ((r &&& 1099511627775) + k).toNat < (m.arr64 (tierA POOL (r >>> 40))).size)
    (hk : (r &&& 1099511627775).toNat + k.toNat < 2 ^ 40)
    (hlx : ((r0 + k0) &&& 1099511627775).toNat < (m.arr64 (tierA POOL ((r0 + k0) >>> 40))).size)
    (hrk : r.toNat + k.toNat < 2 ^ 41) (hP : P.size = 2 ^ 41) (hoff : Off (vpool m) P r.toNat k.toNat)
    (ih : pv (vpool m) r.toNat k.toNat + q.toNat * pv P ob.toNat k.toNat =
      pv P r.toNat k.toNat + c.toNat * wt k.toNat) :
    pv (vpool (m.set64 (tierA POOL rt) (rb + k0)
        ((m.arr64 (tierA POOL ((r0 + k0) >>> 40)))[((r0 + k0) &&& 1099511627775).toNat] - c)))
        r.toNat (k.toNat + 1) +
      q.toNat * pv P ob.toNat k.toNat =
    pv P r.toNat (k.toNat + 1) +
      (if (m.arr64 (tierA POOL ((r0 + k0) >>> 40)))[((r0 + k0) &&& 1099511627775).toNat] < c
        then (1 : Word) else 0).toNat * wt (k.toNat + 1) := by
  subst hrt hrb hr0 hk0
  have hvs := vpool_size m
  have hrk' : (r + k).toNat = r.toNat + k.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have ex : (m.arr64 (tierA POOL ((r + k) >>> 40)))[((r + k) &&& 1099511627775).toNat] =
      P[r.toNat + k.toNat] := by
    rw [vpool_ld m (r + k) hlx (by omega)]
    simp only [hrk']
    exact Off.get _ _ _ _ _ hoff (by omega) (by omega) (by omega)
  rw [ex, vpool_stidx m r k _ hT hst hs hk, hrk',
    pv_set_succ (vpool m) r.toNat k.toNat (k.toNat + 1) (r.toNat + k.toNat) _ rfl rfl (by omega),
    pv_succ P r.toNat k.toNat (k.toNat + 1) (r.toNat + k.toNat) rfl rfl (by omega),
    wt_succ k.toNat (k.toNat + 1) rfl]
  have hd : (P[r.toNat + k.toNat] - c).toNat + c.toNat =
      P[r.toNat + k.toNat].toNat + (if P[r.toNat + k.toNat] < c then (1 : Word) else 0).toNat * 2 ^ 64 := by
    have hlt : (P[r.toNat + k.toNat] < c) ↔ P[r.toNat + k.toNat].toNat < c.toNat :=
      UInt64.lt_iff_toNat_lt
    have := c.toNat_lt; have := P[r.toNat + k.toNat].toNat_lt
    by_cases h : P[r.toNat + k.toNat] < c <;> simp only [h, ite_true, ite_false] <;>
      simp only [hlt] at h <;> rw [UInt64.toNat_sub] <;> simp <;> omega
  have hW := congrArg (· * wt k.toNat) hd
  generalize P[r.toNat + k.toNat] = X at *
  generalize (if X < c then (1 : Word) else 0).toNat = b at *
  generalize (X - c).toNat = e at *
  generalize pv (vpool m) r.toNat k.toNat = A at *
  generalize pv P ob.toNat k.toNat = Bv at *
  generalize pv P r.toNat k.toNat = Cv at *
  generalize wt k.toNat = W at *
  generalize q.toNat = Q at *
  generalize c.toNat = C at *
  generalize X.toNat = Xn at *
  clear hoff hst hlx hs hk ex
  grind

section submul
variable (p : Prog) (P0 : Array Word) (C : Nat)

/-- The invariant of `div_submul`'s pass over the entry pool `P0`: the first `i` limbs of `R`
minus `q` times the first `i` limbs of `b`, with the carry `c` still to subtract. -/
def DSmInv (P0 : Array Word) (C : Nat) (s : St) : Prop :=
  C < 2 ^ 64 ∧ P0.size = 2 ^ 41 ∧ pcap s.mem = C ∧
  (s.loc 0).toNat + (s.loc 1).toNat ≤ C ∧ (s.loc 2).toNat + (s.loc 1).toNat ≤ (s.loc 0).toNat ∧
  s.loc 9 = s.loc 0 >>> 40 ∧ s.loc 10 = s.loc 0 &&& 1099511627775 ∧
  (s.mem.arr64 (tierA POOL (s.loc 9))).size ≤ 2 ^ 40 ∧ (s.loc 9).toNat ≤ 1 ∧ (s.loc 0).toNat < 2 ^ 41 ∧
  (s.loc 4).toNat ≤ (s.loc 1).toNat ∧
  Off (vpool s.mem) P0 (s.loc 0).toNat (s.loc 4).toNat ∧
  pv (vpool s.mem) (s.loc 0).toNat (s.loc 4).toNat +
      (s.loc 3).toNat * pv P0 (s.loc 2).toNat (s.loc 4).toNat =
    pv P0 (s.loc 0).toNat (s.loc 4).toNat + (s.loc 5).toNat * wt (s.loc 4).toNat

def DSmPost (P0 : Array Word) (C : Nat) (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ PFrame s₀.mem s'.mem ∧ pcap s'.mem = C ∧
  Off (vpool s'.mem) P0 (s₀.loc 0).toNat (s₀.loc 1).toNat ∧
  s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧
  s'.loc 9 = s₀.loc 9 ∧ s'.loc 10 = s₀.loc 10 ∧
  pv (vpool s'.mem) (s₀.loc 0).toNat (s₀.loc 1).toNat +
      (s₀.loc 3).toNat * pv P0 (s₀.loc 2).toNat (s₀.loc 1).toNat =
    pv P0 (s₀.loc 0).toNat (s₀.loc 1).toNat + (s'.loc 5).toNat * wt (s₀.loc 1).toNat

set_option maxHeartbeats 2000000 in
theorem dsmLoop_spec (n : Nat) (s₀ : St) (h : DSmInv P0 C s₀) :
    ⦃fun s => s = s₀⦄ exec p n dsmLoop ⦃fun r s' => DSmPost P0 C s₀ r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [DSmInv, DSmPost] at h ⊢
    rw [exec, step_while (w := dsmLoop) rfl]
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih]
    all_goals clear ih
    all_goals (try simp only [DSmInv, DSmPost] at *)
    all_goals (try subst_vars)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem,
      Cmp.eval, Cmp.evalW, BinOp.eval, Nat.reduceEqDiff, reduceIte, decide_eq_true_eq] at *)
    all_goals (try and_intros)
    all_goals first
      | (with_reducible apply dsm_step_goal <;> grind)
      | grind (splits := 20) [arena_grind, lang_grind]

theorem dsmLoop_step_spec (n : Nat) (s₀ : St) (h : DSmInv P0 C s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) dsmLoop ⦃fun r s' => DSmPost P0 C s₀ r s'; ⊤⦄ :=
  Triple.step_exec (dsmLoop_spec p P0 C (n + 1) s₀ h)

theorem divSubmul_spec (hp : p.lookup "div_submul" = some divSubmul) (n : Nat) (s₀ : St)
    (r k ob q : Word) (hs : pcap s₀.mem < 2 ^ 64)
    (hr : r.toNat + k.toNat + 1 ≤ pcap s₀.mem) (hb : ob.toNat + k.toNat ≤ r.toNat) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "div_submul" [r, k, ob, q]
    ⦃fun res s' => LocEq s' s₀ ∧ PFrame s₀.mem s'.mem ∧
      pcap s'.mem = pcap s₀.mem ∧ (res.headD 0).toNat ≤ 1 ∧
      Off (vpool s'.mem) (vpool s₀.mem) r.toNat (k.toNat + 1) ∧
      pv (vpool s'.mem) r.toNat (k.toNat + 1) + q.toNat * pv (vpool s₀.mem) ob.toNat k.toNat =
        pv (vpool s₀.mem) r.toNat (k.toNat + 1) + (res.headD 0).toNat * wt (k.toNat + 1); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, divSubmul]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalArgs, setLoc, setLocs, ld64, st64,
      dsmLoop_step_spec p (vpool s₀.mem) (pcap s₀.mem) n]
    all_goals (try simp only [DSmInv, DSmPost] at *)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem,
      List.headD_cons, L.Locals.init_nil, Locals.init_cons_zero,
      Locals.init_cons_succ, Cmp.eval, Cmp.evalW, BinOp.eval, Nat.reduceEqDiff, reduceIte,
      decide_eq_true_eq, Sig.retVal, Sig.retOr] at *)
    all_goals (try subst_vars)
    all_goals (try and_intros)
    all_goals first
      | (grind (splits := 20) [arena_grind, lang_grind]; done)
      | (apply dsm_top_goal <;> grind (splits := 20) [arena_grind, lang_grind])

end submul

end L.Arena
