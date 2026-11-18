module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.NatDivSubmul
meta import ConAgua.Arena.NatDivWord
import ConAgua.Census.Attr
public import ConAgua.Arena.NatDivSubmul
public import ConAgua.Arena.NatDivWord
import ConAgua.Arena.NatDivFacts
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.NatCmpFacts
import ConAgua.Arena.NatGrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import ConAgua.L.For
public import ConAgua.L.PureEval

@[expose] public section

/-!
# `div_kstep`: one step of Knuth's algorithm D (lane `bigdiv`)

`div_kstep(wj, lb, ob, s, d, v)` divides the window of `lb + 1` limbs at `wj` (a value `T < b · 2^64`)
by the `lb ≥ 2` limbs `b` at `ob`, in place: con-ron's `dm_step` and `dm_correct`
(`ron/nat.rs`). The estimate `q̂ = min(⌊U / d⌋, 2^64 - 1)` comes from the window's top three limbs
read shifted left by `s` (`U = ⌊T 2^s / 2^(64 (lb - 1))⌋`, two words) against
`d = ⌊b 2^s / 2^(64 (lb - 1))⌋`; it is at least `⌊T / b⌋` (`knuth_est`). `div_submul` subtracts
`q̂ b`; while the window is negative, `q̂` steps down and `div_add` adds `b` back.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The correction (con-ron's `dm_correct`): while the window is negative (`c` the borrow), one
decrement of `q` and one addition of `b`; the carry out of the addition ends it. -/
def dcLoop : Stmt := lblk (wj, lb, ob, s, d, v, x, c, q, u1, u0, r) {
  while c != 0 {
    q := q - 1;
    c := call div_add(wj, lb + 1, ob, lb);
    c := u64(c == 0)
  }
}

/-- `div_kstep(wj, lb, ob, s, d, v)`: one step of Knuth's algorithm D on the window of `lb + 1`
limbs at `wj` (con-ron's `dm_step` for `|b| ≥ 2`): the estimate from the window's top three limbs
read shifted by `s` against `d`, `b`'s top two limbs shifted by `s`; then `div_submul` and the
correction. Returns the quotient digit; the window is left holding the remainder. -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def divKstep : FunDecl := lfn (wj, lb, ob, s, d, v) locals (x, c, q, u1, u0, r) {
  x := POOL⦃wj + lb⦄;
  c := POOL⦃wj + lb - 1⦄;
  u1 := (x << s) + ((c >> 1) >> (63 - s));
  x := POOL⦃wj + lb - 2⦄;
  u0 := (c << s) + ((x >> 1) >> (63 - s));
  if d <= u1 { q := 0 - 1 } else { (q, r) := call div_2by1(u1, u0, d, v) };
  c := call div_submul(wj, lb, ob, q);
  ⟪dcLoop⟫;
  return q
}

/-- `div_kstep`'s estimate: the window's top three limbs shifted by `s`, and `q̂`. -/
def kEst : Stmt := lblk (wj, lb, ob, s, d, v, x, c, q, u1, u0, r) {
  x := POOL⦃wj + lb⦄;
  c := POOL⦃wj + lb - 1⦄;
  u1 := (x << s) + ((c >> 1) >> (63 - s));
  x := POOL⦃wj + lb - 2⦄;
  u0 := (c << s) + ((x >> 1) >> (63 - s));
  if d <= u1 { q := 0 - 1 } else { (q, r) := call div_2by1(u1, u0, d, v) }
}

/-- `div_kstep` after the estimate. -/
def kTail : Stmt := lblk (wj, lb, ob, s, d, v, x, c, q, u1, u0, r) {
  c := call div_submul(wj, lb, ob, q);
  ⟪dcLoop⟫;
  return q
}

/-- The body is the estimate then the rest (`rfl`: the function text stays as written). -/
private theorem divKstep_body : divKstep.body = kEst.snoc kTail := rfl

/-! ## The arithmetic of the step -/

/-- The top three limbs of a slice. -/
theorem pv_top3 (P : Array Word) (o k : Nat) :
    pv P o (k + 3) = pv P o k + wt k * ((P[o + k]?.getD 0).toNat + 2 ^ 64 *
      ((P[o + (k + 1)]?.getD 0).toNat + 2 ^ 64 * (P[o + (k + 2)]?.getD 0).toNat)) := by
  have h1 : wt (k + 1) = wt k * 2 ^ 64 := wt_succ k (k + 1) rfl
  have h2 : wt (k + 2) = wt (k + 1) * 2 ^ 64 := wt_succ (k + 1) (k + 2) rfl
  simp only [pv, h2, h1]
  grind

/-- The two words `u1`, `u0` the step computes from the window's top three limbs `x2, x1, x0`
are the window shifted by `s`, divided by the weight below them (no word wraps: the shifted window
is below `wt (k + 3)`). -/
theorem kest_U (L k : Nat) (x2 x1 x0 s : Word) (hL : L < wt k) (hs : s.toNat ≤ 63)
    (hT : (L + wt k * (x0.toNat + 2 ^ 64 * (x1.toNat + 2 ^ 64 * x2.toNat))) * sh s.toNat <
      wt (k + 3)) :
    ((x2 <<< s) + ((x1 >>> 1) >>> (63 - s))).toNat * 2 ^ 64 +
        ((x1 <<< s) + ((x0 >>> 1) >>> (63 - s))).toNat =
      (L + wt k * (x0.toNat + 2 ^ 64 * (x1.toNat + 2 ^ 64 * x2.toNat))) * sh s.toNat /
        wt (k + 1) := by
  have hw3 : wt (k + 3) = wt (k + 1) * (2 ^ 64 * 2 ^ 64) := by
    rw [wt_succ (k + 2) (k + 3) rfl, wt_succ (k + 1) (k + 2) rfl, Nat.mul_assoc]
  have hU : (L + wt k * (x0.toNat + 2 ^ 64 * (x1.toNat + 2 ^ 64 * x2.toNat))) * sh s.toNat /
      wt (k + 1) < 2 ^ 64 * 2 ^ 64 := by
    apply Nat.div_lt_of_lt_mul; rw [← hw3]; exact hT
  rw [top2_div L x0.toNat (x1.toNat + 2 ^ 64 * x2.toNat) k s.toNat hL hs] at hU ⊢
  have hs64 : s.toNat < 64 := by omega
  have l2 := shl_lo x2 s hs64
  have l1 := shl_lo x1 s hs64
  have g1 := shl_hi x1 s hs64
  have g0 := shl_hi x0 s hs64
  have g0lt := shl_hi_lt x0 s hs64
  have room := mod_shift_room x1.toNat s.toNat hs
  simp only [sh] at hU room ⊢
  rw [UInt64.toNat_add, UInt64.toNat_add, l2, l1, g1, g0]
  rw [g0] at g0lt
  have e : (x1.toNat + 2 ^ 64 * x2.toNat) * 2 ^ s.toNat =
      x1.toNat * 2 ^ s.toNat + 2 ^ 64 * (x2.toNat * 2 ^ s.toNat) := by grind
  rw [e] at hU ⊢
  have dm := Nat.div_add_mod (x1.toNat * 2 ^ s.toNat) (2 ^ 64)
  generalize x2.toNat * 2 ^ s.toNat = A2 at *
  generalize x1.toNat * 2 ^ s.toNat = A1 at *
  generalize x0.toNat * 2 ^ s.toNat / 2 ^ 64 = H0 at *
  generalize 2 ^ s.toNat = S at *
  have : A2 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- The shifted window is below `wt (lb + 1)`: `T < b 2^64` and `d = ⌊b 2^s / w⌋` is a word. -/
theorem kest_bound (T b S w : Nat) (hw : 0 < w) (hT : T < b * 2 ^ 64) (hd : b * S / w < 2 ^ 64)
    (hS : 0 < S) : T * S < w * 2 ^ 64 * 2 ^ 64 := by
  have h1 : b * S < 2 ^ 64 * w := (Nat.div_lt_iff_lt_mul hw).mp hd
  have h2 : (T + 1) * S ≤ b * 2 ^ 64 * S := Nat.mul_le_mul_right _ hT
  have h3 : b * 2 ^ 64 * S = b * S * 2 ^ 64 := by grind
  have h4 : b * S * 2 ^ 64 < 2 ^ 64 * w * 2 ^ 64 :=
    Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos _)
  have h5 : (T + 1) * S = T * S + S := by grind
  have h6 : 2 ^ 64 * w * 2 ^ 64 = w * 2 ^ 64 * 2 ^ 64 := by grind
  omega

/-- The estimate from `div_2by1` (`q d + r = U`, `r < d`) is at least the quotient digit. -/
theorem kest_q (T b s w q r U : Nat) (hw : 0 < w) (hD0 : 0 < b * sh s / w)
    (hU : U = T * sh s / w) (hq : q * (b * sh s / w) + r = U) (hr : r < b * sh s / w) :
    T / b ≤ q := by
  have k := knuth_est T b s w hw hD0
  rw [← hU] at k
  have : U / (b * sh s / w) = q := by
    rw [← hq, Nat.add_comm, Nat.add_mul_div_right _ _ hD0, Nat.div_eq_of_lt hr, Nat.zero_add]
  omega

/-- An L load of the pool at an address below `2^41` reads the virtual pool. -/
theorem rd64_at (m : Mem) (a : Word) (j : Nat) (hj : a.toNat = j) (h : j < 2 ^ 41) :
    rd64 m (tierA 0 (a >>> 40)) (a &&& 1099511627775) = (vpool m)[j]?.getD 0 := by
  subst hj
  rw [vpool_getD m a h]
  simp only [rd64, prd, Array.getD_eq_getD_getElem?]

/-- The two words of the estimate, in the shape of the step's verification condition: the
window's top three limbs read by the loads, shifted by `s`, are `⌊T 2^s / wt (lb - 1)⌋`. -/
theorem kest_words (m : Mem) (wj lb s : Word) (B : Nat) (hs : pcap m < 2 ^ 64)
    (hw : wj.toNat + lb.toNat + 1 ≤ pcap m) (hlb : 2 ≤ lb.toNat) (hs63 : s.toNat ≤ 63)
    (hd : B * sh s.toNat / wt (lb.toNat - 1) < 2 ^ 64)
    (hT : pv (vpool m) wj.toNat (lb.toNat + 1) < B * 2 ^ 64) :
    (rd64 m (tierA 0 ((wj + lb) >>> 40)) (wj + lb &&& 1099511627775) <<< s +
        rd64 m (tierA 0 ((wj + lb - 1) >>> 40)) (wj + lb - 1 &&& 1099511627775) >>> 1 >>>
          (63 - s)).toNat * 2 ^ 64 +
      (rd64 m (tierA 0 ((wj + lb - 1) >>> 40)) (wj + lb - 1 &&& 1099511627775) <<< s +
        rd64 m (tierA 0 ((wj + lb - 2) >>> 40)) (wj + lb - 2 &&& 1099511627775) >>> 1 >>>
          (63 - s)).toNat =
    pv (vpool m) wj.toNat (lb.toNat + 1) * sh s.toNat / wt (lb.toNat - 1) := by
  have hc := pcap_eq _ hs
  obtain ⟨k, hk⟩ : ∃ k, lb.toNat = k + 2 := ⟨lb.toNat - 2, by omega⟩
  have a2 : (wj + lb).toNat = wj.toNat + (k + 2) := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega
  have a1 : (wj + lb - 1).toNat = wj.toNat + (k + 1) := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, a2]; simp only [UInt64.reduceToNat]; omega),
      a2]
    simp only [UInt64.reduceToNat]; omega
  have a0 : (wj + lb - 2).toNat = wj.toNat + k := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, a2]; simp only [UInt64.reduceToNat]; omega),
      a2]
    simp only [UInt64.reduceToNat]; omega
  rw [rd64_at m _ _ a2 (by omega), rd64_at m _ _ a1 (by omega), rd64_at m _ _ a0 (by omega)]
  have hw0 : 0 < wt (k + 1) := Nat.two_pow_pos _
  rw [hk, show k + 2 - 1 = k + 1 by omega] at hd ⊢
  rw [hk] at hT
  rw [show k + 2 + 1 = k + 3 by omega] at hT ⊢
  have hb := kest_bound _ B (sh s.toNat) (wt (k + 1)) hw0 hT hd (sh_pos _)
  rw [← wt_succ (k + 1) (k + 2) rfl, ← wt_succ (k + 2) (k + 3) rfl] at hb
  rw [pv_top3] at hb ⊢
  exact kest_U _ k _ _ _ s (pv_lt_wt _ _ _) hs63 hb

/-- `T / b` is a word when `T < b 2^64`. -/
theorem kest_max (T B : Nat) (hB : 0 < B) (hT : T < B * 2 ^ 64) : T / B ≤ (0 - 1 : Word).toNat := by
  have : T / B < 2 ^ 64 := (Nat.div_lt_iff_lt_mul hB).mpr (by grind)
  have e : (0 - 1 : Word).toNat = 2 ^ 64 - 1 := rfl
  omega

/-- `d > 0` makes `b > 0`. -/
theorem kest_Bpos (B s w : Nat) (d : Word) (hd : d.toNat = B * sh s / w) (hd0 : 0 < d.toNat) :
    0 < B := by
  rcases Nat.eq_zero_or_pos B with h | h
  · subst h; simp at hd; omega
  · exact h

/-- What the estimate establishes: the locals that the rest reads, and `q̂ ≥ ⌊T / b⌋`. -/
def KEstPost (s₀ : St) (T B : Nat) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ s'.mem = s₀.mem ∧ s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧
  s'.loc 2 = s₀.loc 2 ∧ T / B ≤ (s'.loc 8).toNat

section est
variable (p : Prog) (hp2 : p.lookup "div_2by1" = some div2by1)

include hp2 in
theorem kEst_spec (T B : Nat) (n : Nat) (s₀ : St) (hs : pcap s₀.mem < 2 ^ 64)
    (hw : (s₀.loc 0).toNat + (s₀.loc 1).toNat + 1 ≤ pcap s₀.mem) (hlb : 2 ≤ (s₀.loc 1).toNat)
    (hs63 : (s₀.loc 3).toNat ≤ 63)
    (hd : (s₀.loc 4).toNat = B * sh (s₀.loc 3).toNat / wt ((s₀.loc 1).toNat - 1))
    (hd0 : 0 < (s₀.loc 4).toNat) (hT : T < B * 2 ^ 64)
    (hTd : T = pv (vpool s₀.mem) (s₀.loc 0).toNat ((s₀.loc 1).toNat + 1)) :
    ⦃fun s => s = s₀⦄ step p (exec p n) kEst ⦃fun r s' => KEstPost s₀ T B r s'; ⊤⦄ := by
  unfold kEst
  vcgen [step, L.evalE_spec, L.evalC_spec, evalArgs, setLoc, setLocs, div2by1_spec p hp2 n]
  all_goals (try subst_vars)
  all_goals (try simp only [KEstPost, Expr.pval, Cond.pval, St.setLoc_loc, L.St.setLoc_mem,
    St.setLocs_nil, St.setLocs_cons, Cmp.eval, BinOp.eval, Nat.reduceEqDiff, reduceIte,
    decide_eq_true_eq] at *)
  all_goals (try simp only [true_and])
  all_goals
    have hB := kest_Bpos _ _ _ _ hd hd0
    have hU := kest_words _ _ _ _ B hs hw hlb hs63 (by rw [← hd]; exact UInt64.toNat_lt _) hT
  · exact kest_max _ _ hB hT
  · obtain ⟨hq, hr⟩ := ‹_ ∧ _›
    rw [hU] at hq
    rw [hd] at hq hr hd0
    exact kest_q _ _ _ _ _ _ _ (Nat.two_pow_pos _) hd0 rfl hq hr
  · rename_i hn
    exact Nat.lt_of_not_le (fun h => hn (UInt64.le_iff_toNat_le.mpr h))

end est


/-! ## The correction loop -/

/-- The correction's invariant over the entry memory `m0`: the window `A` (in place) and `q`
keep `A + q b = T + c · wt (lb + 1)`, `c ≤ 1`, and `q ≥ ⌊T / b⌋`. -/
def DcInv (m0 : Mem) (wj lb ob : Word) (T B : Nat) (s : St) : Prop :=
  pcap m0 < 2 ^ 64 ∧ wj.toNat + lb.toNat + 1 ≤ pcap m0 ∧ ob.toNat + lb.toNat ≤ wj.toNat ∧
  0 < B ∧ B = pv (vpool m0) ob.toNat lb.toNat ∧
  s.loc 0 = wj ∧ s.loc 1 = lb ∧ s.loc 2 = ob ∧
  PFrame m0 s.mem ∧ pcap s.mem = pcap m0 ∧ Off (vpool s.mem) (vpool m0) wj.toNat (lb.toNat + 1) ∧
  (s.loc 7).toNat ≤ 1 ∧ T / B ≤ (s.loc 8).toNat ∧
  pv (vpool s.mem) wj.toNat (lb.toNat + 1) + (s.loc 8).toNat * B =
    T + (s.loc 7).toNat * wt (lb.toNat + 1)

def DcPost (m0 : Mem) (wj lb : Word) (T B : Nat) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ PFrame m0 s'.mem ∧ pcap s'.mem = pcap m0 ∧
  Off (vpool s'.mem) (vpool m0) wj.toNat (lb.toNat + 1) ∧
  (s'.loc 8).toNat = T / B ∧ pv (vpool s'.mem) wj.toNat (lb.toNat + 1) = T % B

/-- One correction: the window was negative (`c = 1`), so `q b > T` and `q - 1 ≥ ⌊T / b⌋`; adding
`b` back with carry `C` leaves the borrow `1 - C`. -/
theorem dc_arith (A A' Q C B T W : Nat) (heq : A + Q * B = T + W) (hA : A < W) (hB : 0 < B)
    (hadd : A' + C * W = A + B) (hC : C ≤ 1) :
    1 ≤ Q ∧ T / B ≤ Q - 1 ∧ A' + (Q - 1) * B = T + (if C = 0 then 1 else 0) * W := by
  have h1 : T < Q * B := by omega
  have h2 : T / B < Q := (Nat.div_lt_iff_lt_mul hB).mpr h1
  have h3 : (Q - 1) * B = Q * B - B := Nat.sub_one_mul Q B
  have h4 : B ≤ Q * B := Nat.le_mul_of_pos_left B (Nat.lt_of_le_of_lt (Nat.zero_le _) h2)
  have h5 : 1 ≤ Q := Nat.lt_of_le_of_lt (Nat.zero_le _) h2
  have h6 : T / B ≤ Q - 1 := Nat.le_sub_one_of_lt h2
  refine ⟨h5, h6, ?_⟩
  rw [h3]
  clear h2 h5 h6
  generalize Q * B = P at *
  rcases Nat.lt_or_ge C 1 with hc | hc
  · have : C = 0 := by omega
    subst this; simp only [↓reduceIte, Nat.one_mul, Nat.zero_mul] at hadd ⊢; omega
  · have : C = 1 := by omega
    subst this; simp only [Nat.one_ne_zero, ↓reduceIte, Nat.zero_mul, Nat.one_mul] at hadd ⊢; omega

/-- The correction ends (`c = 0`): `A + q b = T` with `q ≥ ⌊T / b⌋` pins `q` and the remainder. -/
theorem dc_exit (A Q B T : Nat) (heq : A + Q * B = T) (hq : T / B ≤ Q) (hB : 0 < B) :
    Q = T / B ∧ A = T % B := by
  have h1 : Q ≤ T / B := (Nat.le_div_iff_mul_le hB).mpr (by omega)
  have h2 : Q = T / B := by omega
  refine ⟨h2, ?_⟩
  have := Nat.div_add_mod T B
  subst h2
  have : B * (T / B) = T / B * B := Nat.mul_comm _ _
  omega

/-- The correction's step, in the shape of its verification condition. -/
theorem dc_step_goal (m0 : Mem) (wj lb ob : Word) (T B : Nat) (s1 s : St) (rs : List Word)
    (h : DcInv m0 wj lb ob T B s1) (hc : (s1.loc 7 != 0) = true)
    (hp : LocEq s (s1.setLoc 8 (s1.loc 8 - 1)) ∧ PFrame s1.mem s.mem ∧ pcap s.mem = pcap s1.mem ∧
      (rs.headD 0).toNat ≤ 1 ∧
      Off (vpool s.mem) (vpool s1.mem) (s1.loc 0).toNat (s1.loc 1 + 1).toNat ∧
      pv (vpool s.mem) (s1.loc 0).toNat (s1.loc 1 + 1).toNat +
          (rs.headD 0).toNat * wt (s1.loc 1 + 1).toNat =
        pv (vpool s1.mem) (s1.loc 0).toNat (s1.loc 1 + 1).toNat +
          xv (vpool s1.mem) (s1.loc 2).toNat (s1.loc 1).toNat (s1.loc 1 + 1).toNat) :
    pcap m0 < 2 ^ 64 ∧ wj.toNat + lb.toNat + 1 ≤ pcap m0 ∧ ob.toNat + lb.toNat ≤ wj.toNat ∧
      0 < B ∧ B = pv (vpool m0) ob.toNat lb.toNat ∧
      s.loc 0 = wj ∧ s.loc 1 = lb ∧ s.loc 2 = ob ∧
      PFrame m0 s.mem ∧ pcap s.mem = pcap m0 ∧ Off (vpool s.mem) (vpool m0) wj.toNat (lb.toNat + 1) ∧
      UInt64.toNat (if (rs.headD 0 == 0) = true then 1 else 0) ≤ 1 ∧
      T / B ≤ UInt64.toNat (s.loc 8) ∧
      pv (vpool s.mem) wj.toNat (lb.toNat + 1) + UInt64.toNat (s.loc 8) * B =
        T + UInt64.toNat (if (rs.headD 0 == 0) = true then 1 else 0) * wt (lb.toNat + 1) := by
  obtain ⟨hs, hw, hb, hB, hBd, h0, h1, h2, hF, hcap, hO, hc1, hq, heq⟩ := h
  obtain ⟨hL, hF', hcap', hcar, hO', hadd⟩ := hp
  subst h0 h1 h2
  have l0 : s.loc 0 = s1.loc 0 := by rw [LocEq.loc hL 0]; simp [St.setLoc_loc]
  have l1 : s.loc 1 = s1.loc 1 := by rw [LocEq.loc hL 1]; simp [St.setLoc_loc]
  have l2 : s.loc 2 = s1.loc 2 := by rw [LocEq.loc hL 2]; simp [St.setLoc_loc]
  have l8 : s.loc 8 = s1.loc 8 - 1 := by rw [LocEq.loc hL 8]; simp [St.setLoc_loc]
  have hpc := pcap_eq _ hs
  have hl1 : (s1.loc 1 + 1).toNat = (s1.loc 1).toNat + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega)]
  rw [hl1] at hO' hadd
  rw [xv_full _ _ _ _ (by omega), Off.pv_below _ _ _ _ _ _ hO hb, ← hBd] at hadd
  have hc7 : (s1.loc 7).toNat = 1 := by
    have : s1.loc 7 ≠ 0 := by simpa using hc
    have : (s1.loc 7).toNat ≠ 0 := fun h => this (UInt64.toNat_inj.mp (h.trans UInt64.toNat_zero.symm))
    omega
  rw [hc7, Nat.one_mul] at heq
  have hA := pv_lt_wt (vpool s1.mem) (s1.loc 0).toNat ((s1.loc 1).toNat + 1)
  obtain ⟨hQ, hq', heq'⟩ := dc_arith _ _ _ _ _ _ _ heq hA hB hadd hcar
  have hq1 : (s1.loc 8 - 1).toNat = (s1.loc 8).toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, UInt64.toNat_one]; exact hQ),
      UInt64.toNat_one]
  have hite : UInt64.toNat (if (rs.headD 0 == 0) = true then 1 else 0) =
      if (rs.headD 0).toNat = 0 then 1 else 0 := by
    by_cases h0 : rs.headD 0 = 0
    · rw [h0]; rfl
    · have : (rs.headD 0).toNat ≠ 0 := fun h => h0 (UInt64.toNat_inj.mp (h.trans UInt64.toNat_zero.symm))
      simp only [beq_iff_eq, h0, this, ↓reduceIte, UInt64.toNat_zero]
  rw [l0, l1, l2, l8, hq1, hite]
  refine ⟨hs, hw, hb, hB, hBd, rfl, rfl, rfl, PFrame.trans hF hF', hcap'.trans hcap,
    Off.trans _ _ _ _ _ hO' hO, by split <;> simp, hq', heq'⟩

section loop
variable (p : Prog) (hpl : p.lookup "nat_limb" = some natLimb)
  (hpc : p.lookup "add_carry" = some addCarry) (hpa : p.lookup "div_add" = some divAdd)

include hpl hpc hpa in
theorem dcLoop_spec (m0 : Mem) (wj lb ob : Word) (T B : Nat) (n : Nat) (s₀ : St)
    (h : DcInv m0 wj lb ob T B s₀) :
    ⦃fun s => s = s₀⦄ exec p n dcLoop ⦃fun r s' => DcPost m0 wj lb T B r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [DcInv, DcPost] at h ⊢
    rw [exec, step_while (w := dcLoop) rfl]
    vcgen [step, L.evalE_spec, L.evalC_spec, evalArgs, setLoc, setLocs, ih,
      divAdd_spec p hpl hpc hpa n]
    all_goals clear ih
    all_goals (try subst_vars)
    all_goals (try simp only [DcInv, DcPost, Expr.pval, Cond.pval, St.setLoc_loc, L.St.setLoc_mem,
      St.setLocs_nil, St.setLocs_cons, Cmp.eval, Cmp.evalW, BinOp.eval, Nat.reduceEqDiff,
      reduceIte] at *)
    all_goals first
      | exact dc_step_goal m0 wj lb ob T B _ _ _ h ‹_› ‹_›
      | (obtain ⟨hs, hw, hb, hB, hBd, h0, h1, h2, hF, hcap, hO, hc1, hq, heq⟩ := h
         subst h0 h1 h2
         have hpc := pcap_eq _ hs
         first
           | (rename_i hc0
              simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hc0
              rw [hc0, UInt64.toNat_zero, Nat.zero_mul, Nat.add_zero] at heq
              have := dc_exit _ _ _ _ heq hq hB
              first | exact this.1 | exact this.2)
           | grind)

include hpl hpc hpa in
theorem dcLoop_step_spec (m0 : Mem) (wj lb ob : Word) (T B : Nat) (n : Nat) (s₀ : St)
    (h : DcInv m0 wj lb ob T B s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) dcLoop ⦃fun r s' => DcPost m0 wj lb T B r s'; ⊤⦄ :=
  Triple.step_exec (dcLoop_spec p hpl hpc hpa m0 wj lb ob T B (n + 1) s₀ h)

end loop

section kstep
variable (p : Prog) (hpl : p.lookup "nat_limb" = some natLimb)
  (hpc : p.lookup "add_carry" = some addCarry) (hpa : p.lookup "div_add" = some divAdd)
  (hp2 : p.lookup "div_2by1" = some div2by1) (hpm : p.lookup "div_submul" = some divSubmul)

include hpl hpc hpa hp2 hpm in
/-- `div_kstep` on a window `T < b · 2^64` (`b` the `lb ≥ 2` limbs at `ob`, below the window,
`d` its top word shifted by `s`): returns `⌊T / b⌋` and leaves `T mod b` in the window. -/
theorem divKstep_spec (hpk : p.lookup "div_kstep" = some divKstep) (n : Nat) (s₀ : St)
    (wj lb ob s d v : Word) (hs : pcap s₀.mem < 2 ^ 64)
    (hw : wj.toNat + lb.toNat + 1 ≤ pcap s₀.mem) (hb : ob.toNat + lb.toNat ≤ wj.toNat)
    (hlb : 2 ≤ lb.toNat) (hs63 : s.toNat ≤ 63)
    (hd : d.toNat = pv (vpool s₀.mem) ob.toNat lb.toNat * sh s.toNat / wt (lb.toNat - 1))
    (hd0 : 0 < d.toNat)
    (hT : pv (vpool s₀.mem) wj.toNat (lb.toNat + 1) <
      pv (vpool s₀.mem) ob.toNat lb.toNat * 2 ^ 64) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "div_kstep" [wj, lb, ob, s, d, v]
    ⦃fun r s' => LocEq s' s₀ ∧ PFrame s₀.mem s'.mem ∧ pcap s'.mem = pcap s₀.mem ∧
      Off (vpool s'.mem) (vpool s₀.mem) wj.toNat (lb.toNat + 1) ∧
      (r.headD 0).toNat =
        pv (vpool s₀.mem) wj.toNat (lb.toNat + 1) / pv (vpool s₀.mem) ob.toNat lb.toNat ∧
      pv (vpool s'.mem) wj.toNat (lb.toNat + 1) =
        pv (vpool s₀.mem) wj.toNat (lb.toNat + 1) % pv (vpool s₀.mem) ob.toNat lb.toNat; ⊤⦄ := by
  have hB := kest_Bpos _ _ _ _ hd hd0
  rw [invoke_eq _ hpk]
  simp only [callFn, divKstep_body]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    simp only [exec, step_snoc]
    unfold kTail
    vcgen [step, L.evalE_spec, L.evalC_spec, evalArgs, setLoc, setLocs,
      kEst_spec p hp2 (pv (vpool s₀.mem) wj.toNat (lb.toNat + 1)) (pv (vpool s₀.mem) ob.toNat lb.toNat) n,
      divSubmul_spec p hpm n,
      dcLoop_step_spec p hpl hpc hpa s₀.mem wj lb ob (pv (vpool s₀.mem) wj.toNat (lb.toNat + 1))
        (pv (vpool s₀.mem) ob.toNat lb.toNat) n]
    all_goals (try subst_vars)
    all_goals (try simp only [KEstPost, DcInv, DcPost, Expr.pval, St.setLoc_loc,
      L.St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Nat.reduceEqDiff, reduceIte, List.headD_cons, Locals.init, List.getD_cons_zero,
      List.getD_cons_succ, Sig.retVal, Sig.retOr] at *)
    all_goals (try (apply St.restore; grind))
    all_goals grind [LocEq]

end kstep

end L.Arena
