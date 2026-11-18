module

meta import ConAgua.L.Semantics
import ConAgua.Census.Attr
public import ConAgua.L.Notation
public import ConAgua.Arena.NatShiftFacts
public import ConAgua.Arena.Word
import ConAgua.Arena.NatDivFacts
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# The word steps of `nat_divmod` (lane `bigdiv`)

Three register-only functions of the limb-wise long division (`NatDiv.lean`):

* `div_norm(x)`: the shift `s` that normalises a nonzero `x` (con-ron's `norm_shift`);
* `div_2by1(u1, u0, d, v)`: `⌊(u1 · 2^64 + u0) / d⌋` and the remainder, for `u1 < d` (con-ron's
  `u128` division in `dm_step`): Möller and Granlund's estimate with the reciprocal `v` (Möller and
  Granlund, "Improved division by invariant integers", IEEE TC 2011; GMP's
  `udiv_qrnnd_preinv`), then two correction loops that make the result exact whatever `v` is;
* `div_recip(d)`: that reciprocal, `⌊(2^128 - 1) / d⌋ - 2^64`, by Newton steps from a tangent.

Only the speed depends on `v`: with the exact reciprocal (tested, not proved, as con-ron tests
Knuth's "at most two corrections") neither correction loop of `div_2by1` runs.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- `div_norm(x)`: the left shift `s ≤ 63` that sets the top bit of `x ≠ 0` (con-ron's
`norm_shift`), in six halving steps. -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def divNorm : FunDecl := lfn (x) locals (s) {
  if x < 0x100000000 { x := x << 32; s := 32 };
  if x < 0x1000000000000 { x := x << 16; s := s + 16 };
  if x < 0x100000000000000 { x := x << 8; s := s + 8 };
  if x < 0x1000000000000000 { x := x << 4; s := s + 4 };
  if x < 0x4000000000000000 { x := x << 2; s := s + 2 };
  if x < 0x8000000000000000 { s := s + 1 };
  return s
}

/-- `div_recip(d)`: the reciprocal `⌊(2^128 - 1) / d⌋ - 2^64` of a normalised `d` (Möller and
Granlund's `v`): the tangent of `1/x` at `3/4` (from below, about 3 bits), five Newton steps
`v := v + e + ⌊v e / 2^64⌋` with `e` the top word of `2^128 - d (2^64 + v)` (from below, at most
2 under), then `div_2by1` of `(2^64 - 1 - d) · 2^64 + 2^64 - 1` by `d` with that estimate. Only
the speed of `div_2by1` depends on the estimate. -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def divRecip : FunDecl := lfn (d) locals (v, t, l, h, e, j, k) {
  t := 0 - 1 - d;
  t := t + mulhi(t, 0xC71C71C71C71C71C);
  if 0x1C71C71C71C71C71 < t { v := t - 0x1C71C71C71C71C71 };
  k := 5;
  for j < k {
    l := d * v;
    h := d + mulhi(d, v);
    e := 0 - h - u64(l != 0);
    v := v + e + mulhi(v, e)
  };
  (v, t) := call div_2by1(0 - 1 - d, 0 - 1, d, v);
  return v
}

/-- `div_2by1(u1, u0, d, v)`: `(q, r)` with `u1 · 2^64 + u0 = q · d + r`, `r < d`, for `u1 < d`
(con-ron's `u128` division in `dm_step`). The estimate is Möller and Granlund's
(`udiv_qrnnd_preinv`, with the reciprocal `v` of a normalised `d`); the two loops then step `q`
down while `q · d > u` and up while the remainder is at least `d`, so the result is exact
whatever `v` is (with the true reciprocal neither loop runs). -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def div2by1 : FunDecl := lfn (u1, u0, d, v) locals (q, q0, r, plo, phi, t) {
  q0 := v * u1 + u0;
  q := mulhi(v, u1) + u1 + u64(q0 < u0) + 1;
  r := u0 - q * d;
  if q0 < r { q := q - 1; r := r + d };
  if d <= r { q := q + 1 };
  plo := q * d;
  phi := mulhi(q, d);
  while u1 < phi || (phi == u1 && u0 < plo) {
    q := q - 1;
    phi := phi - u64(plo < d);
    plo := plo - d
  };
  r := u0 - plo;
  t := u1 - phi - u64(u0 < plo);
  while t != 0 || d <= r {
    q := q + 1;
    t := t - u64(r < d);
    r := r - d
  };
  return (q, r)
}


section specs
variable (p : Prog) (hpn : p.lookup "div_norm" = some divNorm)
  (hp2 : p.lookup "div_2by1" = some div2by1) (hpr : p.lookup "div_recip" = some divRecip)

include hpn in
/-- `div_norm(x)` for `x ≠ 0`: `x · 2^s` is a word with its top bit set, `s ≤ 63`. -/
theorem divNorm_spec (n : Nat) (s₀ : St) (x : Word) (hx : 0 < x.toNat) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "div_norm" [x]
    ⦃fun r s' => s' = s₀ ∧ (r.headD 0).toNat ≤ 63 ∧ x.toNat * sh (r.headD 0).toNat < 2 ^ 64 ∧
      2 ^ 63 ≤ x.toNat * sh (r.headD 0).toNat; ⊤⦄ := by
  sorry

include hp2 in
/-- `div_2by1(u1, u0, d, v)` for `u1 < d`: `(q, r)` with `q d + r = u1 2^64 + u0`, `r < d`. -/
theorem div2by1_spec (n : Nat) (s₀ : St) (u1 u0 d v : Word) (hlt : u1.toNat < d.toNat) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "div_2by1" [u1, u0, d, v]
    ⦃fun r s' => s' = s₀ ∧
      (r.headD 0).toNat * d.toNat + (r.tail.headD 0).toNat = u1.toNat * 2 ^ 64 + u0.toNat ∧
      (r.tail.headD 0).toNat < d.toNat; ⊤⦄ := by
  sorry

include hp2 hpr in
/-- `div_recip(d)` for a normalised `d` changes nothing (its result only steers `div_2by1`'s
speed). -/
theorem divRecip_spec (n : Nat) (s₀ : St) (d : Word) (hd : 2 ^ 63 ≤ d.toNat) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "div_recip" [d]
    ⦃fun _ s' => s' = s₀; ⊤⦄ := by
  sorry

end specs

end L.Arena
