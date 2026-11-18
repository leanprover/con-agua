module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.NatDivSubmul
meta import ConAgua.Arena.NatDivWord
import ConAgua.Census.Attr
public import ConAgua.Arena.NatDivSubmul
public import ConAgua.Arena.NatDivWord
import ConAgua.Arena.NatDivFacts
import ConAgua.Arena.Word
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.NatCmpFacts
import ConAgua.Arena.NatGrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import ConAgua.L.For

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
  sorry

end kstep

end L.Arena
