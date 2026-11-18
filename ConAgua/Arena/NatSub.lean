module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.NatAdd
import ConAgua.Census.Attr
public import ConAgua.Arena.NatAdd
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.NatCmpFacts
import ConAgua.Arena.NatGrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import ConAgua.Front.Preserve

@[expose] public section

/-!
# Truncated subtraction on the limb pool: `nat_sub`

`nat_sub(oa, la, ob, lb)` is Lean's `a - b` (`0` when `a < b`), con-ron's `sub`/`sub_from`
(`ron/nat.rs:270-300`). con-ron compares first (`cmp`) and runs the ripple borrow only when
`a > b`; here the ripple borrow runs over `max la lb` limbs (`nat_add`'s loop shape, with
`nat_limb` for both operands) and the borrow out of the top limb decides: `1` means `a < b`,
and the result is `0`. This needs neither normalised inputs nor `nat_cmp`, and the loop is
`nat_add`'s with a borrow instead of a carry, so the proof is too.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## `nat_sub(oa, la, ob, lb)` -/

/-- The limbs both operands have (`i < n`, `n = min la lb`): `x - y - c` and its borrow. -/
def subRowLoop : Stmt := lblk (oa, la, ob, lb, top, n, i, c, x, y, d, pt, pb, ta, qa, tb, qb) {
  for i < n {
    x := POOL⟨ta⟩[qa + i];
    y := POOL⟨tb⟩[qb + i];
    d := x - y;
    POOL⟨pt⟩[pb + i] := d - c;
    c := u64(x < y) + u64(d < c)
  }
}

/-- The rest of `a` (`i < n`, `n = la`): `x - c` and its borrow. -/
def subTailLoop : Stmt := lblk (oa, la, ob, lb, top, n, i, c, x, y, d, pt, pb, ta, qa, tb, qb) {
  for i < n {
    x := POOL⟨ta⟩[qa + i];
    POOL⟨pt⟩[pb + i] := x - c;
    c := u64(x < c)
  }
}

/-- The rest of `b` (`i < n`, `n = lb`): a nonzero limb means `a < b`. -/
def subHighLoop : Stmt := lblk (oa, la, ob, lb, top, n, i, c, x, y, d, pt, pb, ta, qa, tb, qb) {
  for i < n {
    if POOL⟨tb⟩[qb + i] != 0 { c := 1 }
  }
}

/-- The slices resolved to tier and index once, then the common limbs, the rest of `a` (with the
borrow) and the rest of `b` (any nonzero limb is a borrow). A borrow out means `a < b`: the result
is `0`; otherwise it has at most `la` limbs, trimmed. No call but `nat_trim`, which the inliner
inlines: the compiled function is a leaf (lane linleaf).
con-ron: ConRon/Arena/Core.lean:1152-1185 ConRon.Arena.natBinOpResult -/
@[no_expose, l_impl ConRon.Arena.natBinOpResult]
def natSub : FunDecl := lfn (oa, la, ob, lb) locals (top, n, i, c, x, y, d, pt, pb, ta, qa, tb, qb) {
  top := CTL.u64[0];
  pt := ⦃top⦄.tier;
  pb := ⦃top⦄.idx;
  n := la;
  if la < lb { n := lb };
  if len(POOL⟨pt⟩) - pb < n { abort };
  ta := ⦃oa⦄.tier;
  qa := ⦃oa⦄.idx;
  tb := ⦃ob⦄.tier;
  qb := ⦃ob⦄.idx;
  n := la;
  if lb < la { n := lb };
  ⟪subRowLoop⟫;
  n := la;
  ⟪subTailLoop⟫;
  n := lb;
  ⟪subHighLoop⟫;
  if c != 0 { n := 0 } else { n := call nat_trim(top, la) };
  CTL.u64[0] := top + n;
  return n
}

/-- The pool functions with `nat_sub`. -/
def natSubProg : Prog := natProg ++ [("nat_sub", natSub)]

/- `2^64 - 1 = [max]`: operands `[0, 1]` at 0 and `[1]` at 2, top 3. -/
#guard (run natSubProg 100 "nat_sub" [0, 2, 2, 1]
  (Mem.ofWords [(POOL, #[0, 1, 1, 0, 0]), (CTL, #[3])])).toOption.map (fun (r, m) => (r, m.arr64 POOL, m.arr64 CTL)) ==
  some ([1], #[0, 1, 1, 0xFFFFFFFFFFFFFFFF, 0], #[4])
/- `1 - 2^64 = 0`, and `5 - 5 = 0`; the top stays. -/
#guard (run natSubProg 100 "nat_sub" [2, 1, 0, 2]
  (Mem.ofWords [(POOL, #[0, 1, 1, 0, 0]), (CTL, #[3])])).toOption.map (fun (r, m) => (r, m.arr64 CTL)) ==
  some ([0], #[3])
#guard (run natSubProg 100 "nat_sub" [0, 1, 1, 1]
  (Mem.ofWords [(POOL, #[5, 5, 0]), (CTL, #[2])])).toOption.map (fun (r, m) => (r, m.arr64 CTL)) ==
  some ([0], #[2])

/-- A set borrow (or carry) bit times a weight is the weight. -/
theorem bit_mul_wt (c : Word) (k : Nat) (h1 : c.toNat ≤ 1) (h2 : c ≠ 0) : c.toNat * wt k = wt k := by
  have : c.toNat ≠ 0 := fun h => h2 (UInt64.toNat_inj.mp (h.trans UInt64.toNat_zero.symm))
  have : c.toNat = 1 := by omega
  rw [this, Nat.one_mul]
grind_pattern [arena_grind] bit_mul_wt => c.toNat * wt k

section subFn
variable (p : Prog) (hpt : p.lookup "nat_trim" = some natTrim)
  (hpn : p.lookup "nat_sub" = some natSub)

set_option maxHeartbeats 2000000 in
include hpt hpn in
/-- `nat_sub` appends `a - b` (truncated), normalised, at the old top and moves the top past it;
nothing below the old top changes, and no other array but `CTL[0]`. -/
theorem natSub_spec (n : Nat) (s₀ : St) (oa la ob lb : Word) (hok : PoolOK s₀.mem)
    (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_sub" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧ PFrame (s₀.mem.set64 CTL 0 (s₀.mem.top + r.headD 0)) s'.mem ∧
      pcap s'.mem = pcap s₀.mem ∧
      s₀.mem.top.toNat + (r.headD 0).toNat ≤ pcap s'.mem ∧
      Agree (vpool s'.mem) (vpool s₀.mem) s₀.mem.top.toNat ∧
      pv (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat =
        pv (vpool s₀.mem) oa.toNat la.toNat - pv (vpool s₀.mem) ob.toNat lb.toNat ∧
      Norm (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat ∧ Grows s₀.mem s'.mem; ⊤⦄ := by
  sorry

end subFn

end L.Arena
