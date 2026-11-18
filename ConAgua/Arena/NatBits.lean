module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.NatAdd
public import ConAgua.Arena.NatAdd
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import ConAgua.Front.Preserve

@[expose] public section

/-!
# Bitwise `Nat` ops on the limb pool: `land`, `lor`, `xor`

`nat_land`/`nat_lor`/`nat_xor` (con-ron's `land`/`lor`/`xor` and their `*_from` loops,
`ron/nat.rs:658-703`): one pass combining limb `i` of each operand (zero-extended past the
shorter one, con-ron's `limb`, reused from `nat_add` as `nat_limb`), then `nat_trim`. `land`'s
result has `min la lb` limbs (reading only that far, so the loop never needs the zero
extension in practice, but uses the same callee for one shared loop shape); `lor`/`xor` have
`max la lb`. Inputs need not be normalised; the output is.

The model `bv` is `xv` with a combining function instead of a single read: `xv`'s own shape
(`DESIGN.md`, "Loop bodies must be straight-line") carries over, so the loop proof is the house
form, same as `nat_add`'s. Whether packing a limb-wise combine into the pool matches `Nat.land`/
`Nat.lor`/`Nat.xor` on the full value is `NatOpRefine.lean`'s job (deferred, as `Norm`/pv bounds
are for comparison).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- Limb `i` of the slice `(o, l)` as a WORD, `0` past its end (`lv`, but not converted to
`Nat`: `bv` needs to feed it to a word operator `f`). -/
def lvW (p : Array Word) (o l i : Nat) : Word := if i < l then p[o + i]?.getD 0 else 0

theorem lvW_toNat (p : Array Word) (o l i : Nat) : (lvW p o l i).toNat = lv p o l i := by
  simp only [lvW, lv]; split <;> rfl
grind_pattern [arena_grind] lvW_toNat => lvW p o l i, lv p o l i

/-- The value of combining the zero-extended slices `(oa, la)`/`(ob, lb)` limb by limb with `f`,
for the first `k` limbs (`xv` with a second slice and a combinator instead of one read). -/
def bv (f : Word → Word → Word) (p : Array Word) (oa la ob lb : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => bv f p oa la ob lb k + (f (lvW p oa la k) (lvW p ob lb k)).toNat * wt k

theorem bv_succ (f : Word → Word → Word) (p : Array Word) (oa la ob lb k k' : Nat)
    (hk : k' = k + 1) :
    bv f p oa la ob lb k' = bv f p oa la ob lb k + (f (lvW p oa la k) (lvW p ob lb k)).toNat * wt k := by
  subst hk; rfl
grind_pattern [arena_grind] bv_succ => bv f p oa la ob lb k', bv f p oa la ob lb k

@[arena_grind =] theorem bv_zero (f : Word → Word → Word) (p : Array Word) (oa la ob lb : Nat) :
    bv f p oa la ob lb 0 = 0 := rfl

/-- The three word combinators, as NAMED constants (not `(· &&& ·)`-style sections): a lambda
and its point-free `HAnd.hAnd`/… form are eta-equal but not syntactically equal, and `finish`'s
pattern matching saw both forms appear (one from the invariant as written, one from `BinOp.eval`
unfolding the code's own `&`/`|`/`^`) and failed to connect them. One rigid name avoids it. -/
def andF : Word → Word → Word := fun a b => a &&& b
def orF : Word → Word → Word := fun a b => a ||| b
def xorF : Word → Word → Word := fun a b => a ^^^ b

@[arena_grind =] theorem andF_eq (a b : Word) : andF a b = a &&& b := rfl
@[arena_grind =] theorem orF_eq (a b : Word) : orF a b = a ||| b := rfl
@[arena_grind =] theorem xorF_eq (a b : Word) : xorF a b = a ^^^ b := rfl

/-- One pass over the limbs both operands have (`i < lb`, `lb` set to `min la lb`): limb `i` of
the result is the operand limbs combined bitwise. Each operator needs its own `Stmt` (L has no
higher-order operator parameter). -/
def andLoop : Stmt := lblk (oa, la, ob, lb, top, n, i, x, pt, pb, ta, qa, tb, qb) {
  for i < lb {
    x := POOL⟨ta⟩[qa + i] & POOL⟨tb⟩[qb + i];
    POOL⟨pt⟩[pb + i] := x
  }
}

def orLoop : Stmt := lblk (oa, la, ob, lb, top, n, i, x, pt, pb, ta, qa, tb, qb) {
  for i < lb {
    x := POOL⟨ta⟩[qa + i] | POOL⟨tb⟩[qb + i];
    POOL⟨pt⟩[pb + i] := x
  }
}

def xorLoop : Stmt := lblk (oa, la, ob, lb, top, n, i, x, pt, pb, ta, qa, tb, qb) {
  for i < lb {
    x := POOL⟨ta⟩[qa + i] ^ POOL⟨tb⟩[qb + i];
    POOL⟨pt⟩[pb + i] := x
  }
}

/-- The rest of the longer operand `a` (`i < lb`, `lb` set to `la`), copied (`lor`, `xor`). -/
def copyLoop : Stmt := lblk (oa, la, ob, lb, top, n, i, x, pt, pb, ta, qa, tb, qb) {
  for i < lb {
    x := POOL⟨ta⟩[qa + i];
    POOL⟨pt⟩[pb + i] := x
  }
}

/-- The slices resolved to tier and index once, one pass over the common limbs, `nat_trim`. No
call but `nat_trim`, which the inliner inlines: the compiled function is a leaf (lane linleaf).
con-ron: ConRon/Arena/Core.lean:1152-1185 ConRon.Arena.natBinOpResult -/
@[no_expose, l_impl ConRon.Arena.natBinOpResult]
def natLand : FunDecl := lfn (oa, la, ob, lb) locals (top, n, i, x, pt, pb, ta, qa, tb, qb) {
  top := CTL.u64[0];
  pt := ⦃top⦄.tier;
  pb := ⦃top⦄.idx;
  if la < lb { lb := la };
  if len(POOL⟨pt⟩) - pb < lb { abort };
  ta := ⦃oa⦄.tier;
  qa := ⦃oa⦄.idx;
  tb := ⦃ob⦄.tier;
  qb := ⦃ob⦄.idx;
  ⟪andLoop⟫;
  n := call nat_trim(top, lb);
  CTL.u64[0] := top + n;
  return n
}

/-- The operands swapped so that `a` is the longer, the slices resolved to tier and index once,
one pass over the common limbs, the rest of `a` copied, `nat_trim`. No call but `nat_trim`, which
the inliner inlines: the compiled function is a leaf (lane linleaf).
con-ron: ConRon/Arena/Core.lean:1152-1185 ConRon.Arena.natBinOpResult -/
@[no_expose, l_impl ConRon.Arena.natBinOpResult]
def natLor : FunDecl := lfn (oa, la, ob, lb) locals (top, n, i, x, pt, pb, ta, qa, tb, qb) {
  if la < lb { x := oa; oa := ob; ob := x; x := la; la := lb; lb := x };
  top := CTL.u64[0];
  pt := ⦃top⦄.tier;
  pb := ⦃top⦄.idx;
  if len(POOL⟨pt⟩) - pb < la { abort };
  ta := ⦃oa⦄.tier;
  qa := ⦃oa⦄.idx;
  tb := ⦃ob⦄.tier;
  qb := ⦃ob⦄.idx;
  ⟪orLoop⟫;
  lb := la;
  ⟪copyLoop⟫;
  n := call nat_trim(top, la);
  CTL.u64[0] := top + n;
  return n
}

/-- The operands swapped so that `a` is the longer, the slices resolved to tier and index once,
one pass over the common limbs, the rest of `a` copied, `nat_trim`. No call but `nat_trim`, which
the inliner inlines: the compiled function is a leaf (lane linleaf).
con-ron: ConRon/Arena/Core.lean:1152-1185 ConRon.Arena.natBinOpResult -/
@[no_expose, l_impl ConRon.Arena.natBinOpResult]
def natXor : FunDecl := lfn (oa, la, ob, lb) locals (top, n, i, x, pt, pb, ta, qa, tb, qb) {
  if la < lb { x := oa; oa := ob; ob := x; x := la; la := lb; lb := x };
  top := CTL.u64[0];
  pt := ⦃top⦄.tier;
  pb := ⦃top⦄.idx;
  if len(POOL⟨pt⟩) - pb < la { abort };
  ta := ⦃oa⦄.tier;
  qa := ⦃oa⦄.idx;
  tb := ⦃ob⦄.tier;
  qb := ⦃ob⦄.idx;
  ⟪xorLoop⟫;
  lb := la;
  ⟪copyLoop⟫;
  n := call nat_trim(top, la);
  CTL.u64[0] := top + n;
  return n
}

/-- The bitwise `Nat` functions, as one program. -/
def natBitsProg : Prog :=
  natProg ++ [("nat_land", natLand), ("nat_lor", natLor), ("nat_xor", natXor)]

/- `0xF0 land 0x0F = 0` (operands at 0, 1; top at 2, after both). -/
#guard (run natBitsProg 100 "nat_land" [0, 1, 1, 1] (Mem.ofWords [(POOL, #[0xF0, 0x0F, 0, 0]), (CTL, #[2])])).toOption.map (·.1)
  == some [0]
/- `0xF0 lor 0x0F = 0xFF` (same layout). -/
#guard (run natBitsProg 100 "nat_lor" [0, 1, 1, 1] (Mem.ofWords [(POOL, #[0xF0, 0x0F, 0, 0]), (CTL, #[2])])).toOption.map (fun (r, m) => (r, m.arr64 POOL, m.arr64 CTL))
  == some ([1], #[0xF0, 0x0F, 0xFF, 0], #[3])
/- `[1, 1] xor [1] = [0, 1]` (top limb survives, bottom cancels; length 2 after trim; operands at
0 (len 2) and 2 (len 1), top at 3). -/
#guard (run natBitsProg 100 "nat_xor" [0, 2, 2, 1] (Mem.ofWords [(POOL, #[1, 1, 1, 0, 0]), (CTL, #[3])])).toOption.map
  (fun (r, m) => (r, m.arr64 POOL, m.arr64 CTL)) == some ([2], #[1, 1, 1, 0, 1], #[5])

section bitFn
variable (p : Prog) (hpt : p.lookup "nat_trim" = some natTrim)

set_option maxHeartbeats 2000000 in
include hpt in
/-- `nat_land` appends the limb-wise AND of `(oa, la)`/`(ob, lb)` (`min la lb` limbs before
trimming), normalised, at the old top; nothing below the old top changes. -/
theorem natLand_spec (hpa : p.lookup "nat_land" = some natLand) (n : Nat) (s₀ : St)
    (oa la ob lb : Word) (hok : PoolOK s₀.mem) (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_land" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧ PFrame (s₀.mem.set64 CTL 0 (s₀.mem.top + r.headD 0)) s'.mem ∧
      pcap s'.mem = pcap s₀.mem ∧
      s₀.mem.top.toNat + (r.headD 0).toNat ≤ pcap s'.mem ∧
      Agree (vpool s'.mem) (vpool s₀.mem) s₀.mem.top.toNat ∧
      pv (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat =
        bv andF (vpool s₀.mem) oa.toNat la.toNat ob.toNat lb.toNat
          (if lb.toNat < la.toNat then lb.toNat else la.toNat) ∧
      Norm (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat ∧ Grows s₀.mem s'.mem; ⊤⦄ := by
  sorry

set_option maxHeartbeats 2000000 in
include hpt in
theorem natLor_spec (hpo : p.lookup "nat_lor" = some natLor) (n : Nat) (s₀ : St)
    (oa la ob lb : Word) (hok : PoolOK s₀.mem) (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_lor" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧ PFrame (s₀.mem.set64 CTL 0 (s₀.mem.top + r.headD 0)) s'.mem ∧
      pcap s'.mem = pcap s₀.mem ∧
      s₀.mem.top.toNat + (r.headD 0).toNat ≤ pcap s'.mem ∧
      Agree (vpool s'.mem) (vpool s₀.mem) s₀.mem.top.toNat ∧
      pv (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat =
        bv orF (vpool s₀.mem) oa.toNat la.toNat ob.toNat lb.toNat
          (if la.toNat < lb.toNat then lb.toNat else la.toNat) ∧
      Norm (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat ∧ Grows s₀.mem s'.mem; ⊤⦄ := by
  sorry

set_option maxHeartbeats 2000000 in
include hpt in
theorem natXor_spec (hpx : p.lookup "nat_xor" = some natXor) (n : Nat) (s₀ : St)
    (oa la ob lb : Word) (hok : PoolOK s₀.mem) (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_xor" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧ PFrame (s₀.mem.set64 CTL 0 (s₀.mem.top + r.headD 0)) s'.mem ∧
      pcap s'.mem = pcap s₀.mem ∧
      s₀.mem.top.toNat + (r.headD 0).toNat ≤ pcap s'.mem ∧
      Agree (vpool s'.mem) (vpool s₀.mem) s₀.mem.top.toNat ∧
      pv (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat =
        bv xorF (vpool s₀.mem) oa.toNat la.toNat ob.toNat lb.toNat
          (if la.toNat < lb.toNat then lb.toNat else la.toNat) ∧
      Norm (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat ∧ Grows s₀.mem s'.mem; ⊤⦄ := by
  sorry

end bitFn

end L.Arena
