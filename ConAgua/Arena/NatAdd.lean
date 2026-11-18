module

meta import ConAgua.L.Semantics
meta import ConAgua.Layout
public import ConAgua.L.Notation
public import ConAgua.Arena.Pool
import ConAgua.Census.Attr
public import ConAgua.L.Logic
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import ConAgua.Front.Preserve

@[expose] public section

/-!
# `Nat.add` on the limb pool

`nat_trim` (con-ron's `norm`/`sig_len`, `ron/nat.rs:122,149`) and `nat_add` (`add`/`add_from`,
`ron/nat.rs:235,242`), with `vcgen` specs: the result slice denotes `a + b` and is normalised.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## `nat_trim(o, n)`: the length of `(o, n)` without its trailing zero limbs -/

def trimLoop : Stmt := lblk (o, n) {
  while 0 < n && POOL⦃o + n - 1⦄ == 0 { n -= 1 }
}

/-- No `return` inside the loop: the inliner (`Compiler/Inline.lean`) inlines `nat_trim` into its
callers only then, which leaves `nat_add` and the other passes without a call, so the compiler
keeps their locals in registers (lane linleaf).
con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat` -/
@[no_expose] def natTrim : FunDecl := lfn (o, n) {
  ⟪trimLoop⟫;
  return n
}

section trim
variable (p : Prog) (hp : p.lookup "nat_trim" = some natTrim)

include hp in
theorem natTrim_spec (n : Nat) (s₀ : St) (o l : Word) (hs : pcap s₀.mem < 2 ^ 64)
    (hb : o.toNat + l.toNat ≤ pcap s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_trim" [o, l]
    ⦃fun r s' => s' = s₀ ∧ (r.headD 0).toNat ≤ l.toNat ∧
      pv (vpool s₀.mem) o.toNat (r.headD 0).toNat = pv (vpool s₀.mem) o.toNat l.toNat ∧
      Norm (vpool s₀.mem) o.toNat (r.headD 0).toNat; ⊤⦄ := by
  sorry

end trim

/-! ## `nat_add(oa, la, ob, lb)`: append `a + b` to the pool, return its length

The result slice starts at the old top `CTL[0]`. One pass of ripple carry over
`n = max la lb` limbs (a missing limb reads as `0`, con-ron's `limb`), the carry limb, then
`nat_trim`. Inputs need not be normalised; the output is. -/

/-- Limb `i` of the slice `(o, l)`, `0` past its end (con-ron's `limb`, `ron/nat.rs:112`). -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def natLimb : FunDecl := lfn (o, l, i) {
  if i < l { return POOL⦃o + i⦄ };
  return 0
}

/-- The carry out of `x + y + c` for a carry-in `c ≤ 1` (the two `overflowing_add`s of
`add_from`, `ron/nat.rs:257-264`). -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def addCarry : FunDecl := lfn (x, y, c) locals (s) {
  s := x + y;
  if s < x { return 1 };
  s := s + c;
  if s < c { return 1 };
  return 0
}

/-- The limbs both operands have (`i < lb`, the shorter): `x + y + c` and its carry. -/
def addRowLoop : Stmt := lblk (oa, la, ob, lb, top, n, i, c, x, y, pt, pb, ta, qa, tb, qb) {
  for i < lb {
    x := POOL⟨ta⟩[qa + i];
    y := POOL⟨tb⟩[qb + i];
    x := x + c;
    c := u64(x < c);
    x := x + y;
    c := c + u64(x < y);
    POOL⟨pt⟩[pb + i] := x
  }
}

/-- The limbs only the longer operand has (`i < lb`, `lb` set to `la`): `x + c` and its carry. -/
def addTailLoop : Stmt := lblk (oa, la, ob, lb, top, n, i, c, x, y, pt, pb, ta, qa, tb, qb) {
  for i < lb {
    x := POOL⟨ta⟩[qa + i];
    x := x + c;
    c := u64(x < c);
    POOL⟨pt⟩[pb + i] := x
  }
}

/-- The operands swapped so that `a` is the longer, the slices resolved to tier and index once,
then two passes (the common limbs, the longer operand's rest), the carry limb, `nat_trim`. No call
but `nat_trim`, which the inliner inlines: the compiled function is a leaf and keeps its hot
locals in registers (lane linleaf).
con-ron: ConRon/Arena/Core.lean:1152-1185 ConRon.Arena.natBinOpResult -/
@[no_expose, l_impl ConRon.Arena.natBinOpResult]
def natAdd : FunDecl := lfn (oa, la, ob, lb) locals (top, n, i, c, x, y, pt, pb, ta, qa, tb, qb) {
  if la < lb { x := oa; oa := ob; ob := x; x := la; la := lb; lb := x };
  top := CTL.u64[0];
  pt := ⦃top⦄.tier;
  pb := ⦃top⦄.idx;
  if len(POOL⟨pt⟩) - pb <= la { abort };
  ta := ⦃oa⦄.tier;
  qa := ⦃oa⦄.idx;
  tb := ⦃ob⦄.tier;
  qb := ⦃ob⦄.idx;
  ⟪addRowLoop⟫;
  lb := la;
  ⟪addTailLoop⟫;
  POOL⟨pt⟩[pb + la] := c;
  n := call nat_trim(top, la + 1);
  CTL.u64[0] := top + n;
  return n
}

/-- The pool functions, as one `#eval`-able program. -/
def natProg : Prog :=
  [("nat_limb", natLimb), ("add_carry", addCarry), ("nat_trim", natTrim), ("nat_add", natAdd)]

/- `(2^128 - 1) + 1 = 2^128`: limbs `[max, max]` at 0 and `[1]` at 2, top 3; the sum is
`[0, 0, 1]` at 3 and the top moves to 6. -/
#guard (run natProg 100 "nat_add" [0, 2, 2, 1]
  (Mem.ofWords [(POOL, #[0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 1, 0, 0, 0, 0, 0]), (CTL, #[3])])).toOption.map
  (fun (r, m) => (r, m.arr64 POOL, m.arr64 CTL)) ==
  some ([3], #[0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 1, 0, 0, 1, 0, 0], #[6])

/- Normalisation: `0 + 0` has length 0 (the carry limb `0` is trimmed); the top stays. -/
#guard (run natProg 100 "nat_add" [0, 0, 0, 0] (Mem.ofWords [(POOL, #[0, 0]), (CTL, #[0])])).toOption.map (·.1)
  == some [0]

/- No room: `abort`. -/
#guard (run natProg 100 "nat_add" [0, 1, 0, 1] (Mem.ofWords [(POOL, #[5, 0]), (CTL, #[1])])).toOption.isNone

section add
variable (p : Prog) (hpl : p.lookup "nat_limb" = some natLimb)
  (hpc : p.lookup "add_carry" = some addCarry) (Pg : Array Word) (C : Nat)

include hpc in
theorem addCarry_spec (n : Nat) (s₀ : St) (x y c : Word) (hc : c.toNat ≤ 1) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "add_carry" [x, y, c]
    ⦃fun r s' => s' = s₀ ∧ (r.headD 0).toNat = adcHi x y c; ⊤⦄ := by
  rw [invoke_eq _ hpc]
  simp only [callFn, addCarry]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] => vcgen [exec, step, evalE, evalC, evalArgs, setLoc] <;> finish

include hpl in
theorem natLimb_spec (n : Nat) (s₀ : St) (o l i : Word)
    (hb : o.toNat + l.toNat ≤ pcap s₀.mem) (hs : pcap s₀.mem < 2 ^ 64) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_limb" [o, l, i]
    ⦃fun r s' => s' = s₀ ∧
      (r.headD 0).toNat = lv (vpool s₀.mem) o.toNat l.toNat i.toNat; ⊤⦄ := by
  rw [invoke_eq _ hpl]
  simp only [callFn, natLimb]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] => vcgen [exec, step, evalE, evalC, evalArgs, ld64] <;> finish

end add

section addFn
variable (p : Prog) (hpt : p.lookup "nat_trim" = some natTrim)
  (hpa : p.lookup "nat_add" = some natAdd)

set_option maxHeartbeats 2000000 in
include hpt hpa in
/-- `nat_add` appends `a + b`, normalised, at the old top and moves the top past it; nothing
below the old top changes, and no other array but `CTL[0]`. -/
theorem natAdd_spec (n : Nat) (s₀ : St) (oa la ob lb : Word) (hok : PoolOK s₀.mem)
    (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_add" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧ PFrame (s₀.mem.set64 CTL 0 (s₀.mem.top + r.headD 0)) s'.mem ∧
      pcap s'.mem = pcap s₀.mem ∧
      s₀.mem.top.toNat + (r.headD 0).toNat ≤ pcap s'.mem ∧
      Agree (vpool s'.mem) (vpool s₀.mem) s₀.mem.top.toNat ∧
      pv (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat =
        pv (vpool s₀.mem) oa.toNat la.toNat + pv (vpool s₀.mem) ob.toNat lb.toNat ∧
      Norm (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat ∧ Grows s₀.mem s'.mem; ⊤⦄ := by
  sorry

end addFn

end L.Arena
