module

public import ConAgua.Arena.NatDiv
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.NatGrindAttr
import ConAgua.Front.Preserve
import ConAgua.L.GrindAttr
import Std.Data.DTreeMap.Internal.Operations
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# `Nat.gcd` on the limb pool: `nat_gcd`

`nat_gcd(oa, la, ob, lb)` is `Nat.gcd a b` for normalised slices (con-ron's `gcd`,
`ron/nat.rs:644-653`, Lean's own recursion `gcd 0 y = y`, `gcd (x + 1) y = gcd (y % (x + 1)) (x + 1)`):
while `a ≠ 0` (a normalised slice is `0` iff it has no limbs), `(a, b) := (b % a, a)` with
`nat_divmod` (in `gcd_step`, so that the loop body is one call), which appends each remainder
to the pool. It returns `b`'s slice `(o, l)`. As
`nat_pow`'s, the loop invariant follows two slices that move every iteration, with `Grows` from
the entry memory; the step is `Nat.gcd (b % a) a = Nat.gcd a b`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

theorem gcd_step (a b : Nat) : Nat.gcd (b % a) a = Nat.gcd a b := (Nat.gcd_rec a b).symm
grind_pattern [natop_grind] gcd_step => Nat.gcd (b % a) a

theorem gcd_zero_len (p : Array Word) (o : Nat) (l : Word) (b : Nat) (h : l = 0) :
    Nat.gcd (pv p o l.toNat) b = b := by
  subst h; simp [pv]
grind_pattern [natop_grind] gcd_zero_len => Nat.gcd (pv p o l.toNat) b

/-- A normalised slice below `t` stays normalised in a pool that agrees below `t`.
(`LitRefine.lean` has `Agree.norm`; it is not a `module`.) -/
theorem Norm.of_agree (p q : Array Word) (t o l : Nat) (h : Agree p q t) (hk : o + l ≤ t)
    (hn : Norm q o l) : Norm p o l := by
  intro hl
  rw [h (o + (l - 1)) (by omega)]
  exact hn hl
grind_pattern [natop_grind] Norm.of_agree => Agree p q t, Norm q o l

/-- One step of Euclid: `(a, b) := (b % a, a)`. -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
def gcdStep : FunDecl := lfn (oa, la, ob, lb) locals (q, ql, ro, rl) {
  (q, ql, ro, rl) := call nat_divmod(ob, lb, oa, la);
  return (ro, rl, oa, la)
}

def gcdLoop : Stmt := lblk (oa, la, ob, lb) {
  while la != 0 {
    (oa, la, ob, lb) := call gcd_step(oa, la, ob, lb)
  }
}

/-- con-ron: ConRon/Arena/Core.lean:994-1035 ConRon.Arena.natOpResult -/
@[l_impl ConRon.Arena.natOpResult]
def natGcd : FunDecl := lfn (oa, la, ob, lb) {
  ⟪gcdLoop⟫;
  return (ob, lb)
}

/-- The pool functions with `nat_gcd`. -/
def natGcdProg : Prog := natDivProg ++ [("gcd_step", gcdStep), ("nat_gcd", natGcd)]

/- `gcd 12 18 = 6`; `gcd 0 5 = 5`. -/
#guard (run natGcdProg 100000 "nat_gcd" [0, 1, 1, 1]
  { words := #[(#[12, 18] ++ Array.replicate 40 0), #[2]] }).toOption.map
  (fun (r, m) => (r[1]!, m.words[0]![r[0]!.toNat]!)) == some (1, 6)
#guard (run natGcdProg 100000 "nat_gcd" [0, 0, 0, 1]
  { words := #[(#[5] ++ Array.replicate 40 0), #[1]] }).toOption.map (·.1) == some [0, 1]

section gcd
variable (p : Prog) (hpl : p.lookup "nat_limb" = some natLimb)
  (hps : p.lookup "sub_borrow" = some subBorrow) (hpc : p.lookup "add_carry" = some addCarry)
  (hp1 : p.lookup "div_shl1" = some divShl1) (hp2 : p.lookup "div_sub" = some divSub)
  (hp3 : p.lookup "div_add" = some divAdd) (hp4 : p.lookup "div_step" = some divStep)
  (hpt : p.lookup "nat_trim" = some natTrim) (hpd : p.lookup "nat_divmod" = some natDivmod)

include hpl hps hpc hp1 hp2 hp3 hp4 hpt hpd in
/-- `gcd_step` returns `(b % a, a)` as two normalised slices in use; the memory grew. -/
theorem gcdStep_spec (hpg : p.lookup "gcd_step" = some gcdStep) (n : Nat) (s₀ : St)
    (oa la ob lb : Word) (hok : PoolOK s₀.mem) (ha : SliceOK s₀.mem oa la)
    (hb : SliceOK s₀.mem ob lb) (hna : Norm (vpool s₀.mem) oa.toNat la.toNat) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "gcd_step" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧ PoolOK s'.mem ∧ Grows s₀.mem s'.mem ∧
      SliceOK s'.mem (r.headD 0) (r.tail.headD 0) ∧
      Norm (vpool s'.mem) (r.headD 0).toNat (r.tail.headD 0).toNat ∧
      pv (vpool s'.mem) (r.headD 0).toNat (r.tail.headD 0).toNat =
        pv (vpool s₀.mem) ob.toNat lb.toNat % pv (vpool s₀.mem) oa.toNat la.toNat ∧
      r.tail.tail.headD 0 = oa ∧ r.tail.tail.tail.headD 0 = la; ⊤⦄ := by
  rw [invoke_eq _ hpg]
  simp only [callFn, gcdStep]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc, setLocs,
        natDivmod_spec p hpl hps hpc hp1 hp2 hp3 hp4 hpt hpd n] <;>
      -- depth, not search: four results set four locals
      finish (gen := 20)

/-- The Euclid loop's invariant: both slices normalised and in use, their `gcd` is `G`, and the
memory grew from `m₀`. -/
def GcdInv (G : Nat) (m₀ : Mem) (s : St) : Prop :=
  PoolOK s.mem ∧ Grows m₀ s.mem ∧
  SliceOK s.mem (s.loc 0) (s.loc 1) ∧ SliceOK s.mem (s.loc 2) (s.loc 3) ∧
  Norm (vpool s.mem) (s.loc 0).toNat (s.loc 1).toNat ∧
  Norm (vpool s.mem) (s.loc 2).toNat (s.loc 3).toNat ∧
  Nat.gcd (pv (vpool s.mem) (s.loc 0).toNat (s.loc 1).toNat)
    (pv (vpool s.mem) (s.loc 2).toNat (s.loc 3).toNat) = G

def GcdPost (G : Nat) (m₀ : Mem) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ PoolOK s'.mem ∧ Grows m₀ s'.mem ∧ SliceOK s'.mem (s'.loc 2) (s'.loc 3) ∧
  Norm (vpool s'.mem) (s'.loc 2).toNat (s'.loc 3).toNat ∧
  pv (vpool s'.mem) (s'.loc 2).toNat (s'.loc 3).toNat = G

include hpl hps hpc hp1 hp2 hp3 hp4 hpt hpd in
theorem gcdLoop_spec (hpg : p.lookup "gcd_step" = some gcdStep) (G : Nat) (m₀ : Mem) (n : Nat)
    (s₀ : St) (h : GcdInv G m₀ s₀) :
    ⦃fun s => s = s₀⦄ exec p n gcdLoop ⦃fun r s' => GcdPost G m₀ r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [GcdInv, GcdPost] at h ⊢
    rw [exec, step_while (w := gcdLoop) rfl]
    sym only [lang_grind, arena_grind, natop_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        gcdStep_spec p hpl hps hpc hp1 hp2 hp3 hp4 hpt hpd hpg n] <;>
      finish [GcdInv, GcdPost]

include hpl hps hpc hp1 hp2 hp3 hp4 hpt hpd in
theorem gcdLoop_step_spec (hpg : p.lookup "gcd_step" = some gcdStep) (G : Nat) (m₀ : Mem)
    (n : Nat) (s₀ : St) (h : GcdInv G m₀ s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) gcdLoop ⦃fun r s' => GcdPost G m₀ r s'; ⊤⦄ :=
  Triple.step_exec (gcdLoop_spec p hpl hps hpc hp1 hp2 hp3 hp4 hpt hpd hpg G m₀ (n + 1) s₀ h)

include hpl hps hpc hp1 hp2 hp3 hp4 hpt hpd in
/-- `nat_gcd` returns a normalised slice `(o, l)` in use that denotes `Nat.gcd a b`; the memory
grew. -/
theorem natGcd_spec (hpg : p.lookup "gcd_step" = some gcdStep)
    (hpn : p.lookup "nat_gcd" = some natGcd) (n : Nat) (s₀ : St)
    (oa la ob lb : Word) (hok : PoolOK s₀.mem) (ha : SliceOK s₀.mem oa la)
    (hb : SliceOK s₀.mem ob lb) (hna : Norm (vpool s₀.mem) oa.toNat la.toNat)
    (hnb : Norm (vpool s₀.mem) ob.toNat lb.toNat) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_gcd" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧ PoolOK s'.mem ∧ Grows s₀.mem s'.mem ∧
      SliceOK s'.mem (r.headD 0) (r.tail.headD 0) ∧
      Norm (vpool s'.mem) (r.headD 0).toNat (r.tail.headD 0).toNat ∧
      pv (vpool s'.mem) (r.headD 0).toNat (r.tail.headD 0).toNat =
        Nat.gcd (pv (vpool s₀.mem) oa.toNat la.toNat)
          (pv (vpool s₀.mem) ob.toNat lb.toNat); ⊤⦄ := by
  rw [invoke_eq _ hpn]
  simp only [callFn, natGcd]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs,
        gcdLoop_step_spec p hpl hps hpc hp1 hp2 hp3 hp4 hpt hpd hpg
          (Nat.gcd (pv (vpool s₀.mem) oa.toNat la.toNat)
            (pv (vpool s₀.mem) ob.toNat lb.toNat)) s₀.mem n] <;>
      finish [GcdInv, GcdPost]

end gcd

end L.Arena
