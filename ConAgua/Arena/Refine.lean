import ConRon.Arena.Monad
import ConAgua.Arena.NatAdd
import Std.Data.DTreeMap.Internal.Operations
import Std.WP.Triple.SpecLemmas
import ConAgua.Arena.GrindAttr
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# Refinement of an arena-tier function: L code against `AM := StateT AState (Except CheckError)`

The first refinement of L code against con-ron's arena twin (`vendor/con-ron/ConRon/Arena`). The
arena represents a `Nat` literal as a Lean `Nat` inside an interned `lit` node
(`ENodeView.lit (.natVal n)`, `Arena/Store.lean`); its arithmetic is Lean's `Nat` (`natOpResult`,
`Arena/Core.lean:1001`). In L, a literal is a slice of the limb pool, and the arithmetic is
`nat_add`/`nat_mul` (`ConAgua/Arena/NatAdd.lean`, `NatMul.lean`).

The function refined here is the `Nat.add` arm of `natOpResult`:

```lean
else if c == ad then do let x ← internE (.lit (.natVal (a + b))); pure (some x)
```

(`natAddArm` below is that arm verbatim). Its L counterpart `nat_add_lit` adds two pool slices
with `nat_add` and interns the result with an L function `intern_lit(o, l)`.

## The spec shape for a `StateT AState` function

* **The state relation is a parameter.** `R : Mem → AState → Prop` relates an L memory to an
  arena state. Its content (the pool holds every `lit` node's limbs, the node tables mirror the
  arena's, …) is milestone 4's; here the theorem assumes exactly what it uses of it:
  `R` implies nothing about the pool beyond what the specs carry, and **appending to the pool
  preserves `R`** (`hgrow`): nothing the arena refers to lies above the top.
* **The arena result is read off with named run projections**, `AM.ok x a` (the run succeeds),
  `AM.st x a` (its final state) and `AM.res x a` (its result). The post of an L triple is then
  `AM.ok f a₀ ∧ R s'.mem (AM.st f a₀) ∧ AM.res f a₀ = decode r`: equations about named
  functions, with no `∃` over the final arena state, no disjunction and no `fun`. `AM.ok_bind`,
  `AM.st_bind`, `AM.res_bind` (and the `pure` ones) take them through a `do` block, as `grind`
  rewrites.
* **The arena state is a ghost.** `a₀` is a parameter of the theorem with the hypothesis
  `R s₀.mem a₀`; it never enters the L precondition, which stays `s = s₀`.
* **What is not implemented yet is a hypothesis, not a `sorry`.** `intern_lit`'s spec (`hI`)
  is stated in the same shape; milestone 4 (the hash-consing tables) discharges it.

Direction: the L run determines the arena run. If the L function returns `r`, then the arena
function does not fail, its result is `some (decE (r.headD 0))`, and the final states are related. (A
`native` capacity failure of the arena, or an L `abort` on a full pool, claim nothing.)
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order
open ConRon.Arena (AM AState EIdx ENodeView internE)

namespace L.Arena

/-! ## Run projections of an `AM` computation -/

/-- The run of `x` from `a` succeeds. -/
def AM.ok {α : Type} (x : AM α) (a : AState) : Prop :=
  match x.run a with
  | .ok _ => True
  | .error _ => False

/-- The final arena state of the run (`a` on failure). -/
def AM.st {α : Type} (x : AM α) (a : AState) : AState :=
  match x.run a with
  | .ok (_, a') => a'
  | .error _ => a

/-- The result of the run (`default` on failure). -/
def AM.res {α : Type} [Inhabited α] (x : AM α) (a : AState) : α :=
  match x.run a with
  | .ok (v, _) => v
  | .error _ => default

theorem AM.run_of_ok {α : Type} [Inhabited α] (x : AM α) (a : AState) (h : AM.ok x a) :
    x.run a = .ok (AM.res x a, AM.st x a) := by
  simp only [AM.ok, AM.res, AM.st] at *
  split at h <;> simp_all

@[arena_grind =] theorem AM.ok_pure {α : Type} (v : α) (a : AState) :
    AM.ok (pure v : AM α) a = True := rfl

@[arena_grind =] theorem AM.st_pure {α : Type} (v : α) (a : AState) :
    AM.st (pure v : AM α) a = a := rfl

@[arena_grind =] theorem AM.res_pure {α : Type} [Inhabited α] (v : α) (a : AState) :
    AM.res (pure v : AM α) a = v := rfl

@[arena_grind =] theorem AM.ok_bind {α β : Type} [Inhabited α] (x : AM α) (f : α → AM β)
    (a : AState) : AM.ok (x >>= f) a = (AM.ok x a ∧ AM.ok (f (AM.res x a)) (AM.st x a)) := by
  simp only [AM.ok, AM.res, AM.st, StateT.run_bind]
  cases x.run a <;> simp [bind, Except.bind]

theorem AM.st_bind {α β : Type} [Inhabited α] (x : AM α) (f : α → AM β) (a : AState)
    (h : AM.ok (x >>= f) a) : AM.st (x >>= f) a = AM.st (f (AM.res x a)) (AM.st x a) := by
  simp only [AM.ok, AM.res, AM.st, StateT.run_bind] at *
  cases hx : x.run a with
  | error e => simp [hx, bind, Except.bind] at h
  | ok q =>
    simp only [hx, bind, Except.bind] at h ⊢
    split at h <;> simp_all
grind_pattern [arena_grind] AM.st_bind => AM.st (x >>= f) a

theorem AM.res_bind {α β : Type} [Inhabited α] [Inhabited β] (x : AM α) (f : α → AM β)
    (a : AState) (h : AM.ok x a) : AM.res (x >>= f) a = AM.res (f (AM.res x a)) (AM.st x a) := by
  simp only [AM.ok, AM.res, AM.st, StateT.run_bind] at *
  cases hx : x.run a with
  | error e => simp [hx] at h
  | ok q => simp [bind, Except.bind]
grind_pattern [arena_grind] AM.res_bind => AM.res (x >>= f) a

/-! ## Handles -/

/-- An expression handle as an L word, and back. -/
def decE (w : Word) : EIdx := ConRon.Arena.Idx.ofWord w.toUInt32

/-! ## The arena function and its L counterpart -/

/-- The `Nat.add` arm of `natOpResult` (`Arena/Core.lean:1005`), verbatim. -/
def natAddArm (a b : Nat) : AM (Option EIdx) := do
  let x ← internE (.lit (.natVal (a + b)))
  pure (some x)

/-- `nat_add_lit(oa, la, ob, lb)`: add two literal slices and intern the sum. -/
-- con-ron: ConRon/Arena/Core.lean:994-1035 ConRon.Arena.natOpResult
@[l_impl ConRon.Arena.natOpResult]
def natAddLit : FunDecl := lfn (oa, la, ob, lb) locals (o, l, h) {
  o := CTL.u64[0];
  l := call nat_add(oa, la, ob, lb);
  h := call intern_lit(o, l);
  return h
}

section refine
variable (p : Prog) (hpl : p.lookup "nat_limb" = some natLimb)
  (hpc : p.lookup "add_carry" = some addCarry) (hpt : p.lookup "nat_trim" = some natTrim)
  (hpa : p.lookup "nat_add" = some natAdd) (hpn : p.lookup "nat_add_lit" = some natAddLit)
  (R : Mem → AState → Prop)
  (hpool : ∀ m a, R m a → PoolOK m)
  (hgrow : ∀ m m' a, R m a → Grows m m' → R m' a)
  /- The spec of `intern_lit` that milestone 4 proves: interning the slice `(o, l)` is the
  arena's `internE` of the literal the slice denotes. -/
  (hI : ∀ (a₀ : AState) (n : Nat) (s₀ : St) (o l : Word), R s₀.mem a₀ →
    SliceOK s₀.mem o l → Norm (vpool s₀.mem) o.toNat l.toNat →
    (s₀.mem.flag = 0 → o.toNat < 2 ^ 40) →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_lit" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀ ∧
      R s'.mem (AM.st (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀) ∧
      AM.res (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀ = decE (r.headD 0); ⊤⦄)

include hpl hpc hpt hpa hpn hpool hgrow hI in
/-- **`nat_add_lit` refines `natOpResult`'s `Nat.add` arm.** If the L function returns `r`, the
arena arm on the related state succeeds, returns the handle `r`, and ends in a related state. -/
theorem natAddLit_refines (n : Nat) (s₀ : St) (a₀ : AState) (hR : R s₀.mem a₀)
    (oa la ob lb : Word) (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb)
    (hmode : ModeOK s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_add_lit" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (natAddArm (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀ ∧
      R s'.mem (AM.st (natAddArm (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀) ∧
      AM.res (natAddArm (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀ = some (decE (r.headD 0)); ⊤⦄ := by
  have hok := hpool _ _ hR
  have hm0 : s₀.mem.flag = 0 → s₀.mem.top.toNat < 2 ^ 40 := fun hf => by
    rcases hmode with h | h
    · exact absurd hf h
    · exact h
  rw [invoke_eq _ hpn]
  simp only [callFn, natAddLit]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc, setLocs, ld64, natAdd_spec p hpl hpc hpt hpa n,
        hI a₀ n] <;>
      finish [natAddArm]

include hpl hpc hpt hpa hpn hpool hgrow hI in
/-- From an L run to the arena run: if `nat_add_lit` returns `r` with final memory `m'`, the
arena arm on any related state returns the handle `r` and ends in a state related to `m'`. -/
theorem natAddLit_run (fuel : Nat) (m : Mem) (a₀ : AState) (hR : R m a₀)
    (oa la ob lb : Word) (ha : SliceOK m oa la) (hb : SliceOK m ob lb) (hmode : ModeOK m)
    (r : List Word) (m' : Mem)
    (h : run p fuel "nat_add_lit" [oa, la, ob, lb] m = .ok (r, m')) :
    ∃ a', (natAddArm (pv (vpool m) oa.toNat la.toNat) (pv (vpool m) ob.toNat lb.toNat)).run
      a₀ = .ok (some (decE (r.headD 0)), a') ∧ R m' a' := by
  simp only [run] at h
  cases hr : (invoke p (exec p fuel) "nat_add_lit" [oa, la, ob, lb]).run
      { mem := m, loc := Locals.init [] } with
  | error e => simp [hr, Except.map] at h
  | ok rs =>
    simp only [hr, Except.map] at h
    injection h with h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    have := M.of_run (P := fun s => s = { mem := m, loc := Locals.init [] }) rfl hr
      (natAddLit_refines p hpl hpc hpt hpa hpn R hpool hgrow hI fuel _ a₀ hR oa la ob lb ha hb hmode)
    obtain ⟨-, hok, hR', hres⟩ := this
    exact ⟨_, by rw [AM.run_of_ok _ _ hok, hres], hR'⟩

end refine

end L.Arena
