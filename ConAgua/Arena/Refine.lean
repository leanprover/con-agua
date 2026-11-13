module

public import ConRon.Arena.Monad
public import ConAgua.Arena.NatAdd
public import Std.Data.DTreeMap.Internal.Operations
import Std.WP.Triple.SpecLemmas
import ConAgua.Arena.GrindAttr
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

@[expose] public section

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

(`natAddArm`, `NatSizedRef.lean`, is that arm, now behind the size refusal). Its L counterpart `nat_add_lit` adds two pool slices
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

/-- `nat_add_lit(oa, la, ob, lb)`: add two literal slices and intern the sum, refused above the
run's maximum `Nat` size (`lit_nat_sized`, the twin's `litNatSized (a + b)`). -/
-- con-ron: ConRon/Arena/Core.lean:1114-1160 ConRon.Arena.natOpResult
-- con-ron: CHANGED since 4ca283d1 — `ConRon.Arena.natOpResult` is gone upstream; re-check the L code and its proofs, then delete this line
-- con-ron: ConRon/Arena/Core.lean:1059-1069 ConRon.Arena.litNatSized
@[no_expose, l_impl ConRon.Arena.natOpResult ConRon.Arena.litNatSized]
def natAddLit : FunDecl := lfn (oa, la, ob, lb) locals (o, l, h) {
  o := CTL.u64[0];
  l := call nat_add(oa, la, ob, lb);
  h := call lit_nat_sized(o, l);
  return h
}


end L.Arena
