module

public import ConAgua.L.Logic
import ConAgua.L.Notation
-- (the interpreter's equation lemmas, realized there: a second copy here would make the import
-- gate credit this module for them in every module that uses them)
import ConAgua.Front.Preserve
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# L: the counted loop

`for j < n { body }` (`Notation.lean`) is the loop `while j < n { body; j += 1 }`, which is
`forS j n body` here (`snoc` appends the step `j += 1` inside the block's right-nested `seq`, as the
notation writes it). Its rule, proved once:

* `Triple.forUp`: an invariant `I` that each iteration keeps while `j < n` (the body's triple with
  post `ForPost I Q j`: on `normal` the invariant after `j += 1`, on `break` and `return` the loop's
  post) and that gives the loop's post when `j < n` fails is a triple of the loop at every fuel.
  A loop spec of a `for` is then its invariant and one `vcgen` of the body, without an induction
  on the fuel. `Triple.forUp_at` is the rule at a start state.
* `Triple.forUp_pre`: the same rule for a named loop block, in the shape `⦃s = s₀ ∧ P s⦄ exec p k w
  ⦃Q⦄` of a hand loop spec; it takes the loop's whole body (the step included, post `LoopPost`),
  so that `hw` is `rfl` without restating the body.
* `forUp_succ_toNat`: the step does not wrap (`j < n`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L

/-- `s` followed by `t`, inside `s`'s right-nested `seq` (the block `{ s₁; …; sₖ; t }` for the
block `s = { s₁; …; sₖ }`). -/
def Stmt.snoc : Stmt → Stmt → Stmt
  | .seq a b, t => .seq a (Stmt.snoc b t)
  | s, t => .seq s t

/-- Appending inside the block runs as running the block and then `t`. -/
theorem step_snoc (p : Prog) (k : Stmt → M Sig) (s t : Stmt) :
    step p k (s.snoc t) = step p k (.seq s t) := by
  induction s with
  | seq a b _ ihb =>
    simp only [Stmt.snoc, step, ihb, bind_assoc]
    congr 1; funext r; cases r <;> simp
  | _ => rfl

/-- The counted loop `while j < n { body; j += 1 }`. -/
def forS (j n : Var) (body : Stmt) : Stmt :=
  .while (.cmp .ult (.var j) (.var n)) (body.snoc (.set j (.bin .add (.var j) (.const 1))))

/-- What one iteration's body establishes: on `normal`, the invariant after `j += 1`; on `break`,
the loop's post with signal `normal`; on `return`, the loop's post. -/
def ForPost (I : St → Prop) (Q : Sig → St → Prop) (j : Var) : Sig → St → Prop
  | .normal, s => I (s.setLoc j (s.loc j + 1))
  | .brk, s => Q .normal s
  | .ret v, s => Q (.ret v) s

@[simp] theorem ForPost_normal (I : St → Prop) (Q : Sig → St → Prop) (j : Var)
    (s : St) : ForPost I Q j .normal s = I (s.setLoc j (s.loc j + 1)) := rfl
@[simp] theorem ForPost_brk (I : St → Prop) (Q : Sig → St → Prop) (j : Var)
    (s : St) : ForPost I Q j .brk s = Q .normal s := rfl
@[simp] theorem ForPost_ret (I : St → Prop) (Q : Sig → St → Prop) (j : Var)
    (v : List Word) (s : St) : ForPost I Q j (.ret v) s = Q (.ret v) s := rfl

/-- **The counted-loop rule.** An invariant `I` that the body keeps (with `j += 1` after it)
while `j < n`, and that gives the post when `j < n` fails, gives the loop's triple at every
fuel. -/
theorem Triple.forUp {p : Prog} {w body : Stmt} {j n : Var} (hw : w = forS j n body)
    (I : St → Prop) (Q : Sig → St → Prop)
    (hexit : ∀ s, I s → ¬ s.loc j < s.loc n → Q .normal s)
    (hbody : ∀ k s₀, ⦃fun s => s = s₀ ∧ I s ∧ s.loc j < s.loc n⦄ step p (exec p k) body
      ⦃fun r s' => ForPost I Q j r s'; ⊤⦄) :
    ∀ k s₀, ⦃fun s => s = s₀ ∧ I s⦄ exec p k w ⦃Q; ⊤⦄ := by
  intro k
  induction k with
  | zero => intro s₀; vcgen [exec] <;> grind
  | succ k ih =>
    intro s₀
    rw [exec, step_while (c := .cmp .ult (.var j) (.var n)) hw, step_snoc]
    vcgen [step, evalC, evalE, setLoc, hbody k, ih]
    all_goals (subst_vars; simp_all [Cmp.eval, BinOp.eval])

/-- The counted-loop rule at a start state. -/
theorem Triple.forUp_at {p : Prog} {w body : Stmt} {j n : Var} (hw : w = forS j n body)
    (I : St → Prop) (Q : Sig → St → Prop)
    (hexit : ∀ s, I s → ¬ s.loc j < s.loc n → Q .normal s)
    (hbody : ∀ k s₀, ⦃fun s => s = s₀ ∧ I s ∧ s.loc j < s.loc n⦄ step p (exec p k) body
      ⦃fun r s' => ForPost I Q j r s'; ⊤⦄) (k : Nat) (s₀ : St) (hI : I s₀) :
    ⦃fun s => s = s₀⦄ exec p k w ⦃Q; ⊤⦄ :=
  ⟨fun s hs => (Triple.forUp hw I Q hexit hbody k s₀).le_wp s ⟨hs, by subst hs; exact hI⟩⟩

/-- What one iteration of a loop's whole body (the step `j += 1` included) establishes: on
`normal`, the invariant; on `break`, the loop's post with signal `normal`; on `return`, the loop's
post. -/
def LoopPost (I : St → Prop) (Q : Sig → St → Prop) : Sig → St → Prop
  | .normal, s => I s
  | .brk, s => Q .normal s
  | .ret v, s => Q (.ret v) s

@[simp] theorem LoopPost_normal (I : St → Prop) (Q : Sig → St → Prop) (s : St) :
    LoopPost I Q .normal s = I s := rfl
@[simp] theorem LoopPost_brk (I : St → Prop) (Q : Sig → St → Prop) (s : St) :
    LoopPost I Q .brk s = Q .normal s := rfl
@[simp] theorem LoopPost_ret (I : St → Prop) (Q : Sig → St → Prop) (v : List Word) (s : St) :
    LoopPost I Q (.ret v) s = Q (.ret v) s := rfl

/-- **The counted-loop rule for a named loop block**, in the shape of a hand loop spec
`⦃s = s₀ ∧ P s⦄ exec p k w ⦃Q⦄`: `hw` is `rfl` (the condition `j < n` and the whole body `B`, the
step included, are read off the block), the invariant `I` (which may name `s₀`) holds at the start
when `P` does, each iteration keeps it while `j < n`, and it gives the post when `j < n` fails. -/
theorem Triple.forUp_pre {p : Prog} {w B : Stmt} {j n : Var} {P : St → Prop} {s₀ : St}
    (hw : w = .while (.cmp .ult (.var j) (.var n)) B) (I : St → Prop) {Q : Sig → St → Prop}
    (hI : P s₀ → I s₀) (hexit : ∀ s, I s → ¬ s.loc j < s.loc n → Q .normal s)
    (hbody : ∀ k s₁, ⦃fun s => s = s₁ ∧ I s ∧ s.loc j < s.loc n⦄ step p (exec p k) B
      ⦃fun r s' => LoopPost I Q r s'; ⊤⦄) (k : Nat) :
    ⦃fun s => s = s₀ ∧ P s⦄ exec p k w ⦃Q; ⊤⦄ := by
  suffices h : ∀ k s₁, ⦃fun s => s = s₁ ∧ I s⦄ exec p k w ⦃Q; ⊤⦄ from
    ⟨fun s ⟨hs, hP⟩ => (h k s₀).le_wp s ⟨hs, by subst hs; exact hI hP⟩⟩
  intro k
  induction k with
  | zero => intro s₁; vcgen [exec] <;> grind
  | succ k ih =>
    intro s₁
    rw [exec, step_while (c := .cmp .ult (.var j) (.var n)) hw]
    vcgen [evalC, evalE, hbody k, ih]
    all_goals (subst_vars; simp_all [Cmp.eval])

/-! ### Tests: the `for` sugar is `forS` -/

example : (lblk (i, n, x) { for i < n { x += i } }) = forS 0 1 (lblk (i, n, x) { x += i }) := rfl

example : (lblk (i, n, x, y) { for i < n { x += i; if x == 3 { break }; y := x } }) =
    forS 0 1 (lblk (i, n, x, y) { x += i; if x == 3 { break }; y := x }) := rfl

/-- Nested, and the plain form it stands for. -/
example : (lblk (i, j, n, x) { for i < n { j := 0; for j < i { x += j } } }) =
    (lblk (i, j, n, x) { while i < n { j := 0; while j < i { x += j; j += 1 }; i += 1 } }) := rfl

end L
