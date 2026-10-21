/-
Gap: `vcgen` now splits a `∧` postcondition into one VC per conjunct, so a
`grind_pattern` whose trigger term occurs in only ONE conjunct no longer
fires for the VCs of the OTHER conjuncts. `sym ... => vcgen ... <;> finish`
proofs that relied on facts derived from a sibling conjunct now fail.

Toolchains:
  passes: leanprover/lean4:v4.35.0, nightly-2026-09-21, nightly-2026-10-05
  fails:  nightly-2026-10-06, nightly-2026-10-20, nightly-2026-10-21 (latest
          at time of writing)
Bisect (nightly granularity, `lean-bisect --nightly-only`):
  nightly-2026-10-05 (c3286a4a1b85) good .. nightly-2026-10-06 (03eeb6f90f5b) bad.
  That range has 15 commits; the only `vcgen` changes in it are
  leanprover/lean4#15487 "fix: split a `∧` on the RHS of a `vcgen` entailment"
  (1e15c3fdf8) and #15491 "feat: recognize more forms of conjunctive spec
  preconditions in `vcgen`" (dde01e0231). Commit level (both built from
  source): 1e15c3fdf8 (#15487) FAILS, its parent c96933c169 PASSES — so it
  is lean4#15487.

Found in con-leche's `ConLeche/Verify/Cached/KnotC.lean` (vendored into
con-agua): the memo-hit lemmas `CSOK.*_hit` conclude `Runs (...) r ∧
WScoped d r` and are triggered by `grind_pattern ... => CSOK .., s.xC[i]?,
Runs (fueledFns ..).x d i) r`. The spec's post is `CSOK .. ∧ Runs .. ∧
WScoped d r`. On v4.35.0 `vcgen` emits ONE VC with the whole conjunction,
so the `Runs` term is in the e-graph while `grind` proves `WScoped`; on the
new nightlies the `WScoped` conjunct is its own VC, without any `Runs` term,
so the lemma never fires. The same change broke ~a dozen proofs in con-ron's
Bridge tier (the explicit-term ones, `vcgen; subst_vars; exact ⟨rfl, ..⟩`,
now see several goals with the `rfl` conjuncts already closed).

Misleading diagnostic: in the failing goal's `grind` diagnostics the lemma
still shows "Theorem Instance Count ↦ 1" (below: `hit ↦ 1`), although no
instance can be built in that VC; the count does not refer to that goal.
This sent the first investigation (vendor/README.md history) in the wrong
direction ("the conjunction is not re-split").

EXPECTED (v4.35.0 .. nightly-2026-10-05): no error (only the `sorry` warning
of `hit`).

OBSERVED (nightly-2026-10-06 .. nightly-2026-10-21):

    error: `finish` failed
    case vc2
    ...
    x✝¹ : lk i = some r✝
    h✝¹ : ¬R r✝
    ⊢ False
    ...
      [ematch] E-matching patterns
        [thm] hit: [Q #2 #1]
    ...
      [thm] hit ↦ 1

Workaround (what con-agua ships): add a companion lemma for the conjunct,
triggered by a term that IS in its VC, e.g.
  theorem hit_R (hl : lk i = some r) : R r := (hit hl).2
  grind_pattern hit_R => lk i, R r

Run: `lean vcgen-conj-split-grind-trigger.lean` (plain Lean, `import Lean`
only, so that `vcgen`'s syntax is available on v4.35.0 too).
-/
import Lean
set_option experimental.vcgen true
open Std.WP

opaque lk : Nat → Option Nat
opaque Q : Nat → Nat → Prop
opaque R : Nat → Prop

theorem hit {i r : Nat} (hl : lk i = some r) : Q i r ∧ R r := sorry
grind_pattern hit => lk i, Q i r

def look (i : Nat) : StateM Unit Nat :=
  match lk i with
  | some r => pure r
  | none => pure 0

example (i : Nat) (h : lk i ≠ none) :
    ⦃fun _ => True⦄ look i ⦃fun r _ => Q i r ∧ R r⦄ := by
  sym only [hit] =>
    vcgen [look] <;> finish
