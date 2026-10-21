/-
Gap: compiler PANIC (not a clean error) when a `@[csimp]`-paired definition's
body uses the now-`unsafe` `Init.Util.withPtrEq` (deprecated 2026-09-21).

Toolchain: leanprover/lean4:nightly-2026-10-20 (also reproduces on at least
nightly-2026-10-14; not checked further back than that). Found while vendoring
con-leche's `ConLeche/Kernel/Name.lean` into con-agua (docs/survey.md §4,
PLAN.md): that file used the *old* (pre-2026-09-21, genuinely safe,
`:= k ()`) shape of `withPtrEq`, which was fine on nightly-2026-09-21 but
breaks here because `Init.Util.withPtrEq` itself became `unsafe`. The fix we
shipped is to vendor the old safe shape under our own name
(`vendor/con-leche/ConLeche/Util/PtrEq.lean`) rather than work around this
compiler bug — this file is only the minimal reproducer, isolated from
ConLeche entirely.

EXPECTED: three clean elaboration errors (the unsafe-in-kernel-declaration
error, the `show` failure, and then EITHER a clean compile of the `instance`
despite the upstream errors, or a fourth clean "failed to compile" error) —
in any case the Lean *process does not crash*.

OBSERVED: the first two errors are reported correctly, but compiling the
`instance : BEq Nat := ⟨myBeq⟩` declaration (by way of the `@[csimp]`
substitution machinery) crashes the whole `lean` process:

    error: Repro.lean:15:0: failed to compile definition, compiler IR check
    failed at `instBEqNat_repro._closed_0`. Error: unknown join point 'block_0'
    PANIC at _private.Lean.Compiler.LCNF.ExplicitBoxing.0.Lean.Compiler.LCNF.
    Code.explicitBoxing.tryCorrectLetDeclType
    Lean.Compiler.LCNF.ExplicitBoxing:301:45: unreachable code has been reached
    backtrace: ... (Lean.Compiler.LCNF.PassManager.run, explicitBoxing, ...)

So an earlier, already-reported elaboration error (the unsafe-declaration
kernel error) leaves enough of a malformed/partial state around for a later,
unrelated compiler pass (LCNF's explicit-boxing pass, while compiling the
`@[csimp]`-targeted closure) to hit an "unreachable code" assertion and abort
the process, instead of either skipping compilation of the already-erroneous
declaration or failing gracefully. This looks like an error-recovery gap in
the compiler pipeline after a kernel-rejected-as-unsafe declaration, not
something specific to `withPtrEq`.

To reproduce: `lean Repro.lean` (the content below), on
leanprover/lean4:nightly-2026-10-20 or later.
-/

import Init.Util

def myBeq (a b : Nat) : Bool := decide (a = b)

@[inline] def myBeqPtr (a b : Nat) : Bool :=
  withPtrEq a b (fun _ => decide (a = b)) (fun h => by subst h; simp)

theorem myBeqPtr_eq (a b : Nat) : myBeqPtr a b = decide (a = b) := by
  show decide (a = b) = decide (a = b)
  rfl

@[csimp] theorem myBeq_eq_myBeqPtr : @myBeq = @myBeqPtr := by
  funext a b; exact (myBeqPtr_eq a b).symm

instance : BEq Nat := ⟨myBeq⟩
