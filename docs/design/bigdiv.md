# Lane bigdiv: `nat_divmod` one quotient limb at a time (2026-11-18)

## Goal
The user asked for bignum algorithms that are no worse than con-ron's
(de06320f, task #158: `div_mod` became Knuth's algorithm D). On master, L's `nat_divmod` was
restoring division one *bit* at a time: 64 passes of `div_shl1` + `div_sub` (+ `div_add`) over the
remainder for each dividend limb, about 64 × la × lb word steps. The target was con-ron's
complexity, O(la · lb), with a public spec that does not change.

## Design
L has no division instruction (BinOp: add sub mul and or xor shl shr mulhi), so the 2-by-1 word
division is built from `mulhi`.

* **`div_2by1(u1, u0, d, v)`** (`NatDivWord.lean`): returns `⌊(u1·2^64 + u0)/d⌋` and the
  remainder, for `u1 < d`. The estimate is Möller and Granlund's (`udiv_qrnnd_preinv`: one `mul`,
  one `mulhi` and two conditional fixes) with the reciprocal `v`. Two verified register loops
  follow: step `q` down while `q·d > u`, and up while `u - q·d ≥ d`. **The result is exact
  whatever `v` is.** Correctness never depends on the reciprocal; only speed does. With the
  exact reciprocal neither loop runs. This was tested on 3000 random and edge `d`, `u`; it is not
  proved, just as con-ron tests rather than proves Knuth's "at most two corrections".
* **`div_recip(d)`**: `v = ⌊(2^128-1)/d⌋ - 2^64` for a normalised `d`.
  * It starts from the tangent of `1/x` at `3/4`, which is below the true value and good to
    about 3 bits.
  * Five Newton steps follow: `v += e + mulhi(v, e)`, where `e` is the top word of
    `2^128 - d(2^64+v)`.
  * The result is at most 2 below the exact value, never above. A Python model checked this on
    200 000 random `d` plus the edge values.
  * One `div_2by1` then makes it exact.
  * Cost: about 100 instructions, once per `nat_divmod` call.
  * The first prototype used a 64-step bit-serial reciprocal. On a 1×1-limb division that
    cost about 1 150 instructions more than the Newton version (micro table below).
* **`div_norm(x)`**: the shift `s ≤ 63` that sets the top bit, in six halving steps.
* **`lb = 1`** (`div_mod1`, `d1Loop`): con-ron's `u128` case.
  * One `div_2by1` per dividend limb, with the remainder in a register.
  * The divisor is normalised (`d = b·2^s`). Each dividend limb is read shifted on the fly as
    `(r + x>>(64-s), x<<s)`, so no buffer is needed. The remainder is kept as `r·2^s` and
    shifted back at the end.
* **`lb ≥ 2`** (`div_modk`, `dkLoop`, `div_kstep`): Knuth's algorithm D.
  * It runs on a copy of `a` with one zero limb on top. This is the work region `w`, placed
    after the `la - lb + 1` quotient limbs.
  * Step `j` works on the window `w[j‥j+lb]`, which holds `rem·2^64 + a[j]`.
  * The estimate is `q̂ = min(⌊U/D⌋, 2^64-1)`. Here `U` is the window's top three limbs and `D`
    is `b`'s top two limbs, both read shifted left by `s`. So `D` is normalised, as con-ron
    normalises both operands, but without making copies.
  * `div_submul` subtracts `q̂·b` in place in a single pass, using `mulhi` for the high words.
    It returns the borrow out of the top limb.
  * While the window is negative, `div_add` adds `b` back and `q̂` steps down by one (con-ron's
    `dm_correct`).
  * The proof needs only `q̂ ≥ ⌊T/b⌋` (`knuth_est`, as in con-ron) and that each correction
    keeps that bound.
* `lb = 0` or `la < lb`: the result is `(0, a)`.
* `nat_divmod` dispatches to `div_mod1` and `div_modk`. Callers and the spec are unchanged,
  except that the `p.lookup` hypotheses are now bundled in `DivFns p`.
* The bit-serial helpers `div_shl1`, `div_sub` and `div_step`, with their specs, are deleted.
  So are `bitLoop`, `limbLoop`, `rzLoop`, and the `sh`/bit lemmas that only they used.

## Complexity
* Before: about 64 · la · lb limb steps.
* After: (la - lb + 1) · lb multiply-subtract steps, plus O(1) per call for the reciprocal.
* `nat_gcd` (Euclid through `gcd_step`) inherits the change.

## Measurements
See "Final measurements" below. Two methods were used:
* Micro: `instructions:u` per operation, computed as (run − setup)/K.
  * Each fixture is exported with lean4export at v4.35.0-rc3.
  * The run module checks K operations, 50 per theorem
    (`Nat.add (f a b) (Nat.add …) = S := rfl`).
  * The setup module is the same with `Nat.add` in place of the operation, plus
    `theorem dep : @Nat.div = @Nat.div` in both modules, so the definition's own check is not
    counted.
  * The numbers are therefore the operation minus a `Nat.add` of the same operands.
  * Generator and runner: `/home/joachim/.claude/jobs/e879b30f/tmp/bigdiv-bench/` (genmb.py,
    mbrun.py). These are not in the repository.
* End to end: `scripts/bench.py`, interleaved randomised rounds, on gf3 (con-ron's
  `_tmp/gf3/gf3.ndjson`) and `Init` (init435).

## Proof notes
* Pure facts are in `NatDivFacts.lean`:
  * `top2_div`: the top two words of `V·2^s` read from the top limbs.
  * `knuth_est`.
  * `mod_shift_room`.
  * `submul_step`.
* Each in-place pass has its own module.
  * `NatDivSubmul.lean` holds `div_add` and `div_submul`. Lemmas in the goal's shape:
    `dsm_step_goal`, `dsm_top_goal`.
  * `NatDivKstep.lean` holds `div_kstep` (helper lane `bigdiv-kstep`). It splits the body
    into `kEst.snoc kTail` and uses `L.evalE_spec` loads.
  * `NatDivWord.lean` holds `div_norm`, `div_2by1` and `div_recip` (helper lane `bigdiv-word`).
* `NatDiv.lean` holds `div_mod1`, `div_modk` and the dispatching `nat_divmod`.
  * A new frame predicate `Same p q o o' n` says a window is a copy of another.
  * The pattern that worked: a lemma whose conclusion is the verification condition, with the
    pre-loop state passed through the named invariant hypothesis `h`. Examples: `d1_step_goal`,
    `dk_same_goal`, `dk_eq_goal`, `kinit_*`, `kfin_*`.
  * This means every variable of the lemma occurs in the goal or in `h`, so
    `apply … <;> grind` closes the side goals. Side conditions that are conjunctions of local
    equalities (`DkStep`) need `and_intros` before `grind`.
  * Picking hypotheses with `‹_ ∧ _›` hit `isDefEq` timeouts. A wrapper spec in the caller's
    shape (`div2by1_d1_spec`) avoided it.
* Heartbeats: `try` does not catch the heartbeat limit, and the limit counts the whole
  declaration. `divMod1_spec`, `dkLoop_spec` and `divModK_spec` raise it, with a comment.

## What went wrong
* A helper's `grind` on `divRecip_spec`'s last goals reached 18 GB and was killed by the
  watchdog. The tangent's `mulhi`/`if` hypotheses were in context. Moving that prefix into a
  named block with a frame-only spec, and closing the goals with targeted steps, brought it down
  to 1.2 GB.
* Loading `b`'s top limbs after the copy loop meant that facts about the loads had to be carried
  through two memory updates. Moving the loads before the copy made them loads from the entry
  memory, so `hnb` applies directly.
* Microbenchmark baseline: the first version subtracted a setup that did not mention `Nat.div`.
  As a result, checking `Nat.div`'s own definition (about 80 M instructions) was charged to the
  operations. The fix was the `dep` theorem in both modules.
