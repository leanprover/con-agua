# Lane slownat: the slow Nat modules (2026-10-25/26)

## Question
CI's cold build (4-core runner, `LEAN_NUM_THREADS=4`) spent 2293 s in `ConAgua.Arena.NatShl`, and
NatDiv 723 s, NatMul 659 s, NatAdd 410 s, NatShr 404 s, NatSub 370 s. Is something CI-specific?

## Diagnosis: nothing CI-specific
Each module elaborated alone, locally, under an RSS guard, `LEAN_NUM_THREADS=4`, machine load ~250 on 96 cores
(user CPU seconds; the modules run effectively single-threaded, user ~ real):

| module | CPU s | peak RSS |
|---|---|---|
| NatShl | 760 | 1.7 GB |
| NatDiv | 455 | 1.8 GB |
| NatMul | 268 | 3.1 GB |
| NatAdd | 172 | 1.9 GB |
| NatShr | 135 | 1.4 GB |
| NatSub | 121 | 1.5 GB |

The CI/local ratio is about 3 for every module (NatAdd 2.4, NatSub 3.0, NatShr 3.0, NatMul 2.5,
NatShl 3.0): slower runner cores and 4 Lean processes on 4 cores. Not memory-bound (at most 3 GB
per module), not threads (no parallelism inside these proofs). tierpool's "NatShl 51 s -> 134 s"
predates parmode's change to `PoolOK` (below) and was measured on a lighter machine.

## Causes
1. **`PoolOK`'s new disjunct** (parmode-inv, `top < 2^40 ∨ ptop0 ≤ size`): every Nat op does
   `simp only [PoolOK] at hok`, so `grind` case-split on it in every goal. NatShl's value goal:
   438 s -> 205 s from dropping it (`obtain ⟨…, -, …⟩ := hok`).
2. **`sym … => vcgen … <;> finish` on loops with tier-decoded loads**: the `POOL⦃r + i⦄` index
   `(r + i) >>> 40`, `&&& M` is copied into every `setLoc` of the chain `finish` crawls (PLAN
   lesson). NatDiv's three in-place passes 11 + 124 + 203 s -> 7 + 13 + 12 s, NatAdd's and NatSub's loops 79/69 s -> ~20 s,
   with the plain `vcgen` + `simp only [St.setLoc_loc, …]` + `grind` recipe.
3. **`grind` lost in its own search on arithmetic goals.** NatShl's loop step (127 s), its result
   value (2 goals, 570 + 167 s), NatMul's column step (145 s): `grind?` finds a proof with a dozen
   instances, but the generic multi-patterns (`pv_succ`, `pv_set_succ`, `wt_succ`, `wt_add`) and
   the model-based theory combination (splits on `UInt64` equalities in contexts full of abort
   conditions) make the search take minutes. `grind only [the lemmas grind? lists]` fails
   without the anchors. Fix: a lemma in the goal's own shape (`shl_step_goal`, `shl_result_goal`,
   `mul_step_goal`), proved once by explicit rewrites, applied with `with_reducible apply`; its
   side conditions are easy `grind` goals. Each goal is down to 2-13 s.
   Pitfalls: a lemma variable not in the conclusion becomes a metavariable that `grind` cannot
   assign; picking it up with `assumption` (or `‹_ ∧ _›`) unifies against hypotheses about
   `vpool` and timed out at 5 GB (whnf of the `2^41`-element `Array.ofFn`). Restate so every
   variable occurs in the conclusion (NatShl: fold `2^k = sh s * wt w` into the loop equation's
   right-hand side).
4. `simp only [St.setLoc, St.setLocs, Locals.init, …]` (unfolding) plus `and_intros` in
   natMul_spec/natShr_spec: 42 goals instead of 12; the `setLoc` lemma set instead.

## Results (wall seconds of `lake build`, same loaded machine)
NatShl 833 -> 127, NatDiv 347 -> 105, NatMul 197 -> 73, NatAdd 130 -> 49, NatSub 156 -> 45,
NatShr 200 -> 81. On CI (x3): the chain NatAdd -> NatSub -> NatShl -> NatShr -> NatDiv drops from
~70 min to ~20 min.

## Left
natMul_spec's value goal (61 s) and natShl_spec's `lb = 0` value goal (32 s) still go through the
generic search; NatDiv's remaining specs ~60 s in all. Scan.RecordsSpec/RecordsLink untouched.
