# Lane `verdicts-a`: reason-coded aborts and exit codes (journal)

Step (a) of `docs/design/verdicts.md`: L's aborts carry a code, the compiled program returns it in
`rax`, the harness prints `rejected`/`declined`/`error` with the twin's message and exits 1/2/3. No
new proof obligation; step (b) (the verdict theorem) builds on this.

## Design as built

* **L.** `Stmt.abort (e : Expr)`, `Err.abort (k : Word)`; `step` throws `.abort (← evalE e)`.
  An expression rather than a constant, so that a reject/decline site can clear its class inside
  a pin attempt without a branch in L (`fail R` = `abort R ^ (R & ATT)`, below): the site stays one
  `abort` statement, so `l_model`'s models, their `abortᵢ` arm numbering and every downstream proof
  keep their shape. `Err.code` (an abort's value, `0` for every other error) and `Err.plain`
  (code `0`, not fuel) are the two facts the compiler needs.
* **Notation.** `abort` (= `abort 0`), `abort R`, `fail R`. `fail` is a non-reserved keyword
  (`&"fail"`, with the `lstmt` category's `leadingIdentBehavior := both`), so `fail` stays an
  identifier in tactic and term code (`simp [fail]` names con-ron's `fail`).
* **Codes.** `k = 4 r + c`: class `c` (`0` other, `1` reject, `2` decline), reason `r`, a row of
  `scripts/reasons.tsv`. `scripts/reasons.py` writes `ConAgua/Arena/Reasons.lean` (one `abbrev
  R_… : L.Word` per row, class included) and `reasons.h` (the messages), `--check` is a gate in
  `land.sh` (stale files, or a twin message without a row), `--add` appends rows after a twin bump
  (numbers stay stable: rows are only appended). The twin rows: every distinct string literal of a
  `.invalid`/`.notImplemented`/frontend `.declined` error in `vendor/con-ron/ConRon/Arena` (140 at
  the vendored revision; interpolations as `…`, `s!` strings parsed with their `{…}` nesting, Lean
  string gaps joined) plus con-leche's `nonStdAxiomMsg`; then 11 L-only class-0 reasons.
* **The attempt flag.** Global `ATT` (`⟨7⟩`, below the existing ids so the table layout does not
  move): `check_div_mod_pin_loop` sets it to `3` around `call check_div_mod_pin_at` and back to `0`.
  Inside the attempt every `fail R` aborts with class `0` (the twin recovers there, D4).
* **Compiler.** `abort 0` and `if c abort 0` compile as before (`jmp`/`jcc ca_error`); `abort e`
  is `e` into `rax`, `mov rbx, rax`, `jmp ca_abort`; `if c abort k` (`k ≠ 0` a constant) is
  `mov rbx, k` and then the condition's one `jcc ca_abort`: no taken branch on the hot path (a
  capacity check stays one not-taken jump; the general `if` would cost a taken jump per check),
  and no landing pad, so no code-layout proof. `rbx` is free for this: no local lives in it, the
  condition code keeps it (`EPost.keep`), the trampoline restores it. `if c abort e` with a
  non-constant `e` (`fail R`) is the general `if` (the jump over the abort is taken; these are
  reject/decline sites, off the hot loops). The trampoline: `ca_error: mov rbx, 0`, falling into
  `ca_abort: mov rax, rbx; mov rdx, 2` and `ca_finish`, which keeps `rax`.
  `OutcomeRel`: `.error e ↦ rdx = 2 ∧ rax = e.code` (fuel stays `False`). Proof: `Conts.err` now
  takes `e.plain` errors (to `ca_error`), the new `Conts.abrt` an abort whose code is in `rbx` (to
  `ca_abort`); `FunSim` and the function-body lemmas got the same two continuations;
  `sim_ifAbortK` is the new `if c abort k`. Every `compile_correct` statement is unchanged except
  through `OutcomeRel`; the final theorems' statements are unchanged (their `OutcomeRel` uses are
  accept-only; four proofs in `Final/` read `rdx` from the error case and now take `.1`).
* **Harness.** `print_verdict` decodes `rax`; exhausted is exit 3; `--jobs` keeps per thread the
  first failing group index and result and reports the smallest index (`phase_b_verdict`).

## Results (2026-10-25, branch at the labelling merge, the 675 fixtures of the e2e corpus)

* **Labels.** Three Sonnet helpers labelled the reject/decline sites by file group (core: 32 sites
  in Infer/Whnf*/DefEq; inductives: 75 in IndPos2/IndSum/RecCheck/RecGen/IndInstall/IndParts;
  declarations and frontend: about 60 `fail` plus L-only `abort R_…` in Decl*/Front/*); I added the
  `And` pin reject and the capacity reasons of the store room (`R_CAP_STORE`), the key width
  (`R_CAP_KEY`, D34), the slice range (`R_CAP_WORD`) and the region checks (`R_CAP_REGION`). Left
  class 0 on purpose: sites where the twin raises one of several kinds that L merges into one abort
  (`consts_resolve` failures: "unknown constant" reject vs "use of the sorryAx axiom" decline; a
  projection miss: three messages, one a decline; `lv_leq_top`/`lvl_eq_c` tests `!= 2` that merge
  the fuel decline with a reject). Splitting them needs one branch per kind.
* **Exit codes against con-ron** (`--jobs=1`, its embedded pins; rows con-ron, columns L):
  0→0 426; 1→1 195, 1→3 12; 2→2 28, 2→3 7; 3→3 4; con-ron crash (−6)→3 1; timeouts 2 (both).
  No fixture where L says 1 and con-ron 0/2, or L says 2 and con-ron 0/1, or L accepts and con-ron
  does not. Where both label, L prints con-ron's message. `--jobs=4` gives the same exit code and
  line as the sequential run on all 673 finished fixtures.
* **Arena rules.** No bad test is accepted. No good test gets 3: the five good tests that ended in
  the old exit 2 (a non-standard axiom) are declines (2). One good test,
  `good/undecidability/subject-reduction-redex`, now exits 1 ("application type mismatch"):
  **con-ron rejects it too** (a twin behaviour: con-ron rejects a test the arena classifies as
  good; to raise with con-ron). L matches its twin there.
* **Class 0 is exit 3.** It keeps "harness exit 1 or 2 ⇒ the twin's exit code is the same": an L
  capacity or a merged site is no twin decline (a capacity stop on a bad test con-ron rejects would
  otherwise read as a decline). No good test of the corpus ends in class 0 or in exhaustion.
* **Cost.** `perf stat` instructions, base → labelled: app-lam 72.94e9 → 73.02e9, beta-ladder
  19.98e9 → 20.00e9, natmul_deep_major 36.39e9 → 36.42e9, init-prelude 2.029e9 → 2.031e9 (+0.1%);
  wall time within the machine's noise.
* **`L/Semantics.lean`'s `dite` reads.** The `grind` gap they worked around is fixed on the current
  toolchain (the old reproducer's examples pass at once), but the `dite` stays: every load proof is
  written against its verification condition (bound and element, no `Option`).
