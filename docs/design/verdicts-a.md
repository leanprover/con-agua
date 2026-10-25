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
