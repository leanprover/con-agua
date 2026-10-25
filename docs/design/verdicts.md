# Lane `verdicts`: reject vs decline, and a verdict theorem (journal)

Scoping lane, 2026-10-25. Question (user): can L tell rejected from declined, and can we prove
that, unless L stops for a resource reason of its own, its verdict on the 0/1/2/else scale is the
twin's? Follow-up (user, via coordinator): a fixed list of reason codes the harness can print; **no
converse**; worth doing even if every proof is touched, as long as cheaper models can do most of it
in parallel; it is not a release blocker and comes after or alongside parmode.

Pilot: branch `verdicts-pilot` (commit `9efcf754`), file `ConAgua/Pilot/Verdicts.lean`, 315
lines, proved, no `sorry`, elaborates in 2 s, imported by nothing.

## 1. The twin: what decides 0, 1, 2, 3

* **con-leche** has three error kinds, `notImplemented | invalid | internal`
  (`vendor/con-leche/ConLeche/Kernel/Core.lean`, `inductive CheckError`), mapped to exit codes 2, 1
  and 3 by `CheckError.exitCode` (`ConLeche/Driver/Run.lean`). The frontend uses the same type: a
  record kind the checker cannot represent is `notImplemented` (decline), a record that contradicts
  itself is `invalid` (reject), a malformed line is `internal` (3)
  (`ConLeche/Frontend/Export.lean`, module doc and `RecordVerdict`).
* **The twin** (`vendor/con-ron/ConRon/Arena/Monad.lean`, `inductive CheckError`) has a fourth
  kind, `native`, raised at the arena's own capacity limits (a handle word runs out at 2^27 nodes per
  constructor per tier). The twin's `CheckError.exitCode` (`ConRon/Arena/Main.lean:94-98`) maps
  `notImplemented ↦ 2`, `invalid ↦ 1`, `internal ↦ 3`, **`native ↦ 3`**.
* **con-ron's Rust driver** (`crates/con-ron/src/driver.rs:155-169`, `exit_code`) maps
  `NotImplemented ↦ 2`, `Invalid ↦ 1`, `Internal ↦ 3`, **`Native ↦ 2`**. Rust and Lean twin disagree
  on `native` (2 vs 3). A theorem against the twin speaks about the Lean mapping; we should follow
  it (L's capacity stops are exit 3) and tell con-ron about the mismatch.
* **Exit code** is just the kind of the first error the pipeline throws: `runPipelineHead`, the
  parse, `runPipelineTail` (`preparePrelude`, `internAllPins`, `installThenCheck`); the fold's error
  is the first failing record's. Phase B: con-ron's `phase_b_verdict` (`driver.rs:514`) reports the
  first failing **index**, so a parallel run reports what the one-worker walk would.
* **`orElseAttempt`** (`ConRon/Arena/CheckerBase.lean:50-106`) is the only recovery: inside a
  `Nat.div/mod` pin-variant attempt, a non-`native` error is `.recovered` (state restored, next
  variant), a `native` one is `.failed` (the verdict). When no variant is left
  `checkDivModPinLoop` (`DeclCheck.lean:613`) fails with `notImplemented`. So with one pin variant
  (D5, the harness's setting), any `invalid`/`notImplemented`/`internal` inside the attempt becomes a
  **decline**.
* The twin's own fuel: `checkFuel = 2^62` (`Core.lean:3634`); `liftFueled` turns a level
  algorithm's `none` into `notImplemented "resource limit: fuel exhausted"` (`Core.lean:312-314`), a
  decline; the walks' `coreWalkFuel` runs out as `internal`.
* Counts in the twin's arena: 118 `fail (.invalid …)`, 29 `fail (.notImplemented …)`, 127
  `fail (.internal …)`, 10 `fail (.native …)`; 93 distinct literal messages for reject/decline.
  The reject/decline sites sit in `Core.lean` (33), `Inductives/*` (72), `CheckDecl`/`DeclCheck`/
  `CheckerSplit`/`CheckerBase` (42).

**Converse and con-leche.** con-ron proves no converse. Theorem 1 (twin ⇒ con-leche) is
accept-only: every `…_bridge` lemma assumes `hrun : … = .ok …`, and `Bridge/Frontend.lean:40-45`
says so ("every theorem here is one-directional … a twin failure claims nothing"). Theorem 2 (Rust
⇒ twin) is whole-outcome in one direction: a Rust error of kind `k` means a twin error of kind `k`
(`AErrSim`, `ConRon/Refine2/Shape.lean:127`, all four kinds compared since task #98-NATIVE). So the
verdict theorem we can have is "L's kind ⇒ the twin's kind", exactly Theorem 2's shape; it does
**not** extend to con-leche's reject/decline without an error-kind Theorem 1 in con-ron (upstream
work; not ours).

## 2. The refinement shape today

* L's errors: `Err = outOfFuel | oob | noFun f | abort` (`ConAgua/L/Semantics.lean:46-55`); `abort`
  carries nothing, and `M = StateT St (Except Err)` drops the state on an error.
* The compiler (`ConAgua/Compiler/Main.lean:25`, `OutcomeRel`): ok ↦ `rdx = 0` with results and
  memory; `outOfFuel` ↦ `rdx = 1` (stack overflow also `rdx = 1`); **every other error ↦ `rdx = 2`**,
  `rax` unconstrained. Codegen: `abort` and every bounds check jump to `ca_error`
  (`Compile.lean:934, 1188`).
* Every spec and refinement is a partial-correctness triple whose exceptional post is `⊤`: `RefAM`
  (`Arena/IndIface.lean:314`), `CoreSpec` (`Arena/WhnfBase.lean:627`), the `natAddLit_refinesA`
  shape, the generated specs (2213 occurrences of `; ⊤⦄`). The word models are `Option`, `none`
  covering abort and fuel alike; `callW` (`WhnfBase.lean:643`) is a call's run with the error
  forgotten. `PipelineRefines` (`Final/Statement.lean:95-114`) is "returns ACCEPT ⇒ `TwinAccepts`".
* So the shape is: **L ok ⇒ twin ok and related; L error ⇒ nothing**. Note the first half is already
  strong: wherever L returns, the twin did not fail. The twin's errors are never mentioned.

## 3. Design

### 3.1 The claim

`checkerFile_verdict` (next to `checkerFile_accepts_remaining`): every run returns to `ra`, and if
it returns `rdx = 2` with class `c = rax & 3 ∈ {1, 2}`, then the twin's pipeline on `b`, at the pin
list `pb` decodes to, fails with an error of class `c` (`invalid` for 1, `notImplemented` for 2);
accept as today. Everything else (`rdx = 1`, class 0, `ok R`) claims nothing. On the exit-code
scale: harness exit 1 or 2 ⇒ the twin's exit code is the same. Through con-ron's Theorem 2 this is
also what con-ron's Rust binary would say, up to Rust's `Native ↦ 2`.

### 3.2 L side

* **Syntax/semantics:** `Stmt.abort (k : Word)`, `Err.abort (k : Word)`; `lfn`'s bare `abort` is
  `abort 0`. The kind word: bits 0–1 the class (0 other, 1 reject, 2 decline), bits 8+ the reason.
  Class 0 claims nothing, so the change is sound before any site is relabelled. Only three files name
  `Err.abort` today (`L/Semantics.lean`, `Compiler/RunEq.lean`, `E2E/Main.lean`); every existing
  spec has `⊤` for errors, so no other proof changes. It does rebuild the whole library.
* **Sites:** macros `reject R` / `decline R` expand to `if CTL.u64[ATT] != 0 { abort 0 }; abort k`.
  `ATT` is a `CTL` word that `check_div_mod_pin_loop` sets around an attempt: inside an attempt the
  twin recovers, so L must not claim a class (D4). Optional refinement: when the attempt is the last
  variant, `ATT` holds `decline R_NO_PIN_VARIANT` and the macro aborts with it, which makes the
  one-variant case exact (the twin then declines); first version: class 0.
* **Compiler:** `abort k` ↦ `mov rax, k; jmp ca_error`; the bounds checks jump to a new
  `ca_oob: xor eax, eax` that falls into `ca_error` (`mov rdx, 2`). `OutcomeRel`: `.error (.abort k)
  ↦ rdx = 2 ∧ rax = k`, other errors ↦ `rdx = 2 ∧ rax = 0`. `if c abort` keeps its one-jump form with
  a `mov` in a landing pad. The committed `asm/checker.s` and its kernel check regenerate.
* **Harness** (top-level `main.c`, moved there by lane harness): `rdx = 2`: class 1 ⇒ `rejected: <msg>` exit 1; class 2 ⇒
  `declined: <msg>` exit 2; class 0 ⇒ `error: <msg>` exit 3. `rdx = 1` ⇒ `exhausted` exit 3; `ok R` ⇒
  `error: malformed line R` exit 3; accept exit 0. The messages are a table `reasons[]` in a generated
  header (`reasons.h`), written by a script from the L sources' `reject`/`decline` reason
  declarations, checked by a gate like `overview-links.sh`.
* **Threads (`--jobs`):** a thread stops at its first failing group; the harness must report the
  failing group with the **smallest index** and only after every lower group has finished ok
  (`phase_b_verdict`'s rule). Today `main.c:151` stops all threads at the first failure of any.
* **Reason list.** Mirror the twin: one reason per distinct literal message of `fail (.invalid …)`
  / `fail (.notImplemented …)` (93; the interpolated tails — names, counts — are dropped), numbered
  by a script from the citations, so the harness prints the twin's own words. Plus about ten L-only
  class-0 reasons: region/capacity full, word-overflow guard (D32–D34), number past 18 digits (D2),
  escaped `safety`/`kind` string (D3), pin data not readable (D6), defensive check (dangling handle,
  D22/D27/D29), out of bounds (`rax = 0`). The reason is not part of the theorem (trusted labelling);
  proving it is cheap later if the reason maps to the twin's literal (`rfl` per site).
* **Cheaper transport for the unproved variant:** `e2e-l asm` already does this for stubs
  (`DIAG.u64[0] := code; abort`, `E2E/Main.lean:11`). Sites could write `DIAG[0] := k; abort` with no
  semantics or compiler change. It cannot be proved without a compiler theorem about memory on the
  error path, so it is only worth it if (b) is never done; otherwise do `abort k` once.

### 3.3 Proof side

**What each layer must say.** Kinded error claim (pilot: `ErrClaim`):
`e = .abort k → cls k ≠ 0 → ATT = 0 → ∃ ce, T.run a = .error ce ∧ twinCls ce = cls k`, where `T` is
the twin op at the entry state `a`. Fuel, out of bounds and class-0 aborts claim nothing.

**Why only prefixes and sites matter.** An L error at a site in `f` is preceded by ok runs of
`f`'s earlier calls. The existing ok refinements already relate those runs to ok twin runs from the
related state. What is new is (i) propagation of a callee's kinded error through the twin's `bind`,
and (ii) at each class-1/2 site, that the L guard is the twin's failure condition at that point. So
**deviations matter only at the abort sites themselves**: a deviation elsewhere is already inside
the proved ok refinements.

**Generic framework (Opus, done once):**

1. `callE` (a call's whole run with its error) and `callE_spec` ("every call meets its own run, also
   when it fails") — **pilot, proved**; `callW = (callE …).toOption` (pilot).
2. `M.of_run_err`, `M.triple_of_run'` (error versions of `L/Logic.lean`'s bridges) — **pilot,
   proved**; generalise `Triple.step_exec`, `triple_of_callW` etc. from `⊤` to any error post.
3. The twin-side kit: `ErrClaim.bind_left` (callee failed), `ErrClaim.bind_right` (ok prefix, later
   step failed), `ErrClaim.fail` (a site), `ErrClaim.cls0` — **pilot, proved**.
4. `CoreSpecE`/`RefAME`: the error-only triples (`⦃s = s₀⦄ f ⦃⊤; ErrClaim T a₀⦄`), and the
   conjunction rule `⦃P⦄c⦃Q;⊤⦄ → ⦃P⦄c⦃⊤;E⦄ → ⦃P⦄c⦃Q;E⦄`, so the **existing ok proofs stay
   untouched** and the error proofs are new files.
5. **`NoVerdict`**, the syntactic closure lemma: a `Bool` check that a call-closed set of functions
   contains only class-0 aborts gives `ErrClaim` for every function of the set for free (like
   `L/WriteSet.lean`'s frame lemma; proof by fuel induction over `exec`). This covers everything
   outside the closure below.
6. `l_model` (`L/ModelGen.lean`): generate the `Except` model next to the `Option` one (`K = KE.toOption`,
   pilot `ensureSortK_eq`), its arm equations (pilot `ensureSortKE_ok/_e1/_e2/_e3/_err`), and the
   error spec with the same `vcgen`/`finish` script.
7. `OutcomeRel`'s `rax`, `PipelineVerdict p` (the analogue of `PipelineRefines`), and the composition
   to `checkerFile_verdict`.

**What has to be touched (counts from a script over the L sources, `_tmp/verdicts/cg.py`):**

| | count |
|---|---|
| L functions (`lfn`) | 1506 (1360 parsed by the script) |
| `abort` sites | about 890 in 391 functions (1137 textual matches incl. comments/docs) |
| functions with an abort site whose twin has a reject/decline `fail` | 56 functions, 147 sites (by `@[l_impl]`; about 15 more twin functions are mirrored by L helpers without the attribute, and the front adds about 15–20 sites) |
| **closure**: those functions and all their callers (they can propagate a class-1/2 abort) | 156 by the script; **about 200** with the misses |
| of which carry abort sites of their own | 76 |
| everything else (about 1160 functions) | nothing: `NoVerdict` |

So about **200 functions** need an error spec and an error refinement, and about **170–200 sites**
need a class decided against the twin.

**Recipe per closure function** (the pilot shows each step on `ensure_sort`):

1. *Label* each abort site (Sonnet): read the cited twin lines; class 1/2 only if the twin
   `fail (.invalid/.notImplemented …)`s at exactly that point under the same condition; class 0 if
   the twin fails `internal`/`native` there, the check is defensive, or it is a deviation. In
   `ensure_sort` the tag test is the twin's `fail (.invalid "expected a sort")` (class 1); the tier
   and count tests are the twin's `view` on a dangling handle (`internal`, class 0).
2. *Model* (Haiku if generated, Sonnet if hand-written): the `Except` model `KE` beside `K`, with
   `K = KE.toOption` and one equation per arm.
3. *Spec* (Haiku): `f_specE`, the ok spec's own script with `callE_spec` for `callW_spec` and the
   arm equations for `finish`. Pilot: `ensureSort_specE`. **Finding:** the post must be "an `abort`
   error is the model's error", not "every error is the model's": an out-of-bounds read in L where
   the model reads a default (`tfld`) would otherwise be unprovable. First attempt failed exactly
   there; the restricted post went through unchanged.
4. *Refinement* (Sonnet): `f_refinesE` by case analysis on `KE`: callee error ⇒ callee's
   `ErrClaim` + `bind_left`; ok prefix then later error ⇒ the callees' **existing** ok refinements +
   `bind_right`; class-0 site ⇒ `cls0`; class-1/2 site ⇒ `fail`, with the L guard turned into the
   twin's condition (usually the negation of a lemma the ok proof already has: pilot `tag_sort_ne`
   beside `tag_sort_beq`). Pilot: `ensureSort_refinesV`; and on a decl-level function,
   `checkThmVal_claim_mismatch` (six ok calls, then `isDefEqCore = false` ⇒ `invalid`), both by the
   kit and `simp`.

**Non-mechanical parts (Opus):** the knot's error induction (whnf/defeq/infer through `KnotUpTo`,
fuel induction with the ok `KnotUpTo` available: `Core.lean` holds 33 reject/decline sites, so the
knot is in the closure); the loops (`install_fold_go`, `check_pending_go`, the front's `runLoop`:
loop specs with an error invariant); the front (its failures are `.ok (.error (e, n))` values in the
twin and a return word or abort in L); the pin attempt (`ATT`, §3.2); `PipelineVerdict` through the
stages, the prelude and phase B; the threaded harness rule. Sites with a twin counterpart that is
not 1:1 need a decision each (e.g. `lvl_eq_fueled`'s `r == 0` abort is the twin's `liftFueled`
decline only if L's level fuel is the twin's; otherwise class 0).

### 3.4 Deviations that would break verdict equality unless class 0

All are completeness/defensive rows; as class 0 they claim nothing and the theorem holds:

| row | why it cannot be class 1/2 |
|---|---|
| D2 | long numbers: L aborts, twin reads them (would accept or fail elsewhere) |
| D3 | escaped `safety`/`kind` strings read as "not safe": twin compares after unescaping |
| D4 | inside a pin attempt: twin recovers (one variant: declines); handled by `ATT` |
| D6 | pin data the reader does not handle: no twin failure at all |
| D9 | sparse id memo full: capacity |
| D22, D27, D29 | defensive checks the twin does not make (or makes as `internal`) |
| D32, D33, D34 | word-overflow / key-width capacity guards |
| twin `native` mirrors | L's capacity tests that mirror the twin's `native` (twin exit 3) |
| the front's `return 1` | unscannable line: twin `internal`; stays `ok 1` ⇒ exit 3 |

D20 (walk fuel dropped) and the performance rows do not touch abort sites; prefixes are covered by
the ok refinements. D16 is replaced by this design.

## 4. Cost (lane-days; one lane-day = one agent-day of the given tier)

| | work | tier | estimate |
|---|---|---|---|
| **(a) labels and exit codes, no proof** | `abort k` in L, compiler + `compile_correct` for it (needed anyway: the asm file is kernel-checked), asm regeneration | Opus | 1.5–2 |
| | label the ~200 sites (scripted: default class 0; Sonnet decides the candidates from the citations) | Sonnet | 1–1.5 |
| | harness exit codes, reason table generator and gate, threaded min-index rule, docs (OVERVIEW §1.4, §2.4, D16) | Sonnet | 1 |
| | differential test of exit codes against con-ron on the e2e corpus (the check for trusted labels) | Sonnet | 0.5–1 |
| | **total (a)** | | **4–5.5** |
| **(b) proved, L kind ⇒ twin kind** | (a) | | 4–5.5 |
| | framework items 1–7 above | Opus | 4–6 |
| | ~200 closure functions × (model, spec, refinement), mechanical part (~150 functions) | Haiku/Sonnet, 6–8 in parallel | 12–20 (about 1.5–2 weeks wall at 6–8 agents) |
| | non-mechanical: knot, loops, front, attempt, pipeline/phase B (~40–50 functions) | Opus | 10–14 |
| | **total (b)** | | **30–45 lane-days, about 4–6 weeks wall** |
| **(c) both directions** | (b) plus total-correctness obligations for every function (every class-0 abort shown to be a real resource stop or unreachable, about 700 sites, 1360 functions) | | **3–4× (b)**; not wanted |

The pilot calibrates the mechanical part: `ensure_sort`'s error spec was the ok spec's script plus
five arm equations; its error refinement about 40 lines from the kit. Knot functions add the
induction plumbing, which is the Opus part.

## 5. Interaction with parmode

* Conflicts: the semantics change rebuilds everything; the compiler (`OutcomeRel`, codegen,
  `ca_error`), `Final/*` (a new theorem beside the accept ones), `Checker/Entry.lean`, the asm file
  and its kernel check, and `main.c` (exit codes, the threaded min-index rule) are exactly
  what `parmode-sw` (`Final/Abi`, `DrvAbi`, `ParAbi`, `Remaining`, `Compiler/Abi(Sim)`,
  `Checker/Entry`, `PipeFinal`, `AsmFinal`) and the harness lane change.
* So: **step 0 (L `abort k`, compiler, asm, harness) after parmode-sw lands**, as one landing. The
  framework and the per-function error proofs are new files and do not conflict; they can be
  written alongside parmode, but they need step 0's `Err.abort k` to state their posts, so start
  them right after step 0 (or write the first ones against the pilot's stand-in `VErr` and switch).
* The verdict theorem must be stated for every entry parmode keeps (`ca_start`, the driver, the
  threads); the thread entries' error kinds come out per group, and the twin's `PooledAccepts`
  side needs a verdict analogue (first failing index).

## 6. Recommendation

Do (a) now-ish (after parmode-sw): it is small, sound by construction (class 0 claims nothing),
gives the user `rejected`/`declined` with the twin's own messages, and is tested against con-ron.
Do (b) as a background lane with Haiku/Sonnet helpers once (a) has landed: the pilot shows the
mechanical part really is mechanical, and the hard 25% is the knot, the loops and the front. Skip
(c). Report the `native` 2-vs-3 mismatch to con-ron.
