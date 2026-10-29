# Lane inline: the L → L inliner, proved once

The task: the L → L inliner that lnext (§3.1) prototyped and lnext2 (rank 1) re-measured,
implemented as a compiler pass with one correctness theorem, composed with the compiler's so that
the final theorems (`Audit/Final.lean`) keep their statements. No L code and no per-function proof
above the compiler changes.

## 1. The pass (`Compiler/Inline.lean`, 279 lines)

`inlineProg S t R p`: `R` rounds of `inlRound S t`, each replacing in every function every call
`xs := g(args)` of a **leaf** `g` (no call in its body) of at most `S` nodes (`Stmt.size`, lnext's
measure) by

```
zs + o := 0          -- the callee's locals it may read before it assigns them (needZero)
i + o := argᵢ        -- its parameters
conv o xs body end   -- its body, locals shifted by o, exits turned into xs := …
```

* **Shift** (`Stmt.sh o inLoop`): every local `x` of the callee becomes `x + o`, where `o` is
  past every local the caller names (`max nlocals (Stmt.vb body)`). All inlined calls of a
  function share the region from `o` on (its size the largest callee's `nlocals`): a callee's
  locals are dead after the call, and those it reads first are zeroed.
* **Exits** (`conv o xs u k`): continuation passing, structural in `u`. `k` is the converted rest
  of the body; `return es` becomes `xs := es` (missing values `0`) and drops `k`, a `break` outside a
  loop `xs := 0…`, the end of the body `xs := 0…`. An `if` whose one branch always exits
  (`Stmt.allExit`) gets `k` in its other branch only, so nothing is duplicated; an `if` with
  exits that does not always exit, a `return` in a loop, or a call fails the conversion, and the
  call stays a call. A `return` with more values than the call reads is converted only if the
  extra ones cannot fail (`Expr.safe`: `return` evaluates all of them).
* **No `while true { …; break }` wrapper.** lnext's prototype fell back to it where the tail
  conversion failed. Measured on master: with the wrapper as the only form, −0.46 % instructions
  on `Init`; tail conversion with the wrapper as fallback −1.72 %; tail conversion alone −1.75 %.
  The wrapper's loop costs what the call cost, so it is dropped (and with it a third of the
  proof).
* A call is inlined only if it passes as many arguments as the callee has parameters, and a
  function only if its frame stays below the compiler's bound (`frameWords`), else it is kept.
* **Callees** are found through a tree from `nameCode` to the position in `p` (`Prog.idxTree`,
  `envOf`): the kernel compares numbers, not strings.

**Parameters: S = 80, one round.** Exact instructions on `Init` (`perf stat -e instructions:u`,
master's `checker.s` 237.32 G):

| variant | instructions | Δ | directives |
|---|---:|---:|---:|
| S = 40, 1 round | 234.33 G | −1.26 % | 185,713 |
| **S = 80, 1 round** | **232.39 G** | **−2.08 %** | 190,899 |
| S = 80, 2 rounds | 232.30 G | −2.12 % | 196,746 |
| S = 160, 1 round | 232.38 G | −2.08 % | 191,946 |
| lnext's prototype (S = 80, 2 rounds, wrapper fallback, a region per callee) | 233.24 G | −1.72 % | 193,049 |

A second round adds 0.04 %, and each round costs one unit of fuel in the theorem and one round of
kernel-checked literals in the build (§4), so one round it is. The shared region (one per
function rather than one per callee) is what makes this pass better than the prototype's: more
inlined callers stay small enough for the leaf register allocation.

## 2. The theorem

```lean
theorem inlineProg_run : ∀ (R : Nat) (p : Prog), Prog.idxTree p = some t →
    ∀ N f vs m r, L.run (inlineProg S t R p) N f vs m = r → r ≠ .error .outOfFuel →
      L.run p (N + R) f vs m = r
```

A run of the inlined program that does not run out of fuel is a run of the original with `R`
more units of fuel: the same results and memory, or the same error. Why `+R`: an inlined body
runs at its caller's fuel level, one above where the call ran it (`exec p (n+1) (call …)` runs the
body under `exec p n`); its loops re-enter at one unit more than in the original. Inlined bodies
are leaves, so this never compounds along a call chain: one unit per round.

The proof (`Compiler/InlineCorrect.lean`, 1,580 lines with comments; namespace `L.Compiler.Inl`):

| part | what | lines |
|---|---|---:|
| values | `Expr.ev`, `Cond.ev`, `Exprs.ev`, `sstep`: evaluation and the simple statements as functions of the state (`evalE_run`, `step_simple`, run equations of `seq`/`ite`/`while`/`call`) | ~330 |
| shift | `AR o B c` (the callee's frame is the caller's from `o` on; the caller's locals below `o` stay `c`): `Expr.ev_sh`, `sstep_sh`, `shift_step` (induction on the statement, the loops by hypothesis), `shift_exec` (induction on the fuel) | ~400 |
| conversion | `retAssign_run`, `allExit_ne`, `conv_step`: a normal end continues with `k`, an exit sets `xs` | ~260 |
| the call | `zeroS_run`, `paramS_run`, `setLocs_range`; `inl_call`: the view of the shifted region agrees with `Locals.init args` on the parameters and on `needZero` (`exec_da`, `L/DefAssignSim.lean`, which the compiler already uses for its own zeroing), then `conv_step` | ~200 |
| caller and program | `CR o`, `Ref` (a run of the inlined program refines one of the original; running out of fuel refines anything); `caller_step` (induction on the statement), `round_exec` (induction on the fuel), `round_run`; `envOf_sound` (the name tree), `inlineProg_run` (induction on the rounds) | ~350 |

parsespeed §6 estimated ~850 lines; it is about twice that, mostly the value layer (L's
semantics is monadic, and comparing two programs' runs needs the runs as values) and one lemma
per statement form at each of the three levels.

## 3. Wiring into the final theorems

* `Compiler/MainRef.lean`: `Refines q p` (a run of `q` with fuel `N` that does not run out of fuel
  is a run of `p` with fuel `N + abiInl`; `q` has `p`'s functions with their parameter counts) and
  `compile_correct_frame_ref`: `compile_correct_frame` for `q`, with `p`'s outcome.
* **Fuel.** The L-level statements (`DrvAccepts`, `checkA_run`, the stage specs) are about
  `checkerProg` at `abiFuel = 2^62 - 1`, and some need `N < 2^62`. So the stubs now pass
  `abiFuelM = abiFuel - abiInl` to the trampoline (`Compiler/Abi.lean`, `abiInl = 1`), and
  `compile_correct_frame_ref` gives `p`'s run at `abiFuelM + abiInl = abiFuel`: every L-level
  statement above is unchanged.
* The generic ABI theorems (`ParAbi`, `SeqAbi`, `BufAbi`, `DrvAbi`) take `(q p) (hq : Refines q
  p)`, compile `q`, need `Prog.wf tab q`, and speak of `p` as before. `DrvFinal`, `EndToEnd`,
  `VerdictFinal`, `ThreadsFinal`, `ThreadsVerdict` instantiate them with `checkerProgI`,
  `checkerProg`, `checkerProgI_refines`.
* `checkerFile_eq : checkerFile = checkerStub ++ compileProg checkerTab checkerProgI "check"`.

## 4. The whole-program checks

**The risk lnext2 flagged happened.** First attempt: `checkerProgI := inlineProg … checkerProg`
as a computed term, with the existing `nrt_lit`/`skt_lit` over it: the kernel evaluated the
inliner over all functions in one check, each function's inlining evaluating its callees'
declarations (several are themselves computed, `preFn`, `memoFindG …`), and kept all of it: about
60 ms and 9 MB per function (400 functions 30 s, 6.8 GB); the whole program went past 16 GB
(killed by the memory watchdog). Every module that reads the compiled program would have paid it
again.

**The structure now: a checked certificate.** The inlined program is a literal
(`Compiler/InlineLit.lean`):
* `idx_lit checkerIdx : checkerProg` (`Checker/ProgIdx.lean`): the name tree and
  `Prog.idxTree checkerProg = some checkerIdx`, one check over the names (7 s).
* `inl_round_fns checkerProgI : 80 checkerIdx checkerProg lo hi` (`Checker/ProgIPart0–3`): for each
  function, the literal of its inlined declaration (computed by compiled code; the original
  declaration's own term where inlining changes nothing) and
  `inlFn (envOf 80 checkerIdx checkerProg) fdᵢ = checkerProgI.fᵢ`, checked by the kernel eight
  functions per check, so the kernel's memory is released between checks. Byte strings in the
  literal are the environment's constants that hold them (the prelude's 15,700 bytes are
  referenced, not copied: 1.3 MB of `ldc` data sits in the changed functions).
* `inl_round checkerProgI` (`Checker/ProgI.lean`): the list `[(f, checkerProgI.fᵢ), …]`;
  compiled code runs it as the round itself (`implemented_by`), since the literals are not
  compiled.
* `inl_round_eq` (`Checker/ProgIRef.lean`, off the path to the compiled code): `inlRound … =
  checkerProgI` from the per-function equations by congruence, no evaluation (0.8 s).

Every whole-program module downstream (`ProgNrtI`, the `skt` and `prog_wf` parts, the asm parts)
reads the literal, as before it read `checkerProg`.

(numbers: §6)

## 5. Verdicts

`diff-e2e --refs`: 634 of 634 agree (406 accepted, 228 not), 0 UNSOUND / INCOMPLETE / CRASH /
TIMEOUT / REFDIFF. `--jobs 4`: 634 agree.

## 6. Numbers

(pending)
