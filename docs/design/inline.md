# Lane inline: the L → L inliner, proved once

The task: the L → L inliner that lnext (§3.1) prototyped and lnext2 (rank 1) re-measured,
implemented as a compiler pass with one correctness theorem, composed with the compiler's so that
the final theorems (`Audit/Final.lean`) keep their statements. No L code and no per-function proof
above the compiler changes.

## 1. The pass (`Compiler/Inline.lean`, 280 lines)

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

The proof (`Compiler/InlineCorrect.lean`, 1,585 lines with comments; namespace `L.Compiler.Inl`):

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
* `idx_lit checkerIdx : checkerProg` (`Checker/ProgIdx.lean`, 1 s): the name tree, computed by
  compiled code. That it is `Prog.idxTree checkerProg` (`idx_lit_eq`, 7 s) is checked in
  `Checker/ProgIRef.lean`: the literals below hold for any tree, only the correctness theorem
  needs it.
* `inl_round_fns checkerProgI : 80 checkerIdx checkerProg lo hi` (`Checker/ProgIPart0–6`): for each
  function, the literal of its inlined declaration (computed by compiled code; the original
  declaration's own term where inlining changes nothing) and
  `inlFn (envOf 80 checkerIdx checkerProg) fdᵢ = checkerProgI.fᵢ`, checked by the kernel eight
  functions per check, so the kernel's memory is released between checks. Byte strings in the
  literal are the environment's constants that hold them (the prelude's 15,700 bytes are
  referenced, not copied: 1.3 MB of `ldc` data sits in the changed functions).
  Compiled code runs each `checkerProgI.fᵢ` as `inlFn … fdᵢ` (`implemented_by`): the literals
  are not compiled, and the whole-program commands below evaluate the program with compiled code
  (without this, `skt_part` compiled the literals into its temporary definition and took minutes).
* `inl_round checkerProgI` (`Checker/ProgI.lean`, 1 s): the list `[(f, checkerProgI.fᵢ), …]`.
* `inl_round_eq` (`Checker/ProgIRef.lean`, off the path to the compiled code): `inlRound … =
  checkerProgI` from the per-function equations by congruence, no evaluation (0.8 s).

Every whole-program module downstream (`ProgNrt`, the `skt` and `prog_wf` parts, the asm parts)
reads the literal, as before it read `checkerProg`. They are retargeted rather than added:
`checkerNrt`, `checkerSkt` and the static check (`checkerProgI_wf`, with its own name tree
`ProgTreeI`) are now about `checkerProgI`; `ProgTree` (the names of `checkerProg`) stays for the
proofs above. `scripts/checker_prog.py` writes all of these (`INLINE_SIZE`, `INL_PARTS`).

**Cost**, each module alone (`lake env lean F.lean`, one after the other, wall and peak RSS;
before = the whole-program modules of lane wholeprog's split, on `checkerProg`):

| modules | before: sum, slowest, peak | after |
|---|---|---|
| `ProgNrt` | 10 s, 4.2 GB | 11 s, 4.3 GB |
| `ProgSktPart0–5`, `ProgSkt` | 46 s; 9.2 s; 4.2 GB | 66 s; 14.4 s; 4.5 GB |
| `ProgWfPart0–3`, `ProgWf` | 44 s; 15.4 s; 3.4 GB | 59 s; 18.5 s; 3.4 GB |
| `AsmPart0–9`, `Asm` | 175 s; 28.2 s; 4.1 GB | 206 s; 32.8 s; 4.1 GB |
| new: `ProgIdx`, `ProgIPart0–6`, `ProgI`, `ProgTreeI`, `ProgIRef` | | 184 s; 27.1 s; 3.5 GB |
| **all** | **275 module-s** | **526 module-s** |

The downstream modules are 15–35 % slower (a bigger program: `checker.s` has 223,711 lines against
205,835, more leaves, more frames). The new literal parts are 160 module-s, in parallel; on the
path of an L change they add `ProgIdx` (1 s) + the slowest part (27 s) + `ProgI` (1 s), and the
downstream modules' slowest parts are 4–5 s slower: about **+35 s of critical path**, no module
above 4.5 GB. lnext2 measured 199 s of critical path for an L change before wholeprog's split.

## 5. Verdicts

`diff-e2e --refs`: 634 of 634 agree (406 accepted, 228 not), 0 UNSOUND / INCOMPLETE / CRASH /
TIMEOUT / REFDIFF. `--jobs 4`: 634 agree.

## 6. Numbers

Binaries: master's `checker.s` (base) and this branch's (S = 80, one round). Load 2.3–6.7.

**Instructions** (exact): `Init` 237.32 G → 232.39 G (**−2.08 %**); app-lam 50.17 G → 50.17 G
(−0.01 %); c05b 14.43 G → 14.29 G (−1.0 %).

**Wall**, interleaved paired rounds (`_tmp/internspeed/wb.py`, `wstats.py`):

| cell | n | base | median paired | Wilcoxon p | mean, 95 % CI |
|---|---:|---:|---:|---:|---:|
| `Init`, one thread (CPUs 44,92) | 15 | 17.82 s | **−1.5 %** | 0.003 | −2.0 % [−3.5, −0.4] |
| `Init`, `--jobs=16` (24–39) | 30 | 3.66 s | **−2.9 %** | < 0.001 | [−4.0, −1.1] |
| app-lam, one thread | 15 | 10.10 s | −0.2 % | 0.030 | −0.8 % [−1.7, +0.2] |
| c05b, one thread | 15 | 1.35 s | **−2.0 %** | < 0.001 | −5.4 % [−10.3, −0.3] |

**Parse phase** (`_tmp/lnext2/phase.py`, 12 rounds, one thread, 50 ms windows): 1.85 s → 1.80 s,
median paired **−2.7 %**, 12 of 12 rounds faster (sign test p < 0.001).

**Peak RSS** unchanged: `Init` one thread 716 MB both, 16 threads 954 / 953 MB.

lnext2 measured the prototype at −2.8 % (16 threads) and −3.4 % (one thread, wide interval);
this pass saves a little more instructions, and the one-thread wall gain here is −1.5 % at a
lower load.

## 7. Sizes

| file | lines | what |
|---|---:|---|
| `Compiler/Inline.lean` | 280 | the pass |
| `Compiler/InlineCorrect.lean` | 1,585 | its proof |
| `Compiler/InlineLit.lean` | 327 | `idx_lit`, `inl_round_fns`, `inl_round`, `inl_round_eq`, the literal printer |
| `Compiler/MainRef.lean` | 66 | `Refines`, `compile_correct_frame_ref` |
| `Checker/ProgIRef.lean` | 32 | `checkerProgI_refines` |
| `Final/*`, `Compiler/Abi*.lean` | +74 / −61 | `q`/`p` in the ABI theorems, `abiFuelM` |

No L code and no proof above the compiler changed; `Audit/Final.lean` is unchanged.
