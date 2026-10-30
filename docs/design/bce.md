# Lane bce: bounds-check elimination, proved once in the compiler

The task (cgproto §3.1 and §5): a forward, per-function analysis over the L statement that finds
the array accesses whose index is in range, so that the code generator emits them without their
bounds check; its soundness proved once, inside the compiler's simulation proof, with
`Audit/Final.lean` and every L program and per-function proof above the compiler unchanged.
Generic only: facts about one function's locals and the arrays' lengths, no program invariants
(`count ≤ len`, hash masks).

**Result.** `Compiler/Bce.lean` (the analysis), `Compiler/BceSound.lean` and
`Compiler/BcePost.lean` (its soundness), and the facts threaded through the expression and
statement simulation. The compiled checker has 1,244 fewer bounds checks (7,986 → 6,742
`jae`/`jbe ca_error`); on `Init` 28.5 % fewer are executed and 1.86 % fewer instructions. The
output is byte-identical to the prototype's variant with the same analysis (§2). Wall time: §6.

## 1. What the prototype's analysis needed

cgproto's prototype (`_tmp/cgproto/proto/CG.lean`, variant `bce`) dropped checks from the emitted
code. Ablations of it (`_tmp/bce/proto/`, exact dynamic counts of the compiler's bounds-check
`jcc` on `Init`, `scripts/asmprof.py`; master 7.574 G):

| variant | checks executed | static |
|---|---:|---:|
| `bce` (all of cgproto's analysis) | 5.270 G | 6,632 |
| only the register-stack code generator (`gen`) and its stores | 5.355 G | 6,702 |
| … and no facts across a `return`'s or call's argument list | 5.417 G | 6,716 |
| … no bounds from `*`, `<<`, `\|`, `^` | 5.417 G | 6,716 |
| … no "local holds a length" facts | 5.417 G | 6,716 |
| … no bounds of locals from conditions | 5.418 G | 6,742 |
| **the kept analysis (Z)** | **5.418 G** | **6,742** |
| Z without `+` bounds | 6.962 G | 7,269 |
| Z without bounds from assignments | 6.877 G | 7,117 |
| Z without facts from conditions | 5.617 G | 6,824 |
| Z without facts from accesses that ran | 5.816 G | 7,328 |
| Z without bounds of bytes, 32-bit loads, comparisons | 5.418 G | 6,742 |

So the implemented analysis is Z: 97 % of the prototype's reduction of executed checks, with a
smaller analysis and, more importantly, with the unchecked accesses confined to `gen` (the
register-stack code generator) and its two store forms (`genSt`, `genStT`). The fallback code
generator `compileE`, `ldc`, the 8-byte loads and the block statements keep their checks: their
simulation lemmas did not change.

## 2. The analysis (`Compiler/Bce.lean`, 271 lines)

Facts (`Facts`): `lt`, pairs `(K, i)` meaning `i < len(K)`, where `K` (`AKey`) is a byte array, a
word array, tier `tv` of a tiered array (`tv` built from locals, constants and operators), or the
32-bit view of either, and `i` is such an expression too (`Expr.pure`); `hi`, pairs `(x, n)`
meaning `x < n`. At most 48 `lt` facts are kept.

* `hiE`: a bound of an expression from `hi`: constants, locals, `&` (the smaller), `>>` by a
  constant, `+` when it cannot wrap.
* Facts from a condition, in the branch where it holds (`Facts.cond`): `a < len(K)` from `a < b`
  true or `b ≤ a` false, `b` a length (`len8`, `len64`, `len64t`).
* Facts from accesses that ran (`Expr.loads`, `Cond.loads`): every access of an expression that
  evaluated passed its check. For a condition only the accesses that ran in the branch taken
  (`Cond.loadsAny` for the left side of `&&`/`||`: it ran, with a value not known).
* `x := e`: `e`'s accesses, then every fact that reads `x` goes (`kill`), then `x < hiE e`.
* `postF`: the facts after a statement (`none`: it never ends normally; `return`, `break`, `abort`
  end a path); `joinF` at `if` (facts on both sides, the larger bound); a call kills its result
  locals; a loop's head facts are the entry facts without those that read a local the body writes
  (`headF`), and after the loop the exit condition holds only if the body has no `break`.
* `safeIdx`: an access's index is in range when its fact holds, or when `hiE` bounds it by the
  array's minimum length (`Tab.min64`, `min64t` for a tiered access, twice that for 32-bit
  elements).

The code generator carries the facts of the current statement in `Ctx.fa` (default `some {}`).
`compileS` passes `postF` to the second statement of a `seq`, `condAll` to the branches of an
`if`, `headF` to a loop's condition and `condAll` of it to its body. An access asks
`Ctx.ck k i mn` (the check is needed unless `safeIdx`), and `genLd`, `genLdT`, `genLd32`,
`genLd32h`, `genSt`, `genStT` take that flag: the check is `chkR ck r ln`, empty when not needed,
and a constant index is unchecked when below the minimum or not needed. With every flag `true`
the code is master's, byte for byte (that is how the master output was compared).

Everything is structural recursion with list facts and `Bool` equality tests (`Expr.beqP`,
`AKey.beq`), so the kernel evaluates it in the whole-program check of the compiled code (§4).

## 3. The proof

The analysis's soundness is a property of L runs and is proved at L level, with the compiler's
own run functions (`evalP`, `stepRun`, `RunEq.lean`); the simulation then carries the facts.

**What the facts mean** (`Compiler/BceSound.lean`, 643 lines). `Facts.Holds fa σ`: every `lt`
fact's expressions are pure and its index is below the key's length in `σ`
(`AKey.len`), every `hi` bound holds; `FHolds none σ` is `False`. Lemmas: `loads_sound` (an
evaluated expression's accesses passed), `condLoads_sound`, `Holds.cond` and `condAll`,
`hiE_sound`, `Holds.frame` (facts survive a change of the locals they do not read when the sizes
stay), `Holds.set`, `Holds.killAll` with `killAll_idem` (a loop's code depends on its head facts
only), `fholds_join`, and **`safeIdx_sound`**: where `safeIdx` holds and the facts do, the index
is below the length of any array whose length is at least the minimum and the key's length.

The expression proofs run in *ghost* states (`St.ghost`): after code writes a scratch register
that holds a local the rest of the expression does not read, the L state of the proof has that
local changed. So the hypothesis of the expression lemmas is not `FHolds ctx.fa σ` but
**`FactsFor ctx σ e`**: the facts hold in a state with `σ`'s memory that agrees with `σ` on the
locals `e` reads (`Expr.readsV`); it passes to subexpressions (`FactsFor.sub`) and to ghost
states and register writes of registers `e` does not read (`FactsFor.ghost`, `FactsFor.setReg`).
`ck_sound` turns it into the index bound at a dropped check.

**Through the statements** (`Compiler/BcePost.lean`, 483 lines). `PostOk fa s r σ σ'`: a run of
`s` keeps the arrays' sizes and the locals `s` does not write, ends normally only with
`postF (some fa) s` true, and breaks only from a statement with a `break`. `FSound run`: every run
of `run` does. `fsound_step`: one step (`stepRun p K`) is sound when `K` (the next loop iteration
and the callees' bodies) is, by induction on the statement; `fsound_exec`: `exec p n` is, by
induction on the fuel. A callee runs in its own frame, so the caller's locals except the results
stay; its effect on memory keeps every size (`invoke_sizes`, with the empty facts).

**The simulation.** `GenSpec`, `CmpSpec` take `FactsFor ctx σ e`; the access specs
(`genLdW_spec`, `genLdTW_spec`, `genLdB_spec`, `genLd32W_spec`, `genLd32hW_spec`,
`ld32Code_spec`, `ld32hCode_spec`, `sim_genStW`, `sim_genStT`, `genSt_tailWX`) take the flag and
`hck : ck = false → index in range`, and one lemma, `chkR_spec` (`Sim32.lean`), covers the
optional check: with it, the code falls through or reaches `ca_error`; without it, the bound is
the hypothesis. `SimS` takes `FHolds ctx.fa σ`. `sim_seq` gets the facts after the first statement
from `FSound` (`FSound.post`); `sim_ite_gen` gets each branch's from the condition's value
(`fholds_condAll`); `sim_while` enters with the head facts (`fholds_head`), and at the next
iteration, whose code is the loop's under the head facts (`compileS_while_head`), they hold again
after the body (`fholds_head_after`). A function's body starts with the empty facts (`sim_fnBody0`).
The rest of each lemma is unchanged: `Inv`, `Conts` and the final theorems do not mention facts.

## 4. The whole-program check

The kernel evaluates the analysis where it already evaluates the code generator: one kernel check
per function in `Checker/AsmPart0–9` (`asm_lit_fns`). Each part alone (`lake env lean`), master
and this branch interleaved, load 4–10:

| part | master | bce | peak RSS master / bce |
|---|---:|---:|---|
| 0 | 26.7 s | 30.7 s | 3.57 / 3.56 GB |
| 1 | 24.6 s | 30.3 s | 2.69 / 2.78 GB |
| 2 | 26.5 s | 33.2 s | 2.72 / 2.78 GB |
| 3 | 32.7 s | 41.3 s | 2.71 / 2.79 GB |
| 4 | 35.4 s | 45.4 s | 3.54 / 3.93 GB |
| 5 | 35.6 s | 39.3 s | 2.73 / 2.77 GB |
| 6 | 9.4 s | 9.1 s | 3.50 / 3.54 GB |
| 7 | 12.1 s | 13.2 s | 4.02 / 4.18 GB |
| 8 | 9.9 s | 9.4 s | 3.82 / 3.88 GB |
| 9 | 12.1 s | 12.6 s | 4.17 / 4.22 GB |
| **sum** | **225 s** | **265 s (+18 %)** | max 4.17 / 4.22 GB |

The slowest part goes from 35.6 s to 45.4 s: about +10 s on the critical path of an L change. No
other whole-program module evaluates `compileS`.

## 5. Static and dynamic checks, instructions

Exact counts (`scripts/asmprof.py`), master (b4747f1d) against this branch; `Init` is
`init435.ndjson`, the parse phase `Init` cut after the parse (`check_a` returns at
`prepare_prelude`, `_tmp/bce/proto2/Parse.lean`).

| fixture | instructions | Δ | bounds checks executed | Δ |
|---|---:|---:|---:|---:|
| `Init` | 232.50 G → 228.17 G | −1.86 % | 7.581 G → 5.418 G | −28.5 % |
| parse phase | 18.94 G → 18.69 G | −1.32 % | 0.386 G → 0.261 G | −32.3 % |
| app-lam | 45.70 G → 44.98 G | −1.59 % | 2.016 G → 1.653 G | −18.0 % |
| c05b | 14.15 G → 14.02 G | −0.90 % | 0.546 G → 0.482 G | −11.7 % |

## 6. Wall time

Interleaved paired rounds, master's binary (b4747f1d) and this change's (the landed `checker.s`,
deaaa833, byte-identical to the measured one) back to back in random order per fixture
(`_tmp/bce/wb2.py`, `wstats.py`, from cgproto); median paired change, Wilcoxon p, mean with 95 %
CI. One thread on CPUs 44,92; 16 threads on CPUs 24–39. The machine was shared: load 2.8–32.6.

| cell | master | bce | n, load |
|---|---:|---:|---|
| `Init`, one thread, first batch | 17.62 s | **−1.6 %** (p 0.018; mean −1.2 % [−2.4, +0.0]) | 16, median 6.0 |
| `Init`, one thread, both batches | 17.73 s | −1.5 % (p 0.065; [−6.1, +1.2]) | 32, median 7.1 |
| `Init`, `--jobs=16` | 3.56 s | **−1.0 %** (p 0.003; [−2.0, +0.4]) | 70, median 9.4 |
| parse phase | 1.81 s | **−1.5 %** (p 0.001; [−4.6, +0.1]) | 32 |
| app-lam | 8.63 s | **−1.1 %** (p 0.017; [−3.7, +1.5]) | 32 |
| c05b | 1.37 s | +0.2 % (p 0.91; [−1.8, +4.3]) | 32 |

The second one-thread batch ran at load up to 32.6, which widens its intervals (`Init` alone:
−1.0 %, p 0.46); the 16-thread rounds after landing alone give −1.8 % (p < 0.001, n 40).
cgproto measured its prototype (the larger analysis) at −2.5 % (one thread) and −1.4 %
(16 threads) at a lower load (2.0–9.1). As there, wall time moves by less than the instruction
count (§5).

## 7. Verdicts

`diff-e2e --refs --parallel 16`: 634 of 634 agree (406 accepted, 228 not), UNSOUND, INCOMPLETE,
CRASH, TIMEOUT and REFDIFF 0. `--jobs 4`: 634 agree.

## 8. Sizes

| file | lines | what |
|---|---:|---|
| `Compiler/Bce.lean` | 271 | the analysis |
| `Compiler/BceSound.lean` | 643 | what facts mean; the analysis within one state; `safeIdx_sound`, `FactsFor`, `ck_sound` |
| `Compiler/BcePost.lean` | 483 | `PostOk`, `fsound_step`, `fsound_exec`; the helpers for the statement simulation |
| `Compiler/Compile.lean` | +83 / −59 | `Ctx.fa`, `Ctx.ck`, `chkR`, the flags, the facts in `compileS` |
| `Compiler/Sim*.lean`, `Correct.lean` | +611 / −442 | `chkR_spec`, the optional checks in the access specs, `FactsFor` in `GenSpec`, facts in `SimS`, `sim_seq`/`sim_ite_gen`/`sim_while` |

About 1,700 lines of proof against cgproto's estimate of ~1,500.
