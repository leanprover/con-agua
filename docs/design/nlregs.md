# Lane nlregs: locals in registers in non-leaf functions (analysis, prototype, proof plan)

Question: can the compiler keep locals of functions that make calls in registers, proved once in
the compiler, and how much does it buy (lnext §3.2 estimated −2.1 % instructions on `Init`;
scanfast saw a 15 % gap between the same code as a leaf and as a non-leaf)?

Base: master b130493e (§3) and aa459fa6 (§7; same `checker.s`). Nothing landed but this journal. Prototype sources, assembly, binaries,
profiles and bench logs: `_tmp/nlregs/` (`NL.lean`, `*.s`, `prof/`, `bench-*.{log,json}`).
Unproved; never to be landed.

**Answer in short (revised with wall time, §7).** Wall time is the goal; instructions are only a
deterministic stand-in. §7 measures wall time directly: 15 interleaved rounds, paired by round,
with a Wilcoxon signed-rank test. On `Init` and the long fixtures, **no variant gains 2 % wall**:
* **Loop promotion with spills around calls**: −1.0 % on `Init` (p = 0.008). It loads a loop's
  most used frame locals into `r12 r13 rbx` before a loop of a non-leaf function and stores the
  changed ones back after it, spilling them around each call in the loop.
* **IPRA** (§2 D): −0.7 % (p = 0.035).
* **Full callee-saved convention** (A): +2.2 % slower (p < 0.001).
* **The same convention aimed only at the hot loops** (`line_rec`, `next_member`, `sub_rec` and
  others): +1.0 to +2.4 % slower.
* **The abort stub alone** (−0.09 % instructions): +1.4 % slower.
* On the long fixtures every difference is within ±2.3 %. The two that reach 2 % are slower: the
  hot-loop variant on `let-ladder` (+2.3 %) and the callee-saved convention on `Init` (+2.2 %).

The abort stub's result shows that **effects of 1–2 % here come from code layout as much as
from the change itself**. The latency effect (store-to-load forwarding on frame slots) is real but
small: frame locals in hot loops of non-leaf functions are only 11 G of `Init`'s 243 G
instructions, with 1–3 iterations per call. **Recommendation: no implementation lane** (§6).

The first measurement (§3) leaned on instruction counts and on cycle numbers from very noisy
runs. It stays below for the analysis of where the instructions go.

## 1. How the compiler does it now

`ConAgua/Compiler/Compile.lean`:
* **Leaves** (`!Stmt.calls fd.body`) keep their most used locals in registers (`leafAlloc`,
  weighted by `8^loop-depth`, `Stmt.uses`). They use up to 9 registers (`allocRegs`):
  * a parameter keeps its argument register (`rdi r8 r9 r10 r11 rsi`);
  * the other locals take `r13`, `r12`, `rbx` first (not result registers, so `retDirect`
    conflicts less), then the free argument registers.
  * `fnAlloc` is `[]` for every function that calls (`AllocOk.leaf`, `Rel.lean`).
* **Non-leaf functions** keep every local in the frame (`rsp + 8x`).
* **No register survives an L call.** The only fixed registers are:
  * `r15` (table) and `r14` (fuel);
  * `rsp`, with the frame popped by the callee;
  * `rbp` (the trampoline's stack pointer).

  `rbx r12 r13` are saved only by the trampoline, for the C caller (`trampoline`).
* `FunSim` (`SimCall.lean`), the simulation of a call, promises the caller exactly this:
  * `rsp + 8`, `rbp`, `r15`, `r14 ≤`;
  * the results (`ResOut`);
  * memory above the return address unchanged (`Pres`).

  Statement simulations keep only `rsp rbp r15 r14` and memory (`SPost`, `SimStmt.lean`).
  Expression code also keeps every non-scratch register (`RPost.keep`).
* **`if c abort k` writes `rbx` on the path that does not abort** (`movRI .rbx k` before the
  test, `compileS`). Any function without a local in `rbx` therefore clobbers `rbx`. The first K=3
  prototype failed on exactly this (the prelude was rejected).

The compiled code (base `Init`, exact profile `scripts/asmprof.py`, 243.0 G instructions):
* frame stores: 23.7 G;
* frame loads: 12.6 G;
* prologue/epilogue: 13.0 G;
* result-register loads: 12.4 G;
* 4.73 G calls, 2.51 G of them to leaves.

Most frame accesses are not separate instructions. Here is `next_member` on master and with its
locals in `r12`/`rbx`/`r13`:

```
addq $1, (%rsp)        →  addq $1, %r12
cmpq $32, 16(%rsp)     →  cmpq $32, %r13
movq (%rsp), %rax; cmpq 1480(%r15), %rax   →  cmpq 1480(%r15), %r12
```

Only the pure loads (`movq (%rsp), %rax` before a use) disappear, and the parameter stores become
register moves. lnext §3.2 counted every frame touch as a saved instruction. That is why its −2.1 %
does not materialise (§3).

## 2. Options

| | convention | who pays | what the proof needs |
|---|---|---|---|
| A | callee-saved `rbx r12 r13`: every function saves the ones it writes (frame slots above its temporaries) and restores them before `ret` and before a tail call's jump | every call of a function that writes one: 2 instructions per register; this includes the hot leaves with 7–9 locals (`app_find`, `ilm_find`, `ilm_put`, `app_push`) | `FunSim` keeps `rbx r12 r13`; save/restore lemmas; statement simulations keep unallocated callee-saved registers |
| A′ | as A, but leaves prefer the caller-saved registers (`rsi`, then the result registers) | as A, plus leaves lose `retDirect` more often | as A |
| B | reserve R ⊆ {`r12 r13 rbx`} for non-leaf functions: leaves never use R (one register less), non-leaf functions save what they use of R | non-leaf calls (2 per register used); leaves with more than 9−\|R\| hot locals | as A |
| C | caller-saved: spill allocated locals around each call | every executed call site: 2 per allocated local live across it (needs liveness for precision) | liveness in the compiler, per-call spill/reload lemmas; the most proof work |
| D | **interprocedural** (IPRA): the compiler knows the whole program. Table `clob(f)` = the callee-saved registers `f` or anything it can reach writes. A non-leaf `f` that is not recursive takes registers outside `clob` of its callees, and needs no saves at all | nobody | `FunSim` keeps the callee-saved registers outside `clob(f)` (a compiler-computed table, like `Prog.nrt`/`Prog.skt`); same statement-level clause as A, no save/restore |
| D′ | D, plus functions in recursive SCCs save the registers they take (A restricted to SCC members) | recursive non-leaf calls | D + A's save/restore |

All options need **the abort stub**: `if c abort k` becomes one conditional jump to a per-code stub
`ca_abort_k: mov rbx, k; jmp ca_abort`. The stubs are emitted once, after the trampoline. Then no
path that continues writes `rbx`. On its own this saves one instruction per executed
`if c abort k` (`Init`: −0.09 %, 242.77 G against 242.98 G).

## 3. Prototype and numbers

`_tmp/nlregs/NL.lean` re-implements `compileFn`/`compileS`/`compileProg` around the master
code generator: the allocation per mode, saves, the call results and parameters into registers,
tail calls, and the abort stubs. It is run like `AsmEmit`:
`lake env lean --run NL.lean OUT.s K MINUSE LEAFMODE [stubs] [ipra] [CYCMIN]`. K = 0 gives a
`checker.s` byte-identical to master. Every variant accepts the prelude, and the main one passed
the verdict check (below).

**Exact instruction counts on `Init`** (`asmprof.py`, one thread; Δ against master's
242.98 G, split by whether the function is a leaf; `_tmp/nlregs/selfcost.py`):

| variant | non-leaf functions with registers | total | Δ leaves | Δ non-leaf |
|---|---:|---:|---:|---:|
| master | 0 | 242.98 G | | |
| abort stubs only | 0 | 242.77 G (−0.09 %) | | |
| A, K=3, uses ≥ 2 (`k3m2pref`, leaves A′) | 1,414 | 257.09 G (**+5.8 %**) | +4.5 G | +9.6 G |
| A, K=3, leaves unchanged (`k3m2old`) | 1,414 | 264.57 G (+8.9 %) | | |
| A, K=2 | 1,414 | 252.6–256.5 G (+4.0 to +5.6 %) | | |
| A, K=3, uses ≥ 8 (loop locals only) | 303 | 256.96 G (+5.8 %) | +11.1 G | +2.9 G |
| B, R = {`r12`}, uses ≥ 8 (`r1m8`) | 303 | 244.95 G (+0.8 %) | +0.9 G | +1.1 G |
| B, R = {`r12`, `r13`}, uses ≥ 8 | 303 | 246.29 G (+1.4 %) | | |
| **D, IPRA** (`ipra3m2mix`) | 147 | **242.21 G (−0.32 %)** | −0.06 G | −0.72 G |
| D′ (recursive functions save, uses ≥ 8; leaves in A′ order) | 183 + 3 recursive | 242.35 G (−0.26 %) | +0.21 G | −0.84 G |

Findings:
* **The per-call saves dominate.** The hot non-leaf functions are short: `mk_app` 71 instructions
  per call, `intern_app` 59, `ilg_go` 37, `env_find` 24 (164 M, 164 M, 257 M and 94 M calls).
  Six save/restore instructions are 10–25 % of such a function. Their locals are not in loops, so
  a register saves at most a load or two per call. The functions that gain (`next_member` −0.11 G,
  `beta_peel` −0.09 G, `env_row_get` −0.19 G) gain little.
* **Leaves pay for A.** 132–256 leaves write a callee-saved register. On `Init` that is +4.5 to
  +11 G, depending on whether they save it or give it up (`app_find` +1.2 G alone).
* **IPRA reaches few hot functions.** Almost every hot non-leaf function reaches a leaf that uses
  `r13`/`r12`/`rbx` (a leaf with one non-parameter local already takes `r13`), and 541 of the 1,426
  non-leaf functions are in recursive SCCs. Only 147 functions get a register. `line_rec`,
  `next_member`, `mk_app`, `intern_app` and `whnf_app` get none. The gain is real but small, and
  costs nothing.
* **Scanner** (`line_rec`, inclusive, `_tmp/scanfast/incl.py`):

  | variant | scanner instructions |
  |---|---:|
  | master | 12.92 G |
  | IPRA | 12.73 G (−1.5 %) |
  | B, `r12` | 12.86 G |
  | A, K=3 | 13.27 G (+2.7 %) |

  No variant brings it near con-ron's 11.8 G. The scanfast P2/P3 gap (15 %) came from the leaf
  allocation of a whole fast path, which has no calls; the new scanner's record loop calls its
  leaves.

**Cycles.** `bench.py --set init --reps 5 --no-conron --no-ref`, interleaved, four times:
* CPUs 40–41 at load 60–140;
* CPUs 40–41 at load 16–47;
* an idle core (17 and its SMT sibling 65), twice, at load 24–45 and at load 8–37.

The same binary varied between 81 G and 217 G cycles on `Init`, so the medians mean nothing. The
last bench's first two rounds ran while the machine was quiet. Cycles on `Init`, both rounds:

| binary | instructions | cycles, rounds 1 and 2 | against master (best run) |
|---|---:|---:|---:|
| master | 242.98 G | 81.1 G, 81.5 G | |
| IPRA (D) | 242.21 G | 82.1 G, 81.3 G | +0.2 % |
| B (`r12`) | 244.95 G | 81.9 G, 83.9 G | +1.0 % |
| A K=3 | 257.09 G | 83.0 G, 83.9 G | +2.3 % |

The best run of every binary over all four benches agrees within 2 %. **No variant is faster in
cycles; A is about 2 % slower.**
* A removes 12 G frame accesses (frame loads+stores 36.3 → 24.2 G). This does not outweigh its
  14 G extra instructions (saves, restores, register moves).
* The store-forwarding latency of `addq $1, (%rsp)` loops did not show up as a measurable cost.
* The instruction counts above are exact and do not depend on the load.

### 3.1 Default set

`bench.py --set default --reps 5 --cpus 17,65 --no-conron --no-ref`. Load 8–34 during the run. The
spread is 2–15 % except for `inmodel_nested` (34–54 %). Geometric means over the 13 fixtures,
against master:

| binary | instructions | cycles (median) | wall |
|---|---:|---:|---:|
| IPRA (D) | 0.997 | 1.001 | 0.995 |
| B (`r12`, uses ≥ 8) | 1.012 | 0.999 | 0.996 |
| A K=3 | 1.055 | 1.006 | 1.002 |

The largest inputs:

| input | instructions, A K=3 against master | cycles |
|---|---:|---:|
| `c04a_restart_70` | 19.75 G against 18.63 G (+6.0 %) | parity |
| `beta-ladder` | +4.1 % | parity |
| `let-ladder` | +4.4 % | parity |

Again: parity in cycles, more instructions.

### 3.2 Verdicts

`diff-e2e.py --bin … --refs --parallel 16` on 634 fixtures (a smoke check of the prototypes, not
evidence of correctness):

| binary | sequential | `--jobs 4` |
|---|---|---|
| IPRA (`ipra3m2mix`) | 634 agree, 0 REFDIFF | 634 agree |
| A K=3 (`k3m2pref`) | 0 UNSOUND, INCOMPLETE, CRASH, TIMEOUT or REFDIFF | not run |

Every other variant accepts the prelude. The first A build, before the abort stub, rejected it
(`rbx` clobbered by `if c abort k`, §1).

## 4. Proof plan (for D, and for A/B if they are ever wanted)

Correctness stays proved equivalence of the compiled code with L's semantics. Nothing is added
to the trusted base: the registers' convention lives inside the compiled code, and the trampoline
already saves `rbx r12 r13` for the C caller. **The per-function proofs (models, refinements,
error claims) do not change at all**: they are about L semantics, and the allocation is invisible
there. `checkerFile_eq`/`asm_lit` re-evaluate the compiler as before (one more table to
evaluate).

Changes, by file (estimates from the sizes of the lemmas they generalise):
1. **Compile.lean** (~150 lines):
   * the abort stubs;
   * `nlAlloc` and the `clob` table (`Prog.clt : NTree`, like `Prog.nrt`/`Prog.skt`: a bitmask of
     `rbx r12 r13` per function), and the `Bool` check `clobOk` that the kernel evaluates (for
     each `f`: its allocation ⊆ `clob f`; `clob g ⊆ clob f` and `alloc f ∩ clob g = ∅` for every
     callee `g`; a recursive `f` then has no callee-saved local, by the second condition);
   * the call-result and parameter moves into registers (`storeRes`/`zeroVars`/`storeParams` with
     an allocation).
2. **Rel.lean** (~80):
   * `AllocOk.leaf` (non-leaf → `alloc = []`) becomes "non-leaf → allocated registers are
     callee-saved and outside `clob` of every callee";
   * `Inv` gets a ghost clause: the callee-saved registers outside `clob ctx.fn` hold their entry
     values. Through a ghost field of `Ctx` that the code generator never reads, so `Inv`'s arity
     and its 155 uses stay; `compileS {ctx with ghost} = compileS ctx` by a 30-line induction.
     `Inv.congr`/`of_regs` already take "all `allocRegs` unchanged", which covers `rbx r12 r13`,
     so most re-establishments of `Inv` need no change. `Inv.congr'` and the register writes of
     allocated locals (`St.setReg_setLoc`) need the new case.
3. **SimStmt.lean** (~60): `sim_ifAbortK` with the stub (two more steps, and the `rbxFree` case
   disappears); the statements that write `rbx`.
4. **SimCall.lean** (~350):
   * `FunSim` gains "the callee-saved registers outside `clob f` are unchanged";
   * `sim_storeRes`, `sim_zeroVars`, `sim_regArgs` and `sim_callTail` lose `hal : ctx.alloc = []`
     and handle register locals as `sim_zeroLocals` already does;
   * `sim_call` re-establishes the allocated locals from `FunSim`'s new clause and `clobOk`.
5. **SimFun.lean** (~250):
   * `funSim` proves the new clause from the body's final `Inv` (ghost clause) and `clobOk`;
   * `sim_storeParams` for parameters moved into callee-saved registers;
   * `fnCtx_allocOk` for `nlAlloc`.
6. **SimTail.lean** (~60): a tail call from `f` to `g` keeps `clob g ⊆ clob f`.
7. **A/B only** (~250 more):
   * the save area: slots `[F₀, F₀ + K)` above the temporaries. The body is simulated with frame
     `F₀`, so `Pres G (top d F₀)` already says the saves survive the body; nothing in
     `SimStmt`/`SimBlock` changes;
   * save/restore lemmas (`sim_saveCode`, `sim_restCode`), restore before a tail call's jump;
   * the larger stack check (`F₀ + K`, `Prog.skt`).

Total for D: about 950 lines, 15–20 agent-hours, in the compiler files only (`ConAgua/Compiler/`,
17.6 k lines today). A/B adds about 250 lines.

Risks:
* `SimCall`/`SimFun` are among the largest compiler proof files; the larger `FunSim` statement may
  cost elaboration time and memory (keep it a `structure`, not a growing conjunction).
* The kernel evaluates `clobOk` and `Prog.clt` (1,838 functions, reachability) in `asm_lit`. It
  should be per-callee checks over the `NTree`, not a closure computation: `clob g ⊆ clob f` for
  direct callees suffices.

## 5. What would make it pay

* **Leaves taking fewer callee-saved registers.**
  * `leafAlloc` puts the first non-parameter local in `r13`, so nearly every leaf blocks IPRA for
    all its callers.
  * A leaf order that tries `rsi` and the free argument registers first (`retOk` permitting) gave
    IPRA 183 instead of 147 functions, but cost the leaves 0.21 G.
  * A profile-free rule that weighs a leaf's 7th–9th local against its callers' demand is the
    missing piece.
* **Inlining first** (lnext §3.1). Once the hot leaves of `mk_app`/`intern_app`/`ilg_*` are
  inlined, those non-leaf functions become larger, loop-carrying, and partly leaves. Registers in
  non-leaf functions are then worth more, and the saves are spread over more work. The two are
  better done in that order.
* **Freeing `rbp`** (store the trampoline's stack pointer in the table, `ca_finish` reloads it from
  `r15`) gives a fourth register without any convention.
* **Wall time** (§7). Store-to-load forwarding on frame slots is a real latency. Loop promotion
  removes it in hot loops for −1.0 % on `Init`, but non-leaf loops are too small a share of the
  run for more. Registers alone do not close the scanfast leaf/non-leaf gap.

## 6. Recommendation (revised)

No lane. No variant reaches the 2 % wall bar on `Init` or on the long fixtures (§7), so this
journal gives no proof plan for one. The order to try, if non-leaf registers come back:
1. **Inlining first** (lnext §3.1). It turns the short hot non-leaf functions into longer code with
   loops.
2. **Loop promotion** (`promoc`, −1.0 % on `Init`). The most local proof of all the options:
   * nothing changes in `FunSim` or in any convention;
   * the `while` simulation runs its body under a context with a larger allocation, between a load
     prologue and a store epilogue;
   * a call inside the loop is bracketed by spill and reload;
   * estimated 300–400 lines in `SimBlock`/`SimCall`.
3. **IPRA** (§4), about 950 lines.

**Drop the abort stub** as a speed item: it is +1.4 % slower in wall time despite fewer
instructions. It is only needed by the options that make `rbx` callee-saved.

## 7. Wall time, measured with paired statistics

**Method.** `_tmp/nlregs/wallbench.py` and `wallstats.py`. Each round runs every (fixture,
binary) pair once, in a fresh random order, pinned to one physical core (`taskset` on both SMT
threads of a core no other job used). Rounds were never discarded for load: the 1-minute load was
3.0–26.5 (median 4.8–4.9). Per fixture and variant, the round's ratio variant/master is one paired
sample, 15 rounds each. Reported:
* the median paired ratio, with a Wilcoxon signed-rank test (exact, two-sided). It is robust
  against the slow outlier runs (up to +50 %) that the load causes;
* the mean of the log ratios, with its 95 % t-interval (in `wall{2,3}.stats`).

**Bold** = Wilcoxon p < 0.05. All binaries were rebuilt from master aa459fa6, whose `checker.s` is
identical to that of §3's base. Fixtures: `Init` and the long default/full-set inputs.

Bench 1 (`wall2.json`, cores 17/65):

| fixture | master | IPRA | callee-saved (A) | `r12` reserved (B) | loop promotion, call-free loops | loop promotion with spills (`promoc`) |
|---|---:|---:|---:|---:|---:|---:|
| `Init` | 18.47 s | **−0.7 %** (p .035) | **+2.2 %** (p < .001) | −0.5 % (.073) | **+1.0 %** (.035) | **−1.0 %** (.008) |
| `app-lam` | 9.72 s | +0.2 % | **+0.8 %** (.012) | +0.2 % | +0.0 % | +0.4 % |
| `beta-ladder` | 2.40 s | −0.2 % | **+1.1 %** (.007) | +0.2 % | +0.4 % | +0.2 % |
| `let-ladder` | 0.97 s | −0.1 % | +0.3 % | +0.0 % | −0.3 % | −0.5 % |
| `c04a_restart_70` | 2.31 s | +0.2 % | −0.3 % | +0.2 % | −0.1 % | +0.1 % |
| `c05b_nest30_pi1000` | 1.32 s | −0.1 % | +0.4 % | −1.5 % (.121) | −0.3 % | +0.2 % |

Bench 2 (`wall3.json`, cores 21/69, run at the same time as bench 1):

| fixture | master | abort stubs only | callee-saved for 9 hot loop functions (`targ`) | callee-saved for the scanner loops (`targ4`) |
|---|---:|---:|---:|---:|
| `Init` | 18.27 s | **+1.4 %** (p < .001) | **+2.4 %** (< .001) | **+1.0 %** (.003) |
| `app-lam` | 9.73 s | +0.3 % | **+0.6 %** (.026) | +0.0 % |
| `beta-ladder` | 2.37 s | **+1.4 %** (.007) | **+1.8 %** (< .001) | +0.4 % |
| `let-ladder` | 0.95 s | +1.4 % | **+2.3 %** (.008) | +1.2 % |
| `c04a_restart_70` | 2.30 s | **+1.0 %** (.003) | **+1.7 %** (< .001) | **+0.9 %** (.012) |
| `c05b_nest30_pi1000` | 1.32 s | +0.1 % | +0.7 % | −0.1 % |

**The targeted variants** (step 2 of the reopened lane). `NL.lean` mode `targ`:
* the listed functions keep their loop locals (weighted use ≥ 8) in `r12 r13 rbx` and save them
  at entry;
* every leaf reachable from them that writes one of those registers saves it too (demand-driven:
  other leaves do not);
* the abort stubs are on, so non-leaf functions outside the set write no callee-saved register.

The functions were picked from the exact profile by where non-leaf code loops. On `Init`:

| function | loop instructions |
|---|---:|
| `whnf_app` | 3.6 G |
| `beta_peel` | 1.5 G |
| `next_member` | 1.0 G |
| `infer_spine` | 0.9 G |
| `sub_rec` | 0.9 G |
| `mk_app_n` | 0.65 G |
| `line_rec` | 0.5 G |
| `whnf_core_loop` | 0.5 G |
| `type_sort_pw` | 0.4 G |
| all non-leaf loops | 11.0 G of 243 G |

They run 1–5 iterations per call.
* With all nine, 113 leaves must save (`whnf_app` reaches nearly everything). That is +11 G
  instructions and +2.4 % wall.
* With the scanner's three (`targ4`: `line_rec`, `next_member`, `sub_rec`), 5 leaves save: −0.11 G
  instructions, +1.0 % wall. That is −0.4 % beyond the stub's own +1.4 %, if the two add up.

`promo`/`promoc` (loop promotion, mode argument 8 of `NL.lean`) need no convention at all.
* A loop of a non-leaf function is promoted if its weighted uses are ≥ 8.
* `promo`: only loops without calls. They are cold on `Init` (−0.02 G instructions).
* `promoc`: also loops with calls, spilling the promoted locals before each call and reloading
  them after. +2.0 G instructions (+0.8 %), but −1.0 % wall on `Init`: the loop-carried values no
  longer go through memory between the calls.

**Scanner** (`line_rec` inclusive, exact instructions on `Init`; wall is not separable from
`Init`):

| variant | scanner instructions |
|---|---:|
| master | 12.92 G |
| IPRA | 12.73 G |
| `targ4` | 13.02 G |
| `promoc` | 13.93 G |

None helps the scanner toward con-ron's 11.8 G.

**Verdicts** (`diff-e2e.py --refs --parallel 16`, 634 fixtures):

| binary | sequential | `--jobs 4` |
|---|---|---|
| `promoc` | 634 agree, 0 REFDIFF | 634 agree |
| `targ4` | 634 agree, 0 REFDIFF | not run |
| IPRA | as in §3.2 | as in §3.2 |
