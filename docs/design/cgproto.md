# Lane cgproto: the codegen leftovers after the inliner (analysis journal)

Question (lnext2 §2, rank 6): after the inliner, how much do the remaining generic overheads of the
code generator cost, one by one, and which of them are worth a proof? lnext2 measured bounds checks
4.9 % of `Init`'s instructions, the fuel and stack check 5.6 %, "result registers" 5.8 %, and
`der_b` 10.3 % (613 M calls).

Base: master 5b7f6d65 (`checker.s` with the proved inliner, `checkerProgI`). Nothing landed but this
journal. Unproved prototypes, assembly, binaries, profiles and bench data: `_tmp/cgproto/`
(`proto/CG.lean`, `s/`, `bin/`, `prof/`, `wb*.json`, `py/`).

**Answer in short.** Wall time moves by about half of the instruction change or less, and at 16
threads by less still:

* **Bounds checks** (`bce`, a local range and facts analysis): −2.0 % instructions on `Init`,
  **−2.5 % wall at one thread** (p 0.002), −1.4 % at 16 threads, −1.6 % on app-lam, −0.7 % on c05b,
  no change in the parse phase. It is the only candidate near the 2 % bar. Removing *every* bounds
  check (unsafe, the ceiling) gives −6.5 % instructions but only −3.5 % wall at one thread and
  −2.5 % at 16.
* **Fuel** (`fleaf`, no fuel at calls of leaves): −1.7 % instructions, −1.5 % wall at one thread.
  No fuel at all (the ceiling): −2.3 %.
* **Stack checks** (`stk`, only recursive functions check): −1.7 % instructions, −1.4 % wall.
* **"Result registers"** was mostly a misattribution: the 5.8 % are call *arguments* loaded from the
  frame. The result-side leftovers (dead result stores, store-then-reload) are −0.4 % and −0.2 %
  of instructions; their wall effects (−1.0 %, −1.2 %) come with +2.5 % in the parse phase, i.e.
  layout.
* **`der_b`**: 613 M calls is one per node the walks visit (the twin's loose-bvar-range cut) plus
  two per `mk_app` miss: the count is the algorithm's. Its per-call cost (40 instructions) has two
  L-level leftovers: a saturating successor by multiply-select, which makes it keep a frame
  (`derbr`: −1.2 % instructions), and two results computed for the six walk call sites that read
  only the first (`derbv`: −0.8 %). Wall: within ±0.4 % on `Init`, and +1.1 to +1.3 % in the
  parse phase (layout).
* **All of them together** (`all2`): −7.7 % instructions, −3.5 % wall at one thread, −1.2 % at
  16 threads.

**Recommendation** (§6): no implementation lane for fuel, stack, results or `der_b`; the bounds-check
analysis is a candidate only if a one-thread gain of 2.5 % is worth 25–40 h of compiler proof, and
it does not move the 16-thread time (−1.4 %), which is where the gap to con-ron is.

## 1. Method

`proto/CG.lean` (run as `lake env lean --run CG.lean OUT.s VARIANTS`) is master's code generator
from `Compiler/Compile.lean` (`simpleOp` to `compileProg`, 1,290 lines copied unchanged) with:
* a context `PCtx extends Ctx` that adds the variant flags, the facts of the bounds-check analysis
  and the set of locals the function reads;
* `gen`, `compileE`, `compileS` turned into thin wrappers around the copied functions (`gen0`,
  `compileE0`, `compileS0`), which drop the access's own `cmp; jcc ca_error` pair when the analysis
  proves the index in range;
* the fuel, stack-check and result-store points parameterised.

The program is `checkerProg`, optionally rewritten at L level (`derbv`, `derbr`), then inlined as on
master (`inlineProg 80 t 1`). **With no variant the output is byte-identical to master's `checker.s`**
(checked with `cmp`). `CA_PARSEONLY=1` cuts `check_a` after the parse (internspeed's `cutAt`) for
the parse-phase binaries.

Measurements:
* Exact instruction counts: `scripts/asmprof.py` on `Init`, c05b, app-lam, and on `Init` with the
  parse-only binaries. The finer categories below come from `py/ana.py`, which also separates fuel
  checks from stack checks, call arguments from results, and the compiler's bounds checks from `if
  … abort` checks.
* Wall time: paired interleaved rounds, with every variant of one fixture run back to back in random
  order (`wb2.py`, a variant of internspeed's `wb.py`), median paired change and Wilcoxon p
  (`wstats.py`). One thread pinned to CPUs 44,92 (one core, both SMT threads), 16 threads to 24–39.
  Main runs: `wb1b` (16 rounds, all four one-thread cells, load median 2.4), `wb1c`/`wb1d` (10
  rounds, quiet machine, load 2.0–9.1), `wb16c` (40 rounds, load 1.9–9.3). The first runs (`wb1`,
  `wb16`, `wb16b`, load up to 33) are kept in `_tmp/cgproto/` but were too noisy (±10–20 % CIs) to
  use.
* Verdicts: `scripts/diff-e2e.py --bin <variant> --refs` on every variant (the unsafe ceilings too).
  The combined variant `all` also ran with `--jobs 16`. **634 of 634 agree, REFDIFF 0, in every
  variant.**

## 2. Where `Init`'s instructions go now

Master's `checker.s` (inlined): 232.39 G instructions, 4.09 G calls (3.57 G `call`s, the rest tail
calls).

| what | share | instructions | notes |
|---|---:|---:|---|
| compiler bounds checks (`cmp` + `jae`/`jbe ca_error`) | **6.5 %** | 15.15 G | lnext2's 4.9 % missed the checks against a register index and on tiered and 32-bit accesses |
| `if … abort` checks of the L code | 0.9 % | 1.99 G | not the compiler's |
| fuel (`subq $1, %r14` + `jb`) | 4.2 % | 9.77 G | 3.57 G calls, the rest tail calls and loop back edges |
| stack check (`mov rsp`, `sub`, `cmp`, `jb`) | 3.6 % | 8.40 G | 2.10 G checks, in non-leaf functions |
| call arguments loaded from the frame | 4.6 % | 10.61 G | these are lnext2's "result registers (load)" |
| results loaded before a `return` | 0.7 % | 1.71 G | |
| results zeroed before a `return` | 0.3 % | 0.71 G | mostly `der_b`'s `return (0, 0, 0)` |
| results stored after a call | 2.9 % | 6.69 G | |
| store, then reload of the same slot | 0.35 % | 0.81 G | |
| `der_b` | 10.5 % | 24.42 G | 613 M calls, 40 per call |

## 3. The candidates

### 3.1 Bounds checks

**The analysis (`bce`).** Forward, per function, over the L statement, with no knowledge from other
functions:
* facts `i < len(A)` (the array, or for a tiered access the array and its tier expression), where
  `i` is built from locals, constants and operators;
* exclusive upper bounds `x < n` of locals;
* locals that hold a length.

What makes a fact:
* a condition, in the branch where it holds: `i < len(A)`, `len(A) ≤ i` negated, `x < e` or
  `x ≤ e` with a bounded `e`, `x == k`;
* an access that ran: its check passed. This includes accesses earlier in the same `return` or
  argument list, in the order the code generator evaluates them;
* an assignment `x := e` with a bounded `e` (bounds from constants, `&`, `>>`, `<<`, `+`, `*`, `|`,
  bytes, 32-bit loads, comparisons).

What removes a fact: any write to a local it mentions (`set`, call results, `scan8`). At a loop
head, every local the body writes is forgotten. After a loop, the exit condition holds only if the
body has no `break`. The two branches of an `if` are joined; `return`, `break` and `abort` end a
path. Array lengths never change while L code runs: no statement writes them. Then:
* a check is dropped when its fact holds, or when the index's bound is at most the array's
  minimum length (`Tab.min64`, twice that for 32-bit elements);
* the code generator emits the access as before, and the wrapper removes its own check (the last
  `cmp; jcc ca_error` pair within the access's last four directives; constant indices that the
  generator already left unchecked are left alone).

| | static checks | dynamic check instructions on `Init` |
|---|---:|---:|
| master | 6,993 | 15.15 G |
| `bce` | 5,779 (−1,214) | 10.52 G (**−31 %**) |
| `nobc` (all removed) | 0 | 0.17 G (`ld8x8`'s own) |

What the analysis removes:
* in `der_b` and the many places that read a table's count, the `CTL.u64[k + t]` check, where `t` is
  a tier (`(h >> 27) & 1`, at most 1);
* repeated accesses to the same node (`APP⟨t, i⟩.f` then `.a`);
* loop counters checked against the same length.

What it cannot remove (the remaining 10.5 G, the top 40 sites read in `py/hotb.py` output):
* **a handle checked against its table's count, then used to index the table's columns**
  (`if APP⟨t⟩.count <= i { … }; ADER⟨t⟩.u32[i]`; `der_b`, `ilg_app`, `get_app_spine`, `il_bvar`,
  `e_view`, `unfold_definition`, …), about 40 % of what remains. It needs the invariant `count ≤
  len` of every column, which the push functions maintain. That is a property of the program, not
  of one function: the compiler can only use it as an assumption that the per-function proofs
  discharge, which is not a generic technique;
* hash probes `(h & mask) * 4 + k < len` (`ilm_find`, `app_find`, `apd_find`), which need `mask <
  len / 4` (again an invariant);
* runs of stores `R[4c]`, `R[4c+1]`, … (`ilm_put`, `app_push`), where only the first is checked
  from local facts, and `x + 1 < len` then `x < len` (`env_row_get`), which needs no wraparound of
  `x + 1` (unknown for a parameter);
* spine offsets `sp + k < len` in `whnf_app` and `mk_app_n`.

Wall (`wb1d`, quiet): `Init` one thread **−2.5 %** (p 0.002, 95 % CI of the mean [−2.9, −2.0]);
`nobc` −3.5 % ([−3.9, −3.1]). The local analysis gets 70 % of the wall ceiling with 31 % of the
dynamic checks. The `CTL[k + t]` checks it removes sit on the dependency chain from the handle to
the count compare, so they cost more than their count. 16 threads (`wb16c`): −1.4 % (p 0.002),
`nobc` −2.5 %.

### 3.2 Fuel and the stack check

**`fleaf`: no fuel at calls (and tail calls) of leaves.** Leaves call nothing, so along any chain of
nested calls at most one call is a leaf call. L's fuel is a depth (a call runs its callee at `n −
1`, a loop iteration re-enters at `n − 1`), and the machine's `r14` counts every burn. So a run that
skips the leaf burns needs at most one more unit of L fuel than the machine burnt, the same kind of
slack as the inliner's `abiInl` (inline.md §3). Instructions −1.70 % (fuel 9.77 → 5.82 G).
Wall: `Init` −1.5 % (p 0.002), app-lam −0.5 %, c05b +0.6 %, parse +1.4 % (both p ≤ 0.001: layout).

**`nofuel`** (ceiling: no fuel anywhere; the final theorems as stated need it): −4.2 % instructions,
`Init` −2.3 % wall at one thread, −1.0 % at 16.

**`stk`: stack checks only in recursive functions.** A function on no call cycle (541 of the 1,816
functions are on one) does not check. Its callers check for its whole static depth: frame, plus one
word and the depth of its deepest non-checking callee. This is master's `Stmt.need`/`Prog.skt` for
leaves, extended from leaves to the call DAG. 1,165 functions skip the check; dynamic checks fall
from 2.10 G to 1.13 G. Instructions −1.66 % (`Init`), −3.86 % in the parse phase. Wall: `Init`
−1.4 % (p 0.002), parse −1.2 % (p < 0.001), app-lam and c05b unchanged. `stack_fuel_offset` (the
deep-stack fixture) still agrees.

### 3.3 Results

lnext2's "result registers" (5.8 %) is asmprof's pattern `movq N(%rsp), %rdi|r8|…`, which mostly
matches the **arguments** of calls (4.6 %). A function without locals in registers (every
non-leaf) must load them; nlregs measured the alternatives (no gain). What is left on the result
side:
* **`dres`**: a call result the caller never reads is not stored (`ilg_app`'s `u := call ilm_put…`,
  the `e0` of `(fd, j, e0) := call ilm_find…`): −0.41 % instructions. Wall `Init` −1.0 % (p 0.037),
  parse **+2.5 %** (p 0.002).
* **`peep`** (a text-level peephole on `checker.s`): `mov %r, N(%rsp)` directly followed by `mov
  N(%rsp), %r'` becomes a register move or nothing (1,036 sites): −0.19 % instructions, `Init`
  −1.2 % wall (p 0.006; a store-to-load forwarding latency on the critical path, not the count).
* Results loaded or zeroed before `return` (1.0 % together) are needed by the convention.

### 3.4 `der_b`

Where the 613 M calls come from (exact call counts, by call site):

| caller | calls | why |
|---|---:|---|
| `ilg_go` | 257 M | once per node of the memoised instantiate walk: the cut `looseBVarRange(e) ≤ d` |
| `mk_app` | 146 M | twice per cache miss, to build the new node's derived word |
| `il_go`, `il_bvar` | 67 M each | the plain instantiate walk, and the substituted value's range |
| `lp_go` | 31 M | the level-parameter walk |
| `ab_fvb`, `mk_lam`, `mk_forall`, others | 45 M | |

`ilg_go` is called twice per `ilg_app` (196 M of its 257 M calls). Each visited node is checked once,
as in the twin (`instantiateListGo` calls `instListCutoff` first). The number of calls belongs to the
algorithm; no L-level reordering lowers it without departing from the twin.

The cost per call (40 instructions; tags: app 46 %, bvar 27 %, const 11 %, lam 9 %):
* the tag chain, already in frequency order (4, 0, 3, 5, 1, 6, 2, 9, 7);
* the tier gate;
* the count check (`CTL[k + t]` with its bounds check, removed by `bce`);
* the element's bounds check (needs `count ≤ len`, §3.1);
* the call, the frame and the result moves;
* for a bvar (27 % of calls), the saturating successor `(x + 1) * (x < 32767) + 32767 * (32767 ≤
  x)`: 18 instructions, and the temporaries it needs give `der_b` a frame (`subq/addq $56, %rsp`).

Variants:
* **`derbr`** (L rewrite): the saturating successor as `if x < 32767 { return x + 1 … } return 32767 …`.
  `der_b` becomes frameless. Instructions −1.21 % on `Init`.
* **`derbv`** (L): a copy `der_bv` that returns only the first result, called at the six walk
  sites that read only that (`bvar_b`, `il_bvar`, `il_go`, `ilg_go`, `inst_go`, `lift_go`). −4
  instructions per call: −0.75 %. Its 340-node body is far above the inliner's 80.
* **`derbrv`**: both, −1.93 %.
* **`S350`** (the inliner's bound raised so that `der_b` inlines): +23 % code (234,301 directives),
  −0.10 % instructions. Not useful.

Wall: `derbr` `Init` −0.4 % (p 0.13), parse +1.1 % (p 0.027); `derbrv` `Init` −0.2 % (p 0.25),
app-lam −0.3 %, c05b +0.4 %, parse +1.3 %. The saved instructions do not show: `der_b`'s branches
are well predicted, and the work that remains is the two dependent loads.

## 4. All variants

Instructions (exact, change against master):

| variant | `Init` | parse phase | c05b | app-lam |
|---|---:|---:|---:|---:|
| master | 232.39 G | 18.98 G | 14.29 G | 50.17 G |
| `bce` | −1.99 % | −1.40 % | −1.50 % | −2.45 % |
| `nobc` (unsafe) | −6.45 % | −4.18 % | −7.80 % | −9.37 % |
| `fleaf` | −1.70 % | −1.82 % | −1.71 % | −1.47 % |
| `nofuel` (unsafe) | −4.20 % | −4.46 % | −4.20 % | −3.88 % |
| `stk` | −1.66 % | −3.86 % | −1.29 % | −0.65 % |
| `dres` | −0.41 % | −0.21 % | −0.58 % | −0.34 % |
| `peep` | −0.19 % | | | |
| `derbv` | −0.75 % | 0.00 % | −0.06 % | −0.85 % |
| `derbr` | −1.21 % | −0.18 % | −0.35 % | −0.93 % |
| `derbrv` | −1.93 % | −0.18 % | −0.40 % | −1.77 % |
| `all` (bce, fleaf, stk, dres, derbv) | −6.52 % | −7.29 % | −5.14 % | −5.76 % |
| `all2` (`all` + derbr) | −7.70 % | −7.47 % | −5.49 % | −6.69 % |

The effects add up almost exactly (the sum of the parts of `all` is −6.52 %).

Wall, median paired change (Wilcoxon p; **bold**: p < 0.05). One thread: `Init` from `wb1d` (bce,
nobc, fleaf, stk, all2) and `wb1c` (the others), the other cells from `wb1b`; 16 threads: `wb16c`.

| variant | `Init`, 1 thread | `Init`, 16 threads | parse | c05b | app-lam | verdicts |
|---|---:|---:|---:|---:|---:|---|
| master | 17.32 s | 3.50 s | 1.73 s | 1.29 s | 9.72 s | 634/634 |
| `bce` | **−2.5 %** (0.002) | **−1.4 %** (0.002) | −0.5 % (0.13) | **−0.7 %** (0.003) | **−1.6 %** (< 0.001) | 634/634 |
| `nobc` | **−3.5 %** (0.002) | **−2.5 %** (< 0.001) | **−0.4 %** (0.037) | | | 634/634 |
| `fleaf` | **−1.5 %** (0.002) | | **+1.4 %** (< 0.001) | **+0.6 %** (0.001) | **−0.5 %** (< 0.001) | 634/634 |
| `nofuel` | **−2.3 %** (0.002) | **−1.0 %** (0.044) | −0.2 % (0.32) | | | 634/634 |
| `stk` | **−1.4 %** (0.002) | | **−1.2 %** (< 0.001) | +0.2 % (0.23) | +0.1 % (0.13) | 634/634 |
| `dres` | **−1.0 %** (0.037) | | **+2.5 %** (0.002) | | | 634/634 |
| `peep` | **−1.2 %** (0.006) | | −0.0 % (1.0) | | | 634/634 |
| `derbr` | −0.4 % (0.13) | | **+1.1 %** (0.027) | | | 634/634 |
| `derbrv` | −0.2 % (0.25) | | **+1.3 %** (< 0.001) | **+0.4 %** (0.001) | **−0.3 %** (< 0.001) | 634/634 |
| `all2` | **−3.5 %** (0.002) | **−1.2 %** (0.011) | **+1.9 %** (< 0.001) | −0.3 % (0.051) | **−1.5 %** (< 0.001) | 634/634 |

`wb16b` (60 rounds at load 8–28) put `fleaf`, `stk` and `derbrv` at 16 threads within ±0.5 %, none
significant. The parse phase moves by +1 to +2.5 % for changes that save instructions there
(`fleaf`, `dres`, `derbr`, `all2`): the effect of code layout that nlregs saw (1–2 %). It sets the
noise floor for any single change below about 2 %.

## 5. Proof cost (rough)

| variant | what the proof needs | estimate |
|---|---|---|
| `bce` | a soundness theorem for the analysis: its facts hold of the L state at every point (`post`, `condAll` and the loop kill sets, by induction on `exec`); the facts threaded through `SimExpr`, `SimStore`, `Sim32`, `SimGen` and `SimStmt`, with a check-free variant of each load and store lemma (about 40 `errorL` sites); the analysis evaluated by the kernel in the whole-program checks (`asm_lit`), whose cost must be measured | 25–40 h, ~1,500 lines in `Compiler/` |
| `fleaf` | `FunSim` for a leaf callee with `r14 ≤ n` instead of `< n`, one unit of reserve in non-leaf code, the leaf test in `SimCall`/`SimTail`, `abiInl` + 1 in `MainRef` | 10–16 h |
| `stk` | the static depth table (`Prog.skt` generalised to the call DAG, with a kernel-checkable acyclicity witness), the prologue lemma for non-leaf functions that skip the check, `Stmt.need` over it | 10–20 h |
| `dres` | an L → L pass that drops trailing unread call results, with a "locals nobody reads do not matter" simulation (as the inliner's shift layer) | 8–15 h |
| `derbr` | the rewritten `der_b`; `derB_spec` is `vcgen` + `grind` and should go through as it is | 1–3 h |
| `derbv` | a new L function, its spec (the first result of `derBW`), six walk proofs switched to it | 4–8 h |

## 6. Recommendation

* **No lane for `fleaf`, `stk`, `dres`, `peep` or `der_b`.** Each saves 1–2 % of the instructions.
  Each shows −1 to −1.5 % wall on `Init` at one thread, nothing measurable at 16 threads, and a few
  of them +1 to +2.5 % in the parse phase. That is within the layout noise and below the 2 % bar.
  The `der_b` rewrite (`derbr`, 1–3 h) costs little enough to fold into a lane that touches
  `ExprMk` anyway. It does nothing for wall time by itself.
* **The bounds-check analysis is the one borderline winner**: −2.5 % at one thread, −1.4 % at 16,
  −1.6 % on app-lam, for 25–40 h of compiler proof (§5), plus whole-program kernel time still to
  measure. It is generic (local facts only) and needs no new primitive. It belongs after the
  16-thread work of lnext2 ranks 4–5 (the parser's `der`, in-place table growth). Those target the
  remaining gap to con-ron (1.09× at 16 threads, app-lam 1.82×) directly, while this analysis does
  not change the 16-thread picture.
* **What would remove most of the remaining bounds checks** is a different kind of fact: `count ≤
  len` of each table and its columns. That is a program invariant, not a local fact. A generic
  route is an L-level `assume` that the per-function proofs discharge, a new primitive and a
  per-program obligation, so it is out of scope by the rules (generic techniques, minimal
  primitives). Even all checks removed is worth only −3.5 % / −2.5 % wall.
* **The instruction count overstates wall gains here by about 2×.** `all2` saves 7.7 % of
  `Init`'s instructions and 3.5 % of its one-thread time. Future codegen work should be judged on
  wall time from the start (§1's method: variants back to back, Wilcoxon).
