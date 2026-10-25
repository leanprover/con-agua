# Lane `perfgap`: why is L slower than con-ron on Init? (journal)

Branch `perfgap`, worktree `_tmp/wt/perfgap`, scratch `_tmp/perfgap`. Investigation only: nothing
proved or landed. Base: master 1134dff6 (`asm/checker.s` as committed), Init = `init435.ndjson`
(346 MB), con-ron = `_tmp/ref/con-ron-integrate` release (`--jobs=1`, rev 12752ca7 = `vendor/UPSTREAM`).

## 1. The gap depends on the machine load

| | instructions | cycles (user) | wall | IPC | peak RSS |
|---|---:|---:|---:|---:|---:|
| L, load ~10 (`perf stat`, one run) | 359.1 G | 104.2 G | 23.7 s | 3.45 | 773 MB |
| con-ron, same time, other core | 186.2 G | 79.6 G | 18.2 s | 2.34 | 495 MB |
| L, `bench.py` load 11, min of 4 | | 97.6 G | 22.1 s | | |
| con-ron, same | | 78.2 G | 17.7 s | | |
| L, `bench.py` load 26–40, min of 3 | | 125.5 G | 30.4 s | | |
| con-ron, same | | 85.8 G | 20.0 s | | |

On a quiet machine L is **1.25–1.30×** con-ron in cycles and wall (1.93× in instructions). Under
load L loses another 29% of cycles, con-ron 10%: L is instruction-bound (IPC 3.45), con-ron is
memory-bound (IPC 2.3), and an SMT sibling under load takes issue slots, not memory latency. That is
where the user's 1.6–1.9× (39 s vs 24 s at load 25–45) comes from. Cache misses: L 303 M, con-ron
366 M; branch misses: L 318 M, con-ron 595 M. Memory is not the gap any more (lanes memlay,
slotgrow, tierswitch).

## 2. The whole gap is the code generator

`scripts/perfgap/l2c_abi.py` (compopt2's `l2c.py`, ported to tiered arrays, block ops, globals in the
table and the current ABI; the real entry stub of `asm/checker.s` calls the C `ca_enter`) translates
`checkerProg` to C with L's semantics: bounds checks that abort, fuel at every call and loop back-edge,
zeroed locals, the same data layout. `clang -O2` of it is the **perfect-compiler oracle**. Verdict on
Init: accept.

`bench.py --reps 5 --cpus 75` (interleaved; load 13–30; **minimum** over the rounds, the least
disturbed run; medians in `_tmp/perfgap/bench_v2.log` are noisier but agree in direction):

| system | instructions | cycles | wall |
|---|---:|---:|---:|
| L (master) | 359.1 G (1.000) | 97.9 G (1.000) | 22.2 s (1.000) |
| clang -O2 oracle | 231.6 G (0.645) | 71.5 G (0.730) | 16.2 s (0.730) |
| clang -O2 -fno-inline | 257.3 G (0.717) | 77.7 G (0.793) | 17.6 s (0.794) |
| clang, non-leaf locals `volatile` | 285.7 G (0.795) | 88.7 G (0.906) | 20.1 s (0.906) |
| L without fuel and stack checks (asm sed) | 329.4 G (0.917) | 96.2 G (0.983) | 22.0 s (0.989) |
| L without bounds checks (asm sed) | 332.6 G (0.926) | 94.4 G (0.964) | 21.4 s (0.964) |
| L without both | 302.8 G (0.843) | 90.2 G (0.921) | 20.4 s (0.921) |
| con-ron | 186.2 G (0.519) | 78.1 G (0.797) | 17.7 s (0.797) |

(Instruction counts of the other oracle variants, one run each: no bounds 188.7 G, no fuel 197.9 G,
neither 152.0 G, all locals `volatile` 337.1 G; the oracle's fuel is a memory decrement, so its fuel
share is larger than the asm's.)

**The L program compiled by clang is 9% faster than con-ron** (cycles and wall), with the same
bounds checks and fuel. The algorithms, the data layout and the open deviations cost nothing
measurable: `ilm_clear` 0.54% of the instructions, `scratch_reset` 0.01% (D37), `rf_find` 0.002% (D40),
`iw_copy`/`sl_cons` < 0.01% (D18), no D12 effect visible in the probe counts. con-ron in turn spends
~10% of its cycles in mimalloc and Vec copies/drops (`_mi_theap_malloc_zero`, `mi_free`,
`eidx_vec_dup_from`, drop glue) that L does not have.

## 3. Where the compiler loses

Exact per-function counts on both sides: `asmprof.py` (fixed on this branch to link
`harness/main.c`; its `run` with `harness/e2e.c` dies in `cap_check` on the current asm) for L, and
`scripts/perfgap/bbcount.py` (block counters with `pushfq`/`popfq`, `-mno-red-zone`) for
`clang -O2 -fno-inline` of the oracle, so both have the same function boundaries. Call counts agree
exactly (e.g. `der_b` 612,690,171 both). `join.py` lines them up.

L 359.1 G against clang-no-inline 250.6 G: gap 108.5 G.

| | L | clang -fno-inline | gap |
|---|---:|---:|---:|
| leaf functions | 203.1 G | 123.1 G | **79.7 G** |
| non-leaf functions | 156.0 G | 127.5 G | 28.5 G |
| of which the hash tables (`*_find/_put/_push/_clear`, instances of ConsLib/MemoLib) | 113.1 G | 64.7 G | **48.3 G** |
| of which `der_b` | 36.8 G | 26.4 G | 10.3 G |

Top of the gap (instructions per call, L vs clang): `der_b` 60.0/43.1, `app_find` 110.9/64.7,
`ilm_put` 122.2/60.1, `ilm_find` 94.8/65.4, `app_push` 171.5/76.7, `mk_app` 102.7/67.3, `app_fill`
153/72, `intern_app` 72/53, `key_end` 57.8/20.9. The first six are 42% of the gap.

L's own categories (`asmprof`, 359.1 G, 4.99 G calls): frame load+store 62.5 G (17.4%; 22 G of it in
leaves: binary-operator temporaries such as `movq %rax, 56(%rsp)` … `movq 56(%rsp), %rax`), zero
locals 17.1 G (4.8%), prologue/stack check 17.7 G (4.9%), fuel 16.5 G (4.6%), result registers
load/zero 20.5 G (5.7%), bounds checks 23.8 G (6.6%) + base loads 9.6 G, constants 18.0 G (5.0%).
The most frequent removable patterns each stay small: `mov $C, rax; cmp X, rax` 6.6 G,
`mov r, rax; op …, rax; mov rax, r` 3.9 G, `mov rax, r; mov r, rax` 1.8 G, the zeroing triple
`movq $0, M(%rsp)` ×3 9.5 G.

Non-leaf register allocation is worth at most the non-leaf gap (28.5 G, 8%; compopt2's prototype R,
three callee-saved registers, gained nothing). The `volatile` variant overstates it (`volatile`
blocks more than register allocation).

## 4. Ranked causes (≥ 10% of L's cycles)

1. **Leaf-function code quality of the naive compiler** — the only cause above 10%. Estimate: the
   non-inlining part of the compiler gap is 20.7% of L's cycles (clang -fno-inline 0.793), and leaves
   carry 73% of its instructions: **~15% of cycles, 80 G instructions (22%)**. Under load the gain
   is larger (cycles follow instructions there). Concentrated in one template: the ConsLib/MemoLib
   hash functions are 31.5% of L's instructions and the oracle does them in 57% of that.
   It is spread over many small patterns (rax-accumulator expressions, frame temporaries, constant
   materialization, no CSE of the slot-address arithmetic `(r11+rsi)<<2` and its +1/+2 forms, the
   length reloaded from the table for every check, frames and stack checks in leaves that keep all
   locals in registers, e.g. `der_b`'s 56-byte frame). None is above ~2% alone.
   Fix approaches: (a) compiler: a better leaf backend — an expression evaluator with a register
   stack instead of frame temporaries, operands in place (`cmp reg, imm`, `op` into the destination),
   CSE of array-index expressions within a straight-line block, frameless leaves whose stack check
   moves to the caller (leaves do not recurse). Each piece is a local simulation lemma in `Compiler/`
   (the style of compopt2's E3 and tiercost's B); all together maybe 2/3 of the leaf gap; cost:
   several compiler-proof lanes, no twin deviation, no change outside `Compiler/`. (b) L-level: a
   leaner hash template (one bounds check per slot via a slot-sized record access, the key words
   compared through one tiered record load, the region/stamp reads hoisted), proved once in the
   generic library; estimate 3–5% (it helps both compilers); cost one library lane, no deviation
   (layout only).
2. Inlining small leaves: 6.3% of cycles (clang 0.730 vs clang -fno-inline 0.793), 26 G instructions.
   Below the bar; compopt2's naive inlining prototype I gained nothing without the optimisation after
   it.
3. Fuel + stack checks 1.7%, bounds checks 3.6%, together 7.9% of cycles (8.3% / 7.4% / 15.7% of the
   instructions): cheap on Zen 5 (predicted, fused). Below the bar; dropping bounds checks would need
   per-access in-bounds proofs at L level.
4. Non-leaf register allocation: at most 8% of the instructions, likely less in cycles. Below the bar.

No algorithmic, data-layout or deviation cause reaches 1%.

## 5. Files

`_tmp/perfgap/`: `base.s` (= `asm/checker.s`), `oracle.c` + `stub.s`, variants `o_*.bin`/`base_*.s`,
`prof.report`/`prof_all.report` (asmprof, L), `noinl_all.report` (bbcount, clang -fno-inline),
`join_all.txt`, `R.top`/`L.top` (`perf record`, con-ron and L; note `perf`'s instruction samples on
this AMD pile up behind cache misses: `app_find` 12.8% sampled vs 5.3% exact), `bench_base.*`,
`bench_var.*` (load 26–40), `bench_v2.*` (load 13–30).
