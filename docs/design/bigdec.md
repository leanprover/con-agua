# Lane bigdec: subquadratic decimal literals (`nat_dec`)

Goal (2026-11-18): `nat_dec` should be no worse than con-ron's `frontend/nat_decimal.rs`
(task #159, de06320f) in its algorithm.

## Before

`nat_dec(c, d)` read the digits nineteen at a time. Each chunk was folded into all the limbs
read so far by one `nat_mad` pass, so `n` digits cost `O(n² / 19)` word operations.

## Design

* `nat_dec(c, d)` now only dispatches. A literal of at most `decBase` digits goes to
  `nat_dec_chunks`, which is the old chunk loop unchanged. A longer one goes to `nat_dec_big`.
* `nat_dec_big(c, d)` first reserves `2k` words at the pool top `T` for the index of a power
  table: `(address, length)` for each `P[t] = 10^(19 · 2^t)`, `t < k`. Here `k - 1` is the
  largest `t` with `4 · 19 · 2^t ≤ d - c`, as in con-ron's `power_table`. It writes
  `P[0] = 10^19` as one limb at `T + 2k`. It builds each next power by
  `nat_mul(P[t], P[t])`, which appends at the top. Then it calls
  `nat_dec_split(c, d, T, k)` and copies the result down to `T`.
* `nat_dec_split(c, d, tbl, k)` reads at most `decBase` digits with `nat_dec_chunks`. For a
  longer run it takes `dd = 19 · 2^t`, the largest with `4 dd ≤ len`, as con-ron's
  `split_level` does. The high part `[c, d - dd)` is the longer one. The function recurses on
  both parts and computes `nat_add(nat_mul(hi, P[t]), lo)`. Then it copies the sum down to the
  top it started from (`copy!`), so that the scratch stays `O(n)`.
* `nat_dec_split` aborts if `t ≥ k`. This never happens, and it keeps the proof free of a
  table-length argument, as con-ron's `fail` on an out-of-range `pows[t]` does.
* Complexity: `O(M(n) log n)`, where `M` is the cost of `nat_mul`. With the schoolbook
  `nat_mul` this is still `O(n²)`, and it is **twice as slow as the chunk loop** (10^6 digits:
  52.1 G → 109 G instructions). With lane bigmul's Karatsuba it is `O(n^1.58 log n)`. So this
  lane lands only after bigmul.

## The models and their proofs

* `nat_mul` and `nat_add` are the arena's functions, used only through their public specs
  (`mul_callW`, `add_callW` in `NatDecBigVal.lean`, which instantiate `natMul_spec` and
  `natAdd_spec` in `natDecProg`). When bigmul changes `nat_mul`'s code, only the lookup
  arguments of these two wrappers change.
* The front end's model `natDecW` stays an exact function of `(b, m, c, d)` with the same
  signature, as the generated `litW` requires. Its long branch is
  `callF natDecProg "nat_dec_big" m [c, d]` (`Arena/CallF.lean`): the run in `natDecProg`, at
  any fuel. Every program that binds `natDecProg`'s functions alike makes the same run
  (`callF_spec`, with `natDec_closed`: `closedA natDecProg [POOL, tier1 POOL] [0]` by
  `decide +kernel`).
* The long branch also checks `m.arr8 IN = b`, the spec's precondition. So `natDecW_val` keeps
  its statement, which has no hypothesis about the input.
* `natDecW` is evaluated (`#eval`, `#guard`) through `natDecWEval`, which is `callW` at fuel
  `2^64` (`implemented_by`; no proof sees it). Without it the generated `litW` and `nodeW`
  above it would have to be `noncomputable`.
* `natDec_specW` gains one hypothesis, `∀ g ∈ natDecFns, p.lookup g = natDecProg.lookup g`.
  `ExprLookups` gains the field `dec_agree`, and `exprProg` now contains `natDecProg`. The
  coordinator approved this.
* `l_model` generates `splitW` and `bigW` over `callW` of every callee (`NatDecBig.lean`). The
  value proofs (`NatDecBigVal.lean`) are by induction on the fuel:
  * `split_val`: the recursion. The digits split by `decN_append`, and the table's entry `t`
    has the value `10^dd`.
  * `copy_down`: the copy to the old top, with `vpool_copy64` (an ascending copy down inside one
    tier) and `Grows.reset`.
  * `TblOK`: the table invariant, preserved by growth (`TblOK.grows`) and by one new entry
    (`TblOK.push`). `big_init` covers the first entry and `loop2_val` the squaring loop.
  * `big_val` and `natDecW_val`. `natDecW_dk` uses the text's write set (`natDecBig_frame`),
    and `natDecW_top` uses `bigW_top`.

## Correctness checks (prototype)

The test file (`/home/joachim/.claude/jobs/e879b30f/tmp/bigdec-bench/T2.lean`, not committed)
makes copies of the three functions with base 40, so that a 2 000-digit literal splits over
several levels. It checks 499 literals against `String.toNat!`: the value, a non-zero top limb,
the result at the old top, the new top, and the pool below the old top unchanged. The literals:
random ones of 1‥400 digits, runs of `9`, `10^k`, leading zeros, all zeros, `2^64 - 1`, `2^64`,
`2^128 - 1`. All passed. The proofs now cover the same ground.

## Measurements

Fixtures: `scripts/biglit_fixtures.py OUTDIR --lean4export <con-ron's _tmp/lean4export binary>
--digits 10000 100000 1000000 --resize 3000 5000 7000 10000 15000 20000 30000 50000 100000
200000`. Each fixture is `def bigLit : Nat := N` plus `theorem bigLit_eq : bigLit = N := rfl`,
one `natVal` record. con-ron and the checker accept all of them. They are benchmark inputs
only, not fixtures of the repository.

Binaries were built from `checker.s` with `decBase` patched in the assembly (`cmpq $4864`),
on top of a scratch merge of bigmul's prototype `32bd0c99` (Karatsuba, threshold 48 limbs).

**`decBase` sweep** (`instructions:u` minus the fixed cost of 122.64 M, in thousands):

| digits | chunks only | 2432 | 4864 | **7296** | 9728 | 14592 |
|---:|---:|---:|---:|---:|---:|---:|
| 3 000 | 555 | 719 | 555 | 555 | 555 | 555 |
| 5 000 | 1 460 | 1 815 | 1 760 | 1 460 | 1 460 | 1 460 |
| 7 000 | 2 731 | 3 370 | 3 110 | 2 731 | 2 731 | 2 731 |
| 10 000 | 5 472 | 6 048 | 5 957 | 5 911 | 5 911 | 5 472 |
| 15 000 | 12 109 | 11 798 | 11 664 | 11 610 | 11 610 | 12 062 |
| 20 000 | 21 339 | 19 746 | 19 574 | 19 508 | 19 970 | 20 417 |
| 30 000 | 47 510 | 37 941 | 37 700 | 37 639 | 38 564 | 38 998 |
| 50 000 | 131 187 | 92 853 | 92 471 | 92 380 | 94 231 | 94 637 |
| 100 000 | 521 947 | 289 821 | 289 216 | 289 167 | 293 352 | 293 818 |
| 200 000 | 2 081 904 | 892 134 | 890 919 | 890 834 | 899 637 | 900 085 |

`decBase = 7296` (384 chunks) is the best or tied in every row from 15 000 digits on. con-ron
chose 4 864 (256 chunks), but on L 4 864 is never better than 7 296.

**Known small regression region:** between about 7 300 and 12 000 digits every split is a
little worse than the chunk loop. At 10 000 digits the read costs 8 % more than the chunk loop
(+0.44 M instructions). A higher base would avoid this, but costs about 4 % from 15 000 digits
on.

**End to end** (`scripts/bench.py --no-build --no-ref --reps 7 --cpus 90-91`, interleaved and
randomized). Paired wall ratios are given with a t-based 95 % interval and an exact Wilcoxon
signed-rank test (`paired.py` next to the fixtures). "bigmul" is the scratch merge with the
split disabled; "bigdec" is the scratch merge with `decBase = 7296`.

| fixture | master | bigmul | bigdec | wall bigdec/bigmul | 95 % CI | p | con-ron |
|---|---:|---:|---:|---:|---:|---:|---:|
| 10^4 digits | 126.5 M | 126.5 M | 126.9 M | 1.002 | 0.98–1.02 | 1.0 | 198 M |
| 3·10^4 | 168.5 M | 168.5 M | 158.6 M | 0.968 | 0.94–1.02 | 0.30 | 210 M |
| 10^5 | 643 M | 643 M | 410 M | 0.790 | 0.78–0.79 | 0.016 | 304 M |
| 2·10^5 | 2 203 M | 2 203 M | 1 012 M | 0.567 | 0.55–0.58 | 0.016 | 524 M |
| 10^6 | 52 054 M (1.64 s) | 52 054 M | 10 931 M (0.356 s) | 0.218 | 0.217–0.218 | 0.016 | 4 388 M (0.218 s) |

At 10^6 digits, `perf record` puts 81 % of the time in bigmul's `mul_row`, 7 % in `sub_row`,
5 % in `kara_mid` and 2.6 % in the chunk loop. The remaining gap to con-ron (2.5× in
instructions) is the multiplier's constant.

**Init** (`--set init`, 5 rounds): `init435` costs 202 882.8 M instructions with bigdec and with
bigmul, against 202 881.1 M on master (+0.001 %). The paired wall ratio is 1.015 against bigmul
(CI 0.985–1.030, p = 0.63) and 1.001 against master (p = 0.31). There is no regression.

**On the landed tree** (master `3867a4bab` with bigmul, merged; the same method, master against
the branch):

| fixture | master | bigdec | wall bigdec/master | 95 % CI | p |
|---|---:|---:|---:|---:|---:|
| 10^4 digits | 126.5 M | 126.9 M | 0.979 | 0.970–1.003 | 0.11 |
| 3·10^4 | 168.5 M | 158.7 M | 1.007 | 0.985–1.021 | 0.38 |
| 10^5 | 642.9 M | 410.7 M | 0.806 | 0.790–0.826 | 0.016 |
| 2·10^5 | 2 202.9 M | 1 013.9 M | 0.562 | 0.534–0.633 | 0.016 |
| 10^6 | 52 054 M (1.635 s) | 11 763 M (0.375 s) | 0.229 | 0.228–0.230 | 0.016 |

Init (5 rounds): `init435` costs 202 882.8 M instructions on both, and the wall ratio is 0.93
(p = 0.13). `init-prelude` is unchanged. `diff-e2e --refs`: 740 agree, REFDIFF 0.

## What went wrong

* `bench.py` without `--no-build` builds the worktree it runs in, here halfway through an
  edit. Lake's cache guard caught it ("source files changed WHILE Lake was building").
* bigmul's branch tip had a failing WIP proof, so the scratch merge used its prototype commit
  `32bd0c99` instead.
