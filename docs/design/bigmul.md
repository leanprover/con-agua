# Lane bigmul: Karatsuba for `nat_mul`

Lane of 2026-11-18 (Opus), from master `d44857b7a`. Goal (user): the bignum algorithms are no
worse than con-ron's (`de06320f`, task #158), algorithmically. This lane: `nat_mul`.

## Before

`nat_mul(oa, la, ob, lb)` (`Arena/NatMul.lean`): schoolbook, zero `la` limbs at the top, then one
multiply-accumulate row of `a * b[j]` per limb of `b` (`zeroLoop`/`colLoop`/`rowLoop`, the
high word by `mac_hi`), then `nat_trim`. `O(la · lb)` limb products, always; the inner loop runs
over `a` whatever the lengths (gf3's `13 × 9519` products ran 9519 rows of 13 limbs).

## The algorithm (con-ron's `mul_win`, `ron/nat.rs:523-675`)

`mul_win(oa, la, ob, lb, o, n, s)`: `P[o, o + n) += a · b` in place, for the windows
`a = P[oa, oa + la)` and `b = P[ob, ob + lb)`, scratch from `s` up:

* `la < lb`: swap (the longer window is the inner loop);
* `lb < T`: schoolbook rows, one `mul_row(o + j, n - j, oa, la, b[j])` per limb of `b`;
* `2 lb ≤ la`: halve `a`, both halves accumulate into the window (`O(la / lb)` balanced
  products, no combination pass);
* otherwise Karatsuba at `k = ceil(la / 2)`: scratch `[z0 | z2 | sa | sb | sp]` zeroed by one
  `mul_zeros`, `z0 = a0 b0`, `z2 = a1 b1`, `sa = a0 + a1`, `sb = b0 + b1` (two `mul_row`s with
  `y = 1` each), `sp = sa · sb`, `sp -= z0`, `sp -= z2` (`sub_row`), `l = nat_trim(sp)`, then
  `P[o..] += z0`, `P[o + k..] += sp[0, l)`, `P[o + 2k..] += z2`.

The in-place passes (`mul_row`, `sub_row`) abort when a carry or borrow would leave their
window, and `mul_win` aborts unless `n ≥ la + lb`: the sums always fit, so these aborts never
fire, and the proof (partial correctness, every abort is `⊤`) needs no bound on any sum. The
top call: `nat_mul` zeroes `la + lb` limbs at the top, `mul_win(…, top, la + lb, top + la + lb)`,
`nat_trim`.

Complexity: `O(n^1.585)` for balanced `n × n`; `O(la · lb^0.585)` for `la ≥ lb`.

Differences from con-ron, deliberate: no operand copies at all (con-ron's are none either, its
windows are slices of `Vec`s); all temporaries live in one zeroed scratch block above the result
(the stack discipline of the recursion: every call's scratch is above its caller's). The inner
loop has the multiply-accumulate inline (it was the `mac_hi` call, which the compiler inlined
with four argument copies) and loads the operand through its decoded tier and index.

## Measurements

Method. Microbenchmark: Lean files of theorems `Nat.land (Nat.mul (Nat.pow 3 k) (Nat.pow 5 k')) 255
= r := by decide +kernel` (`k`, `k'` chosen for the limb counts; `R` theorems with distinct
exponents per file), exported with lean4export (v4.35.0-rc3), and the same with `Nat.add` in
place of `Nat.mul` (the pows alone); `perf stat -e instructions:u` of the checker on each
(nearly deterministic). Per product: `(mul − base) / R`. Generator: `_tmp/bigmul-bench/mb/`
(`gen.py`, `mk.sh`, `instr.sh`). End to end: `scripts/bench.py --no-conron --no-ref --reps 6`
(interleaved, randomized), paired differences with a t interval and the exact Wilcoxon
signed-rank test (`_tmp/bigmul-bench/tools/paired.py`).

Per product, `instructions:u` (master → this lane, T = 48):

| operands | master | new | |
|---|---:|---:|---:|
| 256 × 256 | 5.75 M | 2.33 M | 2.5× |
| 512 × 512 | 21.4 M | 6.00 M | 3.6× |
| 1024 × 1024 | 85.9 M | 18.8 M | 4.6× |
| 2048 × 2048 | 344 M | 57.6 M | 6.0× |
| 4096 × 4096 | 1 376 M | 174 M | 7.9× |
| 8192 × 8192 | 5 503 M | 527 M | 10.4× |
| 13 × 9519 (gf3's shape) | 9.93 M | 5.72 M | 1.7× |
| 64 × 4096 | 21.3 M | 11.8 M | 1.8× |
| 100 × 1000 | 9.07 M | 5.11 M | 1.8× |

Doubling `n` costs ×3.0 (master ×4.0): `n^1.585`. Every fixture from 8 × 8 to 96 × 96 limbs
is also below master in total (the fixed cost dominates there).

Threshold: `checker.s` patched at `mul_win`'s comparison, `T ∈ {8, 12, 16, 24, 32, 48, 64, 96}`,
balanced 16–8192 limbs and the unbalanced fixtures (fixture totals, M instructions):

| fixture | 16 | 32 | 48 | 64 | 96 |
|---|---:|---:|---:|---:|---:|
| 112² | — | 1 492.8 | 1 492.8 | 1 497.0 | 1 497.0 |
| 192² | — | 1 457.5 | 1 457.5 | 1 459.6 | 1 459.6 |
| 1024² | 1 521 | 1 496 | 1 490 | 1 490 | 1 499 |
| 8192² | 2 707 | 2 479 | 2 426 | 2 426 | 2 507 |
| 13 × 9519 | 3 416 | 3 120 | 3 083 | 3 083 | 3 251 |

48 is never worse than 32 or 64. (con-ron's 64 is for its own code; L's is measured.)

End to end (6 interleaved rounds, master `d44857b7a` vs this lane at T = 48):

| fixture | master | new | paired difference (95 % CI) | Wilcoxon p |
|---|---:|---:|---:|---:|
| gf3, instructions | 146.72 G | 99.67 G | −32.1 % (±0.00 %) | 0.031 (min. for n = 6) |
| gf3, wall | 6.94 s | 3.85 s | −44.7 % (±0.8 %) | 0.031 |
| Init, instructions | 202.881 G | 202.883 G | +0.001 % | 0.031 |
| Init, wall | 14.86 s | 14.77 s | +0.7 % (±3.3 %) | 0.84 |

gf3's products are `13 × 9519`, below the threshold: its gain is the swap (master ran 9519
rows of 13 limbs) and the inline multiply-accumulate. After the change `mul_row` is 57 % of gf3.

**Follow-up (out of scope, the compiler):** `mul_row`'s inner loop costs about 52 instructions
per limb product (master's was about 95); con-ron's is about 16. Every local lives on the
stack in the generated code; that is the codegen gap, not the algorithm.

## Proof

(below)
