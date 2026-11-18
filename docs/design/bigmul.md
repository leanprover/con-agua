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

(below)

## Proof

(below)
