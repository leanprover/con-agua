# Lane bigdec: subquadratic decimal literals (`nat_dec`)

Goal (2026-11-18): `nat_dec` should be no worse than con-ron's `frontend/nat_decimal.rs`
(task #159, de06320f) in its algorithm.

## Before

`nat_dec(c, d)` read the digits nineteen at a time. Each chunk was folded into all the limbs
read so far by one `nat_mad` pass, so `n` digits cost `O(n² / 19)` word operations.

## Design

* `nat_dec(c, d)` now only dispatches. A literal of at most `decBase` digits goes to
  `nat_dec_chunks`, the old chunk loop unchanged. A longer one goes to `nat_dec_big`.
* `nat_dec_big(c, d)` first reserves `2k` words at the pool top for an index: `(address,
  length)` for each power `P[t] = 10^(19 · 2^t)`, `t < k`, where `k - 1` is the largest `t` with
  `4 · 19 · 2^t ≤ d - c` (con-ron's `power_table`). It writes `P[0] = 10^19` as one limb and
  builds each next power by `nat_mul(P[t], P[t])`, which appends at the top. Then it calls
  `nat_dec_split(c, d, tbl, k)` and copies the result down to the old top.
* `nat_dec_split(c, d, tbl, k)` reads at most `decBase` digits with `nat_dec_chunks`. For a
  longer run it takes `dd = 19 · 2^t`, the largest with `4 dd ≤ len`, as con-ron's `split_level`
  does. The high part `[c, d - dd)` is the longer one. The function recurses on both parts and
  computes `nat_add(nat_mul(hi, P[t]), lo)`. It aborts if `t ≥ k`, which never happens and keeps
  the proof free of a table-length argument, as con-ron's `fail` does. It copies the sum down to
  the top it started from (`copy!`), so the scratch stays `O(n)`.
* `nat_mul` and `nat_add` are the arena's functions, used through their public specs. The
  front end's model `natDecW` stays an exact function of the memory. Its long branch is
  `callF natDecProg "nat_dec_big"` (`Arena/CallF.lean`), so it does not depend on `nat_mul`'s
  code: lane bigmul's Karatsuba can replace that code without touching these proofs.
  `natDecW` is evaluated (`#eval`, `#guard`) through `natDecWEval`, which is `callW` at fuel
  `2^64` (`implemented_by`; no proof sees it).
* Complexity: `O(M(n) log n)` with `M` the cost of `nat_mul`. With the schoolbook `nat_mul`
  this is still `O(n²)` but with a smaller constant. With Karatsuba (lane bigmul) it is
  `O(n^1.58)`.

## Correctness checks (prototype)

`_tmp/bigdec/T2.lean` makes copies of the three functions with base 40, so that a
2 000-digit literal splits over several levels. It checks 499 literals against `String.toNat!`:
the value, the top limb non-zero, the result at the old top, the new top, and the pool below
the old top untouched. The literals: random ones of 1‥400 digits, runs of `9`, `10^k`, leading
zeros, all zeros, `2^64 - 1`, `2^64`, `2^128 - 1`. All passed.

## Measurements

(below)
