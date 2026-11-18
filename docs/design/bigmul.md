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

## The L code, as landed

`mul_win` dispatches; the Karatsuba node is split over three functions so that each proof
stays small: `kara_prods` (zero and fill `z0`, `z2`; 4 calls), `kara_sum` (a zeroed `k + 1`
limb sum of the two halves; 3 calls), `kara_mid` (the layout, an abort unless the scratch high
water mark stays below `2^41`, `kara_prods`, two `kara_sum`s, the product of the sums, two
`sub_row`s, `nat_trim`; 8 calls). `mul_win`'s Karatsuba branch is then `kara_mid` and three
`mul_row`s with `y = 1`. `nat_mul` aborts up front unless the top's tier array has `la + lb`
free words (schoolbook) or `9 (la + lb) + 1024` (both operands at the threshold or above): the
scratch of a Karatsuba node of `la` limbs is `la + lb + 4k + 4 ≤ 4 la + 6`, its largest child has
`k + 1 ≤ la / 2 + 2` limbs, so the whole stack is below `8 la + 18 · depth`. (Any store past the
tier array is an `oob` abort anyway; the check only fails early.)

`mac_hi` is gone (its one caller was `nat_mul`'s old column loop; `macHiN`/`mac_split` with it).

## Proof

`ConAgua/Arena/NatMul.lean`, 379 → 1 364 lines (`NatOff.lean` 100 lines); no `sorry`, no axiom. New shared file
`ConAgua/Arena/NatOff.lean`: `Off` (moved unchanged from `NatDiv.lean`, which imports it) and the
new `OffB` (agree below `s` off a window: `mul_win`'s frame), `Off.pv_disj`, `OffB.pv_disj`,
`Off.mono`, `Agree.trans` (moved from `NatPow.lean`). New `grind` attribute `winop_grind`
(`NatGrindAttr.lean`) for the two `pv_disj` patterns, kept out of `arena_grind`.

* The passes (`mul_row`'s two loops, `sub_row`'s two, `mul_zeros`'s) follow `NatDiv`'s passes:
  an `Off` frame against the entry pool, the value equation additive (the subtrahend on the
  left), and the loop step closed by a lemma in the goal's shape (`mrow_step_goal`,
  `carry_step_goal`, `srow_step_goal`, `borrow_step_goal`, `zeros_step_goal`; the word facts
  `mac_inl`, `sbb_inl` by case split and `omega`). Exit of a ripple: `off_split` (the changed
  prefix and the whole window) as a `grind` lemma. `mulRow_at_spec` lifts `mul_row` on
  `[o + k, o + w)` to the whole window (its arguments stated as `BinOp.add.eval o k`, the form
  `vcgen` sees, so that it matches calls with computed offsets).
* `mul_win`, `kara_prods`, `kara_mid`: one `Prop` spec each at fuel `n` (`MulWinSpec`, …), the
  three steps from the specs at `n` (`mulWin_step`, `karaProds_step`, `karaMid_step`), and
  `mulWin_spec` the induction (as `bbGo_spec`). `rowsLoop` (schoolbook) has its own invariant.
* The function-level recipe that worked: plain `vcgen` with the callee specs and the IHs, then
  `clear` the IHs (a `∀`-triple in context sent `grind` into case splits over the argument
  lists), `simp only [LocEq]`, `simp_all only [St.setLoc_loc, Locals.init_cons_*, …]` (this
  names every intermediate state's locals by the caller's arguments), then `split_clear_locs`
  (a small tactic in `NatMul.lean`: `casesAnd`, then clear the `s.loc = Locals.init […]`
  equations — with them in context `grind` cases on the lists), `and_intros`, and per goal
  `omega`, an `apply` of a frame or value lemma in the goal's shape followed by
  `with_reducible assumption` for its premises (`kp_frame`, `kmid_frame`, `halve_frame`,
  `halve_val`, `kara_frame`, `kara_val`, `nm_agree`), or `grind [arena_grind, lang_grind,
  winop_grind]`. The positions of a Karatsuba node are one lemma (`kara_pos`: no word sum wraps
  below `2^41`), proved step by step with `toNat_add_of_lt` (a version by `simp` and `omega` over
  the `% 2^64` forms ran for minutes).
* Karatsuba's identity is the `grind` at the end of `kara_val`, after `pv_append` for both
  operands and `wt (2K) = wt K · wt K`.
* `natMul_spec`'s statement is unchanged. Its program hypothesis `hph` is now `MulFns p`, the
  seven callee lookups as ONE tuple equation, so that every caller (`NatPow`, `NatPowNat`,
  `NatArms`, `CoreNatOp`) still passes `rfl` in the same position.

What went wrong on the way: `simp only [...]` lists naming a lemma of a module not imported
(`L.St.setLoc_mem` lives in `L/LocNF.lean`, `Mem.size64_set64` in `L/Records.lean`) fail as a
whole inside `try`, silently; `repeat (obtain ⟨_, _⟩ := ‹_ ∧ _›)` never terminates (the
anonymous hypothesis is not cleared); a step lemma with a variable that is not in its conclusion
leaves a metavariable after `apply` (state such premises over the conclusion's variables only,
or close them by `with_reducible assumption`); `pkill -f <pattern>` killed the calling shell.

## Landing measurements (the final binary)

The landed `checker.s` (`karaT = 48`), same method: per product 2.34 M / 18.8 M / 175 M / 528 M
instructions at 256² / 1024² / 4096² / 8192² (master 5.75 M / 85.9 M / 1 376 M / 5 503 M), 1.7-1.8×
on the unbalanced shapes; gf3 99.67 G instructions (−32.1 %), Init +1.7 M (+0.001 %). Wall time of
this second run (6 rounds, a build running on the machine): gf3 −39.6 % (±5.6 %, Wilcoxon p =
0.031), Init −3.8 % (±10.6 %, p = 0.44, no change). The first run (quiet machine) is the table
above. `scripts/diff-e2e.py --refs --parallel 16`: 740 agree, 0 unsound, 0 REFDIFF.
