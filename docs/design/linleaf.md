# Lane `linleaf`: the bignum's linear passes as leaves (journal)

Branch `linleaf`, worktree `_tmp/wt/linleaf`. Task: make the linear passes of the bignum (`nat_add`,
`nat_sub`, `land`/`lor`/`xor`, the shifts, the literal hash) fast with the existing compiler, and
(scope added by the user mid-lane) split them into leaf functions that the asm escape (lane
asmesc2) can replace by hand-written bodies.

## 1. Why the passes were slow

The leaf back end (lane leafgen) keeps up to 9 locals of a call-free function in registers. Every
linear pass called `nat_trim`, whose loop returned from inside (`return n` in a `while`), so the
inliner (`Compiler/Inline.lean`, S = 80, one round) could not inline it: the passes stayed
non-leaves and every local lived on the stack (about 80 instructions per limb in `nat_add`, with
`nat_limb` and `add_carry` inlined but their arguments copied through the frame). `lit_hash`, a
leaf, was inlined into its caller `intern_lit` (a non-leaf), so its loop ran on the stack too.

## 2. Phase 1: an unproved prototype (numbers)

Emitter: a copy of `AsmEmit.lean` that patches `checkerProg` with new bodies before inlining and
compiling (scratch, not committed). Exact `instructions:u`, gf3 (`con-ron/_tmp/gf3/gf3.ndjson`)
and `Init` (`init435.ndjson`), master `9e83e46da`:

| change | gf3 | Δ gf3 |
|---|---:|---:|
| master | 97.957 G | |
| `nat_trim` inlinable (no `return` in its loop): every pass call-free | 91.919 G | −6.04 G |
| then `nat_add` with tiers resolved once, two passes | 90.036 G | −1.88 G |
| then `nat_sub` the same | 91.023 G | −0.90 G |
| then `land` | 91.320 G | −0.60 G |
| then `lor` (common limbs, then a copy) | 90.134 G | −1.79 G |
| then `xor` | 90.578 G | −1.34 G |
| then `shr` | 91.344 G | −0.57 G |
| then `shl` | 91.918 G | −0.0005 G (gf3 barely shifts left) |
| `lit_hash` alone: a function of its own, 4 limbs per round | 94.503 G | −3.45 G |
| all but `shl` | 81.387 G | −16.92 % |

`Init`: 202.647 G → 202.626 G (−0.01 %). Wall (`bench.py`, 12 interleaved randomized rounds,
paired, exact Wilcoxon): gf3 3.783 s → 2.949 s, −22.0 % [−22.1, −22.0], p = 0.0005; `Init`
14.82 s → 14.78 s, −0.24 % [−0.72, +0.24], p = 0.3 (no change).

Verdicts: `diff-e2e.py` 740 agree; a new fuzzer (`Nat.add/sub/land/lor/xor/shiftLeft/shiftRight`
on random and carry-heavy operands of 0 to 1000 limbs, 3315 fixtures, true and corrupted results,
natVal substitution into exported templates): no mismatch, master and prototype alike.

What a limb still costs with the compiler (from the asm): each tiered access is about 7
instructions (`and $1` of the tier, the bound `cmp`/`jae`, the base load, the access), a carry by
`u64(x < c)` 5 (`cmov` sequence), plus the loop's test, increment and fuel count (5). `nat_add`'s
common-limb pass is about 38 instructions per limb with one spilled local, the tail about 26,
`lor` about 25, `lit_hash` about 10.5. A hand-written body needs about 4–8.

## 3. The leaves (landed first: `nat_add`, `nat_sub`)

`ConAgua/Arena/NatLeaf.lean`. Each leaf: one loop, plain arguments (tagged pool addresses, a length,
a carry or borrow in), one word out, no call. The output window `[o, o + n)` lies above the
operands.

| leaf | does | returns |
|---|---|---|
| `add_n(o, oa, ob, n, c)` | `P[o+i] := A[oa+i] + B[ob+i] + carry`, `i < n` | the carry |
| `add_1(o, oa, n, c)` | `P[o+i] := A[oa+i] + carry` | the carry |
| `sub_n(o, oa, ob, n, c)` | `P[o+i] := A[oa+i] - B[ob+i] - borrow` | the borrow |
| `sub_1(o, oa, n, c)` | `P[o+i] := A[oa+i] - borrow` | the borrow |

Their specs follow `mul_row`'s window style (`Off`, `pv`); the window lemmas (`w_add`, `win_lt`,
`ld_win`, `st_win`, `sbb_inl`, `split_clear_locs`) moved here from `NatMul.lean`. `nat_add` calls
`add_n` over the shorter operand's limbs and `add_1` over the rest of the longer one (two `if`
arms instead of swapping the operands: a swap of four locals made `simp_all` time out on the
`setLoc` chains), stores the carry limb and trims. `nat_sub` trims `b` first when it is longer
than `a` (the inputs need not be normalised; still longer means `a < b`), then its core block
`subCore` runs `sub_n` and `sub_1`; a borrow out means `a < b` and the result `0`. `subCore` has
its own lemma (`subCore_spec`): proved inside the function's spec, the trim/borrow paths took
`simp_all` 3.5 min at 8M heartbeats; split, NatSub elaborates in 9 s with no heartbeat override.
The leaves allow the output window to be the first operand's (`o = oa`, in place): each limb is
read before it is written, and the specs' disjointness is `oa + n ≤ o ∨ o ≤ oa`. `nat_trim` loops `while 0 < n &&
POOL⦃o + n - 1⦄ == 0`, so the inliner inlines it, and the inlined `nat_add`/`nat_sub` are
call-free.

The callers' proofs compose the leaf specs through lemmas in the shape of the goals
(`add_goal`, `add_agree_goal`, `add_grows`, `room_le`; `sub_goal_ok`, `sub_goal_bor`,
`sub_goal_short`, `sub_agree_goal`, `sub_grows`), applied with `with_reducible apply` and the
metavariables fixed by `case h2/h1/e1/e2 => with_reducible assumption` first.

Proof cost (elaboration, `lake env lean`): NatLeaf 8 s, NatAdd 60 s, NatSub 9 s.

### Measurements of the landing (master `acf6a18d5`, with `mul_row`/`sub_row` in hand asm)

Exact `instructions:u`: gf3 53.582 G → 44.675 G (−16.6 %); Init 202.647 G → 202.649 G
(+0.001 %). Per function on gf3 (perf sampling): `nat_add` 7.02 → 3.13 G, `nat_sub` 3.07 → 1.35 G;
the inlinable `nat_trim` also makes `lor` (5.87 → 4.49 G), `xor` (4.31 → 3.39 G), `shr`
(3.14 → 2.48 G) and `land` (2.02 → 1.48 G) call-free. Verdicts: `diff-e2e.py --refs` 740 agree,
REFDIFF 0; the bignum fuzzer 3315/3315.

Candidates for hand asm (compiled cost per limb, from `checker.s`): `add_n` ≈ 38, `add_1` ≈ 26,
`sub_n` ≈ 36, `sub_1` ≈ 24; a hand-written body needs about 4–8.

## 4. `div_add` through the leaves; no heartbeat overrides

`div_add(r, n, ob, lb)` (`NatDivSubmul.lean`, `nat_divmod`'s add-back) is now `add_n(r, r, ob, m, 0)`
then `add_1(r + m, r + m, n - m, c)` with `m = min lb n`: in place, the output window the first
operand's. The leaves' specs already allowed it (`oa + k ≤ o ∨ o ≤ oa`). `add_carry` lost its last
caller and is gone (with `adcHi`). `nat_add`'s spec got the same split as `nat_sub`'s (its core
`addCore` with its own lemma): NatAdd 60 s → 7 s, and neither NatAdd nor NatLeaf needs a
`maxHeartbeats` override any more. Verdicts: diff-e2e 740 agree; bignum fuzzer 3315/3315; a
`Nat.div`/`Nat.mod` fuzzer (2000 fixtures, random and edge-pattern limbs, 1–17-limb divisors): no
mismatch. gf3 unchanged (44.669 G both; gf3 barely divides).

## 5. The bitwise leaves

`and_n`, `or_n`, `xor_n` (`o, oa, ob, n`) are one generic leaf `bitNG op` (its loop `bitNLoop op` is
built from `Stmt` with the operator as a Lean argument; L has no operator parameter); `copy_n(o, oa,
n)` copies. Their specs: `pv` of the output window is `bwv (BinOp.eval op)` (the limb-wise combine
of the two windows) or the source window's `pv`. `nat_land` calls `and_n` over the shorter length
(`andCore`); `nat_lor`/`nat_xor` are one generic `natBitG g`: `bitCore g` calls `g` over the shorter
length and `copy_n` over the rest of the longer operand; `bv_tail_a`/`bv_tail_b` turn that into
`bv` (the zero-extended combine the public specs use) since `x | 0 = x ^ 0 = x`. Public specs
unchanged. NatBits elaborates in 8 s (it was about 60 s with the old loops), NatLeaf in 9 s, no
heartbeat overrides.

Measured on master `a98d69362e` (add/sub already in hand asm): gf3 40.932 G → 37.365 G
(−8.7 %, exact `instructions:u`). Verdicts: diff-e2e 740 agree; bignum fuzzer 3315/3315.
Compiled per-limb cost (asm, inlined into `nat_lor`): `or_n`'s loop 32 instructions per limb (two
tiered loads and a store at ≈ 7 each, spilled locals, the loop's 5), `copy_n`'s 22: candidates for
hand asm.

## 6. The shift leaves

`shl_n(o, oa, n, s, c)` (`P[o+i] := (A[i] << s) | c`, carry `(A[i] >> 1) >> (63 - s)`, `63 - s`
computed once), `shr_n(o, oa, n, s)` (`P[o+i] := (A[i] >> s) | ((A[i+1] << 1) << (63 - s))`, reads
`n + 1` limbs), `zero_n(o, n)`. `nat_shl` is `zero_n` over the skipped limbs, `shl_n`, the carry on
top (`shlCore`); `nat_shr` is `shr_n` over all but the last limb of the shifted slice and the last
limb shifted alone (`shrCore`). The right shift's word facts (`lowb`, `shr_split`) moved to
NatLeaf. Each function's spec composes its core block's lemma and a final lemma (`shl_final`,
`shr_final`, the latter through the existing `shr_small`). NatShl 23 s and NatShr 16 s, each
with a commented 1M heartbeat budget (before: 8M and unlimited); NatLeaf 9 s.
