# Lane mkmax: the `mk_*` writers take `max` by a branch

Follow-up from derbv.md §5. The `mk_*` writers in `Arena/ExprMk.lean` built the packed range word
with `max` in the `u64` product form, `x + (y - x) * u64(x < y)`: two per store in `mk_app`,
`mk_lam` and `mk_forall` (bvar range, fvar range), four in `mk_let`. derbv/derbr found the branch
form cheaper in `der_b`/`der_bv`. No other writer of a derived word computes a `max`: `mk_proj`
copies one range.

## 1. The change

Each `max` is now a statement, `if x < y { x := y }`, and the store packs the locals,
`x + xf * 32768 + (xl | yl) * 1073741824`. The surrounding code is unchanged (`satPredW` stays the
`u64` form: it is a single expression that `satPredW_L` already names). No twin deviation (con-ron
has no derived word), no function-list changes (same callees).

## 2. Proof

One helper, `step_maxIf_spec`, a Hoare-triple spec for the statement over any post:
`⦃fun s => Q .normal (s.setLoc x (maxW (s.loc x) (s.loc y)))⦄ step p k (if x < y { x := y }) ⦃Q; E⦄`.
The four writer specs add `step_maxIf_spec p` to their `vcgen` list and drop `maxW_L` (now unused,
removed, also from `mkProj_spec`'s list, where it was dead); nothing else in them changes.

Why a triple and not an equation: an equation `step p k (if …) = step p k (x := <product form>)`
in the `vcgen` list (or as `@[spec]` at any priority) is never applied. `vcgen` gives the simp-style
arguments one priority, `unfoldSpecPrio`, so `step`'s own `.ite` equation (`step.eq_6`) wins and the
proof splits at every comparison (`finish` then fails on 4 or 16 goals). An explicit triple spec gets
`explicitSpecPrio`, above every equation, so `vcgen` applies it at the `if` and the post already
states `maxW`: no split, no extra goals. The spec's own proof is `vcgen` and two `grind`s.
ExprMk.lean elaborates in 8 s (as before).

## 3. Numbers

`Init` (`_tmp/fixtures/init/init435.ndjson`, accept), exact instructions (`perf stat -e
instructions:u`), master 44eca3af against this lane, interleaved; two runs at `--jobs=4` agree to
0.01 %:

| | master | mkmax | Δ |
|---|---:|---:|---:|
| `--jobs=4` | 217.08 G | 215.13 G | **−0.90 %** |
| one thread | 215.95 G | 214.00 G | −0.90 % |

`checker.s` shrinks by 58 lines (the four writers lose the multiply sequences).

Verdicts: `diff-e2e --refs --parallel 16`: 634 of 634 agree (406 accepted, 228 not), 0 UNSOUND /
INCOMPLETE / REFDIFF / CRASH / TIMEOUT.

## 4. Elsewhere

The same product form remains in the walks' `max` (`Arena/Walk.lean`, `Arena/FVarRange.lean`,
`Arena/IndPos.lean`). Those return or assign it inside proved `l_model` functions; whether
`step_maxIf_spec` drops in there as easily is untested.

## 5. Follow-up (lane walkmax): the walks and the probe wrap, not done

Measured against master 8f29d88d, `Init` as in §3, `--jobs=4`, exact instructions, two interleaved
runs each. The bar was −0.2 %; neither change reaches it, so neither landed.

**The walks' `max`** (`bb_node`, `depth_node`; `fr_node` would be the same shape). Prototyped and
proved: `step_maxIf_spec` moved to `ViewL.lean` (next to `maxW`), `bb_node` and `depth_node` take
each `max` by `if x < y { x := y }` (`depth_node` loses its local `m`), and their step proofs add
`step_maxIf_spec p` to the `vcgen` list and drop `maxW` from `finish` (two lines each; the
hand-written models `bbNodeW`, `dpNodeW` and their refinements unchanged). Result: 215.15/215.14 G
on master, 215.14/215.12 G on the branch, **−0.007 %**. The walks are cold: `perf record` on the
same run attributes no sample to `bb_node`, `bb_go`, `fr_node`, `fr_go` or `depth_node` (all
below 0.01 %; `mk_app` alone is 2.1 %). `fr_node` was not finished: its model is generated
(`l_model frGo_spec`), and the generator turns each `if x < y { x := y }` into a join point
(a branching model), which the kernel rejects with "deep recursion" at the `l_model`. Taking it
would need `l_model` to read that statement as `x := maxW x y` (and use `step_maxIf_spec` in the
steps), a generator change not worth a cold function.

**The probe wrap** `j := (j + 1) * u64(j + 1 < n)` (`ConsLib`'s `cfAdv`, `kprobeL`; `MemoLib`'s
two probe loops) is the hot select left: it runs at every probe step of every `*_find`/`*_put`
(`app_find` is 16.8 % of `Init`), 8 instructions (two `lea`, `cmp`, two `mov`, `cmov`, `imul`,
`mov`). Not proved, estimated by patching `checker.s` by hand: all 185 copies of that sequence
replaced by what the compiler emits for `j := j + 1; if n <= j { j := 0 }` (`lea`, `mov`, `cmp`,
`jb`, then the rarely taken `mov $0`), verdict output identical. Result: 215.14/215.14 G against
214.84/214.88 G, **−0.13 %**, below the bar; it would also need a sibling triple and a change to
the shared probe proofs of both libraries.

The remaining `u64` products (`WhnfIota`, `WhnfIotaRec`, `IndPos2`) run once per call of cold
functions.
