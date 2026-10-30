# Lane derbv: a one-result `der_bv` for the walks' cut-offs

The task (parprof §3, rank 2): a leaf `der_bv` that returns only the bvar range, for the six walk
call sites that read only `der_b`'s first result (`ilg_go`, `il_go`, `il_bvar`, `inst_go`,
`lift_go`, `bvar_b`), small enough for the inliner if possible.

## 1. The function

`derBv` (`Arena/ExprMk.lean`): `der_b`'s three decodes and tier guard, then the arms in `der_b`'s
order (`app`, `bvar`, `lam`, `forallE`, `proj`, `letE`), each returning the range field alone.
The `const`, `fvar` and `sort` arms of `der_b` return `0` as their range, so `der_bv` has no arm for
them: they fall through to the final `return 0` without a count read. The `bvar` arm saturates by
a branch (`if x < 32767 { return x + 1 }; return 32767`) instead of `der_b`'s
`(x + 1) * u64(x < 32767) + 32767 * u64(32767 <= x)`.

No twin deviation: `der_b` and `der_bv` are both L's own reads of the derived word (con-ron: none).

**Inlining: no.** `der_bv` is 189 nodes (`Stmt.size`; `der_b` 340): the header is 27 and each
compound arm 25, because every arm carries its count read and its 32-bit load. Two arms would be
the most that fit S = 80. Raising S was measured (below) and does not help, so S stays 80 and
`der_bv` stays a call: a leaf with one result register, register-allocated.

## 2. Proof

* `derBv_spec`: `⦃s = s₀⦄ invoke "der_bv" [h] ⦃LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ r.headD 0 =
  derBW s₀.mem h⦄`, `derB_spec`'s first conjunct over the same model `derBW`. Same structure as
  `derB_spec`: the three decodes, then the dispatch as `derBvTail_spec` over `DerLocs`. The
  dispatch closes with `vcgen`, `simp only` over the locals and one `grind` (no `simp_all`).
  ExprMk.lean elaborates in 14 s in all.
* The six callers' proofs change only the lemma (`derB_spec … "der_b"` →
  `derBv_spec … "der_bv"`): `Lift.lean`, `Inst1.lean` (`l_model` specs, the models regenerate
  unchanged, since both posts state `derBW`), `InstList.lean` (`ilGo_step`, `ilgGo_step`),
  `InstListSpec.lean` (`il_bvar`), `BvarB.lean`.
* Program lists: `der_bv` in `liftProgFns`, `liftProg` (so `instProg` and `instListWalkProg`) and
  `bvbProg`, where it replaces `der_b` (the bvar-bound walk reads no other range). Write sets
  (`WriteSets.lean`), `imFns`, the inductive arm's sets (`Checker/IndArmFns.lean`) by hand; the
  generated lists (`loopFns`, `leafFns`, `coreFns`, `nvFns`, `phaseBFns`) by their scripts.

Diff: +60 lines in ExprMk.lean (the function 21, the two theorems 32), one changed line per
caller proof and per list.

## 3. Numbers

`Init` (`_tmp/fixtures/init/init435.ndjson`, accept), exact instructions (`perf stat -e
instructions:u`, `--jobs=4`; repeat runs agree to 0.01 %). The variants were built from master
70e23c1d's `checkerProg` by a script (`_tmp/derbv/Proto.lean`: the six calls renamed, `der_bv`
appended, inlined at S, compiled):

| variant | instructions | Δ |
|---|---:|---:|
| master | 229.31 G | |
| `der_bv` with `der_b`'s `u64` saturation, S = 80 (a call) | 227.40 G | −0.83 % |
| the same, S = 200 (inlined at the six sites) | 227.18 G | −0.93 % |
| master at S = 200 (no `der_bv`) | 229.27 G | −0.01 % |
| **`der_bv` with the branch saturation, S = 80** | **225.24 G** | **−1.78 %** |
| the branch, landed build (`checker.s` of this lane) | 225.29 G | −1.75 % |

* **Inlining does not pay here.** All six callers have calls themselves, so their locals live in
  the frame; the inlined body's decodes and loads go through the frame (`movq …(%rsp)`), where the
  leaf `der_bv` keeps them in registers. At S = 200 the six sites save 0.10 % more, and the
  program grows by 7,500 directives (other leaves of 81‥200 nodes are inlined too), with the
  matching cost in the inliner's literals and the asm parts. Not worth it.
* **The branch saturation is most of the gain** (−0.95 % of the −1.78 %): the `bvar` arm is hot
  (parprof §1.5: 162 M of `der_b`'s 597 M phase-B calls are on a `bvar`), and the `u64` form
  compiles to two `cmov` sequences and two multiplications. `der_b`
  has the same arm (its remaining callers are the `mk_*`, the `abstract1` walk and `lp_go`); the
  same change there is a candidate.

**Wall** (`wb2.py`, `--jobs=16`, CPUs 24–39, 40 interleaved rounds, load 25–50): median −1.2 %,
Wilcoxon p 0.26, mean −1.8 % [−5.0, +1.5] (base 4.10 s). Not resolved at this load.
**Parallel phase** (`ws.py`, 16 threads, CPUs 24–39, 12 interleaved rounds): span median −4.5 %
(lower in 9 of 12), worker cycles median −0.6 % (7 of 12), worker instructions −1.9 %.

## 4. Verdicts

`diff-e2e --parallel 16`: 634 of 634 agree (406 accepted, 228 not), 0 UNSOUND / INCOMPLETE /
CRASH / TIMEOUT.
