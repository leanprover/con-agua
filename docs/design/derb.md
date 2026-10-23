# Lane `derb`: `der_b` only after a hash-cons miss

Task (from lane compopt's profile): `der_b` (a chain of tag tests, ~67 instructions per call, the
top function by instructions on several fixtures) ran on every `mk_app`/`mk_lam`/`mk_forall`,
before `intern_*`. con-ron computes the derived word only on a miss (`EStore.intern`:
`persFindMaybe`, then `scr.find?`, and only in the `none` arm `derOfView` then `push`). Port
compopt's prototype (`feec12bc`, `scripts/compopt_progedit.py derorder mklazy`) into the L source
and fix the proofs.

## What changed (`ConAgua/Arena/ExprMk.lean` only)

* **`mk_app`, `mk_lam`, `mk_forall`**: `intern_*` first; inside the existing `if the counts
  changed` branch: bounds check, **`XDER[q] := 0`**, then the `der_b` calls (and `mk_lam`/
  `mk_forall`'s `satPred`), then the store, as before. This is closer to the twin: the children's
  derived words are read only on a miss.
* **Why the zero store.** L's `intern_*` is one function (probe + push), so `der_b` now reads the
  memory AFTER the append. For every handle that existed before, that reads the same; the only
  handle whose read differs is the new node itself (before: index past the count, `0`; after: index
  in range, the stale word in its slot, e.g. left over from a closed scratch tier). Zeroing the slot
  first makes it `0` again, so the post-append read equals the pre-append read for EVERY handle,
  not just valid ones. Hence `mkAppW`/`mkLamW`/`mkForallW` (and every spec statement over them) are
  unchanged: no downstream file was touched. Cost: one store per miss.
* **`der_b`'s tag tests in order of frequency on Init** (4 0 3 5 1 6 2 9 7; compopt's counts:
  `app` 374 M, `bvar` 179 M, `const` 122 M, `lam` 89 M, `fvar` 20 M, `forallE` 13.5 M, `sort`
  9.5 M, `proj` 5.8 M, `letE` 0.2 M). `der_b` cites `con-ron: none` (it reads L's own derived
  array); the tests are disjoint, so every tag gives the same result. `derB_spec` re-ran unchanged.
* `mk_let`/`mk_proj` still read before `intern_*` (rare on Init: `letE` 0.2 M, `proj` 5.8 M
  `der_b` calls); the same change would apply with `LEDER`/`PJDER` added to `BinTbl` (`mk_let` is
  ternary, so it needs its own `pushZ` shape).

## Proof

* `pushZ R S D k m t f a j`: the append to a binary table (records `R`, slots `S`, count
  `CTL[k + t]`) followed by the zeroed slot; `BinTbl` names the three tables.
  **`der_pushZ`**: `derBW`, `derFW`, `exprLPW` read the same after `pushZ` as before, for every
  handle (one proof for the three tables: `rcases` on the table, tier, handle tier, then `grind`;
  ~1 s each).
* `ainternW_grow` (and `la…`/`fa…`): a call that changed the counts was an append
  (`apushMem … (acnt m t)`, `t ≤ 1`, index `< 2^27`, `r`'s index/tier fields are the count and `t`).
* `ainternW_der` (and `la…`/`fa…`): from `ainternW m f a = some (r, m₁)` and the count change,
  the three reads of `m₁.set64 ADER q 0` (`q` = `r`'s slot) are those of `m`. Registered as an
  `arena_grind` multi-pattern (`ainternW m f a, (r, m₁), derBW (Mem.set64 m₁ ADER q 0) x`), so the
  three `mk*_spec` proofs only add `Mem.set64_set64_same` to their `finish`.
* Gotchas: `bv_decide` is out (it needs `Lean.ofReduceBool`, an axiom the census rejects; and in a
  `module` it fails to compile its reflection). `split at h` after `unfold` sees `Bool.rec`
  (instance unfolded); `simp only [f] at h` first. `first | exact absurd rfl hc | …` whnf's the
  memory in the push branches (timeout): try the cheap alternatives first.

## Measurements

`scripts/bench.py` (compopt's), binaries from master `f6d4f589` (base), base + compopt's prog-edit
(`proto`), and this branch before the master merge (`derb`); `--no-conron --no-ref`.

Init (v4.35.0 export, `_tmp/compopt/init/init435.ndjson`), 3 interleaved rounds, cpus 92-93, load ~80:

| | instructions | wall median (spread) |
|---|---:|---:|
| base | 696,662 M | 70.2 s (15%) |
| proto | 656,277 M (0.942) | 74.2 s (12%) |
| derb | 657,030 M (0.943) | 73.9 s (36%) |

Default set (13 fixtures), 3 rounds, cpus 94-95, load ~40, geometric means: instructions proto
0.968, derb 0.969; wall proto 1.018, derb 0.992 (noise). c03d 5,728 M → 5,649 M; c04a
43,089 M → 40,976 M. All verdicts agree (warm-up).

A second Init run, base vs derb only, 6 rounds (load ~80 plus an e2e run): instructions 696,665 M
→ 657,031 M (0.943); wall medians 99.4 s (spread 50%) vs 86.2 s (40%), ratio 0.867: with such
spreads neither this nor the first run's 1.053 says anything about wall time.

`derb` is within 0.1% of compopt's prototype (the extra zero store per miss). Instructions on Init:
−5.7%. Wall time: not measurable on this machine at this load (memory-bound; compopt's journal).
