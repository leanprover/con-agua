# Lane `appcap`: do the big perf fixtures build more `app` nodes in L than in the twin?

Journal of lane `appcap`. Question from lane `e2efix` (`docs/design/e2efix.md`, "B3"):
`eager_open_nat_control` (67 KB) and `arena/good/perf/app-lam` (1.2 MB) fill `AREC` (array 4, the
`app` records) and accept only at `CA_WORDS = 2^27`. Is that the twin's own node count, or does L
build extra (missing sharing, a cache L lacks or clears more often, an intern path past the cons
table, a walk that rebuilds unchanged subterms)?

## Answer: the counts are equal, node for node

**Twin.** A measurement-only copy of `e2e-ref` (`ConAgua/E2E/Ref.lean`, not committed) with
con-ron's `installThenCheck` → `installFold`/`installStep`/`checkPending` copied in and a
`dbgTrace` of `store.pers.apps.size` and `store.scr.apps.size` right before every
`dropScratch` (both phases), after the prelude, parse and pins, at `--pins=1`.

**L.** The compiled `check` of lane e2efix's run (`_tmp/e2e/e2efix/check.bin`, `CA_PINS=pins.bin`,
`CA_WORDS=2^27`, `CA_HWM=2^20`). `AREC` holds node `i` of tier `t` at `4 i + 2 t` (tiers
interleaved, `AppStore.lean`), so its touched words / 4 = the larger tier's node count (page
granular, 512 words).

| fixture | twin persistent `app`s | twin scratch `app`s, peak (one declaration) | L `AREC` touched words | / 4 |
|---|---:|---:|---:|---:|
| `eager_open_nat_control` | 18,226 | **10,200,353** (phase B, record 51) | 40,801,792 | 10,200,448 |
| `arena/good/perf/app-lam` | 34,077 | **31,995,999** (phase B, record 30) | 127,984,128 | 31,996,032 |

`10,200,353 × 4 = 40,801,412` and `31,995,999 × 4 = 127,983,996`, rounded up to the next 512-word
page: exactly L's high-water marks. Every other declaration's scratch tier holds < 400 `app`s.
(Twin, all constructors, same two declarations: 11.3 M and 40.0 M scratch nodes.) The twin's
run: 9 s and 30 s (`e2e-ref`-style, compiled by Lean); L: 5.3 s and 18.6 s.

So L builds no extra `app` node: it hash-conses exactly the twin's nodes. Nothing to fix on the L
side, no deviation row. The fixtures are by construction big: `eager_open_nat_control` peels
`100000` in unary through `Nat.ble`'s structural recursion (its source says so; ~100 `app`s per
step), `app-lam` is a perf stress test. Both are within the twin's own capacity
(`Idx.idxCap = 2^27` nodes per constructor per tier, which `app_push` checks as well).

## Why it costs 2^27 words per array (layout and harness, not node count)

* **Interleaved tiers.** `AREC[4 i + 2 t]`: one tier can use only a quarter of the array's words,
  though the persistent tier holds 18 K / 34 K nodes here. Two words per node would suffice for a
  scratch-heavy run if the tiers were separate (e.g. persistent from the bottom, scratch from the
  top, or two arrays): `eager_open_nat_control` would then fit in `2^25` words (20.4 M words), and
  `app-lam` in `2^26` (64.0 M of 67.1 M words). A layout change in `AppStore.lean` and every reader
  of `AREC` (`Walk.lean`, the refinement's `ArenaRel`): not small, not done here.
* **One `CA_WORDS` for every array.** `harness/e2e.c` gives all word arrays the same size; at `2^27`
  the run's RSS (~5.4 GB) is mostly `AREC` (1 GB), `ASLOT` (1 GB, touched all over), arrays 28,
  32, 50 and 97 (hash-slot or epoch arrays, touched whole). A per-array override in the harness
  (`CA_WORDS_4=…`) would let these two fixtures run at `2^25` with only `AREC`/`ASLOT` raised.
  Harness only; proposed, not done.

Neither changes a verdict; both are proposals for whoever owns the store capacities.
