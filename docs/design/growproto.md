# Lane growproto: in-place top-down table doubling (prototype journal)

Question (lnext2 §5, rank 5): can the cons tables double **in place** without D38's mark pass and
swap chains, and without lnext §3.5's staging region (`back`: −17.5 % wall on app-lam, but +30–35 %
peak RSS)? Is it correct for linear probing with the `mulhi` home (D36), including the deferred and
the wrap-around entries? What does it gain?

Base: master 77841b51 (`checker.s` with the inliner, `checkerProgI`). Nothing landed but this
journal. Unproved prototype, model check, assembly, binaries, profiles and bench data:
`_tmp/growproto/` (`Grow.lean`, `tools/sim.py`, `s/`, `bin/`, `prof/`, `bench*.json`, `e2e_*.log`).

**Answer in short.**
* **The algorithm works.** One top-down sweep moves almost every entry to its place in the
  doubled table. The O(1) entries per growth that it cannot place that way get a mark, and the
  master swap loop (`kinnerL`) re-inserts them over the marked range only. No memory is used
  beyond the doubled table.
* **Verdicts:** 634/634 agree, 0 REFDIFF, sequential and `--jobs 4`. A randomized model check
  (12 k tables, skewed and wrapping clusters, stale slots) passes.
* **Wall** (30 interleaved paired rounds, Wilcoxon): app-lam **−19.8 %**, beta-ladder **−20.7 %**,
  both p < 0.001, slightly better than `back`. c05b −0.3 % (p < 0.001). `Init` −0.3 % at one
  thread (p 0.09) and −0.6 % at 16 threads (p 0.06): not resolved.
* **Peak RSS: unchanged** (app-lam 1,767 MB, beta-ladder 541 MB, `Init` 716 / 954 MB). The
  doubling touches the same words as master's.
* **Instructions:** app-lam −8.9 %, with `app_push` at 366 → 254 per call. beta-ladder −9.6 %,
  c05b −1.0 %, `Init` +0.05 %.
* **Against con-ron:** app-lam 1.80× → **1.44×**, beta-ladder 1.62× → **1.29×**, while L's peak
  RSS stays at 64 % of con-ron's on app-lam and 62 % on beta-ladder.
* **Recommendation:** a winner, clearly over the 2 % bar on the table-heavy inputs and not hurting
  `Init`. Proof lane: about +600 / −100 lines, 15–25 h (§6). D38 stays but changes its wording
  (§7).

## 1. The algorithm

Notation as `kgrowB`: old slot count `n`, `n2 = 2n`, slot `j` is the words `ob + 2j` (value: `≤ bt`
free, `bt < v < MARK` live, `≥ MARK` marked) and `ob + 2j + 1` (key word). The new home is
`home(q) = mulhi(mix(hash q), n2)`.

```
head, room check, count word (kgrowH); zero the upper half (kzeroL)
e, m, a, c, z := 0, n, n, 0, 0
for H = n-1 downto 0:                      -- pass 1, top-down
  v := slot H; if v is live:
    j := home(q)
    if j > H:                              -- the common case
      probe j upward over live unmarked slots, stopping at the top slot n2-1 (no wrap)
      free slot j      → move the entry to j; slot H := 0
      marked / top     → mark H (defer)
    elif j < H:        → mark H (defer)
    (j = H: the entry stays)
  on a mark: e += 1; m := H; record H in [m,c) (below n/2) or [a,z) (at or above n/2)
for H in [m, c), then H in [a, z):         -- pass 2: master's kinnerL (pick, probe with
  v := slot H; kinnerL                     --   wrap, place / swap), budget e
```

Pass 1 never reads or writes a slot below the cursor `H` except slot `H` itself. Its probe starts
above `H` and only goes up. Pass 2 is master's re-insertion loop, unchanged except where it scans:
it visits only the two ranges that hold marks.

**Why it moves almost everything.** Homes are the top bits of the mixed hash, so an entry of old
home `h` has its new home `2h` or `2h + 1`. An entry at slot `p ≥ h` (displacement `p − h`) has
`j < p` only if its displacement exceeds its home, that is, near the bottom of the table. A wrapped
entry (home near the top, slot near `0`) has `j ≈ 2h > p`: it is an ordinary up-mover whose probe
runs in the top of the new table. That region is already processed, so wrap-around needs no
special case. The only top-end deferral is a probe that reaches slot `n2 − 1` occupied (the new
table would wrap into unprocessed slots). The model (`tools/sim.py`, uniform hashing at load 3/4)
gives about **1.5–2 deferred entries per growth at every size**. That is 0.003 % of the entries at
`n = 65,536`. The pass-2 scan covers about 5 slots on average.

## 2. Correctness sketch

None of this depends on the home function: any `home` gives a correct table. The `mulhi` doubling
property only makes the deferrals rare.

**Pass 1's invariant `TopInv` at cursor `H`** (after slot `H` has been handled), against `m0`, the
memory after the zero loop:
1. the frame (`GFr`, words `0`, `1`) as in `ReinsInv`;
2. slots `< H` are exactly as in `m0`;
3. every slot `≥ H` is free, live unmarked with an admissible key, or marked (the same with `MARK`
   added) at a slot `< n` inside the mark ranges `[m, c) ∪ [a, z)`;
4. every node `x` is in exactly one of three states:
   * still in its old slot `< H`, untouched;
   * marked in some slot;
   * found (`FoundU`) from its new home through live unmarked slots, on a path that starts at a
     slot `> H` and does not wrap (`home + d < n2`).

**Step.** All paths of point 4 lie strictly above `H`.
* Clearing or marking slot `H` breaks no path: `H` is on none of them.
* A moved entry is written to the first free slot `j > H` of its probe. The probe passed only live
  unmarked slots, so the new path also lies above `H` and does not wrap.
* Writing a free slot breaks no other path, because paths consist of live slots.
* Point 2 holds because every write is at a slot `≥ H`.
* At `H = 0` point 2 is empty, so every node is marked or found, and every mark lies in `[m, c)` or
  `[a, z)`.

That is **master's `ReinsInv` at `i = m`**, with "marked ⇒ `i ≤ j < n`" refined to the two ranges.
Pass 2 is `krehashW_inv` run over `[m, c)`, then a skip lemma (no marks in `[c, a)`), then
`[a, z)`. At the end nothing is marked and every node is found. This is the conclusion master's
growth proof hands to `StoreGrow.lean` (`SlotsOKG` of the doubled table), so nothing downstream
changes. A marked slot is on no path, because paths run over live *unmarked* slots. Pass 2 relies on
this (master's `place_inv`), and pass 1 keeps it, because it never places an entry past a marked
slot: it defers instead.

The ranges replace an early exit on the mark count, which would need a counting invariant
(`e = #marks`). With the ranges the invariant stays positional, and `e` stays a budget, as in
master. The first prototype (`Grow_count.lean`, early exit at `e = 0`) and the range version
(`Grow.lean`) execute the same instruction count on app-lam (±300 of 45.7 G). The measured binary
`td` is the count version; `td2` is the range version: verdicts identical, wall within ±0.8 % of
`td`, not resolved over 12 rounds (`bench2.json`).

## 3. The prototype

`Grow.lean` rebuilds the 19 `X_push` functions of `fzCS` with the new growth block (four extra
locals) and runs the inliner (`inlRound 80`) and `compileProg`, as `AsmEmit` does. Mode `same`
reproduces `checker.s` byte for byte. Every rebuilt push passes `FunDecl.wfSpec`.

| binary | sequential | `--jobs 4` |
|---|---|---|
| `td` (count exit) | 634 agree, 0 REFDIFF | 634 agree, 0 REFDIFF |
| `td2` (range exit) | 634 agree, 0 REFDIFF | 634 agree, 0 REFDIFF |

The 634 fixtures grow many tables from 8 slots. In small tables the deferral share is highest
(about 6 % of the entries at `n = 8`), so pass 2 and the swap chains run often there.

`tools/sim.py` is a Python model of exactly this code, including stale slots (`0 < v ≤ bt`) and the
`kinnerL` swap loop. It was run on 12,000 tables of 8 to 4,096 slots: 80 % at load just under 3/4,
30 % with homes concentrated in 1–4 small ranges, 10 % at the two ends (bottom cluster plus top
wrap). After every growth it checks that each live entry is reachable from its new home over live
slots, and that no entry is lost or duplicated. No failures.

## 4. Numbers

Interleaved paired rounds (`tools/wb2.py`: `_tmp/internspeed/wb.py` plus `wait4` peak RSS), 30
rounds, CPUs 12–23,60–63, load 2.3–5.2. Wall changes are the median paired change, Wilcoxon p, and
the 95 % CI of the mean.

| input | master | con-ron | `td` vs master | con-ron vs master |
|---|---:|---:|---:|---:|
| app-lam | 9.54 s | 5.31 s | **−19.8 %** (p < 0.001; [−19.9, −19.7]) | −44.3 % |
| beta-ladder | 2.34 s | 1.44 s | **−20.7 %** (p < 0.001; [−20.8, −20.5]) | −38.3 % |
| c05b | 1.27 s | 0.73 s | **−0.3 %** (p < 0.001; [−0.6, −0.2]) | −43.0 % |
| `Init`, 1 thread | 17.25 s | — | −0.3 % (p 0.088; [−0.4, +0.0]) | — |
| `Init`, 16 threads | 3.81 s | — | −0.6 % (p 0.058; [−0.7, +0.0]) | — |

Peak RSS (median over 30 runs; the maximum is within 3 MB):

| input | master | `td` | con-ron |
|---|---:|---:|---:|
| app-lam | 1,767 MB | 1,767 MB | 2,750 MB |
| beta-ladder | 541 MB | 541 MB | 869 MB |
| c05b | 644 MB | 644 MB | 194 MB |
| `Init` 1 / 16 threads | 716 / 953 MB | 716 / 954 MB | — |

Exact instruction counts (`scripts/asmprof.py`):

| input | master | `td` | change |
|---|---:|---:|---:|
| app-lam | 50.17 G | 45.70 G | −8.9 % |
| beta-ladder | 13.63 G | 12.32 G | −9.6 % |
| c05b | 14.29 G | 14.15 G | −1.0 % |
| `Init` | 232.39 G | 232.50 G | +0.05 % |

On app-lam, `app_push` falls from 366 to 254 instructions per call (32.0 M calls), and `lam_push`
from 364 to 253. As with `back`, wall time falls about twice as much as instructions do: master's
mark pass and swap chains were cache misses more than instructions. The sweep reads the old half
once, top-down, and writes near `2H`: two descending streams. `back` swept upward but zeroed and
copied `4n` words. Here only the `2n` words of the upper half are zeroed, and nothing is copied.

* **`Init`**: presize (#174) keeps its persistent tiers from growing in the parse. What still grows
  is small (level tables, the scratch tier, memos outside `ConsLib`), and the change does not
  resolve.
* **c05b**: its growth is in the memos (`MemoLib`), which this does not touch (lnext §3.5).

## 5. What con-ron does

`HashMap2::try_resize` (`ron/hashmap2.rs`) allocates a new table of twice the capacity.
`move_slots` then visits the old slots in index order and inserts every live slot of the current
epoch with `insert_no_resize` (probe from the home to the first vacant slot). After that it frees
the old `Vec`.
* **At its peak** a table spans 3× the old size (old plus new). L stays at 2×, in place.
* **On the table-heavy inputs** con-ron is still 1.44× (app-lam) and 1.29× (beta-ladder) faster.
  The rest of the gap is not in growth: after this change `app_push` is 17.8 % of app-lam's
  instructions, and con-ron's push does no growth bookkeeping inline.
* **c05b's gap (1.76×)** is elsewhere (`rf_find`, lnext §1).

The new layout differs from con-ron's: pass 1 inserts in descending slot order, `move_slots` in
ascending order, so entries within a cluster of the new table can be ordered differently. Master's
absl rehash differs from con-ron's layout too. Either way it is representation only: lookups and
verdicts are the same.

## 6. Proof plan (if taken)

The table relation, `TierLay` (offset `0`), the freeze truncation, the scratch wrap, the find and
push specs and `StoreGrow.lean`'s conclusion `storeR_kgrow` stay as they are. Pass 2's invariant
and its place, probe and swap lemmas (`SlotRehash.lean`'s `ReinsInv`, `place_inv`,
`kinnerW_inv`) are reused.

| piece | file | change | lines |
|---|---|---:|---:|
| pass-1 model `ktopW` (step: stay / move / mark; no-wrap probe `kupW`), pass 2 as `krehashW` over two ranges; `kmarkW` goes | `SlotGrowSpec.lean` | +70 / −20 | +50 |
| `TopInv`, the step lemmas, `kupW_res` (the probe's path lies above `H` and does not wrap), `TopInv 0 ⇒ ReinsInv m` | `SlotRehash.lean` | +250 | +250 |
| `SlotOK`'s mark condition `i ≤ j < n` generalized to the ranges; the skip lemma `[c, a)` | `SlotRehash.lean` | +60 / −10 | +50 |
| the post-zero state ⇒ `TopInv n` (every node in its old slot, from `SlotsOKG` of the old table) instead of the mark-read lemmas | `StoreGrow.lean` | +60 / −40 | +20 |
| L-level specs: the pass-1 loop (hash via `khashB`'s spec, home, the three branches, the inner probe loop), the two pass-2 loops; the `kmarkL` loop spec goes | `ConsLibSpec.lean` growth block | +230 / −60 | +170 |

That is about **+600 / −100 lines, 15–25 h**: lnext §3.5's estimate for `back` was 12–20 h. This
plan adds where `back` removed, because the swap machinery stays for the deferred entries.

* **Risk:** moderate. Pass 1's invariant has one more node state than `back`'s (untouched below
  `H`). Its frame argument is the standard one: writes only at `≥ H`. The probe is the push's own
  insert without wrap.
* **No new runtime, no OS call.** The four extra locals are ordinary push locals.
* **Alternative:** drop pass 2's swaps by deferring into a second sweep. That would need a staging
  place for the deferred entries, so pass 2 stays absl's loop.

## 7. Deviation note (D38)

D38 stays (L still has no allocator to give an old table back), but its description changes when
this lands. The table doubles where it is. The upper half is zeroed. Then one top-down sweep
re-inserts each live entry from its new home with con-ron's probe. The probe runs above the sweep,
so it meets no unmoved entry. The few entries it cannot place this way get a mark: those whose new
home is below their slot, and those whose probe reaches the top slot or a marked one (about 1–2
per growth). absl's in-place swap loop then re-inserts them, scanning only the marked range. The
layout differs from con-ron's `move_slots` (descending instead of ascending order). That is
representation only.
