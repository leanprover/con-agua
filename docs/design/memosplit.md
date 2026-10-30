# Lane memosplit: the memo put as a register leaf, and a cheaper find

The task (parprof §3, rank 1, and rank 3 if it fits the same `MemoLib` change): split the growth of
`memoPutG` into its own per-schema function `memo_grow`, so that the put becomes a small leaf that
fits the leaf register allocation (parprof §1.5: `ilm_put` takes 71 instructions on its common
path, all five parameters in the frame).

**Result.** One generic change in `ConAgua/Arena/MemoLib.lean`, no new function, no function list
touched, no caller changed, every spec statement unchanged:
* **put** (`memoPutG`): 17 → 13 locals. The growth reuses the put's own locals (`fd` becomes the
  old slot, `j` the probe slot, `b`/`n` the new region), and `fd := 4 j` is the base of the key's
  three stores.
* **find** (`memoFindG`), the cheap part of rank 3:
  * the default slot count tests the cap first (`dfltN_alt`): a large array takes one branch;
  * the hash multiplies by `golden` once instead of twice.

On `Init`: −2.14 % instructions over the whole run, −2.27 % in phase B, worker cycles −2.5 % at
16 threads. Wall time is not resolved (+0.3 %, p = 0.30).

## 1. Why not `memo_grow`

A leaf is a function with no call at all (`Stmt.calls`, `Compile.lean`), and only a leaf keeps
locals in registers (`fnAlloc`). A put that calls `memo_grow`, even as a tail call, is not a leaf:
its parameters go to the frame. Two ways keep the put a leaf:
* the callers call the growth (put returns "grow needed");
* the put keeps the growth inline, with fewer locals.

So the rank-1 design changes either all 76 call sites, or only `MemoLib`.

**Prototypes** (`_tmp/memosplit/Proto.lean`: variants of `checkerProg` compiled with the real
inliner and code generator, unproved). Exact counts, `perf stat -e instructions:u`, `Init`,
`--jobs=4`, against master 229.31 G:

| variant | instructions | Δ |
|---|---:|---:|
| `tail`: put tail-calls `X_grow` (the task's design) | 230.84 G | +0.67 % |
| `leaf`: put returns 1 at growth, every call site then calls `X_grow` | 227.80 G | −0.66 % |
| `nine`: one leaf put of 9 locals (count in `CTL` during the rehash) | 227.66 G | −0.72 % |
| `F`: only the find change | 226.71 G | −1.13 % |
| `R` (**landed**): find change + put of 13 locals | 224.40 G | −2.14 % |
| `Q`: as `R`, the rehash reads the old slot from memory (10 locals) | 223.68 G | −2.45 % |
| `nine2`: find change + `nine` with the store base | 223.27 G | −2.63 % |

* **The task's design is slower.** With the tail call the put is no leaf: its parameters go to
  the frame as before, and the frame grows.
* **`R` against `Q` and `nine2`** (0.3–0.5 % more):
  * `R` spills `k1`, `k2`, `v` (3 stores at entry, 3 loads; the rehash loop's locals outrank
    them, weights `8^depth`).
  * `Q` reads the moved slot's words after writing into the new region. Its proof needs the two
    regions disjoint (or the moves written in descending order and the indices told apart
    mod 4), plus a second free-slot loop with the key in memory.
  * `nine2` keeps the count in `CTL[cs + 1]` during the rehash, which needs `S.arr ≠ CTL`. The
    generic `memoPutG_spec` has no such hypothesis, so all 53 uses would change.
  * Not done.

## 2. The change

`memoPutG S` (13 locals; parameters `k1 k2 v fd j`, locals `c e b n d x y w`):
* **Common path** (no growth): register-only on `Init`'s hot memos.
* **`mgrowBlkG`:** `fd := b; b := b + n; n := n * 2`, then the rehash loop over `fd < b`, the
  header, the count. Then the free slot for `(k1, k2)` through `x := k1; y := k2` and the shared
  `mslotBlkG`.

The blocks (`mslotLoopG`, `mslotBlkG`, `mmoveG`, `mstepG`, `mrehashLoopG`, `mgrowBlkG`) keep their
specs and proofs. Only the local indices and the frame conditions moved, e.g. the rehash loop
keeps `z < 9, z ∉ {3, 4, 5}`.

`memoFindG S`: the default count is `n := len >> 2; if n > MN0 { n := MN0 } else { n := n -
u64(n > 0) }`, and the hash is `j := j * golden; j := mulhi(j ^ (j >> 32), n)`. `dfltN_alt`
(22 lines) states `dfltN` in the code's form. `dfltN` itself, `homeW` and every model (`mfindG`,
`mputG`, `mgrowAt`, `mrehashG`) are unchanged, so `MemoLibRel` and every caller build unchanged.

**Proof size.** `MemoLib.lean` +118 −88 lines (net +30, of it `dfltN_alt` 22; the rest is the blocks and specs with renumbered locals). Elaboration of the module:
8 s. The rebuild of everything above it: no proof changed.

## 3. Measurements

Master 70e23c1d against this branch (`checker.s` from `scripts/asm_file.py`); binaries
`_tmp/memosplit/ca-{base,new}`; `Init` (`init435.ndjson`, accept).

* **Instructions**, `perf stat -e instructions:u`, `--jobs=4`: 229.32 G → 224.42 G (**−2.14 %**).
* **Phase B** (worker sums, `_tmp/parprof/ws.py`, `--jobs=4`): 203.77 G → 199.14 G (**−2.27 %**).
* **16 threads on CPUs 24–39**, 12 interleaved rounds of `ws.py` (load 32–72), ratios new ÷ base:

  | | median | lower in |
  |---|---:|---:|
  | worker instructions | −2.31 % | 12 of 12 |
  | worker cycles | −2.50 % | 9 of 12 |
  | span of the parallel phase | −0.33 % | 6 of 12 |

  The span ranges from −12 % to +22 % between rounds.
* **Wall**, whole run at `--jobs=16` on CPUs 24–39 (`_tmp/bce/wb2.py`, 30 interleaved rounds, load
  18–35, `wstats.py`): base 3.685 s, new **+0.3 %** (Wilcoxon p = 0.30; mean [−1.4, +2.8]).
  Not resolved.

**What is left of ranks 1 and 3:**
* `Q`/`nine2` (another 0.3–0.5 %, §1);
* the find's header and default count kept in globals (parprof rank 3 proper). That changes the
  memo representation (`nG`, `mbG`), and with it `MemoLibRel`.

## 4. Lane memoglob: the region in globals (not landed), a cheaper hash (landed)

The task: the rest of parprof §3 rank 3. Keep each memo's slot count and base in named globals
(lfeat), set at `clear` and at the growth, so that the find no longer compares the header's stamp
and recomputes the default count; let bce facts cover the probe's bounds checks; look at `Q` and
`nine2` again under the new representation. Go only at ≥ 0.5 % instructions and with the proof
change generic in `MemoLib`/`MemoLibRel`.

**Result.** The globals pay (−1.7 to −1.9 %) but cannot be proved inside `MemoLib`/`MemoLibRel`
(§4.2), so they are not landed. Landed instead, generic in the two files: the memo's hash becomes
`(k1 + k2 * golden) * golden`, and the home slot is its high word times `n` (`mhome`), without the
fold `j ^ (j >> 32)`. On `Init`: **−1.21 % instructions**; wall time not resolved.

### 4.1 Prototypes

`_tmp/memoglob/Proto.lean` (memosplit's method: variants of `checkerProg`, compiled with the real
inliner and code generator, unproved; its `base` variant reproduces master's `checker.s` byte for
byte). Exact counts, `perf stat -e instructions:u`, `Init`, `--jobs=4`, master 3b3c479c 219.76 G
(repeat runs within ±0.01 %):

| variant | instructions | Δ |
|---|---:|---:|
| `G`: region in two globals per memo (`0` = the default region); `clear` writes the default; put as master's (13 locals) | 216.09 G | −1.68 % |
| `GL`: as `G`, `clear` only zeroes the count global (the default recomputed at the next find) | 220.46 G | +0.32 % |
| `G11`: as `G`, the growth reads the new region from the globals (11 locals) | 215.52 G | −1.94 % |
| `GN`: as `G` without the zero fallback | aborts | |
| `H`: no globals; the header always names the region (`clear` writes words 1, 2; `0` = default) | 217.63 G | −0.98 % |
| `Ka`: hash `(k1 + k2 * golden) * golden`, fold kept | 217.94 G | −0.83 % |
| `K` (**landed**, as proved): hash `(k1 + k2 * golden) * golden`, no fold | 217.10 G | −1.21 % |
| `KG`: `K` + `G11` | 212.86 G | −3.15 % |

* **Where the globals gain.** Profile of master (`scripts/asmprof.py`, `Init`): 434 M memo finds
  (22.1 G instructions, 10.1 %), 189 M puts (11.3 G). `ilm_find` (238 M calls, 49 instructions)
  takes the default region in 99.9 % of its calls; its prologue is 8 instructions of stamp and
  header test plus 7 of default count. With globals it is 2 loads and a zero test.
* **Why the zero fallback.** `GN` aborts: a worker region starts with its globals at zero (entry 2
  copies `CTL`, not the globals), and some memos are used before their first `clear`.
* **`GL`** recomputes the default on every find of a fresh table (`inst_list` clears `ilm` 26 M
  times for 238 M finds): worse than master.
* **`Q`/`nine2` under globals** (`G11`: the growth reads `b`, `n` from the globals, so the put needs
  11 locals instead of 13): another −0.26 %. Without the globals they stay as in §1.
* **bce.** Nothing to take. 97 % of `ilm`'s probes end at the first slot with one checked access
  (2 instructions). The analysis keeps facts only for the exact index expression, so the three
  words of a slot need three facts, and the loop head drops every fact about `j`.

### 4.2 Why the globals are not landed

`MemoRV` would read the region from the globals, and `memoRV_frame` moves it across any writer with
a `MemFrame`. `MemFrame` (`Arena/Frame.lean`) says nothing about globals, and the write-set check
lets any function write any global (`L/WriteSet.lean`). The 154 uses of
`memoRV_frame`/`memoRG_frame` in 31 files would each need a "the memo's globals are kept" fact.
The alternative is ctlglobals §3: globals inside `MemFrame`, keyed by the `CTL` words of `C`
(e.g. global `16 + x` kept unless `x ∈ C`, so that every frame list `[S.cs, S.cs + 1]` covers its
memo's globals unchanged), `closedW` restricted for `g := e`, and each model frame showing the
globals kept. That is a `--wide` change to `Frame.lean`, `WriteSet.lean` and the model frame
lemmas. It is outside this lane's limit, and it is worth −1.9 % on top of `K` (`KG`).

`H` needs no globals, but `clear` then writes the array: `mclearG_frame` becomes
`MemFrame [S.arr] [S.cs, S.cs + 1]`. That touches about 20 call sites outside the two files and the
clear chains of `CoreCaches`, for −0.98 %. Not done; `K` is cheaper and confined.

### 4.3 The change

`MemoLib.lean`:
* `kh k1 k2 := (k1 + k2 * golden) * golden`.
* New `mhome k1 k2 n := ⌊kh k1 k2 · n / 2^64⌋` (the code's `mulhi`), with `mhome_lt`.
* `mfindG` and `mslotG` probe from `mhome` instead of `homeW (kh …)`.
* The code: `j := k2 * golden; j := (j + k1) * golden; j := mulhi(j, n)` in `memoFindG` and
  `mslotBlkG`.

`MemoLibRel.lean`: `homeW (kh k1 k2) n` → `mhome k1 k2 n` (`runAt`, the probe lemmas). The cons
tables keep `homeW`.

**Why the hash is still sound.** Every bit of `k2` reaches the high half of `k2 * golden`, so
rfhash's concern (a bank's generation in `k2`'s high half) still holds. The fold only changed the
low 32 bits, which move `mulhi(·, n)` by at most 1 for `n < 2^32`. One-word keys get Fibonacci
hashing (`k1 * golden`, high bits).

**Proof delta.** `MemoLib.lean` +25 −11, `MemoLibRel.lean` ±14 (renames). Every spec statement,
`mprobeG`/`mputG`/`MemoRV`, and every caller are unchanged. Elaboration: `MemoLib` 3.9 s,
`MemoLibRel` 1.8 s.

### 4.4 Measurements

Master 3b3c479c against this branch's `checker.s`; binaries `_tmp/memoglob/ca-{base,new}`.

* **Instructions**, `--jobs=4`: `Init` 219.76 G → 217.10 G (**−1.21 %**);
  `complete_c04a_restart_70` 16.70 G → 16.47 G (−1.42 %); arena `cedar` 55.52 G → 55.27 G
  (−0.46 %).
* **16 threads on CPUs 24–39**, 8 interleaved rounds of `ws.py`, ratios new ÷ base:
  * worker instructions −1.29 % (lower in 8 of 8);
  * worker cycles +0.18 % (lower in 4 of 8);
  * span −2.68 % (lower in 5 of 8).
* **Wall** (`wb2.py`, 20 interleaved rounds, CPUs 24–39, load 4.3–7.3, `wstats.py`):
  * `Init` one thread: 16.56 s, −0.2 % (p = 0.35; mean [−0.4, +0.3]);
  * `--jobs=16`: 3.43 s, +0.1 % (p = 0.93).

  Not resolved. The removed instructions (a shift, an xor and a multiply per probe start) were
  off the critical path of the dependent loads.
* **Verdicts**: `diff-e2e --refs --parallel 16` agrees on 634 of 634 (406 accepted, 228 not);
  UNSOUND, INCOMPLETE, CRASH, TIMEOUT and REFDIFF are all 0.
