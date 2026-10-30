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
