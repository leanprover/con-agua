# Lane ronsync: con-ron ed864140 → 97eead2d

con-leche unchanged at 0d2f467b. The protocol of PLAN.md, "Bumping the twin", steps 1–4.

## 1. What changed upstream (con-ron tasks #132–#138)

* **#133, the handle layout** (changes the executed checker; L mirrors it). Every handle word has
  one of two shapes. Bit 31 is the tier in both, bit 30 says which:

      wide   (expression `app` only)        narrow (every other node)
      bit  31      tier                     bit  31      tier
      bit  30      1                        bit  30      0
      bits 29…0    index                    bits 29…26   ctor tag (value unchanged)
                                            bits 25…0    index

  The old layout was tag 31…28, tier 27, index 26…0 for all. Capacities per tier: `app` 2^30
  (`Idx.wideCap`), every other array 2^26 (`Idx.idxCap`, half the old 2^27). `Idx.tag` reads
  `4` (`app`) off a wide word; `Idx.index` is per shape. The decode is not injective on all
  words (a narrow word with tag field 4 reads like the wide word with its index), and `get`
  repairs it: `ETables.get`'s `app` arm (and `getApp`) answers only for a wide word,
  `LTables.get`'s `param` arm only for a narrow one. `derAt` (the `derived` record) does NOT
  test the shape. `ENodeView.cap` replaces `Idx.idxCap` in `internNodeE`, `capOK`,
  `persCapNode`; the binder and N/L/Ls tests keep `idxCap` (now 2^26).
* **#134, #135**: proof-only (omega → grind, `clear_except` before grind).
* **#136–#138**: Arena and Bridge are `module` files (`public import`, a pruned `@[expose]` set
  derived from con-ron's own build), the root modules in `lake build`.
* #132: a script (`palomar-scan.py`); nothing for L.

## 2. The report (step 1)

`_tmp/bump-97eead2d/report.{txt,md,json}`: 19 commits; definitions 13 changed, 4 new, 0
removed; 2 types changed (`EWFAt`, `EWFAt'`); theorems 36 changed, 18 new. L items to re-check:
**48** (26 citations changed, 22 through a changed helper below a cited declaration: the
`internNodeE` family through `Idx.idxCap`); 1318 citations moved. Declarations of ours that
mention a changed twin function or an affected L item: **425** (240 theorems) in 176 files. All
5 patches apply. Changed twin definitions no L code cites: 14 (4 new: `ENodeView.cap`,
`Idx.isWide`, `Idx.mkWide`, `Idx.wideCap`), all of them mirrored (below).

## 3. The bump (step 2)

`scripts/bump-con-ron.sh 97eead2d…`: re-vendored, all patches applied, `census-rust.tsv`
regenerated, `provenance.py update --old ed864140`: 1318 citations moved, **40 CHANGED markers**
(24 files). The first build failed in four files only, the rest blocked behind `Handle.lean`:
`Handle.lean` (the layout), `PromoteTwin.lean` (`ENodeView.cap`), `DeclTwin.lean` and
`Final/Twin.lean` (imports trimmed by #137, see §6).

## 4. The mirror of #133 in L

### Data layout and the word readers

TODO

## 5. Proof fallout

TODO

## 6. The module conversion (#136–#138): what our files needed

TODO

## 7. Gates

TODO

## 8. Performance

TODO
