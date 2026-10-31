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

The handle word is con-ron's word, as before; only its readers and makers change. All of them
are in `L/TRec.lean` ("Handle words", the L expressions) and `Arena/StoreFields.lean` (their
Lean values and laws), the bridge to `Idx` in `Arena/Handle.lean`:

| L | Lean | value | where used |
|---|---|---|---|
| `⟦h⟧.tier` | `tierW` | `(h >> 31) & 1` | every node read (was bit 27) |
| `⟦h⟧.tag` | `tagW` | `f + w·(4 − f)`, `f = (h >> 26) & 15`, `w = (h >> 30) & 1` | every tag test (was `h >> 28`): the twin's `Idx.tag`, exact on every word |
| `⟦h⟧.idx` | `idxW` | `h & 0x43ffffff` | narrow node reads: bit 30 is kept, so a wide word reads ≥ 2^30, past every narrow array |
| `⟦h⟧.aidx` | `idxA` | `(h + 2^30) & 0x7fffffff` | `app` node reads (`node APP⟦h⟧`, `APP⟦h⟧.f`): a narrow word reads ≥ 2^30, past the `app` array |
| `⟦h⟧.gidx` | `idxG` | `h & (2^26 − 1 + w·(2^30 − 2^26))` | the twin's `idxNat` itself: the derived reads of the `app` and `param` arms |
| — | `hdW g t i`, `hdA t i`, `hdS g wide t i` | `t·2^31 + g·2^26 + i`, `t·2^31 + 2^30 + i` | the handles a push returns |

Why three index readers. The twin decodes a tag-4 word in two ways: `get`/`getApp` (and
`LTables.get`'s `param` arm) refuse the other shape, `derAt` does not. The L node read mirrors
`get` with the existing count check: `idxA` sends a narrow word, `idxW` a wide one, past the
array, so the read fails exactly where `get` answers `none` (`View.get_app` needs only
`idxA h < 2^30`, which the count check and the cap give: `app_idx_lt`). The derived reads
(`der_b`, `der_bv`, the `lp`/`hp` blocks, `lvlHPW`) mirror `derAt`, so their `app`/`param` arms
read at `idxG`, and `decI_idxG` holds for every word. Every other arm is entered only with a
narrow word (the tag is not 4), where `idxW` is exact (`narrow_of_tagW`, `decI_idx` now takes the
narrow premise). Dispatchers that compute one shared `i := ⟦h⟧.idx` and then branch on the tag
reassign `i := ⟦h⟧.aidx` (node reads) or `⟦h⟧.gidx` (derived reads) at the head of the `app`
arm (`bb_node`, `fl_node`, `lsb_node`, `ws_node`, `fr_node`, `lift_go`, `i1l_go`, `lp_go`,
`hoist_walk`, `e_view`, `nat_pred`, `raw_nat_lit`, `whnf_core_step`, `der_b`, `der_bv`, …).
With that the L code is the twin's on every word below 2^32, so no relation needs a validity
premise and no deviation row is needed.

Caps: the cons library's push tests `c ≥ capW` (`ConsSch.capW`: `2^30` for the `app` schema,
the only `wide := true` one, `2^26` for the others; the twin's `ENodeView.cap` and
`Idx.idxCap`); the bases `P`/`S` of each schema are `hdS tag wide 0 0`, `hdS tag wide 1 0`.
The generic store library (`StoreLib`, `ConsLibRel`, `DerRel`, `LpColRel`) is stated over
`(tag, wide)`: `protoRun L key tag wide …`, `Schema.hd`, `Schema.cap`, `mkS` (the twin's
`Idx.mk`/`Idx.mkWide`), `capS`.

The environment index (`Env.lean`, `Tiers.lean`, L-private): selector `(⟦w⟧.tag << 1) +
⟦w⟧.tier`, row `⟦w⟧.idx << 1`; `tbl_ix(w) = (⟦w⟧.tag, ⟦w⟧.tier, ⟦w⟧.idx)` (helper ronsync-b).

Not changed: the ROM, `pins.bin` and the export format hold no handle words (as con-ron's #133
notes for its own files); the cons hashes are of words but computed at run time.

## 5. Proof fallout

TODO

## 6. The module conversion (#136–#138): what our files needed

Our ConAgua files are not modules; they import con-ron's (now `module`) files and see their
public, exposed part. Two kinds of fallout, both fixed on our side, **no `@[expose]` was needed**
(no vendor patch; nothing to ask con-ron to upstream):

* **Imports.** #137's `lake shake` turned the Arena/Bridge imports into the minimal public set,
  so names our files got transitively before must now be imported directly:
  `DeclTwin` (`ConRon.Bridge.Checker.Decl`, `.Basis`, `.Fold`, `.Split`, `ConRon.Arena.Checker`),
  `Final/Twin` (`ConRon.Arena.Frontend.Prepare`, `.Prelude`, `ConRon.Bridge.Checker.Pins`,
  `ConRon.Bridge.Frontend.Prepare`, `ConLeche.Verify.Frontend.Prepare`), `Pins`
  (`ConRon.Arena.StdAxioms`, `.TrustAxioms`), `StoreDenLvl`/`StoreDenIntern`/`LevelArena`
  (`ConRon.Arena.WFProofs`), `RomExprRef` (`ConRon.Arena.Frontend.Readback`), `Rom.Gen`/`Rom.Test`
  (`ConLeche.Kernel.NatOpPins`).
* **Definitions** we unfold (`internNodeE`, `ETables.get`, `Idx.tag`, …) are in Arena files that
  are `@[expose] public section` throughout, so every `unfold`/`simp` of a twin body still works.

For the follow-up lane that turns ConAgua's own files into modules: a non-module file importing
these module files saw everything it needed once the imports were explicit; the failures were
all "unknown identifier/constant" (a missing import), never a hidden body. Our `module` files
(StoreFields, TRec, ConsLib, …) import only con-ron's Arena files, which expose everything.

## 7. Gates

TODO

## 8. Performance

TODO
