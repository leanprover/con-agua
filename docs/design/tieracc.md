# Lane `tieracc`: the store record layout behind accessors (journal)

Branch `tieracc`, worktree `_tmp/wt/tieracc`. Goal: code and proofs outside the store library reach
the node stores' records only through accessors, so that lane `tierarr`'s layout change (tier `t` of
array `a` becomes array `a + 256 t`) is a library-only change. Inventory and motivation:
`docs/design/tierarr.md` (branch `tierarr`), §3.

## The interface

**L side** (`ConAgua/L/TRec.lean`, syntax in `L/Notation.lean`, `l_model` support in
`L/ModelGen.lean`). A tiered store record is `L.TRec ⟨arr, w, ca⟩`: the record array, the words per
node, the `CTL` index of tier 0's count. The stores and their one-word columns are declared once,
in `ConAgua/Arena/StoreFields.lean` (`LIT`, `APP`, `SUCC`, `ZERO`, `MAX`, `IMAX`, `PARAM`, `SORT`,
`CONST`, `LET`, `BVAR`, `FVAR`, `LAM`, `FORALL`, `PROJ`, `NANON`, `NSTR`, `NNUM`, `LVLS`; columns
`APP_DER` … `PROJ_DER`, `SUCC_HP`, `MAX_HP`, `IMAX_HP`, `LS_HP`, `SORT_LP`, `CONST_LP`, `FVAR_LP`),
with one constant per field (`APP.f`, `APP.a`, `LET.ty`, …). L code writes

| L | meaning | expands to |
|---|---|---|
| `APP⟨t, i⟩.f` | field `f` of node `i` of tier `t` | `TRec.ld APP t i APP.f` |
| `APP_DER⟨t, i⟩` | a one-word column | `TRec.ld APP_DER t i 0` |
| `APP⟦h⟧.a` | field of the node handle `h` names | `TRec.ld APP (tierE h) (idxE h) APP.a` |
| `APP⟨t⟩.count` | node count of tier `t` | `TRec.cntE APP t` |
| `⟦h⟧.tier`, `⟦h⟧.idx` | a handle's tier bit / index | `tierE h`, `idxE h` |
| `APP⟨t, i⟩.f := e` | field store (library only) | `TRec.st APP t i APP.f e` |

The builders are ordinary `Expr`/`Stmt` values (inlined: no call, nothing new in the semantics or
the compiler). Today `TRec.adE` emits exactly the old index expressions (`i * 4 + t * 2 + 1`,
`i * 2 + t`), so the generated code of a converted function differs only where the old code
shared an index in a local (`k := i * 4 + t * 2`). For the tiered layout, `TRec.ld`/`st`/`cntE`
change to `ld64t`/`st64t` and nothing else in L code.

No new keywords: the forms are built from `⟨ ⟩`, `⟦ ⟧`, `[ ]` and identifiers, so no identifier
becomes reserved (a keyword atom like `"count"` would reserve `count` in every Lean file).

**Proof side** (`StoreFields.lean`). Accessors `tfld m R t i f` and `tcnt m R t`, the handle
decoders `tierW`, `idxW` (moved here from `ViewL.lean`). One evaluation lemma per accessor:
`evalE_tld` + `tld` (pass to `vcgen` as `ld64` is passed), `evalE_cnt` + `tcntM`, `evalE_tierE`,
`evalE_idxE`; pure forms `Expr.pval_tld`, `pval_cntE`, `pval_tierE`, `pval_idxE` (`lang_grind`);
frames `tfld_set64_ne`, `tcnt_set64_ne`, `tfld_setG`, …. `TRec.ad` is written like `adE` (no
`t * 1`, no `+ 0`), so `tfld m APP t i APP.a` is *definitionally* `rdW (m.arr64 AREC) (i * 4 +
t * 2 + 1)` (`rfl`; tests at the end of the file) and `simp [tfld, TRec.ad]` turns it into that
text. Field constants are `@[simp]` (offsets as numerals after `simp`).

## Two phases

A widely used model cannot change alone: `eViewW` (the model of `e_view`) has 62 consumer files.
So:

* **Phase L**: convert L code to the accessors, keep each function's word model as it is (raw),
  and let the function's spec proof bridge: `vcgen [..., evalE_tld, tld, evalE_cnt, tcntM,
  evalE_tierE, evalE_idxE]` then `finish [..., tfld, tcnt, TRec.ad]` (or `simp [..]`). Blast
  radius: the spec proofs of the converted function (`e_view` had two: `eView_spec`, and a
  re-proof `eViewShape` in `IndPartsSpec3`). Exception: `l_model` files (Lift, Inst1, WalkLift,
  Hoist, Prelude, LevelSimp, IndPartsSpec10): the generated model changes with the code, so their
  consumers move with them (phase P for that family at once).
* **Phase P**: models, record relations (`ARecRel` …), the view lemmas (`View.lean`) and their
  consumers to `tfld`/`tcnt`, cluster by cluster, with `simp [tfld, tcnt, TRec.ad]` at the
  boundary to not yet converted code (counted by `scripts/layout_leaks.py`, removed as the
  boundary moves).

## Leak count (`scripts/layout_leaks.py`)

Kinds: `L-arr` (`AREC.u64[`), `L-cnt` (`CTL.u64[4 +`), `L-tier` (`>> 27) & 1`), `P-arr`
(`rdW (m.arr64 AREC)`…), `P-cnt` (`CTL) (4 +`), `P-stride` (`* 4 + … * 2`). Library files
excluded: `L/TRec`, `L/Notation`, `L/ModelGen`, `Arena/StoreFields*`, `StoreLib*`, `StoreRel`,
`StoreGrow*`, `ConsLib*`, `SlotGrow*`, `*Store.lean`, `LpCol`.

| state | L-arr | L-cnt | L-tier | P-arr | P-cnt | P-stride | lines / files |
|---|---:|---:|---:|---:|---:|---:|---|
| master `26450b77` | 354 | 265 | 165 | 1103 | 538 | 1303 | 2447 / 132 |

## Log

* 2026-10-24: interface (TRec, notation, ModelGen, StoreFields); `e_view` converted (phase L);
  asm/checker.s regenerated. **Batch 1 landed** (04b2c8da); verdicts 675/675 as master.
* 2026-10-24: lane tierarr landed its tiered arrays with the surface syntax `A⟨t⟩[i]`,
  `R⟨t⟩[i].f` (an `L.Record` in a tiered array) — the same text as this lane's first accessor
  syntax. The store accessors became `R⟨t, i⟩.f` (comma: no overlap with `A⟨t⟩[i]`);
  `R⟦h⟧.f`, `R⟨t⟩.count`, `⟦h⟧.tier` stay. After the switch the body of `TRec.ld` is
  tierarr's `ld64t R.arr t (i * w + f)` (the coordinator's interface: arguments fixed, only the
  body changes).
* Phase L by three helpers (whnf/defeq: 11 files, 47 spec proofs in 26 files; walks: 7 files,
  ~30 proofs; infer/misc: 12 files, ~30 proofs), all by `_tmp/tieracc/lconv.py` (regex rewrite
  of the L text) plus hand edits where an index was shared in a local (`k := i * 4 + t * 2`:
  `pnArm`, `peLit`, `nameRecPre`). No slowdown measured (spec proofs timed before/after).
* The `l_model` families (Lift, WalkLift, Inst1, the Hoist walk) went to phase P directly:
  `l_model` generates the models from the L text, so they read `tfld`/`tcnt` (offsets as
  numerals: `ModelGen.fieldNum` reads the field constant's value, so `tfld m APP t i 1`;
  field names in proofs gave mismatched `omega` atoms once `simp` had unfolded one copy). Their
  refinements were rewritten by `_tmp/tieracc/pconv.py` (raw proof terms → `tfld`/`tcnt`,
  balanced-parenthesis parser) and use the `…T` forms of `View.lean`'s lemmas (definitionally the
  raw ones: `view_appT … := view_app …`); LiftRefine, WalkLiftRefine, Inst1Refine needed no
  manual edit; HoistWalkRef needed `tfld_arr_eq` (a field depends only on its array) where it
  rewrote with `m₁.arr64 LEREC = m.arr64 LEREC`. InstLP stays phase L: its models are generic
  over the raw array (`ilwBinW AREC …`), and the rewritten models sent `finish` searching for
  25 min; bridged instead.
* Leak-script kinds added: `P-unfold` (`TRec.ad` in a proof outside the library: the phase-L
  bridges) and `P-cslot` (`viewOK m h 4`, `vok 22`: a count slot by number).
* **Batch 2 landed** (62f7d23b): the L code of 37 files; verdicts 675/675 as master.
* Phase P, as one scripted rewrite plus fixes (branch `tieracc-p`):
  * `_tmp/tieracc/pconv.py` over every non-library file: `rdW (m.arr64 AREC) (I * 4 + T * 2 + 1)`
    → `tfld m APP T I 1`, `rdW (m.arr64 CTL) (4 + T)` → `tcnt m APP T` (balanced parentheses,
    multi-line indices, nested reads). 1 285 lines in 101 files at the first pass.
  * `viewOK m h c` takes the store: `viewOK m h APP` (`idxW h < tcnt m APP (tierW h)`), `vok 22`
    → `vok BVAR` (`vokconv.py`; 56 files). Models that chose a store by a count index now choose
    it by `TRec`: `stuckW m FVAR e`, `evoCnt : Word → Option TRec`, `ilwDispW_arm`, the
    `simple`/`tagCase`/`arm` helpers of WhnfDeltaRefine2/4, Abs1Refine, BvarBRefine,
    InstLPWalkRef3. `expr_view_ok`'s L code loads the count itself per tag (`c := BVAR⟨t⟩.count`)
    instead of a count index (`CTL.u64[c + t]`).
  * The record relations (`ARecRel` …, `NatRec`/`StrRec`) state `tfld`; their store files stay
    raw inside, through one `XRecRel_raw : XRecRel m t i k ↔ <raw words> := Iff.rfl` each
    (`relraw.py`), so those proofs did not change. The `…T` lemma variants of batch 2 are gone:
    `View.lean`'s lemmas are themselves in accessor form now.
  * Frames: `tfld_arr_eq` (a field depends only on its array) and `tfld_set64_ne` where proofs
    rewrote with `m'.arr64 AREC = m.arr64 AREC` or `Mem.arr64_set64_ne` (`framefix.py`).
  * Generic models over a record base word became generic over the node: `nrpStr m t i`,
    `pfsStr m t i` (were `… (k : Word)` with `k = idxW h * 8 + tierW h * 4`).
  * Named raw accessors `lsO`/`lsL`/`nsQ`/`nsO`/`nsL` are used only inside their store files;
    elsewhere `tfld m LVLS t i 0` etc.
  * `der_b`'s models (`derBW`, `derFW`) and LpCol's (`lvlHPW`, `lsHPW`, `exprLPW`) read through
    the accessors; LpCol's hash/derived-column blocks are converted too (they are spliced into the
    level and constant pushes: `ConsLib.mapE_tld/cntE/tierE/idxE` let the variable renaming of a
    splice pass through the builders).
  * The level-list store is `LVLS`, not `LS`: `LS` clashed with a local `LS : List Level`.
  * The phase-L bridges (`tfld, tcnt, TRec.ad` in `finish`) were dropped where the models are now
    accessors (47 files); kept in WhnfSpineArgs, InferBodySpine, WhnfIotaRefine3, where the goal
    has a bound condition on the raw address.
* **Library** (the leak script's exclusions): `L/TRec`, `L/Notation`, `L/ModelGen`,
  `StoreFields`, `StoreLib*`, `StoreRel`, `StoreGrow*`, `ConsLib*`, `SlotGrow*`, `MemoLib*`
  (memo tables: not tiered), `*Store.lean`, `LpCol`, `ExprMk` (the `mk_*` pushes with their
  derived-column writes), and the per-store `*Refine.lean` files (the table instances: schema,
  record relation, the `_raw` iff). A layout change edits these.

| state | L-arr | L-cnt | L-tier | P-arr | P-cnt | P-stride | P-unfold | P-cslot | lines / files |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---|
| batch 2 (62f7d23b) | 87 | 57 | 39 | 1102 | 462 | 1056 | 103 | 317 | 2175 / 121 |
| phase P (tieracc-p) | 0 | 2 | 0 | 2 | 0 | 2 | 4 | 0 | 8 / 5 |

The 8 left: the two tag-indexed name-store counts in L (`keys_ok`, `projTableNameL`:
`CTL.u64[34 + g * 2 + t]`), WhnfIotaRefine3's `ldE (m.arr64 REC) (idxW h * 8 + tierW h * 4)`
(a bounds-checked read of `lit_major_to_ctor`'s model) and the bridges named above.
