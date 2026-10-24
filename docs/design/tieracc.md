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
`CONST`, `LET`, `BVAR`, `FVAR`, `LAM`, `FORALL`, `PROJ`, `NANON`, `NSTR`, `NNUM`, `LS`; columns
`APP_DER` … `PROJ_DER`, `SUCC_HP`, `MAX_HP`, `IMAX_HP`, `LS_HP`, `SORT_LP`, `CONST_LP`, `FVAR_LP`),
with one constant per field (`APP.f`, `APP.a`, `LET.ty`, …). L code writes

| L | meaning | expands to |
|---|---|---|
| `APP⟨t⟩[i].f` | field `f` of node `i` of tier `t` | `TRec.ld APP t i APP.f` |
| `APP_DER⟨t⟩[i]` | a one-word column | `TRec.ld APP_DER t i 0` |
| `APP⟦h⟧.a` | field of the node handle `h` names | `TRec.ld APP (tierE h) (idxE h) APP.a` |
| `APP⟨t⟩.count` | node count of tier `t` | `TRec.cntE APP t` |
| `⟦h⟧.tier`, `⟦h⟧.idx` | a handle's tier bit / index | `tierE h`, `idxE h` |
| `APP⟨t⟩[i].f := e` | field store (library only) | `TRec.st APP t i APP.f e` |

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
  asm/checker.s regenerated.
