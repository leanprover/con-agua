# Lane `romintern`: the ROM interns (phase 0 / 1c leftovers)

Journal of lane `romintern`. Only this lane edits this file.

## Why the generic interns are covered, not refined one by one

The twin's `Frontend.internCI`, `internCV`, `internCaps`, `internRules`, `internRule`, `internFire`,
`internCIList`, `internExprList`, `internExpr`, `internProjTable` (and the `Arena` wrappers
`internExpr`, `internExprList`, `internCIList`) take arbitrary con-leche values. L has no such
function: it reads values that are already encoded, either the ROM's fixed data (`romData`: the
basis blocks, the axiom pins, the startup walk's items) or the pin-data buffer's variant list. So
a refinement "for every `ci`" cannot exist (the ROM encoding has no projection table, D29, and no
definition arm), and the `refines_part` theorems of `CIReadRef*.lean` (`ciFits`, plain rules,
`sortZ` names held) are as much as the generic statements can say.

In the twin these functions are reached only through:

* `BasisKind.decls` / `BasisKind.declsA` (from `internAllPins`, `checkBasisDecl`, `basisPinHit`,
  `quotPinHit`), at con-leche's basis blocks;
* the pin constants (`iffA`, `trueCvA`, `reduceNatDeclPin`, …, all proven), at con-leche's pins;
* `internAllPins` → `internPinSets` → `internPinSet` → `internExpr`/`internExprList`, at the pin
  list.

Once these callers are proven, the census counts the generic functions as covered (every path from
`TwinAccepts` passes through a proven target), which is the right reading: their behaviour is
accounted for exactly on the values the twin gives them. `internProjTable` is covered the same
way; the twin never calls it on ROM data (D29 stays Deliberate).

## Landing 1

* `internAllPins_PB` (`Rom/Stage.lean`) is now `@[refines ConRon.Arena.internAllPins]` (was
  `refines_part "over the pin-data buffer, at the decoded pin list"`). Statement unchanged (lane
  `pipeline`'s `checkerProg_internAllPins_PB` uses it as is). It is a full refinement in the decoder
  direction: the pin list is the twin's input and the buffer is L's; `TwinAccepts` quantifies the
  pin list existentially, so every L run that returns is a twin run at the decoded list. What the
  buffer format cannot spell (string literals, `natVal ≥ 2^64`; D6, Temporary) is a completeness
  gap of the input format, the same situation as `read_nat`'s 18 digits for `parseChunks` (D2),
  which is `@[refines]` too. **For the coordinator:** if D6 should block the full tag, revert this
  one attribute; everything else in the landing stands.
* `BasisKind.decls` / `declsA`: their two parts (`"the four kinds basisPinHit tries"`, kinds 0‥3,
  and `"the quotient block"`, kind 4) cover all five `BasisKind`s; added to `COMPLETE_BY_PARTS`
  (`scripts/census.py`).
* `EStore.dropScratch`: `scratchReset_dropScratch` (`Arena/ScratchRefine.lean`,
  `@[refines]`): `scratch_reset(0)` from `ArenaD s₀.mem a` gives `ArenaD` at
  `{a with store := a.store.dropScratch}`. `ArenaD` represents the whole store, so this is the full
  store operation; the old `ArenaD.reset` keeps only the `enableScratch` part tag. Its three callees
  (`NStore`/`LStore`/`LsStore.dropScratch`) are covered through it.
* Census (worktree, master `c921d648` merged): phase 0 185 / 5 written / 106 todo → 215 / 1 / 80
  (991 → 1118 of 1305 Lean lines proven; the one written left is `viewN`, see below); phase 1c
  62 / 10 / 1 → 72 / 1 / 0 (the one left is `builtinPreludeE`, lane `pipeline`); phase 2
  245 → 250 proven (`BasisKind.decls`/`declsA`, `internAllPins`, `internPinSet(s)`).
* No statement changed (lane `pipeline`'s `checkerProg_internReservedPins_PB` /
  `checkerProg_internAllPins_PB` use `internReservedPins_PB` / `internAllPins_PB` as they are).
  There are no `sorry`'d ROM-reader contracts under `Rom/` or `Arena/Rom*.lean`.

### Next: `viewN`

`viewN`'s callers are `promoteN`, `validateIndD` (proven) and `NIdx.isProjFnShape` (phase 2,
written: `is_proj_fn_shape` has L code, only a `sorry` stub spec `L.Ind.isProjFnShape_spec`). A
refinement of `is_proj_fn_shape` covers `viewN` (helper `romintern-pfs`).
