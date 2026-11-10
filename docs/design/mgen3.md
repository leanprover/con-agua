# Lane mgen3: resuming the conversion to `l_model`

Third lane on `l_model` (`ConAgua/L/ModelGen.lean`; `docs/design/mgen.md` for the first two).
The rule changed on 2026-11-10 (user, PLAN.md "Generated over hand-written models"): a conversion
that makes a module slower is no longer blocked; fewer hand models and proofs win over build time,
since a twin sync re-walks every hand model it touches (`docs/design/reproof.md` §2.4: 208 of the
last sync's long manual proofs walked a hand `…W` model call by call). Only an egregious regression
(~3× or above ~60 s per module) blocks a conversion, and then the generated model or the proofs
about it get fixed. Same constraints as every lane: no L program change (`checker.s`, `pins.bin`
identical), no change to a final statement, no new axiom, no heartbeats raised.

## 1. Inventory (master b91d1604)

Script `_tmp/mgen3/inv.py` (outside the repository), with `_tmp/mgen3/fam.py` for the family
table. Classification, stricter than mgen's (§1 there counted every triple that names `"f"`,
including callee premises `p.lookup "f" = …`):

* the program `checkerProg` has 1 775 functions, 289 of them template instances (`FunDecl`s
  with parameters: `memoFindG S`, …; generic hand specs, out of scope here);
* a function is *generated* if an `l_model` names it: **765**;
* it is *hand-specified* if it is not generated and some theorem's triple has it as its
  program (`invoke p … "f"` or `f.body` between the pre and the post): **591**;
* a hand spec's *models* are the heads of its post's conjuncts `F … = some …` and `r… = F …`;
  a model named in more than 40 files is vocabulary (`rdW`, `pinW`, `decPL`, `allocW`, …), not
  a hand model.

**Churn weight.** For each hand model, the changed lines (`difflib`, by declaration name,
reproof's `decls.py` on `09a78343a` → `86737151d`, ronsync2) summed over every declaration
of that sync that is the model, one of its `_`/`.` lemmas, or mentions it: what the sync cost
around that model. A family is the file that defines the models. 237 families, 23 603 lines
in all; the first 32 carry 70 %:

| family (models' file) | fns | reach | ronsync2 lines | cum. |
|---|---:|---:|---:|---:|
| `Arena/IndIface.lean` | 16 | 22 | 2835 | 12 % |
| `Front/IndApplySpec.lean` | 12 | 13 | 2057 | 20 % |
| `Rom/CIReadRefW.lean` | 18 | 9 | 1815 | 28 % |
| `Arena/IndInstallSpec/IcaW.lean` | 5 | 0 | 604 | 30 % |
| `Arena/DeclAndPinIndCopy.lean` | 3 | 1 | 600 | 33 % |
| `Arena/DeclHeader.lean` | 2 | 7 | 573 | 35 % |
| `Arena/IndInstallSpec/BlockRawRec.lean` | 5 | 4 | 546 | 38 % |
| `Arena/IndSumSpec/ConsBlockRecsTF.lean` | 4 | 2 | 521 | 40 % |
| `Arena/DeclCanonInfo.lean` | 4 | 1 | 475 | 42 % |
| `Front/IndApplySpec2.lean` | 9 | 4 | 440 | 44 % |
| `Arena/DeclCanonConst.lean` | 2 | 1 | 386 | 45 % |
| `Arena/IndDeclConstsDrop.lean` | 2 | 1 | 369 | 47 % |
| `Arena/IndSumSpec/TblProg.lean` | 2 | 2 | 334 | 48 % |
| `Arena/LevelSubstL.lean` | 2 | 5 | 332 | 50 % |
| `Arena/IndInstallSpec/PartsShapeFacts.lean` | 1 | 3 | 326 | 51 % |
| `Arena/IndPartsSpec/Bsp.lean` | 3 | 2 | 326 | 53 % |
| `Arena/StripTeleSpec.lean` | 1 | 9 | 322 | 54 % |
| `Arena/IndDeclConstsTable.lean` | 2 | 0 | 303 | 55 % |
| `Arena/WhnfIotaRefine.lean` | 1 | 1 | 302 | 57 % |
| `Arena/IndPosSpec/NcGoW.lean` | 2 | 7 | 298 | 58 % |
| `Arena/RecGenSpec/ClassFeR.lean` | 2 | 0 | 288 | 59 % |
| `Arena/IndPosSpec/RxMapW.lean` | 10 | 14 | 265 | 60 % |
| `Arena/RomPins.lean` | 2 | 0 | 254 | 61 % |
| `Arena/IndSumSpec/SumRules.lean` | 1 | 1 | 250 | 62 % |
| `Arena/DeclRec.lean` | 2 | 2 | 239 | 63 % |
| `Front/ApplyExpr.lean` | 9 | 2 | 239 | 64 % |
| `Arena/IndPosSpec/Pos2CvLpsWStage.lean` | 1 | 3 | 238 | 65 % |
| `Arena/IndDeclConstsRefire.lean` | 1 | 1 | 235 | 66 % |
| `Arena/IndLibSpec.lean` | 1 | 7 | 232 | 67 % |
| `Arena/RecClassSpec/CloseLams.lean` | 3 | 10 | 228 | 68 % |
| `Arena/WhnfIotaRefine6.lean` | 1 | 1 | 228 | 69 % |
| `Arena/IndPosSpec/U4W.lean` | 2 | 4 | 215 | 70 % |

("reach": the most other files any one of the family's models is named in.)

**By blocker** (first match in this order; syntactic, from the model's text and the spec's
hypotheses; "time" no longer blocks):

| blocker | functions | ronsync2 lines |
|---|---:|---:|
| reach (a model named in > 2 other files) | 141 | 12 815 |
| shape (`match` / `bind` / `do` in the hand model) | 48 | 1 826 |
| a precondition over `s₀.mem` (`pre`, `keep`) | 47 | 968 |
| bounds (`.size`, `ldE`, `136 <` in the model) | 5 | 77 |
| none of these (rejected for time or size, or never tried) | 147 | 8 644 |
| no model in the post (`r = [..]`, a pure or relational post) | 203 | 0 |

The 203 without a model are specs whose post is already a value (`r.headD 0 = …` over twin
values, a relation): nothing to convert. So the work is the 388 others, and by the sync's cost
the order is: the three big reach families (`IndIface`, `IndApplySpec`, `CIReadRefW`), then
the low-reach families above (most of them are "none of these": small files whose conversion
the old time rule rejected or nobody tried).

**Split.** The lead takes the reach families (`Front/IndApplySpec`, `Rom/CIReadRefW`,
`Arena/IndIface`'s models) and `Front/ApplyExpr`; three helpers take disjoint groups of the
low-reach families (§2).
