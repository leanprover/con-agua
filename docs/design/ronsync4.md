# Lane ronsync4: the con-ron sync 4ca283d1 → c78714ac

Lane of 2026-11-13 (Opus), from master `dfe9fbdd7`. con-ron `4ca283d1 → c78714ac`, con-leche
`eb2c5939 → ca6af099`, upstream task #152 (con-ron DESIGN.md "### Task #152"; 38 con-ron and 33
con-leche commits). Standing decisions: no new driver/CLI option; every new or rewritten
function gets a generated model and a declarative refinement (exception: limb arithmetic);
`EREC` offsets kept stable, new fields appended.

## 0. Stage 0: footprint and stage plan

`scripts/bump-con-ron.sh --report c78714ac` (`_tmp/bump-c78714ac/report.{txt,md,json}`), then
presync3's classifier (`_tmp/ronsync4/fp.py`, `fp1.py`, outside the repository).

**Upstream** (con-ron's own triage): #573 the constructor record gains its family
(`ctorInfo cv nP nF induct`) and `IIndCaps.neverZero` is stored at install; #556 P-A the stuck
spine (`isStuckHead`, `iotaTarget`, `whnfStuck`: ι once, at the recursor's prefix); #572 the
official `whnfCore` memo policy (the memo moves from the knot's slot into the loop: pending keys
`pend`/`pendC`, the chain stored at its end, the cheap mode stores nothing); #556 P-W (a literal
reduct of `reduceNat` is the answer at once) and P-N (`NatBinOp`, `natBinOpOfName?` once,
`natBinOpResult` replaces `natOpResult`); #557 (`natOpWfNames` deleted); #558/#574/#576/#577
citations only. con-ron definitions: 60 changed, 21 new, 3 removed; types `IConstantInfo`
(ctor arity), `IIndCaps` (`neverZero`), `NatBinOp` (new). con-leche: 157 changed, 46 new, 10
removed. `pins/` did not move. Patches: con-leche/0003 and con-ron/0002 conflict (`KnotC.lean`,
`WhnfCore.lean`, `IotaMajor.lean`, `Lines.lean`).

**L items** to re-check: **159** in 32 files (130 changed citations, 28 gone, 50 through a changed
callee). Groups: `Front/IndApply` 30 (`installIndD`/`validateIndD`: the family), `IndInstall` 14
(caps, ctors), `WhnfDelta` 13 (`reduceNat`, `whnfStep`, the wf names), `WhnfM2C` 12
(`majorToCtor`), the Nat ops 24 (all cite the removed `natOpResult`), `DefEq` 9 (η readers),
`WhnfIotaRec` 9 + `WhnfIota` 6 (`iotaRecAt`, `ctorFamily`, `iotaCase3At`), `WhnfCore` 5 + `Knot` 4
(the memo policy, the stuck spine), `IndDeclConsts` 5, `DeclArms*` 9, `StrLit` 4, `Rom/CIRead` 3.

**Proof declarations** that mention a changed twin function or an affected L item, or carry its
`@[refines]`, plus the `IIndCaps` mentioners: **525 in 155 files, 314 theorems** (with every
`IConstantInfo` mentioner: 806 in 224 files). The `ctorInfo` arity alone: 119 positional
`ctorInfo _ _ _` sites in 47 files (one codemod rule).

| form (theorems) | count | lines |
|---|---:|---:|
| call-by-call walks (`callW`) | 43 | 3 454 |
| model-arm walks | 12 | 1 241 |
| declarative, ≤ 12 lines | 16 | 197 |
| declarative, longer | 39 | 1 418 |
| manual, > 12 lines | 67 | 3 232 |
| manual, ≤ 12 lines | 137 | 1 224 |

Hand specs in the footprint: 35, of which 24 are the Nat primitives (limb arithmetic, kept).

**Final statements**: none of `Final/*`, `Audit/*` mentions a changed twin type or function;
upstream's capstone statements are unchanged. Expected: no final statement change.

**The ROM**: the raw-`EREC` relations (`PinSetR`, `SliceR`, `DivModTypePins`, `BlockRecLpsOk`,
`CIReadRefBase`) mention no constructor record and no caps; `pins/` and `INatOpPinSet` did not
move. The sync reaches the ROM through the CI encoding only (`CIEnc`: the constructor's family
name, the caps' `neverZero` byte), whose refinement (`CIReadRefCI`, `CIReadRefCaps`) already
states its result through `decCI` over the record reader. So the move behind the record reader
is not done (the coordinator's rule: only the encoding bytes are touched).

## 1. Stage plan

**Kind of sync.** Mixed: one type change that breaks many proofs mechanically (the `ctorInfo`
arity: a codemod rule, where the ladder pays) and L-code rewrites (the `whnfCore` loop and slot,
the install's family and `neverZero`, the readers, the Nat dispatch), where it does not
(ronsync3: 0 of 54). Expectation: the rule rung closes most theorems that fail only by the arity
(tens), the rest are re-proofs of the ported functions.

**Stage 3a (lead)**: the constructor record's family at `p + 7` (appended; `decCI`'s ctor arm),
the caps' `neverZero` in the caps record's unread word `q + 7` (the old `sortZ` slot; the record
stays 15 words), the ROM's `encCI`/`encCaps` and the readers' layout lemmas; the pending keys'
storage (a stack slice at `CTL[136]`, `pendC` a suffix of `pend` by an offset: `pushCheapKey` only
ever keeps a suffix) with its relation; `NatBinOp` as a word code with `natBinOpOfName?`'s
vocabulary.

**Fan-out** (after 3a, three helpers, disjoint files):
* **ind** (#573, install and front): `IndInstall`, `IndDeclConsts*`, `IndSum`, `IndParts`,
  `IndPos`, `BasisL`, `DeclArms*`, `Front/IndApply`, `Rom/CIRead*`, and their spec files.
* **core** (#556 P-A, #572): `WhnfCore`, `WhnfCoreSlot`, `WhnfCoreLoop`, `Knot*`, the new stuck
  spine and memo functions, and the #573 readers in `WhnfIota*`, `WhnfM2C*`, `DefEq*`.
* **nat** (#556 P-W/P-N, #557): `WhnfDelta*`, `NatArms`, `Nat*.lean`, `Refine`, `StrLit*`, the
  `reduce_nat_wf` deletion.

## 2. Progress log

* 2026-11-13 07:07 start; 07:10 report; stage 0 sent to the coordinator.
* 07:11–07:17 bump (`79c91c281`). `bump-con-ron.sh c78714ac` stopped at two conflicting patches.
  con-leche/0003 (the `CSOK.*_hit_ws` companions of the `vcgen` ∧-split): upstream moved the two
  `whnfCore` memo lemmas from `KnotC` to `DiscC4` (#572), so their companions moved with them:
  the new patch con-leche/0004, and `DiscC4`'s new `whnfCoreLoopC_spec` finds them through
  `conleche_grind`. con-ron/0002: upstream's new `Arms/WhnfCore` loop proofs (lane B, explicit
  triples) needed the same ∧-split pattern (`all_goals subst_vars`, one closer per conjunct, eight
  sites), `Frontend/Lines`' four `MProd` states became `Prod` (the field order of our toolchain's
  `Prod` state is not `MProd`'s: `(Option …) × (Array … × Nat)`), `Walks/IotaMajor`'s old hunk
  dropped (upstream rewrote the arm, and the new text builds). ConLeche, ConRonArena,
  ConRonBridge build. 208 `CHANGED` markers.
* 07:17–07:22 stage 3a: `decCI`'s constructor reads the family at `p + 7` (`hd?`), `decCaps`
  `neverZero` at `q + 7` (the old `sortZ` word), `ArrExt.decCI`/`decCaps`, the layout table;
  `Rom/CIEnc`: the constructor's family name after `nF`, `bw neverZero` after `ctors`;
  `RomCI`'s item model (the family name is one more name item), `ErecRd.decCI_split`,
  `InitLink`. The arity codemod over the whole tree (`_tmp/ronsync4/arity.py`, `arity2.py`: 35
  files: binders, match arms, hypotheses with `{fam : NIdx}`), the same as rules in
  `scripts/sync-rules/ronsync4.txt` (plus generic `obtain`/`exact`/`fun` rules for base proofs).
* 07:22–07:28 compile passes (build, ladder `--write` on the failing files, build): ladder round
  1 (5 files, 12 failing theorems, 0 closed), round 2 (10 files, 24 failing, 3 closed at the
  codemod rung). By hand: `KnotMono1`'s store-monotonicity list at the new twin (the new
  `whnfCore` memo and stuck-spine functions, `natBinOpOfName?`/`natBinOpResult`; `ctorFamily`
  is pure now), `DeclCanonEq.ciD` and `installIndD_pre` at the new arity, and a TEMPORARY shim
  `Arena/NatOpShim.lean` (con-ron 4ca283d1's `natOpResult`, verbatim) so that the 754 modules
  behind `PinsNatOp` elaborate until the `Nat` port deletes it (upstream's lead did the same
  for #573's fields).
* 07:28–07:35 compile passes 3–4 (`KnotMono2`: `etaCtorPartialFam` is pure now; the shim's
  `natBinOpName`; `WhnfIotaRefine.decCI_ctorR`, `WhnfDeltaRefine`'s `natZeroOk`/`natSuccOk`
  statements at the family; ladder rounds 3–4: 23 more failing theorems, 4 closed at the codemod
  rung). Left blocked: `WhnfCoreLoop` (the slot and the loop changed: core's), `IndKindEnvProof`
  (`blockCapsAt`/`blockFormers` monadic: ind's), `AsmStubEq`/`AsmFileEq` (the ROM bytes changed:
  `checker.s` regenerated at integration). Tickets so far: 47 (`_tmp/ronsync4/tickets-r1.tsv`).
* 07:36 fan-out: helpers `ronsync4-core` (#556 P-A, #572), `ronsync4-ind` (#573 write side: the
  install, the front, the ROM reader, the declaration arms), `ronsync4-rn` (#573 read side and
  the `Nat` dispatch #556 P-W/P-N, #557), briefs `_tmp/ronsync4/brief-{common,core,ind,rn}.md`,
  3 build threads each (lead 3).
