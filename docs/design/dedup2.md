# dedup2: the remaining duplicate lemmas

Lane dedup2 of 2026-11-10 (Opus), from master `52f1aaf0c`. Follow-up of lane dedup
(`syncvocab.md`, "Follow-up: duplicate names"). Pure renames and deletions: no L change, no
statement of a final or refinement theorem changed.

## 1. The scan

An elaboration-time scan of the environment (`_tmp/dedup2/Scan.lean`, run with `scripts/lake env
lean`): it imports every built `ConAgua` module (minus the bench/emit executables, which redefine
`main` or each other's helpers), and groups every theorem of a `ConAgua` module (not generated
`Checker.Asm*`/`Checker.Prog*`, not auxiliary `eq_*`/`match_*`/`_proof_*` declarations) by its type
with binder names and binder kinds erased and universe parameters renamed by position (`Expr`
equality, so instances and implicit arguments must agree). A second pass compares the types
after reducible unfolding (`whnfR` at every subterm): it merges statements that differ only in
`≠` vs `¬ … = …`, `Word` vs `UInt64`, `ArrId` vs `Nat`. Uses come from the `.ilean` reference
index (every `.ilean` under `.lake/build`: module, line, columns), so a rename touches exactly the
references Lean resolved, not text that happens to match.

On master `52f1aaf0c`: 33 612 theorems, 256 groups of the same statement (406 removable names),
16 more groups after reducible unfolding (8 merged, §3).

Tooling (`_tmp/dedup2/`): `Scan.lean` (groups, declaration ranges, binder kinds, simp flag),
`idx.py` (the `.ilean` index), `plan.py` + `decisions.py` (which member stays, under which name,
in which module, and which files need an import), `apply.py` (deletes the other members, puts an
`attribute [...] K` line where one carried attributes, rewrites every reference, adapts the
arguments where the binder kinds differ: `D h` → `K _ _ h` where `K`'s leading binders are
explicit, `D x h` → `K h` where they became implicit and `h` names them, `@K x (by omega)`
otherwise, and adds `import <home>` where the kept module was not visible).

## 2. Batch 1: word arithmetic and word lists, into `L/WordOff.lean`

25 groups (the `UInt64` arithmetic and the `List Word` readings `r.getD k 0`, `r.drop 3`),
122 deleted theorems, 1281 references renamed, in 284 files. The kept statement is a new
theorem in `ConAgua/L/WordOff.lean` (namespace `L`, beside `off_toNat`; it imports only
`L.Syntax`), named in Mathlib style; its binder kinds are those of the copies with the most
references (`toNat_add_of_lt (d k : Word) (h)`: 289 references to explicit copies such as
`widx2`, 114 to implicit ones such as `word_add_toNat`). 244 files import `L.WordOff` now.

| kept | deleted | references |
|---|---|---|
| `L.getD_zero` | `getD_zero_headD`, `agGetD0`, `getD0`, `getD0_headD`, `getD_zero`, `ntGetD0`, `sumGetD0` | 51 |
| `L.toNat_add_ofNat_of_lt` | `word_add`, `fo_toNat_add_small`, `toNat_add_ofNat`, `toNat_add_small`, `toNat_add_small'`, `word_add_toNat`, `addW_toNat`, `ofNat_add_toNat`, `partsWadd`, `tailToNat`, `word_toNat_add` | 47 |
| `L.toNat_add_of_lt` | `addW`, `addW_toNat`, `peel_word_add_toNat`, `widx2`, `sum_toNat_add`, `wadd_toNat'`, `word_add_toNat`, `addN` | 403 |
| `L.toNat_add_of_not_lt` | `add_nc`, `add_noovf`, `dk_toNat`, `toNat_add_of_not_lt'`, `partsAddNoOv`, `pos2_word_add`, `rec3Add_toNat`, `sumAddNoOv`, `word_add_nowrap` | 24 |
| `L.toNat_and_one_le` | `and_one_le`, `tier_bit` | 11 |
| `L.toNat_eq_toNat_sub_one_add_one` | `ctrW_toNat`, `ue_toNat_pred`, `word_toNat_pred`, `ctrW_toNat'`, `fuel_pred`, `toNat_pred` | 25 |
| `L.decide_lt_eq_not_decide_le` | `dec_lt_not_le`, `dec_lt_not_le'` | 3 |
| `L.getD_one` | `getD1`, `getD_one`, `pr_getD1`, `getD1`, `agGetD1`, `cnGetD1'`, `getD1`, `getD1_eq`, `getD1_eq'`, `getD1_headD`, `getD_one`, `getD_one_eq`, `ntGetD1`, `sumGetD1`, `getD1` | 193 |
| `L.getD_two` | `getD2`, `getD_two`, `pr_getD2`, `getD2`, `agGetD2`, `getD2`, `getD2'`, `getD2_eq`, `getD_two`, `pos2_getD2`, `sumGetD2`, `getD2` | 120 |
| `L.getD_three` | `getD3`, `getD3'`, `getD3_eq`, `getD_three`, `scaGetD3`, `getD3` | 34 |
| `L.eq_zero_or_eq_one_of_le_one` | `h01`, `le_one_cases`, `word_le_one` | 36 |
| `L.toNat_ne_zero_of_ne` | `pr_word_ne0`, `toNat_ne_zero'` | 33 |
| `L.toNat_sub_one_of_ne` | `pr_word_sub1`, `sub1_toNat`, `word_pred`, `pos2_word_pred`, `rec2ToNat_pred`, `sumToNat_pred`, `toNat_sub_one'` | 52 |
| `L.toNat_add_one_of_ne` | `succW_toNat`, `toNat_succ_of_ne`, `pos2_word_succ` | 34 |
| `L.toNat_add_one_of_word_lt` | `succ_toNat_of_lt`, `wsucc`, `forUp_succ_toNat` | 19 |
| `L.toNat_add_one_of_lt` | `toNat_succ_lt`, `toNat_succ`, `escTN_add_one`, `toNat_add_one'`, `word_add_one` | 44 |
| `L.toUInt64_toNat` | `toUInt64_toNat_self`, `word_ofNat_toNat` | 13 |
| `L.add_one_add_one` | `word_add11`, `word_add2`, `word_add11` | 11 |
| `L.add_toUInt64_succ` | `word_succ_add`, `word_add_nat_succ` | 4 |
| `L.ofNat_toNat` | `ofNat_toNat'`, `ofNat_toNat_word` | 60 |
| `L.toNat_ofNat_of_lt` | `ofNat_toNat_lt`, `ofNatN`, `ofNat_toNat_lt` | 37 |
| `L.exists_toNat_eq_succ` | `apd_fuel_pred`, `wordSucc_of_ne` | 7 |
| `L.headD_drop_three` | `dcDrop3_headD`, `drop3_headD`, `partsDrop3` | 10 |
| `L.drop_three` | `drop3_eq`, `usDrop3_eq` | 8 |
| `L.getD_four` | `getD4_eq`, `getD_four` | 2 |

What the rewrite met:

* **Binder kinds.** An implicit copy's `D h` became `K _ _ h`; an explicit copy's `D w h` became
  `K h` when `h` is a name (its type fixes `w`), else `@K w (by omega)` (24 places, all
  `toNat_add_one_of_lt`/`toNat_sub_one_of_ne`/`exists_toNat_eq_succ` with a `by` argument);
  two named-argument calls (`addW_toNat (x := …) (y := …)`, DefEqStuckCert) by hand.
* **`L` shadowed.** 76 references are `_root_.L.…`: in 32 files a binder or a `variable (L : …)`
  named `L` (a `Lens`, an `NbLook`, an `RsLook`) turns `L.toNat_add_of_lt` into field notation on
  it. Where no binder shadows it the name is `L.…`.
* **A grind pattern across a private import.** `Pool.lean`'s `grind_pattern [arena_grind] add_nc
  => x + y < x` now puts `L.toNat_add_of_not_lt` into `arena_grind`; with a plain `import
  L.WordOff` every module that uses `arena_grind` without seeing `WordOff` failed with "Unknown
  constant". `Pool` re-exports it (`public import`, in `scripts/shake-allowlist.txt` with the
  reason).
* **Imports.** `shake` then found 37 imports whose only use had been a deleted copy (e.g. eleven
  of `IndPosSpec.NestKeyMap`, five of `Pos2DecHLSplit`): removed. `Arena/DeclValRef.lean` lost its
  last importers that way; nothing used its other lemmas (`dvT`, `checkDefnVal_dvT`,
  `decls_decCI_defn`, …: the refinements in `Verdict/DeclValsE.lean` no longer go through them),
  so it is deleted rather than listed as unbuilt.
* Module docstrings that listed a deleted lemma among the file's contents lost the name
  (DmCgW, Pos2DecHLSplit, DecCVX, ConsRecsTFSimOf, CtorX, DomsW, CheckSumCtor, For, WalkRefine).
  Other lanes' journals that cite old names (natsurvey, forloop, lconstructs, refgen) are history
  and stay.

## 3. Batch 2: the rest

Rescanned after batch 1 (master `d19b0e117`): 244 groups; 213 folded, 19 left (§5), the rest were
the pass-2 groups that stay apart (§5). 279 theorems deleted, 1611 references renamed to the kept
name, and 49 kept theorems renamed (405 references) because their name was a module prefix or a
prime (`rec2IwN_trunc` → `iwN_truncM_some`, `pos3_plW_mfr`/`plW_mfrP` → `plW_mfr`,
`decBool_t_m2c` → `decBool_true_of`, `hix_rd_dw` → `rdW_dw`, `stageR_hi` → `StageR.frame_hi`,
`viewSort_run'` → `viewSort_run`, …), or to give it the name its dot-notation callers use
(`slR_length` → `SlR.length`, `blockAt_grow` → `BlockAt.grow`). 486 files.

**Which copy stays.** A member of the group, in this order of preference: no import cycle (with
every other group's new imports counted: a per-group check let `viewApp_run` in WhnfSpineRefine,
`mkAppW_frame` in Abs1Refine and the Inst1Refine copies close a cycle); the copy that carries a
grind attribute (a deleted copy's `@[lang_grind =]` becomes `attribute [lang_grind =] K` in its
module, which then has to see `K`); no base module (`ConAgua/L`, `ConAgua/Compiler`) that starts
importing an Arena/Front/Checker module for it; the binder kinds most references use; fewest
files that need a new import; the smallest import closure. Four groups have a new home instead,
because both copies sat in modules that must not import each other: `L.Mem.arr8_set8_ne`
(`L/Records.lean`; copies in `Checker/PreludeSim` and `Rom/Subst`), and `L.run_throw`,
`L.except_error_bind`, `L.except_error_map` (`L/Logic.lean`, not `@[simp]` there; the
`Arena/FreezeSpec` copies were `@[simp]`, so FreezeSpec now says `attribute [simp] L.…`).
The census tags stay where they were: a group whose copy carries `@[refines …]` keeps that copy
(`iConstantInfo_name_refines`), or is left (§5) when the tagged one is a wrapper of the other.

**`erRd_of` and `erRd_of_erA`** (one fact up to unfolding `erA`, added to the scan by hand): kept
`L.Arena.erRd_of` (`ErecRd`, `(a v)` explicit, 49 references, and the field `rd` of `erRdOK`);
the 38 `erRd_of_erA h` are now `erRd_of _ _ h` (`h : erA m a.toNat = some v` is accepted:
`erA` unfolds to `erecP` at default transparency). **The `Idx` word `< 2^32` lemmas**
(`nidx_word_lt32` in Env and DeclCanonView2, `dmWord_lt32`, `View.word_lt`): `L.Arena.idx_word_lt32`.

What the rewrite met besides batch 1's kinds:

* **References the `.ilean` does not have.** A `first | … | …` alternative that did not run
  records no reference, nor does a lemma list inside an `l_model` command. Found by grepping every
  deleted name: `tyStab`/`ctStab`/`recStab` (IndFieldsLink3), `Keep.pcap` in two `l_model … finish
  [Keep.size, Keep.pcap]` (RomLevels; with the Rom copy gone `Keep.pcap` elaborated to an unknown
  `L.Keep.pcap`), `St.setLocs_mem'` (ParThreadCall, ThreadsE).
* **A `grind_pattern` or `attribute` naming the kept lemma** needs it in the importers' view, so
  those modules import its module publicly: Rom → Front.ApplyExpr (`Keep.pcap`), StoreRel →
  L.Records, Scan.Common → L.LocNF (in batch 1: Pool → L.WordOff).
* **An import that brings notation**: Compiler/BcePost importing Arena/StoreRel, and Rom/Subst
  importing Checker/PreludeSim, made `call` a token (L's statement notation), and their `| call
  xs f args =>` alternatives stopped parsing; hence the base-layer rule above.
* **An import that brings a name**: Verdict/ThreadsE, importing Front/FrontRunRef for
  `callE_of_run_err`, saw `L.Checker.invoke_agree` (Checker/FrontProg) before `L.invoke_agree`:
  now written `L.invoke_agree`.
* **Dot notation onto a structure field**: `hG.notStack_of_tab h` (implicit `x`) became
  `hG.tab_stack _ h`, the field (`Layout.Ok`, 6 places); named arguments whose binder names
  differ (`erRd_of_erA (m := m1)`, `SpineR.empty' (m := m)`, `misW_end (h := …)`) by hand.
* A deleted theorem's `include … in` / `omit … in` line goes with it.

| module | kept | deleted | refs |
|---|---|---|---|
| `Arena.Abs1Refine` | `L.Arena.mkAppW_frame` (was `L.Arena.mkAppW_frameA`) | `L.Arena.mkAppW_frame` | 3 |
| `Arena.Abs1Refine` | `L.Arena.viewFVarIdx_run` | `L.Ind.viewFVarIdx_run'`, `L.Ind.viewFVarIdx_run''` | 3 |
| `Arena.BasisBlockC` | `L.Ind.BlockAt.grow` (was `L.Ind.blockAt_grow`) | `L.Ind.BlockAt.grow` | 1 |
| `Arena.BasisBlockT` | `L.Ind.RefE.ofTrue` | `L.Arena.RefE.ofTrue` | 1 |
| `Arena.CoreRefine` | `L.Arena.ArenaR.caches_irrel` | `L.Arena.ArenaR.with_caches` | 3 |
| `Arena.CoreRefine` | `L.Arena.genW_zero` | `L.Arena.genW_zero'`, `L.Ind.genW_zero` | 3 |
| `Arena.CoreWalks` | `L.Arena.CoreSpec.zero` (was `L.Arena.CoreSpec.zeroW`) | `L.Arena.CoreSpec.zero` | 0 |
| `Arena.CoreWalks` | `L.Arena.EStore.lss_internBind` (was `L.Arena.EStore.lss_internBindW`) | `L.Arena.EStore.lss_internBind'` | 1 |
| `Arena.DeclAndPinInd` | `L.Arena.decCIs_succ` | `L.Checker.hix_decCIs_succ` | 3 |
| `Arena.DeclAndPinInd` | `L.Arena.trunc_get_some` (was `L.Arena.trunc_getAP`) | `L.Checker.hix_trunc_get` | 6 |
| `Arena.DeclApdRef` | `L.Ind.readLevel_run` | `L.Arena.pr_readLevel_run` | 1 |
| `Arena.DeclCanonInfo` | `L.Ind.decPL_grow` | `L.Ind.sumDecPL_grow` | 1 |
| `Arena.DeclCanonLvl` | `L.Ind.decW0B_of` (was `L.Ind.decW0B_of'`) | `L.Ind.apd_decW0B` | 3 |
| `Arena.DeclCanonLvl` | `L.Ind.iwTop_lt` | `L.Checker.iwTop_lt'` | 1 |
| `Arena.DeclNatBase` | `L.Ind.internSucc_stage` (was `L.Ind.internSuccN_stage`) | `L.Ind.internSucc_stage` | 0 |
| `Arena.DeclNatCv` | `L.Ind.ntBW_some` | `L.Rom.ntBW_inv` | 50 |
| `Arena.DeclNatLit` | `L.Ind.decCV_typeWR` | `L.Arena.decCV_type` | 0 |
| `Arena.DeclRec` | `L.Arena.erAllocW_mem` | `L.Ind.erAllocW_mem`, `L.Rom.erAllocW_mem` | 3 |
| `Arena.DeclRec` | `L.Arena.mapM_some_of` | `L.Front.Ind.mapM_some_ofI`, `L.Rom.rmapM_some_of` | 7 |
| `Arena.DefEqLeaves` | `L.Arena.ite_bne` | `L.Arena.bit_ne` | 1 |
| `Arena.DefEqLeaves` | `L.Arena.rd64_rdW` (was `L.Arena.del_rd64`) | `L.Ind.rd64_eq_rdW`, `L.Arena.rd64_rdW` | 1 |
| `Arena.DefEqMid` | `L.Arena.decE_beq_eq` | `L.Arena.decE_beq`, `L.Arena.ilw_beq` | 10 |
| `Arena.DefEqMid` | `L.Arena.decOptR_none` | `L.Arena.decOptR_noneS`, `L.Arena.decOptR_none_rec` | 4 |
| `Arena.DefEqMid` | `L.Arena.decOptR_some` | `L.Arena.decOptR_someS` | 2 |
| `Arena.DefEqMid` | `L.Arena.mode_eager_bit` | `L.Arena.decMode_eager` | 2 |
| `Arena.DefEqMidSpine` | `L.Arena.viewR_const` | `L.Arena.slViewR_const` | 1 |
| `Arena.DefEqStuckCert` | `L.Arena.decCI_indK` | `L.Arena.decCI_indF` | 2 |
| `Arena.DerRel` | `L.Arena.ArenaD.grow` | `L.Front.ArenaD.grow` | 4 |
| `Arena.DerRel` | `L.Arena.DerR.grow` | `ConAgua.Front.UnescapeLink.DerR.grow` | 1 |
| `Arena.DerRel` | `L.Arena.bvar_derConst` | `L.Front.bvar_derConst` | 0 |
| `Arena.DerRel` | `L.Arena.bvar_derLit` | `L.Front.bvar_derLit` | 4 |
| `Arena.DerRel` | `L.Arena.bvar_derSort` | `L.Front.bvar_derSort` | 0 |
| `Arena.Env` | `L.Arena.erecP_lt64` | `L.Ind.erecP_lt64` | 16 |
| `Arena.ErecRd` | `L.Arena.RdOK.rd` | `L.Ind.rdW_zero'` | 6 |
| `Arena.ErecRd` | `L.Arena.erRd_of` | `L.Ind.erRd_of_erA` | 38 |
| `Arena.ErecVocab` | `L.Ind.erRd_foldN` | `L.Arena.erRd_eqW` | 2 |
| `Arena.EtaRescueRef` | `L.Arena.decCI_ctor_cv` (was `L.Arena.decCI_ctor_cv'`) | `L.Arena.decCI_ctorInfo_cv`, `L.Ind.decCI_ctor_cv` | 2 |
| `Arena.EtaRescueRef` | `L.Arena.erSlEq_spec` (was `L.Arena.erSlEq_specR`) | `L.Stubs.erSlEq_spec'` | 0 |
| `Arena.FVarRangeRefine` | `L.Arena.coreWalkFuel_toNat` | `L.Arena.coreWalkFuel_word`, `L.Arena.fuelW`, `L.Ind.fuelW_eq` | 14 |
| `Arena.FormerNZRef` | `L.Arena.decCI_ind_cv` (was `L.Arena.decCI_ind_cv'`) | `L.Ind.decCI_ind_cv` | 3 |
| `Arena.FormerSortRef` | `L.Arena.viewSort_of_view` (was `L.Arena.viewSort_of_view'`) | `L.Ind.viewSort_of_view` | 3 |
| `Arena.FormerSortRef` | `L.Arena.viewSort_run` (was `L.Arena.viewSort_run'`) | `L.Ind.viewSort_run` | 4 |
| `Arena.Frame` | `L.Arena.MemFrame.arr` | `L.Arena.MemFrame.arr_eq` | 13 |
| `Arena.FuelConsts` | `L.Arena.liftFueled_some` | `L.Arena.liftFueled_run_some` | 1 |
| `Arena.Handle` | `L.Arena.decE_eq` | `L.Ind.decE_eq_decI` | 4 |
| `Arena.IlpRd` | `L.Ind.erCopyW_iwFr` | `L.Ind.posmemo_erCopyW_iw` | 2 |
| `Arena.IlpRdReal` | `L.Ind.ilpfA_stage` | `L.Ind.dcIlpfA_stage` | 1 |
| `Arena.IlpRdReal` | `L.Ind.ilpfC_stage` | `L.Ind.dcIlpfC_stage` | 1 |
| `Arena.IndDecStab` | `L.Ind.OMono.decRules` | `L.Ind.partsDecRules_mono` | 3 |
| `Arena.IndInstallSpec.DomsW` | `L.Ind.decHL_grow` | `L.Ind.decHL_grow3` | 22 |
| `Arena.IndInstallSpec.InstallRec2Tele` | `L.Arena.Sim.post` | `L.Ind.sumSim_map` | 1 |
| `Arena.IndLibSpec` | `L.Ind.hslice?_succ` | `L.Arena.hslice?_succ`, `L.Arena.lp_hslice_succ` | 21 |
| `Arena.IndLibSpec` | `L.Ind.mapM_opt_length` | `L.Arena.mapM_len`, `L.Arena.mapM_option_length` | 4 |
| `Arena.IndMaster` | `L.Ind.mapM_congr_of` | `L.Ind.mapM_opt_congr`, `L.Ind.mapM_opt_congr3` | 17 |
| `Arena.IndPartsSpec.EqW` | `L.Ind.SlR.length` (was `L.Ind.slR_length`) | `L.Ind.SlR.length` | 2 |
| `Arena.IndPartsSpec.IndPartsProg2` | `L.Ind.RelW.simS` (was `L.Ind.partsSimW`) | `L.Ind.RelW.simS` | 1 |
| `Arena.IndPartsSpec.RecTW` | `L.Ind.viewConst_run` (was `L.Ind.viewConst_run'`) | `L.Ind.viewConst_run` | 4 |
| `Arena.IndPartsSpec.SetEqW` | `L.Ind.pslR_nil` (was `L.Ind.partsPSl_nil`) | `L.Ind.pslR_nil` | 2 |
| `Arena.IndPosSpec.CtxFields` | `L.Ind.rec3_specW_iw` (was `L.Ind.posRec3_specW`) | `L.Ind.partsRec3_specW` | 1 |
| `Arena.IndPosSpec.SlRCongr` | `L.Ind.SlR.congr` (was `L.Ind.slR_congr`) | `L.Ind.SlR.congr` | 3 |
| `Arena.IndPosSpec.UnW` | `L.Ind.invoke_exec0` | `L.Arena.invoke_zero_false` | 5 |
| `Arena.IndRealAbs` | `L.Ind.copyW_iwFrame` | `L.Ind.posmemo_copyW_iw` | 5 |
| `Arena.IndRealAbsPos` | `L.Ind.piBW_afr` | `L.Ind.piBW_afrR` | 3 |
| `Arena.IndRealFvt` | `L.Ind.StageR.frame_hi` (was `L.Ind.stageR_hi`) | `L.Ind.StageR.frame_hi` | 23 |
| `Arena.IndRealMemoCr` | `L.Ind.crfP_prog` | `L.Ind.crfP_progK` | 11 |
| `Arena.IndRealNames` | `L.Ind.strWords_rec` (was `L.Ind.strWords_recB`) | `L.Front.Ind.strWords_rec` | 2 |
| `Arena.IndRealOpf2` | `L.Ind.view_run_of` (was `L.Ind.opf_view_run`) | `L.Arena.view_run_of` | 1 |
| `Arena.IndRealWalkT` | `L.Ind.keeps_bvarB_sp` | `L.Arena.keepsSp_bvarB` | 1 |
| `Arena.IndStubs` | `L.Ind.AbsOK.cr` | `L.Ind.AbsOK.crMemo` | 8 |
| `Arena.IndSumSpec.DecCVpGrow` | `L.Ind.getSort_of_get` | `L.Arena.getSort_of_get'` | 2 |
| `Arena.IndSumSpec.McGoStep` | `L.Ind.Sim.ofRun` | `L.Ind.rcSim_ofRun` | 1 |
| `Arena.IndSumSpec.McGoStep` | `L.Ind.hbFastW.arm1` | `L.Ind.hbFastW_eq` | 3 |
| `Arena.IndSumSpec.SoaW` | `L.Ind.consW_pslr` | `L.Ind.clsConsW` | 3 |
| `Arena.IndSumSpec.TsrW` | `L.Ind.decRule_fields` | `L.Ind.decRule_fields'` | 1 |
| `Arena.IndSumSpec.TsrW` | `L.Ind.poolSmall_of_stage` (was `L.Ind.rcPoolSmall`) | `L.Arena.poolSmall_of_stage` | 1 |
| `Arena.IndT.BlockCS` | `L.Ind.dcF_bts` (was `L.Ind.dcF_btsC`) | `L.Ind.dcF_bts` | 1 |
| `Arena.IndT.Lift` | `L.Ind.StageC.of_cstep` | `L.Ind.StageC.of_cstepE` | 1 |
| `Arena.IndT.Pass` | `L.Ind.StageC.ofView` | `L.Ind.StageC.of_checkE` | 5 |
| `Arena.IndView` | `L.Ind.view_const_f` | `L.Arena.view_const_f` | 5 |
| `Arena.IndView` | `L.Ind.view_sort_f` | `L.Arena.view_sort_f` | 1 |
| `Arena.InferBodyDisp` | `L.Arena.eViewW_head` | `L.Arena.quick_eViewW_head`, `L.Ind.partsEView_head` | 2 |
| `Arena.InferBodyIntern` | `L.Arena.keeps_cpl_internFVar` | `L.Arena.peel_keeps_cpl_internFVar` | 1 |
| `Arena.InferBodyIntern` | `L.Arena.ld64_rdW_spec` | `L.Arena.lp_ld64_spec` | 1 |
| `Arena.InferFieldSort` | `L.Arena.readNameM_run'` | `L.Arena.pr_readNameM_run` | 1 |
| `Arena.InferFieldSort` | `L.Arena.readNamesM_run'` | `L.Arena.pr_readNamesM_run` | 10 |
| `Arena.InferLeaves` | `L.Arena.CoreSpec.zeroLet` | `L.Arena.coreSpec_zero` | 1 |
| `Arena.InferLeaves` | `L.Arena.decCI_cvA` | `L.Ind.decCI_cvN` | 1 |
| `Arena.InferLeaves` | `L.Arena.fainternW_hw` | `L.Ind.fainternW_hw'` | 1 |
| `Arena.InferLeaves` | `L.Arena.mkForallW_hw` | `L.Ind.mkForallW_hw'` | 1 |
| `Arena.InferLeaves` | `L.Arena.viewLs_run` | `L.Ind.viewLs_run'` | 1 |
| `Arena.InitLink` | `L.Arena.iConstantInfo_name_refines` | `L.Checker.hix_decCI_name` | 3 |
| `Arena.Inst1Refine` | `L.Arena.viewApp_run` | `L.Arena.viewApp_run'`, `L.Ind.viewApp_run'` | 12 |
| `Arena.Inst1Refine` | `L.Arena.viewBind_run` | `L.Arena.viewBind_run'`, `L.Arena.viewBind_run₀`, `L.Ind.viewBind_run`, `L.Ind.viewBind_run_s` | 33 |
| `Arena.InstLPKeys` | `L.Arena.nview_tier` | `L.Front.Ind.nview_tier` | 1 |
| `Arena.InstLPLevel` | `L.Arena.CoreS.withReadLC` | `L.Arena.CoreS.readLC'` | 5 |
| `Arena.LevelInternRef` | `L.Arena.NmsR.of_arr` | `L.Ind.nmsR_congr` | 4 |
| `Arena.LevelView` | `L.Ind.lview_of_lvNodeW` | `L.Arena.lvNodeW_view` | 1 |
| `Arena.LoopT` | `L.Arena.memoRV_zeroAt` | `L.Checker.memoRV_zero0` | 2 |
| `Arena.MemoLib` | `L.Arena.mfindG_eq_of` | `L.Checker.mfindG_congr` | 1 |
| `Arena.NStrStore` | `L.Arena.setLoc_twice` | `L.Arena.St.setLoc_setLoc_same` | 0 |
| `Arena.NatArms` | `L.Arena.ModeOK.grows` | `L.Front.ModeOK.growsF` | 4 |
| `Arena.NatCmpFacts` | `L.Arena.pv_ge_wt` | `L.Arena.pv_ge` | 4 |
| `Arena.NatCmpFacts` | `L.Arena.pv_lt_wt` | `L.Arena.pv_lt` | 5 |
| `Arena.NatGcd` | `L.Arena.Norm.of_agree` | `L.Arena.Agree.norm` | 3 |
| `Arena.Pins` | `L.Arena.pinsReady_true` | `L.Arena.pinsReady_of` | 1 |
| `Arena.PinsNatOp` | `L.Arena.AM.congr_run` | `L.Arena.am_eq_run` | 1 |
| `Arena.Pool` | `L.Arena.Mem.size_arr64_set64` | `ConAgua.Scan.size_set64` | 0 |
| `Arena.Pool` | `L.Arena.tag_idx_toNat` | `L.Ind.mask40_toNat` | 3 |
| `Arena.Pool` | `L.Arena.tpool_getD` | `L.Arena.tpool_rd` | 2 |
| `Arena.ProjGuardRowsOpf` | `L.Ind.callW_opfF` (was `L.Ind.callW_opfFC`) | `L.Ind.callW_opfF` | 3 |
| `Arena.PropReadRefine` | `L.Arena.RdAfter.refl` | `L.Arena.RdAfter.same` | 0 |
| `Arena.RecCheckSpec.ErToIwWStage` | `L.Ind.cvLpsW_stage` | `L.Ind.pos2_cvLpsW_stage` | 5 |
| `Arena.RecCheckSpec.TcmLook` | `L.Ind.lpsW_mfr` | `L.Ind.lpsW_mfrP`, `L.Ind.lpsW_mfrT`, `L.Ind.pos3_lpsW_mfr` | 2 |
| `Arena.RecCheckSpec.TcmLook` | `L.Ind.pinternW_mfr` | `L.Ind.pinternW_mfrP`, `L.Ind.pos3_pinternW_mfr` | 2 |
| `Arena.RecCheckSpec.TcmLook` | `L.Ind.plW_mfr` | `L.Ind.plW_mfrP`, `L.Ind.pos3_plW_mfr` | 2 |
| `Arena.RecCheckSpec.TcmLook` | `L.Ind.plgW_mfr` | `L.Ind.plgW_mfrP`, `L.Ind.pos3_plgW_mfr` | 4 |
| `Arena.RecClassSpec.CloseLams` | `L.Ind.decCS_motive` | `L.Ind.rec2DecCS_mot` | 2 |
| `Arena.RecClassSpec.CloseLams` | `L.Ind.iwN_lt` | `L.Ind.iwN_idx`, `L.Ind.iwN_lt_p`, `L.Ind.iwN_lt_size` | 13 |
| `Arena.RecClassSpec.MjProg` | `L.Ind.iwH_truncM_some` (was `L.Ind.rec2IwH_trunc`) | `L.Ind.pos2_iwH_trunc` | 2 |
| `Arena.RecClassSpec.MjProg` | `L.Ind.iwN_truncM_some` (was `L.Ind.rec2IwN_trunc`) | `L.Ind.acTr`, `L.Ind.iwN_truncM_get`, `L.Ind.pos2_iwN_trunc` | 34 |
| `Arena.RecClassSpec.MnW` | `L.Ind.misW.arm1` | `L.Ind.misW_end` | 1 |
| `Arena.RecClassSpec.ReadProg` | `L.Ind.FA2.get` | `L.Ind.FA2.getElem` | 3 |
| `Arena.RecFireCore` | `L.Arena.mapM_some_mem` | `L.Ind.gfc_mapM_mem`, `L.Ind.grc_mapM_mem`, `L.Ind.pos_mapM_mem` | 6 |
| `Arena.RecGenSpec.CftW` | `L.Ind.decCV_sliceR` | `L.Arena.decCV_sliceW` | 3 |
| `Arena.RecGenSpec.Rec3TmdWDecB` | `L.Arena.Sim.rsim` (was `L.Ind.rec3Sim_rsim`) | `L.Arena.Sim.rsim` | 4 |
| `Arena.RecGenSpec.Set64` | `L.Ind.iwTop_set_iw` | `L.Ind.cnsTop_set` | 6 |
| `Arena.Refine` | `L.Arena.AM.run_of_ok` | `L.Arena.pr_run_of_ok`, `L.Ind.partsRunOfOk` | 6 |
| `Arena.Rom` | `L.Arena.ArenaD.frameHi` (was `L.Rom.ArenaD.frameHi`) | `L.Arena.ArenaD.frame64` | 6 |
| `Arena.Rom` | `L.Rom.top_set64_ne` | `L.Rom.top_set64_ctl` | 1 |
| `Arena.RomItems` | `L.Rom.run_bind_of` | `L.Rom.irp_run_bind` | 4 |
| `Arena.SimLib` | `L.Arena.of_K` | `L.Ind.ipK_inv1` | 10 |
| `Arena.StoreRel` | `L.Arena.Tbl.push_nodes` | `L.Arena.Tbl.nodes_push'` | 2 |
| `Arena.StoreRel` | `L.Arena.rdW_set64` | `L.Arena.rdW_set64E`, `L.Arena.rdW_set64L` | 28 |
| `Arena.StripTeleSpec` | `L.Ind.eViewW_lam` (was `L.Ind.eViewW_lamS`) | `L.Arena.eViewW_lam` | 1 |
| `Arena.StubIndRefine` | `L.Stubs.rdW_of_get` | `L.Arena.irRdW0`, `L.Arena.strRdW` | 0 |
| `Arena.TwinStep` | `L.Arena.TwinOK.of_check` | `L.Arena.TwinOK.ofCheck` | 1 |
| `Arena.TwinStep` | `L.Arena.denoteL_of_viewR` | `L.Arena.denoteL_some` | 2 |
| `Arena.TwinStep` | `L.Arena.denoteN_of_viewW` | `L.Arena.denoteN_some`, `L.Front.Ind.denoteN_of_viewAt` | 2 |
| `Arena.TwinStep` | `L.Arena.denoteRules_memL` | `L.Arena.denoteRules_levels` | 2 |
| `Arena.Verdict` | `L.Arena.ErrClaim.congr_run` (was `L.Arena.ErrClaim.of_run_eqW`) | `L.Arena.ErrClaim.congr_run` | 0 |
| `Arena.Verdict` | `L.Arena.RefE.mono` | `L.Ind.RefE.weakenP` | 5 |
| `Arena.Verdict` | `L.Arena.fail_bindAM` | `L.Ind.cb_fail_bind` | 2 |
| `Arena.Verdict` | `L.Arena.ite_bindAM` | `L.Ind.installIteBind` | 1 |
| `Arena.View` | `L.Arena.decE_word` | `L.Ind.decE_word` | 0 |
| `Arena.View` | `L.Arena.except_ok_bind` | `L.Arena.exc_ok_bind`, `L.Arena.exc_ok_bind'`, `L.Arena.except_ok_bind'`, `L.Arena.pv_ok_bind`, `L.Ind.exb` | 175 |
| `Arena.View` | `L.Arena.idx_word_lt32` (was `L.Arena.word_lt`) | `L.Arena.nidx_word_lt32`, `L.Ind.dmWord_lt32`, `L.Ind.nidx_word_lt32` | 28 |
| `Arena.WhnfBase` | `L.Arena.StackGrew.trans` | `L.Arena.StackGrew.trans'` | 3 |
| `Arena.WhnfBase` | `L.Arena.StackKept.toGrew` | `L.Arena.StackKept.toGrew'` | 1 |
| `Arena.WhnfCoreProj` | `L.Arena.SpineR.of_spn` (was `L.Arena.SpineR.of_spn_core`) | `L.Arena.SpineR.of_spn`, `L.Arena.SpineR.of_spnP` | 16 |
| `Arena.WhnfCoreProj` | `L.Arena.decMode_verified` | `L.Arena.decMode_vc`, `L.Arena.mode_verified` | 2 |
| `Arena.WhnfCoreProj` | `L.Arena.getElem_rdW` (was `L.Arena.getElem_rdW'`) | `L.Ind.nd_getElem`, `L.Ind.getElem_toNat_rdW`, `L.Arena.getElem_toNat_rdW` | 1 |
| `Arena.WhnfCoreProj` | `L.Arena.viewLsLen_run` | `L.Arena.ip_viewLsLen_run` | 2 |
| `Arena.WhnfDeltaRefine` | `L.Arena.CoreS.of_const` | `L.Arena.CoreS.of_const'` | 3 |
| `Arena.WhnfDeltaRefine` | `L.Arena.StackKept.of_const_frame` | `L.Arena.StackKept.of_constF` | 3 |
| `Arena.WhnfDeltaRefine` | `L.Arena.ceinternW_hw` | `L.Arena.ceinternW_hw'`, `L.Ind.ceinternW_hw'` | 2 |
| `Arena.WhnfDeltaRefine` | `L.Arena.decBool_ite` (was `L.Arena.decBool_ite'`) | `L.Arena.decBool_ite` | 1 |
| `Arena.WhnfDeltaRefine` | `L.Arena.keeps_cpl_internConst` | `L.Arena.keeps_cpl_internConst'` | 3 |
| `Arena.WhnfDeltaRefine` | `L.Arena.rdW_off` | `L.Arena.rdW_off'` | 0 |
| `Arena.WhnfDeltaRefine` | `L.Arena.resH_ite` (was `L.Arena.ResH_ite`) | `L.Arena.resH_ite`, `L.Arena.resH_ite01` | 7 |
| `Arena.WhnfDeltaRefine2` | `L.Arena.LsStore.viewLen_eq_map` | `L.Arena.LsStore.viewLen_eq_map'` | 1 |
| `Arena.WhnfDeltaRefine2` | `L.Arena.whnf_viewLs_run` | `L.Arena.viewLs_run'` | 1 |
| `Arena.WhnfIotaRecRefine` | `L.Arena.ite_bind` (was `L.Arena.ite_bind'`) | `L.Ind.ite_bind'` | 1 |
| `Arena.WhnfIotaRecRefine` | `L.Arena.lvlsEqC_small` | `L.Ind.lvlsEqC_small` | 1 |
| `Arena.WhnfIotaRefine` | `L.Arena.decBool_false_of` (was `L.Arena.decBool_f_m2c`) | `L.Arena.decBool_eq_false`, `L.Arena.decBool_f`, `L.Arena.decBool_false_of` | 40 |
| `Arena.WhnfIotaRefine` | `L.Arena.decBool_true_of` (was `L.Arena.decBool_t_m2c`) | `L.Arena.decBool_eq_true`, `L.Arena.decBool_t`, `L.Arena.decBool_true_of` | 39 |
| `Arena.WhnfIotaRefine` | `L.Arena.decCI_ctorR` | `L.Arena.decCI_ctorF` | 3 |
| `Arena.WhnfIotaRefine` | `L.Arena.decRules_getR` | `L.Arena.decRules_get'`, `L.Ind.decRules_getR` | 2 |
| `Arena.WhnfIotaRefine` | `L.Arena.mapM_option_get` | `L.Arena.mapM_get` | 2 |
| `Arena.WhnfIotaRefine2` | `L.Arena.SpineR.nil_at` | `L.Arena.SpineR.empty`, `L.Ind.SpineR.empty'` | 12 |
| `Arena.WhnfIotaRefine3` | `L.Arena.mkProjW_hw` | `L.Ind.mkProjW_hw'` | 1 |
| `Arena.WhnfIotaRefine3` | `L.Arena.pjinternW_hw` | `L.Ind.pjinternW_hw'` | 1 |
| `Arena.WhnfIotaRefine6` | `L.Arena.viewConstName_f` | `L.Arena.pr_viewConstName` | 1 |
| `Arena.WhnfSpine` | `L.Arena.getAppArgs_refines` | `L.Arena.getAppArgs_spec'` | 1 |
| `Checker.HoistDecode` | `L.Checker.hd?_some` | `L.Checker.hix_hd?_some` | 1 |
| `Checker.HoistDecode` | `L.Checker.rdW_of` | `L.Arena.rdW_of_get`, `L.Ind.rdW_of_get'` | 2 |
| `Checker.HoistIndexRef` | `L.Checker.rdW_dw` (was `L.Checker.hix_rd_dw`) | `L.Checker.rdW_dw` | 4 |
| `Checker.HoistIndexRef` | `L.Checker.rdW_dw0` (was `L.Checker.hix_rd_dw0`) | `L.Checker.rdW_dw0` | 1 |
| `Checker.HoistOrderRef3` | `L.Checker.iteF` | `L.Checker.ite_f` | 10 |
| `Checker.HoistOrderRef3` | `L.Checker.iteT` | `L.Checker.ite_t` | 3 |
| `Checker.HoistOrderRef3` | `L.Checker.tgW_some_ne` | `L.Checker.tgW_ne_zero` | 2 |
| `Checker.ParDriverL` | `L.Checker.checkerProg_flushProg` | `L.Checker.checkerProg_flushProg'` | 2 |
| `Compiler.BcePost` | `L.Compiler.setLocs_loc_out` | `L.Compiler.St.setLocs_loc_not_mem` | 2 |
| `Compiler.BcePost` | `L.Compiler.setLocs_mem` | `L.Compiler.St.setLocs_mem'` | 2 |
| `Compiler.InlineCorrect` | `L.Compiler.Inl.st32_run` (was `L.Compiler.Inl.st32_run'`) | `L.Checker.st32_run` | 3 |
| `Compiler.InlineCorrect` | `L.Compiler.Inl.st64_run` (was `L.Compiler.Inl.st64_run'`) | `L.Checker.st64_run` | 5 |
| `Compiler.InlineCorrect` | `L.Compiler.Inl.st8_run` (was `L.Compiler.Inl.st8_run'`) | `L.Checker.st8_run` | 3 |
| `Compiler.Main` | `L.Compiler.mem_of_lookup` | `L.Checker.mem_of_lookup`, `L.Checker.mem_of_lookupC` | 7 |
| `Compiler.Rel` | `L.Compiler.Layout.Ok.stack_arr` | `L.Compiler.Layout.Ok.notStack_of_arr'` | 1 |
| `Compiler.Rel` | `L.Compiler.Layout.Ok.tab_stack` | `L.Compiler.Layout.Ok.notStack_of_tab` | 5 |
| `Compiler.SimGen` | `L.Compiler.lookup_mem` | `L.Compiler.mem_of_lookup_alloc` | 2 |
| `Compiler.SimStore` | `L.Compiler.Mem.arr64_set64` | `L.Arena.arr64_set64_any` | 0 |
| `Front.ApplyExpr` | `L.Front.Keep.pcap` | `L.Rom.Keep.pcap` | 19 |
| `Front.FrontRunRef` | `L.Front.callE_of_run_err` | `L.Checker.callE_of_run_err` | 2 |
| `Front.IndApplyRefine2` | `L.Front.Ind.wd_eq` | `L.Front.Ind.rdW_wd` | 1 |
| `Front.IndFieldsLink2` | `L.Front.Ind.ctF_stab` | `L.Front.Ind.ctStab` | 1 |
| `Front.IndFieldsLink2` | `L.Front.Ind.recF_stab` | `L.Front.Ind.recStab` | 1 |
| `Front.IndFieldsLink2` | `L.Front.Ind.tyF_stab` | `L.Front.Ind.tyStab` | 1 |
| `Front.IndInstallRefine2` | `L.Front.Ind.wd_set_ne` | `L.Front.Ind.wd_set64_other` | 1 |
| `Front.NatDecLink` | `L.Front.rdW_ctl_top` | `L.Arena.rdW_ctl_top'` | 5 |
| `Front.UnescapeLink` | `ConAgua.Front.UnescapeLink.tag_sub_base` | `L.Arena.tag_sub_base'` | 1 |
| `L.Arrays` | `L.tierA_ne_tierA` | `L.Arena.tierA_ne` | 35 |
| `L.Arrays` | `L.tierA_one` (was `L.tierA_one_eq`) | `L.Arena.tierA_one`, `L.Arena.tierA_one'` | 15 |
| `L.Arrays` | `L.tierA_zero` | `L.Arena.tierA_zero`, `L.Arena.tierA_zero'` | 22 |
| `L.LocNF` | `L.Locals.init_nil` (was `L.LocNF.init_nil`) | `L.Locals.init_nil` | 26 |
| `L.LocNF` | `L.St.setG_loc` (was `L.LocNF.loc_setG`) | `L.St.setG_loc` | 0 |
| `L.LocNF` | `L.St.setLoc_mem` (was `L.LocNF.mem_setLoc`) | `L.St.setLoc_mem` | 154 |
| `L.LocNF` | `L.St.setLocs_mem` (was `L.LocNF.mem_setLocs`) | `L.Compiler.Inl.St.setLocs_mem`, `L.Rom.St.setLocs_mem`, `L.Scan.St.setLocs_mem`, `L.St.setLocs_mem`, `L.St.setLocs_mem'` | 36 |
| `L.Logic` | `L.except_error_bind` (new) | `L.Arena.except_bind_error`, `L.Checker.error_bind'` | 9 |
| `L.Logic` | `L.except_error_map` (new) | `L.Arena.except_map_error`, `L.Checker.error_map'` | 1 |
| `L.Logic` | `L.run_throw` (new) | `L.Arena.run_throw_M`, `L.Checker.run_throw'` | 10 |
| `L.Records` | `L.Mem.arr8_set8_ne` (new) | `L.Mem.arr8_set8_ne`, `L.Rom.arr8_set8_ne` | 2 |
| `L.Records` | `L.Mem.size64_set64` | `L.Arena.arr64_size_set64`, `L.Arena.size_set64`, `L.Arena.size_set64L`, `L.Compiler.Mem.size_set64` | 195 |
| `Verdict.DefEqBaseE` | `L.Arena.ErrClaim.of_callE_zero` | `L.Arena.ErrClaim.of_callE_zeroW` | 0 |

## 4. `finish [erec_grind]`

Lane dedup found that `finish [… , erec_grind]` does not close goals that `finish [… , erRd]`
closes, while `grind [erec_grind]` does. The reason: `finish` is a step inside a grind goal that
`sym`, `grind … =>` or `vcgen … with` set up, and it elaborates its list incrementally
(`Lean.Elab.Tactic.Grind.withParams`, `elabGrindParams (incremental := true)`). Named lemmas and
definitions go to `params.extra` and are activated in the running goal (`Grind.assertExtra`); an
attribute set's name is only pushed onto `params.extensions`, and nothing reads that list any
more, because the goal's E-matching theorems were copied from the extensions when the goal was
made (`mkGoalCore`). So `finish [S]` is a silent no-op for every set (`erec_grind`, `arena_grind`,
`lang_grind`). `vcgen … with finish [S]` is the same: `vcgen` starts its grind goal with
`Grind.mkDefaultParams` (`Lean/Elab/Tactic/VCGen/Frontend.lean`). Checked on a three-line
example (a set `my_grind` holding `f_eq`): `grind [my_grind]`, `grind [my_grind] => finish` and
`grind => finish [f_eq]` close `f n = n + 1`, `grind => finish [my_grind]` does not.

Corrected: `syncvocab.md` (§4's "named by the proofs …" and the Follow-up's `abbrev → def` note),
the docstrings of `ErecVocab.lean` and `L/GrindAttr.lean` (which recommended `finish
[erec_grind]` and `vcgen … with finish [lang_grind]`), and `scripts/sync-rules/vocab_attr.py`:
it added `arena_grind` to every `finish` list and gave a bare `finish` the list `[arena_grind]`
(no effect), and `erec_grind` likewise in `sets+`. Now the sets go only into `grind`/`sym` lists
(and a bare `sym =>` gets one), and `sets+` adds to `finish` lists (and a bare `finish`) the
declaration `erec_grind` holds, `erRd` (`FINISH_PLUS`). No proof in the tree used a set in a
`finish` list.

## 5. Left, and why

| group | why it stays |
|---|---|
| `L.Arena.KM.ConRon.Arena.CoreFnsA.{whnf, whnfCore, infer, inferIO, defeq, defeqE}` / the `RecSMono` fields; `KM.ConRon.Arena.fail` / `SMono.fail` | `smono_derive` (KnotMonoBase) finds the `KM.<f>` lemmas by name |
| `SMono.get` / `SMono.monadStateGet`, `SMono.getThe` / `SMono.monadStateOfGet` | the table `smonoLemma?` names one lemma per instance path |
| `KnotAllProg.constTy` / `constTyAt_refines`, `KnotAllProg.iota` / `iotaRecAt_refines`, `arenaD_init` / `estoreEmpty_refines`, `scanHints_eq_hintsN` / `scanHints_link`, `scanBinderInfo_eq_binderInfoN` / `scanBinderInfo_link` | the second is the census wrapper (`@[refines]`/`@[refines_part]`, in KnotTagged, InitLink, RecordsLink, where `link_val` names it) of the first |
| `romNameW_top` / `romNameW_topK`, and the same for `romLevelW`, `romLevelsW`, `romLvlsW` | the implicit-argument wrapper of the induction lemma (stated with `∀ n`) |
| `dbrs_specP` / `dbrs_spec` | `l_model` output (the program explicit) and its wrapper with the program implicit |
| `checkerFile_threads_accept` / `threadsRun_twinAcceptsPooled` | final theorems (EndToEnd, ThreadsFinal) keep their names |
| the reducible-unfolding groups whose conclusions differ: `wadd_toNat` and `toNat_hdr` (`i.toUInt64` against `UInt64.ofNat k`), `toUInt64_toNat` / `ofNat_toNat`, `tier1_arr` / `TieredArray.t0_arr`, `installIwH` / `truncH` (`H x` against `x.toNat < 2^32`), `invoke_run_loc` / `invoke_run_loc'` (a `match` against projections), `DerR.lvl` / `DerR.congrSt` (`autoParam` premises) | `rw` and `simp` see the spelled form, so one does not replace the other at its uses; the groups that differ only in a premise (`≠` against `¬ … = …`, `Word` against `UInt64`, `ArrId` against `Nat`) were folded |
| `L.Arena.coreWalkFuel_word` in `FuelConsts` | the census tag of `coreWalkFuel` (`@[refines]`); the scan missed it (the same name in `PropReadRefine4`, a deleted copy of `coreWalkFuel_toNat`, hid it) |

Not attempted: duplicates that differ in more than binder names, binder kinds and reducible
unfolding (argument order, a hypothesis more or less, a stronger conclusion), and duplicate
definitions (the scan looks at theorems only).
