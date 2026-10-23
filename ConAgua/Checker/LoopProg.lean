import ConAgua.Checker.LoopProgTac
import ConAgua.Checker.LoopProgInd
import ConAgua.Checker.LoopDeclArm
import ConAgua.Checker.LoopDeclAgree
import ConAgua.Checker.IndCore
import ConAgua.Checker.CoreErec
import ConAgua.Checker.LeafAll
import ConAgua.Checker.LoopAll
import ConAgua.Checker.IndRealNames

/-!
# The declaration loop's program hypotheses at the checker's program (lane `loopt3`)

`installThenCheck_refines`' program hypotheses (`Arena/CheckerT.lean`) for `checkerProg`:
`LoopCallees dn checkerProg` (`checkerProg_loopCallees`), `BracketProg checkerProg`
(`checkerProg_bracket`) and the loop's own lookups. The bundles' lookups by `prog_bundle`
(`LoopProgTac.lean`: one indexed lookup per distinct function, ~800); the write sets and text
agreements from `LoopDecl.lean`, `LoopDeclAgree.lean`, `LoopDeclArm.lean`, `IndCore.lean`,
`CoreErec.lean`, `LeafAll.lean`, `LoopAll.lean`, `LoopProgInd.lean`; the two agreements
`KnotStageProg` asks beyond lookups (`natAgree`, `lvlText`) here.

Two facts are hypotheses, because they do not hold of `checkerProg` as the bundles state them:

* `RomRefs checkerProg` (the ROM readers refine the twin; `QuotProg.rom`, `RedProg.rom`,
  `DmProg7.lRom`): `checkerProg`'s readers read the buffer `PB` (`romU64PB`, …), and `StageR`
  says nothing of `PB`. `romRefs_of` proves it for a program whose readers read the constant ROM
  (`RomReady`), as `checkerProg.subPB bs` does for `bs` the buffer `pb_check` accepted (the ROM
  stages' route, `Rom/Stage.lean`, `triple_subPB`).
* `checkerProg.lookup "inst1" = some instEntry` (`CoreWalkProg.i1`, `Arena/CoreWalks.lean`):
  `checkerProg` binds `inst1` to `inst1A` (`Checker/Entry.lean`, a call of `inst_entry`), not to
  `inst_entry`'s body. False as stated: `CoreWalkProg.i1` should name `inst1A` (and
  `CoreWalkProg.inst1OK` go through the call).
-/

namespace L.Checker

open L L.Arena L.Compiler

set_option maxRecDepth 100000

theorem checkerProg_natArm : ProgHas checkerProg natArmProg' := by prog_bundle []

/-- `WhnfDeltaProg'.natAgree` at `checkerProg`. -/
theorem checkerProg_natAgree : ∀ f ∈ natFns, checkerProg.lookup f = natArmProg'.lookup f :=
  ProgHas.agreeNames checkerProg_natArm

theorem lvlFns_cvg : ∀ f ∈ lvlFns, f ∈ cvgFns ∧ f ∉ openFns := by decide +kernel

/-- `StrLitProg`'s `lvlText` at `checkerProg`. -/
theorem checkerProg_lvlText : ∀ f ∈ lvlFns, checkerProg.lookup f = cvgProg.lookup f :=
  fun f hf => checkerProg_cvgAgree f (lvlFns_cvg f hf).1 (lvlFns_cvg f hf).2

/-- **The declaration loop's callees at the checker's program**, given the ROM readers'
refinement and `CoreWalkProg`'s `inst1` binding (see the module doc: neither holds of
`checkerProg` as stated). -/
theorem checkerProg_loopCallees (hrom : L.Rom.RomRefs checkerProg)
    (hi1 : checkerProg.lookup "inst1" = some instEntry) :
    ∀ dn, L.Ind.DnInj dn → IndArmSpec checkerProg dn → QuotDn dn → LoopCallees dn checkerProg := by
  intro dn hdn harm hq
  prog_bundle [checkerProg_cvg, checkerProg_iv, checkerProg_arm, checkerProg_natGateIn,
    checkerProg_dgIn, checkerProg_leafClosed, checkerProg_loopClosed, checkerProg_coreStage,
    checkerProg_coreErec, checkerProg_indIn, checkerProg_natAgree, checkerProg_lvlText,
    checkerProg_na, checkerProg_nr, checkerProg_il, checkerProg_pt, checkerProg_ipf, hdn, harm,
    hq, hi1, hrom]

theorem checkerProg_bracket : BracketProg checkerProg := by prog_bundle []

/-! The loop's own lookups. -/

theorem checkerProg_pendPush : checkerProg.lookup "pend_push" = some pendPushL := by chk_lk
theorem checkerProg_isNone : checkerProg.lookup "is_none" = some isNoneL := by chk_lk
theorem checkerProg_isSome : checkerProg.lookup "is_some" = some isSomeL := by chk_lk
theorem checkerProg_installStep : checkerProg.lookup "install_step" = some installStepL := by
  chk_lk
theorem checkerProg_installDeclStep :
    checkerProg.lookup "install_decl_step" = some installDeclStepL := by chk_lk
theorem checkerProg_installFoldGo :
    checkerProg.lookup "install_fold_go" = some installFoldGoL := by chk_lk
theorem checkerProg_installFoldNext :
    checkerProg.lookup "install_fold_next" = some installFoldNextL := by chk_lk
theorem checkerProg_checkPending : checkerProg.lookup "check_pending" = some checkPendingL := by
  chk_lk
theorem checkerProg_checkPendingGo :
    checkerProg.lookup "check_pending_go" = some checkPendingGoL := by chk_lk
theorem checkerProg_checkPendingNext :
    checkerProg.lookup "check_pending_next" = some checkPendingNextL := by chk_lk
theorem checkerProg_installThenCheck :
    checkerProg.lookup "install_then_check" = some installThenCheckL := by chk_lk

open Std.WP in
open scoped Lean.Order in
/-- **`installThenCheck_refines` at the checker's program**: what remains are the loop's start
facts, the inductive arm's contract, `Quot`'s handle and the two hypotheses of
`checkerProg_loopCallees`. -/
theorem checkerProg_installThenCheck_refines (hrom : L.Rom.RomRefs checkerProg)
    (hi1 : checkerProg.lookup "inst1" = some instEntry) (mode : ConLeche.CheckMode)
    (pins : List ConRon.Arena.INatOpPinSet) (dn : ConRon.Arena.NIdx → Option ConLeche.Name)
    (ds : Array ConRon.Arena.IDeclaration) (hm : mode = .verified) (hdn : L.Ind.DnInj dn)
    (harm : IndArmSpec checkerProg dn) (hq : QuotDn dn) (hFD : FrontDecls ds) (n : Nat)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : ConRon.Arena.AState)
    (hT : TwinFold pins ds (ConRon.Arena.mkIFEnv ConRon.Arena.IEnv.empty) #[] a₀)
    (hR : LoopR pins dn s₀.mem a₀ 0 (ConRon.Arena.mkIFEnv ConRon.Arena.IEnv.empty) #[] ds)
    (hM : LoopMem dn s₀.mem a₀) (hc : CoreMemos s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "install_then_check" []
    ⦃fun _ s' => LocEq s' s₀ ∧ ∃ (k : Nat) (fe : ConRon.Arena.IFEnv)
      (pend : Array ConRon.Arena.PendingCheck) (a' s'' : ConRon.Arena.AState),
      ConRon.Arena.installFold mode pins (0, ConRon.Arena.mkIFEnv ConRon.Arena.IEnv.empty, #[])
        ds.toList a₀ = .ok (.ok (k, fe, pend), a') ∧
      ConRon.Arena.checkPendingList mode fe pend.toList a'.worker = .ok (.ok (), s''); ⊤⦄ :=
  installThenCheck_refines mode pins dn ds checkerProg hm checkerProg_bracket
    (checkerProg_loopCallees hrom hi1 dn hdn harm hq) hFD checkerProg_pendPush checkerProg_isNone
    checkerProg_isSome checkerProg_installStep checkerProg_installDeclStep
    checkerProg_installFoldGo checkerProg_installFoldNext checkerProg_checkPending
    checkerProg_checkPendingGo checkerProg_checkPendingNext checkerProg_installThenCheck n hn s₀
    a₀ hT hR hM hc

end L.Checker
