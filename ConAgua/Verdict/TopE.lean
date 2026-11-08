module

import ConAgua.Verdict.DeclTopE
import ConAgua.Verdict.KnotAllE
import ConAgua.Verdict.CheckBE
import ConAgua.Verdict.FrontStageE
public import ConAgua.Final.ThreadsVerdict
meta import ConAgua.Verdict.DeclTopE
meta import ConAgua.Verdict.KnotAllE
meta import ConAgua.Verdict.CheckBE
meta import ConAgua.Verdict.FrontStageE
meta import ConAgua.Final.ThreadsVerdict
import ConAgua.Arena.DeclNatSubAll
import ConAgua.Arena.StrLitSup
import ConAgua.Checker.IndArm
import ConAgua.Checker.LoopProg
import ConAgua.Checker.LoopProgTac
import ConAgua.Checker.LoopStage
import ConAgua.Checker.RomProgInit
import ConAgua.Checker.TwinShapeQuot
public import ConAgua.Arena.CheckerT
public import ConAgua.Checker.PipeFinal
import all ConAgua.Arena.Abs1
import all ConAgua.Arena.AppStore
import all ConAgua.Arena.ArRange
import all ConAgua.Arena.ArRangeSpec
import all ConAgua.Arena.BVarStore
import all ConAgua.Arena.BvarB
import all ConAgua.Arena.CheckerL
import all ConAgua.Arena.ConsLib
import all ConAgua.Arena.ConsPresize
import all ConAgua.Arena.ConstStore
import all ConAgua.Arena.ConstsResolveF
import all ConAgua.Arena.CoreCaches
import all ConAgua.Arena.CoreLevels
import all ConAgua.Arena.CoreWalks
import all ConAgua.Arena.DeclAndPin
import all ConAgua.Arena.DeclApd
import all ConAgua.Arena.DeclArms
import all ConAgua.Arena.DeclArmsCanon
import all ConAgua.Arena.DeclArmsNat
import all ConAgua.Arena.DeclStep
import all ConAgua.Arena.DefEq
import all ConAgua.Arena.Env
import all ConAgua.Arena.ExprMk
import all ConAgua.Arena.FVarRange
import all ConAgua.Arena.FVarStore
import all ConAgua.Arena.ForallStore
import all ConAgua.Arena.Freeze
import all ConAgua.Arena.HasFvar
import all ConAgua.Arena.ImaxStore
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.IndInstall
import all ConAgua.Arena.IndParts
import all ConAgua.Arena.IndPos
import all ConAgua.Arena.IndPos2
import all ConAgua.Arena.IndRealIpo
import all ConAgua.Arena.IndSum
import all ConAgua.Arena.Infer
import all ConAgua.Arena.InferFieldSort
import all ConAgua.Arena.Inst1
import all ConAgua.Arena.Inst1Spec
import all ConAgua.Arena.InstLP
import all ConAgua.Arena.InstList
import all ConAgua.Arena.InstListSpec
import all ConAgua.Arena.Knot
import all ConAgua.Arena.LamStore
import all ConAgua.Arena.LetStore
import all ConAgua.Arena.LevelApd
import all ConAgua.Arena.LevelEquiv
import all ConAgua.Arena.LevelHeap
import all ConAgua.Arena.LevelIntern
import all ConAgua.Arena.LevelLeq
import all ConAgua.Arena.LevelSimp
import all ConAgua.Arena.LevelStore
import all ConAgua.Arena.LevelSubst
import all ConAgua.Arena.LevelSubstL
import all ConAgua.Arena.LevelSubstLP
import all ConAgua.Arena.LevelZero
import all ConAgua.Arena.LiftL
import all ConAgua.Arena.LsStore
import all ConAgua.Arena.MaxStore
import all ConAgua.Arena.MemoLib
import all ConAgua.Arena.NAnonStore
import all ConAgua.Arena.NNumStore
import all ConAgua.Arena.NStrStore
import all ConAgua.Arena.NatAdd
import all ConAgua.Arena.NatArms
import all ConAgua.Arena.NatBits
import all ConAgua.Arena.NatCmp
import all ConAgua.Arena.NatDiv
import all ConAgua.Arena.NatGcd
import all ConAgua.Arena.NatMul
import all ConAgua.Arena.NatPow
import all ConAgua.Arena.NatShl
import all ConAgua.Arena.NatShr
import all ConAgua.Arena.NatSub
import all ConAgua.Arena.ParamStore
import all ConAgua.Arena.Pins
import all ConAgua.Arena.Prelude
import all ConAgua.Arena.ProjStore
import all ConAgua.Arena.PropRead
import all ConAgua.Arena.RecCheck
import all ConAgua.Arena.RecCheckSpec.CnfW
import all ConAgua.Arena.RecClass
import all ConAgua.Arena.RecGen
import all ConAgua.Arena.RecGenSpec.DecB
import all ConAgua.Arena.Refine
import all ConAgua.Arena.Rom
import all ConAgua.Arena.RomCI
import all ConAgua.Arena.RomExpr
import all ConAgua.Arena.RomItems
import all ConAgua.Arena.RomLevel
import all ConAgua.Arena.RomLevels
import all ConAgua.Arena.RomPins
import all ConAgua.Arena.Scratch
import all ConAgua.Arena.SortStore
import all ConAgua.Arena.Store
import all ConAgua.Arena.StrLit
import all ConAgua.Arena.StripTele
import all ConAgua.Arena.StubInd
import all ConAgua.Arena.StubNames
import all ConAgua.Arena.TeleLift
import all ConAgua.Arena.Walk
import all ConAgua.Arena.WalkLeaves
import all ConAgua.Arena.WalkLift
import all ConAgua.Arena.WalkScope
import all ConAgua.Arena.WhnfCore
import all ConAgua.Arena.WhnfCoreApp
import all ConAgua.Arena.WhnfDelta
import all ConAgua.Arena.WhnfEntry
import all ConAgua.Arena.WhnfIota
import all ConAgua.Arena.WhnfIotaRec
import all ConAgua.Arena.WhnfM2C
import all ConAgua.Arena.WhnfProj
import all ConAgua.Arena.WhnfSpineArgs
import all ConAgua.Arena.WhnfSpineRefine
import all ConAgua.Arena.ZeroStore
import all ConAgua.Checker.Entry
import all ConAgua.Checker.Hoist
import all ConAgua.Checker.Prelude
import all ConAgua.Checker.Presize
import all ConAgua.Front.Apply
import all ConAgua.Front.ApplyDecl
import all ConAgua.Front.ApplyExpr
import all ConAgua.Front.Driver
import all ConAgua.Front.Fields
import all ConAgua.Front.FieldsDecl
import all ConAgua.Front.IdTable
import all ConAgua.Front.IndApply
import all ConAgua.Front.IndFields
import all ConAgua.Front.Line
import all ConAgua.Front.LineRec
import all ConAgua.Front.NatDec
import all ConAgua.Front.Unescape
import all ConAgua.L.Examples
import all ConAgua.Rom.CIRead
import all ConAgua.Rom.PinRead
import all ConAgua.Rom.PinReadSpec
import all ConAgua.Scan.Key
import all ConAgua.Scan.Leaves
import all ConAgua.Scan.Line
import all ConAgua.Scan.Lit
import all ConAgua.Scan.Member
import all ConAgua.Scan.Records
import all ConAgua.Scan.Str
import all ConAgua.Scan.Utf8
import all ConAgua.Scan.Values

@[expose] public section
/-!
# The verdict claims from the inductive arm's (lane `verdicts-b`, helper `sg`)

The top-level glue: the sequential driver's verdict claims (`SeqVerdicts checkerProg`) and the
threaded harness's (`ThreadVerdicts`) from one hypothesis, the inductive arm's error claim at the
programs phase A runs (`IndArmVerdict`, the shape `indArmSpec_checker` has on the ok side).

* Entry 1 (`entry1Verdict_of`): the prelude and the frontend by `checker_preludeStageE`,
  `checker_frontStageE`; the fold by `foldStageE_checker`, the error half of
  `foldStage_checker`: the run at `checkerProg` is the run at the substituted program
  (`invoke_subPB`, errors included), where `fold_ref`'s error half at the loop's start
  (`loop_start`, its `IstgG` by `istgG_of`) gives phase A's failure, and `TwinVerdict.fold` the
  pipeline's.
* Entry 2 (`entry2Verdict_of`) and the threads' `CPVerdict`: `check_pending`'s `CpG` at the
  substituted program (`cpG_proved`; no inductive arm in phase B).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Checker

open L L.Arena L.Front L.Rom L.Compiler L.Ind ConAgua.Final

/-- **The inductive arm's error claim at the programs phase A runs** (the remaining hypothesis):
`check_ind_decl`'s claim (`IndArmSpecE`) at the substituted program of any pin-data buffer the
loader accepts, at any injective name decoder with `Quot`'s name. -/
def IndArmVerdict : Prop :=
  ∀ (bs : List UInt8), RomOK bs → bs = romData ++ bs.drop romData.length →
    ∀ (dn : NIdx → Option ConLeche.Name), DnInj dn → QuotDn dn →
      IndArmSpecE (Prog.subPB bs checkerProg) dn

theorem checkerProg_uceLookupsPB (bs : List UInt8) : UceLookups (Prog.subPB bs checkerProg) := by
  prog_bundle []

/-- **Phase A's fold from `R7`, error half** (`foldStage_checker`'s): a failing
`install_fold_go(0, cnt, 0)` with class `≠ 0` is the twin pipeline's failure. -/
theorem foldStageE_checker (hia : IndArmVerdict) (b pb : ByteArray) (sz : TieredArray → Nat)
    (hin : InputsOK b pb sz) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (cnt : Word) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "install_fold_go" [0, cnt, 0]
    ⦃fun _ s' => LocEq s' s₀; fun e => Q7 b (checkerRels b pb sz) s₀.mem →
      (∀ h : 0 < (s₀.mem.arr64 L.Front.DECL).size, cnt = (s₀.mem.arr64 L.Front.DECL)[0]) →
      e.cls ≠ 0 → TwinVerdict [b] e.cls⦄ := by
  apply M.triple_of_run'
  · intro s r s' hs hrun
    exact M.of_run (P := fun s => s = s₀) (Q := fun _ s => LocEq s s₀) hs hrun
      (L.invoke_loc checkerProg (exec checkerProg n) "install_fold_go" [0, cnt, 0] s₀)
  intro s e hs hrun hQ hcnt hk
  subst hs
  obtain ⟨sA, pre, sB, rc, sC, ds, sD, pins, ipins, sE, hA, hB, hC, hD, hE, h7⟩ := hQ
  have hpx : TwinPrefix b sA pre sB rc sC ds sD pins ipins sE := ⟨hA, hB, hC, hD, hE⟩
  have hr : RomOK pb.data.toList := by simpa [RomOK] using hin.2.2.1
  have hT := twinFold_of_prefix hpx
  have hcore := core_of_R7 hpx h7
  have hcaps := CapsOK.keep h7.since.keep h7.since.caps
  have hdn : L.Ind.DnInj (dnOf sE.store) := dnOf_inj hT.stateOK.wf
  have hQd : QuotDn (dnOf sE.store) := by
    obtain ⟨k, hk, hd⟩ := prefix_quotU hpx
    exact ⟨k, by simp [dnOf, hk, hd]⟩
  have hLC := checkerProg_loopCalleesPB pb.data.toList hr h7.since.pbpre (dnOf sE.store) hdn
    (indArmSpec_checker _ hr h7.since.pbpre _ hdn) hQd
  have hP := checkerProg_loopTopPB pb.data.toList
  have hpb : s.mem.arr8 PB = pb.data.toList.toArray := by
    rw [h7.since.keep.arr8]; exact loadMem_pb b pb sz
  have hD0 : 0 < (s.mem.arr64 DECL).size := by have := hcaps.2.2.1; simp only [DECL] at this ⊢; omega
  have hcnt' : cnt.toNat = ds.size := by
    rw [hcnt hD0]; have := h7.decls.count; simpa [hD0] using this
  -- the run at the substituted program, as a call
  have hrun' := (invoke_subPB (bs := pb.data.toList) checkerProg_noSt8PB n "install_fold_go"
    [0, cnt, 0] hpb).trans hrun
  have hcall : callE (Prog.subPB pb.data.toList checkerProg) n "install_fold_go" [0, cnt, 0] s.mem =
      .error e :=
    M.of_run_err (P := fun x => x = s) rfl hrun' (callE_spec _ n _ _ s)
  -- the loop's start
  obtain ⟨hR, hM, hc, hIM⟩ := loop_start (pins := ipins) h7.arena hcore h7.pinsFull h7.decls
    h7.pinSets h7.iw (loopZero_of_since h7.since) h7.pin0
    (by have := hcaps.1 EREC (by decide); omega) (by have := hcaps.1 SPN (by decide); omega)
    (by have := hcaps.1 BSTK (by decide); omega) h7.mode
  have hsz : ds.size < 2 ^ 63 := by have := hR.decls.dsize; have := hR.decls.room; omega
  -- the leaves' claims at the substituted program
  have hnv := checkerProg_nvPB pb.data.toList
  have hcE := checkerProg_coreStubsEPB pb.data.toList
  have hkp : CrKeep (Prog.subPB pb.data.toList checkerProg) := ⟨hLC.indMemo, hLC.crf⟩
  have hDG := divGateSpecE_of hLC.cd.dm hLC.knot hLC.leaf hLC.cd.dgClosed
    (substC0_of hLC.cd.natSub.toNatSubProg)
    (substCAll_of ⟨hLC.cd.natSub.toNatSubProg, hLC.cd.dm.lSubstConstAll⟩) hkp hcE hnv ipins
  have hG := istgG_of ipins (dnOf sE.store) ds _ hLC hcE (hia _ hr h7.since.pbpre _ hdn hQd) hDG hnv
    (checkerProg_uceLookupsPB _)
  have hF := RefC.run_err (installFoldGo_specE _ hP.pg n ⟨s.mem, Locals.init []⟩ 0 cnt 0)
    (fun _ h0 => ErrClaimV.of_cls0 h0) trivial hG
    ((fold_ref .verified ipins (dnOf sE.store) ds _ hP.pp hP.pn hP.ps hP.pi hP.pd hP.pg hP.px hsz
      hP.bracket hLC rfl (frontDecls_of_prefix hpx) (declsLpsDn_dnOf hT.pd hT.den) n hn).1
      s.mem sE 0 cnt 0 (mkIFEnv IEnv.empty) #[] (by simp) hcnt' hT hR hM hc hIM) hcall hk
  simp only [UInt64.toNat_zero, List.drop_zero] at hF
  exact TwinVerdict.fold hA hB hC hD hE hF

/-- **Entry 1's verdict claim** from the inductive arm's. -/
theorem entry1Verdict_of_ind (hia : IndArmVerdict) : Entry1Verdict checkerProg :=
  entry1Verdict_of ⟨checker_preludeStageE, checker_frontStageE,
    fun b pb sz hin n hn s₀ cnt => foldStageE_checker hia b pb sz hin n hn s₀ cnt⟩

/-- **What `check_pending`'s error arms assume, at the programs phase B runs**: proved, no
hypothesis. -/
theorem cpG_proved (bs : List UInt8) (hP : PhaseBProg (Prog.subPB bs checkerProg)) :
    CpG (Prog.subPB bs checkerProg) := by
  have hnv := checkerProg_nvPB bs
  have hU : UceProg (Prog.subPB bs checkerProg) :=
    ⟨checkerProg_uceLookupsPB bs, strLitStored_core _ hP.knot.knot.str⟩
  exact ⟨hnv, checkerProg_coreStubsEPB bs, ivgE_okT hP.cvg hP.apd hP.crk hnv hU⟩

/-- **`check_pending`'s error claim at the programs phase B runs** (`CPVerdict`). -/
theorem cpVerdict_proved : CPVerdict := fun bs dn _ _ _ _ hP pins ds fe pend =>
  checkPending_errT .verified pins dn ds _ fe pend hP rfl (cpG_proved bs hP)

/-- **The sequential driver's verdict claims** from the inductive arm's. -/
theorem seqVerdicts_of (hia : IndArmVerdict) : SeqVerdicts checkerProg :=
  ⟨entry1Verdict_of_ind hia, entry2Verdict_of cpG_proved⟩

/-- **The threaded harness's verdict claims** from the inductive arm's. -/
theorem threadVerdicts_of (hia : IndArmVerdict) : ThreadVerdicts :=
  ⟨entry1Verdict_of_ind hia, cpVerdict_proved⟩

end L.Checker
