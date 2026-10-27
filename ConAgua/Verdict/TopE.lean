import ConAgua.Verdict.DeclTopE
import ConAgua.Verdict.KnotAllE
import ConAgua.Verdict.DeclGatesE2
import ConAgua.Verdict.DeclPendE
import ConAgua.Verdict.CheckBE
import ConAgua.Verdict.FrontStageE
import ConAgua.Final.ThreadsVerdict
import ConAgua.Checker.NoVerdictTree

/-!
# The verdict claims from the inductive arm's (lane `verdicts-b`, helper `sg`)

The top-level glue: the sequential driver's verdict claims (`SeqVerdicts checkerProg`) and the
threaded harness's (`ThreadVerdicts`) from one hypothesis, the inductive arm's error claim at the
programs phase A runs (`IndArmVerdict`, the shape `indArmSpec_checker` has on the ok side).

* Entry 1 (`entry1Verdict_of`): the prelude and the frontend by `checker_preludeStageE`,
  `checker_frontStageE`; the fold by `foldStageE_checker`, the error half of
  `foldStage_checker`: the run at `checkerProg` is the run at the substituted program
  (`invoke_subPB`, errors included), where `installFoldGo_errTop` at the loop's start
  (`loop_start`) gives phase A's failure, and `TwinVerdict.fold` the pipeline's.
* Entry 2 (`entry2Verdict_of`) and the threads' `CPVerdict`: `checkPending_errT` at the
  substituted program (no inductive arm in phase B).
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
theorem foldStageE_checker (hia : IndArmVerdict) (b pb : ByteArray) (s8 s64 : List Nat)
    (hin : InputsOK b pb s64) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (cnt : Word) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "install_fold_go" [0, cnt, 0]
    ⦃fun _ s' => LocEq s' s₀; fun e => Q7 b (checkerRels b pb s8 s64) s₀.mem →
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
    rw [h7.since.keep.arr8]; exact loadMem_pb b pb s8 s64
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
    (by have := hcaps.1 145 (by decide); omega) h7.mode
  have hsz : ds.size < 2 ^ 63 := by have := hR.decls.dsize; have := hR.decls.room; omega
  -- the leaves' claims at the substituted program
  have hnv := checkerProg_nvPB pb.data.toList
  have hcE := checkerProg_coreStubsEPB pb.data.toList
  have hkp : CrKeep (Prog.subPB pb.data.toList checkerProg) := ⟨hLC.indMemo, hLC.crf⟩
  have hNG := natGateSpecE_of hLC.cd.natSub hLC.knot hLC.leaf hcE hnv hLC.cd.natGate hLC.cd.natCert
  have hDG := divGateSpecE_of hLC.cd.dm hLC.knot hLC.leaf hLC.cd.dgClosed
    (substC0_of hLC.cd.natSub.toNatSubProg)
    (substCAll_of ⟨hLC.cd.natSub.toNatSubProg, hLC.cd.dm.lSubstConstAll⟩) hkp hcE hnv ipins
  have hgo := (installFoldGo_errTop ipins (dnOf sE.store) ds _ hLC hcE
    (hia _ hr h7.since.pbpre _ hdn hQd) hNG hDG hnv (checkerProg_uceLookupsPB _)
    (frontDecls_of_prefix hpx) (declsLpsDn_dnOf hT.pd hT.den) hP.pp hP.pn hP.ps hP.pi hP.pd hP.pg
    hP.px hsz hP.bracket n hn).1
  have hF := hgo s.mem sE 0 cnt 0 (mkIFEnv IEnv.empty) #[] (by simp) hcnt' hT hR hM hc hIM e hcall hk
  simp only [UInt64.toNat_zero, List.drop_zero] at hF
  exact TwinVerdict.fold hA hB hC hD hE hF

/-- **Entry 1's verdict claim** from the inductive arm's. -/
theorem entry1Verdict_of_ind (hia : IndArmVerdict) : Entry1Verdict checkerProg :=
  entry1Verdict_of ⟨checker_preludeStageE, checker_frontStageE,
    fun b pb s8 s64 hin n hn s₀ cnt => foldStageE_checker hia b pb s8 s64 hin n hn s₀ cnt⟩

/-- **`check_pending`'s error claim at the programs phase B runs** (`CPVerdict`): proved, no
hypothesis. -/
theorem cpVerdict_proved : CPVerdict := by
  intro bs dn _hr _hpre _hdn _hQd hP pins ds fe pend
  have hnv := checkerProg_nvPB bs
  have hU : UceProg (Prog.subPB bs checkerProg) :=
    ⟨checkerProg_uceLookupsPB bs, strLitSupported_core _ hP.knot.knot.str⟩
  have hivE : IvgE (Prog.subPB bs checkerProg) := ivgE_okT hP.cvg hP.apd hP.crk hnv hU
  exact checkPending_errT .verified pins dn ds _ fe pend rfl hP (checkerProg_coreStubsEPB bs) hivE
    (fun _ _ _ _ h => callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) _ _ _ h)
    (fun _ _ _ _ h => callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) _ _ _ h)
    (fun _ _ _ _ h => callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) _ _ _ h)
    (fun _ _ _ _ h => callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) _ _ _ h)
    (fun _ _ _ _ h => callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) _ _ _ h)

/-- **The sequential driver's verdict claims** from the inductive arm's. -/
theorem seqVerdicts_of (hia : IndArmVerdict) : SeqVerdicts checkerProg :=
  ⟨entry1Verdict_of_ind hia, entry2Verdict_of cpVerdict_proved⟩

/-- **The threaded harness's verdict claims** from the inductive arm's. -/
theorem threadVerdicts_of (hia : IndArmVerdict) : ThreadVerdicts :=
  ⟨entry1Verdict_of_ind hia, cpVerdict_proved⟩

end L.Checker
