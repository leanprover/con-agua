module

public import ConAgua.Verdict.ThreadsE
public import ConAgua.Verdict.CmpVModes
import ConAgua.Verdict.IndArmTopE
import ConAgua.Checker.CmpSJobs
import ConAgua.Checker.ParThreadCall
import ConAgua.Checker.ParDriverTwin
import ConAgua.Checker.ParDriverL
import ConAgua.Checker.CmpHdrKeep
import ConAgua.Checker.CheckARun
import ConAgua.Checker.AsmFinal
import ConAgua.Arena.FreezeFresh
import ConAgua.Arena.FreezeTrunc
import ConAgua.Arena.IWFrame
import ConAgua.Checker.JobsStart
import ConAgua.Final.CmpChain
import ConAgua.Checker.RomProgInit
import ConAgua.Verdict.DeclTopE
import ConAgua.Arena.IndT.CheckIndDecl
import ConAgua.Checker.IndArm
import ConAgua.Checker.IotaArm
import ConAgua.Checker.ArmsT
import ConAgua.Checker.LoopProg
import ConAgua.Verdict.KnotAllE
import ConAgua.Checker.DefnArmT
import ConAgua.Checker.BlockRefsProg

@[expose] public section

/-!
# The solution's jobs of the compared run fail only where the twin's do (lane compare2, helper
compare2-verdict)

The error half of `sjobs_chainO` (`Checker/CmpSJobs.lean`): the solution's jobs run one after the
other on one worker region, each on the buffer as the job before left it; when job `j` fails with
a class other than `0` after the jobs below it accepted, the twin's job list over every solution
record fails with that class from the index state's worker (`sjobs_failO`, the walk of
`threads_twinVerdictPooled` over the changing buffers). `cmpV_sjob`: the same from the driver's
runs (`CmpErr`'s third arm), as `TwinCompareVerdict.jobsS`.
-/

open ConRon.Arena ConAgua.Final

namespace L.Checker

open L L.Arena L.Rom L.Compiler ConRon.Bridge

local notation "VM" => ConLeche.CheckMode.verified

/-- **The jobs' error claims at the checker for any record decoder** that is injective and gives
`Quot`'s universe name a handle (`jobG_checker` without the stages). -/
theorem jobG_ofDn {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration}
    {ipins : List INatOpPinSet} (hinj : L.Ind.DnInj dn) (hq : L.Ind.QuotDn dn) (pb : ByteArray)
    (hpb : pb.size < 2 ^ 63) (hpre : PbPre pb) :
    JobG ipins dn ds (Prog.subPB pb.data.toList checkerProg) := by
  have hr : RomOK pb.data.toList := by simpa [RomOK] using hpb
  have H := indArmProgs_checker _ hr hpre
  have hnv := checkerProg_nvPB pb.data.toList
  have hU : UceProg (Prog.subPB pb.data.toList checkerProg) :=
    ⟨checkerProg_uceLookupsPB _⟩
  have hG : VerdictCtxU (Prog.subPB pb.data.toList checkerProg) :=
    ⟨⟨hnv, checkerProg_coreStubsEPB _⟩, hU⟩
  exact jobG_of _ _ _ _
    (armsE_of _ _ _ _ (checkerProg_axArmPB _ hr hpre) (checkerProg_defnArmPB _ hr hpre)
      (checkerProg_thmArmPB _ hr hpre) (checkerProg_opqArmPB _ hr hpre) (checkerProg_quotArmPB _)
      (checkerProg_knotStagePB _) (checkerProg_leafClosedPB _) (checkerProg_apdPB _)
      (checkerProg_crKeepPB _) (checkerProg_crfPB _) (checkerProg_ccvSimsPB _ _)
      (checkerProg_quotSimsPB _ hr hpre hq) hinj hG)
    (indArmSpecE_checker _ hr hpre (cbRefs_checker _ hr hpre (snoSim_checker _)) _ hinj) hnv

/-- **The jobs' error claims at the checker for any twin prefix** (`jobG_checker` at `StagesOut`). -/
theorem jobG_ofOut {sE : AState} {ds : Array IDeclaration} {ipins : List INatOpPinSet}
    {pins : List ConLeche.NatOpPinSet} (ho : StagesOut sE ds ipins pins) (pb : ByteArray)
    (hpb : pb.size < 2 ^ 63) (hpre : PbPre pb) :
    JobG ipins (dnOf sE.store) ds (Prog.subPB pb.data.toList checkerProg) :=
  jobG_ofDn ho.dnInj ho.quotDn pb hpb hpre

/-- A job list failing on a prefix fails with the rest after it. -/
theorem twinFailsV_checkJobList_append {mode : ConLeche.CheckMode} {pins : List INatOpPinSet}
    {J : Option ISolution} {I : IStreamIndex} {ds : Array IDeclaration} {c : Word} :
    ∀ (w rest : List Nat) (a : AState), TwinFailsV (checkJobList mode pins J I ds w) a c →
      TwinFailsV (checkJobList mode pins J I ds (w ++ rest)) a c
  | [], _, a, h => by
    rcases h with ⟨ce, hce, -⟩ | ⟨ce, i, a', hce, -⟩ <;> cases hce
  | t :: w, rest, a, h => by
    have e : ∀ l, (checkJobList mode pins J I ds (t :: l)).run a =
        match runJob mode pins J I ds t a with
        | .ok (.ok (), s') => checkJobList mode pins J I ds l s'
        | .ok (.error e, s') => .ok (.error e, s')
        | .error e => .error e := fun _ => rfl
    have ih := twinFailsV_checkJobList_append (mode := mode) (pins := pins) (J := J) (I := I)
      (ds := ds) (c := c) w rest
    cases hr : runJob mode pins J I ds t a with
    | error ce =>
      rcases h with ⟨ce', hce, hc⟩ | ⟨ce', i, a', hce, hc⟩
      · exact .inl ⟨ce', by rw [List.cons_append, e, hr]; rw [e, hr] at hce; exact hce, hc⟩
      · rw [e, hr] at hce; cases hce
    | ok v =>
      obtain ⟨r, s'⟩ := v
      cases r with
      | error ce =>
        rcases h with ⟨ce', hce, hc⟩ | ⟨ce', i, a', hce, hc⟩
        · rw [e, hr] at hce; cases hce
        · exact .inr ⟨ce', i, a', by rw [List.cons_append, e, hr]; rw [e, hr] at hce; exact hce, hc⟩
      | ok u =>
        cases u
        have h' : TwinFailsV (checkJobList mode pins J I ds w) s' c := by
          rcases h with ⟨ce', hce, hc⟩ | ⟨ce', i, a', hce, hc⟩
          · exact .inl ⟨ce', by rw [e, hr] at hce; exact hce, hc⟩
          · exact .inr ⟨ce', i, a', by rw [e, hr] at hce; exact hce, hc⟩
        rcases ih s' h' with ⟨ce', hce, hc⟩ | ⟨ce', i, a', hce, hc⟩
        · exact .inl ⟨ce', by rw [List.cons_append, e, hr]; exact hce, hc⟩
        · exact .inr ⟨ce', i, a', by rw [List.cons_append, e, hr]; exact hce, hc⟩

end L.Checker
