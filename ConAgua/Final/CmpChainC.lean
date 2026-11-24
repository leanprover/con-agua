module

public import ConAgua.Final.CmpChain
public import ConAgua.Final.CompareTwin
public import ConAgua.Checker.CompareChain6J
public import ConAgua.Checker.CompareTwinJ
import ConAgua.Checker.CrsProgPB
import ConAgua.Checker.RomProgInit
import ConAgua.Final.DrvFinal
import ConAgua.Checker.JobsProg
import ConAgua.Checker.ArmsT
import ConAgua.Checker.CheckARun
import ConAgua.Checker.AsmFinal
import all ConAgua.Checker.Entry
import ConAgua.Checker.CompareJobs
import ConAgua.Arena.JobStart

@[expose] public section

/-!
# The compared run's L runs accept ⇒ the twin's compared run accepts (lane compare)

* `cmpCJobs_twin`: after mode `6` (`F6`), entry 2 in place (`check` with the mode word `2` on a
  memory that keeps mode `6`'s final word arrays the jobs name, the range `[0, c)`, an empty seed)
  returning `ACCEPT` is the twin's challenge jobs accepting at the solution `solutionOf IS res`
  (`checkMode2_seqR`, then `pool_twinJ`, con-ron's `pooledAcceptsJ_bridge` with one worker).
-/

namespace ConAgua.Final

open L L.Compiler L.Checker L.Arena L.Rom
open ConRon.Arena
open ConRon.Bridge (JobChain PExt)

/-- A run of `check` keeps the bytes (the checker stores no byte). -/
theorem run_check_bytes {N : Nat} {m : Mem} {rs : List Word} {m' : Mem}
    (h : L.run checkerProg N "check" [] m = .ok (rs, m')) : m'.bytes = m.bytes := by
  have t := Triple.keep checkerProg_noSt8 (n := N) (f := "check") (vs := [])
    (s₀ := ⟨m, Locals.init []⟩) (Q := fun _ _ => True)
    (M.triple_of_run fun _ _ _ _ _ => trivial)
  have hk := run_post (Q := fun _ m'' => L.Keep m m'') h (by
    apply M.triple_of_run
    intro s r s' hs' hrun
    exact (M.of_run (P := fun x => x = _) hs' hrun t).2.1)
  exact hk.1

/-- **The challenge's jobs of the compared run accept ⇒ the twin's job list accepts** (one worker,
at the solution `solutionOf IS res`): after mode `6` (`F6`), entry 2 in place on a memory `w` that
agrees with mode `6`'s memory before `par_compact(0)` on every array the jobs name, with the range
`[0, c)` and an empty seed, returning `ACCEPT`. -/
theorem cmpCJobs_twin {bC bS pb : ByteArray} (hpb : pb.size < 2 ^ 63) (PS : PhaseS bC bS) {m₇ m : Mem}
    (hF : FoldOn bS pb (abiSz checkerTab) PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m)
    (hS : ∃ s'', checkJobList .verified PS.ipins none PS.IS PS.dsS (List.range PS.dsS.size)
      PS.sF.worker = .ok (.ok (), s''))
    {c : Word} {m9 : Mem} (h6 : F6 PS m c m9) (hb9 : m9.bytes = m.bytes)
    {w : Mem} (hw : ∀ a, phaseBS a = true → w.arr64 a = m9.arr64 a) (hmode : w.glob MODE = 2)
    (hlo : w.glob PLO = 0) (hhi : w.glob PHI = c) (hctlf : (w.arr64 CTLF).size = 0)
    {rs7 : List Word} {m7 : Mem} (h7 : L.run checkerProg abiFuel "check" [] w = .ok (rs7, m7))
    (hacc : rs7.headD 0 = ACCEPT) :
    ∃ (m2 m3 : Mem) (dsC : Array IDeclaration) (sG : AState) (res : List IDeclaration) (m4 : Mem)
      (I : IStreamIndex) (a' : AState),
      Side6 PS m c m2 m3 dsC sG res m4 ∧ buildIndex res.toArray sG = .ok (.ok I, a') ∧
      ∃ s'', checkJobList .verified PS.ipins (some (solutionOf PS.IS res)) I res.toArray
        (List.range res.toArray.size) a'.worker = .ok (.ok (), s'') := by
  obtain ⟨m2, m3, dsC, sG, res, m4, I, a', h, hI, hJ0⟩ := F6.jobR hF h6
  refine ⟨m2, m3, dsC, sG, res, m4, I, a', h, hI, ?_⟩
  obtain ⟨-, -, -, -, ho⟩ := h.phase.out
  -- the program facts
  have hr : RomOK pb.data.toList := by simpa [RomOK] using hpb
  have hpre := hF.r7.since.pbpre
  have hinj : L.Ind.DnInj (dnOf sG.store) := dnOf_inj ho.drv.state.wf
  have hq : L.Ind.QuotDn (dnOf sG.store) := by
    obtain ⟨k, hk, hd⟩ := ho.quot
    exact ⟨k, by simp only [dnOf, hk]; exact hd⟩
  obtain ⟨hdf, hind⟩ := checkerCdG_proved pb PS.ipins (dnOf sG.store) res.toArray hpb hpre hinj
  have hcd := checkerProg_cdProgPB pb.data.toList hr hpre hinj hq hdf hind
  have hJP := checkerProg_jobProgPB pb.data.toList hr hpre hcd (checkerProg_canonPB _)
  -- the L run: a chain of `record_job` calls from the job relation
  have hPB : m9.arr8 L.Rom.PB = pb.data.toList.toArray := by
    show m9.bytes L.Rom.PB = _
    rw [hb9, hF.bytes, ← Mem.arr8, hF.r7.since.keep.arr8]
    exact loadMem_pb bS pb _
  have hcnt : c.toNat = res.toArray.size := by simpa using h.count.1
  have hN : abiFuel ≤ 2 ^ 62 := by simp [abiFuel]
  obtain ⟨r, hJr, hch⟩ : JobsRan PS.ipins (dnOf sG.store) res.toArray (some (solutionOf PS.IS res)) I
      { a' with caches := Caches.empty } (Prog.subPB pb.data.toList checkerProg) res.toArray.size := by
    simp only [L.run] at h7
    cases e : (invoke checkerProg (exec checkerProg abiFuel) "check" []).run ⟨w, Locals.init []⟩ with
    | error _ => rw [e] at h7; cases h7
    | ok x =>
      obtain ⟨r, s⟩ := x
      rw [e] at h7
      simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h7
      obtain ⟨rfl, -⟩ := h7
      exact M.of_run (P := fun x => x = ⟨w, Locals.init []⟩) rfl e
        (checkMode2_seqR hJ0 hPB hJP abiFuel hN c hcnt ⟨w, Locals.init []⟩ hw hmode hlo hhi hctlf) hacc
  -- the twin
  obtain ⟨pinsP, dsP, dsSP, matesU, hst, hspec, hpp, hden, hPD, hH⟩ := poolHypsJ_of h.phase hS hI
    (JobRel PS.ipins (dnOf sG.store) res.toArray (some (solutionOf PS.IS res)) I
      { a' with caches := Caches.empty }) (RecCall (Prog.subPB pb.data.toList checkerProg))
  have hdn : DnPers (dnOf sG.store) := fun k x hk => by
    simp only [dnOf] at hk; split at hk
    · assumption
    · cases hk
  have hds : res.toArray.size < 2 ^ 64 := by rw [← hcnt]; exact UInt64.toNat_lt c
  have H := hH (recCall_stepE (J := some (solutionOf PS.IS res)) hJP ho.front
    (declsLpsDn_dnOf ho.pd ho.den) hdn hpp hds hden hPD hspec
    (fun _ => checkerProg_crsSpecPB pb.data.toList hr hpre hcd))
  exact pool_twinJ H hst ⟨_, ⟨hJr, PExt.of_ext (Ext.refl _), rfl⟩, sameEnter_worker.symm⟩ hch

/-- `2^63 + k` for `k < 2^63` is not `ACCEPT`. -/
theorem high_ne_accept {k : Word} (hk : k.toNat < 2 ^ 63) : (9223372036854775808 : Word) + k ≠ ACCEPT := by
  intro e
  have e2 := congrArg UInt64.toNat e
  rw [UInt64.toNat_add] at e2
  simp only [ACCEPT, UInt64.reduceToNat] at e2
  omega

end ConAgua.Final
