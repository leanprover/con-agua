module

public import ConAgua.Checker.ParThreadTwin
import ConAgua.Arena.FreezeFresh
import ConAgua.Checker.RomProgInit
import ConAgua.Checker.ParThreadCall
import ConAgua.Checker.JobsStart
import ConAgua.Arena.FreezeTrunc
import ConAgua.Arena.IWFrame

@[expose] public section

/-!
# The solution's jobs of the compared run, at the L level (lane compare)

The compared run's driver runs the solution's jobs one after the other on one worker region: job
`j` runs `check` with the mode word `2` on `bufMem Bⱼ rⱼ j`, where `rⱼ` is the region's memory the
job before left (`r₀` the fresh region) and `Bⱼ` the frozen buffer as the job before left it (`B₀`
the buffer after the solution's index build): the frozen arrays are the buffer's, so a job's
stores into them are stores into the buffer. `sjobs_chainO`: such a chain of returning calls,
where each buffer holds the previous job's frozen arrays (`BufKept Bⱼ₊₁ rⱼ₊₁`), is the twin's
`checkJobList` over every record accepting from the index state's worker (one worker of con-ron's
pool, `pool_twin`, claiming `0‥k-1`).
-/

open ConRon.Arena ConAgua.Final

namespace L.Checker

open L L.Arena L.Rom ConRon.Bridge

/-- **The solution's jobs, chained on one region, accept ⇒ the twin's job list accepts.** After the
index build (`FoldOn`, the twin's `StagesOut` and `buildIndex`) and `par_compact(1)`: the buffers
`Bs` (`Bs 0` the frozen buffer) and the region memories `rm` (`rm 0` fresh: every owned array
zero at its size, `INIT = 0`), job `j < |ds|` a returning call on `bufMem (Bs j) (rm j) j` ending in
`rm (j + 1)`, whose frozen arrays (but the header and the seed) are `Bs (j + 1)`'s images. -/
theorem sjobs_chainO {b pb : ByteArray} {sz : TieredArray → Nat} {ds : Array IDeclaration}
    {ipins : List INatOpPinSet} {pins : List ConLeche.NatOpPinSet} {sE : AState} {I : IStreamIndex}
    {sF : AState} {m₇ m : Mem}
    (ho : StagesOut sE ds ipins pins) (hidx : buildIndex ds sE = .ok (.ok I, sF))
    (hF : FoldOn b pb sz ds ipins sE I sF m₇ m)
    (hJP : JobProg ipins (dnOf sE.store) ds (Prog.subPB pb.data.toList checkerProg))
    (hok : parCompactOK m 1 = true) (hlt : (m.arr64 OUT).size < 2 ^ 64)
    (Bs : Nat → Array Word) (hB0 : Bs 0 = bufOf m) (rm : Nat → Mem)
    (hz : ∀ b ∈ parOwnedL, (rm 0).arr64 b = zeros (m.arr64 b).size) (hI0 : (rm 0).glob INIT = 0)
    (hrun : ∀ j < ds.size, ∃ n rs, n ≤ 2 ^ 62 ∧
      L.run checkerProg n "check" [] (bufMem (Bs j) (rm j) (UInt64.ofNat j)) = .ok (rs, rm (j + 1)) ∧
      BufKept (Bs (j + 1)) (rm (j + 1))) :
    ∃ s'', checkJobList .verified ipins none I ds (List.range ds.size) sF.worker = .ok (.ok (), s'') := by
  let bs := pb.data.toList
  let p := Prog.subPB bs checkerProg
  have hsz : ds.size < 2 ^ 63 := by
    have := hF.build.decls.room; have := hF.build.decls.dsize; omega
  have hx := (ho.built hidx).1
  -- the twin's side: the worker state is the job index and the region's memory
  let a₀ : AState := { sF with caches := Caches.empty }
  let Rel : Nat × Mem → AState → Prop := fun r a =>
    ∀ j, ThrAt ipins (dnOf sE.store) ds I a₀ bs (seedMem (bufMem (Bs r.1) r.2 j)) a
  let Call : Nat → Nat × Mem → Nat × Mem → Prop := fun k r r' => r.1 = k ∧ r'.1 = k + 1 ∧ ∃ n rs,
    n ≤ 2 ^ 62 ∧ L.run checkerProg n "check" [] (bufMem (Bs k) r.2 (UInt64.ofNat k)) = .ok (rs, r'.2) ∧
    BufKept (Bs (k + 1)) r'.2
  obtain ⟨pinsP, dsP, hst, hrec, hpp, hden, hPD, hH⟩ := poolHyps_of_out ho hidx Rel Call
  have hFD : FrontDecls ds := ho.front
  have hLD : DeclsLpsDn (dnOf sE.store) ds := declsLpsDn_dnOf ho.pd ho.den
  have hdn : DnPers (dnOf sE.store) := fun k x hk => by
    simp only [dnOf] at hk; split at hk
    · assumption
    · cases hk
  have hRS : RecStep ipins (dnOf sE.store) ds I a₀ p :=
    recCall_stepE (J := none) hJP hFD hLD hdn hpp (by omega) hden hPD hrec (fun h => absurd h (by simp))
  have hstep : ∀ (k : Nat) (r r' : Nat × Mem) (a : AState) (hk : k < ds.size), Rel r a → Call k r r' →
      (∃ env, FoldOK env (I.view k) (AM.st enterScratch a)) →
      ∃ a', recordJob .verified ipins none I k ds[k] a = .ok ((), a') ∧ Rel r' a' := by
    intro k r r' a hk hR ⟨e1, e2, n, rs, hn, hrun, hkept⟩ hfo
    have hk' : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
    have hR' := hR (UInt64.ofNat k)
    rw [e1] at hR'
    obtain ⟨⟨a', hrj, X, hJ, hPB, hX⟩, hI⟩ := runThr hJP.check_jobs hRS hsz n hn a (UInt64.ofNat k)
      (by rw [hk']; exact hk) (by rw [hk']; exact hfo) _ rfl hR' rfl rfl hrun
    refine ⟨a', ?_, fun j => ⟨X, hJ, hPB, fun t ht => ?_⟩⟩
    · have e : ds[(UInt64.ofNat k).toNat]'(by rw [hk']; exact hk) = ds[k] := by simp only [hk']
      rw [← e]; simp only [hk'] at hrj ⊢; exact hrj
    · rw [e2]; exact (thr_next (Bs (k + 1)) j hI hkept t ht).trans (hX t ht)
  have H := hH hstep
  -- the one worker
  have hstart : Rel (0, rm 0) sF.worker := by
    intro j
    have hoff := hF.build.off
    have hw := hF.build.drv.state.wf
    have hKI := indexKeysIn_of (hF.jobM hx).arena.base H.hI H.hpI
    have hJR := JobM.fresh ((hF.jobM hx).trunc hoff hKI) hw hoff
    refine ⟨freshMem m, ⟨_, ⟨hJR, PExt.of_ext (Ext.refl _), rfl⟩, ?_⟩, ?_, ?_⟩
    · exact ⟨by simp [AState.worker, enableScratch_dropScratch], rfl, rfl⟩
    · rw [freshMem_arr8]
      show m.bytes L.Rom.PB = _
      rw [hF.bytes, ← Mem.arr8, hF.r7.since.keep.arr8]; exact loadMem_pb b pb sz
    · show ∀ t, thrS t = true → (seedMem (bufMem (Bs 0) (rm 0) j)).arr64 t = _
      rw [hB0]
      exact thr_first hok hlt (rm 0) j hz hI0
  have hchain : ∀ i ≤ ds.size, JobChain Call (i, rm i) (List.range' i (ds.size - i)) := by
    intro i hi
    induction h : ds.size - i generalizing i with
    | zero => exact .nil _
    | succ c ih =>
      rw [List.range'_succ]
      obtain ⟨n, rs, hn, hr, hk⟩ := hrun i (by omega)
      have hcall : Call i (i, rm i) (i + 1, rm (i + 1)) := ⟨rfl, rfl, n, rs, hn, hr, hk⟩
      exact .cons (w' := (i + 1, rm (i + 1))) hcall (ih (i + 1) (by omega) (by omega))
  have hc0 := hchain 0 (Nat.zero_le _)
  rw [Nat.sub_zero, ← List.range_eq_range'] at hc0
  obtain ⟨-, hacc⟩ := pool_twin H hst [((0, rm 0), List.range ds.size)] (by simpa using hstart)
    (by simpa using hc0) (by simpa using List.pairwise_lt_range)
    (by simp) (fun k hk => ⟨_, List.mem_singleton_self _, List.mem_range.mpr hk⟩)
  exact hacc _ (List.mem_singleton_self _)

end L.Checker
