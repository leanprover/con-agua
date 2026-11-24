module

public import ConAgua.Verdict.CmpVSJobs
public import ConAgua.Verdict.ThreadsE
public import ConAgua.Checker.CmpThreadsC
public import ConAgua.Final.CompareTwinVerdict
import ConAgua.Checker.CmpThreadsPool
import ConAgua.Checker.CmpVerdictNv
import ConAgua.Checker.CompareTwinJ
import ConAgua.Checker.CrsProgPB
import ConAgua.Checker.RomProgInit
import ConAgua.Checker.JobsProg
import ConAgua.Checker.CheckARun
import ConAgua.Checker.AsmFinal
import ConAgua.Arena.FreezeFresh
import ConAgua.Arena.FreezeTrunc
import ConAgua.Arena.JobStart
import ConAgua.Arena.PoolJobsJ

@[expose] public section

/-!
# The challenge's threads of the compared run fail only where the twin's pool does (lane
compare2, helper compare2-verdict)

The error half of `cmpThreadsC_pooledJ` (`Checker/CmpThreadsC.lean`): after the solution's pooled
accept and mode `7` (`F6`, then `par_compact(1)`), a thread over the challenge's buffer whose calls
ran and whose next call failed with a class other than `0`, the jobs below it run by the threads,
is a worker's list of the challenge's jobs failing at the solution
(`TwinCompareVerdictPooled`'s third disjunct). `cjStepE_ofJ`: `cjStepE_of` at any solution, under
the solution's guard (`JobGJ`) and `check_record_sol`'s facts (`CrsFor`).
-/

open ConRon.Arena ConAgua.Final

namespace L.Checker

open L L.Arena L.Rom L.Compiler ConRon.Bridge

local notation "VM" => ConLeche.CheckMode.verified

/-- `CjStepE` at any solution `J`, by `checkJobs_ref` (`cjStepE_of` with `JobGJ` and `CrsFor`). -/
theorem cjStepE_ofJ {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}
    {ds : Array IDeclaration} {I : IStreamIndex} {a₀ : AState} {J : Option ISolution}
    {pinsP : List ConLeche.NatOpPinSet} {p : Prog}
    (hP : JobProg pins dn ds p) (hFD : FrontDecls ds) (hLD : DeclsLpsDn dn ds) (hdn : DnPers dn)
    (hpp : PersPinSets pins) (hds : ds.size < 2 ^ 63)
    (hden : ∀ x ∈ ds.toList, PersDecl x ∧ ∃ d, Frontend.denoteDecl a₀.store x = some d)
    (hPD : PinsDenote a₀.store pins pinsP) (hrec : JobSpec pins pinsP J a₀)
    (hcrs : CrsFor pins dn ds p J) (hG : JobGJ pins dn ds p J) :
    CjStepE pins dn ds I a₀ p J := by
  intro n m a j hn hj ⟨a₁, hJP, hS⟩ hF e hc
  rw [← hS.st] at hF
  have e1 : (j + 1).toNat = j.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  have h := checkJobs_ref (J := J) (I := I) hP hFD hLD hdn hpp hden hPD hrec hcrs (hi := j + 1) (j := j)
    (by rw [e1]; omega) hn hJP
    (fun t a' h1 h2 h3 => by
      obtain rfl : t = j.toNat := by omega
      rw [Nat.sub_self, List.range'_zero] at h3
      cases h3
      exact hF)
  have h' := RefC.run_err (checkJobs_specE p hP.check_jobs n ⟨m, Locals.init []⟩ j (j + 1))
    (fun e h0 => ErrClaimV.of_cls0 h0) trivial hG h hc
  rw [e1, Nat.add_sub_cancel_left, List.range'_one] at h'
  exact fun hk => twinFailsV_of_sameEnter hS (h' hk)

/-- **A challenge job on a thread of the threaded compared run failing is the twin pool's** (the
error half of `cmpThreadsC_pooledJ`). After the solution's index build (`FoldOn`) and its pooled
accept, mode `7` (`F6`, then `par_compact(1)`: `m7`), a thread over mode `7`'s buffer with a fresh
region `r₀` ran its calls `cs` (each below `j`) and its call on `j < c` failed with `e` of class
other than `0`; the threads `ths` (fresh regions, claims below `c`, increasing) ran every index
below `j`: `TwinCompareVerdictPooled`'s third disjunct, at the solution `solutionOf PS.IS res`. -/
theorem cmpV_tjobC {bC bS pb : ByteArray} (hpb : pb.size < 2 ^ 63) (PS : PhaseS bC bS) {m₇ m : Mem}
    (hF : FoldOn bS pb (abiSz checkerTab) PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m)
    (hPS : PooledAccepts .verified PS.ipins PS.dsS PS.sE PS.IS PS.sF)
    {c : Word} {m9 m7 : Mem} (h6 : F6 PS m c m9) (hb9 : m9.bytes = m.bytes)
    (hok : parCompactOK m9 1 = true) (hm7 : m7 = parCompactMem m9 1)
    (r₀ : Mem) (hz : ∀ b ∈ parOwnedL, r₀.arr64 b = zeros (m7.arr64 b).size)
    (hI0 : r₀.glob INIT = 0) (j : Word) (cs : List (Word × Nat × Mem)) (n : Nat) (e : Err)
    (hruns : ThreadFails (cmpBuf OUT m7) j n e r₀ cs) (hcs : ∀ c' ∈ cs, c'.1 < j)
    (hj : j < c) (hk0 : e.cls ≠ 0)
    (ths : List (Mem × List (Word × Nat × Mem)))
    (hth : ∀ t ∈ ths, (∀ b ∈ parOwnedL, t.1.arr64 b = zeros (m7.arr64 b).size) ∧ t.1.glob INIT = 0 ∧
      ThreadRuns (cmpBuf OUT m7) t.1 t.2 ∧ ∀ c' ∈ t.2, c'.1 < c)
    (hinc : ∀ t ∈ ths, (t.2.map (·.1)).Pairwise (· < ·))
    (hbelow : ∀ i : Word, i < j → ∃ t ∈ ths, ∃ c' ∈ t.2, c'.1 = i) :
    TwinCompareVerdictPooled bC bS e.cls := by
  subst hm7
  obtain ⟨m2, m3, dsC, sG, res, m4, I, a', h, hI, hJM, hwf, hoff, hsz9⟩ := F6.jobM hF h6
  obtain ⟨-, -, -, -, ho⟩ := h.phase.out
  let JS := solutionOf PS.IS res
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
  let p := Prog.subPB pb.data.toList checkerProg
  -- the buffer
  have hlt : (m9.arr64 OUT).size < 2 ^ 64 := by
    rw [hsz9, hF.sizeAt]; have := abiSz_le checkerTab_abiOk OUT; simp only [abiWords] at this; omega
  have hB : cmpBuf OUT (parCompactMem m9 1) = bufOf m9 := by
    simp only [cmpBuf]; rw [bufOf, (parCompactMem_hdr hok).2.1]
  rw [hB] at hruns
  have hO := parCompactMem_out m9 1
  have hcnt : c.toNat = res.toArray.size := by simpa using h.count.1
  have hds : res.toArray.size < 2 ^ 63 := by
    have := h.decls.room; have := h.decls.dsize; simp only [List.size_toArray] at *; omega
  have hjN : j.toNat < res.toArray.size := by rw [← hcnt]; exact UInt64.lt_iff_toNat_lt.mp hj
  have hcN : ∀ c' ∈ cs, c'.1.toNat < res.toArray.size := fun c' hc => by
    have := UInt64.lt_iff_toNat_lt.mp (hcs c' hc); omega
  -- the twin's side
  let a₀ : AState := { a' with caches := Caches.empty }
  let Rel : Mem → AState → Prop := fun r a =>
    ∀ j, ThrAt PS.ipins (dnOf sG.store) res.toArray I a₀ pb.data.toList (seedMem (bufMem (bufOf m9) r j)) a
      (some JS)
  let Call : Nat → Mem → Mem → Prop := fun k r r' => ∃ n rs, n ≤ 2 ^ 62 ∧
    L.run checkerProg n "check" [] (bufMem (bufOf m9) r (UInt64.ofNat k)) = .ok (rs, r') ∧
      BufKept (bufOf m9) r'
  obtain ⟨pinsP, dsP, dsSP, matesU, hst, hspec, hpp, hden, hPD, hH⟩ :=
    poolHypsJ_ofP h.phase hPS hI Rel Call
  have hdn : DnPers (dnOf sG.store) := fun k x hk => by
    simp only [dnOf] at hk; split at hk
    · assumption
    · cases hk
  have hcrs : CrsFor PS.ipins (dnOf sG.store) res.toArray p (some JS) :=
    fun _ => checkerProg_crsSpecPB pb.data.toList hr hpre hcd
  have hRS : RecStep PS.ipins (dnOf sG.store) res.toArray I a₀ p (some JS) :=
    recCall_stepE (J := some JS) hJP ho.front (declsLpsDn_dnOf ho.pd ho.den) hdn hpp (by omega) hden hPD
      hspec hcrs
  have hCE : CjStepE PS.ipins (dnOf sG.store) res.toArray I a₀ p (some JS) :=
    cjStepE_ofJ hJP ho.front (declsLpsDn_dnOf ho.pd ho.den) hdn hpp hds hden hPD hspec hcrs
      ⟨jobG_ofDn hinj hq pb hpb hpre, crsG_checker _⟩
  have hstep : ∀ (k : Nat) (r r' : Mem) (a : AState) (hk : k < res.toArray.size), Rel r a → Call k r r' →
      (∃ env, FoldOK env (I.view k) (AM.st enterScratch a)) →
      ∃ a', recordJob VM PS.ipins (some JS) I k res.toArray[k] a = .ok ((), a') ∧ Rel r' a' := by
    intro k r r' a hk hR ⟨n, rs, hn, hrun, hkept⟩ hfo
    have hk' : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
    obtain ⟨⟨a', hrj, X, hJ, hPB, hX⟩, hI'⟩ := runThr hJP.check_jobs hRS hds n hn a (UInt64.ofNat k)
      (by rw [hk']; exact hk) (by rw [hk']; exact hfo) _ rfl (hR _) rfl rfl hrun
    refine ⟨a', ?_, fun j => ⟨X, hJ, hPB, fun t ht => (thr_next _ j hI' hkept (thr_ctl_next hrun) t ht).trans (hX t ht)⟩⟩
    have e : res.toArray[(UInt64.ofNat k).toNat]'(by rw [hk']; exact hk) = res.toArray[k] := by simp only [hk']
    rw [← e]; simp only [hk'] at hrj ⊢; exact hrj
  have H := hH hstep
  -- a fresh region starts in the relation
  have hstart : ∀ r : Mem, (∀ b ∈ parOwnedL, r.arr64 b = zeros ((parCompactMem m9 1).arr64 b).size) →
      r.glob INIT = 0 → Rel r a'.worker := by
    intro r hz hI0 j
    have hKI := indexKeysIn_of hJM.arena.base H.hI H.hpI
    have hSK : SolKeysIn m9 JS := solKeysIn_of hJM.arena.base H.hIS H.hpIS H.hmates
    have hJR := JobM.fresh (hJM.truncJ hoff hKI (fun J' e => by cases e; exact hSK)) hwf hoff
    refine ⟨freshMem m9, ⟨_, ⟨hJR, PExt.of_ext (Ext.refl _), rfl⟩, ?_⟩, ?_, ?_⟩
    · exact ⟨by simp [AState.worker, estore_dropScratch_self hwf hoff], rfl, rfl⟩
    · rw [freshMem_arr8]
      show m9.bytes L.Rom.PB = _
      rw [hb9, hF.bytes, ← Mem.arr8, hF.r7.since.keep.arr8]; exact loadMem_pb bS pb _
    · exact thr_first hok hlt r j (fun b hb => by rw [hz b hb, hO.size]) hI0
  -- the threads' runs below `j`: mixed prefixes up to `j`
  let ths' : List (Mem × List Nat) := ths.map fun t => (t.1, t.2.map (·.1.toNat))
  have hinc' : ∀ t ∈ ths', t.2.Pairwise (· < ·) := by
    intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
    have := hinc t₀ ht₀
    rw [List.pairwise_map] at this ⊢
    exact this.imp fun h => UInt64.lt_iff_toNat_lt.mp h
  have hpre := pool_prefixJ H hst ths'
    (fun t ht => by
      obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
      exact hstart t₀.1 (hth t₀ ht₀).1 (hth t₀ ht₀).2.1)
    (fun t ht => by
      obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
      exact threadRuns_chain (bufOf m9) _ _ (by rw [← hB]; exact (hth t₀ ht₀).2.2.1))
    hinc' j.toNat (Nat.le_of_lt hjN) (fun i hi => by
      have hi64 : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
      obtain ⟨t, ht, c', hc, hci⟩ := hbelow (UInt64.ofNat i) (by rw [UInt64.lt_iff_toNat_lt, hi64]; exact hi)
      exact ⟨_, List.mem_map_of_mem ht, List.mem_map.mpr ⟨c', hc, by rw [hci, hi64]⟩⟩)
  have hfold : ∀ x a, x < res.toArray.size → x ≤ j.toNat → WorkerOK a' a →
      ∃ env, FoldOK env (I.view x) (AM.st enterScratch a) := fun x a hx hxj hw => by
    obtain ⟨hx', -⟩ := H.hden x hx
    exact worker_foldOKJ H.hpinsOK H.hpersPins H.hI H.hpI hx' (hpre x hxj) hw
  -- the thread's walk
  have walk : ∀ (cs : List (Word × Nat × Mem)) (r : Mem) (a : AState), Rel r a → WorkerOK a' a →
      ThreadFails (bufOf m9) j n e r cs → (∀ c' ∈ cs, c'.1 < j) →
      ErrClaimV (checkJobList VM PS.ipins (some JS) I res.toArray (cs.map (·.1.toNat) ++ [j.toNat])) a e := by
    intro cs
    induction cs with
    | nil =>
      intro r a hR hw ⟨hn, hrun⟩ _
      exact runThrE hCE n hn a j hjN (hfold _ a hjN (Nat.le_refl _) hw) _ rfl (hR j) rfl rfl hrun
    | cons c' cs ih =>
      intro r a hR hw h hc
      obtain ⟨j', n', r'⟩ := c'
      obtain ⟨hn', ⟨rs, hrun⟩, hkept, hrest⟩ := h
      have hjj : j'.toNat < j.toNat := UInt64.lt_iff_toNat_lt.mp (hc _ List.mem_cons_self)
      have hj' : j'.toNat < res.toArray.size := by omega
      obtain ⟨⟨a₁, hrj, X, hJ, hPB, hX⟩, hI'⟩ := runThr hJP.check_jobs hRS hds n' hn' a j' hj'
        (hfold _ a hj' (by omega) hw) _ rfl (hR _) rfl rfl hrun
      have hR' : Rel r' a₁ := fun j => ⟨X, hJ, hPB, fun t ht => (thr_next _ j hI' hkept (thr_ctl_next hrun) t ht).trans (hX t ht)⟩
      obtain ⟨hx', hdk⟩ := H.hden _ hj'
      obtain ⟨hw', -⟩ := job_specC H.hrec H.hpp H.hpinsOK H.hpersPins H.hpins H.hpd H.hI
        H.hpI H.hIS H.hpIS H.hndS H.hmates hw hj' hx' hdk (hpre j'.toNat (by omega)) hrj
      exact ErrClaimV.cons_ok hj' hrj
        (ih r' a₁ hR' hw' hrest fun c hc' => hc c (List.mem_cons_of_mem _ hc'))
  have hW := walk cs r₀ a'.worker (hstart r₀ hz hI0) (WorkerOK.start hst) hruns hcs
  obtain ⟨⟨hA, hB', hC⟩, hCS, hDS⟩ := PS.pfx
  refine .inr (.inr ⟨PS.pins, PS.sA, PS.sB, PS.sC, PS.sC', PS.sD, PS.sE, PS.sF, sG, sG, a', PS.pre,
    PS.rC, PS.rS, PS.dsS, dsC, res, PS.ipins, PS.IS, I, cs.map (·.1.toNat) ++ [j.toNat],
    hA, hB', hC, hCS, hDS, PS.pinsR, hPS, h.prep.run, h.run, hI, fun t ht => ?_, hW hk0⟩)
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨c', hc, rfl⟩ := List.mem_map.mp ht
    simpa using hcN c' hc
  · rw [List.mem_singleton.mp ht]; simpa using hjN

-- TEMP (compare2-freeze): `sorryAx` from the stand-ins (thr_ctl_next, ...)
/-- info: 'L.Checker.cmpV_tjobC' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cmpV_tjobC

end L.Checker
