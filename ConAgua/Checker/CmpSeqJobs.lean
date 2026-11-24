module

public import ConAgua.Arena.PoolJobsJ
public import ConAgua.Arena.JobStart

@[expose] public section

/-!
# The sequential compared run's `check_jobs` calls, both outcomes (lane compare2, the sJ variant)

A phase of the sequential compared run is one `check_jobs(0, k)` call over every record, from a
memory in the job relation. `checkJobs_refX` refines it to the twin's `checkJobList` in order,
given con-ron's fold invariant at each job's view from the jobs before it:

* `seq_foldS`, `seq_foldJ`: the invariant from the twin's jobs before it (the solution's: the
  fold's prefix, `job_spec`; the challenge's at the solution: the mixed prefix, `job_specC`), from a
  worker's state of the pool's driver state; the end state is one again.
* `cq_jobsOk`, `cq_jobsErr`: a returning call is the twin's list accepting (with the job relation
  and the record pool's growth at the end), a failing one the twin's list failing with its class.
-/

namespace L.Checker

open L L.Arena
open ConRon.Arena ConRon.Bridge

local notation "V" => ConLeche.CheckMode.verified

section fold

variable {pins : List INatOpPinSet} {pinsP : List ConLeche.NatOpPinSet}
  {ds : Array IDeclaration} {dsP : List ConLeche.Declaration} {I : IStreamIndex} {s₁ : AState}
  {σ : Type} {Rel : σ → AState → Prop} {Call : Nat → σ → σ → Prop}

/-- **The solution's jobs in order keep the fold's prefix** (`checkJobs_seqE`'s induction): from a
worker's state, an accepting list over `t‥t+c-1` after a prefix of length `t` ends in a worker's
state after a prefix of length `t + c`. -/
theorem seq_prefixS (H : PoolHyps (pins := pins) (pinsP := pinsP) (ds := ds) (dsP := dsP) (I := I)
      (s₁ := s₁) Rel Call) :
    ∀ (c t : Nat) (a a' : AState), WorkerOK s₁ a →
      (PrefixOK pinsP dsP t ∧ ((ConLeche.Cached.recsConsts (dsP.take t)).map (·.name)).Nodup) →
      t + c ≤ ds.size →
      checkJobList V pins none I ds (List.range' t c) a = .ok (.ok (), a') →
      WorkerOK s₁ a' ∧ PrefixOK pinsP dsP (t + c) ∧
        ((ConLeche.Cached.recsConsts (dsP.take (t + c))).map (·.name)).Nodup := by
  intro c
  induction c with
  | zero =>
    intro t a a' hw hP _ hl
    rw [List.range'_zero] at hl
    cases hl
    exact ⟨hw, hP⟩
  | succ c ih =>
    intro t a a' hw ⟨hPt, hndt⟩ hle hl
    have htk : t < ds.size := by omega
    rw [List.range'_succ] at hl
    cases hrj : recordJob V pins none I t ds[t] a with
    | error ce =>
      have e1 : (checkJobList V pins none I ds (t :: List.range' (t + 1) c)) a =
          .ok (.error (ce, t), AState.abandoned) := by
        simp only [checkJobList, runJob, Array.getElem?_eq_getElem htk, hrj]
      rw [show (checkJobList V pins none I ds (t :: List.range' (t + 1) c)) a = _ from hl] at e1
      cases e1
    | ok v =>
      obtain ⟨u, a₁⟩ := v
      cases u
      rw [checkJobList_cons_ok htk hrj] at hl
      obtain ⟨htk', hdk⟩ := H.hden t htk
      obtain ⟨hw₁, env', F, hd⟩ := job_spec H.hrec H.hpp H.hpinsOK H.hpersPins H.hpins H.hpd
        H.hI H.hpI hw htk htk' hdk hPt.envWF hndt hrj
      have := ih (t + 1) a₁ a' hw₁ (PrefixOK.step H.hpush htk' hPt hd hndt) (by omega) hl
      rwa [show t + 1 + c = t + (c + 1) by omega] at this

/-- The empty prefix. -/
theorem prefixOK_zero (pinsP : List ConLeche.NatOpPinSet) (dsP : List ConLeche.Declaration) :
    PrefixOK pinsP dsP 0 ∧ ((ConLeche.Cached.recsConsts (dsP.take 0)).map (·.name)).Nodup := by
  have h0 : (ConLeche.Cached.recsConsts ([] : List ConLeche.Declaration)).length = 0 := by
    have := (ConLeche.Cached.buildIndex_spec (#[] : Array ConLeche.Declaration)).next
    simpa [ConLeche.Cached.buildIndex] using this.symm
  refine ⟨⟨0, fun _ _ => rfl⟩, ?_⟩
  rw [List.take_zero, List.eq_nil_of_length_eq_zero h0]
  exact List.nodup_nil

/-- **The solution's fold invariant at each job** from a worker's state `a`: after the jobs before
it accepted in order. -/
theorem seq_foldS (H : PoolHyps (pins := pins) (pinsP := pinsP) (ds := ds) (dsP := dsP) (I := I)
      (s₁ := s₁) Rel Call) {a : AState} (hw : WorkerOK s₁ a) :
    ∀ (t : Nat) (a' : AState), t < ds.size →
      checkJobList V pins none I ds (List.range' 0 t) a = .ok (.ok (), a') →
      ∃ env, FoldOK env (I.view t) (AM.st enterScratch a') := by
  intro t a' ht hl
  obtain ⟨hw', hP, hnd⟩ := seq_prefixS H t 0 a a' hw (prefixOK_zero pinsP dsP) (by omega) hl
  rw [Nat.zero_add] at hP hnd
  obtain ⟨htk', -⟩ := H.hden t ht
  exact worker_foldOK H.hpinsOK H.hpersPins H.hI H.hpI htk' hP hnd hw'

/-- **The solution's jobs in order end in a worker's state.** -/
theorem seq_workerS (H : PoolHyps (pins := pins) (pinsP := pinsP) (ds := ds) (dsP := dsP) (I := I)
      (s₁ := s₁) Rel Call) {a a' : AState} (hw : WorkerOK s₁ a)
    (hl : checkJobList V pins none I ds (List.range ds.size) a = .ok (.ok (), a')) : WorkerOK s₁ a' := by
  rw [List.range_eq_range'] at hl
  exact (seq_prefixS H ds.size 0 a a' hw (prefixOK_zero pinsP dsP) (by omega) hl).1

variable {J : ISolution} {dsS : List ConLeche.Declaration}
  {matesU : Std.HashMap ConLeche.Name (Array ConLeche.Name)}

/-- **The challenge's jobs in order keep the mixed prefix** (`pool_walkJ`'s induction). -/
theorem seq_prefixJ (H : PoolHypsJ (pins := pins) (pinsP := pinsP) (ds := ds) (dsP := dsP) (I := I)
      (s₁ := s₁) (J := J) (dsS := dsS) (matesU := matesU) Rel Call) :
    ∀ (c t : Nat) (a a' : AState), WorkerOK s₁ a →
      MixedPrefix pinsP ⟨ConLeche.mkFEnv (ConLeche.streamEnv dsS), matesU⟩ dsP t →
      t + c ≤ ds.size →
      checkJobList V pins (some J) I ds (List.range' t c) a = .ok (.ok (), a') →
      WorkerOK s₁ a' ∧ MixedPrefix pinsP ⟨ConLeche.mkFEnv (ConLeche.streamEnv dsS), matesU⟩ dsP (t + c) := by
  intro c
  induction c with
  | zero =>
    intro t a a' hw hP _ hl
    rw [List.range'_zero] at hl
    cases hl
    exact ⟨hw, hP⟩
  | succ c ih =>
    intro t a a' hw hP hle hl
    have htk : t < ds.size := by omega
    rw [List.range'_succ] at hl
    cases hrj : recordJob V pins (some J) I t ds[t] a with
    | error ce =>
      have e1 : (checkJobList V pins (some J) I ds (t :: List.range' (t + 1) c)) a =
          .ok (.error (ce, t), AState.abandoned) := by
        simp only [checkJobList, runJob, Array.getElem?_eq_getElem htk, hrj]
      rw [show (checkJobList V pins (some J) I ds (t :: List.range' (t + 1) c)) a = _ from hl] at e1
      cases e1
    | ok v =>
      obtain ⟨u, a₁⟩ := v
      cases u
      rw [checkJobList_cons_ok htk hrj] at hl
      obtain ⟨htk', hdk⟩ := H.hden t htk
      obtain ⟨hw₁, env', hst⟩ := job_specC H.hrec H.hpp H.hpinsOK H.hpersPins H.hpins H.hpd H.hI
        H.hpI H.hIS H.hpIS H.hndS H.hmates hw htk htk' hdk hP hrj
      have := ih (t + 1) a₁ a' hw₁ (MixedPrefix.step htk' hP hst) (by omega) hl
      rwa [show t + 1 + c = t + (c + 1) by omega] at this

/-- **The challenge's fold invariant at each job** from a worker's state `a`. -/
theorem seq_foldJ (H : PoolHypsJ (pins := pins) (pinsP := pinsP) (ds := ds) (dsP := dsP) (I := I)
      (s₁ := s₁) (J := J) (dsS := dsS) (matesU := matesU) Rel Call) {a : AState} (hw : WorkerOK s₁ a) :
    ∀ (t : Nat) (a' : AState), t < ds.size →
      checkJobList V pins (some J) I ds (List.range' 0 t) a = .ok (.ok (), a') →
      ∃ env, FoldOK env (I.view t) (AM.st enterScratch a') := by
  intro t a' ht hl
  obtain ⟨hw', hP⟩ := seq_prefixJ H t 0 a a' hw (MixedPrefix.zero _ _ _) (by omega) hl
  rw [Nat.zero_add] at hP
  obtain ⟨htk', -⟩ := H.hden t ht
  exact worker_foldOKJ H.hpinsOK H.hpersPins H.hI H.hpI htk' hP hw'

end fold

section jobs

variable {pins : List INatOpPinSet} {pinsP : List ConLeche.NatOpPinSet}
  {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration} {p : Prog} {J : Option ISolution}
  {I : IStreamIndex} {a₀ : AState}

/-- **A returning `check_jobs(0, hi)` over every record is the twin's jobs in order accepting**
(`checkJobs_refX`), from a memory in the job relation, given the fold invariant before each job:
the job relation at the end and the record pool grown. -/
theorem cq_jobsOk (hP : JobProg pins dn ds p) (hFD : FrontDecls ds) (hLD : DeclsLpsDn dn ds)
    (hdn : DnPers dn) (hpp : PersPinSets pins)
    (hden : ∀ x ∈ ds.toList, PersDecl x ∧ ∃ d, Frontend.denoteDecl a₀.store x = some d)
    (hPD : PinsDenote a₀.store pins pinsP) (hrec : JobSpec pins pinsP J a₀)
    (hcrs : CrsFor pins dn ds p J) {hi : Word} (hhi : hi.toNat = ds.size)
    {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState} (hR : JobPost pins dn ds J I a₀ m a)
    (hfold : ∀ (t : Nat) (a' : AState), t < ds.size →
      checkJobList V pins J I ds (List.range' 0 t) a = .ok (.ok (), a') →
      ∃ env, FoldOK env (I.view t) (AM.st enterScratch a'))
    {r : List Word} {m' : Mem} (hc : callE p n "check_jobs" [0, hi] m = .ok (r, m')) :
    ∃ a', checkJobList V pins J I ds (List.range ds.size) a = .ok (.ok (), a') ∧
      JobPost pins dn ds J I a₀ m' a' ∧ ArrExt (erecP m) (erecP m') := by
  have h := checkJobs_refX (j := 0) (hi := hi) hP hFD hLD hdn hpp hden hPD hrec hcrs (by omega) hn hR
    (fun t a' _ h2 h3 => by
      simp only [UInt64.toNat_zero, Nat.sub_zero] at h2 h3
      exact hfold t a' (by omega) h3)
  obtain ⟨s', hs', -, hOk⟩ := RefC.run_ok (s₀ := ⟨m, Locals.init []⟩)
    (checkJobs_specE p hP.check_jobs n ⟨m, Locals.init []⟩ 0 hi) h hc
  obtain ⟨a', h1, h2, h3⟩ := hOk
  simp only [UInt64.toNat_zero, Nat.sub_zero, hhi, ← List.range_eq_range'] at h1
  exact ⟨a', h1, by rw [← hs']; exact h2, by rw [← hs']; exact h3⟩

/-- **A failing `check_jobs(0, hi)` over every record is the twin's jobs in order failing**
(`checkJobs_ref`) with the error's class, from a memory in the job relation, given the fold
invariant before each job and `check_decl`'s program facts. -/
theorem cq_jobsErr (hP : JobProg pins dn ds p) (hFD : FrontDecls ds) (hLD : DeclsLpsDn dn ds)
    (hdn : DnPers dn) (hpp : PersPinSets pins)
    (hden : ∀ x ∈ ds.toList, PersDecl x ∧ ∃ d, Frontend.denoteDecl a₀.store x = some d)
    (hPD : PinsDenote a₀.store pins pinsP) (hrec : JobSpec pins pinsP J a₀)
    (hcrs : CrsFor pins dn ds p J) (hG : JobGJ pins dn ds p J) {hi : Word} (hhi : hi.toNat = ds.size)
    {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState} (hR : JobPost pins dn ds J I a₀ m a)
    (hfold : ∀ (t : Nat) (a' : AState), t < ds.size →
      checkJobList V pins J I ds (List.range' 0 t) a = .ok (.ok (), a') →
      ∃ env, FoldOK env (I.view t) (AM.st enterScratch a'))
    {e : Err} (hc : callE p n "check_jobs" [0, hi] m = .error e) :
    ErrClaimV (checkJobList V pins J I ds (List.range ds.size)) a e := by
  have h := checkJobs_ref (j := 0) (hi := hi) hP hFD hLD hdn hpp hden hPD hrec hcrs (by omega) hn hR
    (fun t a' _ h2 h3 => by
      simp only [UInt64.toNat_zero, Nat.sub_zero] at h2 h3
      exact hfold t a' (by omega) h3)
  have h' := RefC.run_err (s₀ := ⟨m, Locals.init []⟩)
    (checkJobs_specE p hP.check_jobs n ⟨m, Locals.init []⟩ 0 hi)
    (fun e h0 => ErrClaimV.of_cls0 h0) trivial hG h hc
  simpa only [UInt64.toNat_zero, Nat.sub_zero, hhi, ← List.range_eq_range'] using h'

/-- **An accepting list from a state that enters alike**, with the end states entering alike. -/
theorem checkJobList_ok_sameEnter {J : Option ISolution} {l : List Nat} {a b a' : AState}
    (h : SameEnter a b) (hl : checkJobList V pins J I ds l a = .ok (.ok (), a')) :
    ∃ b', checkJobList V pins J I ds l b = .ok (.ok (), b') ∧ SameEnter a' b' := by
  rcases l with _ | ⟨t, rest⟩
  · cases hl; exact ⟨b, rfl, h⟩
  · exact ⟨a', by rw [← checkJobList_sameEnter h (by simp)]; exact hl, SameEnter.refl _⟩

/-- **The fold invariant before each job carries over to a state that enters alike.** -/
theorem fold_sameEnter {J : Option ISolution} {a b : AState} (h : SameEnter a b)
    (hf : ∀ (t : Nat) (b' : AState), t < ds.size →
      checkJobList V pins J I ds (List.range' 0 t) b = .ok (.ok (), b') →
      ∃ env, FoldOK env (I.view t) (AM.st enterScratch b')) :
    ∀ (t : Nat) (a' : AState), t < ds.size →
      checkJobList V pins J I ds (List.range' 0 t) a = .ok (.ok (), a') →
      ∃ env, FoldOK env (I.view t) (AM.st enterScratch a') := by
  intro t a' ht hl
  obtain ⟨b', hb, hs⟩ := checkJobList_ok_sameEnter h hl
  rw [hs.st]
  exact hf t b' ht hb

end jobs

end L.Checker
