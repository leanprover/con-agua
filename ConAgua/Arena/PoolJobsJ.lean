module

public import ConAgua.Arena.PoolJobs
public import ConRon.Bridge.Compare.Pooled
import ConLeche.Semantics.DeclWF

@[expose] public section

/-!
# The challenge's jobs at the L level, with a solution (lane compare)

con-ron's `Arena.pooledAcceptsJ_bridge` (`Bridge/Compare/Pooled.lean`) with one worker over the
records in order (the sequential driver's `check_jobs`): `pool_walkJ` does the induction over
positions with the fold's prefix a mixed run with distinct names (`MixedPrefix`, as
`pooledAcceptsJ_bridge`'s invariant), each step refining `recordJob` at the solution under
`FoldOK` (`hstep`) and extending the prefix (`job_specC`, `MixedPrefix.step`): a chain of the
worker's steps over `j‥j+n-1` from a prefix of length `j` is the twin's `checkJobList` accepting.
-/

open ConRon.Arena ConRon.Bridge

namespace L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **`FoldOK` at a job's start, from a mixed prefix** (`worker_foldOK` with con-ron's
`MixedPrefix` for the pure fold's prefix, as in `job_specC`). -/
theorem worker_foldOKJ {pinsP : List ConLeche.NatOpPinSet} {JS : ConLeche.Cached.Solution}
    {dsP : List ConLeche.Declaration} {I : IStreamIndex} {s₁ a : AState} {k : Nat}
    (hpinsOK : PinsOK s₁) (hpersPins : PersPins s₁)
    (hI : IndexDenotes s₁.store I (ConLeche.Cached.buildIndex dsP.toArray))
    (hpI : PersIFBase I.base) (hk : k < dsP.length) (hP : MixedPrefix pinsP JS dsP k)
    (hw : WorkerOK s₁ a) :
    ∃ env, FoldOK env (I.view k) (AM.st enterScratch a) := by
  rw [show AM.st enterScratch a = AState.mk a.store.enableScratch Memos.empty a.caches a.pins from rfl]
  exact ⟨_, view_foldOK hpinsOK hpersPins hI hpI hk (hP.1.envWF ConLeche.Semantics.EnvWF.empty) hP.2
    ⟨EStore.enableScratch_wf hw.state.wf⟩ (hw.pext.trans (PExt.enterScratch hw.state.wf))
    (CacheOK.of_empty hw.caches) hw.pins⟩

section pool

variable {pins : List INatOpPinSet} {pinsP : List ConLeche.NatOpPinSet}
  {ds : Array IDeclaration} {dsP : List ConLeche.Declaration} {I : IStreamIndex} {s₁ : AState}
  {J : ISolution} {dsS : List ConLeche.Declaration}
  {matesU : Std.HashMap ConLeche.Name (Array ConLeche.Name)}
  {σ : Type} (Rel : σ → AState → Prop) (Call : Nat → σ → σ → Prop)

/-- **What the challenge's induction takes** (`pooledAcceptsJ_bridge`'s facts at the driver state
`s₁` after the index build): the records and pins denoting, the index denoting, the solution's
index denoting the solution stream `dsS` with distinct names, its mates `matesU`, and a worker's
step `Call k` refining `recordJob` of record `k` at the solution wherever `FoldOK` holds. -/
structure PoolHypsJ : Prop where
  hrec : RecordSpecC pins pinsP J (ConLeche.streamEnv dsS) matesU
  hpp : PersPinSets pins
  hpinsOK : PinsOK s₁
  hpersPins : PersPins s₁
  hpins : PinsDenote s₁.store pins pinsP
  hpd : ∀ x ∈ ds.toList, PersDecl x
  hden : ∀ (i : Nat) (hi : i < ds.size), ∃ hi' : i < dsP.length,
    Frontend.denoteDecl s₁.store ds[i] = some dsP[i]
  hI : IndexDenotes s₁.store I (ConLeche.Cached.buildIndex dsP.toArray)
  hpI : PersIFBase I.base
  hIS : IndexDenotes s₁.store J.idx (ConLeche.Cached.buildIndex dsS.toArray)
  hpIS : PersIFBase J.idx.base
  hndS : ((ConLeche.Cached.recsConsts dsS).map (·.name)).Nodup
  hmates : MatesRel s₁.store J.mates matesU
  hstep : ∀ (k : Nat) (r r' : σ) (a : AState) (hk : k < ds.size), Rel r a → Call k r r' →
    (∃ env, FoldOK env (I.view k) (AM.st enterScratch a)) →
    ∃ a', recordJob V pins (some J) I k ds[k] a = .ok ((), a') ∧ Rel r' a'

variable {Rel Call}

/-- **The challenge's worker, refined** (con-ron's `pooledAcceptsJ_bridge` with one worker): from
a related worker's state and a mixed prefix of length `j`, a chain of steps over `j‥j+n-1` is the
twin's `checkJobList` accepting at the solution. -/
theorem pool_walkJ (H : PoolHypsJ (pins := pins) (pinsP := pinsP) (ds := ds) (dsP := dsP) (I := I)
      (s₁ := s₁) (J := J) (dsS := dsS) (matesU := matesU) Rel Call) :
    ∀ (n j : Nat) (r : σ) (a : AState), Rel r a → WorkerOK s₁ a →
      JobChain Call r (List.range' j n) → j + n ≤ ds.size →
      MixedPrefix pinsP ⟨ConLeche.mkFEnv (ConLeche.streamEnv dsS), matesU⟩ dsP j →
      ∃ a', checkJobList V pins (some J) I ds (List.range' j n) a = .ok (.ok (), a') := by
  intro n
  induction n with
  | zero => intro _ _ a _ _ _ _ _; exact ⟨a, rfl⟩
  | succ n ih =>
    intro j r a hr hw hc hjn hP
    rw [List.range'_succ] at hc ⊢
    cases hc with
    | @cons _ _ r' _ hcall hrest =>
      have hjk : j < ds.size := by omega
      obtain ⟨hjk', hdk⟩ := H.hden j hjk
      have hF := worker_foldOKJ H.hpinsOK H.hpersPins H.hI H.hpI hjk' hP hw
      obtain ⟨a', hj, hr'⟩ := H.hstep j r r' a hjk hr hcall hF
      obtain ⟨hw', env', hst⟩ := job_specC H.hrec H.hpp H.hpinsOK H.hpersPins H.hpins H.hpd H.hI
        H.hpI H.hIS H.hpIS H.hndS H.hmates hw hjk hjk' hdk hP hj
      obtain ⟨a'', hl⟩ := ih (j + 1) r' a' hr' hw' hrest (by omega) (MixedPrefix.step hjk' hP hst)
      exact ⟨a'', by rw [checkJobList_cons_ok hjk hj]; exact hl⟩

/-- **The challenge's jobs over every record, refined**: a chain of steps over `0‥|ds|-1` from a
state related to the driver state's worker. -/
theorem pool_twinJ (H : PoolHypsJ (pins := pins) (pinsP := pinsP) (ds := ds) (dsP := dsP) (I := I)
      (s₁ := s₁) (J := J) (dsS := dsS) (matesU := matesU) Rel Call) (hst : StateOK s₁)
    {r : σ} (hr : Rel r s₁.worker) (hc : JobChain Call r (List.range ds.size)) :
    ∃ a', checkJobList V pins (some J) I ds (List.range ds.size) s₁.worker = .ok (.ok (), a') := by
  rw [List.range_eq_range'] at hc ⊢
  exact pool_walkJ H ds.size 0 r s₁.worker hr (WorkerOK.start hst) hc (by omega) (MixedPrefix.zero _ _ _)

end pool

end L.Arena
