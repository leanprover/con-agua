module

public import ConAgua.Arena.PoolJobsJ
import ConAgua.Arena.PoolJobs

@[expose] public section

/-!
# The challenge's pool with a solution, several workers (lane compare2)

con-ron's `Arena.pooledAcceptsJ_bridge` (`Bridge/Compare/Pooled.lean`, its `pooled_foldP` over
the workers' job lists) at the L level, for the threaded compared run: as the flat pool
(`Arena/PoolJobs.lean`: `pool_walk`, `pool_prefix`, `pool_twin`) with the prefix a mixed run
(`MixedPrefix`) and each step `job_specC` (`Arena/PoolJobsJ.lean`'s `PoolHypsJ`, whose
`pool_walkJ` is the one-worker case over `j‥j+n-1`).

* `pool_walkJL`: a worker's chain over any list of positions whose prefixes are mixed runs is the
  twin's `checkJobList` accepting at the solution, each record a mixed step at its prefix.
  The pool over workers from their own starts: `pool_prefixJW`, `pool_twinJW` (`Arena/C1Pool.lean`).
-/

open ConRon.Arena ConRon.Bridge

namespace L.Arena

local notation "V" => ConLeche.CheckMode.verified

section pool

variable {pins : List INatOpPinSet} {pinsP : List ConLeche.NatOpPinSet}
  {ds : Array IDeclaration} {dsP : List ConLeche.Declaration} {I : IStreamIndex} {s₁ : AState}
  {J : ISolution} {dsS : List ConLeche.Declaration}
  {matesU : Std.HashMap ConLeche.Name (Array ConLeche.Name)}
  {σ : Type} {Rel : σ → AState → Prop} {Call : Nat → σ → σ → Prop}

/-- **A worker's chain with a solution, refined**: from a related worker's state, a chain of steps
at positions whose prefixes are mixed runs is the twin's `checkJobList` accepting at the solution,
and each record a mixed step at its prefix's environment. -/
theorem pool_walkJL (H : PoolHypsJ (pins := pins) (pinsP := pinsP) (ds := ds) (dsP := dsP) (I := I)
      (s₁ := s₁) (J := J) (dsS := dsS) (matesU := matesU) Rel Call) :
    ∀ (l : List Nat) (r : σ) (a : AState), Rel r a → WorkerOK s₁ a → JobChain Call r l →
      (∀ x ∈ l, x < ds.size ∧
        MixedPrefix pinsP ⟨ConLeche.mkFEnv (ConLeche.streamEnv dsS), matesU⟩ dsP x) →
      (∃ a', checkJobList V pins (some J) I ds l a = .ok (.ok (), a')) ∧
      ∀ x ∈ l, ∃ (hx : x < dsP.length) (env' : ConLeche.Env),
        Compare.MixedStep pinsP ⟨ConLeche.mkFEnv (ConLeche.streamEnv dsS), matesU⟩
          (ConLeche.streamEnv (dsP.take x)) dsP[x] env' := by
  intro l
  induction l with
  | nil => intro r a _ _ _ _; exact ⟨⟨a, rfl⟩, fun x hx => absurd hx (by simp)⟩
  | cons t rest ih =>
    intro r a hr hw hc hl
    cases hc with
    | @cons _ _ r' _ hcall hrest =>
      obtain ⟨htk, hPt⟩ := hl t List.mem_cons_self
      obtain ⟨htk', hdk⟩ := H.hden t htk
      have hF := worker_foldOKJ H.hpinsOK H.hpersPins H.hI H.hpI htk' hPt hw
      obtain ⟨a', hj, hr'⟩ := H.hstep t r r' a htk hr hcall hF
      obtain ⟨hw', env', hst⟩ := job_specC H.hrec H.hpp H.hpinsOK H.hpersPins H.hpins H.hpd H.hI
        H.hpI H.hIS H.hpIS H.hndS H.hmates hw htk htk' hdk hPt hj
      obtain ⟨⟨a'', hl'⟩, hds⟩ := ih r' a' hr' hw' hrest fun x hx => hl x (List.mem_cons_of_mem _ hx)
      refine ⟨⟨a'', ?_⟩, fun x hx => ?_⟩
      · rw [checkJobList_cons_ok htk hj]; exact hl'
      · rcases List.mem_cons.mp hx with rfl | hx'
        · exact ⟨htk', env', hst⟩
        · exact hds x hx'

end pool

end L.Arena
