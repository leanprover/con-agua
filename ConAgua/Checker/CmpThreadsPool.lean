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
* `pool_prefixJ`: workers whose claims increase and cover `[0, n)` give every prefix up to `n` a
  mixed run (by induction on the position: the worker that claimed `k` ran its earlier claims,
  whose prefixes the induction gives).
* `pool_twinJT`: every worker's list accepted by `checkJobList` from the driver state's worker.
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

/-- **The pool's induction with a solution, up to `n`**: workers, each a start state related to
the driver state's worker and a chain of steps, with claims increasing in each worker and covering
the positions below `n`, give every prefix up to length `n` a mixed run. -/
theorem pool_prefixJ (H : PoolHypsJ (pins := pins) (pinsP := pinsP) (ds := ds) (dsP := dsP) (I := I)
      (s₁ := s₁) (J := J) (dsS := dsS) (matesU := matesU) Rel Call) (hst : StateOK s₁)
    (ths : List (σ × List Nat)) (hstart : ∀ t ∈ ths, Rel t.1 s₁.worker)
    (hchain : ∀ t ∈ ths, JobChain Call t.1 t.2) (hinc : ∀ t ∈ ths, t.2.Pairwise (· < ·))
    (n : Nat) (hn : n ≤ ds.size) (hcov : ∀ k < n, ∃ t ∈ ths, k ∈ t.2) :
    ∀ k ≤ n, MixedPrefix pinsP ⟨ConLeche.mkFEnv (ConLeche.streamEnv dsS), matesU⟩ dsP k := by
  have main : ∀ k, k ≤ n → ∀ t ≤ k,
      MixedPrefix pinsP ⟨ConLeche.mkFEnv (ConLeche.streamEnv dsS), matesU⟩ dsP t := by
    intro k
    induction k with
    | zero =>
      intro _ t ht
      obtain rfl : t = 0 := by omega
      exact MixedPrefix.zero _ _ _
    | succ k ih =>
      intro hk t ht
      rcases Nat.lt_or_ge t (k + 1) with htk | htk
      · exact ih (by omega) t (by omega)
      obtain rfl : t = k + 1 := by omega
      have hbelow := ih (by omega)
      have hks : k < ds.size := by omega
      obtain ⟨th, hth, hkw⟩ := hcov k (by omega)
      obtain ⟨pre, post, he⟩ := List.append_of_mem hkw
      have hpw := hinc th hth
      rw [he] at hpw
      have hpre : ∀ x ∈ pre, x < k := fun x hx =>
        (List.pairwise_append.mp hpw).2.2 x hx k List.mem_cons_self
      have hc : JobChain Call th.1 (pre ++ [k]) := by
        have := hchain th hth
        rw [he, show pre ++ k :: post = (pre ++ [k]) ++ post by simp] at this
        exact JobChain.append_left this
      obtain ⟨-, hds⟩ := pool_walkJL H (pre ++ [k]) th.1 s₁.worker (hstart th hth)
        (WorkerOK.start hst) hc fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · have := hpre x hx
            exact ⟨by omega, hbelow x (by omega)⟩
          · obtain rfl := List.mem_singleton.mp hx
            exact ⟨hks, hbelow x (Nat.le_refl _)⟩
      obtain ⟨hk', env', hd⟩ := hds k (by simp)
      exact MixedPrefix.step hk' (hbelow k (Nat.le_refl _)) hd
  exact fun k hk => main n (Nat.le_refl _) k hk

/-- **The pool with a solution, refined** (con-ron's `pooledAcceptsJ_bridge`'s pool at the L level):
workers, each a start state related to the driver state's worker and a chain of steps, whose
claims are positions of the records, increase in each worker and cover the positions, give every
worker's list accepted by the twin's `checkJobList` at the solution from the driver state's
worker. -/
theorem pool_twinJT (H : PoolHypsJ (pins := pins) (pinsP := pinsP) (ds := ds) (dsP := dsP) (I := I)
      (s₁ := s₁) (J := J) (dsS := dsS) (matesU := matesU) Rel Call) (hst : StateOK s₁)
    (ths : List (σ × List Nat)) (hstart : ∀ t ∈ ths, Rel t.1 s₁.worker)
    (hchain : ∀ t ∈ ths, JobChain Call t.1 t.2) (hinc : ∀ t ∈ ths, t.2.Pairwise (· < ·))
    (hrange : ∀ t ∈ ths, ∀ k ∈ t.2, k < ds.size) (hcov : ∀ k < ds.size, ∃ t ∈ ths, k ∈ t.2) :
    ∀ t ∈ ths, ∃ s'', checkJobList V pins (some J) I ds t.2 s₁.worker = .ok (.ok (), s'') := by
  have main := pool_prefixJ H hst ths hstart hchain hinc ds.size (Nat.le_refl _) hcov
  intro th hth
  exact (pool_walkJL H th.2 th.1 s₁.worker (hstart th hth) (WorkerOK.start hst) (hchain th hth)
    fun x hx => have := hrange th hth x hx; ⟨this, main x (by omega)⟩).1

end pool

end L.Arena
