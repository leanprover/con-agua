module

public import ConAgua.Arena.PoolJobs
public import ConAgua.Checker.CmpThreadsPool

@[expose] public section

/-!
# The pools of a threaded compared run: each worker continues (lane compare2)

The threaded compared run's workers each run their solution jobs from the driver state's worker
and then, from where those ended, their challenge jobs. At the L level (`Arena/PoolJobs.lean`,
`Checker/CmpThreadsPool.lean`) that needs two variants of the pools' inductions:

* `pool_twinE`: the solution's pool, each worker's chain with its end (`JobChainE`): every worker's
  list accepted from the driver state's worker, ending in a worker's state related to the chain's
  end.
* `pool_twinJW`: the challenge's pool with each worker from its own start (a worker's state of the
  driver state, related to its chain's start), every worker's list accepted from there.
-/

open ConRon.Arena ConRon.Bridge

namespace L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **A chain of steps with its end**: steps over the positions `l` from `r`, ending in `r'`. -/
inductive JobChainE {σ : Type} (Run : Nat → σ → σ → Prop) : σ → List Nat → σ → Prop
  | nil (r : σ) : JobChainE Run r [] r
  | cons {k : Nat} {r r' r'' : σ} {l : List Nat} : Run k r r' → JobChainE Run r' l r'' →
      JobChainE Run r (k :: l) r''

theorem JobChainE.chain {σ : Type} {Run : Nat → σ → σ → Prop} :
    ∀ {r : σ} {l : List Nat} {r' : σ}, JobChainE Run r l r' → JobChain Run r l
  | _, _, _, .nil r => .nil r
  | _, _, _, .cons h hc => .cons h hc.chain

section pool

variable {pins : List INatOpPinSet} {pinsP : List ConLeche.NatOpPinSet}
  {ds : Array IDeclaration} {dsP : List ConLeche.Declaration} {I : IStreamIndex} {s₁ : AState}
  {σ : Type} {Rel : σ → AState → Prop} {Call : Nat → σ → σ → Prop}

/-- **A worker's chain with its end, refined** (`pool_walk`): the twin's `checkJobList` accepts
and ends in a worker's state related to the chain's end. -/
theorem pool_walkE (H : PoolHyps (pins := pins) (pinsP := pinsP) (ds := ds) (dsP := dsP) (I := I)
      (s₁ := s₁) Rel Call) :
    ∀ (l : List Nat) (r r' : σ) (a : AState), Rel r a → WorkerOK s₁ a → JobChainE Call r l r' →
      (∀ x ∈ l, x < ds.size ∧ PrefixOK pinsP dsP x ∧
        ((ConLeche.Cached.recsConsts (dsP.take x)).map (·.name)).Nodup) →
      ∃ a', checkJobList V pins none I ds l a = .ok (.ok (), a') ∧ Rel r' a' ∧ WorkerOK s₁ a' := by
  intro l
  induction l with
  | nil =>
    intro r r' a hr hw hc _
    cases hc
    exact ⟨a, rfl, hr, hw⟩
  | cons t rest ih =>
    intro r r'' a hr hw hc hl
    cases hc with
    | @cons _ _ r' _ _ hcall hrest =>
      obtain ⟨htk, hPt, hndt⟩ := hl t List.mem_cons_self
      obtain ⟨htk', hdk⟩ := H.hden t htk
      have hF := worker_foldOK H.hpinsOK H.hpersPins H.hI H.hpI htk' hPt hndt hw
      obtain ⟨a', hj, hr'⟩ := H.hstep t r r' a htk hr hcall hF
      obtain ⟨hw', -⟩ := job_spec H.hrec H.hpp H.hpinsOK H.hpersPins H.hpins H.hpd H.hI
        H.hpI hw htk htk' hdk hPt.envWF hndt hj
      obtain ⟨a'', hl', hr'', hw''⟩ := ih r' r'' a' hr' hw' hrest fun x hx => hl x (List.mem_cons_of_mem _ hx)
      exact ⟨a'', by rw [checkJobList_cons_ok htk hj]; exact hl', hr'', hw''⟩

/-- **The solution's pool, each worker with its end** (`pool_twin`): workers, each a start related
to the driver state's worker and a chain with its end, claims increasing, in range and covering:
every worker's list accepted from the driver state's worker, ending in a worker's state related
to the chain's end. -/
theorem pool_twinE (H : PoolHyps (pins := pins) (pinsP := pinsP) (ds := ds) (dsP := dsP) (I := I)
      (s₁ := s₁) Rel Call) (hst : StateOK s₁)
    (ths : List (σ × List Nat × σ)) (hstart : ∀ t ∈ ths, Rel t.1 s₁.worker)
    (hchain : ∀ t ∈ ths, JobChainE Call t.1 t.2.1 t.2.2) (hinc : ∀ t ∈ ths, t.2.1.Pairwise (· < ·))
    (hrange : ∀ t ∈ ths, ∀ k ∈ t.2.1, k < ds.size) (hcov : ∀ k < ds.size, ∃ t ∈ ths, k ∈ t.2.1) :
    ∀ t ∈ ths, ∃ a', checkJobList V pins none I ds t.2.1 s₁.worker = .ok (.ok (), a') ∧
      Rel t.2.2 a' ∧ WorkerOK s₁ a' := by
  let ths' := ths.map fun t => (t.1, t.2.1)
  have main := pool_prefix H hst ths' (fun t ht => by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht; exact hstart u hu)
    (fun t ht => by obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht; exact (hchain u hu).chain)
    (fun t ht => by obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht; exact hinc u hu) ds.size (Nat.le_refl _)
    (fun k hk => by
      obtain ⟨t, ht, hkt⟩ := hcov k hk
      exact ⟨_, List.mem_map_of_mem ht, hkt⟩)
  intro th hth
  exact pool_walkE H th.2.1 th.1 th.2.2 s₁.worker (hstart th hth) (WorkerOK.start hst) (hchain th hth)
    fun x hx => have := hrange th hth x hx; ⟨this, main x (by omega)⟩

end pool

section poolJ

variable {pins : List INatOpPinSet} {pinsP : List ConLeche.NatOpPinSet}
  {ds : Array IDeclaration} {dsP : List ConLeche.Declaration} {I : IStreamIndex} {s₁ : AState}
  {J : ISolution} {dsS : List ConLeche.Declaration}
  {matesU : Std.HashMap ConLeche.Name (Array ConLeche.Name)}
  {σ : Type} {Rel : σ → AState → Prop} {Call : Nat → σ → σ → Prop}

/-- **The challenge's induction, each worker from its own start, up to `n`** (`pool_prefixJ`):
workers, each a start state (a worker's state of the driver state) related to its chain's start,
with claims increasing and covering the positions below `n`: every prefix up to `n` a mixed run. -/
theorem pool_prefixJW (H : PoolHypsJ (pins := pins) (pinsP := pinsP) (ds := ds) (dsP := dsP) (I := I)
      (s₁ := s₁) (J := J) (dsS := dsS) (matesU := matesU) Rel Call)
    (ths : List (σ × AState × List Nat)) (hstart : ∀ t ∈ ths, Rel t.1 t.2.1 ∧ WorkerOK s₁ t.2.1)
    (hchain : ∀ t ∈ ths, JobChain Call t.1 t.2.2) (hinc : ∀ t ∈ ths, t.2.2.Pairwise (· < ·))
    (n : Nat) (hn : n ≤ ds.size) (hcov : ∀ k < n, ∃ t ∈ ths, k ∈ t.2.2) :
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
      obtain ⟨-, hds⟩ := pool_walkJL H (pre ++ [k]) th.1 th.2.1 (hstart th hth).1 (hstart th hth).2 hc
        fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · have := hpre x hx
            exact ⟨by omega, hbelow x (by omega)⟩
          · obtain rfl := List.mem_singleton.mp hx
            exact ⟨hks, hbelow x (Nat.le_refl _)⟩
      obtain ⟨hk', env', hd⟩ := hds k (by simp)
      exact MixedPrefix.step hk' (hbelow k (Nat.le_refl _)) hd
  exact fun k hk => main n (Nat.le_refl _) k hk

/-- **The challenge's pool, each worker from its own start** (`pool_twinJT`): every worker's list
accepted by the twin's `checkJobList` at the solution from its start. -/
theorem pool_twinJW (H : PoolHypsJ (pins := pins) (pinsP := pinsP) (ds := ds) (dsP := dsP) (I := I)
      (s₁ := s₁) (J := J) (dsS := dsS) (matesU := matesU) Rel Call)
    (ths : List (σ × AState × List Nat)) (hstart : ∀ t ∈ ths, Rel t.1 t.2.1 ∧ WorkerOK s₁ t.2.1)
    (hchain : ∀ t ∈ ths, JobChain Call t.1 t.2.2) (hinc : ∀ t ∈ ths, t.2.2.Pairwise (· < ·))
    (hrange : ∀ t ∈ ths, ∀ k ∈ t.2.2, k < ds.size) (hcov : ∀ k < ds.size, ∃ t ∈ ths, k ∈ t.2.2) :
    ∀ t ∈ ths, ∃ s'', checkJobList V pins (some J) I ds t.2.2 t.2.1 = .ok (.ok (), s'') := by
  have main := pool_prefixJW H ths hstart hchain hinc ds.size (Nat.le_refl _) hcov
  intro th hth
  exact (pool_walkJL H th.2.2 th.1 th.2.1 (hstart th hth).1 (hstart th hth).2 (hchain th hth)
    fun x hx => have := hrange th hth x hx; ⟨this, main x (by omega)⟩).1

end poolJ

end L.Arena
