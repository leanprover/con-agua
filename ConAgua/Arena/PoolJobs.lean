module

public import ConAgua.Arena.Jobs

@[expose] public section

/-!
# The pool's induction at the L level

con-ron's `pooled_fold` (Bridge/Checker/Pooled.lean) turns workers' accepted job lists into the
pure fold's accept. At the L level the twin's lists are not given: a worker's memory-level runs
return, and a run refines the twin's `recordJob` only where con-ron's fold invariant `FoldOK`
holds at the job's view, which needs every job below it accepted (in any worker). `pool_twin`
does the induction over positions: the workers' runs, each step refining `recordJob` under
`FoldOK` (`hstep`), with claims increasing in each worker, give every worker's list accepted by
the twin's `checkJobList` from the driver state's worker (con-ron's `PooledAccepts`' last part),
and the pure fold's prefixes. `pool_prefix` is the induction alone, up to a position `n`, from
workers whose claims cover the positions below `n` (the prefix below a failing job).

The worker's L-level state is abstract (`σ`, the relation `Rel`, the step `Call`): the threads'
entry 2 (one call per job) and the sequential `check_jobs` loop (one `record_job` call per job)
both instantiate it.
-/

open ConRon.Arena ConRon.Bridge

namespace L.Arena

universe w

local notation "V" => ConLeche.CheckMode.verified

/-- **`FoldOK` at a job's start**, from a worker's state at a position whose prefix the fold
accepted with distinct names (con-ron's `view_foldOK` at the scratch state, as in `job_spec`). -/
theorem worker_foldOK
    {pinsP : List ConLeche.NatOpPinSet} {dsP : List ConLeche.Declaration} {I : IStreamIndex}
    {s₁ a : AState} {k : Nat} (hpinsOK : PinsOK s₁) (hpersPins : PersPins s₁)
    (hI : IndexDenotes s₁.store I (ConLeche.Cached.buildIndex dsP.toArray))
    (hpI : PersIFBase I.base) (hk : k < dsP.length) (hP : PrefixOK pinsP dsP k)
    (hnd : ((ConLeche.Cached.recsConsts (dsP.take k)).map (·.name)).Nodup) (hw : WorkerOK s₁ a) :
    ∃ env, FoldOK env (I.view k) (AM.st enterScratch a) := by
  rw [show AM.st enterScratch a = AState.mk a.store.enableScratch Memos.empty a.caches a.pins from rfl]
  exact ⟨_, view_foldOK hpinsOK hpersPins hI hpI hk hP hnd ⟨EStore.enableScratch_wf hw.state.wf⟩
    (hw.pext.trans (PExt.enterScratch hw.state.wf)) (CacheOK.of_empty hw.caches) hw.pins⟩

section pool

variable {pins : List INatOpPinSet} {pinsP : List ConLeche.NatOpPinSet}
  {ds : Array IDeclaration} {dsP : List ConLeche.Declaration} {I : IStreamIndex} {s₁ : AState}
  {σ : Type} (Rel : σ → AState → Prop) (Call : Nat → σ → σ → Prop)

/-- What the pool's induction takes: the driver state's facts (as `pooled_fold_records`), and a
worker's step `Call k` refining `recordJob` of record `k` wherever `FoldOK` holds at its view. -/
structure PoolHyps : Prop where
  hrec : RecordSpec pins pinsP
  hpush : KernelPushes pinsP
  hpp : PersPinSets pins
  hpinsOK : PinsOK s₁
  hpersPins : PersPins s₁
  hpins : PinsDenote s₁.store pins pinsP
  hpd : ∀ x ∈ ds.toList, PersDecl x
  hlen : dsP.length = ds.size
  hden : ∀ (i : Nat) (hi : i < ds.size), ∃ hi' : i < dsP.length,
    Frontend.denoteDecl s₁.store ds[i] = some dsP[i]
  hI : IndexDenotes s₁.store I (ConLeche.Cached.buildIndex dsP.toArray)
  hpI : PersIFBase I.base
  hstep : ∀ (k : Nat) (r r' : σ) (a : AState) (hk : k < ds.size), Rel r a → Call k r r' →
    (∃ env, FoldOK env (I.view k) (AM.st enterScratch a)) →
    ∃ a', recordJob V pins none I k ds[k] a = .ok ((), a') ∧ Rel r' a'

variable {Rel Call}

/-- **A worker's chain, refined**: from a related worker's state, a chain of steps at positions
whose prefixes the fold accepted is the twin's `checkJobList` accepting, and each record's
`checkDecl` accepting at its prefix's environment. -/
theorem pool_walk (H : PoolHyps (pins := pins) (pinsP := pinsP) (ds := ds) (dsP := dsP) (I := I)
      (s₁ := s₁) Rel Call) :
    ∀ (l : List Nat) (r : σ) (a : AState), Rel r a → WorkerOK s₁ a → JobChain Call r l →
      (∀ x ∈ l, x < ds.size ∧ PrefixOK pinsP dsP x ∧
        ((ConLeche.Cached.recsConsts (dsP.take x)).map (·.name)).Nodup) →
      (∃ a', checkJobList V pins none I ds l a = .ok (.ok (), a')) ∧
      ∀ x ∈ l, ∃ (hx : x < dsP.length) (env' : ConLeche.Env) (F : Nat),
        ConLeche.checkDecl V (ConLeche.fueledOps V F) pinsP
          (ConLeche.streamEnv (dsP.take x)) dsP[x] = .ok env' := by
  intro l
  induction l with
  | nil => intro r a _ _ _ _; exact ⟨⟨a, rfl⟩, fun x hx => absurd hx (by simp)⟩
  | cons t rest ih =>
    intro r a hr hw hc hl
    cases hc with
    | @cons _ _ r' _ hcall hrest =>
      obtain ⟨htk, hPt, hndt⟩ := hl t List.mem_cons_self
      obtain ⟨htk', hdk⟩ := H.hden t htk
      have hF := worker_foldOK H.hpinsOK H.hpersPins H.hI H.hpI htk' hPt hndt hw
      obtain ⟨a', hj, hr'⟩ := H.hstep t r r' a htk hr hcall hF
      obtain ⟨hw', env', F, hd⟩ := job_spec H.hrec H.hpp H.hpinsOK H.hpersPins H.hpins H.hpd H.hI
        H.hpI hw htk htk' hdk hPt hndt hj
      obtain ⟨⟨a'', hl'⟩, hds⟩ := ih r' a' hr' hw' hrest fun x hx => hl x (List.mem_cons_of_mem _ hx)
      refine ⟨⟨a'', ?_⟩, fun x hx => ?_⟩
      · rw [checkJobList_cons_ok htk hj]; exact hl'
      · rcases List.mem_cons.mp hx with rfl | hx'
        · exact ⟨htk', env', F, hd⟩
        · exact hds x hx'

/-- A chain's prefix is a chain. -/
theorem JobChain.append_left {Run : Nat → σ → σ → Prop} :
    ∀ {l₁ l₂ : List Nat} {r : σ}, JobChain Run r (l₁ ++ l₂) → JobChain Run r l₁
  | [], _, r, _ => .nil r
  | _ :: _, _, _, .cons h hc => .cons h (JobChain.append_left hc)

/-- **The pool's induction up to `n`** (con-ron's `pooled_fold`, at the L level): workers, each a
start state related to the driver state's worker and a chain of steps (`ths`), with claims
increasing in each worker and covering the positions below `n`, give every prefix of the records
up to length `n` accepted by the pure fold with distinct names. -/
theorem pool_prefix (H : PoolHyps (pins := pins) (pinsP := pinsP) (ds := ds) (dsP := dsP) (I := I)
      (s₁ := s₁) Rel Call) (hst : StateOK s₁)
    (ths : List (σ × List Nat)) (hstart : ∀ t ∈ ths, Rel t.1 s₁.worker)
    (hchain : ∀ t ∈ ths, JobChain Call t.1 t.2) (hinc : ∀ t ∈ ths, t.2.Pairwise (· < ·))
    (n : Nat) (hn : n ≤ ds.size) (hcov : ∀ k < n, ∃ t ∈ ths, k ∈ t.2) :
    ∀ k ≤ n, PrefixOK pinsP dsP k ∧
      ((ConLeche.Cached.recsConsts (dsP.take k)).map (·.name)).Nodup := by
  have main : ∀ k, k ≤ n → ∀ t ≤ k, PrefixOK pinsP dsP t ∧
      ((ConLeche.Cached.recsConsts (dsP.take t)).map (·.name)).Nodup := by
    intro k
    induction k with
    | zero =>
      intro _ t ht
      obtain rfl : t = 0 := by omega
      have h0 : (ConLeche.Cached.recsConsts ([] : List ConLeche.Declaration)).length = 0 := by
        have := (ConLeche.Cached.buildIndex_spec (#[] : Array ConLeche.Declaration)).next
        simpa [ConLeche.Cached.buildIndex] using this.symm
      refine ⟨⟨0, fun _ _ => rfl⟩, ?_⟩
      rw [List.take_zero, List.eq_nil_of_length_eq_zero h0]
      exact List.nodup_nil
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
      obtain ⟨-, hds⟩ := pool_walk H (pre ++ [k]) th.1 s₁.worker (hstart th hth)
        (WorkerOK.start hst) hc fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · have := hpre x hx
            exact ⟨by omega, hbelow x (by omega)⟩
          · obtain rfl := List.mem_singleton.mp hx
            exact ⟨hks, hbelow x (Nat.le_refl _)⟩
      obtain ⟨hk', env', F, hd⟩ := hds k (by simp)
      obtain ⟨hPk, hndk⟩ := hbelow k (Nat.le_refl _)
      exact PrefixOK.step H.hpush hk' hPk hd hndk
  exact fun k hk => main n (Nat.le_refl _) k hk

/-- **The pool's induction** (con-ron's `pooled_fold`, at the L level): workers, each a start
state related to the driver state's worker and a chain of steps (`ths`), whose claims are positions
of the records, increase in each worker and cover the positions, give every prefix of the records
accepted by the pure fold with distinct names, and every worker's list accepted by the twin's
`checkJobList` from the driver state's worker. -/
theorem pool_twin (H : PoolHyps (pins := pins) (pinsP := pinsP) (ds := ds) (dsP := dsP) (I := I)
      (s₁ := s₁) Rel Call) (hst : StateOK s₁)
    (ths : List (σ × List Nat)) (hstart : ∀ t ∈ ths, Rel t.1 s₁.worker)
    (hchain : ∀ t ∈ ths, JobChain Call t.1 t.2) (hinc : ∀ t ∈ ths, t.2.Pairwise (· < ·))
    (hrange : ∀ t ∈ ths, ∀ k ∈ t.2, k < ds.size) (hcov : ∀ k < ds.size, ∃ t ∈ ths, k ∈ t.2) :
    (∀ k ≤ ds.size, PrefixOK pinsP dsP k ∧
      ((ConLeche.Cached.recsConsts (dsP.take k)).map (·.name)).Nodup) ∧
    ∀ t ∈ ths, ∃ s'', checkJobList V pins none I ds t.2 s₁.worker = .ok (.ok (), s'') := by
  have main := pool_prefix H hst ths hstart hchain hinc ds.size (Nat.le_refl _) hcov
  refine ⟨main, fun th hth => ?_⟩
  exact (pool_walk H th.2 th.1 s₁.worker (hstart th hth) (WorkerOK.start hst) (hchain th hth)
    fun x hx => have := hrange th hth x hx; ⟨this, main x (by omega)⟩).1

end pool

/-! ## The `check_jobs` loop as a worker -/

/-- **A `record_job(k)` call that returns**, at some fuel. -/
def RecCall (p : Prog) (k : Nat) (m m' : Mem) : Prop :=
  ∃ (n : Nat) (r : List Word), n ≤ 2 ^ 62 ∧ callE p n "record_job" [UInt64.ofNat k] m = .ok (r, m')

/-- **A returning `check_jobs` loop is a chain of `record_job` calls** over the jobs `j‥hi - 1`. -/
theorem checkJobsLoop_chain {p : Prog} {hi : Word} :
    ∀ (n : Nat), n ≤ 2 ^ 62 + 1 → ∀ (m : Mem) (j : Word) (q : Mem), checkJobsE.loop1 p n m j hi = .ok q →
      JobChain (RecCall p) m (List.range' j.toNat (hi.toNat - j.toNat)) := by
  intro n
  induction n with
  | zero =>
    intro _ m j q hq
    rw [checkJobsE.loop1.eq_1] at hq; cases hq
  | succ n ih =>
    intro hn m j q hq
    by_cases g : j < hi
    · rw [checkJobsE.loop1.arm1 _ _ _ _ _ g] at hq
      rw [range'_cons_word g]
      cases hc : callE p n "record_job" [j] m with
      | error e => rw [hc, checkJobsE.k_record_job.none] at hq; cases hq
      | ok q1 =>
        obtain ⟨r, m₁⟩ := q1
        rw [hc, checkJobsE.k_record_job.arm1] at hq
        exact .cons ⟨n, r, by omega, by rw [UInt64.ofNat_toNat]; exact hc⟩ (ih (by omega) m₁ (j + 1) q hq)
    · have : hi.toNat - j.toNat = 0 := by have : ¬ j.toNat < hi.toNat := g; omega
      rw [this]
      exact .nil m

/-- **`record_job` calls as the pool's step**, from the job relation (`JobPost` from `a₀`) and the
facts `recordJob_ref` takes, at `a₀`. -/
theorem recCall_step {pins : List INatOpPinSet} {pinsP : List ConLeche.NatOpPinSet}
    {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration} {p : Prog} {I : IStreamIndex}
    (hP : JobProg pins dn ds p) (hFD : FrontDecls ds) (hLD : DeclsLpsDn dn ds) (hdn : DnPers dn)
    (hrec : RecordSpec pins pinsP) (hpp : PersPinSets pins) (hds : ds.size < 2 ^ 64)
    {a₀ : AState} (hden : ∀ x ∈ ds.toList, PersDecl x ∧ ∃ d, Frontend.denoteDecl a₀.store x = some d)
    (hPD : PinsDenote a₀.store pins pinsP) :
    ∀ (k : Nat) (r r' : Mem) (a : AState) (hk : k < ds.size), JobPost pins dn ds I a₀ r a →
      RecCall p k r r' → (∃ env, FoldOK env (I.view k) (AM.st enterScratch a)) →
      ∃ a', recordJob V pins none I k ds[k] a = .ok ((), a') ∧ JobPost pins dn ds I a₀ r' a' := by
  intro k r r' a hk ⟨hJ, hx, hp⟩ ⟨n, rs, hn, hc⟩ hF
  have hkw : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt (Nat.lt_trans hk hds)
  have hden' : ∀ x ∈ ds.toList, PersDecl x ∧ ∃ d, Frontend.denoteDecl a.store x = some d :=
    fun x hx' => by
      obtain ⟨h1, d, h2⟩ := hden x hx'
      exact ⟨h1, d, denoteDecl_pext hx h1 h2⟩
  have hPD' := PinsDenote.pmono hx pins pinsP hpp hPD
  have hk' : (UInt64.ofNat k).toNat < ds.size := by rw [hkw]; exact hk
  have hr := recordJob_ref hP hFD hLD hdn hrec hpp (N := n) hn hk' hJ (by rw [hkw]; exact hF) hden' hPD'
  rw [hc] at hr
  obtain ⟨u, a₁, hrun, hJ₁, hx₁, hp₁⟩ := hr
  refine ⟨a₁, ?_, hJ₁, hx.trans hx₁, hp₁.trans hp⟩
  have e : recordJob V pins none I (UInt64.ofNat k).toNat ds[(UInt64.ofNat k).toNat] = recordJob V pins none I k ds[k] := by
    simp only [hkw]
  rw [← e]; cases u; exact hrun

end L.Arena
