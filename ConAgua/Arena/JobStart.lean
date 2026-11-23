module

public import ConAgua.Arena.PoolJobs

@[expose] public section

/-!
# A worker's start (stage 3 of lane ronsync2)

Every job opens with `enterScratch`, which keeps only the store, the caches and the pins of the
state it starts from (it opens a fresh scratch tier and resets the walk memos). So two states that agree on
those three (`SameEnter`) run every job, and every nonempty list of jobs, alike
(`recordJob_sameEnter`, `checkJobList_sameEnter`). A worker (`AState.worker`) agrees so with the state with its caches emptied
(`sameEnter_worker`): the jobs' relation need not hold at the worker itself, only at a state that
enters the scratch tier as it does (`JobRel`, `recCall_stepE`).
-/

open ConRon.Arena ConRon.Bridge

namespace L.Arena

/-- Two states that enter the scratch tier alike. -/
def SameEnter (a a' : AState) : Prop :=
  a.store.enableScratch = a'.store.enableScratch ∧ a.caches = a'.caches ∧ a.pins = a'.pins

theorem SameEnter.refl (a : AState) : SameEnter a a := ⟨rfl, rfl, rfl⟩

theorem SameEnter.symm {a a' : AState} (h : SameEnter a a') : SameEnter a' a :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

theorem SameEnter.st {a a' : AState} (h : SameEnter a a') :
    AM.st enterScratch a = AM.st enterScratch a' := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [AM.st, enterScratch_run, EStore.reset, ite_true]
  cases a; cases a'; simp_all

theorem recordJob_sameEnter {mode : ConLeche.CheckMode} {pins : List INatOpPinSet} {J : Option ISolution}
    {I : IStreamIndex} {k : Nat} {d : IDeclaration} {a a' : AState} (h : SameEnter a a') :
    recordJob mode pins J I k d a = recordJob mode pins J I k d a' := by
  have e := h.st
  simp only [AM.st, enterScratch_run] at e
  have e1 := enterScratch_run a
  have e2 := enterScratch_run a'
  simp only [recordJob, bind, StateT.bind]
  rw [show enterScratch a = _ from e1, show enterScratch a' = _ from e2, e]

theorem checkJobList_sameEnter {mode : ConLeche.CheckMode} {pins : List INatOpPinSet} {J : Option ISolution}
    {I : IStreamIndex} {ds : Array IDeclaration} {a a' : AState} (h : SameEnter a a') :
    ∀ {l : List Nat}, l ≠ [] → checkJobList mode pins J I ds l a = checkJobList mode pins J I ds l a'
  | [], hl => absurd rfl hl
  | t :: rest, _ => by
    have hr : runJob mode pins J I ds t a = runJob mode pins J I ds t a' := by
      simp only [runJob]
      split
      · rw [recordJob_sameEnter h]
      · rfl
    show (match runJob mode pins J I ds t a with
      | .ok (.ok (), s') => checkJobList mode pins J I ds rest s'
      | .ok (.error e, s') => .ok (.error e, s')
      | .error e => .error e) = (match runJob mode pins J I ds t a' with
      | .ok (.ok (), s') => checkJobList mode pins J I ds rest s'
      | .ok (.error e, s') => .ok (.error e, s')
      | .error e => .error e)
    rw [hr]

theorem enableScratch_dropScratch (st : EStore) : st.dropScratch.enableScratch = st.enableScratch := rfl

/-- A worker enters the scratch tier as its state with the caches emptied. -/
theorem sameEnter_worker {a : AState} : SameEnter a.worker { a with caches := Caches.empty } :=
  ⟨enableScratch_dropScratch a.store, rfl, rfl⟩

/-- An accepting list from one state accepts from a state that enters alike. -/
theorem checkJobList_ok_of_sameEnter {mode : ConLeche.CheckMode} {pins : List INatOpPinSet} {J : Option ISolution}
    {I : IStreamIndex} {ds : Array IDeclaration} {a a' s' : AState} {l : List Nat}
    (h : SameEnter a a') (hr : checkJobList mode pins J I ds l a = .ok (.ok (), s')) :
    ∃ s'', checkJobList mode pins J I ds l a' = .ok (.ok (), s'') := by
  rcases l with _ | ⟨t, rest⟩
  · exact ⟨a', rfl⟩
  · exact ⟨s', by rw [← checkJobList_sameEnter h (by simp)]; exact hr⟩

/-- A failing list from one state fails alike from a state that enters alike. -/
theorem twinFailsV_of_sameEnter {mode : ConLeche.CheckMode} {pins : List INatOpPinSet} {J : Option ISolution}
    {I : IStreamIndex} {ds : Array IDeclaration} {a a' : AState} {l : List Nat} {c : Word}
    (h : SameEnter a a') (hf : TwinFailsV (checkJobList mode pins J I ds l) a c) :
    TwinFailsV (checkJobList mode pins J I ds l) a' c := by
  rcases l with _ | ⟨t, rest⟩
  · rcases hf with ⟨ce, he, -⟩ | ⟨ce, i, a'', he, -⟩ <;> cases he
  · have e : (checkJobList mode pins J I ds (t :: rest)).run a' =
        (checkJobList mode pins J I ds (t :: rest)).run a :=
      (checkJobList_sameEnter h (by simp)).symm
    unfold TwinFailsV; rw [e]; exact hf

local notation "V" => ConLeche.CheckMode.verified

/-- **The jobs' relation up to the scratch entry**: `JobPost` at a state that enters the scratch
tier as `a` does. -/
def JobRel (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)
    (J : Option ISolution) (I : IStreamIndex) (a₀ : AState) (m : Mem) (a : AState) : Prop :=
  ∃ a', JobPost pins dn ds J I a₀ m a' ∧ SameEnter a' a

/-- **`record_job` calls as the pool's step** over `JobRel` (`recCall_step` through
`recordJob_sameEnter`). -/
theorem recCall_stepE {pins : List INatOpPinSet} {pinsP : List ConLeche.NatOpPinSet}
    {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration} {p : Prog} {J : Option ISolution}
    {I : IStreamIndex}
    (hP : JobProg pins dn ds p) (hFD : FrontDecls ds) (hLD : DeclsLpsDn dn ds) (hdn : DnPers dn)
    (hpp : PersPinSets pins) (hds : ds.size < 2 ^ 64)
    {a₀ : AState} (hden : ∀ x ∈ ds.toList, PersDecl x ∧ ∃ d, Frontend.denoteDecl a₀.store x = some d)
    (hPD : PinsDenote a₀.store pins pinsP) (hrec : JobSpec pins pinsP J a₀)
    (hcrs : CrsFor pins dn ds p J) :
    ∀ (k : Nat) (r r' : Mem) (a : AState) (hk : k < ds.size), JobRel pins dn ds J I a₀ r a →
      RecCall p k r r' → (∃ env, FoldOK env (I.view k) (AM.st enterScratch a)) →
      ∃ a', recordJob V pins J I k ds[k] a = .ok ((), a') ∧ JobRel pins dn ds J I a₀ r' a' := by
  intro k r r' a hk ⟨a₁, hJ, hS⟩ hc hF
  rw [← hS.st] at hF
  obtain ⟨a', hrun, hJ'⟩ := recCall_step hP hFD hLD hdn hpp hds hden hPD hrec hcrs k r r' a₁ hk hJ hc hF
  exact ⟨a', by rw [← recordJob_sameEnter hS]; exact hrun, a', hJ', SameEnter.refl _⟩

end L.Arena
