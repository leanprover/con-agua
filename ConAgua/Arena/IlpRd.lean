import ConAgua.Arena.IndRealAbs

/-!
# How a model's `inst_lp_fast` call is read (lane `indstaget`, helper `rcC`)

A model calling `inst_lp_fast` reads the call through `cR : CallM` (`IndCallM.lean`). Its
relational lemma (`StageR`) takes the call's contract as a hypothesis `IlpRd cR … Pre`: at a call
point satisfying `Pre` (what the model's lemma knows there beyond `StageR`, e.g. `IlpBase`: the
twin state of the lemma's start and an `IW`-only frame from its start memory), the call refines
`instLPFast`, keeps `StageR`, writes no stage memo and keeps `AbsOK`.

* `IlpRd.stub`: the stubs' reading (`instLPFast_spec`, `stubM_memoFrame`, `stub_afr`), any `Pre`.
* `IlpRd.real` (`IlpRdReal.lean`): the program's own reading, from `StageT` at the base point
  (lane `indproofs4`'s `ilpfF_okT`).
-/

open ConRon.Arena

namespace L.Ind

open L.Arena

/-- A frame away from the stage memos (arrays 201‥208, `CTL` words 202‥219): `stubM_memoFrame`'s
shape. -/
def StageMemoFr (m m' : Mem) : Prop :=
  ∃ (A : List ArrId) (C : List Word), (∀ b ∈ A, b < 201 ∨ 208 < b) ∧
    (∀ x ∈ C, x.toNat < 202 ∨ 219 < x.toNat) ∧ MemFrame A C m m'

/-- **The contract of a reading of `inst_lp_fast`** at every exec fuel, at call points satisfying
`Pre`. -/
def IlpRd (cR : CallM) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (Pre : Mem → AState → Prop) : Prop :=
  ∀ (k : Nat) (f o l us e : Word) (ks : List NIdx) (m m' : Mem) (a : AState) (r : List Word), H us → H e →
    Pre m a → StageR dn vis fe m a → decHL m o.toNat l.toNat = some ks →
    cR k "inst_lp_fast" [f, o, l, us, e] m = some (r, m') →
    ∃ x a', (instLPFast f.toNat ks (decI us) (decI e)).run a = .ok (x, a') ∧
      KeepPost dn vis fe decW0E m m' a' r x ∧ StageMemoFr m m' ∧ AFr m m'

/-- The call points of a model whose callees before `inst_lp_fast` write only the record pool and
leave the twin state: the start's twin state, an `IW` frame from the start memory. -/
def IlpBase (m₀ : Mem) (a₀ : AState) (m : Mem) (a : AState) : Prop :=
  a = a₀ ∧ MemFrame [IW] [200] m₀ m

/-- **Every call of a reading of `inst_lp_fast` writes no stage memo.** -/
def IlpFr (cR : CallM) : Prop :=
  ∀ (k : Nat) (args : List Word) (m m' : Mem) (r : List Word), cR k "inst_lp_fast" args m = some (r, m') →
    StageMemoFr m m'

theorem IlpRd.mono {cR : CallM} {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {Pre Pre' : Mem → AState → Prop} (h : IlpRd cR dn vis fe Pre)
    (hP : ∀ m a, Pre' m a → Pre m a) : IlpRd cR dn vis fe Pre' :=
  fun k f o l us e ks m m' a r hu he hp => h k f o l us e ks m m' a r hu he (hP m a hp)

/-- `IlpBase` along a further `IW` frame. -/
theorem IlpBase.iw {m₀ m m' : Mem} {a₀ a : AState} (h : IlpBase m₀ a₀ m a)
    (hf : MemFrame [IW] [200] m m') : IlpBase m₀ a₀ m' a :=
  ⟨h.1, h.2.trans hf⟩

theorem IlpBase.refl (m₀ : Mem) (a₀ : AState) : IlpBase m₀ a₀ m₀ a₀ := ⟨rfl, MemFrame.refl _ _ _⟩

theorem erCopyW_iwFr : ∀ (n : Nat) (m m' : Mem) (d s l : Word), erCopyW n m d s l = some m' →
    MemFrame [IW] [200] m m'
  | 0, _, _, _, _, _, h => by simp [erCopyW] at h
  | n + 1, m, m', d, s, l, h => by
    by_cases hl : l = 0
    · rw [erCopyW_nil n m d s l hl] at h; cases h; exact MemFrame.refl _ _ _
    · rw [erCopyW_step n m d s l hl] at h
      exact (set64IW_frame _ _ _).trans (erCopyW_iwFr n _ _ _ _ _ h)

/-- `er_to_iw` writes the record pool only. -/
theorem erToIwW_iwFr {n : Nat} {m m' : Mem} {o l : Word} {r : List Word}
    (h : erToIwW n m o l = some (r, m')) : MemFrame [IW] [200] m m' := by
  unfold erToIwW at h
  split at h; · simp at h
  rename_i q m1 hal
  split at h; · simp at h
  rename_i m2 hc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact (allocW_iwFrame hal).trans (erCopyW_iwFr _ _ _ _ _ _ hc)

/-- `stripPis` reads the store only: a successful run leaves the twin state. -/
theorem stripPis_st : ∀ (k : Nat) (h : EIdx) (a a' : AState) (x : Option (List EIdx × EIdx)),
    (ConRon.Arena.stripPis k h).run a = .ok (x, a') → a' = a := by
  intro k
  induction k with
  | zero => intro h a a' x hr; simp [ConRon.Arena.stripPis, StateT.run, pure, StateT.pure, Except.pure] at hr; exact hr.2.symm
  | succ k ih =>
    intro h a a' x hr
    simp only [ConRon.Arena.stripPis] at hr
    split at hr
    · simp only [viewBind, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_pure] at hr
      split at hr
      · simp [failDanglingE, fail, StateT.run, throwThe, MonadExceptOf.throw, StateT.lift, Functor.map, Except.map] at hr
      · rename_i ty b _
        cases hk : (ConRon.Arena.stripPis k b).run a with
        | error e => rw [StateT.run_bind, hk] at hr; simp [bind, Except.bind] at hr
        | ok q =>
          obtain ⟨y, a1⟩ := q
          have := ih b a a1 y hk
          subst this
          rw [StateT.run_bind, hk] at hr
          cases y <;> simp [bind, Except.bind, StateT.run, pure, StateT.pure, Except.pure] at hr <;> exact hr.2.symm
    · simp [StateT.run, pure, StateT.pure, Except.pure] at hr; exact hr.2.symm

end L.Ind
