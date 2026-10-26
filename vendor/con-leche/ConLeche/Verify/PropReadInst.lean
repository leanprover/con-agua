module

public import ConLeche.Verify.PropRead
import ConLeche.Verify.InstLevels
import ConLeche.Verify.PropWhen
public import ConLeche.Verify.EnvWF
import ConLeche.Kernel.PropWhen

public section

/-!
# The head-symbol prop-ness readers under substitution (task #342 L18)

What the "a proof" arm's model justification (`prf_of_isProofFast`,
`ConLeche/Model/Rules/ProofFastSound.lean`) needs of the readers
(`ConLeche/Kernel/PropRead.lean`): an answer they give on a term is
still given after the term's loose bound variable is instantiated
(opening a binder, β, ζ) and after the term's level parameters are
instantiated (a stored type at its constant's levels).  Only the
direction "the raw term answered" is needed, and only that direction
holds: instantiating a `bvar` head can make a term the reader did not
read readable.
-/

namespace ConLeche

open Expr

/-! ## Instantiating a bound variable -/

/-- A constant-headed spine keeps its head and instantiates its
arguments. -/
theorem getApp_instantiate1_of_const {v : Expr} {k : Nat} {c : Name}
    {us : List Level} :
    ∀ {e : Expr}, e.getAppFn = .const c us →
      (e.instantiate1 v k).getAppFn = .const c us ∧
        (e.instantiate1 v k).getAppArgs = e.getAppArgs.map (·.instantiate1 v k)
  | .const _ _, h => by
    cases h; exact ⟨rfl, rfl⟩
  | .app f a, h => by
    have ih := getApp_instantiate1_of_const (v := v) (k := k) (e := f) h
    simp only [instantiate1, getAppFn, getAppArgs, List.map_append, List.map_cons,
      List.map_nil] at ih ⊢
    exact ⟨ih.1, by rw [ih.2]⟩
  | .bvar _, h | .fvar _ _, h | .sort _, h | .lam _ _, h | .forallE _ _, h
  | .letE _ _ _, h | .lit _, h | .proj _ _ _, h => nomatch h

/-- A spine whose head is no constant and not the instantiated `bvar`
keeps a head that is no constant. -/
theorem getAppFn_instantiate1_not_const {v : Expr} {k : Nat} :
    ∀ {e : Expr}, (∀ c us, e.getAppFn ≠ .const c us) → e.getAppFn ≠ .bvar k →
      ∀ c us, (e.instantiate1 v k).getAppFn ≠ .const c us
  | .app f a, h1, h2 => by
    simp only [instantiate1, getAppFn] at h1 h2 ⊢
    exact getAppFn_instantiate1_not_const h1 h2
  | .bvar i, _, h2 => by
    intro c us h
    simp only [getAppFn] at h2
    simp only [instantiate1] at h
    split at h
    · next hi => exact h2 (by rw [hi])
    · split at h <;> exact nomatch h
  | .const c' us', h1, _ => absurd rfl (h1 c' us')
  | .fvar _ _, _, _ | .sort _, _, _ | .lam _ _, _, _ | .forallE _ _, _, _
  | .letE _ _ _, _, _ | .lit _, _, _ | .proj _ _ _, _, _ => by
    intro c us h; simp [instantiate1, getAppFn] at h

theorem getD_map_instantiate1 {v : Expr} {k : Nat} (l : List Expr) (i : Nat)
    (dflt : Expr) (hi : i < l.length) :
    (l.map (·.instantiate1 v k)).getD i (dflt.instantiate1 v k) =
      (l.getD i dflt).instantiate1 v k := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]

/-- **The wrapper unfolding commutes with instantiating a bound
variable**, unless the unfolded term's head is that variable. -/
theorem unwrapIdDefs_instantiate1 (find? : Name → Option ConstantInfo) {v : Expr}
    {k : Nat} :
    ∀ (fuel : Nat) (e : Expr),
      unwrapIdDefs find? fuel (e.instantiate1 v k) =
          (unwrapIdDefs find? fuel e).instantiate1 v k ∨
        (unwrapIdDefs find? fuel e).getAppFn = .bvar k := by
  intro fuel
  induction fuel with
  | zero => intro e; exact Or.inl rfl
  | succ fuel ih =>
    intro e
    by_cases hc : ∃ c us, e.getAppFn = .const c us
    · obtain ⟨c, us, hh⟩ := hc
      obtain ⟨hfn, hargs⟩ := getApp_instantiate1_of_const (v := v) (k := k) hh
      simp only [unwrapIdDefs, hfn, hh, hargs, List.length_map]
      cases find? c with
      | none => exact Or.inl rfl
      | some ci =>
        cases ci <;> try exact Or.inl rfl
        case defnInfo cv val hint =>
          dsimp only
          cases hlp : lamProj? 0 val with
          | none => exact Or.inl rfl
          | some kj =>
            obtain ⟨kk, j⟩ := kj
            dsimp only
            split
            · next hlen =>
              simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hlen
              have hj : j < kk := by
                have := lamProj?_lt hlp; omega
              rw [getD_map_instantiate1 _ _ _ (by omega)]
              exact ih _
            · exact Or.inl rfl
    · have hn : ∀ c us, e.getAppFn ≠ .const c us := fun c us h => hc ⟨c, us, h⟩
      rw [unwrapIdDefs_succ_of_not_const find? hn]
      by_cases hb : e.getAppFn = .bvar k
      · exact Or.inr hb
      · left
        exact unwrapIdDefs_succ_of_not_const find?
          (getAppFn_instantiate1_not_const hn hb)
where
  lamProj?_lt : ∀ {k₀ : Nat} {e : Expr} {kk j : Nat},
      lamProj? k₀ e = some (kk, j) → j < kk
    | k₀, .lam _ b, kk, j, h => lamProj?_lt (k₀ := k₀ + 1) (e := b) h
    | k₀, .bvar i, kk, j, h => by
      simp only [lamProj?] at h
      split at h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); assumption
      · exact nomatch h
    | _, .fvar _ _, _, _, h | _, .sort _, _, _, h | _, .const _ _, _, _, h
    | _, .app _ _, _, _, h | _, .forallE _ _, _, _, h | _, .letE _ _ _, _, _, h
    | _, .lit _, _, _, h | _, .proj _ _ _, _, _, h => nomatch h

/-- **A peeled sort survives instantiating a bound variable.** -/
theorem peelPisW_sort_instantiate1 (find? : Name → Option ConstantInfo)
    {v : Expr} :
    ∀ (n : Nat) (e : Expr) (k : Nat) {u : Level},
      peelPisW find? n e = some (.sort u) →
      peelPisW find? n (e.instantiate1 v k) = some (.sort u) := by
  intro n
  induction n with
  | zero =>
    intro e k u h
    simp only [peelPisW] at h ⊢
    have hu' : unwrapIdDefs find? 4 e = .sort u := Option.some.inj h
    rcases unwrapIdDefs_instantiate1 find? (v := v) (k := k) 4 e with h' | h'
    · rw [h', hu']; rfl
    · rw [hu'] at h'; exact nomatch h'
  | succ n ih =>
    intro e k u h
    rw [peelPisW_succ_eq] at h ⊢
    revert h
    cases hu : unwrapIdDefs find? 4 e with
    | forallE ty b =>
      intro h
      rcases unwrapIdDefs_instantiate1 find? (v := v) (k := k) 4 e with h' | h'
      · rw [h', hu]
        exact ih b (k + 1) h
      · rw [hu] at h'; exact nomatch h'
    | _ => intro h; exact nomatch h

/-- **A residual sort survives instantiating a bound variable.** -/
theorem residualPW_peelPisW_instantiate1 (find? : Name → Option ConstantInfo)
    {v : Expr} (n : Nat) (e : Expr) (k : Nat) {pw : PropWhen}
    (h : residualPW (peelPisW find? n e) = some pw) :
    residualPW (peelPisW find? n (e.instantiate1 v k)) = some pw := by
  obtain ⟨u, hu, rfl⟩ := residualPW_some_inv h
  rw [peelPisW_sort_instantiate1 find? n e k hu]
  rfl

/-- A telescope's binder domain instantiates with it. -/
theorem binderDom_instantiate1 {v : Expr} :
    ∀ (j : Nat) (e : Expr) (k : Nat) {D : Expr}, e.binderDom j = some D →
      (e.instantiate1 v k).binderDom j = some (D.instantiate1 v (k + j))
  | 0, .forallE A _, k, D, h => by
    simp only [binderDom] at h; cases h; rfl
  | j + 1, .forallE _ b, k, D, h => by
    simp only [binderDom, instantiate1] at h ⊢
    rw [binderDom_instantiate1 j b (k + 1) h]
    congr 2; omega
  | 0, .bvar _, _, _, h | 0, .fvar _ _, _, _, h | 0, .sort _, _, _, h
  | 0, .const _ _, _, _, h | 0, .app _ _, _, _, h | 0, .lam _ _, _, _, h
  | 0, .letE _ _ _, _, _, h | 0, .lit _, _, _, h | 0, .proj _ _ _, _, _, h
  | _ + 1, .bvar _, _, _, h | _ + 1, .fvar _ _, _, _, h | _ + 1, .sort _, _, _, h
  | _ + 1, .const _ _, _, _, h | _ + 1, .app _ _, _, _, h | _ + 1, .lam _ _, _, _, h
  | _ + 1, .letE _ _ _, _, _, h | _ + 1, .lit _, _, _, h
  | _ + 1, .proj _ _ _, _, _, h => nomatch h

/-- Instantiating a variable that is not the head keeps the arity. -/
theorem numArgs_instantiate1 {v : Expr} {k : Nat} :
    ∀ {e : Expr}, e.getAppFn ≠ .bvar k → (e.instantiate1 v k).numArgs = e.numArgs
  | .app f a, h => by
    simp only [instantiate1, numArgs, getAppFn] at h ⊢
    rw [numArgs_instantiate1 h]
  | .bvar i, h => by
    simp only [getAppFn] at h
    simp only [instantiate1]
    split
    · next hi => exact absurd (by rw [hi]) h
    · split <;> rfl
  | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .lam _ _, _ | .forallE _ _, _
  | .letE _ _ _, _ | .lit _, _ | .proj _ _ _, _ => rfl

/-- Instantiating the head variable by a variable keeps the arity. -/
theorem numArgs_instantiate1_head {i : Nat} {t : Expr} {k : Nat} :
    ∀ {e : Expr}, e.getAppFn = .bvar k →
      (e.instantiate1 (.fvar i t) k).numArgs = e.numArgs ∧
        (e.instantiate1 (.fvar i t) k).getAppFn = .fvar i t
  | .app f a, h => by
    simp only [instantiate1, numArgs, getAppFn] at h ⊢
    obtain ⟨h1, h2⟩ := numArgs_instantiate1_head h
    exact ⟨by rw [h1], h2⟩
  | .bvar j, h => by
    simp only [getAppFn] at h
    cases h
    simp [instantiate1, numArgs, getAppFn]
  | .fvar _ _, h | .sort _, h | .const _ _, h | .lam _ _, h | .forallE _ _, h
  | .letE _ _ _, h | .lit _, h | .proj _ _ _, h => nomatch h

/-- The head of an instantiated spine whose head is not the variable. -/
theorem getAppFn_instantiate1_of_ne {v : Expr} {k : Nat} :
    ∀ {e : Expr}, e.getAppFn ≠ .bvar k →
      (e.instantiate1 v k).getAppFn = e.getAppFn.instantiate1 v k
  | .app f a, h => by
    simp only [instantiate1, getAppFn] at h ⊢
    exact getAppFn_instantiate1_of_ne h
  | .bvar i, h => by
    simp only [getAppFn] at h
    simp only [instantiate1, getAppFn]
    split
    · next hi => exact absurd (by rw [hi]) h
    · split <;> rfl
  | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .lam _ _, _ | .forallE _ _, _
  | .letE _ _ _, _ | .lit _, _ | .proj _ _ _, _ => rfl

/-- The walk at a type that is neither a ∀ nor a sort reads its head. -/
theorem typeSortPWGo_eq_head (find? : Name → Option ConstantInfo) (root : Expr)
    (d : Nat) :
    ∀ {X : Expr}, (∀ ty b, X ≠ .forallE ty b) → (∀ u, X ≠ .sort u) →
      typeSortPWGo find? root X d = headTypePW find? root d X.getAppFn X.numArgs
  | .forallE ty b, h1, _ => absurd rfl (h1 ty b)
  | .sort u, _, h2 => absurd rfl (h2 u)
  | .bvar _, _, _ | .fvar _ _, _, _ | .const _ _, _, _ | .app _ _, _, _
  | .lam _ _, _, _ | .letE _ _ _, _, _ | .lit _, _, _ | .proj _ _ _, _, _ => rfl

theorem not_forallE_instantiate1_of_fvar {i : Nat} {t : Expr} {j : Nat} :
    ∀ {X : Expr}, (∀ ty b, X ≠ .forallE ty b) →
      ∀ ty b, X.instantiate1 (.fvar i t) j ≠ .forallE ty b
  | .bvar k, _, ty, b, h => by
    simp only [instantiate1] at h
    split at h
    · exact nomatch h
    · split at h <;> exact nomatch h
  | .forallE ty₀ b₀, h1, _, _, _ => absurd rfl (h1 ty₀ b₀)
  | .fvar _ _, _, _, _, h | .sort _, _, _, _, h | .const _ _, _, _, _, h
  | .app _ _, _, _, _, h | .lam _ _, _, _, _, h | .letE _ _ _, _, _, _, h
  | .lit _, _, _, _, h | .proj _ _ _, _, _, _, h => by
    simp [instantiate1] at h

theorem not_sort_instantiate1_of_fvar {i : Nat} {t : Expr} {j : Nat} :
    ∀ {X : Expr}, (∀ u, X ≠ .sort u) → ∀ u, X.instantiate1 (.fvar i t) j ≠ .sort u
  | .bvar k, _, u, h => by
    simp only [instantiate1] at h
    split at h
    · exact nomatch h
    · split at h <;> exact nomatch h
  | .sort u₀, h1, _, _ => absurd rfl (h1 u₀)
  | .fvar _ _, _, _, h | .forallE _ _, _, _, h | .const _ _, _, _, h
  | .app _ _, _, _, h | .lam _ _, _, _, h | .letE _ _ _, _, _, h
  | .lit _, _, _, h | .proj _ _ _, _, _, h => by
    simp [instantiate1] at h

/-- The opening at a residual (neither a ∀ nor a sort): the head. -/
theorem typeSortPWGo_open_head (find? : Name → Option ConstantInfo) {A B : Expr}
    {i : Nat} {X : Expr} {j : Nat} {pw : PropWhen}
    (h1 : ∀ ty b, X ≠ .forallE ty b) (h2 : ∀ u, X ≠ .sort u)
    (h : typeSortPWGo find? (.forallE A B) X (j + 1) = some pw) :
    typeSortPWGo find? (B.instantiate1 (.fvar i A)) (X.instantiate1 (.fvar i A) j) j
      = some pw := by
  rw [typeSortPWGo_eq_head find? _ _ h1 h2] at h
  rw [typeSortPWGo_eq_head find? _ _ (not_forallE_instantiate1_of_fvar h1)
    (not_sort_instantiate1_of_fvar h2)]
  by_cases hb : X.getAppFn = .bvar j
  · obtain ⟨hn, hf⟩ := numArgs_instantiate1_head (i := i) (t := A) hb
    rw [hn, hf]
    rw [hb] at h
    simpa [headTypePW, binderDom] using h
  · rw [numArgs_instantiate1 hb, getAppFn_instantiate1_of_ne hb]
    revert h
    cases hfn : X.getAppFn with
    | bvar k =>
      intro h
      simp only [headTypePW] at h
      split at h
      · next hk =>
        have hkj : k < j := by
          have : k ≠ j := fun e => hb (by rw [hfn, e])
          omega
        rw [show j + 1 - 1 - k = (j - 1 - k) + 1 by omega] at h
        simp only [binderDom] at h
        revert h
        cases hD : B.binderDom (j - 1 - k) with
        | none => intro h; exact nomatch h
        | some D =>
          intro h
          have hD' := binderDom_instantiate1 (v := .fvar i A) (j - 1 - k) B 0 hD
          simp only [instantiate1, show ¬ (k = j) from fun e => hb (by rw [hfn, e]),
            show ¬ (k > j) by omega, ↓reduceIte, headTypePW, hkj, hD']
          exact residualPW_peelPisW_instantiate1 find? _ D _ h
      · exact nomatch h
    | fvar idx ty => intro h; simpa [instantiate1, headTypePW] using h
    | const c us => intro h; simpa [instantiate1, headTypePW] using h
    | sort _ | app _ _ | lam _ _ | forallE _ _ | letE _ _ _ | lit _ | proj _ _ _ =>
      intro h; simp [headTypePW] at h

/-- **Opening a ∀'s outermost binder keeps the reader's answer**
(`typeSortPWGo`'s telescope `bvar` heads become the opening variable,
whose carried type is the binder's domain). -/
theorem typeSortPWGo_open (find? : Name → Option ConstantInfo) {A B : Expr}
    {i : Nat} :
    ∀ (X : Expr) (j : Nat) {pw : PropWhen},
      typeSortPWGo find? (.forallE A B) X (j + 1) = some pw →
      typeSortPWGo find? (B.instantiate1 (.fvar i A)) (X.instantiate1 (.fvar i A) j) j
        = some pw := by
  intro X
  induction X with
  | forallE ty b _ ihb =>
    intro j pw h
    simp only [typeSortPWGo, instantiate1] at h ⊢
    exact ihb (j + 1) h
  | sort u => intro j pw h; simpa [typeSortPWGo, instantiate1] using h
  | bvar k =>
    intro j pw h
    exact typeSortPWGo_open_head find? (fun _ _ h => nomatch h) (fun _ h => nomatch h) h
  | fvar k t =>
    intro j pw h
    exact typeSortPWGo_open_head find? (fun _ _ h => nomatch h) (fun _ h => nomatch h) h
  | const c us =>
    intro j pw h
    exact typeSortPWGo_open_head find? (fun _ _ h => nomatch h) (fun _ h => nomatch h) h
  | app f a _ _ =>
    intro j pw h
    exact typeSortPWGo_open_head find? (fun _ _ h => nomatch h) (fun _ h => nomatch h) h
  | lam t b _ _ =>
    intro j pw h
    exact typeSortPWGo_open_head find? (fun _ _ h => nomatch h) (fun _ h => nomatch h) h
  | letE t v b _ _ _ =>
    intro j pw h
    exact typeSortPWGo_open_head find? (fun _ _ h => nomatch h) (fun _ h => nomatch h) h
  | lit l =>
    intro j pw h
    exact typeSortPWGo_open_head find? (fun _ _ h => nomatch h) (fun _ h => nomatch h) h
  | proj s k e _ =>
    intro j pw h
    exact typeSortPWGo_open_head find? (fun _ _ h => nomatch h) (fun _ h => nomatch h) h

/-- **The reader's answer at a ∀ is its opened body's.** -/
theorem typeSortPW_forallE_open (find? : Name → Option ConstantInfo) {A B : Expr}
    (i : Nat) {pw : PropWhen}
    (h : typeSortPW find? (.forallE A B) = some pw) :
    typeSortPW find? (B.instantiate1 (.fvar i A)) = some pw := by
  unfold typeSortPW at h ⊢
  simp only [typeSortPWGo] at h
  exact typeSortPWGo_open find? B 0 h

/-! ## The proof reader under instantiation -/

/-- The number of λ, `let` and application layers the proof reader
walks through before it reads a head. -/
@[expose] def Expr.proofDepth : Expr → Nat
  | .lam _ b => proofDepth b + 1
  | .letE _ _ b => proofDepth b + 1
  | .app f _ => proofDepth f + 1
  | _ => 0

/-- **The proof reader's answer survives instantiating a bound
variable**, at the same depth (its heads are never that variable). -/
theorem proofPW_instantiate1 (find? : Name → Option ConstantInfo)
    (findTable? : Name → Option ProjTable) {v : Expr} :
    ∀ (b : Expr) (k : Nat) {pw : PropWhen}, proofPW find? findTable? b = some pw →
      proofPW find? findTable? (b.instantiate1 v k) = some pw ∧
        (b.instantiate1 v k).proofDepth = b.proofDepth := by
  intro b
  induction b with
  | lam t b _ ihb =>
    intro k pw h
    simp only [proofPW, instantiate1, Expr.proofDepth] at h ⊢
    obtain ⟨h1, h2⟩ := ihb (k + 1) h
    exact ⟨h1, by rw [h2]⟩
  | letE t x b _ _ ihb =>
    intro k pw h
    simp only [proofPW, instantiate1, Expr.proofDepth] at h ⊢
    obtain ⟨h1, h2⟩ := ihb (k + 1) h
    exact ⟨h1, by rw [h2]⟩
  | app f x ihf _ =>
    intro k pw h
    simp only [proofPW, instantiate1, Expr.proofDepth] at h ⊢
    obtain ⟨h1, h2⟩ := ihf k h
    exact ⟨h1, by rw [h2]⟩
  | bvar i => intro k pw h; simp [proofPW, headProofPW] at h
  | fvar i t => intro k pw h; exact ⟨h, rfl⟩
  | const c us => intro k pw h; exact ⟨h, rfl⟩
  | sort u => intro k pw h; exact ⟨h, rfl⟩
  | lit l => intro k pw h; exact ⟨h, rfl⟩
  | forallE t b _ _ => intro k pw h; exact ⟨h, rfl⟩
  | proj sn i e _ => intro k pw h; exact ⟨h, rfl⟩

/-! ## Instantiating level parameters -/

theorem getD_map_instantiateLevelParams (ks : List Name) (us : List Level)
    (l : List Expr) (i : Nat) (dflt : Expr) :
    (l.map (·.instantiateLevelParams ks us)).getD i (dflt.instantiateLevelParams ks us)
      = (l.getD i dflt).instantiateLevelParams ks us := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map]

theorem getAppFn_instantiateLevelParams_not_const (ks : List Name) (us : List Level)
    {e : Expr} (h : ∀ c vs, e.getAppFn ≠ .const c vs) :
    ∀ c vs, (e.instantiateLevelParams ks us).getAppFn ≠ .const c vs := by
  intro c vs hc
  rw [getAppFn_instantiateLevelParams] at hc
  cases hf : e.getAppFn <;> rw [hf] at hc <;>
    simp only [Expr.instantiateLevelParams, reduceCtorEq] at hc
  case const c' vs' => exact h c' vs' hf

theorem unwrapIdDefs_instantiateLevelParams (find? : Name → Option ConstantInfo)
    (ks : List Name) (us : List Level) :
    ∀ (fuel : Nat) (e : Expr),
      unwrapIdDefs find? fuel (e.instantiateLevelParams ks us) =
        (unwrapIdDefs find? fuel e).instantiateLevelParams ks us := by
  intro fuel
  induction fuel with
  | zero => intro e; rfl
  | succ fuel ih =>
    intro e
    by_cases hc : ∃ c vs, e.getAppFn = .const c vs
    · obtain ⟨c, vs, hh⟩ := hc
      have hfn : (e.instantiateLevelParams ks us).getAppFn =
          .const c (vs.map (Level.subst ks us)) := by
        rw [getAppFn_instantiateLevelParams, hh]; rfl
      simp only [unwrapIdDefs, hfn, hh, getAppArgs_instantiateLevelParams, List.length_map]
      cases find? c with
      | none => rfl
      | some ci =>
        cases ci <;> try rfl
        case defnInfo cv val hint =>
          dsimp only
          cases lamProj? 0 val with
          | none => rfl
          | some kj =>
            dsimp only
            split
            · rw [getD_map_instantiateLevelParams, ih]
            · rfl
    · have hn : ∀ c vs, e.getAppFn ≠ .const c vs := fun c vs h => hc ⟨c, vs, h⟩
      rw [unwrapIdDefs_succ_of_not_const find? hn,
        unwrapIdDefs_succ_of_not_const find?
          (getAppFn_instantiateLevelParams_not_const ks us hn)]

theorem peelPisW_instantiateLevelParams (find? : Name → Option ConstantInfo)
    (ks : List Name) (us : List Level) :
    ∀ (n : Nat) (e : Expr),
      peelPisW find? n (e.instantiateLevelParams ks us) =
        (peelPisW find? n e).map (·.instantiateLevelParams ks us) := by
  intro n
  induction n with
  | zero => intro e; simp [peelPisW, unwrapIdDefs_instantiateLevelParams]
  | succ n ih =>
    intro e
    rw [peelPisW_succ_eq, peelPisW_succ_eq, unwrapIdDefs_instantiateLevelParams]
    cases unwrapIdDefs find? 4 e with
    | forallE ty b => simp only [Expr.instantiateLevelParams, ih]
    | _ => rfl

theorem residualPW_map_instantiateLevelParams (ks : List Name) (us : List Level)
    (o : Option Expr) :
    residualPW (o.map (·.instantiateLevelParams ks us)) =
      (residualPW o).map (Level.substPW ks us) := by
  match o with
  | none => rfl
  | some e =>
    cases e <;> try rfl
    case sort u =>
      simp only [Option.map_some, Expr.instantiateLevelParams, residualPW]
      rw [Level.zeronessOf_subst]

theorem binderDom_instantiateLevelParams (ks : List Name) (us : List Level) :
    ∀ (k : Nat) (e : Expr),
      (e.instantiateLevelParams ks us).binderDom k =
        (e.binderDom k).map (·.instantiateLevelParams ks us) := by
  intro k e
  induction e generalizing k <;> cases k <;>
    simp_all [Expr.instantiateLevelParams, binderDom]

theorem numArgs_instantiateLevelParams (ks : List Name) (us : List Level) :
    ∀ (e : Expr), (e.instantiateLevelParams ks us).numArgs = e.numArgs := by
  intro e
  induction e <;> simp_all [Expr.instantiateLevelParams, numArgs]

/-- A spine's arguments keep their level parameters defined. -/
theorem allLevelParamsDefined_getAppArgs {ps : List Name} :
    ∀ {e : Expr}, e.allLevelParamsDefined ps = true →
      ∀ a ∈ e.getAppArgs, a.allLevelParamsDefined ps = true
  | .app f x, h, a, ha => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [getAppArgs, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact allLevelParamsDefined_getAppArgs h.1 a ha
    · exact h.2
  | .bvar _, _, _, ha | .fvar _ _, _, _, ha | .sort _, _, _, ha | .const _ _, _, _, ha
  | .lam _ _, _, _, ha | .forallE _ _, _, _, ha | .letE _ _ _, _, _, ha
  | .lit _, _, _, ha | .proj _ _ _, _, _, ha => by simp [getAppArgs] at ha

theorem allLevelParamsDefined_getD {ps : List Name} {e : Expr}
    (h : e.allLevelParamsDefined ps = true) (i : Nat) :
    (e.getAppArgs.getD i e).allLevelParamsDefined ps = true := by
  rw [List.getD_eq_getElem?_getD]
  cases hget : e.getAppArgs[i]? with
  | none => exact h
  | some a => exact allLevelParamsDefined_getAppArgs h a (List.mem_of_getElem? hget)

theorem allLevelParamsDefined_unwrapIdDefs (find? : Name → Option ConstantInfo)
    {ps : List Name} :
    ∀ (fuel : Nat) {e : Expr}, e.allLevelParamsDefined ps = true →
      (unwrapIdDefs find? fuel e).allLevelParamsDefined ps = true := by
  intro fuel
  induction fuel with
  | zero => intro e h; exact h
  | succ fuel ih =>
    intro e h
    simp only [unwrapIdDefs]
    split <;> try exact h
    split <;> try exact h
    split <;> try exact h
    split
    · next hlen =>
      exact ih (allLevelParamsDefined_getD h _)
    · exact h

theorem allLevelParamsDefined_peelPisW (find? : Name → Option ConstantInfo)
    {ps : List Name} :
    ∀ (n : Nat) {e r : Expr}, e.allLevelParamsDefined ps = true →
      peelPisW find? n e = some r → r.allLevelParamsDefined ps = true := by
  intro n
  induction n with
  | zero =>
    intro e r h hp
    simp only [peelPisW] at hp
    rw [← Option.some.inj hp]
    exact allLevelParamsDefined_unwrapIdDefs find? 4 h
  | succ n ih =>
    intro e r h hp
    rw [peelPisW_succ_eq] at hp
    have hu := allLevelParamsDefined_unwrapIdDefs find? 4 h
    revert hp hu
    cases unwrapIdDefs find? 4 e with
    | forallE ty b =>
      intro hp hu
      simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hu
      exact ih hu.2 hp
    | _ => intro hp; exact nomatch hp

theorem headTypePW_instantiateLevelParams {env : Env} (henv : EnvWF env)
    (ks : List Name) (us : List Level) (root : Expr) (d : Nat) (h : Expr) (n : Nat)
    {pw : PropWhen} (hh : headTypePW env.find? root d h n = some pw) :
    headTypePW env.find? (root.instantiateLevelParams ks us) d
        (h.instantiateLevelParams ks us) n = some (Level.substPW ks us pw) := by
  cases h with
  | const I vs =>
    simp only [headTypePW] at hh ⊢
    simp only [Expr.instantiateLevelParams]
    revert hh
    cases hfI : env.find? I with
    | none => intro hh; exact nomatch hh
    | some ci =>
      intro hh
      dsimp only at hh ⊢
      split at hh
      · next hlen =>
        rw [ite_eq_left (by rw [List.length_map]; exact hlen)]
        revert hh
        cases hres : residualPW (peelPisW env.find? n ci.toConstantVal.type) with
        | none => intro hh; exact nomatch hh
        | some p =>
          intro hh
          obtain rfl := Option.some.inj hh
          obtain ⟨u0, hpeel, rfl⟩ := residualPW_some_inv hres
          have hwf := henv.consts _ (List.mem_of_find?_eq_some hfI)
          have hdef := allLevelParamsDefined_peelPisW env.find? n hwf.2.1 hpeel
          simp only [Expr.allLevelParamsDefined] at hdef
          simp only [Option.map_some]
          rw [Level.substPW_comp hlen (Level.zeronessOf_paramsDefined hdef)]
      · exact nomatch hh
  | fvar idx ty =>
    simp only [headTypePW, Expr.instantiateLevelParams] at hh ⊢
    rw [peelPisW_instantiateLevelParams, residualPW_map_instantiateLevelParams, hh]
    rfl
  | bvar i =>
    simp only [headTypePW, Expr.instantiateLevelParams] at hh ⊢
    split at hh
    · next hi =>
      rw [ite_eq_left hi, binderDom_instantiateLevelParams]
      revert hh
      cases root.binderDom (d - 1 - i) with
      | none => intro hh; exact nomatch hh
      | some D =>
        intro hh
        simp only [Option.map_some] at hh ⊢
        rw [peelPisW_instantiateLevelParams, residualPW_map_instantiateLevelParams, hh]
        rfl
    · exact nomatch hh
  | sort _ | app _ _ | lam _ _ | forallE _ _ | letE _ _ _ | lit _ | proj _ _ _ =>
    simp [headTypePW] at hh

theorem typeSortPWGo_instantiateLevelParams_head {env : Env} (henv : EnvWF env)
    (ks : List Name) (us : List Level) (root : Expr) {X : Expr} {d : Nat}
    {pw : PropWhen} (h1 : ∀ ty b, X ≠ .forallE ty b) (h2 : ∀ u, X ≠ .sort u)
    (h : typeSortPWGo env.find? root X d = some pw) :
    typeSortPWGo env.find? (root.instantiateLevelParams ks us)
      (X.instantiateLevelParams ks us) d = some (Level.substPW ks us pw) := by
  have h1' : ∀ ty b, X.instantiateLevelParams ks us ≠ .forallE ty b := by
    intro ty b he
    cases X <;> simp only [Expr.instantiateLevelParams, reduceCtorEq] at he
    case forallE ty₀ b₀ => exact h1 ty₀ b₀ rfl
  have h2' : ∀ u, X.instantiateLevelParams ks us ≠ .sort u := by
    intro u he
    cases X <;> simp only [Expr.instantiateLevelParams, reduceCtorEq] at he
    case sort u₀ => exact h2 u₀ rfl
  rw [typeSortPWGo_eq_head _ _ _ h1 h2] at h
  rw [typeSortPWGo_eq_head _ _ _ h1' h2', getAppFn_instantiateLevelParams,
    numArgs_instantiateLevelParams]
  exact headTypePW_instantiateLevelParams henv ks us root d _ _ h

/-- **A stored type's prop-ness answer, at its constant's levels**: the
reader on the level-instantiated type answers the instantiated datum. -/
theorem typeSortPWGo_instantiateLevelParams {env : Env} (henv : EnvWF env)
    (ks : List Name) (us : List Level) (root : Expr) :
    ∀ (X : Expr) (d : Nat) {pw : PropWhen},
      typeSortPWGo env.find? root X d = some pw →
      typeSortPWGo env.find? (root.instantiateLevelParams ks us)
        (X.instantiateLevelParams ks us) d = some (Level.substPW ks us pw) := by
  intro X
  induction X with
  | forallE ty b _ ihb =>
    intro d pw h
    simp only [typeSortPWGo, Expr.instantiateLevelParams] at h ⊢
    exact ihb (d + 1) h
  | sort u =>
    intro d pw h
    simp only [typeSortPWGo, Expr.instantiateLevelParams] at h ⊢
    obtain rfl := Option.some.inj h
    rfl
  | bvar _ | fvar _ _ | const _ _ | app _ _ _ _ | lam _ _ _ _ | letE _ _ _ _ _ _
  | lit _ | proj _ _ _ _ =>
    intro d pw h
    exact typeSortPWGo_instantiateLevelParams_head henv ks us root
      (fun _ _ h => nomatch h) (fun _ h => nomatch h) h

/-- The reader at a stored type's level instantiation. -/
theorem typeSortPW_instantiateLevelParams {env : Env} (henv : EnvWF env)
    (ks : List Name) (us : List Level) {T : Expr} {pw : PropWhen}
    (h : typeSortPW env.find? T = some pw) :
    typeSortPW env.find? (T.instantiateLevelParams ks us) = some (Level.substPW ks us pw) :=
  typeSortPWGo_instantiateLevelParams henv ks us T T 0 h

end ConLeche
