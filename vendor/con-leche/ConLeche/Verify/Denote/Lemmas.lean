module

public import ConLeche.Verify.Denote

public section

/-!
# The `denote` lemma battery (task #161, P3.2)

The fixed lemma surface the model tier consumes `denote` through,
beside the clause equations (`Verify/Denote.lean`): inversions and
application spines.  Fuel-free, and the binder inversions conclude
`ea = .pi ta ba` (resp. `.lam ta ba`) *definitionally*.  Every premise
is one the *reading itself* needs (`hacl`: leaf lift-invariance;
`FindPreserved`/`LitGuardsAgree`: the constant and literal clauses read
the environment).
-/

namespace ConLeche.Verify

open ConLeche.Term ConLeche.Verify

open ConLeche (CheckMode Env Expr Name Level PropWhen ProjEntry)

variable {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → Term}

/-! ## Inversions -/

theorem denote_app_inv {d : Nat} {f a : Expr} {ea : Term}
    (h : denote acval env φ d (.app f a) = some ea) :
    ∃ fa aa, denote acval env φ d f = some fa ∧
      denote acval env φ d a = some aa ∧ ea = .app fa aa := by
  rw [denote] at h
  cases hf : denote acval env φ d f with
  | none => rw [hf] at h; exact nomatch h
  | some fa =>
    cases ha : denote acval env φ d a with
    | none => rw [hf, ha] at h; exact nomatch h
    | some aa =>
      rw [hf, ha] at h
      exact ⟨fa, aa, rfl, rfl, (Option.some.inj h).symm⟩

theorem denote_proj_inv {d : Nat} {s : Name} {i : Nat} {e : Expr}
    {ea : Term}
    (h : denote acval env φ d (.proj s i e) = some ea) :
    ∃ ia entry, denote acval env φ d e = some ia ∧ env.findProj? s i = some entry ∧
      ea = projNV (i + 1) ia := by
  rw [denote] at h
  cases he : denote acval env φ d e with
  | none => rw [he] at h; exact nomatch h
  | some ia =>
    rw [he] at h
    replace h : (match env.findProj? s i with
        | some _ => some (projNV (i + 1) ia)
        | none => none)
          = some ea := h
    cases hfp : env.findProj? s i with
    | some entry =>
      rw [hfp] at h
      dsimp only at h
      exact ⟨ia, entry, rfl, rfl, (Option.some.inj h).symm⟩
    | none =>
      rw [hfp] at h
      exact nomatch h

theorem denote_forallE_inv {d : Nat} {ty bd : Expr}
    {ea : Term}
    (h : denote acval env φ d (.forallE ty bd) = some ea) :
    ∃ ta ba, denote acval env φ d ty = some ta ∧
      denote acval env φ (d + 1)
        (bd.instantiate1 (.fvar d ty)) = some ba ∧
      ea = .pi ta ba := by
  rw [denote] at h
  cases ht : denote acval env φ d ty with
  | none => rw [ht] at h; exact nomatch h
  | some ta =>
    cases hb : denote acval env φ (d + 1)
        (bd.instantiate1 (.fvar d ty)) with
    | none => rw [ht, hb] at h; exact nomatch h
    | some ba =>
      rw [ht, hb] at h
      exact ⟨ta, ba, rfl, rfl, (Option.some.inj h).symm⟩

theorem denote_lam_inv {d : Nat} {ty bd : Expr}
    {ea : Term}
    (h : denote acval env φ d (.lam ty bd) = some ea) :
    ∃ ta ba, denote acval env φ d ty = some ta ∧
      denote acval env φ (d + 1)
        (bd.instantiate1 (.fvar d ty)) = some ba ∧
      ea = .lam ta ba := by
  rw [denote] at h
  cases ht : denote acval env φ d ty with
  | none => rw [ht] at h; exact nomatch h
  | some ta =>
    cases hb : denote acval env φ (d + 1)
        (bd.instantiate1 (.fvar d ty)) with
    | none => rw [ht, hb] at h; exact nomatch h
    | some ba =>
      rw [ht, hb] at h
      exact ⟨ta, ba, rfl, rfl, (Option.some.inj h).symm⟩

theorem denote_letE_inv {d : Nat} {ty v bd : Expr} {ea : Term}
    (h : denote acval env φ d (.letE ty v bd) = some ea) :
    ∃ ta va ba, denote acval env φ d ty = some ta ∧
      denote acval env φ d v = some va ∧
      denote acval env φ (d + 1)
        (bd.instantiate1 (.fvar d ty)) = some ba ∧
      ea = .letE va ba := by
  rw [denote] at h
  cases ht : denote acval env φ d ty with
  | none => rw [ht] at h; exact nomatch h
  | some ta =>
  cases hv : denote acval env φ d v with
  | none => rw [ht, hv] at h; exact nomatch h
  | some va =>
    cases hb : denote acval env φ (d + 1)
        (bd.instantiate1 (.fvar d ty)) with
    | none => rw [ht, hv, hb] at h; exact nomatch h
    | some ba =>
      rw [ht, hv, hb] at h
      exact ⟨ta, va, ba, rfl, rfl, rfl, (Option.some.inj h).symm⟩

theorem denote_natLit_inv {d n : Nat} {ea : Term}
    (h : denote acval env φ d (.lit (.natVal n)) = some ea) :
    natLitSupported env = true ∧
      ea = natLitT (acval natZeroName (Level.substFn φ [] []))
        (acval natSuccName (Level.substFn φ [] [])) n := by
  rw [denote] at h
  split at h
  · next hg => exact ⟨hg, (Option.some.inj h).symm⟩
  · exact nomatch h

/-! ## The spine kit

Application spines at the stored-term reading.  Fuel-free, so the
inversion is one induction and the reconciliation of two readings is
`Option.some.inj`. -/

/-- Each expression of a spine reads to the corresponding entry. -/
inductive DenoteSpine (acval : Name → (Name → Nat) → Term)
    (env : Env) (φ : Name → Nat) (d : Nat) :
    List Expr → List Term → Prop
  | nil : DenoteSpine acval env φ d [] []
  | cons {a : Expr} {v : Term} {as : List Expr} {vs : List Term} :
      denote acval env φ d a = some v →
      DenoteSpine acval env φ d as vs →
      DenoteSpine acval env φ d (a :: as) (v :: vs)

/-- A read spine has the length of its source. -/
theorem DenoteSpine.length {acval : Name → (Name → Nat) → Term}
    {d : Nat} {as : List Expr} {vs : List Term}
    (h : DenoteSpine acval env φ d as vs) : as.length = vs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- **The application spine, inverted at the stored-term reading**: the
head and every argument read, and the value is their `Term`
application. -/
theorem denote_mkAppN_inv {acval : Name → (Name → Nat) → Term}
    {d : Nat} : ∀ {as : List Expr} {f : Expr} {ea : Term},
    denote acval env φ d (Expr.mkAppN f as) = some ea →
    ∃ fa vs, denote acval env φ d f = some fa ∧
      DenoteSpine acval env φ d as vs ∧ ea = Term.mkAppN fa vs := by
  intro as
  induction as with
  | nil => intro f ea h; exact ⟨ea, [], h, .nil, rfl⟩
  | cons a as ih =>
    intro f ea h
    obtain ⟨fa, vs, hfa, hsp, rfl⟩ := ih h
    obtain ⟨ff, aa, hff, haa, rfl⟩ := denote_app_inv hfa
    exact ⟨ff, aa :: vs, hff, .cons haa hsp, rfl⟩

theorem DenoteSpine.take {acval : Name → (Name → Nat) → Term}
    {d : Nat} {as : List Expr} {vs : List Term}
    (h : DenoteSpine acval env φ d as vs) :
    ∀ n, DenoteSpine acval env φ d (as.take n) (vs.take n) := by
  induction h with
  | nil => intro n; simpa using DenoteSpine.nil
  | @cons a v as vs ha _ ih =>
    intro n
    cases n with
    | zero => exact DenoteSpine.nil
    | succ n => exact DenoteSpine.cons ha (ih n)

theorem DenoteSpine.drop {acval : Name → (Name → Nat) → Term}
    {d : Nat} {as : List Expr} {vs : List Term}
    (h : DenoteSpine acval env φ d as vs) :
    ∀ n, DenoteSpine acval env φ d (as.drop n) (vs.drop n) := by
  induction h with
  | nil => intro n; simpa using DenoteSpine.nil
  | @cons a v as vs ha htl ih =>
    intro n
    cases n with
    | zero => exact DenoteSpine.cons ha htl
    | succ n => exact ih n

theorem DenoteSpine.append {acval : Name → (Name → Nat) → Term}
    {d : Nat} {as bs : List Expr} {vs ws : List Term}
    (h : DenoteSpine acval env φ d as vs)
    (h2 : DenoteSpine acval env φ d bs ws) :
    DenoteSpine acval env φ d (as ++ bs) (vs ++ ws) := by
  induction h with
  | nil => exact h2
  | cons ha _ ih => exact DenoteSpine.cons ha ih

/-- A mapped spine reads pointwise. -/
theorem DenoteSpine.map_list {acval : Name → (Name → Nat) → Term}
    {d : Nat} {β : Type _} {g : β → Expr} {G : β → Term} :
    ∀ l : List β, (∀ j ∈ l, denote acval env φ d (g j) = some (G j)) →
      DenoteSpine acval env φ d (l.map g) (l.map G) := by
  intro l
  induction l with
  | nil => intro _; exact DenoteSpine.nil
  | cons x xs ih =>
    intro h
    exact DenoteSpine.cons (h x (by simp))
      (ih fun j hj => h j (by simp [hj]))

/-- **The application spine reads, constructing direction** —
`denote_mkAppN_inv`'s converse, the one the fabricated projection
spine needs. -/
theorem denote_mkAppN {acval : Name → (Name → Nat) → Term} {d : Nat}
    {as : List Expr} {vs : List Term}
    (h : DenoteSpine acval env φ d as vs) :
    ∀ {f : Expr} {fa : Term}, denote acval env φ d f = some fa →
      denote acval env φ d (Expr.mkAppN f as) = some (Term.mkAppN fa vs) := by
  induction h with
  | nil => intro f fa hf; exact hf
  | cons ha _ ih =>
    intro f fa hf
    exact ih (by rw [denote_app, hf, ha]; rfl)

/-- A read spine reads at every slot. -/
theorem DenoteSpine.getD {acval : Name → (Name → Nat) → Term} {d : Nat}
    {as : List Expr} {vs : List Term}
    (h : DenoteSpine acval env φ d as vs) :
    ∀ (dflt : Expr) (i : Nat), i < as.length →
      denote acval env φ d (as.getD i dflt) = some (vs.getD i default) := by
  induction h with
  | nil => intro dflt i hi; exact absurd hi (by simp)
  | @cons a v as vs ha _ ih =>
    intro dflt i hi
    match i with
    | 0 => exact ha
    | j + 1 => exact ih dflt j (by simpa using hi)

/-- The clause at a stored entry: the uniform iterated projection of
the subject's reading. -/
theorem denote_proj_tower {d : Nat} {s : Name} {i : Nat} {e : Expr}
    {entry : ProjEntry} {ia : Term}
    (hfe : env.findProj? s i = some entry)
    (he : denote acval env φ d e = some ia) :
    denote acval env φ d (.proj s i e) = some (projNV (i + 1) ia) := by
  rw [denote_proj, he]
  show (match env.findProj? s i with
    | some _ => some (projNV (i + 1) ia)
    | none => none)
      = some (projNV (i + 1) ia)
  rw [hfe]

/-- A read spine extended by one read argument. -/
theorem DenoteSpine.snoc {d : Nat} {as : List Expr} {vs : List Term}
    {a : Expr} {v : Term}
    (h : DenoteSpine acval env φ d as vs)
    (ha : denote acval env φ d a = some v) :
    DenoteSpine acval env φ d (as ++ [a]) (vs ++ [v]) := by
  induction h with
  | nil => exact .cons ha .nil
  | cons h1 _ ih => exact .cons h1 ih

/-- The `k`-th argument of a read spine reads to the `k`-th reading. -/
theorem DenoteSpine.getD_read {d : Nat} :
    ∀ {as : List Expr} {vs : List Term}, DenoteSpine acval env φ d as vs →
      ∀ {k : Nat}, k < as.length →
        denote acval env φ d (as.getD k (.bvar 0))
          = some (vs.getD k default)
  | _, _, .nil, k, hk => absurd hk (Nat.not_lt_zero k)
  | _, _, .cons ha _, 0, _ => by simpa [List.getD] using ha
  | _, _, .cons _ hsp, k + 1, hk => by
    simpa [List.getD] using
      DenoteSpine.getD_read hsp (Nat.lt_of_succ_lt_succ hk)

/-- An application spine splits at any point. -/
theorem _root_.ConLeche.Term.Term.mkAppN_append (f : Term) :
    ∀ (as bs : List Term),
      Term.mkAppN f (as ++ bs) = Term.mkAppN (Term.mkAppN f as) bs
  | [], _ => rfl
  | _ :: as, bs => mkAppN_append _ as bs

end ConLeche.Verify
