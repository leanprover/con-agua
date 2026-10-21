module

public import ConLeche.Verify.Denote.Depth
import ConLeche.Verify.Denote.Shift
public import ConLeche.Verify.Subst
import ConLeche.Verify.Denote

public section

/-!
# `denote` commutes with instantiation (task #161, P3 batch 2)

The substitution crossing the β/ζ clauses of the P-tier step proof run
through.

**It does not cost `EnvWF`.**  Same reason as `denote_shiftFrom`
(`Verify/Denote/Depth.lean`): `denote`'s binder clauses read only the
binder's domain and body, which `Expr.substFvarAt` substitutes
structurally, so each closes by the recursion alone.

**It costs two leaf premises.**

* `hainst : ∀ n ψ y k, (acval n ψ).inst y k = acval n ψ` is what the
  `.const` and `.lit` clauses read.
* `hacl : ∀ n ψ k, (acval n ψ).liftN 1 k = acval n ψ` is what the
  **`fvar`-at-`p` clause** reads, through `denote_lift` below.
  On `Term` neither invariance implies the other (`inst`-invariance
  at every cut is the stronger of the two, but extracting the lift from
  it is a fresh induction, not a rewrite).

Both are discharged from one closedness fact at every real supplier:
`Term.liftN_eq_self` and `Term.inst_eq_self`
(`Verify/Denote/VClosed.lean`) take the same
`Term.bvarsBelow k (acval n ψ)` hypothesis, and `hacl` is
`EnvModel.acval_closed`, read off the `cval_closed` field.

## Where the arithmetic lands

At depth `D + 1` the variable
`fvar p` denotes `.bvar (D - p)`, so the substitution happens at cut
`k = D - p`, and `Term.inst e a k` already substitutes `liftN k a`
— which makes `inst`'s built-in lift *be* the depth shift.
-/

namespace ConLeche.Term.Term

/-! ### Two lift identities the depth-lift needs

Nothing before this file iterated a lift on `Term`. -/

/-- A zero lift is the identity. -/
theorem liftN_zero : ∀ (e : Term) (k : Nat), liftN 0 e k = e := by
  intro e
  induction e with
  | bvar i => intro k; simp only [liftN_bvar]; split <;> rfl
  | sort u => intro _; rfl
  | const c us => intro _; rfl
  | prf => intro _; rfl
  | app f a ihf iha => intro k; rw [liftN_app, ihf, iha]
  | lam A b ihA ihb => intro k; rw [liftN_lam, ihA, ihb]
  | pi A B ihA ihB => intro k; rw [liftN_pi, ihA, ihB]
  | letE v b ihv ihb => intro k; rw [liftN_letE, ihv, ihb]
  | eqE a b iha ihb => intro k; rw [liftN_eqE, iha, ihb]
  | fst e ihe => intro k; rw [liftN_fst, ihe]
  | snd e ihe => intro k; rw [liftN_snd, ihe]

/-- Two lifts at the same cut compose. -/
theorem liftN_liftN : ∀ (e : Term) (n m k : Nat),
    liftN n (liftN m e k) k = liftN (n + m) e k := by
  intro e
  induction e with
  | bvar i =>
    intro n m k
    simp only [liftN_bvar]
    by_cases h : i < k
    · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h, ite_eq_right (show ¬ i + m < k from by omega)]
      congr 1
      omega
  | sort u => intro _ _ _; rfl
  | const c us => intro _ _ _; rfl
  | prf => intro _ _ _; rfl
  | app f a ihf iha =>
    intro n m k; rw [liftN_app, liftN_app, ihf, iha]; rfl
  | lam A b ihA ihb =>
    intro n m k; rw [liftN_lam, liftN_lam, ihA, ihb]; rfl
  | pi A B ihA ihB =>
    intro n m k; rw [liftN_pi, liftN_pi, ihA, ihB]; rfl
  | letE v b ihv ihb =>
    intro n m k; rw [liftN_letE, liftN_letE, ihv, ihb]; rfl
  | eqE a b iha ihb =>
    intro n m k; rw [liftN_eqE, liftN_eqE, iha, ihb]; rfl
  | fst e ihe =>
    intro n m k; rw [liftN_fst, liftN_fst, ihe]; rfl
  | snd e ihe =>
    intro n m k; rw [liftN_snd, liftN_snd, ihe]; rfl

end ConLeche.Term.Term

namespace ConLeche.Verify


open ConLeche.Term ConLeche.Verify

open ConLeche (Env Expr Name Level PropWhen)

variable {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → Term}

/-- The `Nat`-literal spine is `inst`-invariant when its two heads
are.  `Verify/Denote/Depth.lean`'s `natLitT_liftN` one operation over. -/
private theorem natLitT_inst {za sa y : Term} {k : Nat}
    (hz : za.inst y k = za) (hs : sa.inst y k = sa) :
    ∀ n : Nat, (natLitT za sa n).inst y k = natLitT za sa n := by
  intro n
  induction n with
  | zero => exact hz
  | succ n ih =>
    show (Term.app sa (natLitT za sa n)).inst y k = _
    rw [Term.inst_app, hs, ih]
    rfl

/-- Ditto the character-list spine. -/
private theorem charListT_inst {nilA consA ofNatA za sa y : Term}
    {k : Nat} (hn : nilA.inst y k = nilA)
    (hc : consA.inst y k = consA) (ho : ofNatA.inst y k = ofNatA)
    (hz : za.inst y k = za) (hs : sa.inst y k = sa) :
    ∀ cs : List Char,
      (charListT nilA consA ofNatA za sa cs).inst y k
        = charListT nilA consA ofNatA za sa cs := by
  intro cs
  induction cs with
  | nil => exact hn
  | cons c cs ih =>
    show (Term.app (.app consA (.app ofNatA _)) _).inst y k = _
    rw [Term.inst_app, Term.inst_app, Term.inst_app, hc, ho,
      natLitT_inst hz hs, ih]
    rfl

/-- **Depth lifting for `denote`**, iterated out of
`denote_weaken_top`.  The scoping premise is `WScoped` because that
is what `denote_shiftFrom` takes (the annotations have to be scoped
too, hereditarily). -/
theorem denote_lift
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    {p : Nat} {e : Expr} (hw : Expr.WScoped p e) :
    ∀ D : Nat, p ≤ D →
      denote acval env φ D e
        = (denote acval env φ p e).map (Term.liftN (D - p) · 0) := by
  intro D
  induction D with
  | zero =>
    intro hpD
    have hp : p = 0 := by omega
    subst hp
    simp only [Nat.sub_self]
    cases denote acval env φ 0 e with
    | none => rfl
    | some v => simp only [Option.map_some, Term.liftN_zero]
  | succ D ih =>
    intro hpD
    by_cases hpD' : p = D + 1
    · subst hpD'
      simp only [Nat.sub_self]
      cases denote acval env φ (D + 1) e with
      | none => rfl
      | some v => simp only [Option.map_some, Term.liftN_zero]
    · have hpD2 : p ≤ D := by omega
      rw [denote_weaken_top hacl (hw.mono hpD2), ih hpD2]
      cases denote acval env φ p e with
      | none => rfl
      | some v =>
        simp only [Option.map_some, Term.liftN_liftN]
        congr 2
        omega

/-- **The substitution lemma, at the stored-term reading.**
Substituting the expression `a` for `fvar p` corresponds to
instantiating the reading at de Bruijn cut `D - p`.  See the module
docstring for the two leaf premises and for why `EnvWF` is absent. -/
theorem denote_substFvarAt
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : Term) (k : Nat),
      (acval n ψ).inst y k = acval n ψ)
    {p : Nat} {a : Expr} {x : Term}
    (hwa : Expr.WScoped p a) (hba : a.looseBVarsBounded 0 = true)
    (ha : denote acval env φ p a = some x) :
    ∀ (e : Expr) (D : Nat), p ≤ D → Expr.fvarsBelow (D + 1) e →
      denote acval env φ D (Expr.substFvarAt p a e) =
        (denote acval env φ (D + 1) e).map (Term.inst · x (D - p))
  | .bvar i, D, hpD, hfb => by
    have h1 : denote acval env φ D (.bvar i) = none := by
      rw [denote.eq_def]
    have h2 : denote acval env φ (D + 1) (.bvar i) = none := by
      rw [denote.eq_def]
    simp [ConLeche.Expr.substFvarAt, h1, h2]
  | .sort u, D, hpD, hfb => by
    simp only [ConLeche.Expr.substFvarAt, denote, Option.map_some]
    rfl
  | .const n us, D, hpD, hfb => by
    simp only [ConLeche.Expr.substFvarAt, denote]
    cases env.find? n with
    | none => rfl
    | some ci =>
      dsimp only
      split
      · simp only [Option.map_some, hainst]
      · rfl
  | .fvar idx ty, D, hpD, hfb => by
    have hlt : idx < D + 1 := hfb
    by_cases h1 : idx = p
    · subst h1
      rw [show ConLeche.Expr.substFvarAt idx a (Expr.fvar idx ty) = a from by
            simp [ConLeche.Expr.substFvarAt],
        denote_lift hacl hwa D hpD, ha, denote]
      simp only [Option.map_some, Term.inst_bvar,
        show D + 1 - 1 - idx = D - idx from by omega]
      simp
    · by_cases h2 : idx > p
      · rw [show ConLeche.Expr.substFvarAt p a (Expr.fvar idx ty)
              = .fvar (idx - 1) (ConLeche.Expr.substFvarAt p a ty) from by
              simp [ConLeche.Expr.substFvarAt, h1, h2],
          denote, denote]
        simp only [Option.map_some, Term.inst_bvar,
          ite_eq_left (show D + 1 - 1 - idx < D - p from by omega)]
        congr 2
        omega
      · rw [show ConLeche.Expr.substFvarAt p a (Expr.fvar idx ty)
              = .fvar idx ty from by
              simp [ConLeche.Expr.substFvarAt, h1, h2],
          denote, denote]
        simp only [Option.map_some, Term.inst_bvar,
          ite_eq_right (show ¬ D + 1 - 1 - idx < D - p from by omega),
          ite_eq_right (show ¬ D + 1 - 1 - idx = D - p from by omega)]
        congr 2
        omega
  | .app fe b, D, hpD, hfb => by
    simp only [ConLeche.Expr.substFvarAt, denote]
    rw [denote_substFvarAt hacl hainst hwa hba ha fe D hpD hfb.1,
      denote_substFvarAt hacl hainst hwa hba ha b D hpD hfb.2]
    cases denote acval env φ (D + 1) fe <;>
      cases denote acval env φ (D + 1) b <;> rfl
  | .forallE ty body, D, hpD, hfb => by
    simp only [ConLeche.Expr.substFvarAt, denote]
    rw [denote_substFvarAt hacl hainst hwa hba ha ty D hpD hfb.1,
      ← ConLeche.Expr.substFvarAt_instantiate1 hpD hba body 0,
      denote_substFvarAt hacl hainst hwa hba ha
        (body.instantiate1 (.fvar (D + 1) ty)) (D + 1) (by omega)
        (ConLeche.Expr.fvarsBelow_instantiate1 0 hfb.2),
      show D + 1 - p = D - p + 1 from by omega]
    cases denote acval env φ (D + 1) ty with
    | none => rfl
    | some ta =>
      cases denote acval env φ (D + 2)
          (body.instantiate1 (.fvar (D + 1) ty)) with
      | none => rfl
      | some ba => rfl
  | .lam ty body, D, hpD, hfb => by
    simp only [ConLeche.Expr.substFvarAt, denote]
    rw [denote_substFvarAt hacl hainst hwa hba ha ty D hpD hfb.1,
      ← ConLeche.Expr.substFvarAt_instantiate1 hpD hba body 0,
      denote_substFvarAt hacl hainst hwa hba ha
        (body.instantiate1 (.fvar (D + 1) ty)) (D + 1) (by omega)
        (ConLeche.Expr.fvarsBelow_instantiate1 0 hfb.2),
      show D + 1 - p = D - p + 1 from by omega]
    cases denote acval env φ (D + 1) ty with
    | none => rfl
    | some ta =>
      cases denote acval env φ (D + 2)
          (body.instantiate1 (.fvar (D + 1) ty)) with
      | none => rfl
      | some ba => rfl
  | .letE ty val body, D, hpD, hfb => by
    simp only [ConLeche.Expr.substFvarAt, denote]
    rw [denote_substFvarAt hacl hainst hwa hba ha ty D hpD hfb.1,
      denote_substFvarAt hacl hainst hwa hba ha val D hpD hfb.2.1,
      ← ConLeche.Expr.substFvarAt_instantiate1 hpD hba body 0,
      denote_substFvarAt hacl hainst hwa hba ha
        (body.instantiate1 (.fvar (D + 1) ty)) (D + 1) (by omega)
        (ConLeche.Expr.fvarsBelow_instantiate1 0 hfb.2.2),
      show D + 1 - p = D - p + 1 from by omega]
    cases denote acval env φ (D + 1) ty with
    | none => rfl
    | some ta =>
    cases denote acval env φ (D + 1) val with
    | none => rfl
    | some va =>
      cases denote acval env φ (D + 2)
          (body.instantiate1 (.fvar (D + 1) ty)) with
      | none => rfl
      | some ba => rfl
  | .proj sn i e, D, hpD, hfb => by
    simp only [ConLeche.Expr.substFvarAt, denote]
    rw [denote_substFvarAt hacl hainst hwa hba ha e D hpD hfb]
    cases denote acval env φ (D + 1) e with
    | none => rfl
    | some ea =>
      simp only [Option.map_some]
      split
      · exact congrArg some (projNV_inst _ ea x (D - p)).symm
      · rcases i with _ | _ | i <;> rfl
  | .lit (.natVal k), D, hpD, hfb => by
    simp only [ConLeche.Expr.substFvarAt, denote]
    split
    · simp only [Option.map_some]
      rw [natLitT_inst (hainst _ _ _ _) (hainst _ _ _ _)]
    · rfl
  | .lit (.strVal s), D, hpD, hfb => by
    simp only [ConLeche.Expr.substFvarAt, denote]
    split
    · simp only [Option.map_some]
      refine congrArg some ?_
      symm
      rw [Term.inst_app, hainst,
        charListT_inst (by rw [Term.inst_app, hainst, hainst])
          (by rw [Term.inst_app, hainst, hainst]) (hainst _ _ _ _)
          (hainst _ _ _ _) (hainst _ _ _ _)]
    · rfl
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [ConLeche.Expr.sizeB]; omega)
  | (rw [ConLeche.Expr.sizeB_instantiate1 _ rfl]
     simp [ConLeche.Expr.sizeB]; omega)
  | (simp [ConLeche.Expr.sizeB])

/-- **Beta, at the stored-term reading** — the form the reduction
clauses consume: opening a binder body with the argument directly is
opening it with a fresh variable and then instantiating. -/
theorem denote_beta
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : Term) (k : Nat),
      (acval n ψ).inst y k = acval n ψ)
    {d : Nat} {ty body a : Expr} {x : Term}
    (hfb : Expr.fvarsBelow d body) (hwa : Expr.WScoped d a)
    (hba : a.looseBVarsBounded 0 = true)
    (ha : denote acval env φ d a = some x) (k : Nat) :
    denote acval env φ d (body.instantiate1 a k) =
      (denote acval env φ (d + 1)
        (body.instantiate1 (.fvar d ty) k)).map (Term.inst · x 0) := by
  have h := denote_substFvarAt (p := d) hacl hainst hwa hba ha
    (body.instantiate1 (.fvar d ty) k) d (Nat.le_refl d)
    (ConLeche.Expr.fvarsBelow_instantiate1 k hfb)
  rw [ConLeche.Expr.substFvarAt_instantiate1_self body k hfb,
    Nat.sub_self] at h
  exact h


end ConLeche.Verify
