module

public import ConLeche.Verify.Denote.Lemmas
public import ConLeche.Verify.Shift

public section

/-!
# `denote`'s depth shift (task #161, P3.2)

**No `EnvWF`.**  `denote` runs no checker and its binder clauses
read nothing but the binder's domain and body, which `Expr.shiftFrom`
shifts structurally, so each clause closes by the recursion alone.

`hacl` is kept: it is the *leaf* obligation (stored leaves are
lift-invariant), which the constant and literal clauses need.
-/

namespace ConLeche.Verify

open ConLeche.Term ConLeche.Verify

open ConLeche (Env Expr Name Level PropWhen)

variable {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → Term}

/-- The `Nat`-literal spine is lift-invariant when its two heads are. -/
theorem natLitT_liftN {za sa : Term} {k : Nat}
    (hz : za.liftN 1 k = za) (hs : sa.liftN 1 k = sa) :
    ∀ n : Nat, (natLitT za sa n).liftN 1 k = natLitT za sa n := by
  intro n
  induction n with
  | zero => exact hz
  | succ n ih =>
    show (Term.app sa (natLitT za sa n)).liftN 1 k = _
    rw [Term.liftN_app, hs, ih]
    rfl

/-- Ditto the character-list spine. -/
private theorem charListT_liftN {nilA consA ofNatA za sa : Term}
    {k : Nat} (hn : nilA.liftN 1 k = nilA)
    (hc : consA.liftN 1 k = consA) (ho : ofNatA.liftN 1 k = ofNatA)
    (hz : za.liftN 1 k = za) (hs : sa.liftN 1 k = sa) :
    ∀ cs : List Char,
      (charListT nilA consA ofNatA za sa cs).liftN 1 k
        = charListT nilA consA ofNatA za sa cs := by
  intro cs
  induction cs with
  | nil => exact hn
  | cons c cs ih =>
    show (Term.app (.app consA (.app ofNatA _)) _).liftN 1 k = _
    rw [Term.liftN_app, Term.liftN_app, Term.liftN_app, hc, ho,
      natLitT_liftN hz hs, ih]
    rfl

/-- **`denote`'s depth shift.**  See the module docstring for why
`EnvWF` is absent.

Generalized over the cut `p` because the binder clause compares `denote (d+2) (body.instantiate1 (.fvar
(d+1) …))` with `denote (d+1) (body.instantiate1 (.fvar d …))`, two
genuinely different expressions related by `Expr.shiftFrom d`. -/
theorem denote_shiftFrom
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ) {p : Nat} :
    ∀ (e : Expr) (d : Nat), p ≤ d → Expr.WScoped d e →
      denote acval env φ (d + 1) (e.shiftFrom p) =
        (denote acval env φ d e).map (Term.liftN 1 · (d - p))
  | .bvar i, d, _, _ => by
    have h1 : denote acval env φ (d + 1) (.bvar i) = none := by
      rw [denote.eq_def]
    have h2 : denote acval env φ d (.bvar i) = none := by
      rw [denote.eq_def]
    simp [ConLeche.Expr.shiftFrom, h1, h2]
  | .sort u, d, _, _ => by
    simp only [ConLeche.Expr.shiftFrom, denote, Option.map_some]
    rfl
  | .const n us, d, _, _ => by
    simp only [ConLeche.Expr.shiftFrom, denote]
    cases env.find? n with
    | none => rfl
    | some ci =>
      dsimp only
      split
      · simp only [Option.map_some, hacl]
      · rfl
  | .fvar idx ty, d, hpd, hw => by
    rw [ConLeche.Expr.WScoped] at hw
    have hlt : idx < d := hw.1
    simp only [ConLeche.Expr.shiftFrom]
    split
    · next hge =>
      rw [denote, denote, Option.map_some, Term.liftN_bvar,
        ite_eq_left (show d - 1 - idx < d - p by omega),
        show d + 1 - 1 - (idx + 1) = d - 1 - idx from by omega]
    · next hge =>
      rw [denote, denote, Option.map_some, Term.liftN_bvar,
        ite_eq_right (show ¬ d - 1 - idx < d - p by omega),
        show d + 1 - 1 - idx = d - 1 - idx + 1 from by omega]
  | .app fe a, d, hpd, hw => by
    rw [ConLeche.Expr.WScoped] at hw
    simp only [ConLeche.Expr.shiftFrom, denote]
    rw [denote_shiftFrom hacl fe d hpd hw.1,
      denote_shiftFrom hacl a d hpd hw.2]
    cases denote acval env φ d fe <;>
      cases denote acval env φ d a <;> rfl
  | .forallE ty body, d, hpd, hw => by
    rw [ConLeche.Expr.WScoped] at hw
    have hwb : Expr.WScoped (d + 1)
        (body.instantiate1 (.fvar d ty)) :=
      ConLeche.Expr.WScoped.instantiate1 hw.1 0 hw.2
    simp only [ConLeche.Expr.shiftFrom, denote]
    rw [← ConLeche.Expr.shiftFrom_instantiate1 hpd body 0,
      denote_shiftFrom hacl ty d hpd hw.1,
      denote_shiftFrom hacl (body.instantiate1 (.fvar d ty))
        (d + 1) (by omega) hwb,
      show d + 1 - p = d - p + 1 from by omega]
    cases denote acval env φ d ty with
    | none => rfl
    | some ta =>
      cases denote acval env φ (d + 1)
          (body.instantiate1 (.fvar d ty)) with
      | none => rfl
      | some ba => rfl
  | .lam ty body, d, hpd, hw => by
    rw [ConLeche.Expr.WScoped] at hw
    have hwb : Expr.WScoped (d + 1)
        (body.instantiate1 (.fvar d ty)) :=
      ConLeche.Expr.WScoped.instantiate1 hw.1 0 hw.2
    simp only [ConLeche.Expr.shiftFrom, denote]
    rw [← ConLeche.Expr.shiftFrom_instantiate1 hpd body 0,
      denote_shiftFrom hacl ty d hpd hw.1,
      denote_shiftFrom hacl (body.instantiate1 (.fvar d ty))
        (d + 1) (by omega) hwb,
      show d + 1 - p = d - p + 1 from by omega]
    cases denote acval env φ d ty with
    | none => rfl
    | some ta =>
      cases denote acval env φ (d + 1)
          (body.instantiate1 (.fvar d ty)) with
      | none => rfl
      | some ba => rfl
  | .letE ty val body, d, hpd, hw => by
    rw [ConLeche.Expr.WScoped] at hw
    have hwb : Expr.WScoped (d + 1)
        (body.instantiate1 (.fvar d ty)) :=
      ConLeche.Expr.WScoped.instantiate1 hw.1 0 hw.2.2
    simp only [ConLeche.Expr.shiftFrom, denote]
    rw [← ConLeche.Expr.shiftFrom_instantiate1 hpd body 0,
      denote_shiftFrom hacl ty d hpd hw.1,
      denote_shiftFrom hacl val d hpd hw.2.1,
      denote_shiftFrom hacl (body.instantiate1 (.fvar d ty))
        (d + 1) (by omega) hwb,
      show d + 1 - p = d - p + 1 from by omega]
    cases denote acval env φ d ty with
    | none => rfl
    | some ta =>
    cases denote acval env φ d val with
    | none => rfl
    | some va =>
      cases denote acval env φ (d + 1)
          (body.instantiate1 (.fvar d ty)) with
      | none => rfl
      | some ba => rfl
  | .proj sn i e, d, hpd, hw => by
    rw [ConLeche.Expr.WScoped] at hw
    simp only [ConLeche.Expr.shiftFrom, denote]
    rw [denote_shiftFrom hacl e d hpd hw]
    cases denote acval env φ d e with
    | none => rfl
    | some ea =>
      simp only [Option.map_some]
      cases env.findProj? sn i with
      | none => rfl
      | some entry =>
        show some (projNV (i + 1) (Term.liftN 1 ea (d - p)))
          = Option.map (fun x => Term.liftN 1 x (d - p))
            (some (projNV (i + 1) ea))
        simp only [Option.map_some, projNV_liftN]
  | .lit (.natVal k), d, _, _ => by
    simp only [ConLeche.Expr.shiftFrom, denote]
    split
    · simp only [Option.map_some]
      rw [natLitT_liftN (hacl _ _ _) (hacl _ _ _)]
    · rfl
  | .lit (.strVal s), d, _, _ => by
    simp only [ConLeche.Expr.shiftFrom, denote]
    split
    · simp only [Option.map_some]
      refine congrArg some ?_
      symm
      rw [Term.liftN_app, hacl,
        charListT_liftN (by rw [Term.liftN_app, hacl, hacl])
          (by rw [Term.liftN_app, hacl, hacl]) (hacl _ _ _)
          (hacl _ _ _) (hacl _ _ _)]
    · rfl
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [ConLeche.Expr.sizeB]; omega)
  | (rw [ConLeche.Expr.sizeB_instantiate1 _ rfl]
     simp [ConLeche.Expr.sizeB]; omega)
  | (simp [ConLeche.Expr.sizeB])

/-- **One level of weakening**: a `d`-scoped term denoted at `d + 1` is
its depth-`d` reading, lifted. -/
theorem denote_weaken_top
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ) {d : Nat} {e : Expr}
    (hw : Expr.WScoped d e) :
    denote acval env φ (d + 1) e
      = (denote acval env φ d e).map (Term.liftN 1 · 0) := by
  have h := denote_shiftFrom (env := env) (φ := φ) hacl (p := d) e d
    (Nat.le_refl d) hw
  rw [ConLeche.Expr.shiftFrom_eq_self hw.fvarsBelow, Nat.sub_self] at h
  exact h

end ConLeche.Verify
