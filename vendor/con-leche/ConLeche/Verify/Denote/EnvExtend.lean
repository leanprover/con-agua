module

public import ConLeche.Verify.Denote.AcvalCongr
public import ConLeche.Verify.Denote.ConstsBound

public section

/-!
# `denote` across an environment extension (task #161, P3.2)

`denote`'s binder clauses read no environment, so they close on the
two induction hypotheses alone, exactly like `.app`.  The two premises
are the ones the *reading itself* needs: `denote` consults `env`
only through `find?` (`FindPreserved`) and the two support guards
(`LitGuardsAgree`).
-/

namespace ConLeche.Verify

open ConLeche.Term ConLeche.Verify

open ConLeche (Env Expr Name Level PropWhen
  natLitSupported strLitSupported)

/-- **`denote` is stable under environment extension**, stated.

An **equation**, not an implication: an install must not be able to assume silently that a
reading exists on one side and not the other. -/
@[expose] def DenotePEnvExtend (env₀ env : Env)
    (acval : Name → (Name → Nat) → Term) (φ : Name → Nat) : Prop :=
  ∀ (d : Nat) (e : Expr), ConstsBound env₀ e →
    denote acval env₀ φ d e = denote acval env φ d e

/-- **`DenotePEnvExtend`, discharged** — from `FindPreserved` and
`LitGuardsAgree` alone. -/
theorem denote_envExtend {env₀ env : Env}
    {acval : Name → (Name → Nat) → Term} {φ : Name → Nat}
    (hF : FindPreserved env₀ env) (hG : LitGuardsAgree env₀ env)
    (hproj : ∀ (sn : Name) (i : Nat),
      env₀.findProj? sn i = none → env.findProj? sn i = none) :
    DenotePEnvExtend env₀ env acval φ := by
  -- a preserved lookup carries its entry across unchanged
  have hmono : ∀ (sn : Name) (i : Nat) (entry : ConLeche.ProjEntry),
      env₀.findProj? sn i = some entry →
      env.findProj? sn i = some entry := by
    intro sn i entry h
    obtain ⟨tbl, hf0, hi, rfl⟩ := ConLeche.Env.findProj?_some h
    exact ConLeche.Env.findProj?_of_table (hF hf0) hi
  intro d e
  induction d, e using denote.induct (env := env₀) with
  | case1 d u => intro _; rw [denote, denote]
  | case2 d idx ty => intro _; rw [denote, denote]
  | case3 d n us ci hf hlen =>
    intro _
    rw [denote, hf, denote, hF hf]
  | case4 d n us ci hf hlen =>
    intro _
    rw [denote, hf, denote, hF hf]
  | case5 d n us hf =>
    intro hc
    rw [constsBound_const, hf] at hc
    exact nomatch hc
  | case6 d ty body ihty ihbody =>
    intro hc
    rw [constsBound_forallE] at hc
    have hcb : ConstsBound env₀ (body.instantiate1 (.fvar d ty)) :=
      ConstsBound.instantiate1
        (by rw [constsBound_fvar]; exact hc.1) _ _ hc.2
    rw [denote, denote, ihty hc.1, ihbody hcb]
  | case7 d ty body ihty ihbody =>
    intro hc
    rw [constsBound_lam] at hc
    have hcb : ConstsBound env₀ (body.instantiate1 (.fvar d ty)) :=
      ConstsBound.instantiate1
        (by rw [constsBound_fvar]; exact hc.1) _ _ hc.2
    rw [denote, denote, ihty hc.1, ihbody hcb]
  | case8 d f a ihf iha =>
    intro hc
    rw [constsBound_app] at hc
    rw [denote, denote, ihf hc.1, iha hc.2]
  | case9 d ty val body ihty ihv ihbody =>
    intro hc
    rw [constsBound_letE] at hc
    have hcb : ConstsBound env₀ (body.instantiate1 (.fvar d ty)) :=
      ConstsBound.instantiate1
        (by rw [constsBound_fvar]; exact hc.1) _ _ hc.2.2
    rw [denote, denote, ihty hc.1, ihv hc.2.1, ihbody hcb]
  | case10 d sn i e ihe =>
    intro hc
    rw [constsBound_proj] at hc
    rw [denote, denote, ihe hc]
    cases denote acval env φ d e with
    | none => rfl
    | some ea =>
      show (match env₀.findProj? sn i with
          | some entry => some (projNV (i + entry.off) ea)
          | none => Term.projPair? i ea)
        = (match env.findProj? sn i with
          | some entry => some (projNV (i + entry.off) ea)
          | none => Term.projPair? i ea)
      cases hfp0 : env₀.findProj? sn i with
      | some entry => rw [hmono sn i entry hfp0]
      | none => rw [hproj sn i hfp0]
  | case11 d n hsup =>
    intro _
    rw [denote, ite_eq_left hsup, denote, ite_eq_left (hG.1 ▸ hsup)]
  | case12 d n hsup =>
    intro _
    rw [denote, ite_eq_right hsup, denote,
      ite_eq_right (fun h => hsup (hG.1.trans h))]
  | case13 d s hsup =>
    intro _
    obtain ⟨hnil, hcons⟩ := strLitSupported_listNames hsup
    rw [denote, ite_eq_left hsup, denote, ite_eq_left (hG.2 ▸ hsup),
      levelParamsAt_congr hF hnil, levelParamsAt_congr hF hcons]
  | case14 d s hsup =>
    intro _
    rw [denote, ite_eq_right hsup, denote,
      ite_eq_right (fun h => hsup (hG.2.trans h))]
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro _
    cases x with
    | bvar i => rw [denote.eq_def, denote.eq_def]
    | sort u => exact absurd rfl (hs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n us => exact absurd rfl (hc n us)
    | forallE ty b => exact absurd rfl (hpi ty b)
    | lam ty b => exact absurd rfl (hlam ty b)
    | app f a => exact absurd rfl (happ f a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal n => exact absurd rfl (hnat n)
      | strVal s => exact absurd rfl (hstr s)

/-! ## The monotone crossing (task #161, the literal tier's opening)

`LitGuardsAgree` — the guard *equality* — is refutable at a
support-completing install (a pinned-type `def` named `String.ofList`
flips `strLitSupported` upward, and nothing forbids the name).  The
fold therefore rides the **monotone** crossing below: literal guards
only ever gain under a fresh cons (`natLitSupported_cons`/
`strLitSupported_cons`), and a *successful* prefix reading transfers
forward — which is the only direction the harvests use for their
subjects, whose acceptance guaranteed prefix-supported literals. -/

/-- The literal guards are monotone across the extension. -/
@[expose] def LitGuardsMono (env₀ env : Env) : Prop :=
  (natLitSupported env₀ = true → natLitSupported env = true) ∧
  (strLitSupported env₀ = true → strLitSupported env = true)

/-- Free at every fresh cons, of any kind. -/
theorem litGuardsMono_cons {env : Env} {c₀ : ConLeche.ConstantInfo}
    (hfresh : env.find? c₀.name = none) :
    LitGuardsMono env ⟨c₀ :: env.consts⟩ :=
  ⟨natLitSupported_cons hfresh, strLitSupported_cons hfresh⟩

/-- **The monotone crossing**: a successful prefix reading is
reproduced verbatim at the extension. -/
theorem denote_envExtend_mono {env₀ env : Env}
    {acval : Name → (Name → Nat) → Term} {φ : Name → Nat}
    (hF : FindPreserved env₀ env) (hG : LitGuardsMono env₀ env)
    (hproj : ∀ (sn : Name) (i : Nat),
      env₀.findProj? sn i = none → env.findProj? sn i = none) :
    ∀ (d : Nat) (e : Expr), ConstsBound env₀ e →
      ∀ {ea : Term}, denote acval env₀ φ d e = some ea →
        denote acval env φ d e = some ea := by
  have hmono : ∀ (sn : Name) (i : Nat) (entry : ConLeche.ProjEntry),
      env₀.findProj? sn i = some entry →
      env.findProj? sn i = some entry := by
    intro sn i entry h
    obtain ⟨tbl, hf0, hi, rfl⟩ := ConLeche.Env.findProj?_some h
    exact ConLeche.Env.findProj?_of_table (hF hf0) hi
  intro d e
  induction d, e using denote.induct (env := env₀) with
  | case1 d u => intro _ ea h; rw [denote] at h ⊢; exact h
  | case2 d idx ty => intro _ ea h; rw [denote] at h ⊢; exact h
  | case3 d n us ci hf hlen =>
    intro _ ea h
    rw [denote, hf] at h
    rw [denote, hF hf]
    exact h
  | case4 d n us ci hf hlen =>
    intro _ ea h
    rw [denote, hf] at h
    dsimp only at h
    rw [ite_eq_right hlen] at h
    exact nomatch h
  | case5 d n us hf =>
    intro hc ea h
    rw [constsBound_const, hf] at hc
    exact nomatch hc
  | case6 d ty body ihty ihbody =>
    intro hc ea h
    rw [constsBound_forallE] at hc
    have hcb : ConstsBound env₀ (body.instantiate1 (.fvar d ty)) :=
      ConstsBound.instantiate1
        (by rw [constsBound_fvar]; exact hc.1) _ _ hc.2
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denote_forallE_inv h
    rw [denote, ihty hc.1 hta, ihbody hcb hba]
    rfl
  | case7 d ty body ihty ihbody =>
    intro hc ea h
    rw [constsBound_lam] at hc
    have hcb : ConstsBound env₀ (body.instantiate1 (.fvar d ty)) :=
      ConstsBound.instantiate1
        (by rw [constsBound_fvar]; exact hc.1) _ _ hc.2
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denote_lam_inv h
    rw [denote, ihty hc.1 hta, ihbody hcb hba]
    rfl
  | case8 d f a ihf iha =>
    intro hc ea h
    rw [constsBound_app] at hc
    obtain ⟨fa, aa, hfa, haa, rfl⟩ := denote_app_inv h
    rw [denote, ihf hc.1 hfa, iha hc.2 haa]
    rfl
  | case9 d ty val body ihty ihv ihbody =>
    intro hc ea h
    rw [constsBound_letE] at hc
    have hcb : ConstsBound env₀ (body.instantiate1 (.fvar d ty)) :=
      ConstsBound.instantiate1
        (by rw [constsBound_fvar]; exact hc.1) _ _ hc.2.2
    obtain ⟨ta, va, ba, hta, hva, hba, rfl⟩ := denote_letE_inv h
    rw [denote, ihty hc.1 hta, ihv hc.2.1 hva, ihbody hcb hba]
    rfl
  | case10 d sn i e ihe =>
    intro hc ea h
    rw [constsBound_proj] at hc
    obtain ⟨ea', hea', hcase⟩ := denote_proj_inv h
    rcases hcase with ⟨entry, hfp0, rfl⟩ | ⟨hnt0, hdec⟩
    · -- a table entry at the prefix persists unchanged
      rw [denote, ihe hc hea', hmono sn i entry hfp0]
      rfl
    · -- the table-free path: the extension adds no entry either
      rw [denote, ihe hc hea', hproj sn i hnt0]
      exact hdec
  | case11 d n hsup =>
    intro _ ea h
    rw [denote, ite_eq_left hsup] at h
    rw [denote, ite_eq_left (hG.1 hsup)]
    exact h
  | case12 d n hsup =>
    intro _ ea h
    rw [denote, ite_eq_right hsup] at h
    exact nomatch h
  | case13 d s hsup =>
    intro _ ea h
    obtain ⟨hnil, hcons⟩ := strLitSupported_listNames hsup
    rw [denote, ite_eq_left hsup] at h
    rw [denote, ite_eq_left (hG.2 hsup),
      ← levelParamsAt_congr hF hnil, ← levelParamsAt_congr hF hcons]
    exact h
  | case14 d s hsup =>
    intro _ ea h
    rw [denote, ite_eq_right hsup] at h
    exact nomatch h
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro _ ea h
    cases x with
    | bvar i => rw [denote.eq_def] at h; exact nomatch h
    | sort u => exact absurd rfl (hs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n us => exact absurd rfl (hc n us)
    | forallE ty b => exact absurd rfl (hpi ty b)
    | lam ty b => exact absurd rfl (hlam ty b)
    | app f a => exact absurd rfl (happ f a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal n => exact absurd rfl (hnat n)
      | strVal s => exact absurd rfl (hstr s)


/-- **The monotone crossing, read-only**: `denote_envExtend_mono`
without the `ConstsBound` premise — a successful reading resolved every
constant it met (the key parameters of a positivity node, whose `fvar`
annotations are the walk's). -/
theorem denote_envExtend_mono_ok {env₀ env : Env}
    {acval : Name → (Name → Nat) → Term} {φ : Name → Nat}
    (hF : FindPreserved env₀ env) (hG : LitGuardsMono env₀ env)
    (hproj : ∀ (sn : Name) (i : Nat),
      env₀.findProj? sn i = none → env.findProj? sn i = none) :
    ∀ (d : Nat) (e : Expr),
      ∀ {ea : Term}, denote acval env₀ φ d e = some ea →
        denote acval env φ d e = some ea := by
  have hmono : ∀ (sn : Name) (i : Nat) (entry : ConLeche.ProjEntry),
      env₀.findProj? sn i = some entry →
      env.findProj? sn i = some entry := by
    intro sn i entry h
    obtain ⟨tbl, hf0, hi, rfl⟩ := ConLeche.Env.findProj?_some h
    exact ConLeche.Env.findProj?_of_table (hF hf0) hi
  intro d e
  induction d, e using denote.induct (env := env₀) with
  | case1 d u => intro ea h; rw [denote] at h ⊢; exact h
  | case2 d idx ty => intro ea h; rw [denote] at h ⊢; exact h
  | case3 d n us ci hf hlen =>
    intro ea h
    rw [denote, hf] at h
    rw [denote, hF hf]
    exact h
  | case4 d n us ci hf hlen =>
    intro ea h
    rw [denote, hf] at h
    dsimp only at h
    rw [ite_eq_right hlen] at h
    exact nomatch h
  | case5 d n us hf =>
    intro ea h
    rw [denote, hf] at h
    exact nomatch h
  | case6 d ty body ihty ihbody =>
    intro ea h
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denote_forallE_inv h
    rw [denote, ihty hta, ihbody hba]
    rfl
  | case7 d ty body ihty ihbody =>
    intro ea h
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denote_lam_inv h
    rw [denote, ihty hta, ihbody hba]
    rfl
  | case8 d f a ihf iha =>
    intro ea h
    obtain ⟨fa, aa, hfa, haa, rfl⟩ := denote_app_inv h
    rw [denote, ihf hfa, iha haa]
    rfl
  | case9 d ty val body ihty ihv ihbody =>
    intro ea h
    obtain ⟨ta, va, ba, hta, hva, hba, rfl⟩ := denote_letE_inv h
    rw [denote, ihty hta, ihv hva, ihbody hba]
    rfl
  | case10 d sn i e ihe =>
    intro ea h
    obtain ⟨ea', hea', hcase⟩ := denote_proj_inv h
    rcases hcase with ⟨entry, hfp0, rfl⟩ | ⟨hnt0, hdec⟩
    · -- a table entry at the prefix persists unchanged
      rw [denote, ihe hea', hmono sn i entry hfp0]
      rfl
    · -- the table-free path: the extension adds no entry either
      rw [denote, ihe hea', hproj sn i hnt0]
      exact hdec
  | case11 d n hsup =>
    intro ea h
    rw [denote, ite_eq_left hsup] at h
    rw [denote, ite_eq_left (hG.1 hsup)]
    exact h
  | case12 d n hsup =>
    intro ea h
    rw [denote, ite_eq_right hsup] at h
    exact nomatch h
  | case13 d s hsup =>
    intro ea h
    obtain ⟨hnil, hcons⟩ := strLitSupported_listNames hsup
    rw [denote, ite_eq_left hsup] at h
    rw [denote, ite_eq_left (hG.2 hsup),
      ← levelParamsAt_congr hF hnil, ← levelParamsAt_congr hF hcons]
    exact h
  | case14 d s hsup =>
    intro ea h
    rw [denote, ite_eq_right hsup] at h
    exact nomatch h
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro ea h
    cases x with
    | bvar i => rw [denote.eq_def] at h; exact nomatch h
    | sort u => exact absurd rfl (hs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n us => exact absurd rfl (hc n us)
    | forallE ty b => exact absurd rfl (hpi ty b)
    | lam ty b => exact absurd rfl (hlam ty b)
    | app f a => exact absurd rfl (happ f a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal n => exact absurd rfl (hnat n)
      | strVal s => exact absurd rfl (hstr s)

end ConLeche.Verify
