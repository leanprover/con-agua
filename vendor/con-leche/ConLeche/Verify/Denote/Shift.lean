module

public import ConLeche.Verify.Denote
public import ConLeche.Verify.Denote.VClosed
public import ConLeche.Verify.Shift
import ConLeche.Verify.Abstract

public section

/-!
# Closed denotations

A closed expression denotes to a closed term: the literal spines are
closed when their constructor valuations are (`natLitT_closed`,
`charListT_closed`), and `denote` keeps every bound
variable below the depth it reads at (`denote_bvarsBelow`), hence
`denote_closed`.  This is the half of `ConLeche/Verify/Denote/VClosed.lean`'s
trade that `denote` pays in `cval_closed`: it saves a valuation
parameter on every clause.
-/

set_option linter.unusedVariables false

namespace ConLeche.Verify

open ConLeche.Term

variable {cval : Name → (Name → Nat) → Term} {env : Env} {φ : Name → Nat}

/-- A `Nat` literal's term is closed when the two constructor
valuations are. -/
theorem natLitT_closed {zv sv : Term} (hz : Term.Closed zv)
    (hs : Term.Closed sv) : ∀ n, Term.Closed (natLitT zv sv n)
  | 0 => hz
  | n + 1 => ⟨hs, natLitT_closed hz hs n⟩

/-- A character list's term is closed when its constituents are. -/
theorem charListT_closed {nilV consV ofNatV zv sv : Term}
    (hn : Term.Closed nilV) (hc : Term.Closed consV)
    (ho : Term.Closed ofNatV) (hz : Term.Closed zv)
    (hs : Term.Closed sv) :
    ∀ cs : List Char, Term.Closed (charListT nilV consV ofNatV zv sv cs)
  | [] => hn
  | c :: cs =>
    ⟨⟨hc, ⟨ho, natLitT_closed hz hs c.toNat⟩⟩,
      charListT_closed hn hc ho hz hs cs⟩

/-- `projNV` preserves bvar bounds (hereditary proj clauses). -/
theorem projNV_bvarsBelow {d : Nat} :
    ∀ (i : Nat) {v : Term}, Term.bvarsBelow d v →
      Term.bvarsBelow d (projNV i v)
  | 0, _, h => h
  | i + 1, v, h => projNV_bvarsBelow i (v := .snd v) h

/-! ## Scoping transfers to the denotation

The one place the `Expr`/`Term` separation of §12.6 is crossed
*deliberately*: a term scoped below depth `d` denotes to a `Term`
whose bound variables are below `d`.  That is not a leak — it is the
direction that *does* hold, because `denote` maps an `fvar` at index
`idx < d` to `.bvar (d - 1 - idx) < d` and opens each binder one level
deeper.  The converse (typing telling you about syntax) is what does
not hold.

Consumed at the `.const` clause of `inferBody`, where the stored type
is a closed `Expr` and its denotation has to be a closed `Term` for
the environment invariant's typing to survive lifting. -/

theorem denote_bvarsBelow (hcl : ∀ n ψ, Term.Closed (cval n ψ)) :
    ∀ (d : Nat) (e : Expr), Expr.WScoped d e →
      e.looseBVarsBounded 0 = true →
      ∀ {v : Term}, denote cval env φ d e = some v →
        Term.bvarsBelow d v := by
  intro d e
  induction d, e using denote.induct (env := env) with
  | case1 d u =>
    intro _ _ v h
    rw [denote_sort] at h
    obtain rfl : v = .sort (u.eval φ) := (Option.some.inj h).symm
    trivial
  | case2 d idx ty =>
    intro hws _ v h
    rw [denote_fvar] at h
    obtain rfl : v = .bvar (d - 1 - idx) := (Option.some.inj h).symm
    simp only [Expr.WScoped] at hws
    exact Nat.lt_of_lt_of_le (by omega) (Nat.le_refl d)
  | case3 d n us ci h1 h2 =>
    intro _ _ v h
    rw [denote_const h1 h2] at h
    obtain rfl := (Option.some.inj h).symm
    exact Term.bvarsBelow.mono (Nat.zero_le d) (hcl _ _)
  | case4 d n us ci h1 h2 =>
    intro _ _ v h; rw [denote, h1] at h; simp only [ite_eq_right h2] at h
    exact nomatch h
  | case5 d n us h1 =>
    intro _ _ v h; rw [denote, h1] at h; exact nomatch h
  | case6 d ty body ihty ihbody =>
    intro hws hb v h
    rw [denote_forallE] at h
    obtain ⟨B, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨B', h2, h⟩ := Option.bind_eq_some_iff.mp h
    obtain rfl : v = .pi B B' := (Option.some.inj h).symm
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact ⟨ihty hws.1 hb.1 h1,
      ihbody (Expr.WScoped.instantiate1 hws.1 0 hws.2)
        (looseBVarsBounded_instantiate1 body 0 hb.2) h2⟩
  | case7 d ty body ihty ihbody =>
    intro hws hb v h
    rw [denote_lam] at h
    obtain ⟨B, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨B', h2, h⟩ := Option.bind_eq_some_iff.mp h
    obtain rfl : v = .lam B B' := (Option.some.inj h).symm
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact ⟨ihty hws.1 hb.1 h1,
      ihbody (Expr.WScoped.instantiate1 hws.1 0 hws.2)
        (looseBVarsBounded_instantiate1 body 0 hb.2) h2⟩
  | case8 d f a ihf iha =>
    intro hws hb v h
    rw [denote_app] at h
    obtain ⟨vf, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨va, h2, h⟩ := Option.bind_eq_some_iff.mp h
    obtain rfl : v = .app vf va := (Option.some.inj h).symm
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact ⟨ihf hws.1 hb.1 h1, iha hws.2 hb.2 h2⟩
  | case9 d ty val body ihty ihv ihbody =>
    intro hws hb v h
    rw [denote_letE] at h
    obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨B, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨B', h2, h⟩ := Option.bind_eq_some_iff.mp h
    obtain rfl : v = .letE B B' := (Option.some.inj h).symm
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact ⟨ihv hws.2.1 hb.1.2 h1,
      ihbody (Expr.WScoped.instantiate1 hws.1 0 hws.2.2)
        (looseBVarsBounded_instantiate1 body 0 hb.2) h2⟩
  | case10 d sn i e ihe =>
    intro hws hb v h
    rw [denote_proj] at h
    obtain ⟨B, h1, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Expr.WScoped] at hws
    have hB : Term.bvarsBelow d B := ihe hws hb h1
    cases h2 : env.findProj? sn i with
    | some entry =>
      rw [h2] at h
      obtain rfl : v = projNV (i + 1) B := (Option.some.inj h).symm
      exact projNV_bvarsBelow _ hB
    | none =>
      rw [h2] at h
      exact nomatch h
  | case11 d n hg =>
    intro _ _ v h
    rw [denote_natLit hg] at h
    obtain rfl := (Option.some.inj h).symm
    exact Term.bvarsBelow.mono (Nat.zero_le d)
      (natLitT_closed (hcl _ _) (hcl _ _) n)
  | case12 d n hg =>
    intro _ _ v h; rw [denote, ite_eq_right hg] at h; exact nomatch h
  | case13 d t hg =>
    intro _ _ v h
    rw [denote_strLit hg] at h
    obtain rfl := (Option.some.inj h).symm
    refine Term.bvarsBelow.mono (Nat.zero_le d)
      ⟨hcl _ _, charListT_closed ?_ ?_ (hcl _ _) (hcl _ _) (hcl _ _) t.toList⟩
    · exact ⟨hcl _ _, hcl _ _⟩
    · exact ⟨hcl _ _, hcl _ _⟩
  | case14 d t hg =>
    intro _ _ v h; rw [denote, ite_eq_right hg] at h; exact nomatch h
  | case15 d x k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 =>
    intro _ _ v h
    match x with
    | .bvar i => rw [denote_bvar] at h; exact nomatch h
    | .sort u => exact (k1 u rfl).elim
    | .fvar a c => exact (k2 a c rfl).elim
    | .const a b => exact (k3 a b rfl).elim
    | .forallE b c => exact (k4 b c rfl).elim
    | .lam b c => exact (k5 b c rfl).elim
    | .app a b => exact (k6 a b rfl).elim
    | .letE b c dd => exact (k7 b c dd rfl).elim
    | .proj a b c => exact (k8 a b c rfl).elim
    | .lit (.natVal n) => exact (k9 n rfl).elim
    | .lit (.strVal t) => exact (k10 t rfl).elim

/-- A closed expression denotes to a closed term. -/
theorem denote_closed (hcl : ∀ n ψ, Term.Closed (cval n ψ))
    {e : Expr} {v : Term} (hnf : e.hasFvar = false)
    (hb : e.looseBVarsBounded 0 = true)
    (h : denoteClosed cval env φ e = some v) : Term.Closed v :=
  denote_bvarsBelow hcl 0 e (Expr.WScoped.of_not_hasFvar hnf) hb h

end ConLeche.Verify
