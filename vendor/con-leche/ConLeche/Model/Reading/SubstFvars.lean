module

import ConLeche.Semantics.Tower.TowerKit
import ConLeche.Verify.Denote
import ConLeche.Verify.Shift
import ConLeche.Verify.Denote.Inst
public import ConLeche.Model.Env.EnvModel
public import ConLeche.Semantics.SubstAV
public import ConLeche.Verify.SubstFvars
import ConLeche.Verify.Denote.Shift

public section

/-!
# `denote` crosses a parallel substitution of free variables

The reading of `Expr.substFvars b D s e` at depth `D + t` is the reading
of `e` at depth `b + t` with its variables `0 ..< b` — the bound
positions `t + (b - 1 - i)` there — replaced by the readings of the
`s i` (`Term.substAV`).  With `interp_substAV` it reads at the
valuation holding their values: a container frame's constructor type
(the recorded member-abstracted type, its parameters replaced by the
key's, its member holes by the frame's holes or the members' formers)
reads as the recorded fields at the frame of those values.  The proof is `denote_substFvarAt`'s, clause for clause.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify

open ConLeche (Env Expr Name Level)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-- The substitution the reading of `Expr.substFvars b D s` applies:
position `j < b` (the variable `b - 1 - j`) is `x (b - 1 - j)`, the
rest move to `D`. -/
@[expose] def substTau (b D : Nat) (x : Nat → Term) : Nat → Term :=
  fun j => if j < b then x (b - 1 - j) else .bvar (j - b + D)

theorem projPair?_substAV (τ : Nat → Term) (k : Nat) :
    ∀ (i : Nat) (e : Term),
      (Term.projPair? i e).map (Term.substAV τ · k)
        = Term.projPair? i (Term.substAV τ e k)
  | 0, _ => rfl
  | 1, _ => rfl
  | _ + 2, _ => rfl

/-- **The reading crosses a parallel substitution of free variables.** -/
theorem denote_substFvars (m : EnvModel V env) {b D : Nat} {s : Nat → Expr}
    {x : Nat → Term}
    (hs : ∀ i, i < b → Expr.WScoped D (s i) ∧ (s i).looseBVarsBounded 0 = true ∧
      denote m.acval env φ D (s i) = some (x i)) :
    ∀ (e : Expr) (t : Nat), Expr.fvarsBelow (b + t) e →
      denote m.acval env φ (D + t) (Expr.substFvars b D s e)
        = (denote m.acval env φ (b + t) e).map (Term.substAV (substTau b D x) · t)
  | .bvar i, t, _ => by
    have h1 : denote m.acval env φ (D + t) (.bvar i) = none := by rw [denote.eq_def]
    have h2 : denote m.acval env φ (b + t) (.bvar i) = none := by rw [denote.eq_def]
    simp [Expr.substFvars, h1, h2]
  | .sort u, t, _ => by
    simp only [Expr.substFvars, denote, Option.map_some]
    rfl
  | .const n us, t, _ => by
    simp only [Expr.substFvars, denote]
    cases env.find? n with
    | none => rfl
    | some ci =>
      dsimp only
      split
      · simp only [Option.map_some]
        exact congrArg some (Term.substAV_eq_self _ _
          (Term.bvarsBelow.mono (Nat.zero_le _) (m.cval_closed _ _))).symm
      · rfl
  | .fvar i ty, t, hfb => by
    have hlt : i < b + t := hfb
    by_cases hib : i < b
    · obtain ⟨hw, hbd, hx⟩ := hs i hib
      rw [Expr.substFvars_fvar_lt hib, denote_lift m.acval_closed hw (D + t) (by omega), hx,
        denote]
      simp only [Option.map_some, Nat.add_sub_cancel_left]
      rw [Term.substAV_bvar_ge _ (by omega)]
      simp only [substTau, show b + t - 1 - i - t < b by omega, ite_true,
        show b - 1 - (b + t - 1 - i - t) = i by omega]
    · rw [Expr.substFvars_fvar_ge (by omega), denote, denote]
      simp only [Option.map_some]
      rw [Term.substAV_bvar_lt _ (by omega)]
      congr 2
      omega
  | .app fe a, t, hfb => by
    simp only [Expr.substFvars, denote]
    rw [denote_substFvars m hs fe t hfb.1, denote_substFvars m hs a t hfb.2]
    cases denote m.acval env φ (b + t) fe <;>
      cases denote m.acval env φ (b + t) a <;> rfl
  | .forallE ty body, t, hfb => by
    have hsb : ∀ i, i < b → (s i).looseBVarsBounded 0 = true := fun i hi => (hs i hi).2.1
    simp only [Expr.substFvars, denote]
    have hop : (Expr.substFvars b D s body).instantiate1 (.fvar (D + t) (Expr.substFvars b D s ty))
        = Expr.substFvars b D s (body.instantiate1 (.fvar (b + t) ty)) := by
      rw [Expr.substFvars_instantiate1 hsb, Expr.substFvars_fvar_ge (by omega),
        show b + t - b + D = D + t by omega]
    rw [denote_substFvars m hs ty t hfb.1, hop,
      show D + t + 1 = D + (t + 1) by omega,
      denote_substFvars m hs (body.instantiate1 (.fvar (b + t) ty)) (t + 1)
        (by rw [show b + (t + 1) = b + t + 1 by omega]
            exact Expr.fvarsBelow_instantiate1 0 hfb.2),
      show b + (t + 1) = b + t + 1 by omega]
    cases denote m.acval env φ (b + t) ty with
    | none => rfl
    | some ta =>
      cases denote m.acval env φ (b + t + 1) (body.instantiate1 (.fvar (b + t) ty)) with
      | none => rfl
      | some ba => rfl
  | .lam ty body, t, hfb => by
    have hsb : ∀ i, i < b → (s i).looseBVarsBounded 0 = true := fun i hi => (hs i hi).2.1
    simp only [Expr.substFvars, denote]
    have hop : (Expr.substFvars b D s body).instantiate1 (.fvar (D + t) (Expr.substFvars b D s ty))
        = Expr.substFvars b D s (body.instantiate1 (.fvar (b + t) ty)) := by
      rw [Expr.substFvars_instantiate1 hsb, Expr.substFvars_fvar_ge (by omega),
        show b + t - b + D = D + t by omega]
    rw [denote_substFvars m hs ty t hfb.1, hop,
      show D + t + 1 = D + (t + 1) by omega,
      denote_substFvars m hs (body.instantiate1 (.fvar (b + t) ty)) (t + 1)
        (by rw [show b + (t + 1) = b + t + 1 by omega]
            exact Expr.fvarsBelow_instantiate1 0 hfb.2),
      show b + (t + 1) = b + t + 1 by omega]
    cases denote m.acval env φ (b + t) ty with
    | none => rfl
    | some ta =>
      cases denote m.acval env φ (b + t + 1) (body.instantiate1 (.fvar (b + t) ty)) with
      | none => rfl
      | some ba => rfl
  | .letE ty val body, t, hfb => by
    have hsb : ∀ i, i < b → (s i).looseBVarsBounded 0 = true := fun i hi => (hs i hi).2.1
    simp only [Expr.substFvars, denote]
    have hop : (Expr.substFvars b D s body).instantiate1 (.fvar (D + t) (Expr.substFvars b D s ty))
        = Expr.substFvars b D s (body.instantiate1 (.fvar (b + t) ty)) := by
      rw [Expr.substFvars_instantiate1 hsb, Expr.substFvars_fvar_ge (by omega),
        show b + t - b + D = D + t by omega]
    rw [denote_substFvars m hs ty t hfb.1, denote_substFvars m hs val t hfb.2.1, hop,
      show D + t + 1 = D + (t + 1) by omega,
      denote_substFvars m hs (body.instantiate1 (.fvar (b + t) ty)) (t + 1)
        (by rw [show b + (t + 1) = b + t + 1 by omega]
            exact Expr.fvarsBelow_instantiate1 0 hfb.2.2),
      show b + (t + 1) = b + t + 1 by omega]
    cases denote m.acval env φ (b + t) ty with
    | none => rfl
    | some ta =>
    cases denote m.acval env φ (b + t) val with
    | none => rfl
    | some va =>
      cases denote m.acval env φ (b + t + 1) (body.instantiate1 (.fvar (b + t) ty)) with
      | none => rfl
      | some ba => rfl
  | .proj sn i e, t, hfb => by
    simp only [Expr.substFvars, denote]
    rw [denote_substFvars m hs e t hfb]
    cases denote m.acval env φ (b + t) e with
    | none => rfl
    | some ea =>
      simp only [Option.map_some]
      split
      · exact congrArg some (Term.substAV_projNV _ t _ ea).symm
      · exact (projPair?_substAV _ t i ea).symm
  | .lit l, t, _ => by
    have hd : ∀ d, denote m.acval env φ d (.lit l) = denote m.acval env φ 0 (.lit l) := by
      intro d; cases l <;> simp only [denote]
    simp only [Expr.substFvars]
    rw [hd (D + t), hd (b + t)]
    cases h0 : denote m.acval env φ 0 (.lit l) with
    | none => rfl
    | some X =>
      simp only [Option.map_some]
      have hcl : Term.bvarsBelow 0 X :=
        denote_bvarsBelow m.cval_closed 0 _ (by simp [Expr.WScoped]) rfl
          h0
      exact congrArg some (Term.substAV_eq_self _ _
        (Term.bvarsBelow.mono (Nat.zero_le _) hcl)).symm
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [ConLeche.Expr.sizeB]; omega)
  | (rw [ConLeche.Expr.sizeB_instantiate1 _ rfl]
     simp [ConLeche.Expr.sizeB]; omega)
  | (simp [ConLeche.Expr.sizeB])

end ConLeche.Model
