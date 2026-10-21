module

public import ConLeche.Model.Inductives.TargetRecRead

public section

/-!
# The call node's value: `TargetNodeVal` discharged

`interp_targetAbstract` (`TargetRecRead.lean`) reads the classification-
free abstraction with ONE premise, `TargetNodeVal`: at a recursive call
`c x⃗ e⃗ (f a⃗)` of the stored rule body, the stored node reads to its
`ih` variable's value folded along the call's telescope variables.
This file discharges it, with the `ih` values the kernel's own call
typing names: the `ih` term of a call is the READING of the λ the
check inferred (`targetCallOk`: `λ a⃗ : A⃗, c x⃗ e⃗ (f a⃗)` with the
callee a variable of its stored type after the frame), at the callee's
value.  Three facts meet:

* the λ's fold along a FITTING spine is its body at the spine
  (`mkLamsAV_fold`);
* the spine the residue applies the `ih` variable to — the call's own
  telescope variables — fits: the residue node was typed by the rule
  stage (`IhTyped`), in the walk's context (`WalkCtx`), against the
  `ih` variable's type `∀ a⃗ : A⃗, …`, whose domains are the λ's;
* the λ's body and the stored node apply the callee's value to the
  same arguments: the stored node's arguments read the same at every
  frame they are opened at (`interp_open_indep`).

The telescope `A⃗` is read by one function, `teleDoms`, from both the
`∀`-tower (the `ih` type) and the λ-tower (the call's term): their
binders open alike, so their domains are literally one list.
-/

namespace ConLeche.Model
open ConLeche.Verify (denote denote_forallE)
open ConLeche.Term (Term)
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory

open ConLeche (Env Expr Name Level ConstantVal ConstantInfo)

universe uv

variable {acval : Name → (Name → Nat) → Term} {env : Env} {φ : Name → Nat}

/-! ## A telescope's domains, read -/

/-- **A telescope's domains, read above depth `D`**, with `os` of its
binders opened so far — each binder opened by its own opened domain,
exactly as `denote`'s binder clauses open it, so the `∀`-tower and
the λ-tower over one telescope read one list. -/
@[expose] def teleDoms (acval : Name → (Name → Nat) → Term) (env : Env) (φ : Name → Nat)
    (D : Nat) : List Expr → List Expr → Option (List Term)
  | _, [] => some []
  | os, ty :: tys => do
    let a ← denote acval env φ (D + os.length) (ty.instantiateList os 0)
    let r ← teleDoms acval env φ D (.fvar (D + os.length) (ty.instantiateList os 0) :: os) tys
    pure (a :: r)

/-- `teleDoms`'s read list is the telescope's own length. -/
theorem teleDoms_length {D : Nat} :
    ∀ {os tys : List Expr} {ds : List Term},
      teleDoms acval env φ D os tys = some ds → ds.length = tys.length
  | _, [], _, h => by
    simp only [teleDoms, Option.some.injEq] at h
    simp [← h]
  | os, _ :: tys, ds, h => by
    simp only [teleDoms] at h
    obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [pure, Option.some.injEq] at h
    rw [← h]
    simp [teleDoms_length hr]

/-- **The `∀`-tower over a telescope, read**: its domains are the
telescope's domains (`teleDoms`), and its body is read with the
binders opened. -/
theorem denote_mkPisOf {D : Nat} :
    ∀ (tele : List Expr) (X : Expr) (q : Nat) (os : List Expr)
      (P : Term),
      LocList D q os →
      denote acval env φ (D + q) ((Expr.mkPisOf tele X).instantiateList os 0) = some P →
      ∃ (ds : List Term) (Xr : Term) (os' : List Expr),
        P = mkPisAV ds Xr ∧
        teleDoms acval env φ D os tele = some ds ∧
        LocList D (q + tele.length) os' ∧
        denote acval env φ (D + (q + tele.length)) (X.instantiateList os' 0) = some Xr
  | [], X, q, os, P, hos, hP => by
    refine ⟨[], P, os, rfl, ?_, by simpa using hos, by simpa [Expr.mkPisOf] using hP⟩
    simp [teleDoms]
  | ty :: bs, X, q, os, P, hos, hP => by
    have hq : os.length = q := hos.1
    simp only [Expr.mkPisOf, Expr.instantiateList] at hP
    rw [denote_forallE] at hP
    obtain ⟨ta, hta, hP⟩ := Option.bind_eq_some_iff.mp hP
    obtain ⟨ba, hba, hP⟩ := Option.bind_eq_some_iff.mp hP
    obtain rfl : P = .pi ta ba := (Option.some.inj hP).symm
    rw [← Expr.instantiateList_cons, show D + q + 1 = D + (q + 1) from by omega] at hba
    obtain ⟨ds, Xr, os', rfl, hdoms, hos', hX⟩ :=
      denote_mkPisOf bs X (q + 1) _ ba (hos.cons _) hba
    refine ⟨ta :: ds, Xr, os', rfl, ?_,
      by simpa [Nat.add_assoc, Nat.add_comm 1] using hos',
      by simpa [Nat.add_assoc, Nat.add_comm 1] using hX⟩
    show teleDoms acval env φ D os (ty :: bs) = some (ta :: ds)
    rw [teleDoms, hq, hta, hdoms]
    rfl

/-! ## A frame-bounded term's value does not see where it is opened -/

/-- `m` fresh openers above the frame `B`. -/
@[expose] def locOpen (B m : Nat) : List Expr :=
  (List.range m).map fun j => .fvar (B + m - 1 - j) (.sort .zero)

theorem locOpen_locList (B m : Nat) : LocList B m (locOpen B m) := by
  refine ⟨by simp [locOpen], fun j hj => ⟨.sort .zero, ?_⟩⟩
  simp [locOpen, List.getElem?_range hj]

theorem LocList.take {B d m : Nat} {xs : List Expr} (h : LocList B d xs) (hm : m ≤ d) :
    LocList (B + (d - m)) m (xs.take m) := by
  refine ⟨by rw [List.length_take, h.1]; omega, fun j hj => ?_⟩
  obtain ⟨ty, hty⟩ := h.2 j (by omega)
  refine ⟨ty, ?_⟩
  rw [List.getElem?_take, ite_eq_left hj, hty]
  congr 2
  omega

end ConLeche.Model
