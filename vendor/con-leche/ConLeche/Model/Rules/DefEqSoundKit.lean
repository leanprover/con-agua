module

-- `RedSoundKit` is the SHARED kit: `DenoteSpine`'s list algebra,
-- `frame_spine`, `denote_mkAppN(_inv)`, the
-- `PiChain` guard and the tower entry's reading live there
public import ConLeche.Model.Rules.RedSoundKit
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Model.CtxOkKit
import ConLeche.Verify.Denote.Lemmas
import ConLeche.Verify.Denote.ErasedEq
import ConLeche.Verify.PropRead
import ConLeche.Verify.Denote.Closed
import ConLeche.Verify.InstLevels
import ConLeche.Model.Reading.Levels
import ConLeche.Rules.Rigid

public section

/-!
# The definitional-equality soundness kit (task #305)

The plumbing the per-rule lemmas of `Model/Rules/DefEqSound.lean`
share: the frame/grading splitters at each node shape, the two `Nat`
constant readings, and `projNV`'s congruence — stated at the rules
tier's `Frame`/`Graded` vocabulary, so that no `Model/Rules` module is
stated over runs.
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-! ## The frame splitters -/

theorem Frame.app_fn {d : Nat} {f x : Expr} (h : Frame d (.app f x)) :
    Frame d f := by
  obtain ⟨hw, hb, hL⟩ := h
  simp only [Expr.WScoped] at hw
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact ⟨hw.1, hb.1, fun l hl => hL l (by simp [Expr.fvarLeaves, hl])⟩

theorem Frame.app_arg {d : Nat} {f x : Expr} (h : Frame d (.app f x)) :
    Frame d x := by
  obtain ⟨hw, hb, hL⟩ := h
  simp only [Expr.WScoped] at hw
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact ⟨hw.2, hb.2, fun l hl => hL l (by simp [Expr.fvarLeaves, hl])⟩

theorem Frame.proj_arg {d : Nat} {s : Name} {i : Nat} {e : Expr}
    (h : Frame d (.proj s i e)) : Frame d e := by
  obtain ⟨hw, hb, hL⟩ := h
  simp only [Expr.WScoped] at hw
  simp only [Expr.looseBVarsBounded] at hb
  exact ⟨hw, hb, fun l hl => hL l (by simp [Expr.fvarLeaves, hl])⟩

/-- The opened body's frame, at an arbitrary (well-framed) domain. -/
theorem Frame.open_body {d : Nat} {ty' bd : Expr} (hty' : Frame d ty')
    (hwb : Expr.WScoped d bd) (hbb : bd.looseBVarsBounded 1 = true)
    (hLb : Expr.LeavesBounded bd) :
    Frame (d + 1) (bd.instantiate1 (.fvar d ty')) := by
  refine ⟨Expr.WScoped.instantiate1 hty'.1 0 hwb,
    ConLeche.looseBVarsBounded_instantiate1 bd 0 hbb, ?_⟩
  intro l hl
  rcases ConLeche.Expr.fvarLeaves_instantiate1 bd 0 hl with h2 | h2
  · exact hLb l h2
  · rw [ConLeche.Expr.fvarLeaves] at h2
    rcases List.mem_cons.mp h2 with rfl | h3
    · exact hty'.2.1
    · exact hty'.2.2 l h3

theorem Frame.forallE_ty {d : Nat} {ty bd : Expr}
    (h : Frame d (.forallE ty bd)) : Frame d ty := by
  obtain ⟨hw, hb, hL⟩ := h
  simp only [Expr.WScoped] at hw
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact ⟨hw.1, hb.1, fun l hl => hL l (by simp [Expr.fvarLeaves, hl])⟩

theorem Frame.forallE_open {d : Nat} {ty bd ty' : Expr}
    (h : Frame d (.forallE ty bd))
    (hty' : Frame d ty') :
    Frame (d + 1) (bd.instantiate1 (.fvar d ty')) := by
  obtain ⟨hw, hb, hL⟩ := h
  simp only [Expr.WScoped] at hw
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact Frame.open_body hty' hw.2 hb.2
    (fun l hl => hL l (by simp [Expr.fvarLeaves, hl]))

theorem Frame.lam_ty {d : Nat} {ty bd : Expr}
    (h : Frame d (.lam ty bd)) : Frame d ty := by
  obtain ⟨hw, hb, hL⟩ := h
  simp only [Expr.WScoped] at hw
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact ⟨hw.1, hb.1, fun l hl => hL l (by simp [Expr.fvarLeaves, hl])⟩

theorem Frame.lam_open {d : Nat} {ty bd ty' : Expr}
    (h : Frame d (.lam ty bd))
    (hty' : Frame d ty') :
    Frame (d + 1) (bd.instantiate1 (.fvar d ty')) := by
  obtain ⟨hw, hb, hL⟩ := h
  simp only [Expr.WScoped] at hw
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact Frame.open_body hty' hw.2 hb.2
    (fun l hl => hL l (by simp [Expr.fvarLeaves, hl]))

theorem Frame.of_not_hasFvar {d : Nat} {e : Expr} (hf : e.hasFvar = false)
    (hb : e.looseBVarsBounded 0 = true) : Frame d e :=
  ⟨Expr.WScoped.of_not_hasFvar hf, hb, Expr.LeavesBounded.of_not_hasFvar hf⟩

/-! ## The grading splitters, at `Graded` -/

theorem denote_open_rename {acval : Name → (Name → Nat) → Term}
    {d : Nat} {bd ty ty' : Expr} {ba : Term}
    (h : denote acval env φ (d + 1) (bd.instantiate1 (.fvar d ty))
      = some ba) :
    denote acval env φ (d + 1) (bd.instantiate1 (.fvar d ty'))
      = some ba := by
  rw [denote_erasedEq (Expr.ErasedEq.instantiate1 (Expr.ErasedEq.rfl bd)
    (show Expr.ErasedEq (.fvar d ty') (.fvar d ty) from rfl))]
  exact h

/-! ## The constant congruence -/

/-- The same constant at level-equivalent instantiations has one
reading. -/
theorem acval_const_congr {m : EnvModel V env}
    {d : Nat} {n : Name} {us us' : List Level} {aa ba : Term}
    (hlev : Level.isEquivList us us' = some true)
    (hda : denote m.acval env φ d (.const n us) = some aa)
    (hdb : denote m.acval env φ d (.const n us') = some ba) :
    aa = ba := by
  rw [denote] at hda hdb
  cases hf : env.find? n with
  | none => rw [hf] at hda; exact nomatch hda
  | some ci =>
    rw [hf] at hda hdb
    dsimp only at hda hdb
    split at hda
    · split at hdb
      · rw [← Option.some.inj hda, ← Option.some.inj hdb]
        refine m.acval_params n ci hf _ _ ?_
        intro p _
        exact Level.substFn_of_evalEqList _
          (Level.isEquivList_sound hlev φ) p
      · exact nomatch hdb
    · exact nomatch hda

/-! ## The proof-irrelevance fast arm: the shared facts

The justification itself (`prf_of_isProofFast`) is `ProofFastSound.lean`. -/

/-- Every application of `pt` is `pt` (`app_pt`, folded along a spine). -/
theorem foldl_app_pt' {ρ : Nat → V} : ∀ (as : List Term),
    as.foldl (fun r a => app r (interp V ρ a)) (pt : V) = pt
  | [] => rfl
  | a :: as => by rw [List.foldl_cons, app_pt]; exact foldl_app_pt' as

/-- A spine on a `pt`-valued head interprets to `pt`. -/
theorem interp_mkAppN_pt {ρ : Nat → V} {f : Term}
    (hf : interp V ρ f = pt) (as : List Term) :
    interp V ρ (Term.mkAppN f as) = pt := by
  rw [interp_mkAppN, hf]
  exact foldl_app_pt' as

/-- The kernel's "definitely `Prop`" test on a datum: it holds at every
valuation. -/
theorem holds_of_isProp {pw : PropWhen}
    (h : pw.isProp = true) (φ : Name → Nat) : pw.holds φ = true := by
  match pw, h with
  | .ifAllZero [], _ => rfl

/-! ## Leaves of a spine's head -/

/-- A leaf of a spine's head is a leaf of the spine. -/
theorem mem_fvarLeaves_mkAppN : ∀ (as : List Expr) (f : Expr)
    (l : Nat × Expr), l ∈ f.fvarLeaves →
    l ∈ (Expr.mkAppN f as).fvarLeaves
  | [], _, _, h => h
  | a :: as, f, l, h =>
    mem_fvarLeaves_mkAppN as (.app f a) l (by simp [Expr.fvarLeaves, h])

/-- A leaf of a term's head is a leaf of the term. -/
theorem mem_fvarLeaves_of_getAppFn' {a hd : Expr} {l : Nat × Expr}
    (h : a.getAppFn = hd) (hl : l ∈ hd.fvarLeaves) : l ∈ a.fvarLeaves := by
  rw [← ConLeche.Expr.mkAppN_getApp a, h]
  exact mem_fvarLeaves_mkAppN _ _ _ hl

/-- The leaf of a term's head fvar is a leaf of the term. -/
theorem mem_fvarLeaves_of_getAppFn {a ty : Expr} {idx : Nat}
    (h : a.getAppFn = .fvar idx ty) : (idx, ty) ∈ a.fvarLeaves :=
  mem_fvarLeaves_of_getAppFn' h (by simp [Expr.fvarLeaves])

/-- The leaves of an fvar's type are leaves of the fvar. -/
theorem mem_fvarLeaves_of_ty {ty : Expr} {idx : Nat}
    {l : Nat × Expr} (h : l ∈ ty.fvarLeaves) :
    l ∈ (Expr.fvar idx ty).fvarLeaves := by
  simp [Expr.fvarLeaves, h]

/-! ## The η-projection spelling, unfolded locally

`rw [ConLeche.etaProjs]` would reference the function's EQUATION
LEMMA, generated in whichever module first forces it.  The checker's
definitions are `@[expose]`d, so the clause is available by `rfl`
here, in this tier's own module, and the proof term names nothing
outside it. -/

theorem etaProjs_eq (T : Name) (b : Expr) (nF : Nat) :
    ConLeche.etaProjs T b nF = (List.range nF).map fun j => Expr.proj T j b := by
  rfl

/-! ## Proof irrelevance at the io grade (task #342 L18)

The fragment's `eq_pt_of_IORel_prop`: a term whose io-inferred type's
io-inferred sort reduces to `Prop` is the point.  A member of the type:
the type is a truth value.  Hereditary: the type is a ∀ whose sort is
`Prop`, so its body's sort is `Prop` (inversion of `Infer.forallE` at
the syntax, `Sound.lean`; a sort reduces only to itself), and the
application at the hereditary clause's witness is the point by the
body's claim — against the witness.  The recursion over the ∀'s body is
`Sound.lean`'s `prop_pt_io` (it needs the body's inference claim); the
steps are here. -/

/-- The member half: a member of a type whose type reduces to a sort
evaluating to zero is the point ("not pt" source (1): the type and its
type are types). -/
theorem propPt_of_mem {m : EnvModel V env} {d : Nat} {T tt : Expr} {w : Level}
    (hsem : InferSemIO m φ d T tt) (hrs : RedSem m φ d tt (.sort w))
    (hr : Red env d tt (.sort w)) (hw0 : w.eval φ = 0)
    (hfT : Frame d T) {Δa : List Term} {ta : Term}
    (hCT : CtxOkS m φ d Δa T) (hT : denote m.acval env φ d T = some ta)
    (ρ : Nat → V) (v : V) (hρ : Sat V Δa ρ) (hLT : LeavesGr m φ d T ρ)
    (hm : IOMem m φ d T ρ v) : v = pt := by
  obtain ⟨hwT, hvm⟩ := hm.of_reading hT
  obtain ⟨hftt, hsub, tta, htta, hrow⟩ := hsem hfT hCT hT
  rcases (hrow ρ hρ hLT hwT.1).1 with h | h | h
  · -- "not pt" source (1): the type is a type
    exact absurd h hwT.ne_pt
  · obtain ⟨hwtt, hTm⟩ := h.of_reading htta
    obtain ⟨-, -, sa, hsa, hs⟩ := hrs hftt (hCT.of_subset hsub) htta
    rw [denote_sort] at hsa
    obtain rfl : sa = Term.sort (w.eval φ) := (Option.some.inj hsa).symm
    -- "not pt" source (1): the type's type is a type
    obtain ⟨-, heq⟩ := hs ρ hρ (hLT.of_subset hsub) hwtt.1 hwtt.ne_pt
    rw [heq, interp_sort, hw0] at hTm
    exact mem_univ_zero hTm hvm
  · obtain ⟨_, _, rfl⟩ := h.forallE
    exact nomatch Red.rigid hr trivial

/-- At a type that is not a ∀ the io claim is the point or a member. -/
theorem propPt_of_not_forallE {m : EnvModel V env} {d : Nat} {T tt : Expr} {w : Level}
    (hsem : InferSemIO m φ d T tt) (hrs : RedSem m φ d tt (.sort w))
    (hr : Red env d tt (.sort w)) (hw0 : w.eval φ = 0)
    (hnf : ∀ ty body, T ≠ .forallE ty body) : PropPt m φ d T := by
  intro hfT Δa ta hCT hT ρ v hρ hLT h
  rcases h.of_not_forallE hnf with h | h
  · exact h
  · exact propPt_of_mem hsem hrs hr hw0 hfT hCT hT ρ v hρ hLT h

/-- At a ∀: the member half as above; the hereditary half is the
point at its witness by the body's claim, a contradiction. -/
theorem propPt_forallE {m : EnvModel V env} {d : Nat} {ty body tt : Expr}
    {w : Level}
    (hsem : InferSemIO m φ d (.forallE ty body) tt) (hrs : RedSem m φ d tt (.sort w))
    (hr : Red env d tt (.sort w)) (hw0 : w.eval φ = 0)
    (hbody : PropPt m φ (d + 1) (body.instantiate1 (.fvar d ty))) :
    PropPt m φ d (.forallE ty body) := by
  intro hfT Δa ta hCT hT ρ v hρ hLT h
  rcases h with h | h | h
  · exact h
  · exact propPt_of_mem hsem hrs hr hw0 hfT hCT hT ρ v hρ hLT h
  · rw [IOHered_forallE] at h
    obtain ⟨tya, htya, hwT, -, ⟨x₀, hx₀, hne⟩, hall⟩ := h
    exact absurd (hbody (hfT.forallE_open hfT.forallE_ty)
      (CtxOkS.openS hCT.forallE_ty hCT.forallE_body htya)
      (ta := (denote m.acval env φ (d + 1) (body.instantiate1 (.fvar d ty))).getD
        default) (by
          obtain ⟨_, ba, -, hba, -⟩ := denote_forallE_inv hT
          rw [hba]; rfl)
      (cons x₀ ρ) _ (Sat_cons V hρ hx₀)
      (LeavesGr.open hCT.forallE_ty hCT.forallE_body hLT.forallE_ty hLT.forallE_body
        htya hwT)
      (hall x₀ hx₀)) hne

/-- A ∀'s sort `imax u v` reducing to a sort that evaluates to zero:
`v` evaluates to zero (a sort reduces only to itself). -/
theorem eval_zero_of_red_imax {d : Nat} {u v w : Level}
    (hr : Red env d (.sort (.imax u v)) (.sort w)) (hw0 : w.eval φ = 0) :
    v.eval φ = 0 := by
  have h := Red.rigid hr trivial
  injection h with h
  subst h
  revert hw0
  simp only [Level.eval]
  split
  · next h => exact fun _ => h
  · next h => exact fun h' => absurd (Nat.max_eq_zero_iff.mp h').2 h

end ConLeche.Model.Rules
