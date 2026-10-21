module

public import ConLeche.Model.Inductives.NestPosAcc
public import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Env.LfpAcc

public section

/-!
# Accessibility hole relations, truncated and extended

The counterparts of `HoleRel.drop`, `HoleRel.dropBase` and `HoleRel.extendEmpty`
(`ContFrame.lean`) for the accessibility hole relation `HoleRelA`:

* `HoleRelA.drop`: the relation seen at a depth at or above every hole
  (a container instance's key depth), the frames kept;
* `HoleRelA.dropBase`: the relation seen at the block's own depth, the
  frames forgotten (a cached instantiation's parameters lie below every
  frame hole);
* `HoleRelA.extendEmpty`: a frameless relation at the block's own depth
  extended by enclosing frames holding `∅` on both sides — their holes are
  blind (`∅` applied is `∅`) and never hold `pt`.

The admissible items move with the positions (`holeQ_shift`,
`holeQ_nil`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules

open ConLeche (Env Expr Name Level NestCtx NestKey NestHole)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {φ : Name → Nat} {w : Nat}

/-! ## The admissible items, moved -/

/-- The admissible items `k` positions further down. -/
theorem holeQ_shift {ctx : NestCtx} {prog : List NestHole} {d k i n : Nat}
    (h : HoleQ ctx prog d i n) : HoleQ ctx prog (d + k) (i + k) n := by
  rcases h with ⟨t, ht, hlt, rfl, hn⟩ | ⟨j, hk, hj, hlt, rfl, hn⟩
  · exact Or.inl ⟨t, ht, by omega, by omega, hn⟩
  · exact Or.inr ⟨j, hk, hj, by omega, by omega, hn⟩

/-- The member holes are admissible under any frames. -/
theorem holeQ_nil {ctx : NestCtx} {prog : List NestHole} {d i n : Nat}
    (h : HoleQ ctx [] d i n) : HoleQ ctx prog d i n := by
  rcases h with h | ⟨j, hk, hj, -⟩
  · exact Or.inl h
  · simp at hj

/-- An item of the frame `n` positions down is its item `n` positions up. -/
theorem holds_drop {ρ : Nat → V} {n : Nat} {o : Occ V} :
    Holds (fun i => ρ (i + n)) o ↔ Holds ρ (o.1 + n, o.2) := Iff.rfl

/-! ## Truncation -/

/-- **The accessibility hole relation, truncated** at a depth `h` at or
above every hole: the frame's walk sees the context below `h`. -/
theorem HoleRelA.drop {ctx : NestCtx} {prog : List NestHole} {d : Nat} {Δa : List Term}
    {R : FrameRel V} (hR : HoleRelA m φ w ctx prog d Δa R) {h : Nat}
    (_hhi : ctx.hiAt prog.length ≤ h) (hle : h ≤ d) :
    HoleRelA m φ w ctx prog h (Δa.drop (d - h)) (R.drop (d - h)) where
  dom := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    obtain ⟨h1, h2⟩ := hR.dom ρ ρ' hr
    exact ⟨Sat_drop h1 _, Sat_drop h2 _⟩
  agree := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ i hi
    refine hR.agree ρ ρ' hr (i + (d - h)) fun hp => hi ?_
    obtain ⟨h1, h2, h3⟩ := hp
    refine ⟨by omega, ?_, ?_⟩ <;> omega
  dsScoped := hR.dsScoped
  symm := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    exact ⟨ρ', ρ, hR.symm ρ ρ' hr, rfl, rfl⟩
  ptFree hw := by
    rintro _ _ ⟨ρ, ρ₀, hr, rfl, rfl⟩ i vs hQ
    have hQ' : HoleQ ctx prog d (i + (d - h)) vs.length := by
      have := holeQ_shift (k := d - h) hQ
      rwa [show h + (d - h) = d by omega] at this
    exact hR.ptFree hw ρ ρ₀ hr (i + (d - h)) vs hQ'
  lrefl := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    exact ⟨ρ, ρ, hR.lrefl ρ ρ' hr, rfl, rfl⟩

/-- **The accessibility hole relation seen at the block's own depth**, the
frames forgotten. -/
theorem HoleRelA.dropBase {ctx : NestCtx} {prog : List NestHole} {d : Nat} {Δa : List Term}
    {R : FrameRel V} (hR : HoleRelA m φ w ctx prog d Δa R) (hle : ctx.hiAt prog.length ≤ d) :
    HoleRelA m φ w ctx [] (ctx.hiAt 0) (Δa.drop (d - ctx.hiAt 0)) (R.drop (d - ctx.hiAt 0)) where
  dom := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    obtain ⟨h1, h2⟩ := hR.dom ρ ρ' hr
    exact ⟨Sat_drop h1 _, Sat_drop h2 _⟩
  agree := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ i hi
    refine hR.agree ρ ρ' hr (i + (d - ctx.hiAt 0)) fun hp => hi ?_
    simp only [holeP, NestCtx.hiAt, List.length_nil] at hp hle ⊢
    omega
  dsScoped := by
    intro i hk h
    simp at h
  symm := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    exact ⟨ρ', ρ, hR.symm ρ ρ' hr, rfl, rfl⟩
  ptFree hw := by
    have hle0 : ctx.hiAt 0 ≤ d := by simp only [NestCtx.hiAt] at hle ⊢; omega
    rintro _ _ ⟨ρ, ρ₀, hr, rfl, rfl⟩ i vs hQ
    have hQ' : HoleQ ctx prog d (i + (d - ctx.hiAt 0)) vs.length := by
      have := holeQ_nil (prog := prog) (holeQ_shift (k := d - ctx.hiAt 0) hQ)
      rwa [show ctx.hiAt 0 + (d - ctx.hiAt 0) = d by omega] at this
    exact hR.ptFree hw ρ ρ₀ hr _ vs hQ'
  lrefl := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    exact ⟨ρ, ρ, hR.lrefl ρ ρ' hr, rfl, rfl⟩

/-! ## Empty enclosing frames -/

theorem consList_replicate_lt (n : Nat) (a : V) (σ : Nat → V) {i : Nat} (hi : i < n) :
    consList (List.replicate n a) σ i = a := by
  rw [consList_getD_of_lt _ _ _ (by simpa using hi)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate, List.length_replicate]
  rw [ite_eq_left (by omega)]
  rfl

/-- **Empty enclosing frames**: a frameless relation at the block's own
depth, extended by the enclosing frames of `prog` holding `∅` on both
sides (a `Sort 0` entry each). -/
theorem HoleRelA.extendEmpty {ctx : NestCtx} {Δ0 : List Term} {R00 : FrameRel V}
    (hR : HoleRelA m φ w ctx [] (ctx.hiAt 0) Δ0 R00) (prog : List NestHole)
    (hsc : ∀ (i : Nat) (hk : NestHole), prog.reverse[i]? = some hk → ∀ x ∈ hk.key.ds,
      Expr.WScoped (ctx.hiAt prog.length) x) :
    HoleRelA m φ w ctx prog (ctx.hiAt prog.length)
      (List.replicate prog.length (.sort 0) ++ Δ0)
      (fun σ σ' => ∃ ρ ρ', R00 ρ ρ' ∧ σ = consList (List.replicate prog.length empty) ρ ∧
        σ' = consList (List.replicate prog.length empty) ρ') where
  dom := extendEmpty_dom _ hR.dom
  agree := extendEmpty_agree _ hR.agree
  dsScoped := hsc
  symm := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    exact ⟨ρ', ρ, hR.symm ρ ρ' hr, rfl, rfl⟩
  ptFree hw := by
    rintro _ _ ⟨ρ, ρ₀, hr, rfl, rfl⟩ i vs hQ hpt
    -- an enclosing frame's hole holds nothing
    by_cases hip : i < prog.length
    · rw [consList_replicate_lt _ _ _ hip, foldlApp_empty] at hpt
      exact not_mem_empty _ hpt
    -- an admissible position beyond the enclosing frames is a member hole
    obtain ⟨j, rfl⟩ : ∃ j, i = j + prog.length := ⟨i - prog.length, by omega⟩
    have hQ0 : HoleQ ctx [] (ctx.hiAt 0) j vs.length := by
      rcases hQ with ⟨t, ht, hlt, hi, hn⟩ | ⟨jj, hk, hj, hlt, hi, hn⟩
      · refine Or.inl ⟨t, ht, ?_, ?_, hn⟩
        · simp only [NestCtx.hiAt] at hlt ⊢; omega
        · simp only [NestCtx.hiAt] at hi ⊢; omega
      · have := (List.getElem?_eq_some_iff.mp hj).1
        simp only [List.length_reverse] at this
        simp only [NestCtx.hiAt] at hi; omega
    have ea := consList_apply_add (List.replicate prog.length (empty : V)) ρ j
    rw [List.length_replicate] at ea
    rw [ea] at hpt
    exact hR.ptFree hw ρ ρ₀ hr j vs hQ0 hpt
  lrefl := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    exact ⟨ρ, ρ, hR.lrefl ρ ρ' hr, rfl, rfl⟩

end ConLeche.Model
