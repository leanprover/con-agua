module

public import ConAgua.Arena.LevelEquiv
public import ConAgua.Arena.LevelLeqRel
import ConAgua.Census.Attr
import ConAgua.Arena.LevelSimpRel

@[expose] public section

/-!
# `lv_leq_top`, `lv_equiv`, `lv_equivs` are `leq`, `isEquiv`, `isEquivList`

Under the decoder `LvR` (and `LvsR` for the lists in `POOL`), from `leqOK` (`LevelLeqRel.lean`)
at the entry's fuel `10^4` and `diff = 0`.
-/


namespace L.Arena

open ConLeche

variable {N : Word → Name → Prop}

theorem DR_zero : DR 4294967296 0 := by simp [DR]

/-- **`lv_leq_top` is `leq`.** -/
@[refines ConLeche.Level.leq ConLeche.Level.defaultFuel]
theorem leqTopW_ok (hN : NameRel N) (n : Nat) (m m' : Mem) (l r x : Word) (L R : Level)
    (hl : LvR N m l L) (hr : LvR N m r R) (h : leqTopW n m l r = some (x, m')) :
    HeapExt m m' ∧ x = encO (Level.leq L R) := by
  cases n with
  | zero => simp [leqTopW] at h
  | succ n =>
    rw [leqTopW_succ] at h
    rcases e₁ : simpW n m l with _ | ⟨x₁, m₁⟩ <;> simp only [e₁, ltK₁, reduceCtorEq] at h
    obtain ⟨he₁, hx₁⟩ := simpW_ok n _ _ _ _ _ hl e₁
    rcases e₂ : simpW n m₁ r with _ | ⟨y, m₂⟩ <;> simp only [e₂, ltK₁.ltK₂, reduceCtorEq] at h
    obtain ⟨he₂, hy⟩ := simpW_ok n _ _ _ _ _ (hr.mono he₁) e₂
    obtain ⟨he₃, hx⟩ := (leqOK hN n).1 _ _ _ _ _ _ _ _ _ 10000 0 (hx₁.mono he₂) hy rfl DR_zero
      (by decide) h
    exact ⟨(he₁.trans he₂).trans he₃, by rw [hx]; rfl⟩

theorem isEquiv_eq (L R : Level) :
    Level.isEquiv L R =
      if L = R then some true
      else if Level.simplify L = Level.simplify R then some true
      else (Level.leq L R).bind (fun c => if c then Level.leq R L else some false) := by
  simp only [Level.isEquiv, beq_iff_eq]; rfl

/-- **`lv_equiv` is `isEquiv`.** -/
@[refines ConLeche.Level.isEquiv]
theorem equivW_ok (hN : NameRel N) (n : Nat) (m m' : Mem) (l r x : Word) (L R : Level)
    (hl : LvR N m l L) (hr : LvR N m r R) (h : equivW n m l r = some (x, m')) :
    HeapExt m m' ∧ x = encO (Level.isEquiv L R) := by
  cases n with
  | zero => simp [equivW] at h
  | succ n =>
    rw [equivW_succ] at h
    rw [isEquiv_eq]
    cases e₀ : lvEqW n m l r with
    | none => rw [e₀] at h; simp [evK₁] at h
    | some z₀ =>
      rw [e₀] at h
      have hz₀ := lvEqW_ok hN n l r L R z₀ hl hr e₀
      simp only [Level.beq, decide_eq_true_eq] at hz₀
      by_cases eLR : L = R
      · simp only [eLR, ↓reduceIte] at hz₀; subst hz₀
        rw [evK₁_ne (hz := by decide)] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
        exact ⟨HeapExt.refl _, by simp [eLR, encO]⟩
      simp only [eLR, ↓reduceIte] at hz₀; subst hz₀
      rw [evK₁_zero] at h
      rcases e₁ : simpW n m l with _ | ⟨x₁, m₁⟩ <;> simp only [e₁, evK₁.evK₂, reduceCtorEq] at h
      obtain ⟨he₁, hx₁⟩ := simpW_ok n _ _ _ _ _ hl e₁
      rcases e₂ : simpW n m₁ r with _ | ⟨y, m₂⟩ <;> simp only [e₂, evK₁.evK₃, reduceCtorEq] at h
      obtain ⟨he₂, hy⟩ := simpW_ok n _ _ _ _ _ (hr.mono he₁) e₂
      have hx₁' := hx₁.mono he₂
      cases e₃ : lvEqW n m₂ x₁ y with
      | none => rw [e₃] at h; simp [evK₁.evK₄] at h
      | some z₁ =>
        rw [e₃] at h
        have hz₁ := lvEqW_ok hN n x₁ y _ _ z₁ hx₁' hy e₃
        simp only [Level.beq, decide_eq_true_eq] at hz₁
        by_cases eS : Level.simplify L = Level.simplify R
        · simp only [eS, ↓reduceIte] at hz₁; subst hz₁
          rw [evK₄_ne (hz := by decide)] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨he₁.trans he₂, by simp [eLR, eS, encO]⟩
        simp only [eS, ↓reduceIte] at hz₁; subst hz₁
        rw [evK₄_zero] at h
        simp only [eLR, eS, ↓reduceIte]
        cases e₄ : leqW n m₂ 10000 x₁ y 4294967296 with
        | none => rw [e₄] at h; simp [evK₁.evK₅] at h
        | some w₄ =>
          obtain ⟨z, m₃⟩ := w₄
          rw [e₄] at h
          obtain ⟨he₃, hz⟩ := (leqOK hN n).1 _ _ _ _ _ _ _ _ _ 10000 0 hx₁' hy rfl DR_zero
            (by decide) e₄
          have hlq : Level.leq L R = Level.leqCore 10000 (Level.simplify L) (Level.simplify R) 0 :=
            rfl
          by_cases hz2 : z = 2
          · subst hz2
            rw [evK₅_go] at h
            obtain ⟨he₄, hx⟩ := (leqOK hN n).1 _ _ _ _ _ _ _ _ _ 10000 0 (hy.mono he₃)
              (hx₁'.mono he₃) rfl DR_zero (by decide) h
            refine ⟨((he₁.trans he₂).trans he₃).trans he₄, ?_⟩
            rw [hlq, enc_eq2 hz, hx]; rfl
          · rw [evK₅_stop (hz := hz2)] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
            refine ⟨(he₁.trans he₂).trans he₃, ?_⟩
            rw [hlq]; rw [hz] at hz2 ⊢; exact (enc_stop_and hz2).symm

/-! ## Lists -/

/-- The words `A[a .. a + n)` are pointers to the levels `ls`. -/
inductive LvsR (N : Word → Name → Prop) (m : Mem) : Word → Word → List Level → Prop
  | nil {a : Word} : LvsR N m a 0 []
  | cons {a n : Word} {l : Level} {ls : List Level} : n ≠ 0 → LvR N m (prd m a) l →
      LvsR N m (a + 1) (n - 1) ls → LvsR N m a n (l :: ls)

theorem LvsR.mono {m m' : Mem} (he : HeapExt m m') {a n : Word} {ls : List Level}
    (h : LvsR N m a n ls) : LvsR N m' a n ls := by
  induction h with
  | nil => exact .nil
  | cons hn hl _ ih =>
    refine .cons hn ?_ ih
    rw [prd_congr _ (he.arr POOL (by decide) (by decide)) (he.arr POOL1 (by decide) (by decide))]
    exact hl.mono he

theorem LvsR.zero {m : Mem} {a : Word} {ls : List Level} (h : LvsR N m a 0 ls) : ls = [] := by
  cases h with
  | nil => rfl
  | cons hn _ _ => exact absurd rfl hn

theorem LvsR.ne {m : Mem} {a n : Word} {ls : List Level} (h : LvsR N m a n ls) (hn : n ≠ 0) :
    ∃ l ls', ls = l :: ls' ∧ LvR N m (prd m a) l ∧ LvsR N m (a + 1) (n - 1) ls' := by
  cases h with
  | nil => exact absurd rfl hn
  | cons _ hl hls => exact ⟨_, _, rfl, hl, hls⟩

/-- **`lv_equivs` is `isEquivList`.** -/
@[refines ConLeche.Level.isEquivList]
theorem equivsW_ok (hN : NameRel N) (n : Nat) : ∀ (m m' : Mem) (a ln b k x : Word)
    (Ls Rs : List Level), LvsR N m a ln Ls → LvsR N m b k Rs →
    equivsW n m a ln b k = some (x, m') → HeapExt m m' ∧ x = encO (Level.isEquivList Ls Rs) := by
  induction n with
  | zero => intro m m' a ln b k x Ls Rs _ _ h; simp [equivsW] at h
  | succ n ih =>
    intro m m' a ln b k x Ls Rs hL hR h
    by_cases c : ln = 0 ∨ k = 0
    · rw [equivsW_end n m a ln b k c] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
      refine ⟨HeapExt.refl _, ?_⟩
      rcases c with c | c
      · subst c; rw [hL.zero]
        by_cases hk : k = 0
        · subst hk; rw [hR.zero]; rfl
        · obtain ⟨r, rs, rfl, -, -⟩ := hR.ne hk
          simp [Ne.symm hk, Level.isEquivList, encO]
      · subst c; rw [hR.zero]
        by_cases hk : ln = 0
        · subst hk; rw [hL.zero]; rfl
        · obtain ⟨l, ls, rfl, -, -⟩ := hL.ne hk
          simp [hk, Level.isEquivList, encO]
    · rw [equivsW_cons n m a ln b k c] at h
      simp only [not_or] at c
      obtain ⟨l, ls, rfl, hl, hls⟩ := hL.ne c.1
      obtain ⟨r, rs, rfl, hr, hrs⟩ := hR.ne c.2
      cases e : equivW n m _ _ with
      | none => rw [e] at h; simp [esK] at h
      | some w =>
        obtain ⟨z, m₁⟩ := w
        rw [e] at h
        obtain ⟨he₁, hz⟩ := equivW_ok hN n _ _ _ _ _ _ _ hl hr e
        have heq : Level.isEquivList (l :: ls) (r :: rs) =
            (Level.isEquiv l r).bind (fun c => if c then Level.isEquivList ls rs else some false) := by
          simp only [Level.isEquivList]; rfl
        rw [heq]
        by_cases hz2 : z = 2
        · subst hz2
          rw [esK_go] at h
          obtain ⟨he₂, hx⟩ := ih _ _ _ _ _ _ _ _ _ (hls.mono he₁) (hrs.mono he₁) h
          refine ⟨he₁.trans he₂, ?_⟩
          rw [enc_eq2 hz, hx]; rfl
        · rw [esK_stop (hz := hz2)] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
          refine ⟨he₁, ?_⟩
          rw [hz] at hz2 ⊢; exact (enc_stop_and hz2).symm

end L.Arena
