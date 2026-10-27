module

public import ConAgua.Arena.LevelSimp
public import ConAgua.Arena.LevelHeapRel
import ConAgua.Census.Attr
public import ConLeche.Kernel.Level
import Std.Data.DTreeMap.Internal.Operations
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-!
# `lv_comb`, `lv_simp`, `lv_nz` are `combining`, `simplify`, `isNeverZero`

Under the decoder `LvR` (`LevelHeapRel.lean`): if the model returns, the result denotes the
twin's value and the heap only grew (`HeapExt`). By induction on the L fuel, one case per
constructor of the argument's derivation; each allocation by `lhMkW_ext`.
-/


namespace L.Arena

open ConLeche

variable {N : Word → Name → Prop}

/-! ## Allocations -/

theorem mk_succ {m m' : Mem} {a x : Word} {l : Level} (h : lhMkW m 1 a 0 = some (x, m'))
    (ha : LvR N m a l) : HeapExt m m' ∧ LvR N m' x (.succ l) := by
  obtain ⟨he, hv, -⟩ := lhMkW_ext h
  exact ⟨he, .succ hv (ha.mono he)⟩

theorem mk_max {m m' : Mem} {a b x : Word} {l r : Level} (h : lhMkW m 2 a b = some (x, m'))
    (ha : LvR N m a l) (hb : LvR N m b r) : HeapExt m m' ∧ LvR N m' x (.max l r) := by
  obtain ⟨he, hv, -⟩ := lhMkW_ext h
  exact ⟨he, .max hv (ha.mono he) (hb.mono he)⟩

theorem mk_imax {m m' : Mem} {a b x : Word} {l r : Level} (h : lhMkW m 3 a b = some (x, m'))
    (ha : LvR N m a l) (hb : LvR N m b r) : HeapExt m m' ∧ LvR N m' x (.imax l r) := by
  obtain ⟨he, hv, -⟩ := lhMkW_ext h
  exact ⟨he, .imax hv (ha.mono he) (hb.mono he)⟩

theorem succK_inv {o : Option (Word × Mem)} {x : Word} {m' : Mem} (h : succK o = some (x, m')) :
    ∃ y m₁, o = some (y, m₁) ∧ lhMkW m₁ 1 y 0 = some (x, m') := by
  cases o with
  | none => simp [succK] at h
  | some v => exact ⟨v.1, v.2, rfl, h⟩

/-- The tag field of a related pointer. -/
theorem LvR.tag_zero {m : Mem} {p : Word} (h : LvR N m p .zero) : lvG m p = 0 := by
  cases h with | zero hv => simp [lvG, hv]

/-! ## `combining` -/

theorem combining_zero_right (l : Level) : Level.combining l .zero = l := by
  cases l <;> simp [Level.combining]

theorem combining_max (l r : Level) (h0 : l ≠ .zero) (h0' : r ≠ .zero)
    (hs : ¬ ((∃ a, l = .succ a) ∧ ∃ b, r = .succ b)) : Level.combining l r = .max l r := by
  cases l <;> cases r <;> simp_all [Level.combining]

/-- **`lv_comb` is `combining`.** -/
@[refines ConLeche.Level.combining]
theorem combW_ok (n : Nat) : ∀ (m m' : Mem) (l r x : Word) (L R : Level),
    LvR N m l L → LvR N m r R → combW n m l r = some (x, m') →
    HeapExt m m' ∧ LvR N m' x (Level.combining L R) := by
  induction n with
  | zero => intro m m' l r x L R _ _ h; simp [combW] at h
  | succ n ih =>
    intro m m' l r x L R hl hr h
    by_cases hz : lvG m l = 0
    · rw [combW.arm1 n m l r hz] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
      have : L = .zero := by cases hl <;> simp_all [lvG]
      subst this; exact ⟨HeapExt.refl _, by simpa [Level.combining] using hr⟩
    have hL : L ≠ .zero := by rintro rfl; exact hz hl.tag_zero
    by_cases hz' : lvG m r = 0
    · rw [combW.arm2 n m l r hz hz'] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
      have : R = .zero := by cases hr <;> simp_all [lvG]
      subst this; exact ⟨HeapExt.refl _, by rw [combining_zero_right]; exact hl⟩
    have hR : R ≠ .zero := by rintro rfl; exact hz' hr.tag_zero
    by_cases hs : lvG m l = 1 ∧ lvG m r = 1
    · rw [combW.arm3 n m l r hz hz' hs] at h
      obtain ⟨y, m₁, hy, hm⟩ := succK_inv h
      cases hl with
      | succ hv hl₁ =>
        cases hr with
        | succ hv' hr₁ =>
          rw [(lv_fields hv).2.1, (lv_fields hv').2.1] at hy
          obtain ⟨he₁, hy'⟩ := ih _ _ _ _ _ _ _ hl₁ hr₁ hy
          obtain ⟨he₂, hx⟩ := mk_succ hm hy'
          exact ⟨he₁.trans he₂, by simpa [Level.combining] using hx⟩
        | _ => simp_all [lvG]
      | _ => simp_all [lvG]
    · rw [combW.arm4 n m l r hz hz' hs] at h
      obtain ⟨he, hx⟩ := mk_max h hl hr
      refine ⟨he, ?_⟩
      rw [combining_max L R hL hR]
      · exact hx
      · rintro ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
        apply hs
        cases hl; cases hr; simp_all [lvG]

/-! ## `simplify` -/

/-- con-leche's `imax` arm of `simplify`, on the simplified children. -/
def simpImax (ls rs : Level) : Level :=
  if ls = .zero || ls = .succ .zero then rs
  else match rs with
    | .zero => .zero
    | .succ _ => Level.combining ls rs
    | _ => .imax ls rs

theorem simplify_imax (l r : Level) :
    Level.simplify (.imax l r) = simpImax (Level.simplify l) (Level.simplify r) := by
  simp only [Level.simplify, simpImax]
  split
  · rfl
  · cases Level.simplify r <;> rfl

theorem imaxW_ok (n : Nat) (m m' : Mem) (x y z : Word) (S T : Level)
    (hx : LvR N m x S) (hy : LvR N m y T) (h : simpW.k_lv_simp_2 n 3 x (some (y, m)) = some (z, m')) :
    HeapExt m m' ∧ LvR N m' z (simpImax S T) := by
  -- the left test: `S = zero` or `S = succ zero`
  by_cases h0 : lvG m x = 0
  · rw [simpW.k_lv_simp_2.arm2 n 3 x y m (by decide) h0] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
    have : S = .zero := by cases hx <;> simp_all [lvG]
    subst this; exact ⟨HeapExt.refl _, by simpa [simpImax] using hy⟩
  have hS0 : S ≠ .zero := by rintro rfl; exact h0 hx.tag_zero
  by_cases h1 : lvG m x = 1 ∧ lvG m (lvA m x) = 0
  · rw [simpW.k_lv_simp_2.arm3 n 3 x y m (by decide) h0 h1.1 h1.2] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
    cases hx with
    | succ hv hc =>
      rw [(lv_fields hv).2.1] at h1
      cases hc with
      | zero => exact ⟨HeapExt.refl _, by simpa [simpImax] using hy⟩
      | _ => simp_all [lvG]
    | _ => simp_all [lvG]
  have hS1 : S ≠ .succ .zero := by
    rintro rfl
    apply h1
    cases hx with
    | succ hv hc =>
      rw [(lv_fields hv).2.1]; exact ⟨by simp [lvG, hv], hc.tag_zero⟩
  have hif : (S = .zero || S = .succ .zero) = false := by simp [hS0, hS1]
  have hj : simpW.k_lv_simp_2 n 3 x (some (y, m)) = simpW.j1 n x y m := by
    by_cases hx1 : lvG m x = 1
    · exact simpW.k_lv_simp_2.arm4 n 3 x y m (by decide) h0 hx1 (fun e => h1 ⟨hx1, e⟩)
    · exact simpW.k_lv_simp_2.arm5 n 3 x y m (by decide) h0 hx1
  rw [hj] at h
  by_cases h2 : lvG m y = 0
  · rw [simpW.j1.arm1 n x y m h2] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
    have : T = .zero := by cases hy <;> simp_all [lvG]
    subst this; exact ⟨HeapExt.refl _, by simpa [simpImax, hif] using hy⟩
  by_cases h3 : lvG m y = 1
  · rw [simpW.j1.arm2 n x y m h2 h3] at h
    obtain ⟨he, hz⟩ := combW_ok n m m' x y z S T hx hy h
    cases hy with
    | succ hv _ => exact ⟨he, by simpa [simpImax, hif] using hz⟩
    | _ => simp_all [lvG]
  · rw [simpW.j1.arm3 n x y m h2 h3] at h
    obtain ⟨he, hz⟩ := mk_imax h hx hy
    refine ⟨he, ?_⟩
    cases hy with
    | zero hv | succ hv _ => simp_all [lvG]
    | max _ _ _ | imax _ _ _ | param _ _ => simpa [simpImax, hif] using hz

/-- **`lv_simp` is `simplify`.** -/
@[refines ConLeche.Level.simplify]
theorem simpW_ok (n : Nat) : ∀ (m m' : Mem) (p x : Word) (L : Level),
    LvR N m p L → simpW n m p = some (x, m') → HeapExt m m' ∧ LvR N m' x (Level.simplify L) := by
  induction n with
  | zero => intro m m' p x L _ h; simp [simpW] at h
  | succ n ih =>
    intro m m' p x L hp h
    cases hp with
    | zero hv =>
      rw [simpW.arm1 n m p (Or.inl (by simp [lvG, hv]))] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨HeapExt.refl _, by simpa [Level.simplify] using LvR.zero hv⟩
    | param hv hn =>
      rw [simpW.arm1 n m p (Or.inr (by simp [lvG, hv]))] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨HeapExt.refl _, by simpa [Level.simplify] using LvR.param hv hn⟩
    | succ hv ha =>
      rw [simpW.arm2 n m p (by simp [lvG, hv]), (lv_fields hv).2.1,
        show lvG m p = 1 by simp [lvG, hv]] at h
      cases e₁ : simpW n m _ with
      | none => rw [e₁] at h; simp [simpW.k_lv_simp] at h
      | some v₁ =>
        obtain ⟨y, m₁⟩ := v₁
        rw [e₁, simpW.k_lv_simp.arm1 n 1 _ y m₁ rfl] at h
        obtain ⟨he₁, hy'⟩ := ih _ _ _ _ _ ha e₁
        obtain ⟨he₂, hx⟩ := mk_succ h hy'
        exact ⟨he₁.trans he₂, by simpa [Level.simplify] using hx⟩
    | max hv ha hb =>
      rw [simpW.arm2 n m p (by simp [lvG, hv]), (lv_fields hv).2.1, (lv_fields hv).2.2,
        show lvG m p = 2 by simp [lvG, hv]] at h
      cases e₁ : simpW n m _ with
      | none => rw [e₁] at h; simp [simpW.k_lv_simp] at h
      | some v₁ =>
        obtain ⟨x₁, m₁⟩ := v₁
        rw [e₁, simpW.k_lv_simp.arm2 n 2 _ x₁ m₁ (by decide)] at h
        obtain ⟨he₁, hx₁⟩ := ih _ _ _ _ _ ha e₁
        cases e₂ : simpW n m₁ _ with
        | none => rw [e₂] at h; simp [simpW.k_lv_simp_2] at h
        | some v₂ =>
          obtain ⟨y, m₂⟩ := v₂
          rw [e₂, simpW.k_lv_simp_2.arm1 n 2 x₁ y m₂ rfl] at h
          obtain ⟨he₂, hy⟩ := ih _ _ _ _ _ (hb.mono he₁) e₂
          obtain ⟨he₃, hz⟩ := combW_ok n _ _ _ _ _ _ _ (hx₁.mono he₂) hy h
          exact ⟨(he₁.trans he₂).trans he₃, by simpa [Level.simplify] using hz⟩
    | imax hv ha hb =>
      rw [simpW.arm2 n m p (by simp [lvG, hv]), (lv_fields hv).2.1, (lv_fields hv).2.2,
        show lvG m p = 3 by simp [lvG, hv]] at h
      cases e₁ : simpW n m _ with
      | none => rw [e₁] at h; simp [simpW.k_lv_simp] at h
      | some v₁ =>
        obtain ⟨x₁, m₁⟩ := v₁
        rw [e₁, simpW.k_lv_simp.arm2 n 3 _ x₁ m₁ (by decide)] at h
        obtain ⟨he₁, hx₁⟩ := ih _ _ _ _ _ ha e₁
        cases e₂ : simpW n m₁ _ with
        | none => rw [e₂] at h; simp [simpW.k_lv_simp_2] at h
        | some v₂ =>
          obtain ⟨y, m₂⟩ := v₂
          rw [e₂] at h
          obtain ⟨he₂, hy⟩ := ih _ _ _ _ _ (hb.mono he₁) e₂
          obtain ⟨he₃, hz⟩ := imaxW_ok n _ _ _ _ _ _ _ (hx₁.mono he₂) hy h
          exact ⟨(he₁.trans he₂).trans he₃, by rw [simplify_imax]; exact hz⟩

/-! ## `isNeverZero` -/

/-- **`lv_nz` is `isNeverZero`.** -/
@[refines ConLeche.Level.isNeverZero]
theorem nzW_ok (n : Nat) : ∀ (m : Mem) (p x : Word) (L : Level),
    LvR N m p L → nzW n m p = some x → x = if Level.isNeverZero L then 1 else 0 := by
  induction n with
  | zero => intro m p x L _ h; simp [nzW] at h
  | succ n ih =>
    intro m p x L hp h
    cases hp with
    | zero hv =>
      rw [nzW.arm4 n m p (by simp [lvG, hv]) (by simp [lvG, hv]) (by simp [lvG, hv])] at h
      simp at h; simp [Level.isNeverZero, h]
    | param hv _ =>
      rw [nzW.arm4 n m p (by simp [lvG, hv]) (by simp [lvG, hv]) (by simp [lvG, hv])] at h
      simp at h; simp [Level.isNeverZero, h]
    | succ hv _ =>
      rw [nzW.arm1 n m p (by simp [lvG, hv])] at h; simp at h; simp [Level.isNeverZero, h]
    | imax hv _ hb =>
      rw [nzW.arm3 n m p (by simp [lvG, hv]) (by simp [lvG, hv]) (by simp [lvG, hv]),
        (lv_fields hv).2.2] at h
      rw [ih _ _ _ _ hb h]
      rfl
    | @max _ a b l r hv ha hb =>
      rw [nzW.arm2 n m p (by simp [lvG, hv]) (by simp [lvG, hv]), (lv_fields hv).2.1,
        (lv_fields hv).2.2] at h
      cases e : nzW n m _ with
      | none => rw [e] at h; simp [nzW.k_lv_nz] at h
      | some y =>
        rw [e] at h
        have hy := ih _ _ _ _ ha e
        by_cases hy0 : y = 0
        · subst hy0; rw [nzW.k_lv_nz.arm2 _ _ _ _ (by simp)] at h
          rw [ih _ _ _ _ hb h]
          have hl : Level.isNeverZero l = false := by
            revert hy; cases Level.isNeverZero l <;> simp
          simp [Level.isNeverZero, hl]
        · rw [nzW.k_lv_nz.arm1 _ _ _ _ hy0] at h; simp at h
          have hl : Level.isNeverZero l = true := by
            revert hy; cases Level.isNeverZero l <;> simp_all
          simp [Level.isNeverZero, hl, ← h]

end L.Arena
