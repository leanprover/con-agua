module

public import ConAgua.Arena.LevelLeq
public import ConAgua.Arena.LevelSimpRel
import ConAgua.Census.Attr

@[expose] public section

/-!
# The comparison refines con-leche's: `subst`, `leqCore`, `rest`, `imaxRules`, `byCases`

Under the decoder `LvR` (`LevelHeapRel.lean`), by induction on the L fuel:

* `substW_ok`: `lv_subst(l, k, v)` is `subst [K] [V] L` (one key);
* `leqOK`: the five functions of the comparison return the encoding (`encO`) of con-leche's
  `Option Bool`, with the fuel word equal to con-leche's fuel and the bias word
  `d = diff + 2^32`, as long as `|diff| + fuel` stays below `2^31` (it does: both start at
  `0` and `10^4`, and every step that moves `diff` by one spends one unit of fuel).
-/


namespace L.Arena

open ConLeche

variable {N : Word → Name → Prop}

/-! ## `subst` with one key -/

/-- **`lv_subst` is `subst` with one key.** -/
@[refines_part ConLeche.Level.subst "one key", refines_part ConLeche.Level.subst.go "one key"]
theorem substW_ok (hN : NameRel N) (n : Nat) : ∀ (m m' : Mem) (l k v x : Word) (L V : Level)
    (K : Name), LvR N m l L → N k K → LvR N m v V → substW n m l k v = some (x, m') →
    HeapExt m m' ∧ LvR N m' x (Level.subst [K] [V] L) := by
  induction n with
  | zero => intro m m' l k v x L V K _ _ _ h; simp [substW] at h
  | succ n ih =>
    intro m m' l k v x L V K hl hk hv h
    cases hl with
    | zero hw =>
      rw [substW_zero n m l k v (lv_fields hw).1] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨HeapExt.refl _, by simpa [Level.subst] using LvR.zero hw⟩
    | @param _ a b nm hw hn =>
      by_cases e : a = k
      · subst e
        rw [substW_hit n m l a v (lv_fields hw).1 (lv_fields hw).2.1] at h
        simp at h; obtain ⟨rfl, rfl⟩ := h
        rw [hN.fn _ _ _ hk hn]
        exact ⟨HeapExt.refl _, by simpa [Level.subst, Level.subst.go] using hv⟩
      · rw [substW_miss n m l k v (lv_fields hw).1 (by rw [(lv_fields hw).2.1]; exact e)] at h
        simp at h; obtain ⟨rfl, rfl⟩ := h
        have hne : K ≠ nm := fun h' => e (hN.inj _ _ _ hn (h' ▸ hk))
        exact ⟨HeapExt.refl _, by simpa [Level.subst, Level.subst.go, hne] using LvR.param hw hn⟩
    | succ hw ha =>
      rw [substW_succ n m l k v (lv_fields hw).1, (lv_fields hw).2.1] at h
      obtain ⟨y, m₁, hy, hm⟩ := succK_inv h
      obtain ⟨he₁, hy'⟩ := ih _ _ _ _ _ _ _ _ _ ha hk hv hy
      obtain ⟨he₂, hx⟩ := mk_succ hm hy'
      exact ⟨he₁.trans he₂, by simpa [Level.subst] using hx⟩
    | max hw ha hb =>
      rw [substW_bin n m l k v (by simp [lvG, hw]) (by simp [lvG, hw]) (by simp [lvG, hw]),
        (lv_fields hw).1, (lv_fields hw).2.1, (lv_fields hw).2.2] at h
      rcases e₁ : substW n m _ k v with _ | ⟨x₁, m₁⟩ <;> rw [e₁] at h
      · simp [subK₁] at h
      rw [subK₁_some] at h
      obtain ⟨he₁, hx₁⟩ := ih _ _ _ _ _ _ _ _ _ ha hk hv e₁
      rcases e₂ : substW n m₁ _ k v with _ | ⟨y, m₂⟩ <;> rw [e₂] at h
      · simp [subK₂] at h
      rw [subK₂_some] at h
      obtain ⟨he₂, hy⟩ := ih _ _ _ _ _ _ _ _ _ (hb.mono he₁) hk (hv.mono he₁) e₂
      obtain ⟨he₃, hz⟩ := mk_max h (hx₁.mono he₂) hy
      exact ⟨(he₁.trans he₂).trans he₃, by simpa [Level.subst] using hz⟩
    | imax hw ha hb =>
      rw [substW_bin n m l k v (by simp [lvG, hw]) (by simp [lvG, hw]) (by simp [lvG, hw]),
        (lv_fields hw).1, (lv_fields hw).2.1, (lv_fields hw).2.2] at h
      rcases e₁ : substW n m _ k v with _ | ⟨x₁, m₁⟩ <;> rw [e₁] at h
      · simp [subK₁] at h
      rw [subK₁_some] at h
      obtain ⟨he₁, hx₁⟩ := ih _ _ _ _ _ _ _ _ _ ha hk hv e₁
      rcases e₂ : substW n m₁ _ k v with _ | ⟨y, m₂⟩ <;> rw [e₂] at h
      · simp [subK₂] at h
      rw [subK₂_some] at h
      obtain ⟨he₂, hy⟩ := ih _ _ _ _ _ _ _ _ _ (hb.mono he₁) hk (hv.mono he₁) e₂
      obtain ⟨he₃, hz⟩ := mk_imax h (hx₁.mono he₂) hy
      exact ⟨(he₁.trans he₂).trans he₃, by simpa [Level.subst] using hz⟩

/-- `lv_subsimp` is `simplify ∘ subst`. -/
theorem ssW_ok (hN : NameRel N) (n : Nat) (m m' : Mem) (l k v x : Word) (L V : Level) (K : Name)
    (hl : LvR N m l L) (hk : N k K) (hv : LvR N m v V) (h : ssW n m l k v = some (x, m')) :
    HeapExt m m' ∧ LvR N m' x (Level.simplify (Level.subst [K] [V] L)) := by
  cases n with
  | zero => simp [ssW] at h
  | succ n =>
    rw [ssW_succ] at h
    rcases e : substW n m l k v with _ | ⟨y, m₁⟩ <;> simp only [e, ssK, reduceCtorEq] at h
    obtain ⟨he₁, hy⟩ := substW_ok hN n _ _ _ _ _ _ _ _ _ hl hk hv e
    obtain ⟨he₂, hx⟩ := simpW_ok n _ _ _ _ _ hy h
    exact ⟨he₁.trans he₂, hx⟩

/-- `lv_dist1` builds `max (imax a k) b`. -/
theorem dist1W_ok (m m' : Mem) (a k b x : Word) (A K B : Level) (ha : LvR N m a A)
    (hk : LvR N m k K) (hb : LvR N m b B) (h : dist1W m a k b = some (x, m')) :
    HeapExt m m' ∧ LvR N m' x (.max (.imax A K) B) := by
  rw [dist1W_eq] at h
  rcases e : lhMkW m 3 a k with _ | ⟨y, m₁⟩ <;> simp only [e, d1K, reduceCtorEq] at h
  obtain ⟨he₁, hy⟩ := mk_imax e ha hk
  obtain ⟨he₂, hx⟩ := mk_max h hy (hb.mono he₁)
  exact ⟨he₁.trans he₂, hx⟩

/-- `lv_dist2` builds `simplify (max (imax a j) (imax a k))`. -/
theorem dist2W_ok (n : Nat) (m m' : Mem) (a j k x : Word) (A J K : Level) (ha : LvR N m a A)
    (hj : LvR N m j J) (hk : LvR N m k K) (h : dist2W n m a j k = some (x, m')) :
    HeapExt m m' ∧ LvR N m' x (Level.simplify (.max (.imax A J) (.imax A K))) := by
  cases n with
  | zero => simp [dist2W] at h
  | succ n =>
    rw [dist2W_succ] at h
    rcases e₁ : lhMkW m 3 a j with _ | ⟨y₁, m₁⟩ <;> simp only [e₁, d2K₁, reduceCtorEq] at h
    obtain ⟨he₁, hy₁⟩ := mk_imax e₁ ha hj
    rcases e₂ : lhMkW m₁ 3 a k with _ | ⟨y₂, m₂⟩ <;> simp only [e₂, d2K₁.d2K₂, reduceCtorEq] at h
    obtain ⟨he₂, hy₂⟩ := mk_imax e₂ (ha.mono he₁) (hk.mono he₁)
    cases e₃ : lhMkW m₂ 2 y₁ y₂ with
    | none => rw [e₃] at h; simp [ssK] at h
    | some w₃ =>
      obtain ⟨y₃, m₃⟩ := w₃
      rw [e₃, ssK_some] at h
      obtain ⟨he₃, hy₃⟩ := mk_max e₃ (hy₁.mono he₂) hy₂
      obtain ⟨he₄, hx⟩ := simpW_ok n _ _ _ _ _ hy₃ h
      exact ⟨((he₁.trans he₂).trans he₃).trans he₄, hx⟩

/-! ## Tags, the bias word, the fuel word -/

/-- The store's tag of a level's head constructor. -/
def tagOf : Level → Word
  | .zero => 0 | .succ _ => 1 | .max _ _ => 2 | .imax _ _ => 3 | .param _ => 4

/-- The tag of an `imax`'s right child (`7` for any other level). -/
def rtagOf : Level → Word
  | .imax _ b => tagOf b | _ => 7

theorem LvR.tag {m : Mem} {p : Word} {L : Level} (h : LvR N m p L) : lvG m p = tagOf L := by
  cases h <;> simp_all [lvG, tagOf]

theorem LvR.rtag {m : Mem} {p : Word} {L : Level} (h : LvR N m p L) (h3 : lvG m p = 3) :
    lvG m (lvB m p) = rtagOf L := by
  cases h with
  | imax hv _ hb => rw [(lv_fields hv).2.2, hb.tag]; rfl
  | _ => simp_all [lvG]

/-- The encoding of con-leche's answer. -/
def encO : Option Bool → Word
  | none => 0
  | some false => 1
  | some true => 2

/-- The bias word: `d = diff + 2^32`. -/
def DR (d : Word) (diff : Int) : Prop := (d.toNat : Int) = diff + 4294967296

theorem DR.ge {d : Word} {diff : Int} (h : DR d diff) : 4294967296 ≤ d ↔ 0 ≤ diff := by
  rw [UInt64.le_iff_toNat_le]; simp only [DR] at h; constructor <;> intro e <;> simp at e ⊢ <;> omega

theorem DR.lt {d : Word} {diff : Int} (h : DR d diff) : d < 4294967296 ↔ diff < 0 := by
  rw [UInt64.lt_iff_toNat_lt]; simp only [DR] at h; constructor <;> intro e <;> simp at e ⊢ <;> omega

theorem DR.pred {d : Word} {diff : Int} (h : DR d diff) (hb : diff.natAbs < 2 ^ 31) :
    DR (d - 1) (diff - 1) := by
  simp only [DR] at h ⊢
  have h1 : (1 : Word) ≤ d := by rw [UInt64.le_iff_toNat_le]; simp; omega
  rw [UInt64.toNat_sub_of_le _ _ h1]; simp; omega

theorem DR.succ {d : Word} {diff : Int} (h : DR d diff) (hb : diff.natAbs < 2 ^ 31) :
    DR (d + 1) (diff + 1) := by
  simp only [DR] at h ⊢
  rw [UInt64.toNat_add]; simp; omega

theorem fuel_pred {f : Word} {fuel : Nat} (hf : f.toNat = fuel) (h0 : f ≠ 0) :
    (f - 1).toNat = fuel - 1 ∧ fuel ≠ 0 := by
  have h1 : (1 : Word) ≤ f := by
    rw [UInt64.le_iff_toNat_le]; have : f.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp (by simpa using e)); simp; omega
  rw [UInt64.toNat_sub_of_le _ _ h1]; simp
  refine ⟨by omega, fun e => h0 (UInt64.toNat_inj.mp (by simp; omega))⟩

/-! ## con-leche's comparison, arm by arm -/

namespace LevelEq
variable (f : Nat) (d : Int)

theorem rest_pp (a x : Name) :
    Level.rest f (.param a) (.param x) d = some (decide (a = x) && decide (d ≥ 0)) := by
  simp [Level.rest]
theorem rest_pz (a : Name) : Level.rest f (.param a) .zero d = some false := by simp [Level.rest]
theorem rest_zp (x : Name) : Level.rest f .zero (.param x) d = some (decide (d ≥ 0)) := by
  simp [Level.rest]
theorem rest_sl (s R : Level) : Level.rest f (.succ s) R d = Level.leqCore f s R (d - 1) := by
  cases R <;> simp [Level.rest]
theorem rest_sr (L s : Level) (h : tagOf L ≠ 1) :
    Level.rest f L (.succ s) d = Level.leqCore f L s (d + 1) := by
  cases L <;> simp_all [Level.rest, tagOf]
theorem rest_ml (a b R : Level) (h : tagOf R ≠ 1) :
    Level.rest f (.max a b) R d =
      (Level.leqCore f a R d).bind (fun c => if c then Level.leqCore f b R d else some false) := by
  cases R <;> simp_all [Level.rest, tagOf] <;> rfl
theorem rest_mr (L x y : Level) (h : tagOf L = 4 ∨ tagOf L = 0) :
    Level.rest f L (.max x y) d =
      (Level.leqCore f L x d).bind (fun c => if c then some true else Level.leqCore f L y d) := by
  cases L <;> simp_all [Level.rest, tagOf] <;> rfl
theorem rest_ii (a b x y : Level) :
    Level.rest f (.imax a b) (.imax x y) d =
      if (a = x && b = y && d ≥ 0) then some true
      else Level.imaxRules f (.imax a b) (.imax x y) d := by
  simp [Level.rest]
theorem rest_im (L R : Level) (h1 : ¬ (tagOf L = 4 ∧ tagOf R = 4))
    (h2 : ¬ (tagOf L = 4 ∧ tagOf R = 0)) (h3 : ¬ (tagOf L = 0 ∧ tagOf R = 4)) (h4 : tagOf L ≠ 1)
    (h5 : tagOf R ≠ 1) (h6 : tagOf L ≠ 2) (h7 : ¬ (tagOf R = 2 ∧ (tagOf L = 4 ∨ tagOf L = 0)))
    (h8 : ¬ (tagOf L = 3 ∧ tagOf R = 3)) : Level.rest f L R d = Level.imaxRules f L R d := by
  cases L <;> cases R <;> simp_all [Level.rest, tagOf]

theorem im_cl (a : Level) (p : Name) (R : Level) :
    Level.imaxRules f (.imax a (.param p)) R d = Level.byCases f p (.imax a (.param p)) R d := by
  simp only [Level.imaxRules]
theorem im_cr (L x : Level) (p : Name) (h : ¬ (tagOf L = 3 ∧ rtagOf L = 4)) :
    Level.imaxRules f L (.imax x (.param p)) d = Level.byCases f p L (.imax x (.param p)) d := by
  unfold Level.imaxRules; split <;> (try simp_all [tagOf, rtagOf]) <;>
    (intro u q e; subst e; simp_all [tagOf, rtagOf])
theorem im_il (a x y R : Level) (h : ¬ (tagOf R = 3 ∧ rtagOf R = 4)) :
    Level.imaxRules f (.imax a (.imax x y)) R d =
      Level.leqCore f (.max (.imax a y) (.imax x y)) R d := by
  unfold Level.imaxRules; split <;> (try simp_all [tagOf, rtagOf]) <;>
    (intro u q e; subst e; simp_all [tagOf, rtagOf])
theorem im_ml (a x y R : Level) (h : ¬ (tagOf R = 3 ∧ rtagOf R = 4)) :
    Level.imaxRules f (.imax a (.max x y)) R d =
      Level.leqCore f (Level.simplify (.max (.imax a x) (.imax a y))) R d := by
  unfold Level.imaxRules; split <;> (try simp_all [tagOf, rtagOf]) <;>
    (intro u q e; subst e; simp_all [tagOf, rtagOf])
theorem im_ir (L x j k : Level) (h1 : ¬ (tagOf L = 3 ∧ rtagOf L = 4))
    (h2 : ¬ (tagOf L = 3 ∧ rtagOf L = 3)) (h3 : ¬ (tagOf L = 3 ∧ rtagOf L = 2)) :
    Level.imaxRules f L (.imax x (.imax j k)) d =
      Level.leqCore f L (.max (.imax x k) (.imax j k)) d := by
  unfold Level.imaxRules; split <;> (try simp_all [tagOf, rtagOf]) <;>
    (intro u q e; subst e; simp_all [tagOf, rtagOf])
theorem im_mr (L x j k : Level) (h1 : ¬ (tagOf L = 3 ∧ rtagOf L = 4))
    (h2 : ¬ (tagOf L = 3 ∧ rtagOf L = 3)) (h3 : ¬ (tagOf L = 3 ∧ rtagOf L = 2)) :
    Level.imaxRules f L (.imax x (.max j k)) d =
      Level.leqCore f L (Level.simplify (.max (.imax x j) (.imax x k))) d := by
  unfold Level.imaxRules; split <;> (try simp_all [tagOf, rtagOf]) <;>
    (intro u q e; subst e; simp_all [tagOf, rtagOf])
theorem im_none (L R : Level) (h1 : ¬ (tagOf L = 3 ∧ rtagOf L = 4))
    (h2 : ¬ (tagOf R = 3 ∧ rtagOf R = 4)) (h3 : ¬ (tagOf L = 3 ∧ rtagOf L = 3))
    (h4 : ¬ (tagOf L = 3 ∧ rtagOf L = 2)) (h5 : ¬ (tagOf R = 3 ∧ rtagOf R = 3))
    (h6 : ¬ (tagOf R = 3 ∧ rtagOf R = 2)) : Level.imaxRules f L R d = none := by
  unfold Level.imaxRules; split <;> (try simp_all [tagOf, rtagOf]) <;>
    (intro u q e; subst e; simp_all [tagOf, rtagOf])

theorem byCases_eq (p : Name) (L R : Level) :
    Level.byCases f p L R d =
      (Level.leqCore f (Level.simplify (Level.subst [p] [.zero] L))
        (Level.simplify (Level.subst [p] [.zero] R)) d).bind (fun c => if c then
          Level.leqCore f (Level.simplify (Level.subst [p] [.succ (.param p)] L))
            (Level.simplify (Level.subst [p] [.succ (.param p)] R)) d else some false) := by
  simp only [Level.byCases]; rfl

end LevelEq

/-! ## The comparison under the decoder -/

section ok
variable (N)

/-- `lv_leq` is `leqCore`. -/
def LeqOK (n : Nat) : Prop := ∀ (m m' : Mem) (f l r d x : Word) (L R : Level) (fuel : Nat)
  (diff : Int), LvR N m l L → LvR N m r R → f.toNat = fuel → DR d diff →
  diff.natAbs + fuel ≤ 2 ^ 31 → leqW n m f l r d = some (x, m') →
  HeapExt m m' ∧ x = encO (Level.leqCore fuel L R diff)

/-- `lv_rest` is `rest` (one more unit of room: `rest` moves `diff` without spending fuel). -/
def RestOK (n : Nat) : Prop := ∀ (m m' : Mem) (f l r d x : Word) (L R : Level) (fuel : Nat)
  (diff : Int), LvR N m l L → LvR N m r R → f.toNat = fuel → DR d diff →
  diff.natAbs + fuel + 1 ≤ 2 ^ 31 → restW n m f l r d = some (x, m') →
  HeapExt m m' ∧ x = encO (Level.rest fuel L R diff)

/-- `lv_imax` is `imaxRules`. -/
def ImaxOK (n : Nat) : Prop := ∀ (m m' : Mem) (f l r d x : Word) (L R : Level) (fuel : Nat)
  (diff : Int), LvR N m l L → LvR N m r R → f.toNat = fuel → DR d diff →
  diff.natAbs + fuel ≤ 2 ^ 31 → imaxRW n m f l r d = some (x, m') →
  HeapExt m m' ∧ x = encO (Level.imaxRules fuel L R diff)

/-- `lv_imax_l` is `imaxRules` past its two `byCases` arms. -/
def ImaxLOK (n : Nat) : Prop := ∀ (m m' : Mem) (f l r d x : Word) (L R : Level) (fuel : Nat)
  (diff : Int), LvR N m l L → LvR N m r R → f.toNat = fuel → DR d diff →
  diff.natAbs + fuel ≤ 2 ^ 31 → ¬ (tagOf L = 3 ∧ rtagOf L = 4) → ¬ (tagOf R = 3 ∧ rtagOf R = 4) →
  imaxLW n m f l r d = some (x, m') → HeapExt m m' ∧ x = encO (Level.imaxRules fuel L R diff)

/-- `lv_imax_r` is `imaxRules` past its four left arms. -/
def ImaxROK (n : Nat) : Prop := ∀ (m m' : Mem) (f l r d x : Word) (L R : Level) (fuel : Nat)
  (diff : Int), LvR N m l L → LvR N m r R → f.toNat = fuel → DR d diff →
  diff.natAbs + fuel ≤ 2 ^ 31 → ¬ (tagOf L = 3 ∧ rtagOf L = 4) → ¬ (tagOf R = 3 ∧ rtagOf R = 4) →
  ¬ (tagOf L = 3 ∧ rtagOf L = 3) → ¬ (tagOf L = 3 ∧ rtagOf L = 2) →
  imaxRrW n m f l r d = some (x, m') → HeapExt m m' ∧ x = encO (Level.imaxRules fuel L R diff)

/-- `lv_cases` is `byCases`. -/
def CasesOK (n : Nat) : Prop := ∀ (m m' : Mem) (f q l r d x : Word) (P : Name) (L R : Level)
  (fuel : Nat) (diff : Int), N q P → LvR N m l L → LvR N m r R → f.toNat = fuel → DR d diff →
  diff.natAbs + fuel ≤ 2 ^ 31 → casesW n m f q l r d = some (x, m') →
  HeapExt m m' ∧ x = encO (Level.byCases fuel P L R diff)

/-- `lv_cases_at` is one case of `byCases`. -/
def CaOK (n : Nat) : Prop := ∀ (m m' : Mem) (f q l r d v x : Word) (P : Name) (L R V : Level)
  (fuel : Nat) (diff : Int), N q P → LvR N m l L → LvR N m r R → LvR N m v V → f.toNat = fuel →
  DR d diff → diff.natAbs + fuel ≤ 2 ^ 31 → caW n m f q l r d v = some (x, m') →
  HeapExt m m' ∧ x = encO (Level.leqCore fuel (Level.simplify (Level.subst [P] [V] L))
    (Level.simplify (Level.subst [P] [V] R)) diff)

end ok

theorem tag0_iff {m : Mem} {p : Word} {L : Level} (h : LvR N m p L) : lvG m p = 0 ↔ L = .zero := by
  rw [h.tag]; cases L <;> simp [tagOf]

theorem leq_ok (n : Nat) (ih : RestOK N n) : LeqOK N (n + 1) := by
  intro m m' f l r d x L R fuel diff hl hr hf hd hb h
  by_cases hf0 : f = 0
  · rw [leqW_f0 n m f l r d hf0] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
    have : fuel = 0 := by rw [← hf, hf0]; rfl
    subst this; exact ⟨HeapExt.refl _, by simp [Level.leqCore, encO]⟩
  obtain ⟨hf', hfuel⟩ := fuel_pred hf hf0
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
  by_cases c1 : lvG m l = 0 ∧ 4294967296 ≤ d
  · rw [leqW_lz n m f l r d hf0 c1.1 c1.2] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
    have hL : L = .zero := (tag0_iff hl).mp c1.1
    have hd0 : 0 ≤ diff := hd.ge.mp c1.2
    exact ⟨HeapExt.refl _, by simp [Level.leqCore, hL, hd0, encO]⟩
  have n1 : ¬ (L = .zero ∧ diff ≥ 0) := fun ⟨a, b⟩ => c1 ⟨(tag0_iff hl).mpr a, hd.ge.mpr b⟩
  by_cases c2 : lvG m r = 0 ∧ d < 4294967296
  · rw [leqW_rz n m f l r d hf0 c1 c2.1 c2.2] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
    have hR : R = .zero := (tag0_iff hr).mp c2.1
    have hd0 : diff < 0 := hd.lt.mp c2.2
    exact ⟨HeapExt.refl _, by simp [Level.leqCore, n1, hR, hd0, encO]⟩
  have n2 : ¬ (R = .zero ∧ diff < 0) := fun ⟨a, b⟩ => c2 ⟨(tag0_iff hr).mpr a, hd.lt.mpr b⟩
  rw [leqW_rest n m f l r d hf0 c1 c2] at h
  obtain ⟨he, hx⟩ := ih m m' (f - 1) l r d x L R k diff hl hr (by omega) hd (by omega) h
  exact ⟨he, by rw [hx]; simp only [Level.leqCore, n1, n2, ↓reduceIte]⟩

theorem ca_ok (hN : NameRel N) (n : Nat) (ih : LeqOK N n) : CaOK N (n + 1) := by
  intro m m' f q l r d v x P L R V fuel diff hq hl hr hv hf hd hb h
  rw [caW_succ] at h
  rcases e₁ : ssW n m l q v with _ | ⟨x₁, m₁⟩ <;> simp only [e₁, caK₁, caK₁_some, reduceCtorEq] at h
  obtain ⟨he₁, hx₁⟩ := ssW_ok hN n _ _ _ _ _ _ _ _ _ hl hq hv e₁
  rcases e₂ : ssW n m₁ r q v with _ | ⟨y, m₂⟩ <;> simp only [e₂, caK₂, caK₂_some, reduceCtorEq] at h
  obtain ⟨he₂, hy⟩ := ssW_ok hN n _ _ _ _ _ _ _ _ _ (hr.mono he₁) hq (hv.mono he₁) e₂
  obtain ⟨he₃, hx⟩ := ih _ _ _ _ _ _ _ _ _ fuel diff (hx₁.mono he₂) hy hf hd hb h
  exact ⟨(he₁.trans he₂).trans he₃, hx⟩

theorem cases_ok (n : Nat) (ih : CaOK N n) : CasesOK N (n + 1) := by
  intro m m' f q l r d x P L R fuel diff hq hl hr hf hd hb h
  rw [casesW_succ] at h
  rcases e₁ : lhMkW m 0 0 0 with _ | ⟨z, m₁⟩ <;> simp only [e₁, csK₁, csK₁_some, reduceCtorEq] at h
  obtain ⟨he₁, hz, -⟩ := lhMkW_ext e₁
  have hz' : LvR N m₁ z .zero := .zero hz
  cases e₂ : caW n m₁ f q l r d z with
  | none => rw [e₂] at h; simp [csK₂] at h
  | some w₂ =>
    obtain ⟨y, m₂⟩ := w₂
    rw [e₂] at h
    obtain ⟨he₂, hy⟩ := ih _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hq (hl.mono he₁) (hr.mono he₁) hz' hf hd
      hb e₂
    rw [LevelEq.byCases_eq]
    by_cases hy2 : y = 2
    · subst hy2
      rw [csK₂_go] at h
      cases e₃ : lhMkW m₂ 4 q 0 with
      | none => rw [e₃] at h; simp [csK₃] at h
      | some w₃ =>
        obtain ⟨s₁, m₃⟩ := w₃
        rw [e₃, csK₃_some] at h
        obtain ⟨he₃, hs₁, -⟩ := lhMkW_ext e₃
        cases e₄ : lhMkW m₃ 1 s₁ 0 with
        | none => rw [e₄] at h; simp [csK₄] at h
        | some w₄ =>
          obtain ⟨s₂, m₄⟩ := w₄
          rw [e₄, csK₄_some] at h
          obtain ⟨he₄, hs₂⟩ := mk_succ e₄ (LvR.param hs₁ hq)
          have hm := (he₂.trans he₃).trans he₄
          obtain ⟨he₅, hx⟩ := ih _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hq (hl.mono (he₁.trans hm))
            (hr.mono (he₁.trans hm)) hs₂ hf hd hb h
          refine ⟨(he₁.trans hm).trans he₅, ?_⟩
          rw [hx]
          revert hy
          cases Level.leqCore fuel _ _ diff with
          | none => simp [encO]
          | some b => cases b <;> simp [encO]
    · rw [csK₂_stop (hx := hy2)] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
      refine ⟨he₁.trans he₂, ?_⟩
      rw [hy] at hy2 ⊢
      revert hy2
      cases Level.leqCore fuel _ _ diff with
      | none => simp [encO]
      | some b => cases b <;> simp [encO]

theorem guard_iff {m : Mem} {p : Word} {L : Level} (h : LvR N m p L) (t : Word) :
    (lvG m p = 3 ∧ lvG m (lvB m p) = t) ↔ (tagOf L = 3 ∧ rtagOf L = t) := by
  constructor
  · rintro ⟨h3, ht⟩
    refine ⟨by rw [← h.tag]; exact h3, ?_⟩
    rw [← h.rtag h3]; exact ht
  · rintro ⟨h3, ht⟩
    have g3 : lvG m p = 3 := by rw [h.tag]; exact h3
    exact ⟨g3, by rw [h.rtag g3]; exact ht⟩

/-- The answer after a `max`/`or` short-cut: `y` was not the continuing answer. -/
theorem enc_stop_and {o : Option Bool} {k : Bool → Option Bool} (h : encO o ≠ 2) :
    encO (o.bind fun c => if c then k c else some false) = encO o := by
  cases o with
  | none => rfl
  | some b => cases b <;> simp_all [encO]

theorem enc_stop_or {o : Option Bool} {k : Bool → Option Bool} (h : encO o ≠ 1) :
    encO (o.bind fun c => if c then some true else k c) = encO o := by
  cases o with
  | none => rfl
  | some b => cases b <;> simp_all [encO]

theorem enc_eq2 {o : Option Bool} (h : 2 = encO o) : o = some true := by
  cases o with
  | none => simp [encO] at h
  | some b => cases b <;> simp_all [encO]

theorem enc_eq1 {o : Option Bool} (h : 1 = encO o) : o = some false := by
  cases o with
  | none => simp [encO] at h
  | some b => cases b <;> simp_all [encO]

/-! ### Inversion by tag -/

section inv
variable {m : Mem} {p : Word} {L : Level} (h : LvR N m p L)
include h

theorem LvR.inv0 (g : lvG m p = 0) : L = .zero := by
  cases h <;> simp_all [lvG]
theorem LvR.inv1 (g : lvG m p = 1) : ∃ a l, lvNodeW m p = [1, a, 0] ∧ LvR N m a l ∧ L = .succ l := by
  cases h with
  | succ hv ha => exact ⟨_, _, hv, ha, rfl⟩
  | _ => simp_all [lvG]
theorem LvR.inv2 (g : lvG m p = 2) :
    ∃ a b l r, lvNodeW m p = [2, a, b] ∧ LvR N m a l ∧ LvR N m b r ∧ L = .max l r := by
  cases h with
  | max hv ha hb => exact ⟨_, _, _, _, hv, ha, hb, rfl⟩
  | _ => simp_all [lvG]
theorem LvR.inv3 (g : lvG m p = 3) :
    ∃ a b l r, lvNodeW m p = [3, a, b] ∧ LvR N m a l ∧ LvR N m b r ∧ L = .imax l r := by
  cases h with
  | imax hv ha hb => exact ⟨_, _, _, _, hv, ha, hb, rfl⟩
  | _ => simp_all [lvG]
theorem LvR.inv4 (g : lvG m p = 4) : ∃ a b nm, lvNodeW m p = [4, a, b] ∧ N a nm ∧ L = .param nm := by
  cases h with
  | param hv hn => exact ⟨_, _, _, hv, hn, rfl⟩
  | _ => simp_all [lvG]

end inv

theorem rest_ok (hN : NameRel N) (n : Nat) (ihL : LeqOK N n) (ihI : ImaxOK N n) :
    RestOK N (n + 1) := by
  intro m m' f l r d x L R fuel diff hl hr hf hd hb h
  have tL := hl.tag
  have tR := hr.tag
  by_cases c1 : lvG m l = 4 ∧ lvG m r = 4
  · rw [restW_pp n m f l r d c1] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
    refine ⟨HeapExt.refl _, ?_⟩
    obtain ⟨a, _, A, hv, hA, rfl⟩ := hl.inv4 c1.1
    obtain ⟨b, _, B, hw, hB, rfl⟩ := hr.inv4 c1.2
    rw [LevelEq.rest_pp, (lv_fields hv).2.1, (lv_fields hw).2.1]
    by_cases e : a = b
    · subst e; rw [hN.fn _ _ _ hA hB]
      by_cases hd0 : 0 ≤ diff <;> simp [hd0, hd.ge, encO]
    · have : A ≠ B := fun h' => e (hN.inj _ _ _ hA (h' ▸ hB))
      simp [e, this, encO]
  by_cases c2 : lvG m l = 4 ∧ lvG m r = 0
  · rw [restW_pz n m f l r d c1 c2] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
    refine ⟨HeapExt.refl _, ?_⟩
    obtain ⟨a, _, A, hv, hA, rfl⟩ := hl.inv4 c2.1
    rw [hr.inv0 c2.2, LevelEq.rest_pz]; rfl
  by_cases c3 : lvG m l = 0 ∧ lvG m r = 4
  · rw [restW_zp n m f l r d c1 c2 c3] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
    refine ⟨HeapExt.refl _, ?_⟩
    obtain ⟨b, _, B, hw, hB, rfl⟩ := hr.inv4 c3.2
    rw [hl.inv0 c3.1, LevelEq.rest_zp]; by_cases hd0 : 0 ≤ diff <;> simp [hd0, hd.ge, encO]
  by_cases c4 : lvG m l = 1
  · rw [restW_sl n m f l r d c1 c2 c3 c4] at h
    obtain ⟨a, A, hv, ha, rfl⟩ := hl.inv1 c4
    rw [(lv_fields hv).2.1] at h
    obtain ⟨he, hx⟩ := ihL _ _ _ _ _ _ _ _ _ fuel (diff - 1) ha hr hf (hd.pred (by omega))
      (by omega) h
    exact ⟨he, by rw [hx, LevelEq.rest_sl]⟩
  by_cases c5 : lvG m r = 1
  · rw [restW_sr n m f l r d c1 c2 c3 c4 c5] at h
    obtain ⟨a, A, hv, ha, rfl⟩ := hr.inv1 c5
    rw [(lv_fields hv).2.1] at h
    obtain ⟨he, hx⟩ := ihL _ _ _ _ _ _ _ _ _ fuel (diff + 1) hl ha hf (hd.succ (by omega))
      (by omega) h
    exact ⟨he, by rw [hx, LevelEq.rest_sr _ _ _ _ (by rw [← tL]; exact c4)]⟩
  by_cases c6 : lvG m l = 2
  · rw [restW_ml n m f l r d c1 c2 c3 c4 c5 c6] at h
    obtain ⟨a, b, A, B, hv, ha, hb', rfl⟩ := hl.inv2 c6
    rw [(lv_fields hv).2.1, (lv_fields hv).2.2] at h
    rw [LevelEq.rest_ml _ _ _ _ _ (by rw [← tR]; exact c5)]
    cases e : leqW n m f a r d with
    | none => rw [e] at h; simp [andK] at h
    | some w =>
      obtain ⟨y, m₁⟩ := w
      rw [e] at h
      obtain ⟨he₁, hy⟩ := ihL _ _ _ _ _ _ _ _ _ fuel diff ha hr hf hd (by omega) e
      by_cases hy2 : y = 2
      · subst hy2
        rw [andK_go] at h
        obtain ⟨he₂, hx⟩ := ihL _ _ _ _ _ _ _ _ _ fuel diff (hb'.mono he₁) (hr.mono he₁) hf hd
          (by omega) h
        refine ⟨he₁.trans he₂, ?_⟩
        rw [hx, enc_eq2 hy]; rfl
      · rw [andK_stop (hx := hy2)] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
        refine ⟨he₁, ?_⟩
        rw [hy] at hy2 ⊢; rw [enc_stop_and hy2]
  by_cases c7 : lvG m r = 2 ∧ (lvG m l = 4 ∨ lvG m l = 0)
  · rw [restW_mr n m f l r d c1 c2 c3 c4 c5 c6 c7] at h
    have hL : tagOf L = 4 ∨ tagOf L = 0 := by rw [← tL]; exact c7.2
    obtain ⟨a, b, A, B, hv, ha, hb', rfl⟩ := hr.inv2 c7.1
    rw [(lv_fields hv).2.1, (lv_fields hv).2.2] at h
    rw [LevelEq.rest_mr _ _ _ _ _ hL]
    cases e : leqW n m f l a d with
    | none => rw [e] at h; simp [orK] at h
    | some w =>
      obtain ⟨y, m₁⟩ := w
      rw [e] at h
      obtain ⟨he₁, hy⟩ := ihL _ _ _ _ _ _ _ _ _ fuel diff hl ha hf hd (by omega) e
      by_cases hy1 : y = 1
      · subst hy1
        rw [orK_go] at h
        obtain ⟨he₂, hx⟩ := ihL _ _ _ _ _ _ _ _ _ fuel diff (hl.mono he₁) (hb'.mono he₁) hf hd
          (by omega) h
        refine ⟨he₁.trans he₂, ?_⟩
        rw [hx, enc_eq1 hy]; rfl
      · rw [orK_stop (hx := hy1)] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
        refine ⟨he₁, ?_⟩
        rw [hy] at hy1 ⊢; rw [enc_stop_or hy1]
  by_cases c8 : lvG m l = 3 ∧ lvG m r = 3 ∧ 4294967296 ≤ d
  · rw [restW_ii n m f l r d c1 c2 c3 c4 c5 c6 c7 c8] at h
    have hd0 : 0 ≤ diff := hd.ge.mp c8.2.2
    obtain ⟨a, b, A, B, hv, ha, hb', rfl⟩ := hl.inv3 c8.1
    obtain ⟨x', y', X, Y, hw, hx', hy', rfl⟩ := hr.inv3 c8.2.1
    rw [LevelEq.rest_ii]
    rw [(lv_fields hv).2.1, (lv_fields hw).2.1] at h
    cases e₁ : lvEqW n m a x' with
    | none => rw [e₁] at h; simp [eqK₁] at h
    | some z₁ =>
      rw [e₁] at h
      have hz₁ := lvEqW_ok hN n a x' A X z₁ ha hx' e₁
      simp only [Level.beq, decide_eq_true_eq] at hz₁
      by_cases eAX : A = X
      · simp only [eAX, ↓reduceIte] at hz₁; subst hz₁
        rw [eqK₁_ne (hx := by decide), (lv_fields hv).2.2, (lv_fields hw).2.2] at h
        cases e₂ : lvEqW n m b y' with
        | none => rw [e₂] at h; simp [eqK₂] at h
        | some z₂ =>
          rw [e₂] at h
          have hz₂ := lvEqW_ok hN n b y' B Y z₂ hb' hy' e₂
          simp only [Level.beq, decide_eq_true_eq] at hz₂
          by_cases eBY : B = Y
          · simp only [eBY, ↓reduceIte] at hz₂; subst hz₂
            rw [eqK₂_ne (hx := by decide)] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
            refine ⟨HeapExt.refl _, ?_⟩
            simp [eAX, eBY, hd0, encO]
          · simp only [eBY, ↓reduceIte] at hz₂; subst hz₂
            rw [eqK₂_zero] at h
            obtain ⟨he, hx⟩ := ihI _ _ _ _ _ _ _ _ _ fuel diff (.imax hv ha hb')
              (.imax hw hx' hy') hf hd (by omega) h
            exact ⟨he, by rw [hx]; simp [eBY]⟩
      · simp only [eAX, ↓reduceIte] at hz₁; subst hz₁
        rw [eqK₁_zero] at h
        obtain ⟨he, hx⟩ := ihI _ _ _ _ _ _ _ _ _ fuel diff (.imax hv ha hb')
          (.imax hw hx' hy') hf hd (by omega) h
        exact ⟨he, by rw [hx]; simp [eAX]⟩
  rw [restW_im n m f l r d c1 c2 c3 c4 c5 c6 c7 c8] at h
  obtain ⟨he, hx⟩ := ihI _ _ _ _ _ _ _ _ _ fuel diff hl hr hf hd (by omega) h
  refine ⟨he, ?_⟩
  rw [hx]
  by_cases c9 : lvG m l = 3 ∧ lvG m r = 3
  · have hd0 : ¬ 0 ≤ diff := fun e => c8 ⟨c9.1, c9.2, hd.ge.mpr e⟩
    obtain ⟨a, b, A, B, hv, ha, hb', rfl⟩ := hl.inv3 c9.1
    obtain ⟨x', y', X, Y, hw, hx', hy', rfl⟩ := hr.inv3 c9.2
    rw [LevelEq.rest_ii]; simp [hd0]
  · simp only [tL, tR] at c1 c2 c3 c4 c5 c6 c7 c9
    rw [LevelEq.rest_im _ _ _ _ c1 c2 c3 c4 c5 c6 c7 c9]

theorem imax_ok (n : Nat) (ihIL : ImaxLOK N n) (ihC : CasesOK N n) : ImaxOK N (n + 1) := by
  intro m m' f l r d x L R fuel diff hl hr hf hd hb h
  have g := fun t => (guard_iff hl t)
  have g' := fun t => (guard_iff hr t)
  by_cases c1 : lvG m l = 3 ∧ lvG m (lvB m l) = 4
  · rw [imaxRW_cl n m f l r d c1] at h
    obtain ⟨a, b, A, B, hv, ha, hb', rfl⟩ := hl.inv3 c1.1
    rw [(lv_fields hv).2.2] at c1 h
    obtain ⟨q, _, P, hw, hq, rfl⟩ := hb'.inv4 c1.2
    rw [(lv_fields hw).2.1] at h
    obtain ⟨he, hx⟩ := ihC _ _ _ _ _ _ _ _ _ _ _ fuel diff hq (.imax hv ha (.param hw hq)) hr hf hd
      hb h
    exact ⟨he, by rw [hx, LevelEq.im_cl]⟩
  have n1 : ¬ (tagOf L = 3 ∧ rtagOf L = 4) := fun e => c1 ((g 4).mpr e)
  by_cases c2 : lvG m r = 3 ∧ lvG m (lvB m r) = 4
  · rw [imaxRW_cr n m f l r d c1 c2] at h
    obtain ⟨a, b, A, B, hv, ha, hb', rfl⟩ := hr.inv3 c2.1
    rw [(lv_fields hv).2.2] at c2 h
    obtain ⟨q, _, P, hw, hq, rfl⟩ := hb'.inv4 c2.2
    rw [(lv_fields hw).2.1] at h
    obtain ⟨he, hx⟩ := ihC _ _ _ _ _ _ _ _ _ _ _ fuel diff hq hl (.imax hv ha (.param hw hq)) hf hd
      hb h
    exact ⟨he, by rw [hx, LevelEq.im_cr _ _ _ _ _ n1]⟩
  have n2 : ¬ (tagOf R = 3 ∧ rtagOf R = 4) := fun e => c2 ((g' 4).mpr e)
  rw [imaxRW_l n m f l r d c1 c2] at h
  exact ihIL _ _ _ _ _ _ _ _ _ fuel diff hl hr hf hd hb n1 n2 h

theorem imaxL_ok (n : Nat) (ihL : LeqOK N n) (ihIR : ImaxROK N n) : ImaxLOK N (n + 1) := by
  intro m m' f l r d x L R fuel diff hl hr hf hd hb n1 n2 h
  have g := fun t => (guard_iff hl t)
  by_cases c3 : lvG m l = 3 ∧ lvG m (lvB m l) = 3
  · rw [imaxLW_i n m f l r d c3] at h
    obtain ⟨a, b, A, B, hv, ha, hb', rfl⟩ := hl.inv3 c3.1
    rw [(lv_fields hv).2.1, (lv_fields hv).2.2] at h
    rw [(lv_fields hv).2.2] at c3
    obtain ⟨x', y', X, Y, hw, hx', hy', rfl⟩ := hb'.inv3 c3.2
    rw [(lv_fields hw).2.2] at h
    rcases e : dist1W m a y' b with _ | ⟨z, m₁⟩ <;> simp only [e, leqLK, leqLK_some, reduceCtorEq] at h
    obtain ⟨he₁, hz⟩ := dist1W_ok m m₁ a y' b z A Y _ ha hy' (.imax hw hx' hy') e
    obtain ⟨he₂, hx⟩ := ihL _ _ _ _ _ _ _ _ _ fuel diff hz (hr.mono he₁) hf hd hb h
    exact ⟨he₁.trans he₂, by rw [hx, LevelEq.im_il _ _ _ _ _ _ n2]⟩
  have n3 : ¬ (tagOf L = 3 ∧ rtagOf L = 3) := fun e => c3 ((g 3).mpr e)
  by_cases c4 : lvG m l = 3 ∧ lvG m (lvB m l) = 2
  · rw [imaxLW_m n m f l r d c3 c4] at h
    obtain ⟨a, b, A, B, hv, ha, hb', rfl⟩ := hl.inv3 c4.1
    rw [(lv_fields hv).2.1, (lv_fields hv).2.2] at h
    rw [(lv_fields hv).2.2] at c4
    obtain ⟨x', y', X, Y, hw, hx', hy', rfl⟩ := hb'.inv2 c4.2
    rw [(lv_fields hw).2.1, (lv_fields hw).2.2] at h
    rcases e : dist2W n m a x' y' with _ | ⟨z, m₁⟩ <;> simp only [e, leqLK, leqLK_some, reduceCtorEq] at h
    obtain ⟨he₁, hz⟩ := dist2W_ok n m m₁ a x' y' z A X Y ha hx' hy' e
    obtain ⟨he₂, hx⟩ := ihL _ _ _ _ _ _ _ _ _ fuel diff hz (hr.mono he₁) hf hd hb h
    exact ⟨he₁.trans he₂, by rw [hx, LevelEq.im_ml _ _ _ _ _ _ n2]⟩
  have n4 : ¬ (tagOf L = 3 ∧ rtagOf L = 2) := fun e => c4 ((g 2).mpr e)
  rw [imaxLW_r n m f l r d c3 c4] at h
  exact ihIR _ _ _ _ _ _ _ _ _ fuel diff hl hr hf hd hb n1 n2 n3 n4 h

theorem imaxR_ok (n : Nat) (ihL : LeqOK N n) : ImaxROK N (n + 1) := by
  intro m m' f l r d x L R fuel diff hl hr hf hd hb n1 n2 n3 n4 h
  have g' := fun t => (guard_iff hr t)
  by_cases c5 : lvG m r = 3 ∧ lvG m (lvB m r) = 3
  · rw [imaxRrW_i n m f l r d c5] at h
    obtain ⟨a, b, A, B, hv, ha, hb', rfl⟩ := hr.inv3 c5.1
    rw [(lv_fields hv).2.1, (lv_fields hv).2.2] at h
    rw [(lv_fields hv).2.2] at c5
    obtain ⟨x', y', X, Y, hw, hx', hy', rfl⟩ := hb'.inv3 c5.2
    rw [(lv_fields hw).2.2] at h
    rcases e : dist1W m a y' b with _ | ⟨z, m₁⟩ <;> simp only [e, leqRK, leqRK_some, reduceCtorEq] at h
    obtain ⟨he₁, hz⟩ := dist1W_ok m m₁ a y' b z A Y _ ha hy' (.imax hw hx' hy') e
    obtain ⟨he₂, hx⟩ := ihL _ _ _ _ _ _ _ _ _ fuel diff (hl.mono he₁) hz hf hd hb h
    exact ⟨he₁.trans he₂, by rw [hx, LevelEq.im_ir _ _ _ _ _ _ n1 n3 n4]⟩
  have n5 : ¬ (tagOf R = 3 ∧ rtagOf R = 3) := fun e => c5 ((g' 3).mpr e)
  by_cases c6 : lvG m r = 3 ∧ lvG m (lvB m r) = 2
  · rw [imaxRrW_m n m f l r d c5 c6] at h
    obtain ⟨a, b, A, B, hv, ha, hb', rfl⟩ := hr.inv3 c6.1
    rw [(lv_fields hv).2.1, (lv_fields hv).2.2] at h
    rw [(lv_fields hv).2.2] at c6
    obtain ⟨x', y', X, Y, hw, hx', hy', rfl⟩ := hb'.inv2 c6.2
    rw [(lv_fields hw).2.1, (lv_fields hw).2.2] at h
    rcases e : dist2W n m a x' y' with _ | ⟨z, m₁⟩ <;> simp only [e, leqRK, leqRK_some, reduceCtorEq] at h
    obtain ⟨he₁, hz⟩ := dist2W_ok n m m₁ a x' y' z A X Y ha hx' hy' e
    obtain ⟨he₂, hx⟩ := ihL _ _ _ _ _ _ _ _ _ fuel diff (hl.mono he₁) hz hf hd hb h
    exact ⟨he₁.trans he₂, by rw [hx, LevelEq.im_mr _ _ _ _ _ _ n1 n3 n4]⟩
  have n6 : ¬ (tagOf R = 3 ∧ rtagOf R = 2) := fun e => c6 ((g' 2).mpr e)
  rw [imaxRrW_none n m f l r d c5 c6] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
  exact ⟨HeapExt.refl _, by rw [LevelEq.im_none _ _ _ _ n1 n2 n3 n4 n5 n6]; rfl⟩

/-- **The comparison refines con-leche's**, at every L fuel: the seven functions at once. -/
@[refines ConLeche.Level.leqCore ConLeche.Level.rest ConLeche.Level.imaxRules ConLeche.Level.byCases]
theorem leqOK (hN : NameRel N) (n : Nat) :
    LeqOK N n ∧ RestOK N n ∧ ImaxOK N n ∧ ImaxLOK N n ∧ ImaxROK N n ∧ CasesOK N n ∧ CaOK N n := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
      | intro m m' f l r d x L R fuel diff _ _ _ _ _ h; simp [leqW, restW, imaxRW] at h; done
      | intro m m' f l r d x L R fuel diff _ _ _ _ _ _ _ h; simp [imaxLW] at h; done
      | intro m m' f l r d x L R fuel diff _ _ _ _ _ _ _ _ _ h; simp [imaxRrW] at h; done
      | intro m m' f q l r d x P L R fuel diff _ _ _ _ _ _ h; simp [casesW] at h; done
      | intro m m' f q l r d v x P L R V fuel diff _ _ _ _ _ _ _ h; simp [caW] at h; done
  | succ n ih =>
    obtain ⟨hL, hR, hI, hIL, hIR, hC, hA⟩ := ih
    exact ⟨leq_ok n hR, rest_ok hN n hL hI, imax_ok n hIL hC, imaxL_ok n hL hIR, imaxR_ok n hL,
      cases_ok n hA, ca_ok hN n hL⟩

end L.Arena
