import ConAgua.Arena.ArRangeSpec
import ConAgua.Arena.Abs1Refine
import ConAgua.Census.Attr

/-!
# `ar_entry` refines the arena's `abstractRangeFast`

`Abs1Refine.lean`'s proof with the range `(d, k)` and the cursor `c`; its tier (`ArenaA`), cut-off
(`fvbW_ok`), probe, tail and rebuild lemmas are reused as they are. New: the `fvar` arm's range
test (`d ≤ idx < d + k` over words is the twin's over `Nat` once `d + k` does not wrap, which the L
arm checks) and the entry's `k = 0` identity.
-/

open ConRon.Arena ConLeche
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

theorem dk_toNat (d k : UInt64) (hdk : ¬ d + k < d) : (d + k).toNat = d.toNat + k.toNat := by
  have h := UInt64.not_lt.mp hdk
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_add] at h
  rw [UInt64.toNat_add]
  have := d.toNat_lt; have := k.toNat_lt
  omega
theorem rng_iff (d k I : UInt64) (hdk : ¬ d + k < d) :
    (d ≤ I ∧ I < d + k) ↔ (decide (d.toNat ≤ I.toNat) && decide (I.toNat < d.toNat + k.toNat)) = true := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt,
    dk_toNat d k hdk]
theorem rng_word (c d k I : UInt64) (hdk : ¬ d + k < d) (hi : d ≤ I ∧ I < d + k)
    (ho : ¬ c + (d + k - 1 - I) < c) :
    (c + (d + k - 1 - I)).toNat = c.toNat + (d.toNat + k.toNat - 1 - I.toNat) := by
  obtain ⟨h1, h2⟩ := hi
  have e := dk_toNat d k hdk
  rw [UInt64.le_iff_toNat_le] at h1
  rw [UInt64.lt_iff_toNat_lt, e] at h2
  have h3 : (1 : UInt64) ≤ d + k := by rw [UInt64.le_iff_toNat_le, e]; simp; omega
  have h4 : I ≤ d + k - 1 := by rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ h3, e]; simp; omega
  have e2 : (d + k - 1 - I).toNat = d.toNat + k.toNat - 1 - I.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ h4, UInt64.toNat_sub_of_le _ _ h3, e]; simp
  have ho' := UInt64.not_lt.mp ho
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_add, e2] at ho'
  rw [UInt64.toNat_add, e2]
  have := c.toNat_lt
  have hb := (d + k).toNat_lt
  rw [e] at hb
  have hf : d.toNat + k.toNat - 1 - I.toNat < 2 ^ 64 := by omega
  generalize d.toNat + k.toNat - 1 - I.toNat = X at hf ho' ⊢
  omega

/-! ## The twin's dispatcher, named -/

/-- The part of `abstractRangeGo` after the cut-off: the dispatch on the tag. -/
def arNodeA (d k F : Nat) (h : EIdx) (c : Nat) : AM EIdx :=
  let tg := h.tag
  if tg == ETag.app then absRangeGoArmApp d k F h c
  else if ETag.isBind tg then absRangeGoArmBind d k F h c
  else if tg == ETag.fvar then absRangeArmFVar d k h c
  else if tg == ETag.letE then absRangeGoArmLet d k F h c
  else if tg == ETag.proj then absRangeGoArmProj d k F h c
  else pure h

theorem abstractRangeGo_succ' (d k F : Nat) (h : EIdx) (c : Nat) :
    abstractRangeGo d k (F + 1) h c = (do
      let fb ← fvarB F h
      if fb ≤ d then pure h else arNodeA d k F h c) := by
  rw [abstractRangeGo_succ]; rfl

/-! ## The statements, by fuel -/

/-- What `abs_go`'s model at fuel `n` says about the arena walk at any fuel `F ≥ n`. -/
def RGoOK (n : Nat) : Prop :=
  ∀ (F : Nat) (m m' : Mem) (a : AState) (h c d k r : Word), n ≤ F → ArenaA m a →
    h.toNat < 2 ^ 32 → arW n m h c d k = some (r, m') →
    ∃ a', (abstractRangeGo d.toNat k.toNat F (decE h) c.toNat).run a = .ok (decE r, a') ∧ ArenaA m' a'

/-- The same for `ab_node` and the dispatch. -/
def RNodeOK (n : Nat) : Prop :=
  ∀ (F : Nat) (m m' : Mem) (a : AState) (h c d k r : Word), n ≤ F + 1 → ArenaA m a →
    h.toNat < 2 ^ 32 → arNodeW n m h c d k = some (r, m') →
    ∃ a', (arNodeA d.toNat k.toNat F (decE h) c.toNat).run a = .ok (decE r, a') ∧ ArenaA m' a'

/-- The arena arm `arm` refines the L arm `armW` at `h`, under `ArenaA`. -/
def RArmRef (n : Nat) (armW : Nat → Mem → Word → Word → Word → Word → Option (Word × Mem))
    (arm : AM EIdx) (m m' : Mem) (a : AState) (h c d k r : Word) : Prop :=
  armW n m h c d k = some (r, m') → ∃ a', arm.run a = .ok (decE r, a') ∧ ArenaA m' a'

/-- The five arms, each at its tag. -/
def RArmOK (n : Nat) : Prop :=
  ∀ (F : Nat) (m m' : Mem) (a : AState) (h c d k r : Word), n ≤ F + 1 → ArenaA m a →
    h.toNat < 2 ^ 32 →
    (h >>> 28 = 4 → RArmRef n arAppW (absRangeGoArmApp d.toNat k.toNat F (decE h) c.toNat) m m' a h c d k r) ∧
    (h >>> 28 = 5 → RArmRef n arLamW (absRangeGoArmBind d.toNat k.toNat F (decE h) c.toNat) m m' a h c d k r) ∧
    (h >>> 28 = 6 →
      RArmRef n arForallW (absRangeGoArmBind d.toNat k.toNat F (decE h) c.toNat) m m' a h c d k r) ∧
    (h >>> 28 = 7 → RArmRef n arLetW (absRangeGoArmLet d.toNat k.toNat F (decE h) c.toNat) m m' a h c d k r) ∧
    (h >>> 28 = 9 → RArmRef n arProjW (absRangeGoArmProj d.toNat k.toNat F (decE h) c.toNat) m m' a h c d k r)

theorem rgoOK_succ (n : Nat) (ih : RNodeOK n) : RGoOK (n + 1) := by
  intro F m m' a h c d k r hF hA hh hb
  obtain ⟨F, rfl⟩ : ∃ G, F = G + 1 := ⟨F - 1, by omega⟩
  rw [arW_eq] at hb
  cases hf : fvbW n m h with
  | none => simp [hf, rcutK] at hb
  | some p =>
  obtain ⟨x, m₁⟩ := p
  rw [hf, rcutK_some] at hb
  obtain ⟨a₁, ha₁, hA₁⟩ := fvbW_ok n F (by omega) m m₁ a hA h x hh hf
  rw [abstractRangeGo_succ', StateT.run_bind, ha₁, except_ok_bind]
  by_cases hc : x ≤ d
  · rw [if_pos hc] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    rw [if_pos (UInt64.le_iff_toNat_le.mp hc)]
    exact ⟨a₁, rfl, hA₁⟩
  · rw [if_neg hc] at hb
    rw [if_neg (fun e => hc (UInt64.le_iff_toNat_le.mpr e))]
    exact ih F m₁ m' a₁ h c d k r (by omega) hA₁ hh hb

theorem rnodeOK_succ (n : Nat) (ih : RArmOK n) : RNodeOK (n + 1) := by
  intro F m m' a h c d k r hF hA hh hb
  have arm := ih F m m' a h c d k r (by omega) hA hh
  have t4 : h >>> 28 = 4 ↔ (h >>> 28).toUInt32 = 4 := by simpa using tag_iff h 4 hh (by decide)
  have t5 : h >>> 28 = 5 ↔ (h >>> 28).toUInt32 = 5 := by simpa using tag_iff h 5 hh (by decide)
  have t6 : h >>> 28 = 6 ↔ (h >>> 28).toUInt32 = 6 := by simpa using tag_iff h 6 hh (by decide)
  have t1 : h >>> 28 = 1 ↔ (h >>> 28).toUInt32 = 1 := by simpa using tag_iff h 1 hh (by decide)
  have t7 : h >>> 28 = 7 ↔ (h >>> 28).toUInt32 = 7 := by simpa using tag_iff h 7 hh (by decide)
  have t9 : h >>> 28 = 9 ↔ (h >>> 28).toUInt32 = 9 := by simpa using tag_iff h 9 hh (by decide)
  simp only [arNodeA, decE_tag h hh]
  simp only [ETag.app, ETag.isBind, ETag.lam, ETag.forallE, ETag.fvar, ETag.letE, ETag.proj,
    beq_iff_eq, Bool.or_eq_true] at *
  by_cases g4 : h >>> 28 = 4
  · rw [arNodeW_app n m h c d k g4] at hb
    simp only [show (h >>> 28).toUInt32 = 4 from (t4.mp g4), ↓reduceIte]
    exact arm.1 g4 hb
  have g4' : ¬ (h >>> 28).toUInt32 = 4 := fun e => g4 (t4.mpr e)
  by_cases g5 : h >>> 28 = 5
  · rw [arNodeW_lam n m h c d k g5] at hb
    simp only [g4', show (h >>> 28).toUInt32 = 5 from (t5.mp g5), true_or, ↓reduceIte]
    exact arm.2.1 g5 hb
  have g5' : ¬ (h >>> 28).toUInt32 = 5 := fun e => g5 (t5.mpr e)
  by_cases g6 : h >>> 28 = 6
  · rw [arNodeW_forall n m h c d k g6] at hb
    simp only [g4', g5', show (h >>> 28).toUInt32 = 6 from (t6.mp g6), or_true, ↓reduceIte]
    exact arm.2.2.1 g6 hb
  have g6' : ¬ (h >>> 28).toUInt32 = 6 := fun e => g6 (t6.mpr e)
  simp only [g4', g5', g6', or_self, ↓reduceIte]
  by_cases g1 : h >>> 28 = 1
  · simp only [show (h >>> 28).toUInt32 = 1 from (t1.mp g1), ↓reduceIte]
    by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
    · rw [arNodeW] at hb; simp [g4, g5, g6, g1, hs] at hb
    by_cases hc : rdW (m.arr64 CTL) (26 + tierW h) ≤ idxW h
    · rw [arNodeW] at hb; simp [g4, g5, g6, g1, hs, hc] at hb
    have hv : viewOK m h 26 := ⟨hs, UInt64.not_le.mp hc⟩
    by_cases hdk : d + k < d
    · rw [arNodeW] at hb; simp [g4, g5, g6, g1, hs, hc, hdk] at hb
    rw [absRangeArmFVar, StateT.run_bind, viewFVarIdx_run, viewFVarIdx_ok m a hA.1.1 h hh hv]
    simp only [except_ok_bind]
    by_cases hi : d ≤ rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2) ∧ rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2) < d + k
    · by_cases ho : c + (d + k - 1 - rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2)) < c
      · rw [arNodeW] at hb; simp [g4, g5, g6, g1, hs, hc, hdk, hi, ho] at hb
      rw [arNodeW_fvar_in n m h c d k hv g1 hdk hi ho] at hb
      obtain ⟨hok, hA', hres⟩ := internBVar_A m a hA _ r m' hb
      rw [rng_word c d k _ hdk hi ho] at hok hA' hres
      simp only [(rng_iff d k _ hdk).mp hi, ↓reduceIte, internBVarE]
      rw [AM.run_of_ok _ _ hok, hres]; exact ⟨_, rfl, hA'⟩
    · rw [arNodeW_fvar_out n m h c d k hv g1 hdk hi] at hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      have hi' := fun e => hi ((rng_iff d k _ hdk).mpr e)
      simp only [Bool.eq_false_iff.mpr hi', Bool.false_eq_true, ↓reduceIte]; exact ⟨a, rfl, hA⟩
  have g1' : ¬ (h >>> 28).toUInt32 = 1 := fun e => g1 (t1.mpr e)
  simp only [g1', ↓reduceIte]
  by_cases g7 : h >>> 28 = 7
  · rw [arNodeW_let n m h c d k g7] at hb
    simp only [show (h >>> 28).toUInt32 = 7 from (t7.mp g7), ↓reduceIte]
    exact arm.2.2.2.1 g7 hb
  have g7' : ¬ (h >>> 28).toUInt32 = 7 := fun e => g7 (t7.mpr e)
  simp only [g7', ↓reduceIte]
  by_cases g9 : h >>> 28 = 9
  · rw [arNodeW_proj n m h c d k g9] at hb
    simp only [show (h >>> 28).toUInt32 = 9 from (t9.mp g9), ↓reduceIte]
    exact arm.2.2.2.2 g9 hb
  have g9' : ¬ (h >>> 28).toUInt32 = 9 := fun e => g9 (t9.mpr e)
  simp only [g9', ↓reduceIte]
  rw [arNodeW_leaf n m h c d k g1 g4 g5 g6 g7 g9] at hb
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
  exact ⟨a, rfl, hA⟩

/-! ## The arms -/

section arms
variable (n F : Nat) (ih : RGoOK n) (hF : n ≤ F) (m m' : Mem) (a : AState) (hA : ArenaA m a)
  (h c d k r : Word) (hh : h.toNat < 2 ^ 32)
include ih hF hA hh

theorem rappArm_ok (hg : h >>> 28 = 4) :
    RArmRef (n + 1) arAppW (absRangeGoArmApp d.toNat k.toNat F (decE h) c.toNat) m m' a h c d k r := by
  intro hb
  rw [absRangeGoArmApp]
  refine aprobe_ok _ _ m m' a hA h c r hh (arAppW_hit n m h c d k)
    (fun hr => by rw [arAppW]; simp [hr]) (fun hr hh0 hb => ?_) hb
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [arAppW] at hb; simp only [ne_eq] at hs; simp only [hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, not_false_eq_true, and_self, reduceCtorEq] at hb
  by_cases hc : rdW (m.arr64 CTL) (4 + tierW h) ≤ idxW h
  · rw [arAppW] at hb; simp only [ne_eq] at hs; simp only [hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, hc, not_false_eq_true, and_self, and_true, reduceCtorEq] at hb
  have hv : viewOK m h 4 := ⟨hs, UInt64.not_le.mp hc⟩
  obtain ⟨-, hfw, haw⟩ := view_app m a hA.1.1 h hh hv hg
  rw [arAppW_miss n m h c d k hr hh0 hv] at hb
  rw [StateT.run_bind, viewApp_run, viewApp_ok m a hA.1.1 h hh hv, except_ok_bind]
  cases h1 : arW n m (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2)) c d k with
  | none => simp [h1, rappK₁] at hb
  | some p =>
  obtain ⟨x, m₁⟩ := p
  cases h2 : arW n m₁ (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2 + 1)) c d k with
  | none => simp [h1, h2, rappK₁, rappK₁.rappK₂] at hb
  | some q =>
  obtain ⟨y, m₂⟩ := q
  simp only [h1, h2, rappK₁, rappK₁.rappK₂] at hb
  obtain ⟨a₁, ha₁, hA₁⟩ := ih F m m₁ a _ c d k x hF hA hfw h1
  obtain ⟨a₂, ha₂, hA₂⟩ := ih F m₁ m₂ a₁ _ c d k y hF hA₁ haw h2
  obtain ⟨a', h3, h4⟩ := atail_ok (internRebuiltApp (decE h)
      (decE x == decE (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2)) && decE y == decE (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2 + 1))) (decE x) (decE y))
      _ a₂ h c r m' hh (fun r₃ m₃ hr₃ => by
    unfold internRebuiltApp
    refine rb_ok _ _ _ _ m₂ a₂ hA₂ h r₃ m₃ (fun ⟨e1, e2⟩ => by simp [e1, e2]) (fun hn hI => ?_) hr₃
    obtain ⟨hx, hy⟩ := mkAppW_lt m₂ x y r₃ m₃ hI
    refine ⟨?_, mkApp_okA m₂ a₂ hA₂ x y r₃ m₃ hI⟩
    rcases Decidable.em (decE x = decE (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2))) with e1 | e1
    · have e2 : decE y ≠ decE (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2 + 1)) :=
        fun e2 => hn ⟨decE_inj _ _ hx hfw e1, decE_inj _ _ hy haw e2⟩
      simp [e1, e2]
    · simp [e1]) hb
  exact ⟨a', by simp only [StateT.run_bind, ha₁, ha₂, except_ok_bind]; exact h3, h4⟩

theorem rlamArm_ok (hg : h >>> 28 = 5) :
    RArmRef (n + 1) arLamW (absRangeGoArmBind d.toNat k.toNat F (decE h) c.toNat) m m' a h c d k r := by
  intro hb
  by_cases hk1 : c + 1 = 0
  · rw [arLamW] at hb; simp [hk1] at hb
  rw [absRangeGoArmBind]
  refine aprobe_ok _ _ m m' a hA h c r hh (arLamW_hit n m h c d k hk1)
    (fun hr => by rw [arLamW]; simp [hk1, hr]) (fun hr hh0 hb => ?_) hb
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [arLamW] at hb; simp only [ne_eq] at hs; simp only [hk1, hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, not_false_eq_true, and_self, reduceCtorEq] at hb
  by_cases hc : rdW (m.arr64 CTL) (28 + tierW h) ≤ idxW h
  · rw [arLamW] at hb; simp only [ne_eq] at hs; simp only [hk1, hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, hc, not_false_eq_true, and_self, and_true, reduceCtorEq] at hb
  have hv : viewOK m h 28 := ⟨hs, UInt64.not_le.mp hc⟩
  obtain ⟨-, hfw, haw⟩ := view_lam m a hA.1.1 h hh hv hg
  rw [arLamW_miss n m h c d k hk1 hr hh0 hv] at hb
  rw [StateT.run_bind, viewBind_run, viewBind_lam m a hA.1.1 h hh hv hg, except_ok_bind]
  cases h1 : arW n m (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2)) c d k with
  | none => simp [h1, rlamK₁] at hb
  | some p =>
  obtain ⟨x, m₁⟩ := p
  cases h2 : arW n m₁ (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2 + 1)) (c + 1) d k with
  | none => simp [h1, h2, rlamK₁, rlamK₁.rlamK₂] at hb
  | some q =>
  obtain ⟨y, m₂⟩ := q
  simp only [h1, h2, rlamK₁, rlamK₁.rlamK₂] at hb
  obtain ⟨a₁, ha₁, hA₁⟩ := ih F m m₁ a _ c d k x hF hA hfw h1
  obtain ⟨a₂, ha₂, hA₂⟩ := ih F m₁ m₂ a₁ _ (c + 1) d k y hF hA₁ haw h2
  rw [succW_toNat c hk1] at ha₂
  have hbind : ∀ t b, internBindE (decE h).tag t b = internE (.lam t b) := by
    intro t b; simp [internBindE, decE_tag h hh, hg, ETag.lam, internE]
  obtain ⟨a', h3, h4⟩ := atail_ok (internRebuiltBind (decE h)
      (decE x == decE (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2)) && decE y == decE (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2 + 1))) (decE h).tag (decE x) (decE y))
      _ a₂ h c r m' hh (fun r₃ m₃ hr₃ => by
    unfold internRebuiltBind
    rw [hbind]
    refine rb_ok _ _ _ _ m₂ a₂ hA₂ h r₃ m₃ (fun ⟨e1, e2⟩ => by simp [e1, e2]) (fun hn hI => ?_) hr₃
    obtain ⟨hx, hy⟩ := mkLamW_lt m₂ x y r₃ m₃ hI
    refine ⟨?_, mkLam_okA m₂ a₂ hA₂ x y r₃ m₃ hI⟩
    rcases Decidable.em (decE x = decE (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2))) with e1 | e1
    · have e2 : decE y ≠ decE (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2 + 1)) :=
        fun e2 => hn ⟨decE_inj _ _ hx hfw e1, decE_inj _ _ hy haw e2⟩
      simp [e1, e2]
    · simp [e1]) hb
  exact ⟨a', by simp only [StateT.run_bind, ha₁, ha₂, except_ok_bind]; exact h3, h4⟩

theorem rforallArm_ok (hg : h >>> 28 = 6) :
    RArmRef (n + 1) arForallW (absRangeGoArmBind d.toNat k.toNat F (decE h) c.toNat) m m' a h c d k r := by
  intro hb
  by_cases hk1 : c + 1 = 0
  · rw [arForallW] at hb; simp [hk1] at hb
  rw [absRangeGoArmBind]
  refine aprobe_ok _ _ m m' a hA h c r hh (arForallW_hit n m h c d k hk1)
    (fun hr => by rw [arForallW]; simp [hk1, hr]) (fun hr hh0 hb => ?_) hb
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [arForallW] at hb; simp only [ne_eq] at hs; simp only [hk1, hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, not_false_eq_true, and_self, reduceCtorEq] at hb
  by_cases hc : rdW (m.arr64 CTL) (30 + tierW h) ≤ idxW h
  · rw [arForallW] at hb; simp only [ne_eq] at hs; simp only [hk1, hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, hc, not_false_eq_true, and_self, and_true, reduceCtorEq] at hb
  have hv : viewOK m h 30 := ⟨hs, UInt64.not_le.mp hc⟩
  obtain ⟨-, hfw, haw⟩ := view_forall m a hA.1.1 h hh hv hg
  rw [arForallW_miss n m h c d k hk1 hr hh0 hv] at hb
  rw [StateT.run_bind, viewBind_run, viewBind_forall m a hA.1.1 h hh hv hg, except_ok_bind]
  cases h1 : arW n m (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2)) c d k with
  | none => simp [h1, rfaK₁] at hb
  | some p =>
  obtain ⟨x, m₁⟩ := p
  cases h2 : arW n m₁ (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2 + 1)) (c + 1) d k with
  | none => simp [h1, h2, rfaK₁, rfaK₁.rfaK₂] at hb
  | some q =>
  obtain ⟨y, m₂⟩ := q
  simp only [h1, h2, rfaK₁, rfaK₁.rfaK₂] at hb
  obtain ⟨a₁, ha₁, hA₁⟩ := ih F m m₁ a _ c d k x hF hA hfw h1
  obtain ⟨a₂, ha₂, hA₂⟩ := ih F m₁ m₂ a₁ _ (c + 1) d k y hF hA₁ haw h2
  rw [succW_toNat c hk1] at ha₂
  have hbind : ∀ t b, internBindE (decE h).tag t b = internE (.forallE t b) := by
    intro t b; simp [internBindE, decE_tag h hh, hg, ETag.lam, internE]
  obtain ⟨a', h3, h4⟩ := atail_ok (internRebuiltBind (decE h)
      (decE x == decE (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2)) && decE y == decE (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2 + 1))) (decE h).tag (decE x) (decE y))
      _ a₂ h c r m' hh (fun r₃ m₃ hr₃ => by
    unfold internRebuiltBind
    rw [hbind]
    refine rb_ok _ _ _ _ m₂ a₂ hA₂ h r₃ m₃ (fun ⟨e1, e2⟩ => by simp [e1, e2]) (fun hn hI => ?_) hr₃
    obtain ⟨hx, hy⟩ := mkForallW_lt m₂ x y r₃ m₃ hI
    refine ⟨?_, mkForall_okA m₂ a₂ hA₂ x y r₃ m₃ hI⟩
    rcases Decidable.em (decE x = decE (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2))) with e1 | e1
    · have e2 : decE y ≠ decE (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2 + 1)) :=
        fun e2 => hn ⟨decE_inj _ _ hx hfw e1, decE_inj _ _ hy haw e2⟩
      simp [e1, e2]
    · simp [e1]) hb
  exact ⟨a', by simp only [StateT.run_bind, ha₁, ha₂, except_ok_bind]; exact h3, h4⟩

theorem rletArm_ok (hg : h >>> 28 = 7) :
    RArmRef (n + 1) arLetW (absRangeGoArmLet d.toNat k.toNat F (decE h) c.toNat) m m' a h c d k r := by
  intro hb
  by_cases hk1 : c + 1 = 0
  · rw [arLetW] at hb; simp [hk1] at hb
  rw [absRangeGoArmLet]
  refine aprobe_ok _ _ m m' a hA h c r hh (arLetW_hit n m h c d k hk1)
    (fun hr => by rw [arLetW]; simp [hk1, hr]) (fun hr hh0 hb => ?_) hb
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [arLetW] at hb; simp only [ne_eq] at hs; simp only [hk1, hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, not_false_eq_true, and_self, reduceCtorEq] at hb
  by_cases hc : rdW (m.arr64 CTL) (20 + tierW h) ≤ idxW h
  · rw [arLetW] at hb; simp only [ne_eq] at hs; simp only [hk1, hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, hc, not_false_eq_true, and_self, and_true, reduceCtorEq] at hb
  have hv : viewOK m h 20 := ⟨hs, UInt64.not_le.mp hc⟩
  obtain ⟨-, htw, hvw, hbw⟩ := view_let m a hA.1.1 h hh hv hg
  rw [arLetW_miss n m h c d k hk1 hr hh0 hv] at hb
  rw [StateT.run_bind, viewLet_run, viewLet_ok m a hA.1.1 h hh hv, except_ok_bind]
  cases h1 : arW n m (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3)) c d k with
  | none => simp [h1, rleK₁] at hb
  | some p =>
  obtain ⟨x, m₁⟩ := p
  cases h2 : arW n m₁ (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 1)) c d k with
  | none => simp [h1, h2, rleK₁, rleK₁.rleK₂] at hb
  | some q =>
  obtain ⟨y, m₂⟩ := q
  cases h3 : arW n m₂ (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 2)) (c + 1) d k with
  | none => simp [h1, h2, h3, rleK₁, rleK₁.rleK₂, rleK₁.rleK₃] at hb
  | some o =>
  obtain ⟨z, m₃⟩ := o
  simp only [h1, h2, h3, rleK₁, rleK₁.rleK₂, rleK₁.rleK₃] at hb
  obtain ⟨a₁, ha₁, hA₁⟩ := ih F m m₁ a _ c d k x hF hA htw h1
  obtain ⟨a₂, ha₂, hA₂⟩ := ih F m₁ m₂ a₁ _ c d k y hF hA₁ hvw h2
  obtain ⟨a₃, ha₃, hA₃⟩ := ih F m₂ m₃ a₂ _ (c + 1) d k z hF hA₂ hbw h3
  rw [succW_toNat c hk1] at ha₃
  obtain ⟨a', h4, h5⟩ := atail_ok (internRebuiltLetE (decE h)
      (decE x == decE (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3)) && decE y == decE (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 1)) && decE z == decE (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 2)))
      (decE x) (decE y) (decE z)) _ a₃ h c r m' hh (fun r₄ m₄ hr₄ => by
    unfold internRebuiltLetE internLetEE
    refine rb_ok _ _ _ _ m₃ a₃ hA₃ h r₄ m₄ (fun ⟨e1, e2, e3⟩ => by simp [e1, e2, e3])
      (fun hn hI => ?_) hr₄
    obtain ⟨hx, hy, hz⟩ := mkLetW_lt m₃ x y z r₄ m₄ hI
    refine ⟨?_, mkLet_okA m₃ a₃ hA₃ x y z r₄ m₄ hI⟩
    rcases Decidable.em (decE x = decE (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3))) with e1 | e1
    · rcases Decidable.em (decE y = decE (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 1)))
        with e2 | e2
      · have e3 : decE z ≠ decE (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 2)) :=
          fun e3 => hn ⟨decE_inj _ _ hx htw e1, decE_inj _ _ hy hvw e2, decE_inj _ _ hz hbw e3⟩
        simp [e1, e2, e3]
      · simp [e1, e2]
    · simp [e1]) hb
  exact ⟨a', by simp only [StateT.run_bind, ha₁, ha₂, ha₃, except_ok_bind]; exact h4, h5⟩

theorem rprojArm_ok (hg : h >>> 28 = 9) :
    RArmRef (n + 1) arProjW (absRangeGoArmProj d.toNat k.toNat F (decE h) c.toNat) m m' a h c d k r := by
  intro hb
  rw [absRangeGoArmProj]
  refine aprobe_ok _ _ m m' a hA h c r hh (arProjW_hit n m h c d k)
    (fun hr => by rw [arProjW]; simp [hr]) (fun hr hh0 hb => ?_) hb
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [arProjW] at hb; simp only [ne_eq] at hs; simp only [hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, not_false_eq_true, and_self, reduceCtorEq] at hb
  by_cases hc : rdW (m.arr64 CTL) (32 + tierW h) ≤ idxW h
  · rw [arProjW] at hb; simp only [ne_eq] at hs; simp only [hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, hc, not_false_eq_true, and_self, and_true, reduceCtorEq] at hb
  have hv : viewOK m h 32 := ⟨hs, UInt64.not_le.mp hc⟩
  obtain ⟨-, -, hew⟩ := view_proj m a hA.1.1 h hh hv hg
  rw [arProjW_miss n m h c d k hr hh0 hv] at hb
  rw [StateT.run_bind, viewProj_run, viewProj_ok m a hA.1.1 h hh hv, except_ok_bind]
  cases h1 : arW n m (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 2)) c d k with
  | none => simp [h1, rpjK₁] at hb
  | some p =>
  obtain ⟨x, m₁⟩ := p
  simp only [h1, rpjK₁] at hb
  obtain ⟨a₁, ha₁, hA₁⟩ := ih F m m₁ a _ c d k x hF hA hew h1
  obtain ⟨a', h3, h4⟩ := atail_ok (internRebuiltProj (decE h) (decE x == decE (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 2)))
      (decI (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3))) (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 1)).toNat (decE x)) _ a₁ h c r m' hh (fun r₃ m₃ hr₃ => by
    unfold internRebuiltProj internProjE
    refine rb_ok _ _ _ _ m₁ a₁ hA₁ h r₃ m₃ (fun e1 => by simp [e1]) (fun hn hI => ?_) hr₃
    have hx := mkProjW_lt m₁ _ _ x r₃ m₃ hI
    refine ⟨?_, mkProj_okA m₁ a₁ hA₁ _ _ x r₃ m₃ hI⟩
    have e1 : decE x ≠ decE (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 2)) :=
      fun e1 => hn (decE_inj _ _ hx hew e1)
    simp [e1]) hb
  exact ⟨a', by simp only [StateT.run_bind, ha₁, except_ok_bind]; exact h3, h4⟩

end arms

theorem rarmOK_succ (n : Nat) (ih : RGoOK n) : RArmOK (n + 1) := by
  intro F m m' a h c d k r hF hA hh
  have hF' : n ≤ F := by omega
  exact ⟨rappArm_ok n F ih hF' m m' a hA h c d k r hh, rlamArm_ok n F ih hF' m m' a hA h c d k r hh,
    rforallArm_ok n F ih hF' m m' a hA h c d k r hh, rletArm_ok n F ih hF' m m' a hA h c d k r hh,
    rprojArm_ok n F ih hF' m m' a hA h c d k r hh⟩

/-- **The model of `ar_go` refines `abstractRangeGo`** at every fuel. -/
theorem arOK (n : Nat) : RGoOK n ∧ RNodeOK n ∧ RArmOK n := by
  induction n with
  | zero =>
    refine ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ hb => by simp [arW] at hb,
      fun _ _ _ _ _ _ _ _ _ _ _ _ hb => by simp [arNodeW] at hb,
      fun _ _ _ _ _ _ _ _ _ _ _ _ => ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    intro _ hb <;> simp [arAppW, arLamW, arForallW, arLetW, arProjW] at hb
  | succ n ih => exact ⟨rgoOK_succ n ih.2.1, rnodeOK_succ n ih.2.2, rarmOK_succ n ih.1⟩


/-! ## The entry `ar_entry` refines `abstractRangeFast` -/

theorem arFast_run (F : Nat) (e : EIdx) (d k c : Nat) (hk : k ≠ 0) (a : AState) :
    (abstractRangeFast F e d k c).run a =
      ((abstractRangeGo d k F e c).run (withAC a ∅) >>= fun p => .ok (p.1, withAC p.2 ∅)) := by
  simp only [abstractRangeFast, hk, ↓reduceIte, StateT.run_bind, abs1Clear_run, except_ok_bind]
  cases (abstractRangeGo d k F e c).run (withAC a ∅) <;> rfl

theorem arEntryW_correct (n F : Nat) (hF : n ≤ F) (m m' : Mem) (a : AState) (hA : ArenaA m a)
    (e d k c r : Word) (he : e.toNat < 2 ^ 32) (hb : arEntryW n m e d k c = some (r, m')) :
    ∃ a', (abstractRangeFast F (decE e) d.toNat k.toNat c.toNat).run a = .ok (decE r, a') ∧
      ArenaA m' a' := by
  simp only [arEntryW] at hb
  by_cases hk : k = 0
  · simp only [hk, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact ⟨a, by simp [abstractRangeFast, hk]; rfl, hA⟩
  have hk' : k.toNat ≠ 0 := fun e => hk (UInt64.toNat_inj.mp e)
  simp only [hk, ↓reduceIte] at hb
  by_cases h0 : rdW (m.arr64 CTL) 48 + 2 = 0
  · simp [h0] at hb
  simp only [h0, ↓reduceIte] at hb
  have hA₀ := ArenaA.amemo_clear m a hA h0
  cases hw : arW n (mclearG abSch m) e c d k with
  | none => simp [hw, aclrK] at hb
  | some p =>
    obtain ⟨r₁, m₁⟩ := p
    by_cases h1 : rdW (m₁.arr64 CTL) 48 + 2 = 0
    · simp [hw, aclrK, h1] at hb
    simp only [hw, aclrK, h1, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    obtain ⟨a₁, ha₁, hA₁⟩ := (arOK n).1 F _ _ _ e c d k r₁ hF hA₀ he hw
    exact ⟨_, by rw [arFast_run _ _ _ _ _ hk', ha₁]; rfl, ArenaA.amemo_clear m₁ a₁ hA₁ h1⟩

/-- **`ar_entry(e, d, k, c)` refines the arena's `abstractRangeFast` under `ArenaA`.** -/
@[refines ConRon.Arena.abstractRangeFast]
theorem arEntry_refines (p : Prog) (hp : ArProg p) (hpe : p.lookup "ar_entry" = some arEntry)
    (n F : Nat) (hF : n ≤ F) (s₀ : St) (a₀ : AState) (hA : ArenaA s₀.mem a₀) (e d k c : Word)
    (he : e.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "ar_entry" [e, d, k, c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (abstractRangeFast F (decE e) d.toNat k.toNat c.toNat) a₀ ∧
      ArenaA s'.mem (AM.st (abstractRangeFast F (decE e) d.toNat k.toNat c.toNat) a₀) ∧
      AM.res (abstractRangeFast F (decE e) d.toNat k.toNat c.toNat) a₀ = decE (r.headD 0); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun (arEntry_spec p hp hpe n s₀ e d k c)
  subst hs
  obtain ⟨a', ha', hA'⟩ := arEntryW_correct n F hF _ _ a₀ hA e d k c _ he hI
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ ha'
  exact ⟨hloc, hok, hst ▸ hA', hres⟩

end L.Arena
