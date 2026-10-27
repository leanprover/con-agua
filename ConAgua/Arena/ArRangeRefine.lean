import ConAgua.Arena.ArRangeSpec
import ConAgua.Arena.Abs1Refine
import ConAgua.Census.Attr
import Std.Tactic.BVDecide.Normalize.Prop

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

/-- What `ar_go`'s model at L fuel `n` and counter `fu` says about the arena walk at the twin
fuel `fu.toNat` (exactly: the counter is the twin's `fuel`, any L fuel). -/
def RGoOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (h c d k fu r : Word), ArenaA m a →
    h.toNat < 2 ^ 32 → arW n m h c d k fu = some (r, m') →
    ∃ a', (abstractRangeGo d.toNat k.toNat fu.toNat (decE h) c.toNat).run a = .ok (decE r, a') ∧
      ArenaA m' a'

/-- The same for `ar_node` and the dispatch. -/
def RNodeOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (h c d k fu r : Word), ArenaA m a →
    h.toNat < 2 ^ 32 → arNodeW n m h c d k fu = some (r, m') →
    ∃ a', (arNodeA d.toNat k.toNat fu.toNat (decE h) c.toNat).run a = .ok (decE r, a') ∧ ArenaA m' a'

/-- The arena arm `arm` refines the L arm `armW` at `h`, under `ArenaA`. -/
def RArmRef (n : Nat) (armW : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem))
    (arm : AM EIdx) (m m' : Mem) (a : AState) (h c d k fu r : Word) : Prop :=
  armW n m h c d k fu = some (r, m') → ∃ a', arm.run a = .ok (decE r, a') ∧ ArenaA m' a'

/-- The five arms, each at its tag. -/
def RArmOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (h c d k fu r : Word), ArenaA m a →
    h.toNat < 2 ^ 32 →
    (h >>> 28 = 4 → RArmRef n arAppW (absRangeGoArmApp d.toNat k.toNat fu.toNat (decE h) c.toNat) m m' a h c d k fu r) ∧
    (h >>> 28 = 5 → RArmRef n arLamW (absRangeGoArmBind d.toNat k.toNat fu.toNat (decE h) c.toNat) m m' a h c d k fu r) ∧
    (h >>> 28 = 6 →
      RArmRef n arForallW (absRangeGoArmBind d.toNat k.toNat fu.toNat (decE h) c.toNat) m m' a h c d k fu r) ∧
    (h >>> 28 = 7 → RArmRef n arLetW (absRangeGoArmLet d.toNat k.toNat fu.toNat (decE h) c.toNat) m m' a h c d k fu r) ∧
    (h >>> 28 = 9 → RArmRef n arProjW (absRangeGoArmProj d.toNat k.toNat fu.toNat (decE h) c.toNat) m m' a h c d k fu r)

theorem rgoOK_succ (n : Nat) (ih : RNodeOK n) : RGoOK (n + 1) := by
  intro m m' a h c d k fu r hA hh hb
  have hfu : ¬ fu = 0 := fun hfu => by rw [arW] at hb; simp [hfu] at hb
  rw [arW_eq n m h c d k fu hfu] at hb
  rw [ctrW_toNat fu hfu, abstractRangeGo_succ']
  refine SimD.exists (Sim.bindD rfl (fun _ _ => rfl)
    (Sim.ofD fun x m₁ e => fvbW_ok n m m₁ a hA h (fu - 1) x hh e) fun x m₁ a₁ hA₁ => ?_) hb
  rw [rcutK_some]
  by_cases hc : x ≤ d
  · rw [ite_eq_left hc, ite_eq_left (UInt64.le_iff_toNat_le.mp hc)]; exact Sim.ret ⟨rfl, hA₁⟩
  · rw [ite_eq_right hc, ite_eq_right (fun e => hc (UInt64.le_iff_toNat_le.mpr e))]
    exact Sim.ofD fun r m' hb => ih m₁ m' a₁ h c d k (fu - 1) r hA₁ hh hb

theorem rnodeOK_succ (n : Nat) (ih : RArmOK n) : RNodeOK (n + 1) := by
  intro m m' a h c d k fu r hA hh hb
  have arm := ih m m' a h c d k fu r hA hh
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
  · rw [arNodeW_app n m h c d k fu g4] at hb
    simp only [show (h >>> 28).toUInt32 = 4 from (t4.mp g4), ↓reduceIte]
    exact arm.1 g4 hb
  have g4' : ¬ (h >>> 28).toUInt32 = 4 := fun e => g4 (t4.mpr e)
  by_cases g5 : h >>> 28 = 5
  · rw [arNodeW_lam n m h c d k fu g5] at hb
    simp only [show (h >>> 28).toUInt32 = 5 from (t5.mp g5), true_or, ↓reduceIte]
    exact arm.2.1 g5 hb
  have g5' : ¬ (h >>> 28).toUInt32 = 5 := fun e => g5 (t5.mpr e)
  by_cases g6 : h >>> 28 = 6
  · rw [arNodeW_forall n m h c d k fu g6] at hb
    simp only [show (h >>> 28).toUInt32 = 6 from (t6.mp g6), or_true, ↓reduceIte]
    exact arm.2.2.1 g6 hb
  have g6' : ¬ (h >>> 28).toUInt32 = 6 := fun e => g6 (t6.mpr e)
  simp only [g4', g5', g6', or_self, ↓reduceIte]
  by_cases g1 : h >>> 28 = 1
  · simp only [show (h >>> 28).toUInt32 = 1 from (t1.mp g1), ↓reduceIte]
    have hs : ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) := fun hs => by rw [arNodeW] at hb; simp [g1, hs] at hb
    by_cases hc : tcnt m FVAR (tierW h) ≤ idxW h
    · rw [arNodeW] at hb; simp [g1, hs, hc] at hb
    have hv : viewOK m h FVAR := ⟨hs, UInt64.not_le.mp hc⟩
    by_cases hdk : d + k < d
    · rw [arNodeW] at hb; simp [g1, hs, hc, hdk] at hb
    rw [absRangeArmFVar, StateT.run_bind, viewFVarIdx_run, viewFVarIdx_ok m a hA.1.1 h hh hv]
    simp only [except_ok_bind]
    by_cases hi : d ≤ tfld m FVAR (tierW h) (idxW h) 0 ∧ tfld m FVAR (tierW h) (idxW h) 0 < d + k
    · by_cases ho : c + (d + k - 1 - tfld m FVAR (tierW h) (idxW h) 0) < c
      · rw [arNodeW] at hb; simp [g1, hs, hc, hdk, hi, ho] at hb
      rw [arNodeW_fvar_in n m h c d k fu hv g1 hdk hi ho] at hb
      obtain ⟨hok, hA', hres⟩ := internBVar_A m a hA _ r m' hb
      rw [rng_word c d k _ hdk hi ho] at hok hA' hres
      simp only [(rng_iff d k _ hdk).mp hi, ↓reduceIte, internBVarE]
      rw [AM.run_of_ok _ _ hok, hres]; exact ⟨_, rfl, hA'⟩
    · rw [arNodeW_fvar_out n m h c d k fu hv g1 hdk hi] at hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      have hi' := fun e => hi ((rng_iff d k _ hdk).mpr e)
      simp only [Bool.eq_false_iff.mpr hi', Bool.false_eq_true, ↓reduceIte]; exact ⟨a, rfl, hA⟩
  have g1' : ¬ (h >>> 28).toUInt32 = 1 := fun e => g1 (t1.mpr e)
  simp only [g1', ↓reduceIte]
  by_cases g7 : h >>> 28 = 7
  · rw [arNodeW_let n m h c d k fu g7] at hb
    simp only [show (h >>> 28).toUInt32 = 7 from (t7.mp g7), ↓reduceIte]
    exact arm.2.2.2.1 g7 hb
  have g7' : ¬ (h >>> 28).toUInt32 = 7 := fun e => g7 (t7.mpr e)
  simp only [g7', ↓reduceIte]
  by_cases g9 : h >>> 28 = 9
  · rw [arNodeW_proj n m h c d k fu g9] at hb
    simp only [show (h >>> 28).toUInt32 = 9 from (t9.mp g9), ↓reduceIte]
    exact arm.2.2.2.2 g9 hb
  have g9' : ¬ (h >>> 28).toUInt32 = 9 := fun e => g9 (t9.mpr e)
  simp only [g9', ↓reduceIte]
  rw [arNodeW_leaf n m h c d k fu g1 g4 g5 g6 g7 g9] at hb
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
  exact ⟨a, rfl, hA⟩

/-! ## The arms -/

section arms
variable (n : Nat) (ih : RGoOK n) (m m' : Mem) (a : AState) (hA : ArenaA m a)
  (h c d k fu r : Word) (hh : h.toNat < 2 ^ 32)
include ih hA hh

theorem rappArm_ok (hg : h >>> 28 = 4) :
    RArmRef (n + 1) arAppW (absRangeGoArmApp d.toNat k.toNat fu.toNat (decE h) c.toNat) m m' a h c d k fu r := by
  intro hb
  rw [absRangeGoArmApp]
  refine aprobe_ok _ _ m m' a hA h c r hh (arAppW_hit n m h c d k fu)
    (fun hr => by rw [arAppW]; simp [hr]) (fun hr hh0 hb => ?_) hb
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [arAppW] at hb; simp only [ne_eq] at hs; simp only [hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, not_false_eq_true, and_self, reduceCtorEq] at hb
  have hv : viewOK m h APP := ⟨hs, UInt64.not_le.mp fun hc => by
    rw [arAppW] at hb; simp only [ne_eq] at hs; simp only [hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, hc, reduceCtorEq] at hb⟩
  obtain ⟨-, hfw, haw⟩ := view_app m a hA.1.1 h hh hv hg
  rw [arAppW_miss n m h c d k fu hr hh0 hv] at hb
  rw [StateT.run_bind, viewApp_run, viewApp_ok m a hA.1.1 h hh hv, except_ok_bind]
  refine SimD.exists (Sim.bindD rfl (fun _ _ => rfl)
    (Sim.ofD fun x m₁ e => ih m m₁ a _ c d k fu x hA hfw e) fun x m₁ a₁ hA₁ => ?_) hb
  refine Sim.bindD (K := rappK₁.rappK₂ h c _ _ x) rfl (fun _ _ => rfl)
    (Sim.ofD fun y m₂ e => ih m₁ m₂ a₁ _ c d k fu y hA₁ haw e) fun y m₂ a₂ hA₂ => ?_
  refine Sim.ofD fun r m' hb => atail_ok (internRebuiltApp (decE h)
      (decE x == decE (tfld m APP (tierW h) (idxW h) 0) && decE y == decE (tfld m APP (tierW h) (idxW h) 1)) (decE x) (decE y))
      _ a₂ h c r m' hh (fun r₃ m₃ hr₃ => by
    unfold internRebuiltApp
    refine rb_ok _ _ _ _ m₂ a₂ hA₂ h r₃ m₃ (fun ⟨e1, e2⟩ => by simp [e1, e2]) (fun hn hI => ?_) hr₃
    obtain ⟨hx, hy⟩ := mkAppW_lt m₂ x y r₃ m₃ hI
    refine ⟨?_, mkApp_okA m₂ a₂ hA₂ x y r₃ m₃ hI⟩
    rcases Decidable.em (decE x = decE (tfld m APP (tierW h) (idxW h) 0)) with e1 | e1
    · have e2 : decE y ≠ decE (tfld m APP (tierW h) (idxW h) 1) :=
        fun e2 => hn ⟨decE_inj _ _ hx hfw e1, decE_inj _ _ hy haw e2⟩
      simp [e1, e2]
    · simp [e1]) hb

theorem rlamArm_ok (hg : h >>> 28 = 5) :
    RArmRef (n + 1) arLamW (absRangeGoArmBind d.toNat k.toNat fu.toNat (decE h) c.toNat) m m' a h c d k fu r := by
  intro hb
  have hk1 : ¬ c + 1 = 0 := fun hk1 => by rw [arLamW] at hb; simp [hk1] at hb
  rw [absRangeGoArmBind]
  refine aprobe_ok _ _ m m' a hA h c r hh (arLamW_hit n m h c d k fu hk1)
    (fun hr => by rw [arLamW]; simp [hk1, hr]) (fun hr hh0 hb => ?_) hb
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [arLamW] at hb; simp only [ne_eq] at hs; simp only [hk1, hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, not_false_eq_true, and_self, reduceCtorEq] at hb
  have hv : viewOK m h LAM := ⟨hs, UInt64.not_le.mp fun hc => by
    rw [arLamW] at hb; simp only [ne_eq] at hs; simp only [hk1, hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, hc, reduceCtorEq] at hb⟩
  obtain ⟨-, hfw, haw⟩ := view_lam m a hA.1.1 h hh hv hg
  rw [arLamW_miss n m h c d k fu hk1 hr hh0 hv] at hb
  rw [StateT.run_bind, viewBind_run, viewBind_lam m a hA.1.1 h hh hv hg, except_ok_bind]
  refine SimD.exists (Sim.bindD rfl (fun _ _ => rfl)
    (Sim.ofD fun x m₁ e => ih m m₁ a _ c d k fu x hA hfw e) fun x m₁ a₁ hA₁ => ?_) hb
  refine Sim.bindD (K := rlamK₁.rlamK₂ h c _ _ x) rfl (fun _ _ => rfl)
    (Sim.ofD fun y m₂ e => by
    simpa only [succW_toNat c hk1] using ih m₁ m₂ a₁ _ (c + 1) d k fu y hA₁ haw e)
        fun y m₂ a₂ hA₂ => ?_
  have hbind : ∀ t b, internBindE (decE h).tag t b = internE (.lam t b) := by
    intro t b; simp [internBindE, decE_tag h hh, hg, ETag.lam, internE]
  refine Sim.ofD fun r m' hb => atail_ok (internRebuiltBind (decE h)
      (decE x == decE (tfld m LAM (tierW h) (idxW h) 0) && decE y == decE (tfld m LAM (tierW h) (idxW h) 1)) (decE h).tag (decE x) (decE y))
      _ a₂ h c r m' hh (fun r₃ m₃ hr₃ => by
    unfold internRebuiltBind
    rw [hbind]
    refine rb_ok _ _ _ _ m₂ a₂ hA₂ h r₃ m₃ (fun ⟨e1, e2⟩ => by simp [e1, e2]) (fun hn hI => ?_) hr₃
    obtain ⟨hx, hy⟩ := mkLamW_lt m₂ x y r₃ m₃ hI
    refine ⟨?_, mkLam_okA m₂ a₂ hA₂ x y r₃ m₃ hI⟩
    rcases Decidable.em (decE x = decE (tfld m LAM (tierW h) (idxW h) 0)) with e1 | e1
    · have e2 : decE y ≠ decE (tfld m LAM (tierW h) (idxW h) 1) :=
        fun e2 => hn ⟨decE_inj _ _ hx hfw e1, decE_inj _ _ hy haw e2⟩
      simp [e1, e2]
    · simp [e1]) hb

theorem rforallArm_ok (hg : h >>> 28 = 6) :
    RArmRef (n + 1) arForallW (absRangeGoArmBind d.toNat k.toNat fu.toNat (decE h) c.toNat) m m' a h c d k fu r := by
  intro hb
  have hk1 : ¬ c + 1 = 0 := fun hk1 => by rw [arForallW] at hb; simp [hk1] at hb
  rw [absRangeGoArmBind]
  refine aprobe_ok _ _ m m' a hA h c r hh (arForallW_hit n m h c d k fu hk1)
    (fun hr => by rw [arForallW]; simp [hk1, hr]) (fun hr hh0 hb => ?_) hb
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [arForallW] at hb; simp only [ne_eq] at hs; simp only [hk1, hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, not_false_eq_true, and_self, reduceCtorEq] at hb
  have hv : viewOK m h FORALL := ⟨hs, UInt64.not_le.mp fun hc => by
    rw [arForallW] at hb; simp only [ne_eq] at hs; simp only [hk1, hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, hc, reduceCtorEq] at hb⟩
  obtain ⟨-, hfw, haw⟩ := view_forall m a hA.1.1 h hh hv hg
  rw [arForallW_miss n m h c d k fu hk1 hr hh0 hv] at hb
  rw [StateT.run_bind, viewBind_run, viewBind_forall m a hA.1.1 h hh hv hg, except_ok_bind]
  refine SimD.exists (Sim.bindD rfl (fun _ _ => rfl)
    (Sim.ofD fun x m₁ e => ih m m₁ a _ c d k fu x hA hfw e) fun x m₁ a₁ hA₁ => ?_) hb
  refine Sim.bindD (K := rfaK₁.rfaK₂ h c _ _ x) rfl (fun _ _ => rfl)
    (Sim.ofD fun y m₂ e => by
    simpa only [succW_toNat c hk1] using ih m₁ m₂ a₁ _ (c + 1) d k fu y hA₁ haw e)
        fun y m₂ a₂ hA₂ => ?_
  have hbind : ∀ t b, internBindE (decE h).tag t b = internE (.forallE t b) := by
    intro t b; simp [internBindE, decE_tag h hh, hg, ETag.lam, internE]
  refine Sim.ofD fun r m' hb => atail_ok (internRebuiltBind (decE h)
      (decE x == decE (tfld m FORALL (tierW h) (idxW h) 0) && decE y == decE (tfld m FORALL (tierW h) (idxW h) 1)) (decE h).tag (decE x) (decE y))
      _ a₂ h c r m' hh (fun r₃ m₃ hr₃ => by
    unfold internRebuiltBind
    rw [hbind]
    refine rb_ok _ _ _ _ m₂ a₂ hA₂ h r₃ m₃ (fun ⟨e1, e2⟩ => by simp [e1, e2]) (fun hn hI => ?_) hr₃
    obtain ⟨hx, hy⟩ := mkForallW_lt m₂ x y r₃ m₃ hI
    refine ⟨?_, mkForall_okA m₂ a₂ hA₂ x y r₃ m₃ hI⟩
    rcases Decidable.em (decE x = decE (tfld m FORALL (tierW h) (idxW h) 0)) with e1 | e1
    · have e2 : decE y ≠ decE (tfld m FORALL (tierW h) (idxW h) 1) :=
        fun e2 => hn ⟨decE_inj _ _ hx hfw e1, decE_inj _ _ hy haw e2⟩
      simp [e1, e2]
    · simp [e1]) hb

theorem rletArm_ok (hg : h >>> 28 = 7) :
    RArmRef (n + 1) arLetW (absRangeGoArmLet d.toNat k.toNat fu.toNat (decE h) c.toNat) m m' a h c d k fu r := by
  intro hb
  have hk1 : ¬ c + 1 = 0 := fun hk1 => by rw [arLetW] at hb; simp [hk1] at hb
  rw [absRangeGoArmLet]
  refine aprobe_ok _ _ m m' a hA h c r hh (arLetW_hit n m h c d k fu hk1)
    (fun hr => by rw [arLetW]; simp [hk1, hr]) (fun hr hh0 hb => ?_) hb
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [arLetW] at hb; simp only [ne_eq] at hs; simp only [hk1, hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, not_false_eq_true, and_self, reduceCtorEq] at hb
  have hv : viewOK m h LET := ⟨hs, UInt64.not_le.mp fun hc => by
    rw [arLetW] at hb; simp only [ne_eq] at hs; simp only [hk1, hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, hc, reduceCtorEq] at hb⟩
  obtain ⟨-, htw, hvw, hbw⟩ := view_let m a hA.1.1 h hh hv hg
  rw [arLetW_miss n m h c d k fu hk1 hr hh0 hv] at hb
  rw [StateT.run_bind, viewLet_run, viewLet_ok m a hA.1.1 h hh hv, except_ok_bind]
  refine SimD.exists (Sim.bindD rfl (fun _ _ => rfl)
    (Sim.ofD fun x m₁ e => ih m m₁ a _ c d k fu x hA htw e) fun x m₁ a₁ hA₁ => ?_) hb
  refine Sim.bindD (K := rleK₁.rleK₂ n h c d k fu _ _ _ x) rfl (fun _ _ => rfl)
    (Sim.ofD fun y m₂ e => ih m₁ m₂ a₁ _ c d k fu y hA₁ hvw e) fun y m₂ a₂ hA₂ => ?_
  refine Sim.bindD (K := rleK₁.rleK₃ h c _ _ _ x y) rfl (fun _ _ => rfl)
    (Sim.ofD fun z m₃ e => by
    simpa only [succW_toNat c hk1] using ih m₂ m₃ a₂ _ (c + 1) d k fu z hA₂ hbw e)
        fun z m₃ a₃ hA₃ => ?_
  refine Sim.ofD fun r m' hb => atail_ok (internRebuiltLetE (decE h)
      (decE x == decE (tfld m LET (tierW h) (idxW h) 0) && decE y == decE (tfld m LET (tierW h) (idxW h) 1) && decE z == decE (tfld m LET (tierW h) (idxW h) 2))
      (decE x) (decE y) (decE z)) _ a₃ h c r m' hh (fun r₄ m₄ hr₄ => by
    unfold internRebuiltLetE internLetEE
    refine rb_ok _ _ _ _ m₃ a₃ hA₃ h r₄ m₄ (fun ⟨e1, e2, e3⟩ => by simp [e1, e2, e3])
      (fun hn hI => ?_) hr₄
    obtain ⟨hx, hy, hz⟩ := mkLetW_lt m₃ x y z r₄ m₄ hI
    refine ⟨?_, mkLet_okA m₃ a₃ hA₃ x y z r₄ m₄ hI⟩
    rcases Decidable.em (decE x = decE (tfld m LET (tierW h) (idxW h) 0)) with e1 | e1
    · rcases Decidable.em (decE y = decE (tfld m LET (tierW h) (idxW h) 1))
        with e2 | e2
      · have e3 : decE z ≠ decE (tfld m LET (tierW h) (idxW h) 2) :=
          fun e3 => hn ⟨decE_inj _ _ hx htw e1, decE_inj _ _ hy hvw e2, decE_inj _ _ hz hbw e3⟩
        simp [e1, e2, e3]
      · simp [e1, e2]
    · simp [e1]) hb

theorem rprojArm_ok (hg : h >>> 28 = 9) :
    RArmRef (n + 1) arProjW (absRangeGoArmProj d.toNat k.toNat fu.toNat (decE h) c.toNat) m m' a h c d k fu r := by
  intro hb
  rw [absRangeGoArmProj]
  refine aprobe_ok _ _ m m' a hA h c r hh (arProjW_hit n m h c d k fu)
    (fun hr => by rw [arProjW]; simp [hr]) (fun hr hh0 hb => ?_) hb
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [arProjW] at hb; simp only [ne_eq] at hs; simp only [hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, not_false_eq_true, and_self, reduceCtorEq] at hb
  have hv : viewOK m h PROJ := ⟨hs, UInt64.not_le.mp fun hc => by
    rw [arProjW] at hb; simp only [ne_eq] at hs; simp only [hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, hc, reduceCtorEq] at hb⟩
  obtain ⟨-, -, hew⟩ := view_proj m a hA.1.1 h hh hv hg
  rw [arProjW_miss n m h c d k fu hr hh0 hv] at hb
  rw [StateT.run_bind, viewProj_run, viewProj_ok m a hA.1.1 h hh hv, except_ok_bind]
  refine SimD.exists (Sim.bindD rfl (fun _ _ => rfl)
    (Sim.ofD fun x m₁ e => ih m m₁ a _ c d k fu x hA hew e) fun x m₁ a₁ hA₁ => ?_) hb
  refine Sim.ofD fun r m' hb => atail_ok (internRebuiltProj (decE h) (decE x == decE (tfld m PROJ (tierW h) (idxW h) 2))
      (decI (tfld m PROJ (tierW h) (idxW h) 0)) (tfld m PROJ (tierW h) (idxW h) 1).toNat (decE x)) _ a₁ h c r m' hh (fun r₃ m₃ hr₃ => by
    unfold internRebuiltProj internProjE
    refine rb_ok _ _ _ _ m₁ a₁ hA₁ h r₃ m₃ (fun e1 => by simp [e1]) (fun hn hI => ?_) hr₃
    have hx := mkProjW_lt m₁ _ _ x r₃ m₃ hI
    refine ⟨?_, mkProj_okA m₁ a₁ hA₁ _ _ x r₃ m₃ hI⟩
    have e1 : decE x ≠ decE (tfld m PROJ (tierW h) (idxW h) 2) :=
      fun e1 => hn (decE_inj _ _ hx hew e1)
    simp [e1]) hb

end arms

theorem rarmOK_succ (n : Nat) (ih : RGoOK n) : RArmOK (n + 1) := by
  intro m m' a h c d k fu r hA hh
  exact ⟨rappArm_ok n ih m m' a hA h c d k fu r hh, rlamArm_ok n ih m m' a hA h c d k fu r hh,
    rforallArm_ok n ih m m' a hA h c d k fu r hh, rletArm_ok n ih m m' a hA h c d k fu r hh,
    rprojArm_ok n ih m m' a hA h c d k fu r hh⟩

/-- **The model of `ar_go` refines `abstractRangeGo`** at every fuel. -/
theorem arOK (n : Nat) : RGoOK n ∧ RNodeOK n ∧ RArmOK n := by
  induction n with
  | zero =>
    refine ⟨fun _ _ _ _ _ _ _ _ _ _ _ hb => by simp [arW] at hb,
      fun _ _ _ _ _ _ _ _ _ _ _ hb => by simp [arNodeW] at hb,
      fun _ _ _ _ _ _ _ _ _ _ _ => ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    intro _ hb <;> simp [arAppW, arLamW, arForallW, arLetW, arProjW] at hb
  | succ n ih => exact ⟨rgoOK_succ n ih.2.1, rnodeOK_succ n ih.2.2, rarmOK_succ n ih.1⟩


/-! ## The entry `ar_entry` refines `abstractRangeFast` -/

theorem arFast_run (F : Nat) (e : EIdx) (d k c : Nat) (hk : k ≠ 0) (a : AState) :
    (abstractRangeFast F e d k c).run a =
      ((abstractRangeGo d k F e c).run (withAC a ∅) >>= fun p => .ok (p.1, withAC p.2 ∅)) := by
  simp only [abstractRangeFast, hk, ↓reduceIte, StateT.run_bind, abs1Clear_run, except_ok_bind]
  cases (abstractRangeGo d k F e c).run (withAC a ∅) <;> rfl

theorem arEntryW_correct (n : Nat) (m m' : Mem) (a : AState) (hA : ArenaA m a)
    (e d k c r : Word) (he : e.toNat < 2 ^ 32) (hb : arEntryW n m e d k c = some (r, m')) :
    ∃ a', (abstractRangeFast coreWalkFuel (decE e) d.toNat k.toNat c.toNat).run a = .ok (decE r, a') ∧
      ArenaA m' a' ∧ r.toNat < 2 ^ 32 := by
  simp only [arEntryW] at hb
  by_cases hk : k = 0
  · simp only [hk, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact ⟨a, by simp [abstractRangeFast, hk, decE_and32]; rfl, hA, and32_lt e⟩
  have hk' : k.toNat ≠ 0 := fun e => hk (UInt64.toNat_inj.mp e)
  simp only [hk, ↓reduceIte] at hb
  have h0 : ¬ rdW (m.arr64 CTL) 48 + 2 = 0 := fun h0 => by simp [h0] at hb
  simp only [h0, ↓reduceIte] at hb
  have hA₀ := ArenaA.amemo_clear m a hA h0
  cases hw : arW n (mclearG abSch m) e c d k 4000000000 with
  | none => simp [hw, aclrK] at hb
  | some p =>
    obtain ⟨r₁, m₁⟩ := p
    have h1 : ¬ rdW (m₁.arr64 CTL) 48 + 2 = 0 := fun h1 => by simp [hw, aclrK, h1] at hb
    simp only [hw, aclrK, h1, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    obtain ⟨a₁, ha₁, hA₁⟩ := (arOK n).1 _ _ _ e c d k 4000000000 r₁ hA₀ he hw
    rw [coreWalkFuel_toNat] at ha₁
    exact ⟨_, by rw [arFast_run _ _ _ _ _ hk', ha₁, decE_and32]; rfl,
      ArenaA.amemo_clear m₁ a₁ hA₁ h1, and32_lt r₁⟩

/-- **`ar_entry(e, d, k, c)` refines the arena's `abstractRangeFast coreWalkFuel` under `ArenaA`**,
at every L fuel (the walk's counter starts at `coreWalkFuel`). -/
@[refines ConRon.Arena.abstractRangeFast]
theorem arEntry_refines (p : Prog) (hp : ArProg p) (hpe : p.lookup "ar_entry" = some arEntry)
    (n : Nat) (s₀ : St) (a₀ : AState) (hA : ArenaA s₀.mem a₀) (e d k c : Word)
    (he : e.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "ar_entry" [e, d, k, c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (abstractRangeFast coreWalkFuel (decE e) d.toNat k.toNat c.toNat) a₀ ∧
      ArenaA s'.mem (AM.st (abstractRangeFast coreWalkFuel (decE e) d.toNat k.toNat c.toNat) a₀) ∧
      AM.res (abstractRangeFast coreWalkFuel (decE e) d.toNat k.toNat c.toNat) a₀ = decE (r.headD 0) ∧
      (r.headD 0).toNat < 2 ^ 32; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun (arEntry_spec p hp hpe n s₀ e d k c)
  subst hs
  obtain ⟨a', ha', hA', hlt⟩ := arEntryW_correct n _ _ a₀ hA e d k c _ he hI
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ ha'
  exact ⟨hloc, hok, hst ▸ hA', hres, hlt⟩

end L.Arena
