import ConAgua.Arena.FVarRange
import ConAgua.Arena.View
import ConRon.Arena.ExprOps
import ConRon.Arena.Core
import ConAgua.Arena.SimLib
import ConAgua.Census.Attr

/-!
# `fr_go` refines the arena's `fvarRangeGo`

Exactly, at the twin fuel `c.toNat` of the walk's counter word `c`, for any L fuel.

`WalkRefine.lean`'s shape exactly (`FVarRange.lean` has the L code, its model `frW`/`frNodeW` and
the `vcgen` specs), with the `bvar`/`fvar` arms swapped and no truncation on a binder's/`letE`'s
last child (con-ron's `expr_ops.rs`; `FVarRange.lean`'s module doc).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

/-! ## The memo operations under `ArenaR` -/

/-- The arena state after `fvarBSet k r`. -/
def withFC (a : AState) (mp : Std.HashMap EIdx Nat) : AState :=
  { a with memos := { a.memos with fvarBC := mp } }

theorem fvarBGet_run (k : EIdx) (a : AState) : (fvarBGet k).run a = .ok (a.memos.fvarBC[k]?, a) := rfl

theorem fvarBClear_run (a : AState) : fvarBClear.run a = .ok ((), withFC a ∅) := rfl

/-- **`fm_put` (via `fr_set`) is `fvarBSet`.** -/
theorem ArenaR.fmemo_set (m m' : Mem) (a : AState) (hR : ArenaR m a) (k v : Word)
    (hk : k.toNat < 2 ^ 32) (hs : msetG frSch m k 0 v = some m') :
    ArenaR m' (withFC a (a.memos.fvarBC.insert (decE k) v.toNat)) := by
  have hf := msetG_frame frSch frSch_wf m m' k 0 v hs
  exact hR.with_memos hf (by apart) (by apart) (by
    memos_build hR.memos, hf with
      exact memoRG_set frSch frSch_wf bmKey _ m _ hR.memos.fvar k 0 v ⟨hk, rfl⟩ m' hs)

/-- **`fm_clear` is `fvarBClear`.** -/
theorem ArenaR.fmemo_clear (m : Mem) (a : AState) (hR : ArenaR m a)
    (h0 : rdW (m.arr64 CTL) 46 + 2 ≠ 0) : ArenaR (mclearG frSch m) (withFC a ∅) := by
  have hf := mclearG_frame frSch m
  exact hR.with_memos hf (by apart) (by apart) (by
    memos_build hR.memos, hf with exact memoRG_clear frSch frSch_wf bmKey _ m _ hR.memos.fvar h0)

/-! ## The arena walk, unfolded -/

/-- The arms of `fvarRangeGo` on a view (its inner `match`), named. -/
def frArm (F : Nat) : ENodeView → AM Nat
  | .fvar idx _ => pure (idx + 1)
  | .bvar _ | .sort _ | .const _ _ | .lit _ => pure 0
  | .app f a => fvarRangeArmApp F f a
  | .lam ty body | .forallE ty body => fvarRangeArmBind F ty body
  | .letE ty val body => fvarRangeArmLet F ty val body
  | .proj _ _ sub => fvarRangeGo F sub

/-- The node half of `fvarRangeGo`: view, then the arm. -/
def frNodeA (F : Nat) (h : EIdx) : AM Nat := do
  let v ← view h
  frArm F v

theorem fvarRangeGo_succ' (F : Nat) (h : EIdx) :
    fvarRangeGo (F + 1) h = (do
      match ← fvarBGet h with
      | some r => pure r
      | none => do
        let r ← frNodeA F h
        fvarBSet h r
        pure r) := by
  rw [fvarRangeGo_succ]
  simp only [frNodeA]
  congr

theorem frNodeA_run (F : Nat) (h : EIdx) (a : AState) (v : ENodeView)
    (hv : a.store.view h = some v) : (frNodeA F h).run a = (frArm F v).run a := by
  simp only [frNodeA, StateT.run_bind, view_run h a v hv]; rfl

/-! ## The refinement, by induction on the fuel

The walk's counter `c` is the twin's `fuel` exactly (`c.toNat`): at `c = 0` the L code aborts (the
twin throws), else `c.toNat = (c - 1).toNat + 1` and the twin's `fuel + 1` clause runs its arms at
`(c - 1).toNat`, where `fr_node` runs. The induction is on L's own fuel `n`. -/

/-- A nonzero counter is the successor of its decrement (the twin's `fuel + 1` clause). -/
theorem ctrW_toNat (c : Word) (hc : c ≠ 0) : c.toNat = (c - 1).toNat + 1 := by
  have : c.toNat ≠ 0 := fun h => hc (UInt64.toNat_inj.mp (by simpa using h))
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega

/-- The walks' entries start their counter at the literal `4000000000`: the twin's
`coreWalkFuel` (`ConRon/Arena/Core.lean`), the fuel the core calls every walk at. -/
theorem coreWalkFuel_toNat : (4000000000 : Word).toNat = coreWalkFuel := rfl

/-- What `fr_go`'s model at L fuel `n` and counter `c` says about the arena walk at `c.toNat`. -/
def FrGoOK (n : Nat) : Prop :=
  ∀ (F : Nat) (m m' : Mem) (a : AState) (h c r : Word), (c.toNat ≤ F ∨ n ≤ F) → ArenaR m a →
    h.toNat < 2 ^ 32 → frW n m h c = some (r, m') →
    ∃ a', (fvarRangeGo F (decE h)).run a = .ok (r.toNat, a') ∧ ArenaR m' a'

/-- The same for `fr_node`'s model and the arena's view-and-arm. -/
def FrNodeOK (n : Nat) : Prop :=
  ∀ (F : Nat) (m m' : Mem) (a : AState) (h c r : Word), (c.toNat ≤ F ∨ n ≤ F) → ArenaR m a →
    h.toNat < 2 ^ 32 → frNodeW n m h c = some (r, m') →
    ∃ a', (frNodeA F (decE h)).run a = .ok (r.toNat, a') ∧ ArenaR m' a'

theorem frGoOK_succ (n : Nat) (ih : FrNodeOK n) : FrGoOK (n + 1) := by
  intro F m m' a h c r hF hR hh hb
  by_cases hc : c = 0
  · rw [frW] at hb; simp [hc] at hb
  have hc1 := ctrW_toNat c hc
  obtain ⟨G, rfl⟩ : ∃ G, F = G + 1 := ⟨F - 1, by omega⟩
  rw [fvarRangeGo_succ', StateT.run_bind, fvarBGet_run]
  by_cases hr : mfindG frSch m h 0 = []
  · rw [frW] at hb; simp [hc, hr] at hb
  by_cases hh0 : (mfindG frSch m h 0).headD 0 ≠ 0
  · rw [frW_hit n m h c hc hr hh0] at hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    rw [show a.memos.fvarBC[decE h]? = _ from memoRG_hit frSch bmKey _ m _ hR.memos.fvar h 0 hr hh0 ⟨hh, rfl⟩]
    exact ⟨a, rfl, hR⟩
  · simp only [ne_eq, Decidable.not_not] at hh0
    rw [frW_miss n m h c hc hr hh0] at hb
    rw [show a.memos.fvarBC[decE h]? = none from
      memoRG_miss frSch bmKey _ m _ hR.memos.fvar h 0 ⟨hh, rfl⟩ hr hh0]
    cases hn : frNodeW n m h (c - 1) with
    | none => simp [frK, hn] at hb
    | some p =>
      obtain ⟨r₁, m₁⟩ := p
      simp only [hn, frK, frSet_eq] at hb
      cases hs : msetG frSch m₁ h 0 r₁ with
      | none => simp [hs, frSetK] at hb
      | some m₂ =>
        simp only [hs, frSetK, Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        obtain ⟨a₁, ha₁, hR₁⟩ := ih G m m₁ a h (c - 1) r₁ (by omega) hR hh hn
        refine ⟨_, ?_, ArenaR.fmemo_set m₁ m₂ a₁ hR₁ h r₁ hh hs⟩
        change StateT.run (do let r ← frNodeA G (decE h); fvarBSet (decE h) r; pure r) a = _
        simp only [StateT.run_bind, ha₁]
        rfl

/-- The `app` arm: two children, `max x y`. -/
theorem frAppArm_ok (n : Nat) (ih : FrGoOK n) (F : Nat) (m m' : Mem) (a : AState)
    (hR : ArenaR m a) (c fw aw r : Word) (hf : fw.toNat < 2 ^ 32) (ha : aw.toNat < 2 ^ 32)
    (hF : c.toNat ≤ F ∨ n ≤ F)
    (hb : frAppK₁ n c aw (frW n m fw c) = some (r, m')) :
    ∃ a', (fvarRangeArmApp F (decE fw) (decE aw)).run a = .ok (r.toNat, a') ∧ ArenaR m' a' := by
  unfold fvarRangeArmApp
  refine SimD.exists (Sim.bindD rfl (fun _ _ => rfl)
    (Sim.ofD fun x m₁ e => ih F m m₁ a _ c x hF hR hf e) fun x m₁ a₁ hR₁ => ?_) hb
  refine Sim.bindD (K := frAppK₁.frAppK₂ x) rfl (fun _ _ => rfl)
    (Sim.ofD fun y m₂ e => ih F m₁ m₂ a₁ _ c y hF hR₁ ha e) fun y m₂ a₂ hR₂ => ?_
  exact Sim.ret ⟨(maxW_toNat x y).symm, hR₂⟩

/-- The binder arm (`lam`, `forallE`): two children, `max x y` (no truncation). -/
theorem frBindArm_ok (n : Nat) (ih : FrGoOK n) (F : Nat) (m m' : Mem) (a : AState)
    (hR : ArenaR m a) (c tw bw r : Word) (ht : tw.toNat < 2 ^ 32) (hb' : bw.toNat < 2 ^ 32)
    (hF : c.toNat ≤ F ∨ n ≤ F)
    (hb : frBindK₁ n c bw (frW n m tw c) = some (r, m')) :
    ∃ a', (fvarRangeArmBind F (decE tw) (decE bw)).run a = .ok (r.toNat, a') ∧ ArenaR m' a' := by
  unfold fvarRangeArmBind
  refine SimD.exists (Sim.bindD rfl (fun _ _ => rfl)
    (Sim.ofD fun x m₁ e => ih F m m₁ a _ c x hF hR ht e) fun x m₁ a₁ hR₁ => ?_) hb
  refine Sim.bindD (K := frBindK₁.frBindK₂ x) rfl (fun _ _ => rfl)
    (Sim.ofD fun y m₂ e => ih F m₁ m₂ a₁ _ c y hF hR₁ hb' e) fun y m₂ a₂ hR₂ => ?_
  exact Sim.ret ⟨(maxW_toNat x y).symm, hR₂⟩

/-- The `letE` arm: three children, `max (max x y) z` (no truncation). -/
theorem frLetArm_ok (n : Nat) (ih : FrGoOK n) (F : Nat) (m m' : Mem) (a : AState)
    (hR : ArenaR m a) (c tw vw bw r : Word) (ht : tw.toNat < 2 ^ 32) (hv : vw.toNat < 2 ^ 32)
    (hb' : bw.toNat < 2 ^ 32) (hF : c.toNat ≤ F ∨ n ≤ F)
    (hb : frLetK₁ n c vw bw (frW n m tw c) = some (r, m')) :
    ∃ a', (fvarRangeArmLet F (decE tw) (decE vw) (decE bw)).run a = .ok (r.toNat, a') ∧
      ArenaR m' a' := by
  unfold fvarRangeArmLet
  refine SimD.exists (Sim.bindD rfl (fun _ _ => rfl)
    (Sim.ofD fun x m₁ e => ih F m m₁ a _ c x hF hR ht e) fun x m₁ a₁ hR₁ => ?_) hb
  refine Sim.bindD (K := frLetK₁.frLetK₂ n c bw x) rfl (fun _ _ => rfl)
    (Sim.ofD fun y m₂ e => ih F m₁ m₂ a₁ _ c y hF hR₁ hv e) fun y m₂ a₂ hR₂ => ?_
  refine Sim.bindD (K := frLetK₁.frLetK₃ x y) rfl (fun _ _ => rfl)
    (Sim.ofD fun z m₃ e => ih F m₂ m₃ a₂ _ c z hF hR₂ hb' e) fun z m₃ a₃ hR₃ => ?_
  exact Sim.ret ⟨by rw [maxW_toNat, maxW_toNat], hR₃⟩

theorem frNodeOK_succ (n : Nat) (ih : FrGoOK n) : FrNodeOK (n + 1) := by
  intro F m m' a h c r hF hR hh hb
  have hF' : c.toNat ≤ F ∨ n ≤ F := by omega
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [frNodeW] at hb; simp only [ite_eq_left hs, reduceCtorEq] at hb
  have vok : ∀ c, ¬ tcnt m c (tierW h) ≤ idxW h → viewOK m h c :=
    fun c hc => ⟨hs, UInt64.not_le.mp hc⟩
  have zero : ∀ v, a.store.view (decE h) = some v → frArm F v = pure 0 → r = 0 → m' = m →
      ∃ a', (frNodeA F (decE h)).run a = .ok (r.toNat, a') ∧ ArenaR m' a' := by
    intro v hv hx hr hm; subst hr hm
    exact ⟨a, by rw [frNodeA_run F _ a _ hv, hx]; rfl, hR⟩
  by_cases g0 : h >>> 28 = 0
  · by_cases hc : tcnt m BVAR (tierW h) ≤ idxW h
    · rw [frNodeW] at hb; simp [hs, g0, hc] at hb
    rw [frNodeW_bvar n m h c g0 (vok BVAR hc)] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    exact zero _ (view_bvar m a hR h hh (vok BVAR hc) g0) rfl rfl rfl
  by_cases g1 : h >>> 28 = 1
  · by_cases hc : tcnt m FVAR (tierW h) ≤ idxW h
    · rw [frNodeW] at hb; simp [hs, g1, hc] at hb
    by_cases h1 : tfld m FVAR (tierW h) (idxW h) 0 + 1 = 0
    · rw [frNodeW] at hb; simp [hs, g1, hc, h1] at hb
    rw [frNodeW_fvar n m h c (vok FVAR hc) g1 h1] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    obtain ⟨hv, -⟩ := view_fvar_idx m a hR h hh (vok FVAR hc) g1
    refine ⟨a, ?_, hR⟩
    rw [frNodeA_run F _ a _ hv, show frArm F (.fvar _ _) = pure (_ + 1) from rfl,
      succW_toNat _ h1]
    rfl
  by_cases g4 : h >>> 28 = 4
  · by_cases hc : tcnt m APP (tierW h) ≤ idxW h
    · rw [frNodeW] at hb; simp [hs, g4, hc] at hb
    obtain ⟨hv, hf, ha⟩ := view_app m a hR h hh (vok APP hc) g4
    rw [frNodeW_app n m h c (vok APP hc) g4] at hb
    obtain ⟨a', h1, h2⟩ := frAppArm_ok n ih F m m' a hR c _ _ r hf ha hF' hb
    exact ⟨a', (frNodeA_run F _ a _ hv).trans h1, h2⟩
  by_cases g5 : h >>> 28 = 5
  · by_cases hc : tcnt m LAM (tierW h) ≤ idxW h
    · rw [frNodeW] at hb; simp [hs, g5, hc] at hb
    obtain ⟨hv, hf, ha⟩ := view_lam m a hR h hh (vok LAM hc) g5
    rw [frNodeW_lam n m h c (vok LAM hc) g5] at hb
    obtain ⟨a', h1, h2⟩ := frBindArm_ok n ih F m m' a hR c _ _ r hf ha hF' hb
    exact ⟨a', (frNodeA_run F _ a _ hv).trans h1, h2⟩
  by_cases g6 : h >>> 28 = 6
  · by_cases hc : tcnt m FORALL (tierW h) ≤ idxW h
    · rw [frNodeW] at hb; simp [hs, g6, hc] at hb
    obtain ⟨hv, hf, ha⟩ := view_forall m a hR h hh (vok FORALL hc) g6
    rw [frNodeW_forall n m h c (vok FORALL hc) g6] at hb
    obtain ⟨a', h1, h2⟩ := frBindArm_ok n ih F m m' a hR c _ _ r hf ha hF' hb
    exact ⟨a', (frNodeA_run F _ a _ hv).trans h1, h2⟩
  by_cases g7 : h >>> 28 = 7
  · by_cases hc : tcnt m LET (tierW h) ≤ idxW h
    · rw [frNodeW] at hb; simp [hs, g7, hc] at hb
    obtain ⟨hv, ht, hv', hb'⟩ := view_let m a hR h hh (vok LET hc) g7
    rw [frNodeW_let n m h c (vok LET hc) g7] at hb
    obtain ⟨a', h1, h2⟩ := frLetArm_ok n ih F m m' a hR c _ _ _ r ht hv' hb' hF' hb
    exact ⟨a', (frNodeA_run F _ a _ hv).trans h1, h2⟩
  by_cases g9 : h >>> 28 = 9
  · by_cases hc : tcnt m PROJ (tierW h) ≤ idxW h
    · rw [frNodeW] at hb; simp [hs, g9, hc] at hb
    obtain ⟨hv, -, he⟩ := view_proj m a hR h hh (vok PROJ hc) g9
    rw [frNodeW_proj n m h c (vok PROJ hc) g9] at hb
    obtain ⟨a', h1, h2⟩ := ih F m m' a _ c r hF' hR he hb
    exact ⟨a', (frNodeA_run F _ a _ hv).trans h1, h2⟩
  by_cases g2 : h >>> 28 = 2
  · by_cases hc : tcnt m SORT (tierW h) ≤ idxW h
    · rw [frNodeW] at hb; simp [hs, g2, hc] at hb
    rw [frNodeW_sort n m h c g2 (vok SORT hc)] at hb
    obtain ⟨_, hv⟩ := view_sort m a hR h hh (vok SORT hc) g2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    exact zero _ hv rfl rfl rfl
  by_cases g3 : h >>> 28 = 3
  · by_cases hc : tcnt m CONST (tierW h) ≤ idxW h
    · rw [frNodeW] at hb; simp [hs, g3, hc] at hb
    rw [frNodeW_const n m h c g3 (vok CONST hc)] at hb
    obtain ⟨_, _, hv⟩ := view_const m a hR h hh (vok CONST hc) g3
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    exact zero _ hv rfl rfl rfl
  by_cases g8 : h >>> 28 = 8
  · by_cases hc : tcnt m LIT (tierW h) ≤ idxW h
    · rw [frNodeW] at hb; simp [hs, g8, hc] at hb
    rw [frNodeW_lit n m h c g8 (vok LIT hc)] at hb
    obtain ⟨_, hv⟩ := view_lit m a hR h hh (vok LIT hc) g8
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    exact zero _ hv rfl rfl rfl
  rw [frNodeW] at hb; simp [hs, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9] at hb

/-- **The model of `fr_go` refines `fvarRangeGo`** at every fuel. -/
theorem frGoOK (n : Nat) : FrGoOK n ∧ FrNodeOK n := by
  induction n with
  | zero =>
    exact ⟨fun _ _ _ _ _ _ _ _ _ _ hb => by simp [frW] at hb,
      fun _ _ _ _ _ _ _ _ _ _ hb => by simp [frNodeW] at hb⟩
  | succ n ih => exact ⟨frGoOK_succ n ih.2, frNodeOK_succ n ih.1⟩

/-! ## The entry `fr_memo` refines `fvarRangeMemo` -/

theorem fvarRangeMemo_run (F : Nat) (e : EIdx) (a : AState) :
    (fvarRangeMemo F e).run a =
      ((fvarRangeGo F e).run (withFC a ∅) >>= fun p => .ok (p.1, withFC p.2 ∅)) := by
  simp only [fvarRangeMemo, StateT.run_bind, fvarBClear_run, except_ok_bind]
  cases (fvarRangeGo F e).run (withFC a ∅) <;> rfl

/-- **The model of `fr_memo` refines `fvarRangeMemo` at any twin fuel `F`** with `c.toNat ≤ F` or the
L fuel `n ≤ F` (the walk's counter or its L fuel bounds the twin's). -/
theorem frMemoW_correctF (n F : Nat) (m m' : Mem) (a : AState) (hR : ArenaR m a)
    (h c r : Word) (hh : h.toNat < 2 ^ 32) (hF : c.toNat ≤ F ∨ n ≤ F)
    (hb : frMemoW n m h c = some (r, m')) :
    ∃ a', (fvarRangeMemo F (decE h)).run a = .ok (r.toNat, a') ∧ ArenaR m' a' := by
  simp only [frMemoW] at hb
  by_cases h0 : rdW (m.arr64 CTL) 46 + 2 = 0
  · simp [h0] at hb
  simp only [h0, ↓reduceIte] at hb
  have hR₀ := ArenaR.fmemo_clear m a hR h0
  cases hw : frW n (mclearG frSch m) h c with
  | none => simp [hw, frClrK] at hb
  | some p =>
    obtain ⟨r₁, m₁⟩ := p
    by_cases h1 : rdW (m₁.arr64 CTL) 46 + 2 = 0
    · simp [hw, frClrK, h1] at hb
    simp only [hw, frClrK, h1, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    obtain ⟨a₁, ha₁, hR₁⟩ := (frGoOK n).1 F _ _ _ h c r₁ hF hR₀ hh hw
    exact ⟨_, by rw [fvarRangeMemo_run, ha₁]; rfl, ArenaR.fmemo_clear m₁ a₁ hR₁ h1⟩

/-- **The model of `fr_memo` refines `fvarRangeMemo`** at the counter's value `c.toNat`. -/
theorem frMemoW_correct (n : Nat) (m m' : Mem) (a : AState) (hR : ArenaR m a)
    (h c r : Word) (hh : h.toNat < 2 ^ 32) (hb : frMemoW n m h c = some (r, m')) :
    ∃ a', (fvarRangeMemo c.toNat (decE h)).run a = .ok (r.toNat, a') ∧ ArenaR m' a' := by
  exact frMemoW_correctF n _ m m' a hR h c r hh (.inl (Nat.le_refl _)) hb

/-- **`fr_memo` refines the arena's `fvarRangeMemo` under `ArenaR`**: if the L walk returns, the
arena walk at the counter's fuel `c.toNat` succeeds with the same range, in a related state. -/
@[refines ConRon.Arena.fvarRangeMemo]
theorem frMemo_refines (p : Prog) (hpf : p.lookup "fm_find" = some (memoFindG frSch))
    (hps : p.lookup "fm_put" = some (memoPutG frSch)) (hpc : p.lookup "fm_clear" = some (memoClearG frSch))
    (hp : p.lookup "fr_go" = some frGo) (hpn : p.lookup "fr_node" = some frNode)
    (hpm : p.lookup "fr_memo" = some frMemo) (n : Nat) (s₀ : St) (a₀ : AState)
    (hR : ArenaR s₀.mem a₀) (h c : Word) (hh : h.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "fr_memo" [h, c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (fvarRangeMemo c.toNat (decE h)) a₀ ∧
      ArenaR s'.mem (AM.st (fvarRangeMemo c.toNat (decE h)) a₀) ∧
      AM.res (fvarRangeMemo c.toNat (decE h)) a₀ = (r.headD 0).toNat; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (frMemo_spec p hpf hps hp hpn hpc hpm n s₀ h c)
  subst hs
  obtain ⟨a', ha', hR'⟩ := frMemoW_correct n _ _ a₀ hR h c _ hh hI
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ ha'
  exact ⟨hloc, hok, hst ▸ hR', hres⟩

end L.Arena
