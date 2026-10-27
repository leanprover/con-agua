import ConAgua.Arena.Walk
import ConAgua.Arena.FVarRangeRefine
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# `bb_go` refines the arena's `bvarBoundGo`

The arena side of the walk (`Walk.lean` has the L code, its model `bbW`/`bbNodeW` and the
`vcgen` specs). Pure Lean, by induction on the fuel: if the model returns `r` and `m'` from `m`
related to `a` by `ArenaR`, then `bvarBoundGo c.toNat (decE h)` from `a` returns `r.toNat` in a
state related to `m'`, at the twin fuel `c.toNat` of the walk's counter word `c` exactly
whatever the L fuel.

* **Decoding a handle word** (`decE_tag`, `decE_idx`, `decE_pers`): the tag is `h >> 28`, the
  index `h & (2^27 - 1)`, persistence the tier bit, for `h < 2^32`.
* **The view** (`view_*`): under `ArenaR` and the L code's checks (`viewOK`), the arena's
  `view (decE h)` is the node the L records hold, children decoded from their words.
* **The memo** (`ArenaR.memo_set`, `ArenaR.memo_clear`): `memo_set` is `bvarBSet`, `memo_clear`
  is `bvarBClear`, everything else framed.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

/-! ## The memo operations under `ArenaR` -/

/-- The arena state after `bvarBSet k r`. -/
def withBC (a : AState) (mp : Std.HashMap EIdx Nat) : AState :=
  { a with memos := { a.memos with bvarBC := mp } }

theorem bvarBGet_run (k : EIdx) (a : AState) : (bvarBGet k).run a = .ok (a.memos.bvarBC[k]?, a) := rfl

theorem bvarBClear_run (a : AState) : bvarBClear.run a = .ok ((), withBC a ∅) := rfl

/-- **`memo_set` is `bvarBSet`.** -/
theorem ArenaR.memo_set (m m' : Mem) (a : AState) (hR : ArenaR m a) (k v : Word)
    (hk : k.toNat < 2 ^ 32) (hs : msetG bmSch m k 0 v = some m') :
    ArenaR m' (withBC a (a.memos.bvarBC.insert (decE k) v.toNat)) := by
  have hf := msetG_frame bmSch bmSch_wf m m' k 0 v hs
  exact hR.with_memos hf (by apart) (by apart) (by
    memos_build hR.memos, hf with
      exact memoRG_set bmSch bmSch_wf bmKey _ m _ hR.memos.bvar k 0 v ⟨hk, rfl⟩ m' hs)

/-- **`memo_clear` is `bvarBClear`.** -/
theorem ArenaR.memo_clear (m : Mem) (a : AState) (hR : ArenaR m a)
    (h0 : rdW (m.arr64 CTL) 24 + 2 ≠ 0) : ArenaR (mclearG bmSch m) (withBC a ∅) := by
  have hf := mclearG_frame bmSch m
  exact hR.with_memos hf (by apart) (by apart) (by
    memos_build hR.memos, hf with exact memoRG_clear bmSch bmSch_wf bmKey _ m _ hR.memos.bvar h0)

/-! ## The arena walk, unfolded -/

/-- The arms of `bvarBoundGo` on a view (its inner `match`), named. -/
def bbArm (F : Nat) : ENodeView → AM Nat
  | .bvar i => pure (i + 1)
  | .fvar _ _ | .sort _ | .const _ _ | .lit _ => pure 0
  | .app f a => bvarBoundArmApp F f a
  | .lam ty body | .forallE ty body => bvarBoundArmBind F ty body
  | .letE ty val body => bvarBoundArmLet F ty val body
  | .proj _ _ sub => bvarBoundGo F sub

/-- The node half of `bvarBoundGo`: view, then the arm. -/
def bbNodeA (F : Nat) (h : EIdx) : AM Nat := do
  let v ← view h
  bbArm F v

theorem bvarBoundGo_succ' (F : Nat) (h : EIdx) :
    bvarBoundGo (F + 1) h = (do
      match ← bvarBGet h with
      | some r => pure r
      | none => do
        let r ← bbNodeA F h
        bvarBSet h r
        pure r) := by
  rw [bvarBoundGo_succ]
  simp only [bbNodeA]
  congr

theorem bbNodeA_run (F : Nat) (h : EIdx) (a : AState) (v : ENodeView)
    (hv : a.store.view h = some v) : (bbNodeA F h).run a = (bbArm F v).run a := by
  simp only [bbNodeA, StateT.run_bind, view_run h a v hv]; rfl

/-! ## The refinement, by induction on the fuel

The counter `c` is the twin's `fuel` exactly (`c.toNat`; `FVarRangeRefine.lean`'s `ctrW_toNat`):
at `c = 0` the L code aborts where the twin throws. -/

/-- What `bb_go`'s model at L fuel `n` and counter `c` says about the arena walk at `c.toNat`. -/
def GoOK (n : Nat) : Prop :=
  ∀ (F : Nat) (m m' : Mem) (a : AState) (h c r : Word), (c.toNat ≤ F ∨ n ≤ F) → ArenaR m a →
    h.toNat < 2 ^ 32 → bbW n m h c = some (r, m') →
    ∃ a', (bvarBoundGo F (decE h)).run a = .ok (r.toNat, a') ∧ ArenaR m' a'

/-- The same for `bb_node`'s model and the arena's view-and-arm. -/
def NodeOK (n : Nat) : Prop :=
  ∀ (F : Nat) (m m' : Mem) (a : AState) (h c r : Word), (c.toNat ≤ F ∨ n ≤ F) → ArenaR m a →
    h.toNat < 2 ^ 32 → bbNodeW n m h c = some (r, m') →
    ∃ a', (bbNodeA F (decE h)).run a = .ok (r.toNat, a') ∧ ArenaR m' a'

theorem goOK_succ (n : Nat) (ih : NodeOK n) : GoOK (n + 1) := by
  intro F m m' a h c r hF hR hh hb
  have hc : ¬ c = 0 := fun hc => by rw [bbW] at hb; simp [hc] at hb
  have hc1 := ctrW_toNat c hc
  obtain ⟨G, rfl⟩ : ∃ G, F = G + 1 := ⟨F - 1, by omega⟩
  rw [bvarBoundGo_succ', StateT.run_bind, bvarBGet_run]
  have hr : ¬ mfindG bmSch m h 0 = [] := fun hr => by rw [bbW] at hb; simp [hc, hr] at hb
  by_cases hh0 : (mfindG bmSch m h 0).headD 0 ≠ 0
  · rw [bbW_hit n m h c hc hr hh0] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    rw [show a.memos.bvarBC[decE h]? = _ from memoRG_hit bmSch bmKey _ m _ hR.memos.bvar h 0 hr hh0 ⟨hh, rfl⟩]
    exact ⟨a, rfl, hR⟩
  · simp only [ne_eq, Decidable.not_not] at hh0
    rw [bbW_miss n m h c hc hr hh0] at hb
    rw [show a.memos.bvarBC[decE h]? = none from
      memoRG_miss bmSch bmKey _ m _ hR.memos.bvar h 0 ⟨hh, rfl⟩ hr hh0]
    rcases hn : bbNodeW n m h (c - 1) with _ | ⟨r₁, m₁⟩ <;> simp only [hn, bbK, bbSet_eq, reduceCtorEq] at hb
    cases hs : msetG bmSch m₁ h 0 r₁ with
    | none => simp [hs, setK] at hb
    | some m₂ =>
      simp only [hs, setK, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      obtain ⟨a₁, ha₁, hR₁⟩ := ih G m m₁ a h (c - 1) r₁ (by omega) hR hh hn
      refine ⟨_, ?_, ArenaR.memo_set m₁ m₂ a₁ hR₁ h r₁ hh hs⟩
      change StateT.run (do let r ← bbNodeA G (decE h); bvarBSet (decE h) r; pure r) a = _
      simp only [StateT.run_bind, ha₁]
      rfl

/-- The `app` arm: two children, `max x y`. -/
theorem bbAppArm_ok (n : Nat) (ih : GoOK n) (F : Nat) (m m' : Mem) (a : AState)
    (hR : ArenaR m a) (c fw aw r : Word) (hf : fw.toNat < 2 ^ 32) (ha : aw.toNat < 2 ^ 32)
    (hF : c.toNat ≤ F ∨ n ≤ F)
    (hb : bbAppK₁ n c aw (bbW n m fw c) = some (r, m')) :
    ∃ a', (bvarBoundArmApp F (decE fw) (decE aw)).run a = .ok (r.toNat, a') ∧ ArenaR m' a' := by
  cases h1 : bbW n m fw c with
  | none => simp only [h1, bbAppK₁, reduceCtorEq] at hb
  | some p =>
    obtain ⟨x, m₁⟩ := p
    rcases h2 : bbW n m₁ aw c with _ | ⟨y, m₂⟩ <;> simp only [h2, h1, bbAppK₁, bbAppK₁.bbAppK₂, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    obtain ⟨a₁, ha₁, hR₁⟩ := ih F m m₁ a _ c x hF hR hf h1
    obtain ⟨a₂, ha₂, hR₂⟩ := ih F m₁ m₂ a₁ _ c y hF hR₁ ha h2
    refine ⟨a₂, ?_, hR₂⟩
    rw [maxW_toNat]
    simp only [bvarBoundArmApp, StateT.run_bind, ha₁, except_ok_bind, ha₂]
    rfl

/-- The binder arm (`lam`, `forallE`): two children, `max x (y - 1)`. -/
theorem bbBindArm_ok (n : Nat) (ih : GoOK n) (F : Nat) (m m' : Mem) (a : AState)
    (hR : ArenaR m a) (c tw bw r : Word) (ht : tw.toNat < 2 ^ 32) (hb' : bw.toNat < 2 ^ 32)
    (hF : c.toNat ≤ F ∨ n ≤ F)
    (hb : bbBindK₁ n c bw (bbW n m tw c) = some (r, m')) :
    ∃ a', (bvarBoundArmBind F (decE tw) (decE bw)).run a = .ok (r.toNat, a') ∧ ArenaR m' a' := by
  cases h1 : bbW n m tw c with
  | none => simp only [h1, bbBindK₁, reduceCtorEq] at hb
  | some p =>
    obtain ⟨x, m₁⟩ := p
    rcases h2 : bbW n m₁ bw c with _ | ⟨y, m₂⟩ <;> simp only [h2, h1, bbBindK₁, bbBindK₁.bbBindK₂, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    obtain ⟨a₁, ha₁, hR₁⟩ := ih F m m₁ a _ c x hF hR ht h1
    obtain ⟨a₂, ha₂, hR₂⟩ := ih F m₁ m₂ a₁ _ c y hF hR₁ hb' h2
    refine ⟨a₂, ?_, hR₂⟩
    rw [maxW_toNat, predW_toNat]
    simp only [bvarBoundArmBind, StateT.run_bind, ha₁, except_ok_bind, ha₂]
    rfl

/-- The `letE` arm: three children, `max (max x y) (z - 1)`. -/
theorem bbLetArm_ok (n : Nat) (ih : GoOK n) (F : Nat) (m m' : Mem) (a : AState)
    (hR : ArenaR m a) (c tw vw bw r : Word) (ht : tw.toNat < 2 ^ 32) (hv : vw.toNat < 2 ^ 32)
    (hb' : bw.toNat < 2 ^ 32) (hF : c.toNat ≤ F ∨ n ≤ F)
    (hb : bbLetK₁ n c vw bw (bbW n m tw c) = some (r, m')) :
    ∃ a', (bvarBoundArmLet F (decE tw) (decE vw) (decE bw)).run a = .ok (r.toNat, a') ∧
      ArenaR m' a' := by
  cases h1 : bbW n m tw c with
  | none => simp only [h1, bbLetK₁, reduceCtorEq] at hb
  | some p =>
    obtain ⟨x, m₁⟩ := p
    cases h2 : bbW n m₁ vw c with
    | none => simp only [h1, h2, bbLetK₁, bbLetK₁.bbLetK₂, reduceCtorEq] at hb
    | some q =>
      obtain ⟨y, m₂⟩ := q
      cases h3 : bbW n m₂ bw c with
      | none => simp only [h1, h2, h3, bbLetK₁, bbLetK₁.bbLetK₂, bbLetK₁.bbLetK₃, reduceCtorEq] at hb
      | some o =>
        obtain ⟨z, m₃⟩ := o
        simp only [h1, h2, h3, bbLetK₁, bbLetK₁.bbLetK₂, bbLetK₁.bbLetK₃, Option.some.injEq,
          Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        obtain ⟨a₁, ha₁, hR₁⟩ := ih F m m₁ a _ c x hF hR ht h1
        obtain ⟨a₂, ha₂, hR₂⟩ := ih F m₁ m₂ a₁ _ c y hF hR₁ hv h2
        obtain ⟨a₃, ha₃, hR₃⟩ := ih F m₂ m₃ a₂ _ c z hF hR₂ hb' h3
        refine ⟨a₃, ?_, hR₃⟩
        rw [maxW_toNat, maxW_toNat, predW_toNat]
        simp only [bvarBoundArmLet, StateT.run_bind, ha₁, except_ok_bind, ha₂, ha₃]
        rfl

theorem nodeOK_succ (n : Nat) (ih : GoOK n) : NodeOK (n + 1) := by
  intro F m m' a h c r hF hR hh hb
  have hF' : c.toNat ≤ F ∨ n ≤ F := by omega
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [bbNodeW] at hb; simp only [ite_eq_left hs, reduceCtorEq] at hb
  have vok : ∀ c, ¬ tcnt m c (tierW h) ≤ idxW h → viewOK m h c :=
    fun c hc => ⟨hs, UInt64.not_le.mp hc⟩
  have zero : ∀ v, a.store.view (decE h) = some v → bbArm F v = pure 0 → r = 0 → m' = m →
      ∃ a', (bbNodeA F (decE h)).run a = .ok (r.toNat, a') ∧ ArenaR m' a' := by
    intro v hv hx hr hm; subst hr hm
    exact ⟨a, by rw [bbNodeA_run F _ a _ hv, hx]; rfl, hR⟩
  by_cases g0 : h >>> 28 = 0
  · by_cases hc : tcnt m BVAR (tierW h) ≤ idxW h
    · rw [bbNodeW] at hb; simp [hs, g0, hc] at hb
    by_cases h1 : tfld m BVAR (tierW h) (idxW h) 0 + 1 = 0
    · rw [bbNodeW] at hb; simp [hs, g0, hc, h1] at hb
    rw [bbNodeW_bvar n m h c (vok BVAR hc) g0 h1] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    refine ⟨a, ?_, hR⟩
    rw [bbNodeA_run F _ a _ (view_bvar m a hR h hh (vok BVAR hc) g0), succW_toNat _ h1]; rfl
  by_cases g4 : h >>> 28 = 4
  · by_cases hc : tcnt m APP (tierW h) ≤ idxW h
    · rw [bbNodeW] at hb; simp [hs, g4, hc] at hb
    obtain ⟨hv, hf, ha⟩ := view_app m a hR h hh (vok APP hc) g4
    rw [bbNodeW_app n m h c (vok APP hc) g4] at hb
    obtain ⟨a', h1, h2⟩ := bbAppArm_ok n ih F m m' a hR c _ _ r hf ha hF' hb
    exact ⟨a', (bbNodeA_run F _ a _ hv).trans h1, h2⟩
  by_cases g5 : h >>> 28 = 5
  · by_cases hc : tcnt m LAM (tierW h) ≤ idxW h
    · rw [bbNodeW] at hb; simp [hs, g5, hc] at hb
    obtain ⟨hv, hf, ha⟩ := view_lam m a hR h hh (vok LAM hc) g5
    rw [bbNodeW_lam n m h c (vok LAM hc) g5] at hb
    obtain ⟨a', h1, h2⟩ := bbBindArm_ok n ih F m m' a hR c _ _ r hf ha hF' hb
    exact ⟨a', (bbNodeA_run F _ a _ hv).trans h1, h2⟩
  by_cases g6 : h >>> 28 = 6
  · by_cases hc : tcnt m FORALL (tierW h) ≤ idxW h
    · rw [bbNodeW] at hb; simp [hs, g6, hc] at hb
    obtain ⟨hv, hf, ha⟩ := view_forall m a hR h hh (vok FORALL hc) g6
    rw [bbNodeW_forall n m h c (vok FORALL hc) g6] at hb
    obtain ⟨a', h1, h2⟩ := bbBindArm_ok n ih F m m' a hR c _ _ r hf ha hF' hb
    exact ⟨a', (bbNodeA_run F _ a _ hv).trans h1, h2⟩
  by_cases g7 : h >>> 28 = 7
  · by_cases hc : tcnt m LET (tierW h) ≤ idxW h
    · rw [bbNodeW] at hb; simp [hs, g7, hc] at hb
    obtain ⟨hv, ht, hv', hb'⟩ := view_let m a hR h hh (vok LET hc) g7
    rw [bbNodeW_let n m h c (vok LET hc) g7] at hb
    obtain ⟨a', h1, h2⟩ := bbLetArm_ok n ih F m m' a hR c _ _ _ r ht hv' hb' hF' hb
    exact ⟨a', (bbNodeA_run F _ a _ hv).trans h1, h2⟩
  by_cases g9 : h >>> 28 = 9
  · by_cases hc : tcnt m PROJ (tierW h) ≤ idxW h
    · rw [bbNodeW] at hb; simp [hs, g9, hc] at hb
    obtain ⟨hv, -, he⟩ := view_proj m a hR h hh (vok PROJ hc) g9
    rw [bbNodeW_proj n m h c (vok PROJ hc) g9] at hb
    obtain ⟨a', h1, h2⟩ := ih F m m' a _ c r hF' hR he hb
    exact ⟨a', (bbNodeA_run F _ a _ hv).trans h1, h2⟩
  by_cases g1 : h >>> 28 = 1
  · by_cases hc : tcnt m FVAR (tierW h) ≤ idxW h
    · rw [bbNodeW] at hb; simp [hs, g1, hc] at hb
    rw [bbNodeW_fvar n m h c g1 (vok FVAR hc)] at hb
    obtain ⟨_, _, hv⟩ := view_fvar m a hR h hh (vok FVAR hc) g1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    exact zero _ hv rfl rfl rfl
  by_cases g2 : h >>> 28 = 2
  · by_cases hc : tcnt m SORT (tierW h) ≤ idxW h
    · rw [bbNodeW] at hb; simp [hs, g2, hc] at hb
    rw [bbNodeW_sort n m h c g2 (vok SORT hc)] at hb
    obtain ⟨_, hv⟩ := view_sort m a hR h hh (vok SORT hc) g2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    exact zero _ hv rfl rfl rfl
  by_cases g3 : h >>> 28 = 3
  · by_cases hc : tcnt m CONST (tierW h) ≤ idxW h
    · rw [bbNodeW] at hb; simp [hs, g3, hc] at hb
    rw [bbNodeW_const n m h c g3 (vok CONST hc)] at hb
    obtain ⟨_, _, hv⟩ := view_const m a hR h hh (vok CONST hc) g3
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    exact zero _ hv rfl rfl rfl
  by_cases g8 : h >>> 28 = 8
  · by_cases hc : tcnt m LIT (tierW h) ≤ idxW h
    · rw [bbNodeW] at hb; simp [hs, g8, hc] at hb
    rw [bbNodeW_lit n m h c g8 (vok LIT hc)] at hb
    obtain ⟨_, hv⟩ := view_lit m a hR h hh (vok LIT hc) g8
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    exact zero _ hv rfl rfl rfl
  rw [bbNodeW] at hb; simp [hs, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9] at hb

/-- **The model of `bb_go` refines `bvarBoundGo`** at every fuel. -/
theorem goOK (n : Nat) : GoOK n ∧ NodeOK n := by
  induction n with
  | zero =>
    exact ⟨fun _ _ _ _ _ _ _ _ _ _ hb => by simp [bbW] at hb,
      fun _ _ _ _ _ _ _ _ _ _ hb => by simp [bbNodeW] at hb⟩
  | succ n ih => exact ⟨goOK_succ n ih.2, nodeOK_succ n ih.1⟩

/-! ## The entry `bb_memo` refines `bvarBoundMemo` -/

theorem bvarBoundMemo_run (F : Nat) (e : EIdx) (a : AState) :
    (bvarBoundMemo F e).run a =
      ((bvarBoundGo F e).run (withBC a ∅) >>= fun p => .ok (p.1, withBC p.2 ∅)) := by
  simp only [bvarBoundMemo, StateT.run_bind, bvarBClear_run, except_ok_bind]
  cases (bvarBoundGo F e).run (withBC a ∅) <;> rfl

/-- **The model of `bb_memo` refines `bvarBoundMemo` at any twin fuel `F`** with `c.toNat ≤ F` or the
L fuel `n ≤ F` (the walk's counter or its L fuel bounds the twin's). -/
theorem bbMemoW_correctF (n F : Nat) (m m' : Mem) (a : AState) (hR : ArenaR m a)
    (h c r : Word) (hh : h.toNat < 2 ^ 32) (hF : c.toNat ≤ F ∨ n ≤ F)
    (hb : bbMemoW n m h c = some (r, m')) :
    ∃ a', (bvarBoundMemo F (decE h)).run a = .ok (r.toNat, a') ∧ ArenaR m' a' := by
  simp only [bbMemoW] at hb
  have h0 : ¬ rdW (m.arr64 CTL) 24 + 2 = 0 := fun h0 => by simp [h0] at hb
  simp only [h0, ↓reduceIte] at hb
  have hR₀ := ArenaR.memo_clear m a hR h0
  cases hw : bbW n (mclearG bmSch m) h c with
  | none => simp [hw, clrK] at hb
  | some p =>
    obtain ⟨r₁, m₁⟩ := p
    have h1 : ¬ rdW (m₁.arr64 CTL) 24 + 2 = 0 := fun h1 => by simp [hw, clrK, h1] at hb
    simp only [hw, clrK, h1, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    obtain ⟨a₁, ha₁, hR₁⟩ := (goOK n).1 F _ _ _ h c r₁ hF hR₀ hh hw
    exact ⟨_, by rw [bvarBoundMemo_run, ha₁]; rfl, ArenaR.memo_clear m₁ a₁ hR₁ h1⟩

/-- **The model of `bb_memo` refines `bvarBoundMemo`** at the counter's value `c.toNat`. -/
theorem bbMemoW_correct (n : Nat) (m m' : Mem) (a : AState) (hR : ArenaR m a)
    (h c r : Word) (hh : h.toNat < 2 ^ 32) (hb : bbMemoW n m h c = some (r, m')) :
    ∃ a', (bvarBoundMemo c.toNat (decE h)).run a = .ok (r.toNat, a') ∧ ArenaR m' a' := by
  exact bbMemoW_correctF n _ m m' a hR h c r hh (.inl (Nat.le_refl _)) hb

/-- **`bb_memo` refines the arena's `bvarBoundMemo` under `ArenaR`**: if the L walk returns, the
arena walk at the counter's fuel `c.toNat` succeeds with the same bound, in a related state. -/
@[refines ConRon.Arena.bvarBoundMemo]
theorem bbMemo_refines (p : Prog) (hpf : p.lookup "bm_find" = some (memoFindG bmSch))
    (hps : p.lookup "bm_put" = some (memoPutG bmSch)) (hpc : p.lookup "bm_clear" = some (memoClearG bmSch))
    (hp : p.lookup "bb_go" = some bbGo) (hpn : p.lookup "bb_node" = some bbNode)
    (hpm : p.lookup "bb_memo" = some bbMemo) (n : Nat) (s₀ : St) (a₀ : AState)
    (hR : ArenaR s₀.mem a₀) (h c : Word) (hh : h.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "bb_memo" [h, c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (bvarBoundMemo c.toNat (decE h)) a₀ ∧
      ArenaR s'.mem (AM.st (bvarBoundMemo c.toNat (decE h)) a₀) ∧
      AM.res (bvarBoundMemo c.toNat (decE h)) a₀ = (r.headD 0).toNat; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (bbMemo_spec p hpf hps hp hpn hpc hpm n s₀ h c)
  subst hs
  obtain ⟨a', ha', hR'⟩ := bbMemoW_correct n _ _ a₀ hR h c _ hh hI
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ ha'
  exact ⟨hloc, hok, hst ▸ hR', hres⟩

end L.Arena
