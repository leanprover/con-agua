import ConAgua.Arena.Walk
import ConAgua.Arena.View
import ConRon.Arena.ExprOps
import ConAgua.Census.Attr

/-!
# `bb_go` refines the arena's `bvarBoundGo`

The arena side of the walk (`Walk.lean` has the L code, its model `bbW`/`bbNodeW` and the
`vcgen` specs). Pure Lean, by induction on the fuel: if the model returns `r` and `m'` from `m`
related to `a` by `ArenaR`, then `bvarBoundGo F (decE h)` from `a` returns `r.toNat` in a state
related to `m'`, for every arena fuel `F` at least the L fuel.

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

set_option linter.unusedSimpArgs false

namespace L.Arena

/-! ## The memo operations under `ArenaR` -/

/-- The arena state after `bvarBSet k r`. -/
def withBC (a : AState) (mp : Std.HashMap EIdx Nat) : AState :=
  { a with memos := { a.memos with bvarBC := mp } }

theorem bvarBGet_run (k : EIdx) (a : AState) : (bvarBGet k).run a = .ok (a.memos.bvarBC[k]?, a) := rfl

theorem bvarBSet_run (k : EIdx) (r : Nat) (a : AState) :
    (bvarBSet k r).run a = .ok ((), withBC a (a.memos.bvarBC.insert k r)) := rfl

theorem bvarBClear_run (a : AState) : bvarBClear.run a = .ok ((), withBC a ∅) := rfl

/-- **`memo_set` is `bvarBSet`.** -/
theorem ArenaR.memo_set (m m' : Mem) (a : AState) (hR : ArenaR m a) (k v : Word)
    (hk : k.toNat < 2 ^ 32) (hs : msetG bmSch m k 0 v = some m') :
    ArenaR m' (withBC a (a.memos.bvarBC.insert (decE k) v.toNat)) := by
  have hf := msetG_frame bmSch bmSch_wf m m' k 0 v hs
  arena_build hR, hf with exact memoRG_set bmSch bmSch_wf bmKey _ m _ hR.memo k 0 v ⟨hk, rfl⟩ m' hs

/-- **`memo_clear` is `bvarBClear`.** -/
theorem ArenaR.memo_clear (m : Mem) (a : AState) (hR : ArenaR m a)
    (h0 : rdW (m.arr64 CTL) 24 + 2 ≠ 0) : ArenaR (mclearG bmSch m) (withBC a ∅) := by
  have hf := mclearG_frame bmSch m
  arena_build hR, hf with exact memoRG_clear bmSch bmSch_wf bmKey _ m _ hR.memo h0

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

/-! ## The refinement, by induction on the fuel -/

/-- What `bb_go`'s model at fuel `n` says about the arena walk at any fuel `F ≥ n`. -/
def GoOK (n : Nat) : Prop :=
  ∀ (F : Nat) (m m' : Mem) (a : AState) (h r : Word), n ≤ F → ArenaR m a → h.toNat < 2 ^ 32 →
    bbW n m h = some (r, m') →
    ∃ a', (bvarBoundGo F (decE h)).run a = .ok (r.toNat, a') ∧ ArenaR m' a'

/-- The same for `bb_node`'s model and the arena's view-and-arm. -/
def NodeOK (n : Nat) : Prop :=
  ∀ (F : Nat) (m m' : Mem) (a : AState) (h r : Word), n ≤ F + 1 → ArenaR m a →
    h.toNat < 2 ^ 32 → bbNodeW n m h = some (r, m') →
    ∃ a', (bbNodeA F (decE h)).run a = .ok (r.toNat, a') ∧ ArenaR m' a'

theorem goOK_succ (n : Nat) (ih : NodeOK n) : GoOK (n + 1) := by
  intro F m m' a h r hF hR hh hb
  obtain ⟨F, rfl⟩ : ∃ G, F = G + 1 := ⟨F - 1, by omega⟩
  rw [bvarBoundGo_succ', StateT.run_bind, bvarBGet_run]
  by_cases hr : mfindG bmSch m h 0 = []
  · rw [bbW] at hb; simp [hr] at hb
  by_cases hh0 : (mfindG bmSch m h 0).headD 0 ≠ 0
  · rw [bbW_hit n m h hr hh0] at hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    rw [show a.memos.bvarBC[decE h]? = _ from memoRG_hit bmSch bmKey _ m _ hR.memo h 0 hr hh0]
    exact ⟨a, rfl, hR⟩
  · simp only [ne_eq, Decidable.not_not] at hh0
    rw [bbW_miss n m h hr hh0] at hb
    rw [show a.memos.bvarBC[decE h]? = none from
      memoRG_miss bmSch bmKey _ m _ hR.memo h 0 ⟨hh, rfl⟩ hr hh0]
    cases hn : bbNodeW n m h with
    | none => simp [bbK, hn] at hb
    | some p =>
      obtain ⟨r₁, m₁⟩ := p
      simp only [hn, bbK, bbSet_eq] at hb
      cases hs : msetG bmSch m₁ h 0 r₁ with
      | none => simp [hs, setK] at hb
      | some m₂ =>
        simp only [hs, setK, Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        obtain ⟨a₁, ha₁, hR₁⟩ := ih F m m₁ a h r₁ (by omega) hR hh hn
        refine ⟨_, ?_, ArenaR.memo_set m₁ m₂ a₁ hR₁ h r₁ hh hs⟩
        change StateT.run (do let r ← bbNodeA F (decE h); bvarBSet (decE h) r; pure r) a = _
        simp only [StateT.run_bind, ha₁]
        rfl

/-- The `app` arm: two children, `max x y`. -/
theorem appArm_ok (n F : Nat) (ih : GoOK n) (hF : n ≤ F) (m m' : Mem) (a : AState)
    (hR : ArenaR m a) (fw aw r : Word) (hf : fw.toNat < 2 ^ 32) (ha : aw.toNat < 2 ^ 32)
    (hb : appK₁ n aw (bbW n m fw) = some (r, m')) :
    ∃ a', (bvarBoundArmApp F (decE fw) (decE aw)).run a = .ok (r.toNat, a') ∧ ArenaR m' a' := by
  cases h1 : bbW n m fw with
  | none => simp only [h1, appK₁, reduceCtorEq] at hb
  | some p =>
    obtain ⟨x, m₁⟩ := p
    cases h2 : bbW n m₁ aw with
    | none => simp only [h1, h2, appK₁, appK₁.appK₂, reduceCtorEq] at hb
    | some q =>
      obtain ⟨y, m₂⟩ := q
      simp only [h1, h2, appK₁, appK₁.appK₂, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      obtain ⟨a₁, ha₁, hR₁⟩ := ih F m m₁ a _ x hF hR hf h1
      obtain ⟨a₂, ha₂, hR₂⟩ := ih F m₁ m₂ a₁ _ y hF hR₁ ha h2
      refine ⟨a₂, ?_, hR₂⟩
      rw [maxW_toNat]
      simp only [bvarBoundArmApp, StateT.run_bind, ha₁, except_ok_bind, ha₂]
      rfl

/-- The binder arm (`lam`, `forallE`): two children, `max x (y - 1)`. -/
theorem bindArm_ok (n F : Nat) (ih : GoOK n) (hF : n ≤ F) (m m' : Mem) (a : AState)
    (hR : ArenaR m a) (tw bw r : Word) (ht : tw.toNat < 2 ^ 32) (hb' : bw.toNat < 2 ^ 32)
    (hb : bindK₁ n bw (bbW n m tw) = some (r, m')) :
    ∃ a', (bvarBoundArmBind F (decE tw) (decE bw)).run a = .ok (r.toNat, a') ∧ ArenaR m' a' := by
  cases h1 : bbW n m tw with
  | none => simp only [h1, bindK₁, reduceCtorEq] at hb
  | some p =>
    obtain ⟨x, m₁⟩ := p
    cases h2 : bbW n m₁ bw with
    | none => simp only [h1, h2, bindK₁, bindK₁.bindK₂, reduceCtorEq] at hb
    | some q =>
      obtain ⟨y, m₂⟩ := q
      simp only [h1, h2, bindK₁, bindK₁.bindK₂, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      obtain ⟨a₁, ha₁, hR₁⟩ := ih F m m₁ a _ x hF hR ht h1
      obtain ⟨a₂, ha₂, hR₂⟩ := ih F m₁ m₂ a₁ _ y hF hR₁ hb' h2
      refine ⟨a₂, ?_, hR₂⟩
      rw [maxW_toNat, predW_toNat]
      simp only [bvarBoundArmBind, StateT.run_bind, ha₁, except_ok_bind, ha₂]
      rfl

/-- The `letE` arm: three children, `max (max x y) (z - 1)`. -/
theorem letArm_ok (n F : Nat) (ih : GoOK n) (hF : n ≤ F) (m m' : Mem) (a : AState)
    (hR : ArenaR m a) (tw vw bw r : Word) (ht : tw.toNat < 2 ^ 32) (hv : vw.toNat < 2 ^ 32)
    (hb' : bw.toNat < 2 ^ 32) (hb : letK₁ n vw bw (bbW n m tw) = some (r, m')) :
    ∃ a', (bvarBoundArmLet F (decE tw) (decE vw) (decE bw)).run a = .ok (r.toNat, a') ∧
      ArenaR m' a' := by
  cases h1 : bbW n m tw with
  | none => simp only [h1, letK₁, reduceCtorEq] at hb
  | some p =>
    obtain ⟨x, m₁⟩ := p
    cases h2 : bbW n m₁ vw with
    | none => simp only [h1, h2, letK₁, letK₁.letK₂, reduceCtorEq] at hb
    | some q =>
      obtain ⟨y, m₂⟩ := q
      cases h3 : bbW n m₂ bw with
      | none => simp only [h1, h2, h3, letK₁, letK₁.letK₂, letK₁.letK₃, reduceCtorEq] at hb
      | some o =>
        obtain ⟨z, m₃⟩ := o
        simp only [h1, h2, h3, letK₁, letK₁.letK₂, letK₁.letK₃, Option.some.injEq,
          Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        obtain ⟨a₁, ha₁, hR₁⟩ := ih F m m₁ a _ x hF hR ht h1
        obtain ⟨a₂, ha₂, hR₂⟩ := ih F m₁ m₂ a₁ _ y hF hR₁ hv h2
        obtain ⟨a₃, ha₃, hR₃⟩ := ih F m₂ m₃ a₂ _ z hF hR₂ hb' h3
        refine ⟨a₃, ?_, hR₃⟩
        rw [maxW_toNat, maxW_toNat, predW_toNat]
        simp only [bvarBoundArmLet, StateT.run_bind, ha₁, except_ok_bind, ha₂, ha₃]
        rfl

theorem nodeOK_succ (n : Nat) (ih : GoOK n) : NodeOK (n + 1) := by
  intro F m m' a h r hF hR hh hb
  have hF' : n ≤ F := by omega
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [bbNodeW] at hb; simp only [ite_eq_left hs, reduceCtorEq] at hb
  have vok : ∀ c, ¬ rdW (m.arr64 CTL) (c + tierW h) ≤ idxW h → viewOK m h c :=
    fun c hc => ⟨hs, UInt64.not_le.mp hc⟩
  have zero : ∀ v, a.store.view (decE h) = some v → bbArm F v = pure 0 → r = 0 → m' = m →
      ∃ a', (bbNodeA F (decE h)).run a = .ok (r.toNat, a') ∧ ArenaR m' a' := by
    intro v hv hx hr hm; subst hr hm
    exact ⟨a, by rw [bbNodeA_run F _ a _ hv, hx]; rfl, hR⟩
  by_cases g0 : h >>> 28 = 0
  · by_cases hc : rdW (m.arr64 CTL) (22 + tierW h) ≤ idxW h
    · rw [bbNodeW] at hb; simp [hs, g0, hc] at hb
    by_cases h1 : rdW (m.arr64 BREC) (idxW h * 2 + tierW h) + 1 = 0
    · rw [bbNodeW] at hb; simp [hs, g0, hc, h1] at hb
    rw [bbNodeW_bvar n m h (vok 22 hc) g0 h1] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    refine ⟨a, ?_, hR⟩
    rw [bbNodeA_run F _ a _ (view_bvar m a hR h hh (vok 22 hc) g0), succW_toNat _ h1]; rfl
  by_cases g4 : h >>> 28 = 4
  · by_cases hc : rdW (m.arr64 CTL) (4 + tierW h) ≤ idxW h
    · rw [bbNodeW] at hb; simp [hs, g4, hc] at hb
    obtain ⟨hv, hf, ha⟩ := view_app m a hR h hh (vok 4 hc) g4
    rw [bbNodeW_app n m h (vok 4 hc) g4] at hb
    obtain ⟨a', h1, h2⟩ := appArm_ok n F ih hF' m m' a hR _ _ r hf ha hb
    exact ⟨a', (bbNodeA_run F _ a _ hv).trans h1, h2⟩
  by_cases g5 : h >>> 28 = 5
  · by_cases hc : rdW (m.arr64 CTL) (28 + tierW h) ≤ idxW h
    · rw [bbNodeW] at hb; simp [hs, g5, hc] at hb
    obtain ⟨hv, hf, ha⟩ := view_lam m a hR h hh (vok 28 hc) g5
    rw [bbNodeW_lam n m h (vok 28 hc) g5] at hb
    obtain ⟨a', h1, h2⟩ := bindArm_ok n F ih hF' m m' a hR _ _ r hf ha hb
    exact ⟨a', (bbNodeA_run F _ a _ hv).trans h1, h2⟩
  by_cases g6 : h >>> 28 = 6
  · by_cases hc : rdW (m.arr64 CTL) (30 + tierW h) ≤ idxW h
    · rw [bbNodeW] at hb; simp [hs, g6, hc] at hb
    obtain ⟨hv, hf, ha⟩ := view_forall m a hR h hh (vok 30 hc) g6
    rw [bbNodeW_forall n m h (vok 30 hc) g6] at hb
    obtain ⟨a', h1, h2⟩ := bindArm_ok n F ih hF' m m' a hR _ _ r hf ha hb
    exact ⟨a', (bbNodeA_run F _ a _ hv).trans h1, h2⟩
  by_cases g7 : h >>> 28 = 7
  · by_cases hc : rdW (m.arr64 CTL) (20 + tierW h) ≤ idxW h
    · rw [bbNodeW] at hb; simp [hs, g7, hc] at hb
    obtain ⟨hv, ht, hv', hb'⟩ := view_let m a hR h hh (vok 20 hc) g7
    rw [bbNodeW_let n m h (vok 20 hc) g7] at hb
    obtain ⟨a', h1, h2⟩ := letArm_ok n F ih hF' m m' a hR _ _ _ r ht hv' hb' hb
    exact ⟨a', (bbNodeA_run F _ a _ hv).trans h1, h2⟩
  by_cases g9 : h >>> 28 = 9
  · by_cases hc : rdW (m.arr64 CTL) (32 + tierW h) ≤ idxW h
    · rw [bbNodeW] at hb; simp [hs, g9, hc] at hb
    obtain ⟨hv, -, he⟩ := view_proj m a hR h hh (vok 32 hc) g9
    rw [bbNodeW_proj n m h (vok 32 hc) g9] at hb
    obtain ⟨a', h1, h2⟩ := ih F m m' a _ r hF' hR he hb
    exact ⟨a', (bbNodeA_run F _ a _ hv).trans h1, h2⟩
  by_cases g1 : h >>> 28 = 1
  · by_cases hc : rdW (m.arr64 CTL) (26 + tierW h) ≤ idxW h
    · rw [bbNodeW] at hb; simp [hs, g1, hc] at hb
    rw [bbNodeW_fvar n m h g1 (vok 26 hc)] at hb
    obtain ⟨_, _, hv⟩ := view_fvar m a hR h hh (vok 26 hc) g1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    exact zero _ hv rfl rfl rfl
  by_cases g2 : h >>> 28 = 2
  · by_cases hc : rdW (m.arr64 CTL) (16 + tierW h) ≤ idxW h
    · rw [bbNodeW] at hb; simp [hs, g2, hc] at hb
    rw [bbNodeW_sort n m h g2 (vok 16 hc)] at hb
    obtain ⟨_, hv⟩ := view_sort m a hR h hh (vok 16 hc) g2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    exact zero _ hv rfl rfl rfl
  by_cases g3 : h >>> 28 = 3
  · by_cases hc : rdW (m.arr64 CTL) (18 + tierW h) ≤ idxW h
    · rw [bbNodeW] at hb; simp [hs, g3, hc] at hb
    rw [bbNodeW_const n m h g3 (vok 18 hc)] at hb
    obtain ⟨_, _, hv⟩ := view_const m a hR h hh (vok 18 hc) g3
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    exact zero _ hv rfl rfl rfl
  by_cases g8 : h >>> 28 = 8
  · by_cases hc : rdW (m.arr64 CTL) (2 + tierW h) ≤ idxW h
    · rw [bbNodeW] at hb; simp [hs, g8, hc] at hb
    rw [bbNodeW_lit n m h g8 (vok 2 hc)] at hb
    obtain ⟨_, hv⟩ := view_lit m a hR h hh (vok 2 hc) g8
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    exact zero _ hv rfl rfl rfl
  rw [bbNodeW] at hb; simp [hs, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9] at hb

/-- **The model of `bb_go` refines `bvarBoundGo`** at every fuel. -/
theorem goOK (n : Nat) : GoOK n ∧ NodeOK n := by
  induction n with
  | zero =>
    exact ⟨fun _ _ _ _ _ _ _ _ _ hb => by simp [bbW] at hb,
      fun _ _ _ _ _ _ _ _ _ hb => by simp [bbNodeW] at hb⟩
  | succ n ih => exact ⟨goOK_succ n ih.2, nodeOK_succ n ih.1⟩

/-! ## The entry `bb_memo` refines `bvarBoundMemo` -/

theorem bvarBoundMemo_run (F : Nat) (e : EIdx) (a : AState) :
    (bvarBoundMemo F e).run a =
      ((bvarBoundGo F e).run (withBC a ∅) >>= fun p => .ok (p.1, withBC p.2 ∅)) := by
  simp only [bvarBoundMemo, StateT.run_bind, bvarBClear_run, except_ok_bind]
  cases (bvarBoundGo F e).run (withBC a ∅) <;> rfl

/-- **The model of `bb_memo` refines `bvarBoundMemo`**, at every arena fuel `F ≥ n`. -/
theorem bbMemoW_correct (n F : Nat) (hF : n ≤ F) (m m' : Mem) (a : AState) (hR : ArenaR m a)
    (h r : Word) (hh : h.toNat < 2 ^ 32) (hb : bbMemoW n m h = some (r, m')) :
    ∃ a', (bvarBoundMemo F (decE h)).run a = .ok (r.toNat, a') ∧ ArenaR m' a' := by
  simp only [bbMemoW] at hb
  by_cases h0 : rdW (m.arr64 CTL) 24 + 2 = 0
  · simp [h0] at hb
  simp only [h0, ↓reduceIte] at hb
  have hR₀ := ArenaR.memo_clear m a hR h0
  cases hw : bbW n (mclearG bmSch m) h with
  | none => simp [hw, clrK] at hb
  | some p =>
    obtain ⟨r₁, m₁⟩ := p
    by_cases h1 : rdW (m₁.arr64 CTL) 24 + 2 = 0
    · simp [hw, clrK, h1] at hb
    simp only [hw, clrK, h1, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    obtain ⟨a₁, ha₁, hR₁⟩ := (goOK n).1 F _ _ _ h r₁ hF hR₀ hh hw
    exact ⟨_, by rw [bvarBoundMemo_run, ha₁]; rfl, ArenaR.memo_clear m₁ a₁ hR₁ h1⟩

/-- **`bb_memo` refines the arena's `bvarBoundMemo` under `ArenaR`**: if the L walk returns, the
arena walk at any fuel `F ≥ n` succeeds with the same bound, in a related state. -/
@[refines ConRon.Arena.bvarBoundMemo]
theorem bbMemo_refines (p : Prog) (hpf : p.lookup "bm_find" = some (memoFindG bmSch))
    (hps : p.lookup "bm_put" = some (memoPutG bmSch)) (hpc : p.lookup "bm_clear" = some (memoClearG bmSch))
    (hp : p.lookup "bb_go" = some bbGo) (hpn : p.lookup "bb_node" = some bbNode)
    (hpm : p.lookup "bb_memo" = some bbMemo) (n F : Nat) (hF : n ≤ F) (s₀ : St) (a₀ : AState)
    (hR : ArenaR s₀.mem a₀) (h : Word) (hh : h.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "bb_memo" [h]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (bvarBoundMemo F (decE h)) a₀ ∧
      ArenaR s'.mem (AM.st (bvarBoundMemo F (decE h)) a₀) ∧
      AM.res (bvarBoundMemo F (decE h)) a₀ = (r.headD 0).toNat; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (bbMemo_spec p hpf hps hp hpn hpc hpm n s₀ h)
  subst hs
  obtain ⟨a', ha', hR'⟩ := bbMemoW_correct n F hF _ _ a₀ hR h _ hh hI
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ ha'
  exact ⟨hloc, hok, hst ▸ hR', hres⟩

/-- From an L run of `bb_memo` to the arena run of `bvarBoundMemo`, at any fuel `F ≥ fuel`. -/
theorem bbMemo_run (fuel F : Nat) (hF : fuel ≤ F) (m : Mem) (a₀ : AState) (hR : ArenaR m a₀)
    (h : Word) (hh : h.toNat < 2 ^ 32) (r : List Word) (m' : Mem)
    (hrun : run walkProg fuel "bb_memo" [h] m = .ok (r, m')) :
    ∃ a', (bvarBoundMemo F (decE h)).run a₀ = .ok ((r.headD 0).toNat, a') ∧ ArenaR m' a' := by
  cases fuel with
  | zero =>
    have : (invoke walkProg (exec walkProg 0) "bb_memo" [h]).run
        { mem := m, loc := Locals.init [] } = .error .outOfFuel := rfl
    simp [run, this, Except.map] at hrun
  | succ n =>
    simp only [run] at hrun
    cases hr : (invoke walkProg (exec walkProg (n + 1)) "bb_memo" [h]).run
        { mem := m, loc := Locals.init [] } with
    | error e => simp [hr, Except.map] at hrun
    | ok rs =>
      simp only [hr, Except.map] at hrun
      injection hrun with hrun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
      have := M.of_run (P := fun s => s = { mem := m, loc := Locals.init [] }) rfl hr
        (bbMemo_refines walkProg rfl rfl rfl rfl rfl rfl n F (by omega) _ a₀ hR h hh)
      obtain ⟨-, hok, hR', hres⟩ := this
      exact ⟨_, by rw [AM.run_of_ok _ _ hok, hres], hR'⟩

end L.Arena
