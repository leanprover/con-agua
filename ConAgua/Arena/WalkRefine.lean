import ConAgua.Arena.Walk
import ConAgua.Arena.ArenaRel
import ConRon.Arena.ExprOps

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

/-! ## Handle words -/

theorem decE_tag (h : Word) (hh : h.toNat < 2 ^ 32) : (decE h).tag = (h >>> 28).toUInt32 := by
  simp only [decE, Idx.tag]
  apply UInt32.toNat_inj.mp
  simp [UInt32.toNat_div, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  omega

theorem decE_idx (h : Word) : (decE h).idxNat = (idxW h).toNat := by
  simp only [decE, Idx.idxNat, Idx.index, idxW]
  simp [UInt32.toNat_mod, UInt64.toNat_toUInt32, UInt64.toNat_and]
  have : (134217727 : Nat) = 2 ^ 27 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

theorem decE_pers (h : Word) (hh : h.toNat < 2 ^ 32) : (decE h).isPersistent = (tierW h == 0) := by
  rw [decE_eq, isPersistent_decI h hh]; rfl

theorem tierW_le (h : Word) : tierW h ≤ 1 := by
  simp only [tierW]; exact UInt64.and_le_right

/-! ## Nodes of a table -/

theorem storeR_node {α δ : Type} {k : IdxKind} [BEq α] [Hashable α] (S : Schema)
    (R : Mem → Word → Word → α → Prop) (hs : Mem → Word → Word → Word) (m : Mem) (on : Bool)
    (P Q : Tbl α (Idx k) δ) (hR : StoreR S R hs m on P Q) (t : Word) (ht : t ≤ 1) (i : Word)
    (hi : i < cntW S m t) :
    ∃ x, (if t = 0 then P else Q).nodes[i.toNat]? = some x ∧ R m t i x := by
  have hT : TierR S R hs m t (if t = 0 then P else Q) := by
    rcases word_le_one t ht with rfl | rfl
    · simpa using hR.2.2.1
    · simpa using hR.2.2.2
  obtain ⟨hc, -, -, hrec, -⟩ := hT
  have hlt : i.toNat < (if t = 0 then P else Q).nodes.size := by
    rw [← hc]; exact hi
  exact ⟨_, Array.getElem?_eq_getElem hlt, hrec _ _ (Array.getElem?_eq_getElem hlt)⟩

/-! ## The view -/

section view
variable (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)

include hR hh in
/-- Under the L code's scratch check, the arena's view of the handle reads the tier its bit
names. -/
theorem view_tier (hv : ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0)) :
    a.store.view (decE h) = (if tierW h = 0 then a.store.pers else a.store.scr).get (decE h) := by
  have hfl := hR.app.2.1
  unfold EStore.view
  rw [decE_pers h hh]
  by_cases ht : tierW h = 0
  · simp [ht]
  · have hon : a.store.scratchOn = true := by
      rw [← hfl]; simp only [bne_iff_ne, ne_eq]; exact fun h1 => hv ⟨ht, h1⟩
    simp [ht, hon]

/-- A node of the tier the handle names, from a table relation and the count check. -/
theorem node_of {α : Type} [BEq α] [Hashable α] (S : Schema) (R : Mem → Word → Word → α → Prop)
    (hs : Mem → Word → Word → Word) (tbl : ETables → Tbl α EIdx UInt64) (on : Bool)
    (hT : StoreR S R hs m on (tbl a.store.pers) (tbl a.store.scr))
    (hc : idxW h < cntW S m (tierW h)) :
    ∃ k, (tbl (if tierW h = 0 then a.store.pers else a.store.scr)).nodes[(idxW h).toNat]? = some k ∧
      R m (tierW h) (idxW h) k := by
  obtain ⟨k, h1, h2⟩ := storeR_node S R hs m on _ _ hT (tierW h) (tierW_le h) (idxW h) hc
  refine ⟨k, ?_, h2⟩
  rw [apply_ite tbl]; exact h1

end view

theorem get_bvar (tb : ETables) (h : Word) (hh : h.toNat < 2 ^ 32) (hg : h >>> 28 = 0) :
    tb.get (decE h) = (tb.bvars.node? (idxW h).toNat).map fun r => .bvar r.i := by
  simp [ETables.get, decE_tag h hh, hg, decE_idx h, ETag.bvar]
theorem get_sort (tb : ETables) (h : Word) (hh : h.toNat < 2 ^ 32) (hg : h >>> 28 = 2) :
    tb.get (decE h) = (tb.sorts.node? (idxW h).toNat).map fun r => .sort r.u := by
  simp [ETables.get, decE_tag h hh, hg, decE_idx h, ETag.bvar, ETag.fvar, ETag.sort]
theorem get_const (tb : ETables) (h : Word) (hh : h.toNat < 2 ^ 32) (hg : h >>> 28 = 3) :
    tb.get (decE h) = (tb.consts.node? (idxW h).toNat).map fun r => .const r.n r.us := by
  simp [ETables.get, decE_tag h hh, hg, decE_idx h, ETag.bvar, ETag.fvar, ETag.sort, ETag.const]
theorem get_app (tb : ETables) (h : Word) (hh : h.toNat < 2 ^ 32) (hg : h >>> 28 = 4) :
    tb.get (decE h) = (tb.apps.node? (idxW h).toNat).map fun r => .app r.f r.a := by
  simp [ETables.get, decE_tag h hh, hg, decE_idx h, ETag.bvar, ETag.fvar, ETag.sort, ETag.const,
    ETag.app]
theorem get_let (tb : ETables) (h : Word) (hh : h.toNat < 2 ^ 32) (hg : h >>> 28 = 7) :
    tb.get (decE h) = (tb.lets.node? (idxW h).toNat).map fun r => .letE r.ty r.val r.body := by
  simp [ETables.get, decE_tag h hh, hg, decE_idx h, ETag.bvar, ETag.fvar, ETag.sort, ETag.const,
    ETag.app, ETag.lam, ETag.forallE, ETag.letE]
theorem get_lit (tb : ETables) (h : Word) (hh : h.toNat < 2 ^ 32) (hg : h >>> 28 = 8) :
    tb.get (decE h) = (tb.lits.node? (idxW h).toNat).map fun r => .lit r.l := by
  simp [ETables.get, decE_tag h hh, hg, decE_idx h, ETag.bvar, ETag.fvar, ETag.sort, ETag.const,
    ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit]

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
    (hk : k.toNat < 2 ^ 32) (hs : msetW m k v = some m') :
    ArenaR m' (withBC a (a.memos.bvarBC.insert (decE k) v.toNat)) := by
  have hf := msetW_frame m m' k v hs
  exact ⟨hR.lit.frame _ _ m m' hf a (by apart), hR.app.frame _ _ m m' hf a (by apart),
    hR.sort.frame _ _ m m' hf a (by apart), hR.const.frame _ _ m m' hf a (by apart),
    hR.letE.frame _ _ m m' hf a (by apart), hR.bvar.frame _ _ m m' hf a (by apart),
    hR.zero.frame _ _ m m' hf a (by apart), hR.succ.frame _ _ m m' hf a (by apart),
    hR.max.frame _ _ m m' hf a (by apart), hR.imax.frame _ _ m m' hf a (by apart),
    hR.param.frame _ _ m m' hf a (by apart), memoR_set m _ hR.memo k v hk m' hs⟩

/-- **`memo_clear` is `bvarBClear`.** -/
theorem ArenaR.memo_clear (m : Mem) (a : AState) (hR : ArenaR m a)
    (h0 : rdW (m.arr64 CTL) 24 + 2 ≠ 0) : ArenaR (mclearMem m) (withBC a ∅) := by
  have hf := mclearMem_frame m
  exact ⟨hR.lit.frame _ _ m _ hf a (by apart), hR.app.frame _ _ m _ hf a (by apart),
    hR.sort.frame _ _ m _ hf a (by apart), hR.const.frame _ _ m _ hf a (by apart),
    hR.letE.frame _ _ m _ hf a (by apart), hR.bvar.frame _ _ m _ hf a (by apart),
    hR.zero.frame _ _ m _ hf a (by apart), hR.succ.frame _ _ m _ hf a (by apart),
    hR.max.frame _ _ m _ hf a (by apart), hR.imax.frame _ _ m _ hf a (by apart),
    hR.param.frame _ _ m _ hf a (by apart), memoR_clear m _ hR.memo h0⟩

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

theorem view_run (h : EIdx) (a : AState) (v : ENodeView) (hv : a.store.view h = some v) :
    (view h).run a = .ok (v, a) := by
  simp [view, hv, StateT.run_bind, StateT.run_get]; rfl

theorem bbNodeA_run (F : Nat) (h : EIdx) (a : AState) (v : ENodeView)
    (hv : a.store.view h = some v) : (bbNodeA F h).run a = (bbArm F v).run a := by
  simp only [bbNodeA, StateT.run_bind, view_run h a v hv]; rfl

/-! ## Arithmetic of the arms -/

theorem maxW_toNat (x y : Word) : (maxW x y).toNat = max x.toNat y.toNat := by
  simp only [maxW]
  by_cases h : x < y
  · have e : x + (y - x) = y := by rw [UInt64.add_comm, UInt64.sub_add_cancel]
    simp only [h, ↓reduceIte, UInt64.mul_one, e]
    have : x.toNat < y.toNat := h; omega
  · simp only [h, ↓reduceIte, UInt64.mul_zero, UInt64.add_zero]
    have : ¬ x.toNat < y.toNat := h; omega

theorem predW_toNat (z : Word) : (predW z).toNat = z.toNat - 1 := by
  simp only [predW]
  by_cases h : 0 < z
  · simp only [h, ↓reduceIte]
    have : 0 < z.toNat := h
    rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega)]; simp
  · simp only [h, ↓reduceIte, UInt64.sub_zero]
    have : ¬ 0 < z.toNat := h; omega

theorem succW_toNat (x : Word) (h : x + 1 ≠ 0) : (x + 1).toNat = x.toNat + 1 := by
  have := x.toNat_lt
  rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]
  rw [Nat.mod_eq_of_lt]
  rcases Nat.lt_or_ge (x.toNat + 1) (2 ^ 64) with hl | hl
  · exact hl
  · exfalso; apply h; apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add]; simp only [UInt64.toNat_one, UInt64.toNat_zero]; omega

theorem decE_word (x : EIdx) : decE x.word.toUInt64 = x := by
  cases x; simp [decE]

theorem word_lt (x : EIdx) : x.word.toUInt64.toNat < 2 ^ 32 := by
  simp; exact x.word.toNat_lt

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
  by_cases hr : mfindW m h = []
  · rw [bbW] at hb; simp [hr] at hb
  by_cases hh0 : (mfindW m h).headD 0 ≠ 0
  · rw [bbW_hit n m h hr hh0] at hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    rw [memoR_hit m _ hR.memo h hr hh0]
    exact ⟨a, rfl, hR⟩
  · simp only [ne_eq, Decidable.not_not] at hh0
    rw [bbW_miss n m h hr hh0] at hb
    rw [memoR_miss m _ hR.memo h hh hr hh0]
    cases hn : bbNodeW n m h with
    | none => simp [bbK, hn] at hb
    | some p =>
      obtain ⟨r₁, m₁⟩ := p
      simp only [hn, bbK, bbSet_eq] at hb
      cases hs : msetW m₁ h r₁ with
      | none => simp [hs, setK] at hb
      | some m₂ =>
        simp only [hs, setK, Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        obtain ⟨a₁, ha₁, hR₁⟩ := ih F m m₁ a h r₁ (by omega) hR hh hn
        refine ⟨_, ?_, ArenaR.memo_set m₁ m₂ a₁ hR₁ h r₁ hh hs⟩
        change StateT.run (do let r ← bbNodeA F (decE h); bvarBSet (decE h) r; pure r) a = _
        simp only [StateT.run_bind, ha₁]
        rfl

theorem except_ok_bind {ε α β : Type} (x : α) (f : α → Except ε β) :
    (Except.ok x >>= f) = f x := rfl

theorem pure_run (v : Nat) (a : AState) : (pure v : AM Nat).run a = .ok (v, a) := rfl

theorem nodeOK_succ (n : Nat) (ih : GoOK n) : NodeOK (n + 1) := by
  intro F m m' a h r hF hR hh hb
  have hF' : n ≤ F := by omega
  rw [bbNodeW] at hb
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp only [ite_eq_left hs, reduceCtorEq] at hb
  simp only [ite_eq_right hs] at hb
  have hview := view_tier m a hR h hh hs
  by_cases g0 : h >>> 28 = 0
  · simp only [g0, ↓reduceIte] at hb
    by_cases hc : rdW (m.arr64 CTL) (22 + tierW h) ≤ idxW h
    · simp only [hc, ↓reduceIte, reduceCtorEq] at hb
    by_cases h1 : rdW (m.arr64 BREC) (idxW h * 2 + tierW h) + 1 = 0
    · simp only [hc, h1, ↓reduceIte, reduceCtorEq] at hb
    simp only [hc, h1, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    obtain ⟨k, hk, hkr⟩ := node_of m a h bvarSch BRecRel bhash (·.bvars) _ hR.bvar
      (UInt64.not_le.mp hc)
    have hv : a.store.view (decE h) = some (.bvar k.i) := by
      rw [hview, get_bvar _ h hh g0, Tbl.node?, hk]; rfl
    refine ⟨a, ?_, hR⟩
    rw [bbNodeA_run F _ a _ hv, succW_toNat _ h1]
    simp only [BRecRel] at hkr
    rw [hkr]; rfl
  simp only [g0, ↓reduceIte] at hb
  by_cases g4 : h >>> 28 = 4
  · simp only [g4, ↓reduceIte] at hb
    by_cases hc : rdW (m.arr64 CTL) (4 + tierW h) ≤ idxW h
    · simp only [hc, ↓reduceIte, reduceCtorEq] at hb
    obtain ⟨k, hk, hf, ha⟩ := node_of m a h appSch ARecRel ahash (·.apps) _ hR.app
      (UInt64.not_le.mp hc)
    have hv : a.store.view (decE h) = some (.app k.f k.a) := by
      rw [hview, get_app _ h hh g4, Tbl.node?, hk]; rfl
    simp only [hc, ↓reduceIte, hf, ha] at hb
    cases h1 : bbW n m k.f.word.toUInt64 with
    | none => simp only [h1, reduceCtorEq] at hb
    | some p =>
      obtain ⟨x, m₁⟩ := p
      cases h2 : bbW n m₁ k.a.word.toUInt64 with
      | none => simp only [h1, h2, reduceCtorEq] at hb
      | some q =>
        obtain ⟨y, m₂⟩ := q
        simp only [h1, h2, Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        obtain ⟨a₁, ha₁, hR₁⟩ := ih F m m₁ a _ x hF' hR (word_lt _) h1
        rw [decE_word] at ha₁
        obtain ⟨a₂, ha₂, hR₂⟩ := ih F m₁ m₂ a₁ _ y hF' hR₁ (word_lt _) h2
        rw [decE_word] at ha₂
        refine ⟨a₂, ?_, hR₂⟩
        rw [bbNodeA_run F _ a _ hv, maxW_toNat]
        simp only [bbArm, bvarBoundArmApp, StateT.run_bind, ha₁, except_ok_bind, ha₂]
        rfl
  simp only [g4, ↓reduceIte] at hb
  by_cases g7 : h >>> 28 = 7
  · simp only [g7, ↓reduceIte] at hb
    by_cases hc : rdW (m.arr64 CTL) (20 + tierW h) ≤ idxW h
    · simp only [hc, ↓reduceIte, reduceCtorEq] at hb
    obtain ⟨k, hk, hf, ha, hb'⟩ := node_of m a h letSch LeRecRel lehash (·.lets) _ hR.letE
      (UInt64.not_le.mp hc)
    have hv : a.store.view (decE h) = some (.letE k.ty k.val k.body) := by
      rw [hview, get_let _ h hh g7, Tbl.node?, hk]; rfl
    simp only [hc, ↓reduceIte, hf, ha, hb'] at hb
    cases h1 : bbW n m k.ty.word.toUInt64 with
    | none => simp only [h1, reduceCtorEq] at hb
    | some p =>
      obtain ⟨x, m₁⟩ := p
      cases h2 : bbW n m₁ k.val.word.toUInt64 with
      | none => simp only [h1, h2, reduceCtorEq] at hb
      | some q =>
        obtain ⟨y, m₂⟩ := q
        cases h3 : bbW n m₂ k.body.word.toUInt64 with
        | none => simp only [h1, h2, h3, reduceCtorEq] at hb
        | some o =>
          obtain ⟨z, m₃⟩ := o
          simp only [h1, h2, h3, Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          obtain ⟨a₁, ha₁, hR₁⟩ := ih F m m₁ a _ x hF' hR (word_lt _) h1
          rw [decE_word] at ha₁
          obtain ⟨a₂, ha₂, hR₂⟩ := ih F m₁ m₂ a₁ _ y hF' hR₁ (word_lt _) h2
          rw [decE_word] at ha₂
          obtain ⟨a₃, ha₃, hR₃⟩ := ih F m₂ m₃ a₂ _ z hF' hR₂ (word_lt _) h3
          rw [decE_word] at ha₃
          refine ⟨a₃, ?_, hR₃⟩
          rw [bbNodeA_run F _ a _ hv, maxW_toNat, maxW_toNat, predW_toNat]
          simp only [bbArm, bvarBoundArmLet, StateT.run_bind, ha₁, except_ok_bind, ha₂, ha₃]
          rfl
  simp only [g7, ↓reduceIte] at hb
  by_cases g2 : h >>> 28 = 2
  · simp only [g2, ↓reduceIte] at hb
    by_cases hc : rdW (m.arr64 CTL) (16 + tierW h) ≤ idxW h
    · simp only [hc, ↓reduceIte, reduceCtorEq] at hb
    simp only [hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    obtain ⟨k, hk, -⟩ := node_of m a h sortSch SoRecRel sohash (·.sorts) _ hR.sort
      (UInt64.not_le.mp hc)
    have hv : a.store.view (decE h) = some (.sort k.u) := by
      rw [hview, get_sort _ h hh g2, Tbl.node?, hk]; rfl
    exact ⟨a, by rw [bbNodeA_run F _ a _ hv]; rfl, hR⟩
  simp only [g2, ↓reduceIte] at hb
  by_cases g3 : h >>> 28 = 3
  · simp only [g3, ↓reduceIte] at hb
    by_cases hc : rdW (m.arr64 CTL) (18 + tierW h) ≤ idxW h
    · simp only [hc, ↓reduceIte, reduceCtorEq] at hb
    simp only [hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    obtain ⟨k, hk, -⟩ := node_of m a h constSch CeRecRel cehash (·.consts) _ hR.const
      (UInt64.not_le.mp hc)
    have hv : a.store.view (decE h) = some (.const k.n k.us) := by
      rw [hview, get_const _ h hh g3, Tbl.node?, hk]; rfl
    exact ⟨a, by rw [bbNodeA_run F _ a _ hv]; rfl, hR⟩
  simp only [g3, ↓reduceIte] at hb
  by_cases g8 : h >>> 28 = 8
  · simp only [g8, ↓reduceIte] at hb
    by_cases hc : rdW (m.arr64 CTL) (2 + tierW h) ≤ idxW h
    · simp only [hc, ↓reduceIte, reduceCtorEq] at hb
    simp only [hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    obtain ⟨k, hk, -⟩ := node_of m a h litSch RecRel litH (·.lits) _ hR.lit.2
      (UInt64.not_le.mp hc)
    have hv : a.store.view (decE h) = some (.lit k.l) := by
      rw [hview, get_lit _ h hh g8, Tbl.node?, hk]; rfl
    exact ⟨a, by rw [bbNodeA_run F _ a _ hv]; rfl, hR⟩
  simp only [g8, ↓reduceIte, reduceCtorEq] at hb

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
  cases hw : bbW n (mclearMem m) h with
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
theorem bbMemo_refines (p : Prog) (hpf : p.lookup "memo_find" = some memoFind)
    (hps : p.lookup "memo_set" = some memoSet) (hpc : p.lookup "memo_clear" = some memoClear)
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
