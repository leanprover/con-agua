import ConAgua.Arena.View
import ConAgua.Arena.ExprMk

/-!
# The derived range relation `DerR`, and the `mk_*` constructors under `ArenaR ∧ DerR`

`DerR m a`: for every expression table and tier, one derived word per node (`Tbl.der`), whose
range field (`bvarOfData`) is `satSucc i` for `bvar i`, `0` for the other leaves, and the word the
L memory holds at `XDER[2 i + t]` for the five compound tables (`ExprMk.lean`). Under `ArenaR` and
`DerR`, `der_b(h)` is `bvarOfData (a.store.derived (decE h))` (`derBW_ok`), and each `mk_*` refines
the arena's `internE` keeping both relations (`mkApp_ok`, …). `ArenaD m a` is the pair.

`DerR` is not a field of `ArenaR`: the compound tables' `intern_*` called directly would add a
node with no range in L. Walks that read the derived word (`liftLooseBVarsGo`, `instantiate1Go`, …)
run under `ArenaD` and intern through `mk_*`.
-/

open ConRon.Arena ConLeche
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

/-! ## The relation -/

/-- The derived words of one tier of one table: one per node, and `P i x (derAt i)` of node `i`. -/
def DerT {α : Type} [BEq α] [Hashable α] (tb : Tbl α EIdx UInt64) (P : Nat → α → UInt64 → Prop) :
    Prop :=
  tb.der.size = tb.nodes.size ∧ ∀ i x, tb.nodes[i]? = some x → P i x (tb.derAt i)

/-- The same for both tiers of a table `g`; `P` gets the tier word. -/
def DerT2 {α : Type} [BEq α] [Hashable α] (a : AState) (g : ETables → Tbl α EIdx UInt64)
    (P : Word → Nat → α → UInt64 → Prop) : Prop :=
  DerT (g a.store.pers) (P 0) ∧ DerT (g a.store.scr) (P 1)

/-- A leaf other than `bvar`: range `0`. -/
def zP {α : Type} : Word → Nat → α → UInt64 → Prop := fun _ _ _ d => bvarOfData d = 0

/-- `bvar i`: range `satSucc i`. -/
def bvP : Word → Nat → BVarNode → UInt64 → Prop := fun _ _ x d => bvarOfData d = satSucc x.i

/-- A compound table: the range is in L at `A[2 i + t]`. -/
def cP {α : Type} (A : ArrId) (m : Mem) : Word → Nat → α → UInt64 → Prop :=
  fun t i _ d => rdW (m.arr64 A) (UInt64.ofNat i * 2 + t) = bvarOfData d

/-- **The derived range relation.** -/
structure DerR (m : Mem) (a : AState) : Prop where
  bvar : DerT2 a (·.bvars) bvP
  fvar : DerT2 a (·.fvars) zP
  sort : DerT2 a (·.sorts) zP
  const : DerT2 a (·.consts) zP
  lit : DerT2 a (·.lits) zP
  app : DerT2 a (·.apps) (cP ADER m)
  lam : DerT2 a (·.lams) (cP LADER m)
  forallE : DerT2 a (·.foralls) (cP FADER m)
  letE : DerT2 a (·.lets) (cP LEDER m)
  proj : DerT2 a (·.projs) (cP PJDER m)

/-- **The arena relation with the derived ranges.** -/
def ArenaD (m : Mem) (a : AState) : Prop := ArenaR m a ∧ DerR m a

/-! ## Facts of one tier -/

/-- The tier a tier word names. -/
def tierOf (a : AState) (t : Word) : ETables := if t = 0 then a.store.pers else a.store.scr

theorem derT2_tier {α : Type} [BEq α] [Hashable α] {a : AState} {g : ETables → Tbl α EIdx UInt64}
    {P : Word → Nat → α → UInt64 → Prop} (hD : DerT2 a g P) (t : Word) (ht : t ≤ 1) :
    DerT (g (tierOf a t)) (P t) := by
  rcases word_le_one t ht with rfl | rfl
  · simpa [tierOf] using hD.1
  · simpa [tierOf] using hD.2

/-- Past the nodes, the derived word is `0`. -/
theorem derT_out {α : Type} [BEq α] [Hashable α] {tb : Tbl α EIdx UInt64}
    {P : Nat → α → UInt64 → Prop} (hD : DerT tb P) (i : Nat) (hi : tb.nodes.size ≤ i) :
    tb.derAt i = 0 := by
  simp only [Tbl.derAt, Array.getD_eq_getD_getElem?]
  rw [Array.getElem?_eq_none (by rw [hD.1]; exact hi)]; rfl

/-- A leaf table's range is `0` everywhere. -/
theorem derT_zero {α : Type} [BEq α] [Hashable α] {tb : Tbl α EIdx UInt64} {t : Word}
    (hD : DerT tb (zP t)) (i : Nat) : bvarOfData (tb.derAt i) = 0 := by
  by_cases hi : i < tb.nodes.size
  · exact hD.2 i _ (Array.getElem?_eq_getElem hi)
  · rw [derT_out hD i (by omega)]; rfl

/-- The count of a tier in L is its node count. -/
theorem cnt_tier {α δ : Type} {k : IdxKind} [BEq α] [Hashable α] (S : Schema)
    (R : Mem → Word → Word → α → Prop) (hs : Mem → Word → Word → Word) (m : Mem) (on : Bool)
    (P Q : Tbl α (Idx k) δ) (hR : StoreR S R hs m on P Q) (t : Word) (ht : t ≤ 1) :
    (cntW S m t).toNat = (if t = 0 then P else Q).nodes.size := by
  rcases word_le_one t ht with rfl | rfl
  · simpa using hR.2.2.1.1
  · simpa using hR.2.2.2.1

/-! ## `derived` under `ArenaR` -/

theorem decE_tierW (h : Word) : (decE h).isPersistent = (tierW h == 0) := by
  simp only [decE, Idx.isPersistent, Idx.tier, tierW]
  have := bit27_toNat h
  have : (h.toUInt32 / 134217728 % 2).toNat = h.toNat / 2 ^ 27 % 2 := by
    simp [UInt32.toNat_mod, UInt32.toNat_div, UInt64.toNat_toUInt32]; omega
  grind

section derived
variable (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word)

include hR in
theorem derived_closed (hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) :
    a.store.derived (decE h) = 0 := by
  have hfl := hR.app.2.1
  have hon : a.store.scratchOn = false := by
    rw [← hfl]; simp [hs.2]
  simp [EStore.derived, decE_tierW, hs.1, hon]

include hR in
theorem derived_tier (hs : ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0)) :
    a.store.derived (decE h) = (tierOf a (tierW h)).derAt (decE h) := by
  have hfl := hR.app.2.1
  unfold EStore.derived tierOf
  rw [decE_tierW]
  by_cases ht : tierW h = 0
  · simp [ht]
  · have hon : a.store.scratchOn = true := by
      rw [← hfl]; simp only [bne_iff_ne, ne_eq]; exact fun h1 => hs ⟨ht, h1⟩
    simp [ht, hon]

end derived

section derAt
variable (tb : ETables) (h : Word) (hh : h.toNat < 2 ^ 32)
include hh

theorem derAt_bvar (hg : h >>> 28 = 0) : tb.derAt (decE h) = tb.bvars.derAt (idxW h).toNat := by
  simp [ETables.derAt, decE_tag h hh, hg, decE_idx h, ETag.bvar]
theorem derAt_fvar (hg : h >>> 28 = 1) : tb.derAt (decE h) = tb.fvars.derAt (idxW h).toNat := by
  simp [ETables.derAt, decE_tag h hh, hg, decE_idx h, ETag.bvar, ETag.fvar]
theorem derAt_sort (hg : h >>> 28 = 2) : tb.derAt (decE h) = tb.sorts.derAt (idxW h).toNat := by
  simp [ETables.derAt, decE_tag h hh, hg, decE_idx h, ETag.bvar, ETag.fvar, ETag.sort]
theorem derAt_const (hg : h >>> 28 = 3) : tb.derAt (decE h) = tb.consts.derAt (idxW h).toNat := by
  simp [ETables.derAt, decE_tag h hh, hg, decE_idx h, ETag.bvar, ETag.fvar, ETag.sort, ETag.const]
theorem derAt_app (hg : h >>> 28 = 4) : tb.derAt (decE h) = tb.apps.derAt (idxW h).toNat := by
  simp [ETables.derAt, decE_tag h hh, hg, decE_idx h, ETag.bvar, ETag.fvar, ETag.sort, ETag.const,
    ETag.app]
theorem derAt_lam (hg : h >>> 28 = 5) : tb.derAt (decE h) = tb.lams.derAt (idxW h).toNat := by
  simp [ETables.derAt, decE_tag h hh, hg, decE_idx h, ETag.bvar, ETag.fvar, ETag.sort, ETag.const,
    ETag.app, ETag.lam]
theorem derAt_forall (hg : h >>> 28 = 6) : tb.derAt (decE h) = tb.foralls.derAt (idxW h).toNat := by
  simp [ETables.derAt, decE_tag h hh, hg, decE_idx h, ETag.bvar, ETag.fvar, ETag.sort, ETag.const,
    ETag.app, ETag.lam, ETag.forallE]
theorem derAt_let (hg : h >>> 28 = 7) : tb.derAt (decE h) = tb.lets.derAt (idxW h).toNat := by
  simp [ETables.derAt, decE_tag h hh, hg, decE_idx h, ETag.bvar, ETag.fvar, ETag.sort, ETag.const,
    ETag.app, ETag.lam, ETag.forallE, ETag.letE]
theorem derAt_lit (hg : h >>> 28 = 8) : tb.derAt (decE h) = tb.lits.derAt (idxW h).toNat := by
  simp [ETables.derAt, decE_tag h hh, hg, decE_idx h, ETag.bvar, ETag.fvar, ETag.sort, ETag.const,
    ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit]
theorem derAt_proj (hg : h >>> 28 = 9) : tb.derAt (decE h) = tb.projs.derAt (idxW h).toNat := by
  simp [ETables.derAt, decE_tag h hh, hg, decE_idx h, ETag.bvar, ETag.fvar, ETag.sort, ETag.const,
    ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj]
theorem derAt_other (h0 : h >>> 28 ≠ 0) (h1 : h >>> 28 ≠ 1) (h2 : h >>> 28 ≠ 2)
    (h3 : h >>> 28 ≠ 3) (h4 : h >>> 28 ≠ 4) (h5 : h >>> 28 ≠ 5) (h6 : h >>> 28 ≠ 6)
    (h7 : h >>> 28 ≠ 7) (h8 : h >>> 28 ≠ 8) (h9 : h >>> 28 ≠ 9) : tb.derAt (decE h) = 0 := by
  have hl : (h >>> 28).toNat < 16 := by
    simp only [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; simp; omega
  have ne : ∀ k : Nat, h >>> 28 ≠ UInt64.ofNat k → (h >>> 28).toNat ≠ k := by
    intro k hk e; apply hk; apply UInt64.toNat_inj.mp; simp [e]; omega
  have := ne 0 h0; have := ne 1 h1; have := ne 2 h2; have := ne 3 h3; have := ne 4 h4
  have := ne 5 h5; have := ne 6 h6; have := ne 7 h7; have := ne 8 h8; have := ne 9 h9
  have hT : ((h >>> 28).toUInt32).toNat = (h >>> 28).toNat := by
    simp only [UInt64.toNat_toUInt32]; omega
  have hk : ∀ k : UInt32, k.toNat < 10 → (h >>> 28).toUInt32 ≠ k := fun k hk e => by
    have := congrArg UInt32.toNat e; omega
  simp only [ETables.derAt, decE_tag h hh, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app,
    ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj, beq_iff_eq, hk 0 (by decide),
    hk 1 (by decide), hk 2 (by decide), hk 3 (by decide), hk 4 (by decide), hk 5 (by decide),
    hk 6 (by decide), hk 7 (by decide), hk 8 (by decide), hk 9 (by decide), ↓reduceIte]

end derAt

/-! ## `der_b` is the range field of `derived` -/

theorem satSuccW_eq (w : Word) : satSuccW w = satSucc w.toNat := by
  simp only [satSuccW, satSucc, satRange]
  by_cases h : w < 32767
  · have : w.toNat < 32767 := h
    simp only [h, ↓reduceIte, UInt64.mul_one, show ¬ (32767 : Word) ≤ w from UInt64.not_le.mpr h,
      UInt64.mul_zero, UInt64.add_zero]
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add]; simp; omega
  · have : ¬ w.toNat < 32767 := h
    simp only [h, ↓reduceIte, UInt64.mul_zero, UInt64.zero_add,
      show (32767 : Word) ≤ w from UInt64.not_lt.mp h, UInt64.mul_one]
    apply UInt64.toNat_inj.mp; simp; omega

theorem ofNat_idxW (h : Word) : UInt64.ofNat (idxW h).toNat = idxW h := by simp

/-- A compound tier's range, from `DerT` and the L count. -/
theorem derC {α : Type} [BEq α] [Hashable α] (A : ArrId) (m : Mem) (tb : Tbl α EIdx UInt64)
    (t : Word) (hD : DerT tb (cP A m t)) (i : Word) (hc : (i.toNat < tb.nodes.size)) :
    rdW (m.arr64 A) (i * 2 + t) = bvarOfData (tb.derAt i.toNat) := by
  obtain ⟨x, hx⟩ : ∃ x, tb.nodes[i.toNat]? = some x := ⟨_, Array.getElem?_eq_getElem hc⟩
  have := hD.2 _ x hx
  simpa only [cP, UInt64.ofNat_toNat] using this

/-- **`der_b(h)` is the range field of the arena's derived word.** -/
theorem derBW_ok (m : Mem) (a : AState) (hR : ArenaR m a) (hD : DerR m a) (h : Word)
    (hh : h.toNat < 2 ^ 32) : derBW m h = bvarOfData (a.store.derived (decE h)) := by
  have ht := tierW_le h
  unfold derBW
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [ite_eq_left hs, derived_closed m a hR h hs]; rfl
  rw [ite_eq_right hs, derived_tier m a hR h hs]
  -- a compound tag: the count, then the L word
  have comp : ∀ {α : Type} [BEq α] [Hashable α] (S : Schema) (R : Mem → Word → Word → α → Prop)
      (hsh : Mem → Word → Word → Word) (g : ETables → Tbl α EIdx UInt64) (A : ArrId)
      (hT : StoreR S R hsh m a.store.scratchOn (g a.store.pers) (g a.store.scr))
      (hd : DerT2 a g (cP A m)),
      (if cntW S m (tierW h) ≤ idxW h then (0 : Word) else rdW (m.arr64 A) (idxW h * 2 + tierW h)) =
        bvarOfData ((g (tierOf a (tierW h))).derAt (idxW h).toNat) := by
    intro α _ _ S R hsh g A hT hd
    have hc := cnt_tier S R hsh m _ _ _ hT (tierW h) ht
    have hD' := derT2_tier hd (tierW h) ht
    have hg : (if tierW h = 0 then g a.store.pers else g a.store.scr) = g (tierOf a (tierW h)) := by
      simp only [tierOf]; split <;> rfl
    rw [hg] at hc
    split
    · rename_i hle
      rw [derT_out hD' _ (by rw [← hc]; exact hle)]; rfl
    · rename_i hlt
      exact derC A m _ _ hD' _ (by rw [← hc]; exact UInt64.not_le.mp hlt)
  by_cases g0 : h >>> 28 = 0
  · simp only [g0, ↓reduceIte]
    rw [derAt_bvar _ h hh g0]
    have hc := cnt_tier bvarSch BRecRel bhash m _ _ _ hR.bvar (tierW h) ht
    have hD' := derT2_tier hD.bvar (tierW h) ht
    have hg : (if tierW h = 0 then a.store.pers.bvars else a.store.scr.bvars) =
        (tierOf a (tierW h)).bvars := by simp only [tierOf]; split <;> rfl
    rw [hg] at hc
    split
    · rename_i hle
      rw [derT_out hD' _ (by rw [← hc]; exact hle)]; rfl
    · rename_i hlt
      obtain ⟨k, hk, hkr⟩ := node_of m a h bvarSch BRecRel bhash (·.bvars) _ hR.bvar
        (UInt64.not_le.mp hlt)
      have hk' : (tierOf a (tierW h)).bvars.nodes[(idxW h).toNat]? = some k := by
        simpa [tierOf, apply_ite] using hk
      rw [hD'.2 _ k hk', satSuccW_eq]
      simp only [BRecRel] at hkr; rw [hkr]
  simp only [g0, ↓reduceIte]
  by_cases g4 : h >>> 28 = 4
  · simp only [g4, ↓reduceIte]; rw [derAt_app _ h hh g4]
    exact comp appSch ARecRel ahash (·.apps) ADER hR.app hD.app
  simp only [g4, ↓reduceIte]
  by_cases g5 : h >>> 28 = 5
  · simp only [g5, ↓reduceIte]; rw [derAt_lam _ h hh g5]
    exact comp lamSch LaRecRel lahash (·.lams) LADER hR.lam hD.lam
  simp only [g5, ↓reduceIte]
  by_cases g6 : h >>> 28 = 6
  · simp only [g6, ↓reduceIte]; rw [derAt_forall _ h hh g6]
    exact comp forallSch FaRecRel fahash (·.foralls) FADER hR.forallE hD.forallE
  simp only [g6, ↓reduceIte]
  by_cases g7 : h >>> 28 = 7
  · simp only [g7, ↓reduceIte]; rw [derAt_let _ h hh g7]
    exact comp letSch LeRecRel lehash (·.lets) LEDER hR.letE hD.letE
  simp only [g7, ↓reduceIte]
  by_cases g9 : h >>> 28 = 9
  · simp only [g9, ↓reduceIte]; rw [derAt_proj _ h hh g9]
    exact comp projSch PJRecRel pjhash (·.projs) PJDER hR.proj hD.proj
  simp only [g9, ↓reduceIte]
  have tz := fun {α : Type} [BEq α] [Hashable α] (g : ETables → Tbl α EIdx UInt64)
    (hd : DerT2 a g zP) => derT_zero (derT2_tier hd (tierW h) ht) (idxW h).toNat
  by_cases g1 : h >>> 28 = 1
  · rw [derAt_fvar _ h hh g1, tz (·.fvars) hD.fvar]
  by_cases g2 : h >>> 28 = 2
  · rw [derAt_sort _ h hh g2, tz (·.sorts) hD.sort]
  by_cases g3 : h >>> 28 = 3
  · rw [derAt_const _ h hh g3, tz (·.consts) hD.const]
  by_cases g8 : h >>> 28 = 8
  · rw [derAt_lit _ h hh g8, tz (·.lits) hD.lit]
  rw [derAt_other _ h hh g0 g1 g2 g3 g4 g5 g6 g7 g8 g9]; rfl

/-! ## The twin's interning, by cases -/

section proto
variable {α : Type} [BEq α] [Hashable α]

/-- The run of `protoRun`: a hit (state unchanged), or an append to the tier the store is in,
returning the handle of the new node. -/
theorem protoRun_cases (L : Lens α UInt64 .expr) (key : α) (tag : UInt32) (pf : Option EIdx)
    (d : UInt64) (err : CheckError) (a a' : AState) (y : EIdx)
    (h : protoRun L key tag pf d err a = .ok (y, a')) :
    a' = a ∨
    (L.on a = false ∧ (L.getP a).nodes.size < 2 ^ 27 ∧
      y = decI (hdW tag.toUInt64 0 (UInt64.ofNat (L.getP a).nodes.size)) ∧
      a' = L.setP a ((L.getP a).push key d y)) ∨
    (L.on a = true ∧ (L.getS a).nodes.size < 2 ^ 27 ∧
      y = decI (hdW tag.toUInt64 1 (UInt64.ofNat (L.getS a).nodes.size)) ∧
      a' = L.setS a ((L.getS a).push key d y)) := by
  unfold protoRun at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact .inl h.2.symm
  · split at h
    · rename_i hon
      split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact .inl h.2.symm
      · split at h
        · rename_i hc
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine .inr (.inr ⟨hon, by simpa [Tbl.size, Idx.idxCap] using hc, ?_, ?_⟩) <;>
            simp only [show Idx.tierS = UInt32.ofNat 1 from rfl, mk_eq, Tbl.size] <;> rfl
        · simp at h
    · rename_i hon
      split at h
      · rename_i hc
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine .inr (.inl ⟨by simpa using hon, by simpa [Tbl.size, Idx.idxCap] using hc, ?_, ?_⟩) <;>
          simp only [show Idx.tierP = UInt32.ofNat 0 from rfl, mk_eq, Tbl.size] <;> rfl
      · simp at h

end proto

/-! ## Handle words of a new node -/

theorem idxW_tierW_of_decE (r w : Word) (h : decE r = decE w) :
    idxW r = idxW w ∧ tierW r = tierW w := by
  have e : r.toUInt32 = w.toUInt32 := by
    simp only [decE] at h; exact Idx.ofWord.inj h
  have e' : r.toNat % 2 ^ 32 = w.toNat % 2 ^ 32 := by
    have := congrArg UInt32.toNat e; simpa [UInt64.toNat_toUInt32] using this
  constructor
  · apply UInt64.toNat_inj.mp
    simp only [idxW, UInt64.toNat_and]
    have : (134217727 : Word).toNat = 2 ^ 27 - 1 := rfl
    rw [this, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]; omega
  · apply UInt64.toNat_inj.mp
    simp only [tierW, bit27_toNat]; omega

theorem idxW_hdW (g t n : Word) (_hg : g.toNat < 16) (ht : t ≤ 1) (hn : n.toNat < 2 ^ 27) :
    idxW (hdW g t n) = n ∧ tierW (hdW g t n) = t := by
  have ht' : t.toNat ≤ 1 := ht
  constructor
  · apply UInt64.toNat_inj.mp
    simp only [idxW, hdW, UInt64.toNat_and]
    have : (134217727 : Word).toNat = 2 ^ 27 - 1 := rfl
    rw [this, Nat.and_two_pow_sub_one_eq_mod]
    simp only [UInt64.toNat_add, UInt64.toNat_mul]
    simp; omega
  · apply UInt64.toNat_inj.mp
    simp only [tierW, bit27_toNat, hdW, UInt64.toNat_add, UInt64.toNat_mul]
    simp; omega

/-- The handle words of the node an append made: its index and tier. -/
theorem new_handle (r : Word) (g : UInt32) (t : Word) (n : Nat) (hg : g.toNat < 16) (ht : t ≤ 1)
    (hn : n < 2 ^ 27) (h : decE r = decI (hdW g.toUInt64 t (UInt64.ofNat n))) :
    idxW r = UInt64.ofNat n ∧ tierW r = t := by
  obtain ⟨h1, h2⟩ := idxW_tierW_of_decE r _ h
  obtain ⟨h3, h4⟩ := idxW_hdW g.toUInt64 t (UInt64.ofNat n) (by simpa using hg) ht
    (by simp; omega)
  exact ⟨h1.trans h3, h2.trans h4⟩

/-! ## One tier's derived words across a change -/

section derT
variable {α : Type} [BEq α] [Hashable α]

theorem lt_of_getElem? {β : Type} {xs : Array β} {i : Nat} {x : β} (h : xs[i]? = some x) :
    i < xs.size := by
  rcases Nat.lt_or_ge i xs.size with hl | hl
  · exact hl
  · rw [Array.getElem?_eq_none hl] at h; cases h

theorem derT_mono {tb : Tbl α EIdx UInt64} {P P' : Nat → α → UInt64 → Prop} (hD : DerT tb P)
    (h : ∀ i x d, i < tb.nodes.size → P i x d → P' i x d) : DerT tb P' :=
  ⟨hD.1, fun i x hx => h i x _ (lt_of_getElem? hx) (hD.2 i x hx)⟩

/-- An append keeps `DerT` if the new node's derived word satisfies `P`. -/
theorem derT_push {tb : Tbl α EIdx UInt64} {P : Nat → α → UInt64 → Prop} (hD : DerT tb P)
    (key : α) (d : UInt64) (y : EIdx) (hP : P tb.nodes.size key d) :
    DerT (tb.push key d y) P := by
  obtain ⟨hs, hn⟩ := hD
  have hp : (tb.push key d y).nodes = tb.nodes.push key ∧ (tb.push key d y).der = tb.der.push d := by
    cases tb; exact ⟨rfl, rfl⟩
  refine ⟨by rw [hp.1, hp.2]; simp [hs], fun i x hx => ?_⟩
  have hda : (tb.push key d y).derAt i = (tb.der.push d).getD i 0 := by
    simp only [Tbl.derAt, hp.2]; rfl
  rw [hp.1] at hx
  rw [hda]
  by_cases hi : i < tb.nodes.size
  · have hi' : i < tb.der.size := by rw [hs]; exact hi
    have := hn i x (by
      rw [Array.getElem?_eq_getElem hi]; rw [Array.getElem?_push_lt hi] at hx; exact hx)
    have e1 : (tb.der.push d).getD i 0 = tb.der[i] := by
      simp [Array.getD, hi', Array.getElem_push_lt hi'] <;> intro h <;> omega
    have e2 : tb.derAt i = tb.der[i] := by simp [Tbl.derAt, Array.getD, hi']
    rw [e1]; rw [e2] at this; exact this
  · have hi' : i = tb.nodes.size := by
      have := lt_of_getElem? hx; simp at this; omega
    subst hi'
    rw [Array.getElem?_push_size] at hx
    obtain rfl := Option.some.inj hx
    have e1 : (tb.der.push d).getD tb.nodes.size 0 = d := by simp [Array.getD, ← hs]
    rw [e1]; exact hP

/-- `cP` across a memory change that keeps the entries' words. -/
theorem derT_cP {tb : Tbl α EIdx UInt64} {A : ArrId} {m m' : Mem} {t : Word}
    (hD : DerT tb (cP A m t))
    (h : ∀ i, i < tb.nodes.size → rdW (m'.arr64 A) (UInt64.ofNat i * 2 + t) =
      rdW (m.arr64 A) (UInt64.ofNat i * 2 + t)) : DerT tb (cP A m' t) :=
  derT_mono hD fun i _ _ hi hP => by simp only [cP] at hP ⊢; rw [h i hi]; exact hP

end derT

/-! ## The frame of `DerR` -/

/-- **`DerR` survives a writer of other arrays.** -/
theorem DerR.frame (m m' : Mem) (a : AState) (hD : DerR m a)
    (h : ∀ B, B = ADER ∨ B = LADER ∨ B = FADER ∨ B = LEDER ∨ B = PJDER → m'.arr64 B = m.arr64 B) :
    DerR m' a := by
  have f := fun (B : ArrId) (hB : B = ADER ∨ B = LADER ∨ B = FADER ∨ B = LEDER ∨ B = PJDER)
    {α : Type} [BEq α] [Hashable α] (g : ETables → Tbl α EIdx UInt64) (hd : DerT2 a g (cP B m)) =>
    (⟨derT_cP hd.1 (fun i _ => by rw [h B hB]), derT_cP hd.2 (fun i _ => by rw [h B hB])⟩ :
      DerT2 a g (cP B m'))
  exact ⟨hD.bvar, hD.fvar, hD.sort, hD.const, hD.lit, f _ (by simp) _ hD.app,
    f _ (by simp) _ hD.lam, f _ (by simp) _ hD.forallE, f _ (by simp) _ hD.letE,
    f _ (by simp) _ hD.proj⟩

theorem DerR.frameM (A : List ArrId) (C : List Word) (m m' : Mem) (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, b < 42 ∨ 46 < b) (a : AState) (hD : DerR m a) : DerR m' a :=
  DerR.frame m m' a hD fun B hB => hf.1 B (fun h => by
    have := hA B h; rcases hB with rfl | rfl | rfl | rfl | rfl <;> revert this <;> decide) (by
    rcases hB with rfl | rfl | rfl | rfl | rfl <;> decide)

/-! ## The range field of a new node's derived word -/

theorem maxW_eq (x y : Word) : maxW x y = max x y := by
  apply UInt64.toNat_inj.mp; rw [maxW_toNat, toNat_max]

theorem satPredW_eq (x : Word) : satPredW x = satPred x := by
  simp only [satPredW, satPred]
  by_cases h1 : x = 32767
  · subst h1; decide
  by_cases h0 : x = 0
  · subst h0; decide
  have : 0 < x := by
    have : x.toNat ≠ 0 := fun h => h0 (UInt64.toNat_inj.mp (by simpa using h))
    exact UInt64.lt_iff_toNat_lt.mpr (by simp; omega)
  simp [h1, h0, this]

theorem bvar_lt (x : UInt64) : (bvarOfData x).toNat < 32768 := bvarOfData_lt x
theorem fvar_lt (x : UInt64) : (fvarOfData x).toNat < 32768 := fvarOfData_lt x

theorem bvar_derBVar (st : EStore) (i : Nat) :
    bvarOfData (st.derOfView (.bvar i)) = satSucc i := by
  simp only [EStore.derOfView, EStore.derOfBVar]
  exact bvarOfData_pack _ _ _ _ (satSucc_lt i) (by decide)

theorem bvar_derApp (st : EStore) (f x : EIdx) :
    bvarOfData (st.derOfView (.app f x)) =
      max (bvarOfData (st.derived f)) (bvarOfData (st.derived x)) := by
  simp only [EStore.derOfView, EStore.derOfApp]
  exact bvarOfData_pack _ _ _ _ (max_lt_32768 (bvar_lt _) (bvar_lt _))
    (max_lt_32768 (fvar_lt _) (fvar_lt _))

theorem bvar_derBind (st : EStore) (tag : UInt64) (ty b : EIdx) :
    bvarOfData (st.derOfBindAt tag ty b) =
      max (bvarOfData (st.derived ty)) (satPred (bvarOfData (st.derived b))) := by
  simp only [EStore.derOfBindAt, derOfBind]
  exact bvarOfData_pack _ _ _ _ (max_lt_32768 (bvar_lt _) (satPred_lt (bvar_lt _)))
    (max_lt_32768 (fvar_lt _) (fvar_lt _))

theorem bvar_derLet (st : EStore) (ty v b : EIdx) :
    bvarOfData (st.derOfView (.letE ty v b)) =
      max (max (bvarOfData (st.derived ty)) (bvarOfData (st.derived v)))
        (satPred (bvarOfData (st.derived b))) := by
  simp only [EStore.derOfView, EStore.derOfLetAt, derOfLet]
  exact bvarOfData_pack _ _ _ _
    (max_lt_32768 (max_lt_32768 (bvar_lt _) (bvar_lt _)) (satPred_lt (bvar_lt _)))
    (max_lt_32768 (max_lt_32768 (fvar_lt _) (fvar_lt _)) (fvar_lt _))

theorem bvar_derProj (st : EStore) (n : NIdx) (i : Nat) (e : EIdx) :
    bvarOfData (st.derOfView (.proj n i e)) = bvarOfData (st.derived e) := by
  simp only [EStore.derOfView, EStore.derOfProj]
  exact bvarOfData_pack _ _ _ _ (bvar_lt _) (fvar_lt _)

/-- A leaf other than `bvar` (`fvar`, `sort`, `const`, `lit`): range `0` (`zP`). -/
theorem bvar_derFVar (st : EStore) (idx : Nat) (ty : EIdx) :
    bvarOfData (st.derOfView (.fvar idx ty)) = 0 := by
  simp only [EStore.derOfView, EStore.derOfFVar]
  exact bvarOfData_pack _ _ _ _ (by decide) (satSucc_lt idx)

theorem bvar_derSort (st : EStore) (u : LIdx) : bvarOfData (st.derOfView (.sort u)) = 0 := by
  simp only [EStore.derOfView, EStore.derOfSort]
  exact bvarOfData_pack _ _ _ _ (by decide) (by decide)

theorem bvar_derConst (st : EStore) (n : NIdx) (us : LsIdx) :
    bvarOfData (st.derOfView (.const n us)) = 0 := by
  simp only [EStore.derOfView, EStore.derOfConst]
  exact bvarOfData_pack _ _ _ _ (by decide) (by decide)

theorem bvar_derLit (st : EStore) (l : ConLeche.Literal) :
    bvarOfData (st.derOfView (.lit l)) = 0 := by
  simp only [EStore.derOfView, EStore.derOfLit]
  exact bvarOfData_pack _ _ _ _ (by decide) (by decide)

/-- The guard of every `mk_*`: the handle words are below `2^32`. -/
theorem or_shr32 (f x : Word) (h : (f ||| x) >>> 32 = 0) : f.toNat < 2 ^ 32 ∧ x.toNat < 2 ^ 32 := by
  have := congrArg UInt64.toNat h
  simp only [UInt64.toNat_shiftRight, UInt64.toNat_or, Nat.shiftRight_eq_div_pow] at this
  simp at this
  exact ⟨Nat.lt_of_le_of_lt Nat.left_le_or this, Nat.lt_of_le_of_lt Nat.right_le_or this⟩

theorem or_lt32 (f x : Word) (h : (f ||| x).toNat < 2 ^ 32) : f.toNat < 2 ^ 32 ∧ x.toNat < 2 ^ 32 := by
  rw [UInt64.toNat_or] at h
  exact ⟨Nat.lt_of_le_of_lt Nat.left_le_or h, Nat.lt_of_le_of_lt Nat.right_le_or h⟩

/-! ## The tail of a `mk_*`, generically -/

theorem derPutW_frame (A : ArrId) (hA : A ≠ CTL) (c : Word) (m₁ m' : Mem) (s r d : Word)
    (h : derPutW A c m₁ s r d = some m') : MemFrame [A] [] m₁ m' := by
  unfold derPutW at h
  split at h
  · cases h; exact MemFrame.refl _ _ _
  split at h
  · cases h
  · cases h; exact MemFrame.set64 m₁ A hA _ _

/-- Two record positions `2 i + t` differ when the nodes or the tiers do. -/
theorem ix_ne (i j : Nat) (t u : Word) (hi : i < 2 ^ 27) (hj : j < 2 ^ 27) (ht : t ≤ 1)
    (hu : u ≤ 1) (h : i ≠ j ∨ t ≠ u) : UInt64.ofNat i * 2 + t ≠ UInt64.ofNat j * 2 + u := by
  intro e
  have e' := congrArg UInt64.toNat e
  have ht' : t.toNat ≤ 1 := ht
  have hu' : u.toNat ≤ 1 := hu
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat'] at e'
  simp at e'
  try rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)] at e'
  rcases h with h | h
  · omega
  · exact h (UInt64.toNat_inj.mp (by omega))

section derMk
variable {α : Type} [BEq α] [Hashable α] (S : Schema) (hS : S.WF)
  (R : Mem → Word → Word → α → Prop) (hsh : Mem → Word → Word → Word)
  (L : Lens α UInt64 .expr) (g : ETables → Tbl α EIdx UInt64)
  (hgP : ∀ a, L.getP a = g a.store.pers) (hgS : ∀ a, L.getS a = g a.store.scr)
  (hPP : ∀ a t, g (L.setP a t).store.pers = t) (hPS : ∀ a t, g (L.setP a t).store.scr = g a.store.scr)
  (hSP : ∀ a t, g (L.setS a t).store.pers = g a.store.pers)
  (hSS : ∀ a t, g (L.setS a t).store.scr = t)

theorem cnt2_eq (m : Mem) : cnt2 m S.ca = cntW S m 0 + cntW S m 1 := by
  simp [cnt2, cntW]

include hS hgP hgS hPP hPS hSP hSS in
/-- **The tail of a `mk_*`**: after the interning (`m` to `m₁`, the arena `a` to `a'`, result
`r`) and `derPutW`, the compound table's `DerT2` holds of `a'` and `m'`, if the range written is
the new node's (`dd = bvarOfData d`); `m'` differs from `m₁` only in `A`. -/
theorem derMk (A : ArrId) (m m₁ m' : Mem) (a a' : AState) (key : α) (d : UInt64)
    (y : EIdx) (r dd : Word)
    (hT : StoreR S R hsh m a.store.scratchOn (g a.store.pers) (g a.store.scr))
    (hT₁ : StoreR S R hsh m₁ a'.store.scratchOn (g a'.store.pers) (g a'.store.scr))
    (hd : DerT2 a g (cP A m)) (hfr : m₁.arr64 A = m.arr64 A)
    (hst : a' = a ∨
      (L.on a = false ∧ (L.getP a).nodes.size < 2 ^ 27 ∧
        y = decI (hdW S.tag.toUInt64 0 (UInt64.ofNat (L.getP a).nodes.size)) ∧
        a' = L.setP a ((L.getP a).push key d y)) ∨
      (L.on a = true ∧ (L.getS a).nodes.size < 2 ^ 27 ∧
        y = decI (hdW S.tag.toUInt64 1 (UInt64.ofNat (L.getS a).nodes.size)) ∧
        a' = L.setS a ((L.getS a).push key d y)))
    (hres : decE r = y) (hdd : dd = bvarOfData d)
    (hput : derPutW A S.ca m₁ (cnt2 m S.ca) r dd = some m') :
    DerT2 a' g (cP A m') := by
  have hfrA : ∀ i t, rdW (m₁.arr64 A) (UInt64.ofNat i * 2 + t) = rdW (m.arr64 A) (UInt64.ofNat i * 2 + t) :=
    fun i t => by rw [hfr]
  have c0 := cnt_tier S R hsh m _ _ _ hT 0 (by decide)
  have c1 := cnt_tier S R hsh m _ _ _ hT 1 (by decide)
  have d0 := cnt_tier S R hsh m₁ _ _ _ hT₁ 0 (by decide)
  have d1 := cnt_tier S R hsh m₁ _ _ _ hT₁ 1 (by decide)
  have b0 := hT.2.2.1.2.1
  have b1 := hT.2.2.2.2.1
  simp only [ite_true, show (1 : Word) ≠ 0 by decide, ite_false] at c0 c1 d0 d1
  have htag := hS.tag
  rcases hst with rfl | ⟨hoff, hsz, hy, rfl⟩ | ⟨hon', hsz, hy, rfl⟩
  · -- a hit: the counts did not move, nothing is written
    have e : cnt2 m₁ S.ca = cnt2 m S.ca := by
      rw [cnt2_eq, cnt2_eq, UInt64.toNat_inj.mp (c0.trans d0.symm),
        UInt64.toNat_inj.mp (c1.trans d1.symm)]
    simp only [derPutW, e, ite_true, Option.some.injEq] at hput
    subst hput
    exact ⟨derT_cP hd.1 (fun i _ => hfrA i 0), derT_cP hd.2 (fun i _ => hfrA i 1)⟩
  · -- an append to the persistent tier
    simp only [hPP, hPS, hgP] at d0 d1
    rw [hgP] at hsz hy
    have hpsz : ((g a.store.pers).push key d y).nodes.size = (g a.store.pers).nodes.size + 1 := by
      cases g a.store.pers; simp [Tbl.push]
    have ne : cnt2 m₁ S.ca ≠ cnt2 m S.ca := by
      intro e
      rw [cnt2_eq, cnt2_eq] at e
      have e' := congrArg UInt64.toNat e
      rw [UInt64.toNat_add, UInt64.toNat_add, d0, d1] at e'
      simp only [hpsz] at e'
      have := (cntW S m 0).toNat_lt; have := (cntW S m 1).toNat_lt; omega
    obtain ⟨hi, ht⟩ := new_handle r S.tag 0 _ htag (by decide) hsz (hres.trans hy)
    simp only [derPutW, ne, ite_false, hi, ht] at hput
    split at hput
    · cases hput
    rename_i hlen
    simp only [Option.some.injEq] at hput
    subst hput
    have hq : (UInt64.ofNat (g a.store.pers).nodes.size * 2 + 0).toNat <
        (m₁.arr64 A).size := by
      have h1 := UInt64.not_le.mp hlen
      rw [UInt64.lt_iff_toNat_lt, len64_eq, UInt64.toNat_ofNat'] at h1
      exact Nat.lt_of_lt_of_le h1 (Nat.mod_le _ _)
    have rd : ∀ i t, i < 2 ^ 27 → t ≤ 1 → (i ≠ (g a.store.pers).nodes.size ∨ t ≠ 0) →
        rdW ((m₁.set64 A (UInt64.ofNat (g a.store.pers).nodes.size * 2 + 0) dd).arr64 A)
          (UInt64.ofNat i * 2 + t) = rdW (m.arr64 A) (UInt64.ofNat i * 2 + t) := by
      intro i t hi ht hne
      rw [rdW_set64, ite_eq_right (fun h => ix_ne _ _ _ _ hsz hi (by decide) ht
        (hne.elim (fun h => .inl (Ne.symm h)) (fun h => .inr (Ne.symm h))) h.2.1), hfrA]
    refine ⟨?_, ?_⟩
    · rw [hPP, hgP]
      refine derT_push (derT_cP hd.1 (fun i hi => rd i 0 (by omega) (by decide) (.inl (by omega))))
        key d y ?_
      simp only [cP]
      rw [rdW_set64, ite_eq_left ⟨rfl, rfl, hq⟩, hdd]
    · rw [hPS]
      exact derT_cP hd.2 (fun i hi => rd i 1 (by omega) (by decide) (.inr (by decide)))
  · -- an append to the scratch tier
    simp only [hSP, hSS, hgS] at d0 d1
    rw [hgS] at hsz hy
    have hpsz : ((g a.store.scr).push key d y).nodes.size = (g a.store.scr).nodes.size + 1 := by
      cases g a.store.scr; simp [Tbl.push]
    have ne : cnt2 m₁ S.ca ≠ cnt2 m S.ca := by
      intro e
      rw [cnt2_eq, cnt2_eq] at e
      have e' := congrArg UInt64.toNat e
      rw [UInt64.toNat_add, UInt64.toNat_add, d0, d1] at e'
      simp only [hpsz] at e'
      have := (cntW S m 0).toNat_lt; have := (cntW S m 1).toNat_lt; omega
    obtain ⟨hi, ht⟩ := new_handle r S.tag 1 _ htag (by decide) hsz (hres.trans hy)
    simp only [derPutW, ne, ite_false, hi, ht] at hput
    split at hput
    · cases hput
    rename_i hlen
    simp only [Option.some.injEq] at hput
    subst hput
    have hq : (UInt64.ofNat (g a.store.scr).nodes.size * 2 + 1).toNat < (m₁.arr64 A).size := by
      have h1 := UInt64.not_le.mp hlen
      rw [UInt64.lt_iff_toNat_lt, len64_eq, UInt64.toNat_ofNat'] at h1
      exact Nat.lt_of_lt_of_le h1 (Nat.mod_le _ _)
    have rd : ∀ i t, i < 2 ^ 27 → t ≤ 1 → (i ≠ (g a.store.scr).nodes.size ∨ t ≠ 1) →
        rdW ((m₁.set64 A (UInt64.ofNat (g a.store.scr).nodes.size * 2 + 1) dd).arr64 A)
          (UInt64.ofNat i * 2 + t) = rdW (m.arr64 A) (UInt64.ofNat i * 2 + t) := by
      intro i t hi ht hne
      rw [rdW_set64, ite_eq_right (fun h => ix_ne _ _ _ _ hsz hi (by decide) ht
        (hne.elim (fun h => .inl (Ne.symm h)) (fun h => .inr (Ne.symm h))) h.2.1), hfrA]
    refine ⟨?_, ?_⟩
    · rw [hSP]
      exact derT_cP hd.1 (fun i hi => rd i 0 (by omega) (by decide) (.inr (by decide)))
    · rw [hSS, hgS]
      refine derT_push (derT_cP hd.2 (fun i hi => rd i 1 (by omega) (by decide) (.inl (by omega))))
        key d y ?_
      simp only [cP]
      rw [rdW_set64, ite_eq_left ⟨rfl, rfl, hq⟩, hdd]

end derMk

/-! ## The `mk_*` constructors refine `internE` under `ArenaD` -/

/-- The twin's run of an interning, by cases (`protoRun_cases` through the run equation). -/
theorem AM.proto_cases {α : Type} [BEq α] [Hashable α] (L : Lens α UInt64 .expr) (op : AM EIdx)
    (key : α) (tag : UInt32) (pf : Option EIdx) (d : UInt64) (err : CheckError) (a : AState)
    (hrun : op.run a = protoRun L key tag pf d err a) (hok : AM.ok op a) :
    AM.st op a = a ∨
    (L.on a = false ∧ (L.getP a).nodes.size < 2 ^ 27 ∧
      AM.res op a = decI (hdW tag.toUInt64 0 (UInt64.ofNat (L.getP a).nodes.size)) ∧
      AM.st op a = L.setP a ((L.getP a).push key d (AM.res op a))) ∨
    (L.on a = true ∧ (L.getS a).nodes.size < 2 ^ 27 ∧
      AM.res op a = decI (hdW tag.toUInt64 1 (UInt64.ofNat (L.getS a).nodes.size)) ∧
      AM.st op a = L.setS a ((L.getS a).push key d (AM.res op a))) :=
  protoRun_cases L key tag pf d err a _ _ (hrun.symm.trans (AM.run_of_ok op a hok))

theorem cP_other {α : Type} [BEq α] [Hashable α] {a : AState} {g : ETables → Tbl α EIdx UInt64}
    {B : ArrId} {m m' : Mem} (hd : DerT2 a g (cP B m)) (h : m'.arr64 B = m.arr64 B) :
    DerT2 a g (cP B m') :=
  ⟨derT_cP hd.1 (fun i _ => by rw [h]), derT_cP hd.2 (fun i _ => by rw [h])⟩

/-- **`mk_app` refines `internE (.app _ _)` under `ArenaD`.** -/
theorem mkApp_ok (m : Mem) (a : AState) (hA : ArenaD m a) (f x r : Word) (m' : Mem)
    (hI : mkAppW m f x = some (r, m')) :
    AM.ok (internE (.app (decE f) (decE x))) a ∧
    ArenaD m' (AM.st (internE (.app (decE f) (decE x))) a) ∧
    AM.res (internE (.app (decE f) (decE x))) a = decE r := by
  obtain ⟨hR, hD⟩ := hA
  unfold mkAppW at hI
  split at hI
  · cases hI
  rename_i hg
  obtain ⟨hf, hx⟩ := or_shr32 f x (by simpa using hg)
  cases hI₁ : ainternW m f x with
  | none => simp [hI₁, mkK] at hI
  | some p =>
  obtain ⟨r₁, m₁⟩ := p
  simp only [hI₁, mkK_some] at hI
  cases hP : derPutW ADER 4 m₁ (cnt2 m 4) r₁ (maxW (derBW m f) (derBW m x)) with
  | none => simp [hP] at hI
  | some m₂ =>
  simp only [hP, Option.some.injEq, Prod.mk.injEq] at hI
  obtain ⟨rfl, rfl⟩ := hI
  obtain ⟨hok, hX, hres⟩ := aintern_correct m a hR.app f x hf hx _ _ hI₁
  have hI₂ := hI₁; rw [ainternW_eq] at hI₂
  have hfr := internM_frame _ appSch_wf _ _ _ _ _ _ _ _ hI₂
  have hcs := AM.proto_cases appLens _ _ _ _ _ _ a (internE_app_run _ _ a) hok
  have hR₁ := hR.lift_app _ _ _ _ hX hfr (AM.st_proto appLens _ _ _ _ _ _ a (internE_app_run _ _ a) hok)
  have hD₁ : DerR m₁ a := DerR.frameM _ _ m m₁ hfr (by simp [appSch, AREC, ASLOT]) a hD
  have hfr₂ := derPutW_frame ADER (by decide) _ _ _ _ _ _ hP
  have hnew := derMk appSch appSch_wf ARecRel ahash appLens (·.apps) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) ADER m m₁ m₂ a _ _ _ _ r₁ _
    hR.app hR₁.app hD.app (hfr.1 ADER (by simp [appSch, ADER, AREC, ASLOT]) (by decide)) hcs hres.symm
    (by rw [maxW_eq, derBW_ok m a hR hD f hf, derBW_ok m a hR hD x hx, bvar_derApp]) hP
  have o := fun B (hB : B ≠ ADER) (hC : B ≠ CTL) => hfr₂.1 B (by simpa using hB) hC
  refine ⟨hok, ⟨ArenaR.frame_above _ _ (by simp [ADER, LADER, FADER, LEDER, PJDER]) (by simp) _ _ hfr₂ _ hR₁, ?_⟩, hres⟩
  rcases hcs with h | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> rw [h] at hnew ⊢ <;>
  exact ⟨hD₁.bvar, hD₁.fvar, hD₁.sort, hD₁.const, hD₁.lit, hnew,
    cP_other hD₁.lam (o LADER (by decide) (by decide)), cP_other hD₁.forallE (o FADER (by decide) (by decide)),
    cP_other hD₁.letE (o LEDER (by decide) (by decide)), cP_other hD₁.proj (o PJDER (by decide) (by decide))⟩

/-- **`mk_lam` refines `internE (.lam _ _)` under `ArenaD`.** -/
theorem mkLam_ok (m : Mem) (a : AState) (hA : ArenaD m a) (t b r : Word) (m' : Mem)
    (hI : mkLamW m t b = some (r, m')) :
    AM.ok (internE (.lam (decE t) (decE b))) a ∧
    ArenaD m' (AM.st (internE (.lam (decE t) (decE b))) a) ∧
    AM.res (internE (.lam (decE t) (decE b))) a = decE r := by
  obtain ⟨hR, hD⟩ := hA
  unfold mkLamW at hI
  split at hI
  · cases hI
  rename_i hg
  obtain ⟨ht, hb⟩ := or_shr32 t b (by simpa using hg)
  cases hI₁ : lainternW m t b with
  | none => simp [hI₁, mkK] at hI
  | some p =>
  obtain ⟨r₁, m₁⟩ := p
  simp only [hI₁, mkK_some] at hI
  cases hP : derPutW LADER 28 m₁ (cnt2 m 28) r₁ (maxW (derBW m t) (satPredW (derBW m b))) with
  | none => simp [hP] at hI
  | some m₂ =>
  simp only [hP, Option.some.injEq, Prod.mk.injEq] at hI
  obtain ⟨rfl, rfl⟩ := hI
  obtain ⟨hok, hX, hres⟩ := laintern_correct m a hR.lam t b ht hb _ _ hI₁
  have hI₂ := hI₁; rw [lainternW_eq] at hI₂
  have hfr := internM_frame _ lamSch_wf _ _ _ _ _ _ _ _ hI₂
  have hcs := AM.proto_cases lamLens _ _ _ _ _ _ a (internE_lam_run _ _ a) hok
  have hR₁ := hR.lift_lam _ _ _ _ hX hfr (AM.st_proto lamLens _ _ _ _ _ _ a (internE_lam_run _ _ a) hok)
  have hD₁ : DerR m₁ a := DerR.frameM _ _ m m₁ hfr (by simp [lamSch, LAREC, LASLOT]) a hD
  have hfr₂ := derPutW_frame LADER (by decide) _ _ _ _ _ _ hP
  have hnew := derMk lamSch lamSch_wf LaRecRel lahash lamLens (·.lams) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) LADER m m₁ m₂ a _ _ _ _ r₁ _
    hR.lam hR₁.lam hD.lam (hfr.1 LADER (by simp [lamSch, LADER, LAREC, LASLOT]) (by decide)) hcs
    hres.symm (by rw [maxW_eq, satPredW_eq, derBW_ok m a hR hD t ht, derBW_ok m a hR hD b hb,
      bvar_derBind]) hP
  have o := fun B (hB : B ≠ LADER) (hC : B ≠ CTL) => hfr₂.1 B (by simpa using hB) hC
  refine ⟨hok, ⟨ArenaR.frame_above _ _ (by simp [ADER, LADER, FADER, LEDER, PJDER]) (by simp) _ _ hfr₂ _ hR₁, ?_⟩, hres⟩
  rcases hcs with h | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> rw [h] at hnew ⊢ <;>
  exact ⟨hD₁.bvar, hD₁.fvar, hD₁.sort, hD₁.const, hD₁.lit,
    cP_other hD₁.app (o ADER (by decide) (by decide)), hnew,
    cP_other hD₁.forallE (o FADER (by decide) (by decide)),
    cP_other hD₁.letE (o LEDER (by decide) (by decide)),
    cP_other hD₁.proj (o PJDER (by decide) (by decide))⟩

/-- **`mk_forall` refines `internE (.lam _ _)` under `ArenaD`.** -/
theorem mkForall_ok (m : Mem) (a : AState) (hA : ArenaD m a) (t b r : Word) (m' : Mem)
    (hI : mkForallW m t b = some (r, m')) :
    AM.ok (internE (.forallE (decE t) (decE b))) a ∧
    ArenaD m' (AM.st (internE (.forallE (decE t) (decE b))) a) ∧
    AM.res (internE (.forallE (decE t) (decE b))) a = decE r := by
  obtain ⟨hR, hD⟩ := hA
  unfold mkForallW at hI
  split at hI
  · cases hI
  rename_i hg
  obtain ⟨ht, hb⟩ := or_shr32 t b (by simpa using hg)
  cases hI₁ : fainternW m t b with
  | none => simp [hI₁, mkK] at hI
  | some p =>
  obtain ⟨r₁, m₁⟩ := p
  simp only [hI₁, mkK_some] at hI
  cases hP : derPutW FADER 30 m₁ (cnt2 m 30) r₁ (maxW (derBW m t) (satPredW (derBW m b))) with
  | none => simp [hP] at hI
  | some m₂ =>
  simp only [hP, Option.some.injEq, Prod.mk.injEq] at hI
  obtain ⟨rfl, rfl⟩ := hI
  obtain ⟨hok, hX, hres⟩ := faintern_correct m a hR.forallE t b ht hb _ _ hI₁
  have hI₂ := hI₁; rw [fainternW_eq] at hI₂
  have hfr := internM_frame _ forallSch_wf _ _ _ _ _ _ _ _ hI₂
  have hcs := AM.proto_cases forallLens _ _ _ _ _ _ a (internE_forall_run _ _ a) hok
  have hR₁ := hR.lift_forallE _ _ _ _ hX hfr (AM.st_proto forallLens _ _ _ _ _ _ a (internE_forall_run _ _ a) hok)
  have hD₁ : DerR m₁ a := DerR.frameM _ _ m m₁ hfr (by simp [forallSch, FAREC, FASLOT]) a hD
  have hfr₂ := derPutW_frame FADER (by decide) _ _ _ _ _ _ hP
  have hnew := derMk forallSch forallSch_wf FaRecRel fahash forallLens (·.foralls) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) FADER m m₁ m₂ a _ _ _ _ r₁ _
    hR.forallE hR₁.forallE hD.forallE (hfr.1 FADER (by simp [forallSch, FADER, FAREC, FASLOT]) (by decide)) hcs
    hres.symm (by rw [maxW_eq, satPredW_eq, derBW_ok m a hR hD t ht, derBW_ok m a hR hD b hb,
      bvar_derBind]) hP
  have o := fun B (hB : B ≠ FADER) (hC : B ≠ CTL) => hfr₂.1 B (by simpa using hB) hC
  refine ⟨hok, ⟨ArenaR.frame_above _ _ (by simp [ADER, LADER, FADER, LEDER, PJDER]) (by simp) _ _ hfr₂ _ hR₁, ?_⟩, hres⟩
  rcases hcs with h | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> rw [h] at hnew ⊢ <;>
  exact ⟨hD₁.bvar, hD₁.fvar, hD₁.sort, hD₁.const, hD₁.lit,
    cP_other hD₁.app (o ADER (by decide) (by decide)),
    cP_other hD₁.lam (o LADER (by decide) (by decide)), hnew,
    cP_other hD₁.letE (o LEDER (by decide) (by decide)),
    cP_other hD₁.proj (o PJDER (by decide) (by decide))⟩

/-- **`mk_let` refines `internE (.letE _ _ _)` under `ArenaD`.** -/
theorem mkLet_ok (m : Mem) (a : AState) (hA : ArenaD m a) (t v b r : Word) (m' : Mem)
    (hI : mkLetW m t v b = some (r, m')) :
    AM.ok (internE (.letE (decE t) (decE v) (decE b))) a ∧
    ArenaD m' (AM.st (internE (.letE (decE t) (decE v) (decE b))) a) ∧
    AM.res (internE (.letE (decE t) (decE v) (decE b))) a = decE r := by
  obtain ⟨hR, hD⟩ := hA
  unfold mkLetW at hI
  split at hI
  · cases hI
  rename_i hg
  obtain ⟨htv, hb⟩ := or_shr32 _ b (by simpa using hg)
  obtain ⟨ht, hv⟩ := or_lt32 t v htv
  cases hI₁ : leinternW m t v b with
  | none => simp [hI₁, mkK] at hI
  | some p =>
  obtain ⟨r₁, m₁⟩ := p
  simp only [hI₁, mkK_some] at hI
  cases hP : derPutW LEDER 20 m₁ (cnt2 m 20) r₁
      (maxW (maxW (derBW m t) (derBW m v)) (satPredW (derBW m b))) with
  | none => simp [hP] at hI
  | some m₂ =>
  simp only [hP, Option.some.injEq, Prod.mk.injEq] at hI
  obtain ⟨rfl, rfl⟩ := hI
  obtain ⟨hok, hX, hres⟩ := leintern_correct m a hR.letE t v b ht hv hb _ _ hI₁
  have hI₂ := hI₁; rw [leinternW_eq] at hI₂
  have hfr := internM_frame _ letSch_wf _ _ _ _ _ _ _ _ hI₂
  have hcs := AM.proto_cases letLens _ _ _ _ _ _ a (internE_let_run _ _ _ a) hok
  have hR₁ := hR.lift_letE _ _ _ _ hX hfr
    (AM.st_proto letLens _ _ _ _ _ _ a (internE_let_run _ _ _ a) hok)
  have hD₁ : DerR m₁ a := DerR.frameM _ _ m m₁ hfr (by simp [letSch, LEREC, LESLOT]) a hD
  have hfr₂ := derPutW_frame LEDER (by decide) _ _ _ _ _ _ hP
  have hnew := derMk letSch letSch_wf LeRecRel lehash letLens (·.lets) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) LEDER m m₁ m₂ a _ _ _ _ r₁ _
    hR.letE hR₁.letE hD.letE (hfr.1 LEDER (by simp [letSch, LEDER, LEREC, LESLOT]) (by decide)) hcs
    hres.symm (by rw [maxW_eq, maxW_eq, satPredW_eq, derBW_ok m a hR hD t ht,
      derBW_ok m a hR hD v hv, derBW_ok m a hR hD b hb, bvar_derLet]) hP
  have o := fun B (hB : B ≠ LEDER) (hC : B ≠ CTL) => hfr₂.1 B (by simpa using hB) hC
  refine ⟨hok, ⟨ArenaR.frame_above _ _ (by simp [ADER, LADER, FADER, LEDER, PJDER]) (by simp) _ _ hfr₂ _ hR₁, ?_⟩, hres⟩
  rcases hcs with h | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> rw [h] at hnew ⊢ <;>
  exact ⟨hD₁.bvar, hD₁.fvar, hD₁.sort, hD₁.const, hD₁.lit,
    cP_other hD₁.app (o ADER (by decide) (by decide)),
    cP_other hD₁.lam (o LADER (by decide) (by decide)),
    cP_other hD₁.forallE (o FADER (by decide) (by decide)), hnew,
    cP_other hD₁.proj (o PJDER (by decide) (by decide))⟩

/-- **`mk_proj` refines `internE (.proj _ _ _)` under `ArenaD`.** -/
theorem mkProj_ok (m : Mem) (a : AState) (hA : ArenaD m a) (n i e r : Word) (m' : Mem)
    (hI : mkProjW m n i e = some (r, m')) :
    AM.ok (internE (.proj (decI n) i.toNat (decE e))) a ∧
    ArenaD m' (AM.st (internE (.proj (decI n) i.toNat (decE e))) a) ∧
    AM.res (internE (.proj (decI n) i.toNat (decE e))) a = decE r := by
  obtain ⟨hR, hD⟩ := hA
  unfold mkProjW at hI
  split at hI
  · cases hI
  rename_i hg
  obtain ⟨hn, he⟩ := or_shr32 n e (by simpa using hg)
  cases hI₁ : pjinternW m n i e with
  | none => simp [hI₁, mkK] at hI
  | some p =>
  obtain ⟨r₁, m₁⟩ := p
  simp only [hI₁, mkK_some] at hI
  cases hP : derPutW PJDER 32 m₁ (cnt2 m 32) r₁ (derBW m e) with
  | none => simp [hP] at hI
  | some m₂ =>
  simp only [hP, Option.some.injEq, Prod.mk.injEq] at hI
  obtain ⟨rfl, rfl⟩ := hI
  obtain ⟨hok, hX, hres⟩ := pjintern_correct m a hR.proj n i e hn he _ _ hI₁
  have hI₂ := hI₁; rw [pjinternW_eq] at hI₂
  have hfr := internM_frame _ projSch_wf _ _ _ _ _ _ _ _ hI₂
  have hcs := AM.proto_cases projLens _ _ _ _ _ _ a (internE_proj_run _ _ _ a) hok
  have hR₁ := hR.lift_proj _ _ _ _ hX hfr
    (AM.st_proto projLens _ _ _ _ _ _ a (internE_proj_run _ _ _ a) hok)
  have hD₁ : DerR m₁ a := DerR.frameM _ _ m m₁ hfr (by simp [projSch, PJREC, PJSLOT]) a hD
  have hfr₂ := derPutW_frame PJDER (by decide) _ _ _ _ _ _ hP
  have hnew := derMk projSch projSch_wf PJRecRel pjhash projLens (·.projs) (fun _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) PJDER m m₁ m₂
    a _ _ _ _ r₁ _ hR.proj hR₁.proj hD.proj
    (hfr.1 PJDER (by simp [projSch, PJDER, PJREC, PJSLOT]) (by decide)) hcs
    hres.symm (by rw [derBW_ok m a hR hD e he, bvar_derProj]) hP
  have o := fun B (hB : B ≠ PJDER) (hC : B ≠ CTL) => hfr₂.1 B (by simpa using hB) hC
  refine ⟨hok, ⟨ArenaR.frame_above _ _ (by simp [ADER, LADER, FADER, LEDER, PJDER]) (by simp) _ _ hfr₂ _ hR₁, ?_⟩, hres⟩
  rcases hcs with h | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> rw [h] at hnew ⊢ <;>
  exact ⟨hD₁.bvar, hD₁.fvar, hD₁.sort, hD₁.const, hD₁.lit,
    cP_other hD₁.app (o ADER (by decide) (by decide)),
    cP_other hD₁.lam (o LADER (by decide) (by decide)),
    cP_other hD₁.forallE (o FADER (by decide) (by decide)),
    cP_other hD₁.letE (o LEDER (by decide) (by decide)), hnew⟩

/-- **`intern_bvar` refines `internE (.bvar _)` under `ArenaD`** (a leaf: its range is
`satSucc i`, not stored in L, so the plain `intern_bvar` keeps `DerR`). -/
theorem internBVar_D (m : Mem) (a : AState) (hA : ArenaD m a) (u r : Word) (m' : Mem)
    (hI : binternW m u = some (r, m')) :
    AM.ok (internE (.bvar u.toNat)) a ∧ ArenaD m' (AM.st (internE (.bvar u.toNat)) a) ∧
    AM.res (internE (.bvar u.toNat)) a = decE r := by
  obtain ⟨hR, hD⟩ := hA
  obtain ⟨hok, hX, hres⟩ := bintern_correct m a hR.bvar u _ _ hI
  have hI₂ := hI; rw [binternW_eq] at hI₂
  have hfr := internM_frame _ bvarSch_wf _ _ _ _ _ _ _ _ hI₂
  have hcs := AM.proto_cases bvarLens _ _ _ _ _ _ a (internE_bvar_run _ a) hok
  have hR₁ := hR.lift_bvar _ _ _ _ hX hfr
    (AM.st_proto bvarLens _ _ _ _ _ _ a (internE_bvar_run _ a) hok)
  have hD₁ : DerR m' a := DerR.frameM _ _ m m' hfr (by simp [bvarSch, BREC, BSLOT]) a hD
  refine ⟨hok, ⟨hR₁, ?_⟩, hres⟩
  rcases hcs with h | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> rw [h]
  · exact hD₁
  · exact ⟨⟨derT_push hD₁.bvar.1 _ _ _ (bvar_derBVar _ _), hD₁.bvar.2⟩, hD₁.fvar, hD₁.sort,
      hD₁.const, hD₁.lit, hD₁.app, hD₁.lam, hD₁.forallE, hD₁.letE, hD₁.proj⟩
  · exact ⟨⟨hD₁.bvar.1, derT_push hD₁.bvar.2 _ _ _ (bvar_derBVar _ _)⟩, hD₁.fvar, hD₁.sort,
      hD₁.const, hD₁.lit, hD₁.app, hD₁.lam, hD₁.forallE, hD₁.letE, hD₁.proj⟩

/-- **`intern_fvar` refines `internE (.fvar _ _)` under `ArenaD`** (a leaf: range `0`). -/
theorem internFVar_D (m : Mem) (a : AState) (hA : ArenaD m a) (u ty r : Word)
    (hty : ty.toNat < 2 ^ 32) (m' : Mem) (hI : fvinternW m u ty = some (r, m')) :
    AM.ok (internE (.fvar u.toNat (decE ty))) a ∧
    ArenaD m' (AM.st (internE (.fvar u.toNat (decE ty))) a) ∧
    AM.res (internE (.fvar u.toNat (decE ty))) a = decE r := by
  obtain ⟨hR, hD⟩ := hA
  obtain ⟨hok, hX, hres⟩ := fvintern_correct m a hR.fvar u ty hty _ _ hI
  have hI₂ := hI; rw [fvinternW_eq] at hI₂
  have hfr := internM_frame _ fvarSch_wf _ _ _ _ _ _ _ _ hI₂
  have hcs := AM.proto_cases fvarLens _ _ _ _ _ _ a (internE_fvar_run _ _ a) hok
  have hR₁ := hR.lift_fvar _ _ _ _ hX hfr
    (AM.st_proto fvarLens _ _ _ _ _ _ a (internE_fvar_run _ _ a) hok)
  have hD₁ : DerR m' a := DerR.frameM _ _ m m' hfr (by simp [fvarSch, FVREC, FVSLOT]) a hD
  refine ⟨hok, ⟨hR₁, ?_⟩, hres⟩
  rcases hcs with h | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> rw [h]
  · exact hD₁
  · exact ⟨hD₁.bvar, ⟨derT_push hD₁.fvar.1 _ _ _ (bvar_derFVar _ _ _), hD₁.fvar.2⟩, hD₁.sort,
      hD₁.const, hD₁.lit, hD₁.app, hD₁.lam, hD₁.forallE, hD₁.letE, hD₁.proj⟩
  · exact ⟨hD₁.bvar, ⟨hD₁.fvar.1, derT_push hD₁.fvar.2 _ _ _ (bvar_derFVar _ _ _)⟩, hD₁.sort,
      hD₁.const, hD₁.lit, hD₁.app, hD₁.lam, hD₁.forallE, hD₁.letE, hD₁.proj⟩

/-- **`intern_sort` refines `internE (.sort _)` under `ArenaD`** (a leaf: range `0`). -/
theorem internSort_D (m : Mem) (a : AState) (hA : ArenaD m a) (u r : Word)
    (hu : u.toNat < 2 ^ 32) (m' : Mem) (hI : sointernW m u = some (r, m')) :
    AM.ok (internE (.sort (decI u))) a ∧ ArenaD m' (AM.st (internE (.sort (decI u))) a) ∧
    AM.res (internE (.sort (decI u))) a = decI r := by
  obtain ⟨hR, hD⟩ := hA
  obtain ⟨hok, hX, hres⟩ := sointern_correct m a hR.sort u hu _ _ hI
  have hI₂ := hI; rw [sointernW_eq] at hI₂
  have hfr := internM_frame _ sortSch_wf _ _ _ _ _ _ _ _ hI₂
  have hcs := AM.proto_cases sortLens _ _ _ _ _ _ a (internE_sort_run _ a) hok
  have hR₁ := hR.lift_sort _ _ _ _ hX hfr
    (AM.st_proto sortLens _ _ _ _ _ _ a (internE_sort_run _ a) hok)
  have hD₁ : DerR m' a := DerR.frameM _ _ m m' hfr (by simp [sortSch, SOREC, SOSLOT]) a hD
  refine ⟨hok, ⟨hR₁, ?_⟩, hres⟩
  rcases hcs with h | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> rw [h]
  · exact hD₁
  · exact ⟨hD₁.bvar, hD₁.fvar, ⟨derT_push hD₁.sort.1 _ _ _ (bvar_derSort _ _), hD₁.sort.2⟩,
      hD₁.const, hD₁.lit, hD₁.app, hD₁.lam, hD₁.forallE, hD₁.letE, hD₁.proj⟩
  · exact ⟨hD₁.bvar, hD₁.fvar, ⟨hD₁.sort.1, derT_push hD₁.sort.2 _ _ _ (bvar_derSort _ _)⟩,
      hD₁.const, hD₁.lit, hD₁.app, hD₁.lam, hD₁.forallE, hD₁.letE, hD₁.proj⟩

/-- **`intern_const` refines `internE (.const _ _)` under `ArenaD`** (a leaf: range `0`). -/
theorem internConst_D (m : Mem) (a : AState) (hA : ArenaD m a) (f x r : Word)
    (hf : f.toNat < 2 ^ 32) (hx : x.toNat < 2 ^ 32) (m' : Mem)
    (hI : ceinternW m f x = some (r, m')) :
    AM.ok (internE (.const (decI (k := .name) f) (decI (k := .levels) x))) a ∧
    ArenaD m' (AM.st (internE (.const (decI (k := .name) f) (decI (k := .levels) x))) a) ∧
    AM.res (internE (.const (decI (k := .name) f) (decI (k := .levels) x))) a = decI r := by
  obtain ⟨hR, hD⟩ := hA
  obtain ⟨hok, hX, hres⟩ := ceintern_correct m a hR.const f x hf hx _ _ hI
  have hI₂ := hI; rw [ceinternW_eq] at hI₂
  have hfr := internM_frame _ constSch_wf _ _ _ _ _ _ _ _ hI₂
  have hcs := AM.proto_cases constLens _ _ _ _ _ _ a (internE_const_run _ _ a) hok
  have hR₁ := hR.lift_const _ _ _ _ hX hfr
    (AM.st_proto constLens _ _ _ _ _ _ a (internE_const_run _ _ a) hok)
  have hD₁ : DerR m' a := DerR.frameM _ _ m m' hfr (by simp [constSch, CREC, CSLOT]) a hD
  refine ⟨hok, ⟨hR₁, ?_⟩, hres⟩
  rcases hcs with h | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> rw [h]
  · exact hD₁
  · exact ⟨hD₁.bvar, hD₁.fvar, hD₁.sort,
      ⟨derT_push hD₁.const.1 _ _ _ (bvar_derConst _ _ _), hD₁.const.2⟩, hD₁.lit, hD₁.app, hD₁.lam,
      hD₁.forallE, hD₁.letE, hD₁.proj⟩
  · exact ⟨hD₁.bvar, hD₁.fvar, hD₁.sort,
      ⟨hD₁.const.1, derT_push hD₁.const.2 _ _ _ (bvar_derConst _ _ _)⟩, hD₁.lit, hD₁.app, hD₁.lam,
      hD₁.forallE, hD₁.letE, hD₁.proj⟩

/-- **`intern_lit` refines `internE (.lit (.natVal _))` under `ArenaD`** (a leaf: range `0`). -/
theorem internLit_D (m : Mem) (a : AState) (hA : ArenaD m a) (o l r : Word)
    (hq : SliceOK m o l) (hn : Norm (m.arr64 POOL) o.toNat l.toNat) (m' : Mem)
    (hI : internW m o l = some (r, m')) :
    AM.ok (internE (.lit (.natVal (pv (m.arr64 POOL) o.toNat l.toNat)))) a ∧
    ArenaD m' (AM.st (internE (.lit (.natVal (pv (m.arr64 POOL) o.toNat l.toNat)))) a) ∧
    AM.res (internE (.lit (.natVal (pv (m.arr64 POOL) o.toNat l.toNat)))) a = decE r := by
  obtain ⟨hR, hD⟩ := hA
  obtain ⟨hok, hX, hres⟩ := intern_correct m a hR.lit o l hq hn _ _ hI
  have hI₂ := hI; rw [internW_eq] at hI₂
  have hfr := internM_frame _ litS_wf _ _ _ _ _ _ _ _ hI₂
  have hcs := AM.proto_cases litLens _ _ _ _ _ _ a (internE_lit_run _ a) hok
  have hR₁ := hR.lift_lit _ _ _ _ hX hfr
    (AM.st_proto litLens _ _ _ _ _ _ a (internE_lit_run _ a) hok)
  have hD₁ : DerR m' a := DerR.frameM _ _ m m' hfr (by simp [litSch, REC, SLOT]) a hD
  refine ⟨hok, ⟨hR₁, ?_⟩, hres⟩
  rcases hcs with h | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> rw [h]
  · exact hD₁
  · exact ⟨hD₁.bvar, hD₁.fvar, hD₁.sort, hD₁.const,
      ⟨derT_push hD₁.lit.1 _ _ _ (bvar_derLit _ _), hD₁.lit.2⟩, hD₁.app, hD₁.lam, hD₁.forallE,
      hD₁.letE, hD₁.proj⟩
  · exact ⟨hD₁.bvar, hD₁.fvar, hD₁.sort, hD₁.const,
      ⟨hD₁.lit.1, derT_push hD₁.lit.2 _ _ _ (bvar_derLit _ _)⟩, hD₁.app, hD₁.lam, hD₁.forallE,
      hD₁.letE, hD₁.proj⟩

/-- `DerR` reads only the store: a state with the same store (other memos, caches) has it too. -/
theorem DerR.of_store (m : Mem) (a a' : AState) (hD : DerR m a) (hs : a'.store = a.store) :
    DerR m a' := by
  have e : ∀ {α : Type} [BEq α] [Hashable α] (g : ETables → Tbl α EIdx UInt64)
      (P : Word → Nat → α → UInt64 → Prop), DerT2 a g P → DerT2 a' g P := by
    intro α _ _ g P h; unfold DerT2 at *; rw [hs]; exact h
  exact ⟨e _ _ hD.bvar, e _ _ hD.fvar, e _ _ hD.sort, e _ _ hD.const, e _ _ hD.lit, e _ _ hD.app,
    e _ _ hD.lam, e _ _ hD.forallE, e _ _ hD.letE, e _ _ hD.proj⟩

/-! ## The initial state -/

theorem derT_empty {α : Type} [BEq α] [Hashable α] (P : Nat → α → UInt64 → Prop) :
    DerT (Tbl.empty : Tbl α EIdx UInt64) P :=
  ⟨rfl, fun i x h => by simp [Tbl.empty] at h⟩

/-- **`DerR` holds initially**, at any memory: every table is empty. -/
theorem derR_init (m : Mem) : DerR m (AState.init EStore.empty) := by
  have e := fun {α : Type} [BEq α] [Hashable α] (P : Word → Nat → α → UInt64 → Prop) =>
    (⟨derT_empty (P 0), derT_empty (P 1)⟩ : DerT (Tbl.empty : Tbl α EIdx UInt64) (P 0) ∧
      DerT (Tbl.empty : Tbl α EIdx UInt64) (P 1))
  exact ⟨e _, e _, e _, e _, e _, e _, e _, e _, e _, e _⟩

/-- **`ArenaD` holds initially.** -/
theorem arenaD_init (sizes : List Nat) (hlen : 64 ≤ sizes.length) (hctl : 64 ≤ sizes[1]?.getD 0)
    (hpool : sizes[0]?.getD 0 < 2 ^ 63) : ArenaD (initMem sizes) (AState.init EStore.empty) :=
  ⟨arenaR_init sizes hlen hctl hpool, derR_init _⟩

/-! ## Appending to the pool keeps `ArenaD`, and `natAddLit_refinesD` -/

/-- **Appending to the pool keeps `DerR`**: the five derived-range arrays (`42`‥`46`) are
untouched by a pool append (only `POOL`, `0`, and `CTL[0]` move). -/
theorem DerR.grow (m m' : Mem) (hg : Grows m m') (a : AState) (hD : DerR m a) : DerR m' a :=
  DerR.frameM [POOL] [0] m m' (grows_frame m m' hg) (by decide) a hD

/-- **Appending to the pool keeps `ArenaD`.** -/
theorem ArenaD.grow (m m' : Mem) (hg : Grows m m') (a : AState) (hA : ArenaD m a) : ArenaD m' a :=
  ⟨ArenaR.grow m m' hg a hA.1, DerR.grow m m' hg a hA.2⟩

/-- `intern_lit` refines `internE (.lit (.natVal _))` under `ArenaD`. -/
theorem internLit_refinesD (p : Prog) (hph : p.lookup "lit_hash" = some litHash)
    (hpe : p.lookup "limbs_eq" = some limbsEq) (hpm : p.lookup "lit_match" = some litMatch)
    (hpf : p.lookup "lit_find" = some litFind) (hpp : p.lookup "lit_push" = some litPush)
    (hp : p.lookup "intern_lit" = some internLit)
    (a₀ : AState) (n : Nat) (s₀ : St) (o l : Word) (hA : ArenaD s₀.mem a₀)
    (hq : SliceOK s₀.mem o l) (hn : Norm (s₀.mem.arr64 POOL) o.toNat l.toNat) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_lit" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (internE (.lit (.natVal (pv (s₀.mem.arr64 POOL) o.toNat l.toNat)))) a₀ ∧
      ArenaD s'.mem (AM.st (internE (.lit (.natVal (pv (s₀.mem.arr64 POOL) o.toNat l.toNat)))) a₀) ∧
      AM.res (internE (.lit (.natVal (pv (s₀.mem.arr64 POOL) o.toNat l.toNat)))) a₀ =
        decE (r.headD 0); ⊤⦄ := by
  have ⟨_, _, hps, htop⟩ := hA.1.lit.1
  have hspec := internLit_spec p hph hpe hpm hpf hpp hp n s₀ o l (by omega)
    (by simp only [SliceOK] at hq; omega)
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun hspec
  subst hs
  exact ⟨hloc, internLit_D s.mem a₀ hA o l _ hq hn _ hI⟩

/-- **`nat_add_lit` refines `natOpResult`'s `Nat.add` arm under `ArenaD`.** -/
theorem natAddLit_refinesD (n : Nat) (s₀ : St) (a₀ : AState) (hA : ArenaD s₀.mem a₀)
    (oa la ob lb : Word) (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb) :
    ⦃fun s => s = s₀⦄
    invoke storeProg (exec storeProg n) "nat_add_lit" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (natAddArm (pv (s₀.mem.arr64 POOL) oa.toNat la.toNat)
        (pv (s₀.mem.arr64 POOL) ob.toNat lb.toNat)) a₀ ∧
      ArenaD s'.mem (AM.st (natAddArm (pv (s₀.mem.arr64 POOL) oa.toNat la.toNat)
        (pv (s₀.mem.arr64 POOL) ob.toNat lb.toNat)) a₀) ∧
      AM.res (natAddArm (pv (s₀.mem.arr64 POOL) oa.toNat la.toNat)
        (pv (s₀.mem.arr64 POOL) ob.toNat lb.toNat)) a₀ = some (decE (r.headD 0)); ⊤⦄ :=
  natAddLit_refines storeProg rfl rfl rfl rfl rfl ArenaD (fun _ _ h => h.1.lit.1)
    (fun m m' a hA hg => ArenaD.grow m m' hg a hA)
    (internLit_refinesD storeProg rfl rfl rfl rfl rfl rfl) n s₀ a₀ hA oa la ob lb ha hb

end L.Arena
