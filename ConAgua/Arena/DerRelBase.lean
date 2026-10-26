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

/-- A leaf other than `bvar`/`fvar` (`sort`, `const`, `lit`): both ranges `0` (lane `exprops3`
added the fvar-range conjunct). -/
def zP {α : Type} : Word → Nat → α → UInt64 → Prop :=
  fun _ _ _ d => bvarOfData d = 0 ∧ fvarOfData d = 0

/-- `lit`: both ranges `0` and no level parameter (helper `whnf4-d23` added the `lp` conjunct to
the two leaves whose bit is the constant `false`; `sort`/`const`/`fvar` keep theirs in a column,
`ArenaR`). -/
def zlP {α : Type} : Word → Nat → α → UInt64 → Prop :=
  fun _ _ _ d => bvarOfData d = 0 ∧ fvarOfData d = 0 ∧ lpOfData d = false

/-- `bvar i`: bvar range `satSucc i`, fvar range `0` (a bound variable is not free), no level
parameter. -/
def bvP : Word → Nat → BVarNode → UInt64 → Prop :=
  fun _ _ x d => bvarOfData d = satSucc x.i ∧ fvarOfData d = 0 ∧ lpOfData d = false

/-- `fvar idx ty`: bvar range `0`, fvar range `satSucc idx` (lane `exprops3`). -/
def fvP : Word → Nat → FVarNode → UInt64 → Prop :=
  fun _ _ x d => bvarOfData d = 0 ∧ fvarOfData d = satSucc x.idx

/-- A compound table: both ranges and the level-parameter bit are in L, packed at `A[2 i + t]`
(`packBFL`; lane `exprops3` widened this from the bvar range alone, helper `whnf4-d23` added the
bit). -/
def cP {α : Type} (A : ArrId) (m : Mem) : Word → Nat → α → UInt64 → Prop :=
  fun t i _ d => rdW (m.arr64 (tierA A t)) (UInt64.ofNat i) =
    packBFL (bvarOfData d) (fvarOfData d) (lpW d)

/-- **The derived range relation.** -/
structure DerR (m : Mem) (a : AState) : Prop where
  bvar : DerT2 a (·.bvars) bvP
  fvar : DerT2 a (·.fvars) fvP
  sort : DerT2 a (·.sorts) zP
  const : DerT2 a (·.consts) zP
  lit : DerT2 a (·.lits) zlP
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

/-- A `sort`/`const`/`lit` table's bvar range is `0` everywhere. -/
theorem derT_zero_b {α : Type} [BEq α] [Hashable α] {tb : Tbl α EIdx UInt64} {t : Word}
    (hD : DerT tb (zP t)) (i : Nat) : bvarOfData (tb.derAt i) = 0 := by
  by_cases hi : i < tb.nodes.size
  · exact (hD.2 i _ (Array.getElem?_eq_getElem hi)).1
  · rw [derT_out hD i (by omega)]; rfl

/-- A `sort`/`const`/`lit` table's fvar range is `0` everywhere (lane `exprops3`). -/
theorem derT_zero_f {α : Type} [BEq α] [Hashable α] {tb : Tbl α EIdx UInt64} {t : Word}
    (hD : DerT tb (zP t)) (i : Nat) : fvarOfData (tb.derAt i) = 0 := by
  by_cases hi : i < tb.nodes.size
  · exact (hD.2 i _ (Array.getElem?_eq_getElem hi)).2
  · rw [derT_out hD i (by omega)]; rfl

/-- `zlP` is `zP` and more. -/
theorem derT2_zl {α : Type} [BEq α] [Hashable α] {a : AState} {g : ETables → Tbl α EIdx UInt64}
    (hD : DerT2 a g zlP) : DerT2 a g zP :=
  ⟨⟨hD.1.1, fun i x h => ⟨(hD.1.2 i x h).1, (hD.1.2 i x h).2.1⟩⟩,
    ⟨hD.2.1, fun i x h => ⟨(hD.2.2 i x h).1, (hD.2.2 i x h).2.1⟩⟩⟩

/-- A `bvar` node's fvar range is `0` (lane `exprops3`: a bound variable is not free). -/
theorem derT_bvar_f {tb : Tbl BVarNode EIdx UInt64} {t : Word}
    (hD : DerT tb (bvP t)) (i : Nat) : fvarOfData (tb.derAt i) = 0 := by
  by_cases hi : i < tb.nodes.size
  · exact (hD.2 i _ (Array.getElem?_eq_getElem hi)).2.1
  · rw [derT_out hD i (by omega)]; rfl

/-- A `fvar` node's bvar range is `0` (lane `exprops3`: an `fvar` is not de Bruijn). -/
theorem derT_fvar_b {tb : Tbl FVarNode EIdx UInt64} {t : Word}
    (hD : DerT tb (fvP t)) (i : Nat) : bvarOfData (tb.derAt i) = 0 := by
  by_cases hi : i < tb.nodes.size
  · exact (hD.2 i _ (Array.getElem?_eq_getElem hi)).1
  · rw [derT_out hD i (by omega)]; rfl

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
  have hfl := ConsR.flag hR.app
  have hon : a.store.scratchOn = false := by
    rw [← hfl]; simp [hs.2]
  simp [EStore.derived, decE_tierW, hs.1, hon]

include hR in
theorem derived_tier (hs : ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0)) :
    a.store.derived (decE h) = (tierOf a (tierW h)).derAt (decE h) := by
  have hfl := ConsR.flag hR.app
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

/-- A compound tier's range, from `DerT` and the L count. -/
theorem derC {α : Type} [BEq α] [Hashable α] (A : ArrId) (m : Mem) (tb : Tbl α EIdx UInt64)
    (t : Word) (hD : DerT tb (cP A m t)) (i : Word) (hc : (i.toNat < tb.nodes.size)) :
    rdW (m.arr64 (tierA A t)) i =
      packBFL (bvarOfData (tb.derAt i.toNat)) (fvarOfData (tb.derAt i.toNat))
        (lpW (tb.derAt i.toNat)) := by
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
  have comp : ∀ {α : Type} [BEq α] [Hashable α] (C : ConsSch) (R : Mem → Word → Word → α → Prop)
      (g : ETables → Tbl α EIdx UInt64) (A : ArrId)
      (hT : ConsR C R m a.store.scratchOn (g a.store.pers) (g a.store.scr))
      (hd : DerT2 a g (cP A m)),
      (if cntC C m (tierW h) ≤ idxW h then (0 : Word)
       else rdW (m.arr64 (tierA A (tierW h))) (idxW h) &&& 32767) =
        bvarOfData ((g (tierOf a (tierW h))).derAt (idxW h).toNat) := by
    intro α _ _ C R g A hT hd
    have hc := ConsR.cnt hT (tierW h) ht
    have hD' := derT2_tier hd (tierW h) ht
    have hg : (if tierW h = 0 then g a.store.pers else g a.store.scr) = g (tierOf a (tierW h)) := by
      simp only [tierOf]; split <;> rfl
    rw [hg] at hc
    split
    · rename_i hle
      rw [derT_out hD' _ (by rw [← hc]; exact hle)]; rfl
    · rename_i hlt
      rw [derC A m _ _ hD' _ (by rw [← hc]; exact UInt64.not_le.mp hlt)]
      exact packBFL_bvar _ _ _ (bvarOfData_lt _) (fvarOfData_lt _) (b2w_le _)
  by_cases g0 : h >>> 28 = 0
  · simp only [g0, ↓reduceIte]
    rw [derAt_bvar _ h hh g0]
    have hc := ConsR.cnt hR.bvar (tierW h) ht
    have hD' := derT2_tier hD.bvar (tierW h) ht
    have hg : (if tierW h = 0 then a.store.pers.bvars else a.store.scr.bvars) =
        (tierOf a (tierW h)).bvars := by simp only [tierOf]; split <;> rfl
    rw [hg] at hc
    split
    · rename_i hle
      rw [derT_out hD' _ (by rw [← hc]; exact hle)]; rfl
    · rename_i hlt
      obtain ⟨k, hk, hkr⟩ := node_of m a h bvarCS BRecRel (·.bvars) _ hR.bvar
        (UInt64.not_le.mp hlt)
      have hk' : (tierOf a (tierW h)).bvars.nodes[(idxW h).toNat]? = some k := by
        simpa [tierOf, apply_ite] using hk
      rw [(hD'.2 _ k hk').1, satSuccW_eq]
      simp only [BRecRel] at hkr; rw [hkr]
  simp only [g0, ↓reduceIte]
  by_cases g4 : h >>> 28 = 4
  · simp only [g4, ↓reduceIte]; rw [derAt_app _ h hh g4]
    exact comp appCS ARecRel (·.apps) ADER hR.app hD.app
  simp only [g4, ↓reduceIte]
  by_cases g5 : h >>> 28 = 5
  · simp only [g5, ↓reduceIte]; rw [derAt_lam _ h hh g5]
    exact comp lamCS LaRecRel (·.lams) LADER hR.lam hD.lam
  simp only [g5, ↓reduceIte]
  by_cases g6 : h >>> 28 = 6
  · simp only [g6, ↓reduceIte]; rw [derAt_forall _ h hh g6]
    exact comp forallCS FaRecRel (·.foralls) FADER hR.forallE hD.forallE
  simp only [g6, ↓reduceIte]
  by_cases g7 : h >>> 28 = 7
  · simp only [g7, ↓reduceIte]; rw [derAt_let _ h hh g7]
    exact comp letCS LeRecRel (·.lets) LEDER hR.letE hD.letE
  simp only [g7, ↓reduceIte]
  by_cases g9 : h >>> 28 = 9
  · simp only [g9, ↓reduceIte]; rw [derAt_proj _ h hh g9]
    exact comp projCS PJRecRel (·.projs) PJDER hR.proj hD.proj
  simp only [g9, ↓reduceIte]
  by_cases g1 : h >>> 28 = 1
  · rw [derAt_fvar _ h hh g1, derT_fvar_b (derT2_tier hD.fvar (tierW h) ht) (idxW h).toNat]
  have tz := fun {α : Type} [BEq α] [Hashable α] (g : ETables → Tbl α EIdx UInt64)
    (hd : DerT2 a g zP) => derT_zero_b (derT2_tier hd (tierW h) ht) (idxW h).toNat
  by_cases g2 : h >>> 28 = 2
  · rw [derAt_sort _ h hh g2, tz (·.sorts) hD.sort]
  by_cases g3 : h >>> 28 = 3
  · rw [derAt_const _ h hh g3, tz (·.consts) hD.const]
  by_cases g8 : h >>> 28 = 8
  · rw [derAt_lit _ h hh g8, tz (·.lits) (derT2_zl hD.lit)]
  rw [derAt_other _ h hh g0 g1 g2 g3 g4 g5 g6 g7 g8 g9]; rfl

/-- **`der_f(h)` is the fvar-range field of the arena's derived word** (lane `exprops3`). -/
theorem derFW_ok (m : Mem) (a : AState) (hR : ArenaR m a) (hD : DerR m a) (h : Word)
    (hh : h.toNat < 2 ^ 32) : derFW m h = fvarOfData (a.store.derived (decE h)) := by
  have ht := tierW_le h
  unfold derFW
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [ite_eq_left hs, derived_closed m a hR h hs]; rfl
  rw [ite_eq_right hs, derived_tier m a hR h hs]
  have comp : ∀ {α : Type} [BEq α] [Hashable α] (C : ConsSch) (R : Mem → Word → Word → α → Prop)
      (g : ETables → Tbl α EIdx UInt64) (A : ArrId)
      (hT : ConsR C R m a.store.scratchOn (g a.store.pers) (g a.store.scr))
      (hd : DerT2 a g (cP A m)),
      (if cntC C m (tierW h) ≤ idxW h then (0 : Word)
       else (rdW (m.arr64 (tierA A (tierW h))) (idxW h) >>> 15) &&& 32767) =
        fvarOfData ((g (tierOf a (tierW h))).derAt (idxW h).toNat) := by
    intro α _ _ C R g A hT hd
    have hc := ConsR.cnt hT (tierW h) ht
    have hD' := derT2_tier hd (tierW h) ht
    have hg : (if tierW h = 0 then g a.store.pers else g a.store.scr) = g (tierOf a (tierW h)) := by
      simp only [tierOf]; split <;> rfl
    rw [hg] at hc
    split
    · rename_i hle
      rw [derT_out hD' _ (by rw [← hc]; exact hle)]; rfl
    · rename_i hlt
      rw [derC A m _ _ hD' _ (by rw [← hc]; exact UInt64.not_le.mp hlt)]
      exact packBFL_fvar _ _ _ (bvarOfData_lt _) (fvarOfData_lt _) (b2w_le _)
  by_cases g1 : h >>> 28 = 1
  · simp only [g1, ↓reduceIte]
    rw [derAt_fvar _ h hh g1]
    have hc := ConsR.cnt hR.fvar (tierW h) ht
    have hD' := derT2_tier hD.fvar (tierW h) ht
    have hg : (if tierW h = 0 then a.store.pers.fvars else a.store.scr.fvars) =
        (tierOf a (tierW h)).fvars := by simp only [tierOf]; split <;> rfl
    rw [hg] at hc
    split
    · rename_i hle
      rw [derT_out hD' _ (by rw [← hc]; exact hle)]; rfl
    · rename_i hlt
      obtain ⟨k, hk, hkr⟩ := node_of m a h fvarCS FVRecRel (·.fvars) _ hR.fvar
        (UInt64.not_le.mp hlt)
      have hk' : (tierOf a (tierW h)).fvars.nodes[(idxW h).toNat]? = some k := by
        simpa [tierOf, apply_ite] using hk
      rw [(hD'.2 _ k hk').2, satSuccW_eq]
      simp only [FVRecRel] at hkr; rw [hkr.1]
  simp only [g1, ↓reduceIte]
  by_cases g4 : h >>> 28 = 4
  · simp only [g4, ↓reduceIte]; rw [derAt_app _ h hh g4]
    exact comp appCS ARecRel (·.apps) ADER hR.app hD.app
  simp only [g4, ↓reduceIte]
  by_cases g5 : h >>> 28 = 5
  · simp only [g5, ↓reduceIte]; rw [derAt_lam _ h hh g5]
    exact comp lamCS LaRecRel (·.lams) LADER hR.lam hD.lam
  simp only [g5, ↓reduceIte]
  by_cases g6 : h >>> 28 = 6
  · simp only [g6, ↓reduceIte]; rw [derAt_forall _ h hh g6]
    exact comp forallCS FaRecRel (·.foralls) FADER hR.forallE hD.forallE
  simp only [g6, ↓reduceIte]
  by_cases g7 : h >>> 28 = 7
  · simp only [g7, ↓reduceIte]; rw [derAt_let _ h hh g7]
    exact comp letCS LeRecRel (·.lets) LEDER hR.letE hD.letE
  simp only [g7, ↓reduceIte]
  by_cases g9 : h >>> 28 = 9
  · simp only [g9, ↓reduceIte]; rw [derAt_proj _ h hh g9]
    exact comp projCS PJRecRel (·.projs) PJDER hR.proj hD.proj
  simp only [g9, ↓reduceIte]
  by_cases g0 : h >>> 28 = 0
  · rw [derAt_bvar _ h hh g0, derT_bvar_f (derT2_tier hD.bvar (tierW h) ht) (idxW h).toNat]
  have tz := fun {α : Type} [BEq α] [Hashable α] (g : ETables → Tbl α EIdx UInt64)
    (hd : DerT2 a g zP) => derT_zero_f (derT2_tier hd (tierW h) ht) (idxW h).toNat
  by_cases g2 : h >>> 28 = 2
  · rw [derAt_sort _ h hh g2, tz (·.sorts) hD.sort]
  by_cases g3 : h >>> 28 = 3
  · rw [derAt_const _ h hh g3, tz (·.consts) hD.const]
  by_cases g8 : h >>> 28 = 8
  · rw [derAt_lit _ h hh g8, tz (·.lits) (derT2_zl hD.lit)]
  rw [derAt_other _ h hh g0 g1 g2 g3 g4 g5 g6 g7 g8 g9]; rfl

/-- A table whose records carry no level parameter (`bvP`, `zlP`): `lp` is `false` everywhere. -/
theorem derT_lp_false {α : Type} [BEq α] [Hashable α] {tb : Tbl α EIdx UInt64}
    {P : Nat → α → UInt64 → Prop} (hD : DerT tb P) (hP : ∀ i x d, P i x d → lpOfData d = false)
    (i : Nat) : lpOfData (tb.derAt i) = false := by
  by_cases hi : i < tb.nodes.size
  · exact hP _ _ _ (hD.2 i _ (Array.getElem?_eq_getElem hi))
  · rw [derT_out hD i (by omega)]; rfl

/-- **`der_b`'s third result is the level-parameter bit of the arena's derived word** (helper
`whnf4-d23`, deviation D23): `exprLPW m h = lpW (a.store.derived (decE h))`, i.e. `1` iff
`lpOfData (derived h)`. This is the read `instLP`'s cut-off (`instLPGo`, `instLPFast`) needs. -/
theorem derLW_ok (m : Mem) (a : AState) (hR : ArenaR m a) (hD : DerR m a) (h : Word)
    (hh : h.toNat < 2 ^ 32) : exprLPW m h = lpW (a.store.derived (decE h)) := by
  have ht := tierW_le h
  unfold exprLPW
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [if_pos hs, derived_closed m a hR h hs]; rfl
  rw [if_neg hs, derived_tier m a hR h hs]
  -- a compound tag: the count, then bit 30 of the L word
  have comp : ∀ {α : Type} [BEq α] [Hashable α] (C : ConsSch) (R : Mem → Word → Word → α → Prop)
      (g : ETables → Tbl α EIdx UInt64) (A : ArrId)
      (hT : ConsR C R m a.store.scratchOn (g a.store.pers) (g a.store.scr))
      (hd : DerT2 a g (cP A m)),
      (if idxW h < cntC C m (tierW h) then rdW (m.arr64 (tierA A (tierW h))) (idxW h) >>> 30
       else (0 : Word)) = lpW ((g (tierOf a (tierW h))).derAt (idxW h).toNat) := by
    intro α _ _ C R g A hT hd
    have hc := ConsR.cnt hT (tierW h) ht
    have hD' := derT2_tier hd (tierW h) ht
    have hg : (if tierW h = 0 then g a.store.pers else g a.store.scr) = g (tierOf a (tierW h)) := by
      simp only [tierOf]; split <;> rfl
    rw [hg] at hc
    split
    · rename_i hlt
      rw [derC A m _ _ hD' _ (by rw [← hc]; exact UInt64.lt_iff_toNat_lt.mp hlt)]
      exact packBFL_lp _ _ _ (bvarOfData_lt _) (fvarOfData_lt _) (b2w_le _)
    · rename_i hge
      rw [derT_out hD' _ (by rw [← hc]; exact UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp hge))]; rfl
  -- a leaf with a column (`fvar`, `sort`, `const`)
  have leaf : ∀ {α : Type} [BEq α] [Hashable α] (C : ConsSch) (R : Mem → Word → Word → α → Prop)
      (L : Lens α UInt64 .expr) (g : ETables → Tbl α EIdx UInt64)
      (A : ArrId) (hT : ConsR C R m a.store.scratchOn (g a.store.pers) (g a.store.scr))
      (hgP : L.getP a = g a.store.pers) (hgS : L.getS a = g a.store.scr)
      (hc : ColT2 L A lpW m a),
      (if idxW h < rdW (m.arr64 CTL) (C.ca + tierW h) then rdW (m.arr64 (tierA A (tierW h))) (idxW h)
       else (0 : Word)) = lpW ((g (tierOf a (tierW h))).derAt (idxW h).toNat) := by
    intro α _ _ C R L g A hT hgP hgS hc
    have := col_read A lpW m _ _ _ hT (hgP ▸ hc.1) (hgS ▸ hc.2) rfl (tierW h) (idxW h) ht
    rw [this]; simp only [tierOf]; split <;> rfl
  by_cases g1 : h >>> 28 = 1
  · simp only [g1, ↓reduceIte]; rw [derAt_fvar _ h hh g1]
    exact leaf fvarCS FVRecRel fvarLens (·.fvars) FVLP hR.fvar rfl rfl hR.fvarLp
  simp only [g1, ↓reduceIte]
  by_cases g2 : h >>> 28 = 2
  · simp only [g2, ↓reduceIte]; rw [derAt_sort _ h hh g2]
    exact leaf sortCS SoRecRel sortLens (·.sorts) SOLP hR.sort rfl rfl hR.sortLp
  simp only [g2, ↓reduceIte]
  by_cases g3 : h >>> 28 = 3
  · simp only [g3, ↓reduceIte]; rw [derAt_const _ h hh g3]
    exact leaf constCS CeRecRel constLens (·.consts) CLP hR.const rfl rfl hR.constLp
  simp only [g3, ↓reduceIte]
  by_cases g4 : h >>> 28 = 4
  · simp only [g4, ↓reduceIte]; rw [derAt_app _ h hh g4]
    exact comp appCS ARecRel (·.apps) ADER hR.app hD.app
  simp only [g4, ↓reduceIte]
  by_cases g5 : h >>> 28 = 5
  · simp only [g5, ↓reduceIte]; rw [derAt_lam _ h hh g5]
    exact comp lamCS LaRecRel (·.lams) LADER hR.lam hD.lam
  simp only [g5, ↓reduceIte]
  by_cases g6 : h >>> 28 = 6
  · simp only [g6, ↓reduceIte]; rw [derAt_forall _ h hh g6]
    exact comp forallCS FaRecRel (·.foralls) FADER hR.forallE hD.forallE
  simp only [g6, ↓reduceIte]
  by_cases g7 : h >>> 28 = 7
  · simp only [g7, ↓reduceIte]; rw [derAt_let _ h hh g7]
    exact comp letCS LeRecRel (·.lets) LEDER hR.letE hD.letE
  simp only [g7, ↓reduceIte]
  by_cases g9 : h >>> 28 = 9
  · simp only [g9, ↓reduceIte]; rw [derAt_proj _ h hh g9]
    exact comp projCS PJRecRel (·.projs) PJDER hR.proj hD.proj
  simp only [g9, ↓reduceIte]
  by_cases g0 : h >>> 28 = 0
  · rw [derAt_bvar _ h hh g0, lpW, derT_lp_false (derT2_tier hD.bvar (tierW h) ht)
      (fun _ _ _ hp => hp.2.2)]; rfl
  by_cases g8 : h >>> 28 = 8
  · rw [derAt_lit _ h hh g8, lpW, derT_lp_false (derT2_tier hD.lit (tierW h) ht)
      (fun _ _ _ hp => hp.2.2)]; rfl
  rw [derAt_other _ h hh g0 g1 g2 g3 g4 g5 g6 g7 g8 g9]; rfl

end L.Arena
