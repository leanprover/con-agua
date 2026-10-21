import ConAgua.Arena.View
import ConAgua.Arena.LevelEquivRel
import ConRon.Arena.WFProofs
import ConRon.Arena.Core
import ConAgua.Census.Attr

/-!
# Level handles under `ArenaR`: the store's levels are related by `LvR`

The bridge from the arena to the level heap's decoder (`LevelHeapRel.lean`): under `ArenaR`, a
level handle's word `h` views in L (`lvNodeW`) as the arena's `LStore.view (decI h)`
(`lvNodeW_store`), and so `denoteL` of the handle is related to `h` by `LvR` with the name
decoder `nameN` (the store's `denoteN`, on handle words) (`denoteL_lvR`). With
`NStoreWF` (con-ron's `denoteN_inj`), `nameN` is a `NameRel`.

No readback is involved: the level algorithms run on `h` itself.
-/

open ConRon.Arena

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace L.Arena

open ConLeche

/-- The store's name decoder on handle words. -/
def nameN (ns : NStore) (w : Word) (x : Name) : Prop :=
  w.toNat < 2 ^ 32 ∧ denoteN ns (decI w) = some x

theorem nameN_rel (ns : NStore) (hwf : NStoreWF ns) : NameRel (nameN ns) := by
  refine ⟨fun w x y hx hy => ?_, fun w w' x hx hy => ?_⟩
  · exact Option.some.inj (hx.2.symm.trans hy.2)
  · have e := denoteN_inj hwf hx.2 hy.2
    have := congrArg (fun i : NIdx => i.word.toUInt64) e
    simp only [decI] at this
    apply UInt64.toNat_inj.mp
    have h1 := hx.1; have h2 := hy.1
    have := congrArg UInt64.toNat this
    simp [UInt64.toNat_toUInt32] at this
    omega

/-! ## Handle words of level handles -/

theorem decL_tag (h : Word) (hh : h.toNat < 2 ^ 32) :
    (decI h : LIdx).tag = (h >>> 28).toUInt32 := by
  simp only [decI, Idx.tag]
  apply UInt32.toNat_inj.mp
  simp [UInt32.toNat_div, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  omega

theorem decL_idx (h : Word) : (decI h : LIdx).idxNat = (idxW h).toNat := by
  simp only [decI, Idx.idxNat, Idx.index, idxW]
  simp [UInt32.toNat_mod, UInt64.toNat_toUInt32, UInt64.toNat_and]
  have : (134217727 : Nat) = 2 ^ 27 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

theorem decL_pers (h : Word) (hh : h.toNat < 2 ^ 32) :
    (decI h : LIdx).isPersistent = (tierW h == 0) := by
  rw [isPersistent_decI h hh]; rfl

/-- A node of a table relation's tier: the count is past its index, and the record relation
holds. -/
theorem tier_node {α δ : Type} {k : IdxKind} [BEq α] [Hashable α] (S : Schema)
    (R : Mem → Word → Word → α → Prop) (hs : Mem → Word → Word → Word) (m : Mem) (on : Bool)
    (P Q : Tbl α (Idx k) δ) (hR : StoreR S R hs m on P Q) (t : Word) (ht : t ≤ 1) (i : Word)
    (x : α) (hx : (if t = 0 then P else Q).nodes[i.toNat]? = some x) :
    ¬ cntW S m t ≤ i ∧ R m t i x := by
  have hT : TierR S R hs m t (if t = 0 then P else Q) := by
    rcases word_le_one t ht with rfl | rfl
    · simpa using hR.2.2.1
    · simpa using hR.2.2.2
  obtain ⟨hc, -, -, hrec, -⟩ := hT
  have hlt : i.toNat < (if t = 0 then P else Q).nodes.size := by
    rcases Array.getElem?_eq_some_iff.mp hx with ⟨h, -⟩; exact h
  refine ⟨fun e => ?_, hrec _ _ hx⟩
  rw [UInt64.le_iff_toNat_le, hc] at e; omega

/-! ## The view of a level handle -/

/-- The L view of a node view. -/
def lvEnc : LNodeView → List Word
  | .zero => [0, 0, 0]
  | .succ u => [1, u.word.toUInt64, 0]
  | .max u v => [2, u.word.toUInt64, v.word.toUInt64]
  | .imax u v => [3, u.word.toUInt64, v.word.toUInt64]
  | .param n => [4, n.word.toUInt64, 0]

theorem h32 {h : Word} (hh : h.toNat < 2 ^ 32) : h >>> 32 = 0 := by
  apply UInt64.toNat_inj.mp
  simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; omega

/-- The tag of a level handle word, as the arena reads it. -/
theorem decL_tag_eq (h : Word) (hh : h.toNat < 2 ^ 32) (g : Nat) (hg : g < 16) :
    ((decI h : LIdx).tag = UInt32.ofNat g) ↔ (h >>> 28 = UInt64.ofNat g) := by
  rw [decL_tag h hh]
  have hgt : (h >>> 28).toNat < 16 := by
    simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; omega
  constructor
  · intro e; apply UInt64.toNat_inj.mp
    have := congrArg UInt32.toNat e
    simp [UInt64.toNat_toUInt32] at this ⊢; omega
  · intro e; rw [e]; apply UInt32.toNat_inj.mp; simp

section view
variable {m : Mem} {a : AState} (hR : ArenaR m a) {h : Word} (hh : h.toNat < 2 ^ 32)
include hR hh

/-- The tier the handle names, and the scratch check, from a successful view. -/
theorem lview_tier {v : LNodeView} (hv : a.store.lss.ls.view (decI h) = some v) :
    ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) ∧
      (if tierW h = 0 then a.store.lss.ls.pers else a.store.lss.ls.scr).get (decI h) = some v := by
  have hfl := hR.zero.2.1
  unfold LStore.view at hv
  rw [decL_pers h hh] at hv
  by_cases ht : tierW h = 0
  · simp only [ht, beq_self_eq_true, ↓reduceIte] at hv
    exact ⟨fun e => e.1 ht, by simpa [ht] using hv⟩
  · simp only [ht, beq_iff_eq, ↓reduceIte] at hv
    split at hv
    · rename_i hon
      refine ⟨fun e => ?_, by simpa [ht] using hv⟩
      rw [← hfl] at hon; simp [e.2] at hon
    · simp at hv


/-- **Under `ArenaR`, L's view of a level handle is the arena's.** -/
theorem lvNodeW_store {v : LNodeView} (hv : a.store.lss.ls.view (decI h) = some v) :
    lvNodeW m h = lvEnc v := by
  obtain ⟨hsc, hg⟩ := lview_tier hR hh hv
  have ht1 := tierW_le h
  have hidx := decL_idx h
  simp only [LTables.get, decL_tag h hh] at hg
  simp only [lvNodeW, h32 hh, ne_eq, not_true_eq_false, ↓reduceIte, hsc]
  have e0 : ((decI h : LIdx).tag = 0 ↔ h >>> 28 = 0) := decL_tag_eq h hh 0 (by decide)
  have e1 : ((decI h : LIdx).tag = 1 ↔ h >>> 28 = 1) := decL_tag_eq h hh 1 (by decide)
  have e2 : ((decI h : LIdx).tag = 2 ↔ h >>> 28 = 2) := decL_tag_eq h hh 2 (by decide)
  have e3 : ((decI h : LIdx).tag = 3 ↔ h >>> 28 = 3) := decL_tag_eq h hh 3 (by decide)
  have e4 : ((decI h : LIdx).tag = 4 ↔ h >>> 28 = 4) := decL_tag_eq h hh 4 (by decide)
  rw [← decL_tag h hh] at hg
  simp only [LTag.zero, LTag.succ, LTag.max, LTag.max, LTag.imax, LTag.param, beq_iff_eq] at hg
  simp only [e0, e1, e2, e3, e4] at hg
  by_cases g0 : h >>> 28 = 0
  · simp (config := { decide := true }) only [g0, ↓reduceIte, Option.map_eq_some_iff] at hg ⊢
    obtain ⟨z, hz, rfl⟩ := hg
    rw [Tbl.node?, hidx, apply_ite LTables.zeros] at hz
    obtain ⟨hc, -⟩ := tier_node zeroSch ZRecRel zhash m _ _ _ hR.zero (tierW h) ht1 _ _ hz
    simp only [cntW, zeroSch] at hc
    simp [hc, lvEnc]
  by_cases g1 : h >>> 28 = 1
  · simp (config := { decide := true }) only [g1, ↓reduceIte, Option.map_eq_some_iff] at hg ⊢
    obtain ⟨z, hz, rfl⟩ := hg
    rw [Tbl.node?, hidx, apply_ite LTables.succs] at hz
    obtain ⟨hc, hr⟩ := tier_node succSch SRecRel shash m _ _ _ hR.succ (tierW h) ht1 _ _ hz
    simp only [cntW, succSch] at hc
    simp only [SRecRel] at hr
    simp [hc, hr, lvEnc]
  by_cases g2 : h >>> 28 = 2
  · simp (config := { decide := true }) only [g2, ↓reduceIte, Option.map_eq_some_iff] at hg ⊢
    obtain ⟨z, hz, rfl⟩ := hg
    rw [Tbl.node?, hidx, apply_ite LTables.maxs] at hz
    obtain ⟨hc, hr⟩ := tier_node maxSch MRecRel mhash m _ _ _ hR.max (tierW h) ht1 _ _ hz
    simp only [cntW, maxSch] at hc
    simp only [MRecRel] at hr
    simp [hc, hr.1, hr.2, lvEnc]
  by_cases g3 : h >>> 28 = 3
  · simp (config := { decide := true }) only [g3, ↓reduceIte, Option.map_eq_some_iff] at hg ⊢
    obtain ⟨z, hz, rfl⟩ := hg
    rw [Tbl.node?, hidx, apply_ite LTables.imaxs] at hz
    obtain ⟨hc, hr⟩ := tier_node imaxSch IRecRel imhash m _ _ _ hR.imax (tierW h) ht1 _ _ hz
    simp only [cntW, imaxSch] at hc
    simp only [IRecRel] at hr
    simp [hc, hr.1, hr.2, lvEnc]
  by_cases g4 : h >>> 28 = 4
  · simp (config := { decide := true }) only [g4, ↓reduceIte, Option.map_eq_some_iff] at hg ⊢
    obtain ⟨z, hz, rfl⟩ := hg
    rw [Tbl.node?, hidx, apply_ite LTables.params] at hz
    obtain ⟨hc, hr⟩ := tier_node paramSch PRecRel phash m _ _ _ hR.param (tierW h) ht1 _ _ hz
    simp only [cntW, paramSch] at hc
    simp only [PRecRel] at hr
    simp [hc, hr, lvEnc]
  simp [g0, g1, g2, g3, g4] at hg

end view

/-- **Under `ArenaR`, a level handle denotes its readback**: `denoteL` of the handle is related
to the handle's word by `LvR` with the store's name decoder. -/
theorem denoteLAux_lvR {m : Mem} {a : AState} (hR : ArenaR m a) (f : Nat) :
    ∀ (h : Word) (l : Level), h.toNat < 2 ^ 32 → denoteLAux a.store.lss.ls f (decI h) = some l →
      LvR (nameN a.store.lss.ls.ns) m h l := by
  induction f with
  | zero => intro h l _ e; simp [denoteLAux] at e
  | succ f ih =>
    intro h l hh e
    simp only [denoteLAux, Option.bind_eq_some_iff] at e
    obtain ⟨v, hv, e⟩ := e
    have hn := lvNodeW_store hR hh hv
    cases v with
    | zero =>
      simp at e; subst e; exact .zero (by rw [hn]; rfl)
    | succ u =>
      simp only [Option.map_eq_some_iff] at e
      obtain ⟨x, hx, rfl⟩ := e
      exact .succ (by rw [hn]; rfl) (ih _ _ (word_lt u) (by rw [decI_word]; exact hx))
    | max u w =>
      simp only [opt2_eq_some_iff] at e
      obtain ⟨x, y, hx, hy, rfl⟩ := e
      exact .max (by rw [hn]; rfl) (ih _ _ (word_lt u) (by rw [decI_word]; exact hx))
        (ih _ _ (word_lt w) (by rw [decI_word]; exact hy))
    | imax u w =>
      simp only [opt2_eq_some_iff] at e
      obtain ⟨x, y, hx, hy, rfl⟩ := e
      exact .imax (by rw [hn]; rfl) (ih _ _ (word_lt u) (by rw [decI_word]; exact hx))
        (ih _ _ (word_lt w) (by rw [decI_word]; exact hy))
    | param nidx =>
      simp only [Option.map_eq_some_iff] at e
      obtain ⟨x, hx, rfl⟩ := e
      exact .param (by rw [hn]; rfl) ⟨word_lt nidx, by rw [decI_word]; exact hx⟩

theorem denoteL_lvR {m : Mem} {a : AState} (hR : ArenaR m a) (u : LIdx) (l : Level)
    (e : denoteL a.store.lss.ls u = some l) :
    LvR (nameN a.store.lss.ls.ns) m u.word.toUInt64 l :=
  denoteLAux_lvR hR _ _ _ (word_lt u) (by rw [decI_word]; exact e)

/-! ## The twin's `lvlEq?` -/

/-- The readback cache holds readbacks. -/
def ReadLCOK (a : AState) : Prop :=
  ∀ (h : LIdx) (l : Level), a.caches.readLC[h]? = some l → denoteL a.store.ls h = some l

/-- The verdict cache holds verdicts (at the pair asked). -/
def LvlEqCOK (a : AState) (u v : LIdx) (lu lv : Level) : Prop :=
  ∀ r, a.caches.lvlEqC[(u, v)]? = some r → Level.isEquiv lu lv = some r

theorem readLevelM_run (a : AState) (h : LIdx) (l : Level) (hd : denoteL a.store.ls h = some l)
    (hc : ReadLCOK a) :
    ∃ c, (readLevelM h).run a = .ok (l, { a with caches := c }) ∧
      ReadLCOK { a with caches := c } := by
  simp only [readLevelM]
  cases e : a.caches.readLC[h]? with
  | some l' =>
    have := hc _ _ e; rw [hd] at this; cases this
    exact ⟨a.caches, by simp [e]; rfl, hc⟩
  | none =>
    refine ⟨{ a.caches with readLC := a.caches.readLC.insert h l }, ?_, ?_⟩
    · simp [e, hd]; rfl
    · intro h' l' e'
      simp only [Std.HashMap.getElem?_insert] at e'
      split at e'
      · rename_i hb; cases e'; rw [← eq_of_beq hb]; exact hd
      · exact hc _ _ e'

/-- **The twin's `lvlEq?` is `isEquiv` of the readbacks**, given its caches hold what they
claim; its state changes only in the caches. -/
theorem lvlEq?_run (a : AState) (u v : LIdx) (lu lv : Level) (hu : denoteL a.store.ls u = some lu)
    (hv : denoteL a.store.ls v = some lv) (hc : ReadLCOK a) (he : LvlEqCOK a u v lu lv) :
    ∃ c, (lvlEq? u v).run a = .ok (Level.isEquiv lu lv, { a with caches := c }) := by
  simp only [lvlEq?]
  cases e : a.caches.lvlEqC[(u, v)]? with
  | some r =>
    rw [he r e]; exact ⟨a.caches, by simp [e]; rfl⟩
  | none =>
    obtain ⟨c₁, h₁, hc₁⟩ := readLevelM_run a u lu hu hc
    obtain ⟨c₂, h₂, -⟩ := readLevelM_run { a with caches := c₁ } v lv hv hc₁
    cases eq : Level.isEquiv lu lv with
    | none =>
      exact ⟨c₂, by simp [e, StateT.run_bind, h₁, except_ok_bind, h₂, eq]; rfl⟩
    | some r =>
      exact ⟨{ c₂ with lvlEqC := c₂.lvlEqC.insert (u, v) r },
        by simp [e, StateT.run_bind, h₁, except_ok_bind, h₂, eq]; rfl⟩

/-! ## `lvl_eq` refines `lvlEq?` -/

theorem ArenaR.with_caches {m : Mem} {a : AState} (c : Caches) (hR : ArenaR m a) :
    ArenaR m { a with caches := c } :=
  ⟨hR.lit, hR.app, hR.sort, hR.const, hR.letE, hR.bvar, hR.fvar, hR.lam, hR.forallE, hR.proj,
    hR.zero, hR.succ, hR.max, hR.imax, hR.param, hR.ls, hR.nanon, hR.nstr, hR.nnum, hR.memos⟩

theorem HeapExt.memFrame {m m' : Mem} (h : HeapExt m m') : MemFrame [LH] [192] m m' :=
  ⟨fun b hb hc => h.arr b (by simpa using hb) hc, fun x hx => h.ctl x (by simpa using hx), h.size,
    h.wsize⟩

theorem reset_frame (m : Mem) : MemFrame [] [192] m (m.set64 CTL 192 0) := by
  refine ⟨fun b _ hc => Mem.arr64_set64_ne _ _ _ _ _ hc, fun x hx => ?_, fun b => size_set64L _ _ _ _ _,
    Mem.words_size_set64 _ _ _ _⟩
  rw [rdW_set64L]; simp only [List.mem_singleton] at hx; simp [Ne.symm hx]

theorem lh_not_arena : ∀ b ∈ [LH], b ∉ arenaArrs := by decide
theorem c192_not_arena : ∀ x ∈ [(192 : Word)], x ∉ arenaCtl := by
  intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact not_mem_arenaCtl _ (by decide)

/-- **`lvl_eq` refines con-ron's `lvlEq?`**: under `ArenaR`, with the name store well-formed
(`denoteN` injective), the two handles' readbacks defined, and the twin's caches holding what
they claim (`readLC`, `lvlEqC` are not represented in L), the L answer is the encoding of the
twin's, and the relation holds after (L wrote only the heap; the twin only its caches). -/
@[refines ConRon.Arena.lvlEq?]
theorem lvlEq_refines {m m' : Mem} {a : AState} (hR : ArenaR m a)
    (hwf : NStoreWF a.store.lss.ls.ns) (u v : LIdx) (lu lv : Level)
    (hu : denoteL a.store.ls u = some lu) (hv : denoteL a.store.ls v = some lv)
    (hc : ReadLCOK a) (he : LvlEqCOK a u v lu lv) (n : Nat) (z : Word)
    (h : lvlEqW n m u.word.toUInt64 v.word.toUInt64 = some (z, m')) :
    ∃ o a', (lvlEq? u v).run a = .ok (o, a') ∧ z = encO o ∧ ArenaR m' a' := by
  cases n with
  | zero => simp [lvlEqW] at h
  | succ n =>
    simp only [lvlEqW] at h
    have hR₀ : ArenaR (m.set64 CTL 192 0) a :=
      ArenaR.frame (by decide) c192_not_arena (reset_frame m) hR
    have hl := denoteL_lvR hR₀ u lu hu
    have hr := denoteL_lvR hR₀ v lv hv
    obtain ⟨hx, hz⟩ := equivW_ok (nameN_rel _ hwf) n _ _ _ _ _ _ _ hl hr h
    have hR' : ArenaR m' a := ArenaR.frame lh_not_arena c192_not_arena hx.memFrame hR₀
    obtain ⟨c, hrun⟩ := lvlEq?_run a u v lu lv hu hv hc he
    exact ⟨_, _, hrun, hz, hR'.with_caches c⟩

/-! ## The run -/

/-- The level program's functions. -/
def levelFns : List FnName := levelProg.map Prod.fst

/-- **The write set**: the level program writes only the heap and its top. -/
theorem levelProg_closed : closedA levelProg [LH] [192] levelFns = true := by decide +kernel

/-- **A run of `lvl_eq` refines `lvlEq?`** (from `lvlEq_refines` and `lvlEq_spec`). -/
theorem lvlEq_run {m m' : Mem} {a : AState} (hR : ArenaR m a) (hwf : NStoreWF a.store.lss.ls.ns)
    (u v : LIdx) (lu lv : Level) (hu : denoteL a.store.ls u = some lu)
    (hv : denoteL a.store.ls v = some lv) (hc : ReadLCOK a) (he : LvlEqCOK a u v lu lv)
    (fuel : Nat) (r : List Word)
    (hrun : run levelProg fuel "lvl_eq" [u.word.toUInt64, v.word.toUInt64] m = .ok (r, m')) :
    ∃ o a', (lvlEq? u v).run a = .ok (o, a') ∧ r.headD 0 = encO o ∧ ArenaR m' a' := by
  simp only [run] at hrun
  cases hr : (invoke levelProg (exec levelProg fuel) "lvl_eq"
      [u.word.toUInt64, v.word.toUInt64]).run { mem := m, loc := Locals.init [] } with
  | error e => simp [hr, Except.map] at hrun
  | ok rs =>
    simp only [hr, Except.map] at hrun
    injection hrun with hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
    have := M.of_run (P := fun s => s = { mem := m, loc := Locals.init [] }) rfl hr
      (lvlEq_spec levelProg levelProg_ok rfl rfl fuel _ _ _)
    exact lvlEq_refines hR hwf u v lu lv hu hv hc he fuel _ this.2

end L.Arena
