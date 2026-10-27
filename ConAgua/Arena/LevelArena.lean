import ConAgua.Arena.View
import ConAgua.Arena.LevelEquivRel
import ConRon.Arena.Core
import Std.Tactic.BVDecide.Normalize.Prop

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
    simp at this
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
theorem tier_node {α δ : Type} {k : IdxKind} [BEq α] [Hashable α] (C : ConsSch)
    (R : Mem → Word → Word → α → Prop) (m : Mem) (on : Bool)
    (P Q : Tbl α (Idx k) δ) (hR : ConsR C R m on P Q) (t : Word) (ht : t ≤ 1) (i : Word)
    (x : α) (hx : (if t = 0 then P else Q).nodes[i.toNat]? = some x) :
    ¬ cntC C m t ≤ i ∧ R m t i x := by
  have hc := hR.cnt t ht
  have hlt : i.toNat < (if t = 0 then P else Q).nodes.size := by
    rcases Array.getElem?_eq_some_iff.mp hx with ⟨h, -⟩; exact h
  refine ⟨fun e => ?_, hR.rec t ht _ _ hx⟩
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
  have hfl := ConsR.flag hR.zero
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
    obtain ⟨hc, -⟩ := tier_node zeroCS ZRecRel m _ _ _ hR.zero (tierW h) ht1 _ _ hz
    replace hc : ¬ tcnt m ZERO (tierW h) ≤ idxW h := hc
    simp [hc, lvEnc]
  by_cases g1 : h >>> 28 = 1
  · simp (config := { decide := true }) only [g1, ↓reduceIte, Option.map_eq_some_iff] at hg ⊢
    obtain ⟨z, hz, rfl⟩ := hg
    rw [Tbl.node?, hidx, apply_ite LTables.succs] at hz
    obtain ⟨hc, hr⟩ := tier_node succCS SRecRel m _ _ _ hR.succ (tierW h) ht1 _ _ hz
    replace hc : ¬ tcnt m SUCC (tierW h) ≤ idxW h := hc
    simp only [SRecRel] at hr
    simp [hc, hr, lvEnc]
  by_cases g2 : h >>> 28 = 2
  · simp (config := { decide := true }) only [g2, ↓reduceIte, Option.map_eq_some_iff] at hg ⊢
    obtain ⟨z, hz, rfl⟩ := hg
    rw [Tbl.node?, hidx, apply_ite LTables.maxs] at hz
    obtain ⟨hc, hr⟩ := tier_node maxCS MRecRel m _ _ _ hR.max (tierW h) ht1 _ _ hz
    replace hc : ¬ tcnt m MAX (tierW h) ≤ idxW h := hc
    simp only [MRecRel] at hr
    simp [hc, hr.1, hr.2, lvEnc]
  by_cases g3 : h >>> 28 = 3
  · simp (config := { decide := true }) only [g3, ↓reduceIte, Option.map_eq_some_iff] at hg ⊢
    obtain ⟨z, hz, rfl⟩ := hg
    rw [Tbl.node?, hidx, apply_ite LTables.imaxs] at hz
    obtain ⟨hc, hr⟩ := tier_node imaxCS IRecRel m _ _ _ hR.imax (tierW h) ht1 _ _ hz
    replace hc : ¬ tcnt m IMAX (tierW h) ≤ idxW h := hc
    simp only [IRecRel] at hr
    simp [hc, hr.1, hr.2, lvEnc]
  by_cases g4 : h >>> 28 = 4
  · simp (config := { decide := true }) only [g4, ↓reduceIte, Option.map_eq_some_iff] at hg ⊢
    obtain ⟨z, hz, rfl⟩ := hg
    rw [Tbl.node?, hidx, apply_ite LTables.params] at hz
    obtain ⟨hc, hr⟩ := tier_node paramCS PRecRel m _ _ _ hR.param (tierW h) ht1 _ _ hz
    replace hc : ¬ tcnt m PARAM (tierW h) ≤ idxW h := hc
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
    hR.zero, hR.succ, hR.max, hR.imax, hR.param, hR.ls, hR.nanon, hR.nstr, hR.nnum, hR.memos,
    hR.zeroHp, hR.paramHp, hR.succHp, hR.maxHp, hR.imaxHp, hR.lsHp, hR.sortLp, hR.constLp, hR.fvarLp⟩

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

/-! ## Level lists -/

/-- **A slice of handle words is related to the readbacks** (`LvsR`), element by element. -/
theorem lvsR_of_slice {m : Mem} {a : AState} (hR : ArenaR m a) :
    ∀ (ids : List LIdx) (Ls : List Level) (o n : Word),
      sliceL (vpool m) o.toNat n.toNat = lsWords ids → o.toNat + n.toNat < 2 ^ 41 →
      denoteLList a.store.ls ids = some Ls → LvsR (nameN a.store.lss.ls.ns) m o n Ls := by
  intro ids
  induction ids with
  | nil =>
    intro Ls o n hs _ hd
    have hn : n.toNat = 0 := by have := sliceL_length (vpool m) o.toNat n.toNat; rw [hs] at this; simpa [lsWords] using this.symm
    have : n = 0 := UInt64.toNat_inj.mp (by simpa using hn)
    subst this
    simp [denoteLList] at hd; subst hd; exact .nil
  | cons u us ih =>
    intro Ls o n hs hon hd
    have hlen := sliceL_length (vpool m) o.toNat n.toNat
    rw [hs] at hlen
    simp only [lsWords, List.length_map, List.length_cons] at hlen
    obtain ⟨k, hk⟩ : ∃ k, n.toNat = k + 1 := ⟨us.length, hlen.symm⟩
    rw [hk, sliceL_succ] at hs
    simp only [lsWords, List.map_cons, List.cons.injEq] at hs
    obtain ⟨h1, h2⟩ := hs
    simp only [denoteLList, opt2_eq_some_iff] at hd
    obtain ⟨l, ls, hl, hls, rfl⟩ := hd
    have hn0 : n ≠ 0 := fun e => by subst e; simp at hk
    have ho1 : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hn1 : (n - 1).toNat = k := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
    refine .cons hn0 ?_ (ih ls (o + 1) (n - 1) (by rw [ho1, hn1]; exact h2) (by omega) hls)
    have hw : prd m o = u.word.toUInt64 := by rw [← vpool_getD m o (by omega)]; exact h1
    rw [hw]; exact denoteL_lvR hR u l hl

theorem decLs_tag0 (h : Word) (hh : h.toNat < 2 ^ 32) :
    ((decI h : LsIdx).tag == LsTag.list) = (h >>> 28 == 0) := by
  have this : ((decI h : LsIdx).tag = 0 ↔ h >>> 28 = 0) := decL_tag_eq h hh 0 (by decide)
  rw [Bool.eq_iff_iff]; simp only [beq_iff_eq, LsTag.list]; exact this
where
  decL_tag_eq {k : IdxKind} (h : Word) (hh : h.toNat < 2 ^ 32) (g : Nat) (hg : g < 16) :
      ((decI h : Idx k).tag = UInt32.ofNat g) ↔ (h >>> 28 = UInt64.ofNat g) := by
    have e : (decI h : Idx k).tag = (h >>> 28).toUInt32 := by
      simp only [decI, Idx.tag]
      apply UInt32.toNat_inj.mp
      simp [UInt32.toNat_div, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight,
        Nat.shiftRight_eq_div_pow]
      omega
    rw [e]
    have hgt : (h >>> 28).toNat < 16 := by
      simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; omega
    constructor
    · intro e; apply UInt64.toNat_inj.mp
      have := congrArg UInt32.toNat e
      simp [UInt64.toNat_toUInt32] at this ⊢; omega
    · intro e; rw [e]; apply UInt32.toNat_inj.mp; simp

theorem decLs_idx (h : Word) : (decI h : LsIdx).idxNat = (idxW h).toNat := by
  simp only [decI, Idx.idxNat, Idx.index, idxW]
  simp [UInt32.toNat_mod, UInt64.toNat_toUInt32, UInt64.toNat_and]
  have : (134217727 : Nat) = 2 ^ 27 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

/-- **Under `ArenaR`, L's view of a level-list handle is the arena's**: the record's slice holds
the list's handle words, a slice in use. -/
theorem lsNodeW_store' {m : Mem} {a : AState} (hR : ArenaR m a) {h : Word} (hh : h.toNat < 2 ^ 32)
    {ids : List LIdx} (hv : a.store.lss.view (decI h) = some ids) :
    lsNodeW m h = [tfld m LVLS (tierW h) (idxW h) 0, tfld m LVLS (tierW h) (idxW h) 1] ∧
      SliceOK m (tfld m LVLS (tierW h) (idxW h) 0) (tfld m LVLS (tierW h) (idxW h) 1) ∧
      sliceL (vpool m) (tfld m LVLS (tierW h) (idxW h) 0).toNat (tfld m LVLS (tierW h) (idxW h) 1).toNat =
        lsWords ids := by
  have hfl := ConsR.flag hR.ls
  have ht1 := tierW_le h
  have hpers : (decI h : LsIdx).isPersistent = (tierW h == 0) := by rw [isPersistent_decI h hh]; rfl
  unfold LsStore.view at hv
  rw [hpers] at hv
  have hsc : ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) ∧
      (if tierW h = 0 then a.store.lss.pers else a.store.lss.scr).get (decI h) = some ids := by
    by_cases ht : tierW h = 0
    · simp only [ht, beq_self_eq_true, ↓reduceIte] at hv
      exact ⟨fun e => e.1 ht, by simpa [ht] using hv⟩
    · simp only [ht, beq_iff_eq, ↓reduceIte] at hv
      split at hv
      · rename_i hon
        refine ⟨fun e => ?_, by simpa [ht] using hv⟩
        rw [← hfl] at hon; simp [e.2] at hon
      · simp at hv
  obtain ⟨hsc, hg⟩ := hsc
  simp only [LsTables.get, decLs_tag0 h hh] at hg
  by_cases g0 : h >>> 28 = 0
  · simp only [g0, beq_self_eq_true, ↓reduceIte, Option.map_eq_some_iff] at hg
    obtain ⟨z, hz, rfl⟩ := hg
    rw [Tbl.node?, decLs_idx h, apply_ite LsTables.lists] at hz
    obtain ⟨hc, hr⟩ := tier_node lsCS LsRecRel m _ _ _ hR.ls (tierW h) ht1 _ _ hz
    replace hc : ¬ tcnt m LVLS (tierW h) ≤ idxW h := hc
    simp only [LsRecRel] at hr
    refine ⟨?_, hr.1.1, hr.2.1⟩
    simp [lsNodeW, g0, hsc, hc]
  · simp [g0] at hg

/-- `lsNodeW_store'` with the slice below the pool top. -/
theorem lsNodeW_store {m : Mem} {a : AState} (hR : ArenaR m a) {h : Word} (hh : h.toNat < 2 ^ 32)
    {ids : List LIdx} (hv : a.store.lss.view (decI h) = some ids) :
    lsNodeW m h = [tfld m LVLS (tierW h) (idxW h) 0, tfld m LVLS (tierW h) (idxW h) 1] ∧
      (tfld m LVLS (tierW h) (idxW h) 0).toNat + (tfld m LVLS (tierW h) (idxW h) 1).toNat ≤ m.top.toNat ∧
      sliceL (vpool m) (tfld m LVLS (tierW h) (idxW h) 0).toNat (tfld m LVLS (tierW h) (idxW h) 1).toNat =
        lsWords ids :=
  have h' := lsNodeW_store' hR hh hv
  ⟨h'.1, h'.2.1.1, h'.2.2⟩

/-- **A level-list handle `ls_node` reads is a node of the store**, its length the record's
count. -/
theorem lsNodeW_view {m : Mem} {a : AState} (hR : ArenaR m a) {h : Word} (hh : h.toNat < 2 ^ 32)
    (hne : lsNodeW m h ≠ []) :
    ∃ ids : List LIdx, a.store.lss.view (decI h) = some ids ∧
      (lsNodeW m h).tail.headD 0 = tfld m LVLS (tierW h) (idxW h) 1 ∧
      (tfld m LVLS (tierW h) (idxW h) 1).toNat = ids.length := by
  have hg : h >>> 28 = 0 := Classical.byContradiction fun c => hne (by simp [lsNodeW, c])
  have hsc : ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) := fun c => hne (by simp [lsNodeW, hg, c])
  have hc : ¬ tcnt m LVLS (tierW h) ≤ idxW h := fun c => hne (by
    rw [lsNodeW, ite_eq_right (by simpa using hg), ite_eq_right hsc, ite_eq_left c])
  have hval : lsNodeW m h = [tfld m LVLS (tierW h) (idxW h) 0, tfld m LVLS (tierW h) (idxW h) 1] := by
    rw [lsNodeW, ite_eq_right (by simpa using hg), ite_eq_right hsc, ite_eq_right hc]
  obtain ⟨x, hx, hr⟩ := ConsR.node hR.ls (tierW h) (tierW_le h)
    (idxW h) (UInt64.not_le.mp hc)
  refine ⟨x.us, ?_, by rw [hval]; rfl, ?_⟩
  · have hfl := ConsR.flag hR.ls
    have hpers : (decI h : LsIdx).isPersistent = (tierW h == 0) := by
      rw [isPersistent_decI h hh]; rfl
    have hget : ∀ T : LsTables, T.lists.nodes[(idxW h).toNat]? = some x →
        T.get (decI h) = some x.us := fun T hT => by
      simp only [LsTables.get, decLs_tag0 h hh, hg, beq_self_eq_true, ↓reduceIte, Tbl.node?,
        decLs_idx h, hT, Option.map_some]
    unfold LsStore.view
    rw [hpers]
    by_cases ht : tierW h = 0
    · simp only [ht, ↓reduceIte] at hx; simp only [ht, beq_self_eq_true, ↓reduceIte]; exact hget _ hx
    · simp only [ht, ↓reduceIte] at hx
      have hon : a.store.lss.scratchOn = true := by
        rw [← hfl]; simp only [bne_iff_ne, ne_eq]; exact fun h1 => hsc ⟨ht, h1⟩
      simp only [ht, beq_iff_eq, ↓reduceIte, hon]; exact hget _ hx
  · have := sliceL_length (vpool m) (tfld m LVLS (tierW h) (idxW h) 0).toNat (tfld m LVLS (tierW h) (idxW h) 1).toNat
    rw [hr.2.1] at this; simpa [lsWords] using this.symm

/-- The readback cache of lists holds readbacks. -/
def ReadLsCOK (a : AState) : Prop :=
  ∀ (h : LsIdx) (ls : List Level), a.caches.readLsC[h]? = some ls → denoteLs a.store.lss h = some ls

/-- The verdict cache of lists holds verdicts (at the pair asked). -/
def LvlsEqCOK (a : AState) (us vs : LsIdx) (lu lv : List Level) : Prop :=
  ∀ r, a.caches.lvlsEqC[(us, vs)]? = some r → Level.isEquivList lu lv = some r

theorem readLevelsM_run (a : AState) (h : LsIdx) (ls : List Level)
    (hd : denoteLs a.store.lss h = some ls) (hc : ReadLsCOK a) :
    ∃ c, (readLevelsM h).run a = .ok (ls, { a with caches := c }) ∧
      ReadLsCOK { a with caches := c } := by
  simp only [readLevelsM]
  cases e : a.caches.readLsC[h]? with
  | some l' =>
    have := hc _ _ e; rw [hd] at this; cases this
    exact ⟨a.caches, by simp [e]; rfl, hc⟩
  | none =>
    refine ⟨{ a.caches with readLsC := a.caches.readLsC.insert h ls }, ?_, ?_⟩
    · simp [e, hd]; rfl
    · intro h' l' e'
      simp only [Std.HashMap.getElem?_insert] at e'
      split at e'
      · rename_i hb; cases e'; rw [← eq_of_beq hb]; exact hd
      · exact hc _ _ e'

theorem lvlsEq?_run (a : AState) (us vs : LsIdx) (lu lv : List Level)
    (hu : denoteLs a.store.lss us = some lu) (hv : denoteLs a.store.lss vs = some lv)
    (hc : ReadLsCOK a) (he : LvlsEqCOK a us vs lu lv) :
    ∃ c, (lvlsEq? us vs).run a = .ok (Level.isEquivList lu lv, { a with caches := c }) := by
  simp only [lvlsEq?]
  cases e : a.caches.lvlsEqC[(us, vs)]? with
  | some r =>
    rw [he r e]; exact ⟨a.caches, by simp [e]; rfl⟩
  | none =>
    obtain ⟨c₁, h₁, hc₁⟩ := readLevelsM_run a us lu hu hc
    obtain ⟨c₂, h₂, -⟩ := readLevelsM_run { a with caches := c₁ } vs lv hv hc₁
    cases eq : Level.isEquivList lu lv with
    | none =>
      exact ⟨c₂, by simp [e, StateT.run_bind, h₁, except_ok_bind, h₂, eq]; rfl⟩
    | some r =>
      exact ⟨{ c₂ with lvlsEqC := c₂.lvlsEqC.insert (us, vs) r },
        by simp [e, StateT.run_bind, h₁, except_ok_bind, h₂, eq]; rfl⟩

/-- The list readback, from the list's view and the elements' readbacks. -/
theorem denoteLs_view (a : AState) (h : LsIdx) (ls : List Level)
    (hd : denoteLs a.store.lss h = some ls) :
    ∃ ids, a.store.lss.view h = some ids ∧ denoteLList a.store.ls ids = some ls := by
  simp only [denoteLs] at hd
  split at hd
  · simp at hd
  · rename_i ids hv; exact ⟨ids, hv, hd⟩

/-- **`lvls_eq` refines con-ron's `lvlsEq?`**, under the hypotheses of `lvlEq_refines` for lists. -/
@[refines ConRon.Arena.lvlsEq?]
theorem lvlsEq_refines {m m' : Mem} {a : AState} (hR : ArenaR m a)
    (hwf : NStoreWF a.store.lss.ls.ns) (us vs : LsIdx) (lu lv : List Level)
    (hu : denoteLs a.store.lss us = some lu) (hv : denoteLs a.store.lss vs = some lv)
    (hc : ReadLsCOK a) (he : LvlsEqCOK a us vs lu lv) (n : Nat) (z : Word)
    (h : lvlsEqW n m us.word.toUInt64 vs.word.toUInt64 = some (z, m')) :
    ∃ o a', (lvlsEq? us vs).run a = .ok (o, a') ∧ z = encO o ∧ ArenaR m' a' := by
  cases n with
  | zero => simp [lvlsEqW] at h
  | succ n =>
    simp only [lvlsEqW] at h
    obtain ⟨ids₁, hv₁, hd₁⟩ := denoteLs_view a us lu hu
    obtain ⟨ids₂, hv₂, hd₂⟩ := denoteLs_view a vs lv hv
    have hw₁ : (us.word.toUInt64 : Word).toNat < 2 ^ 32 := word_lt us
    have hw₂ : (vs.word.toUInt64 : Word).toNat < 2 ^ 32 := word_lt vs
    obtain ⟨e₁, t₁, s₁⟩ := lsNodeW_store hR hw₁ (by rw [decI_word]; exact hv₁)
    obtain ⟨e₂, t₂, s₂⟩ := lsNodeW_store hR hw₂ (by rw [decI_word]; exact hv₂)
    rw [e₁, e₂] at h
    simp only [List.headD_cons, List.tail_cons, reduceCtorEq, or_self, ↓reduceIte] at h
    have hR₀ : ArenaR (m.set64 CTL 192 0) a :=
      ArenaR.frame (by decide) c192_not_arena (reset_frame m) hR
    have hpool : (m.set64 CTL 192 0).arr64 POOL = m.arr64 POOL :=
      Mem.arr64_set64_ne _ _ _ _ _ (by decide)
    have hpool1 : (m.set64 CTL 192 0).arr64 POOL1 = m.arr64 POOL1 :=
      Mem.arr64_set64_ne _ _ _ _ _ (by decide)
    have hpoolv := vpool_congr hpool hpool1
    have htop := hR.lit.1.top41
    have hl₁ := lvsR_of_slice hR₀ ids₁ lu _ _ (by rw [hpoolv]; exact s₁) (by omega) hd₁
    have hl₂ := lvsR_of_slice hR₀ ids₂ lv _ _ (by rw [hpoolv]; exact s₂) (by omega) hd₂
    obtain ⟨hx, hz⟩ := equivsW_ok (nameN_rel _ hwf) n _ _ _ _ _ _ _ _ _ hl₁ hl₂ h
    have hR' : ArenaR m' a := ArenaR.frame lh_not_arena c192_not_arena hx.memFrame hR₀
    obtain ⟨c, hrun⟩ := lvlsEq?_run a us vs lu lv hu hv hc he
    exact ⟨_, _, hrun, hz, hR'.with_caches c⟩

end L.Arena
