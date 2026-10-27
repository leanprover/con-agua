import ConAgua.Arena.LsStore
import ConAgua.Arena.LpColRel
import ConAgua.Arena.LitRefine
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The level-list store refines the arena's level-list tables

The first table with a variable-length key that is not a number: `ListNode { us : List LIdx }`
(`ConAgua/Arena/LsStore.lean` has the L code). The list lives in the pool, one handle word per
element (`lsWords`), and the record points at the slice. The schema `lsSch` (`LSREC`, `LSSLOT`,
three words per node, counts at `CTL[40 + t]`, tag `0`), the record relation `LsRecRel` (a slice
below the pool top holding the list's words, and its hash), the node hash `lshash` (word 2), the
lens `lsLens` on `a.store.lss`'s two tables. Matching is equality of lists by `slice_key`
(`PoolSlice.lean`) and the injectivity of `lsWords`; there is no scratch skip.

`LsR m a` is the library's `ConsR`; `internLs_refines`: `intern_ls(o, l)` refines
`internLsNode us` for the list `us` whose words the slice holds, under `LsR` and `PoolOK`.
`LsR.grow`: the pool growing keeps the relation (as `LitR.grow`).

Not represented: the derived column (`LsStore.derOfView`, through `mixHash`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

/-- The words of a level list: its handle words. -/
def lsWords (us : List LIdx) : List Word := us.map fun u => u.word.toUInt64

theorem lsWords_inj (us vs : List LIdx) (h : lsWords us = lsWords vs) : us = vs :=
  (List.map_inj_right fun u v h => by
    cases u; cases v; simp only [Idx.ofWord.injEq]; exact UInt32.toUInt64_inj.mp h).mp h

/-- The arena's level-list cons key. -/
abbrev lsKey (us : List LIdx) : ListNode := ⟨us⟩

/-- `a` with the scratch / persistent level-list table replaced. -/
def withScrLists (a : AState) (t : Tbl ListNode LsIdx LDer) : AState :=
  { a with store := { a.store with lss := { a.store.lss with
      scr := { a.store.lss.scr with lists := t } } } }
def withPersLists (a : AState) (t : Tbl ListNode LsIdx LDer) : AState :=
  { a with store := { a.store with lss := { a.store.lss with
      pers := { a.store.lss.pers with lists := t } } } }

/-- The level-list store's two tables. -/
def lsLens : Lens ListNode LDer .levels where
  on a := a.store.lss.scratchOn
  getP a := a.store.lss.pers.lists
  getS a := a.store.lss.scr.lists
  setP := withPersLists
  setS := withScrLists
  on_setP _ _ := rfl
  on_setS _ _ := rfl
  getP_setP _ _ := rfl
  getS_setP _ _ := rfl
  getP_setS _ _ := rfl
  getS_setS _ _ := rfl

/-- `internLsNode` is the library's protocol, with no skip. -/
theorem internLsNode_run (us : List LIdx) (a : AState) :
    (internLsNode us).run a =
      protoRun lsLens (lsKey us) LsTag.list a.store.lss.pers.lists.cons[lsKey us]?
        (a.store.lss.derOfView us) (.native "arena: level-list array full") a := by
  simp only [internLsNode, LsStore.find?, LsTables.find?, Tbl.find?, LsTables.sizeOf,
    EStore.internLevels, LsStore.intern, LsTables.push]
  cases hp : a.store.lss.pers.lists.cons[lsKey us]? <;> cases hs : a.store.lss.scratchOn <;>
    cases hc : a.store.lss.scr.lists.cons[lsKey us]? <;>
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hp, hs, hc, Bool.false_eq_true,
      ↓reduceIte, lsKey, protoRun, lsLens] <;>
    (try split) <;> simp_all [withScrLists, withPersLists, fail,
      throwThe, MonadExceptOf.throw, StateT.run, set, StateT.set,
      StateT.lift, bind, Except.bind, pure, Except.pure, StateT.bind, StateT.pure]

/-! ## The relation between L memory and the arena's level-list tables -/

/-- The level-list schema: `LSREC`, `LSSLOT`, three words per node, the counts at `CTL[40 + t]`. -/
def lsSch : Schema := ⟨LSREC, LSSLOT, 3, 40, LsTag.list⟩

theorem lsSch_wf : lsSch.WF :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

theorem fld_ls0 (m : Mem) (t i : Word) : fld lsSch m t i 0 = rdW (m.arr64 (tierA LSREC t)) (i * 3) := by
  simp [fld, Schema.ad, lsSch]
theorem fld_ls (m : Mem) (t i f : Word) :
    fld lsSch m t i f = rdW (m.arr64 (tierA LSREC t)) (i * 3 + f) := rfl

/-- The offset and length words of node `i` of tier `t`. -/
abbrev lsO (m : Mem) (t i : Word) : Word := rdW (m.arr64 (tierA LSREC t)) (i * 3)
abbrev lsL (m : Mem) (t i : Word) : Word := rdW (m.arr64 (tierA LSREC t)) (i * 3 + 1)

/-- Node `i` of tier `t` holds the list `k.us`: a slice below the pool top holding its handle
words, and the slice's hash. -/
def LsRecRel (m : Mem) (t i : Word) (k : ListNode) : Prop :=
  RSlice m t (tfld m LVLS t i 0) (tfld m LVLS t i 1) ∧
  sliceL (vpool m) (tfld m LVLS t i 0).toNat (tfld m LVLS t i 1).toNat = lsWords k.us ∧
  tfld m LVLS t i 2 = hashN (tpool m) (tfld m LVLS t i 0).toNat (tfld m LVLS t i 1).toNat

/-- `LsRecRel` in the raw words (inside the store library). -/
theorem LsRecRel_raw (m : Mem) (t i : Word) (k : ListNode) :
    LsRecRel m t i k ↔
    RSlice m t (lsO m t i) (lsL m t i) ∧
    sliceL (vpool m) (lsO m t i).toNat (lsL m t i).toNat = lsWords k.us ∧
    rdW (m.arr64 (tierA LSREC t)) (i * 3 + 2) = hashN (tpool m) (lsO m t i).toNat (lsL m t i).toNat
  := Iff.rfl

/-- **The state relation** of the level-list store: the library's relation for its two tables. -/
def LsR (m : Mem) (a : AState) : Prop :=
  ConsR lsCS LsRecRel m a.store.lss.scratchOn a.store.lss.pers.lists a.store.lss.scr.lists

/-- A node's relation and hash depend on its three words, the pool and the top. -/
theorem lsFrame : RFrame lsSch LsRecRel lshash := by
  intro m m' t i ⟨hb, htop⟩ hf
  have h0 := hf 0 (by decide)
  have h1 := hf 1 (by decide)
  have h2 := hf 2 (by decide)
  rw [fld_ls0, fld_ls0] at h0
  rw [fld_ls, fld_ls] at h1 h2
  have hp : m'.arr64 POOL = m.arr64 POOL := hb POOL (by decide) (by decide) (by decide) (by decide) (by decide)
  have hp₁ : m'.arr64 POOL1 = m.arr64 POOL1 := hb POOL1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hpₜ : m'.arr64 PT0 = m.arr64 PT0 := hb PT0 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hpv := vpool_congr hp hp₁
  have hpq := tpool_congr hp hp₁
  have ht : m'.top = m.top := htop
  have hrs := fun t o l => RSlice_congr (m := m) (m' := m') t o l ht (ptop0_congr hpₜ)
  refine ⟨fun a h => ?_, by simp only [lshash, h2]⟩
  simpa only [LsRecRel_raw, lsO, lsL, h0, h1, h2, hpv, hpq, hrs] using h

/-! ## The query's obligations -/

/-- The match of `ls_match` on node `i` of tier `t`. -/
def lsMt (m : Mem) (o l h t i : Word) : Bool := lsmatchW (m.arr64 (tierA LSREC t)) (tpool m) t i o l h

section query
variable (m : Mem) (hpool : PoolOK m) (o l : Word) (hq : SliceOK m o l) (us : List LIdx)
  (hk : sliceL (vpool m) o.toNat l.toNat = lsWords us)

include hpool hq hk in
/-- **Matching is equality of level lists**, on a node of a represented tier. -/
theorem lsMatchOK :
    MatchOK LsRecRel (lsMt m o l (hashN (tpool m) o.toNat l.toNat)) m (lsKey us) := by
  intro t i k hr
  obtain ⟨hsl, hw, hh⟩ := (LsRecRel_raw m t i k).mp hr
  have hle := hsl.le
  have hq1 := hq.le
  have htop := hpool.2.2.2.1
  have hpc := pcap_eq m (by have := hpool.2.2.1; omega)
  have hw' : sliceL (tpool m) (lsO m t i).toNat (lsL m t i).toNat = lsWords k.us := by
    rw [sliceL_tpool m _ _ (by omega)]; exact hw
  have hk' : sliceL (tpool m) o.toNat l.toNat = lsWords us := by
    rw [sliceL_tpool m _ _ (by omega)]; exact hk
  have key := slice_key (tpool m) (lsO m t i) (lsL m t i) o l (by omega) (by omega)
  simp only [lsMt, lsmatchW, Bool.and_assoc]
  constructor
  · intro h
    simp only [Bool.and_eq_true] at h
    have := key.mp (by simpa only [Bool.and_eq_true] using h.2)
    rw [hw', hk'] at this
    obtain ⟨k⟩ := k
    exact congrArg ListNode.mk (lsWords_inj _ _ this)
  · intro h
    subst h
    have e : sliceL (tpool m) (lsO m t i).toNat (lsL m t i).toNat =
        sliceL (tpool m) o.toNat l.toNat := by rw [hw', hk']
    have := key.mpr e
    simp only [Bool.and_eq_true] at this
    simp only [Bool.and_eq_true, this, and_true, beq_iff_eq, hh]
    exact slice_key_hash _ _ _ _ _ _ e

theorem lsHomeOK (h : Word) : HomeOK lshash (lsMt m o l h) m h := by
  intro t i hm
  simp only [lsMt, lsmatchW, Bool.and_eq_true, beq_iff_eq] at hm
  exact hm.1.1

variable (hq0 : m.flag = 0 → o.toNat < 2 ^ 40)

include hq hk hq0 in
/-- The record `ls_push` writes holds the list. -/
theorem lsNewOK :
    NewOKR lsSch LsRecRel lshash m [o, l, hashN (tpool m) o.toNat l.toNat]
      (lsKey us) (hashN (tpool m) o.toNat l.toNat) := by
  intro t ht hroom ht0
  have hp : (newRecM lsSch m t [o, l, hashN (tpool m) o.toNat l.toNat]).arr64 POOL = m.arr64 POOL :=
    wrRec_arr_ne lsSch _ _ POOL (ne_tierA (by decide) (by decide) (by decide) _) _ _ _
  have hp₁ : (newRecM lsSch m t [o, l, hashN (tpool m) o.toNat l.toNat]).arr64 POOL1 = m.arr64 POOL1 :=
    wrRec_arr_ne lsSch _ _ POOL1 (tierA_ne_pool _ (by decide) _).2.symm _ _ _
  have hpₜ : (newRecM lsSch m t [o, l, hashN (tpool m) o.toNat l.toNat]).arr64 PT0 = m.arr64 PT0 :=
    wrRec_arr_ne lsSch _ _ PT0 (ne_tierA (by decide) (by decide) (by decide) _) _ _ _
  have hpv := vpool_congr hp hp₁
  have hpq := tpool_congr hp hp₁
  have htop : rdW ((newRecM lsSch m t [o, l, hashN (tpool m) o.toNat l.toNat]).arr64 CTL) 0 =
      rdW (m.arr64 CTL) 0 := by
    rw [newRecM, wrRec_arr_ne lsSch _ _ CTL (ne_tierA (by decide) (by decide) (by decide) _)]
  have hrs : RSlice (newRecM lsSch m t [o, l, hashN (tpool m) o.toNat l.toNat]) t o l :=
    (RSlice_congr t o l (by simp only [top_rdW]; exact htop) (ptop0_congr hpₜ)).mpr (RSlice.intern hq hq0 ht0)
  have e : ∀ f, f < 3 → fld lsSch (newRecM lsSch m t [o, l, hashN (tpool m) o.toNat l.toNat]) t
      (cntW lsSch m t) f =
      [o, l, hashN (tpool m) o.toNat l.toNat].getD f.toNat 0 := by
    intro f hf
    have := hroom.1
    have := hroom.2
    rw [fld_newRecM lsSch lsSch_wf] <;> simp only [lsSch, Schema.ad] at * <;> grind
  have e0 := e 0 (by decide)
  have e1 := e 1 (by decide)
  have e2 := e 2 (by decide)
  rw [fld_ls0] at e0
  rw [fld_ls] at e1 e2
  simp only [lsKey, LsRecRel_raw, lshash, lsO, lsL, e0, e1, e2, hpv, hpq, ← top_rdW] at htop hrs ⊢
  simp only [List.getD_cons_zero, List.getD_cons_succ, show (1 : Word).toNat = 0 + 1 from rfl,
    show (2 : Word).toNat = 1 + 1 from rfl, show (0 : Word).toNat = 0 from rfl]
  exact ⟨⟨hrs, hk, trivial⟩, trivial⟩

end query

/-! ## The bridges from the L models -/

theorem lspushOK_room (m : Mem) (t : Word) (h : lspushOK m t = true) : PushRoom lsSch m t := by
  simp only [lspushOK, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [PushRoom, cntW, lscnt, lsSch, len64_eq] at *
  grind

/-- **The level-list table's shape.** -/
theorem lsCS_wf : lsCS.WF where
  sch := lsSch_wf
  P := by decide
  S := by decide
  col A h := by
    simp only [lsCS, Option.some.injEq] at h; subst h
    exact ⟨by decide, by decide, by decide, fun m u k x t i => by
      simp only [lsCS, lshash, Mem.arr64_set64_ne _ _ _ _ _
        (tierA_ne (by decide) (by decide) (show LSREC ≠ LSHP by decide) t u)]⟩
  room m t h := (lspushOK_room m t ((lspushOK_eqC m t).trans h)).2
  colRoom A h m t ht hp := by
    simp only [lsCS, Option.some.injEq] at h; subst h
    rw [← lspushOK_eqC] at hp
    simp only [lspushOK, Bool.and_eq_true, decide_eq_true_eq] at hp
    exact colRoom_of m LSHP _ t hp.2
  colLt A h := by
    simp only [lsCS, Option.some.injEq] at h; subst h; decide
  vs ks h hk := by simp [pushArgs, lsCS, hk]
  ex h := by simp [lsCS] at h

/-- `LsRecRel` does not read the column. -/
theorem lsColFree : ColFree lsCS LsRecRel := by
  intro A h m u k x t i a hr
  simp only [lsCS, Option.some.injEq] at h; subst h
  have hp : (m.set64 (tierA LSHP u) k x).arr64 POOL = m.arr64 POOL :=
    Mem.arr64_set64_ne _ _ _ _ _ (ne_tierA (by decide) (by decide) (by decide) u)
  have hp₁ : (m.set64 (tierA LSHP u) k x).arr64 POOL1 = m.arr64 POOL1 :=
    Mem.arr64_set64_ne _ _ _ _ _ (tierA_ne_pool _ (by decide) u).2.symm
  have hpₜ : (m.set64 (tierA LSHP u) k x).arr64 PT0 = m.arr64 PT0 :=
    Mem.arr64_set64_ne _ _ _ _ _ (ne_tierA (by decide) (by decide) (by decide) u)
  have hpv := vpool_congr hp hp₁
  have hpq := tpool_congr hp hp₁
  have hc : (m.set64 (tierA LSHP u) k x).arr64 CTL = m.arr64 CTL :=
    Mem.arr64_set64_ne _ _ _ _ _ (ne_tierA (by decide) (by decide) (by decide) u)
  have hrs := fun t o l => RSlice_congr (m := m) (m' := m.set64 (tierA LSHP u) k x) t o l
    (by simp only [Mem.top, hc]) (ptop0_congr hpₜ)
  simpa only [LsRecRel_raw, lsO, lsL, top_rdW, hpv, hpq, hrs, hc,
    Mem.arr64_set64_ne _ _ _ _ _ (tierA_ne (by decide) (by decide) (show LSREC ≠ LSHP by decide) t u)] using hr

/-- **What `intern_ls` changes**: the table's arrays, the column, the counts. -/
theorem lsinternW_frame (m : Mem) (o l : Word) (w : Word) (m' : Mem) (hI : lsinternW m o l = some (w, m')) :
    MemFrame [LSREC, LSREC + 256, LSSLOT, LSSLOT + 256, LSHP, LSHP + 256] [40, 41] m m' :=
  consInternM_frame lsCS_wf hI

theorem lsLocal : RLocal lsSch LsRecRel lshash [POOL, POOL1, PT0] [0] := by
  intro m m' hra hb hc
  have h0 := hc 0 (by simp)
  have hp := hb POOL (by simp)
  have hp₁ := hb POOL1 (by simp)
  have hpₜ := hb PT0 (by simp)
  have hpv := vpool_congr hp hp₁
  have hpq := tpool_congr hp hp₁
  have hrs := fun t o l => RSlice_congr (m := m) (m' := m') t o l (by simp only [top_rdW]; exact h0)
    (ptop0_congr hpₜ)
  simp only [lsSch] at hra
  refine ⟨fun t i k h => ?_, fun t i => by simp only [lshash, hra]⟩
  simpa only [LsRecRel_raw, lsO, lsL, hra, hpv, hpq, hrs] using h

/-! ## `intern_ls` refines `internLsNode` -/

section intern
variable (m : Mem) (a : AState) (hpool : PoolOK m) (hR : LsR m a) (o l : Word)
  (hq : SliceOK m o l) (us : List LIdx) (hk : sliceL (vpool m) o.toNat l.toNat = lsWords us)

variable (hq0 : m.flag = 0 → o.toNat < 2 ^ 40)

include hpool hR hq hk hq0 in
/-- **`intern_ls`'s model refines the arena's `internLsNode`** at the list the slice holds. -/
theorem lsintern_correct (w : Word) (m' : Mem) (hI : lsinternW m o l = some (w, m')) :
    AM.ok (internLsNode us) a ∧ LsR m' (AM.st (internLsNode us) a) ∧
    AM.res (internLsNode us) a = decI w :=
  consIntern_correct lsCS_wf lsFrame lsColFree lsLens a hR _ _ _ _ _
    (internLsNode_run us a) false rfl [o, l] (by simp [skipC, lsCS]) (by simp)
    ⟨rfl, lsMatchOK m hpool o l hq us hk, lsHomeOK m o l _, lsNewOK m o l hq us hk hq0⟩ w m' hI

include hpool hR hq hk hq0 in
/-- **The column across `intern_ls`**: the new node's word is its record's bit (`hb`). -/
theorem lsintern_hp (hC : ColT2 lsLens LSHP hpW m a)
    (hb : lsOrW m o l.toNat = b2w (a.store.lss.derOfView us).hasParam) (w : Word) (m' : Mem)
    (hI : lsinternW m o l = some (w, m')) :
    ColT2 lsLens LSHP hpW m' (AM.st (internLsNode us) a) := by
  obtain ⟨hok, hX, hres⟩ := lsintern_correct m a hpool hR o l hq us hk hq0 w m' hI
  have hcs := AM.proto_casesG lsLens _ _ _ _ _ _ a (internLsNode_run us a) hok
  exact colMkC lsCS_wf rfl lsLens hpW hR hX hC hI hcs
    (by show lsOrW m o l.toNat = _; rw [hb]; rfl)

end intern

/-! ## Appending to the pool preserves the relation -/

section grow
variable (m m' : Mem) (hg : Grows m m')

include hg in
theorem LsRecRel_grow (hpool : PoolOK m) (t i : Word) (k : ListNode) (h : LsRecRel m t i k) :
    LsRecRel m' t i k := by
  have hr := grow_arr m m' hg (tierA LSREC t) (tierA_ne_pool _ (by decide) t)
    (ne_tierA (by decide) (by decide) (by decide) t).symm
  have h41 := hpool.top41
  have hta := hg.tagree (by omega)
  have hag := hg.agree
  simp only [LsRecRel_raw, lsO, lsL, hr] at h ⊢
  obtain ⟨hsl, hw, hh⟩ := h
  have hle := hsl.le
  exact ⟨hsl.grows hg, by rw [Agree.sliceL _ _ _ _ _ hag hle, hw],
    by rw [Agree.hashN _ _ _ _ _ hta hle, hh]⟩

include hg in
/-- **Appending to the pool preserves the relation.** -/
theorem LsR.grow (hpool : PoolOK m) (a : AState) (hR : LsR m a) : LsR m' a := by
  have hr : ∀ t, m'.arr64 (tierA LSREC t) = m.arr64 (tierA LSREC t) := fun t =>
    grow_arr m m' hg _ (tierA_ne_pool _ (by decide) t) (ne_tierA (by decide) (by decide) (by decide) t).symm
  refine ConsR.mono hR hr (fun t => grow_arr m m' hg _ (tierA_ne_pool _ (by decide) t) (ne_tierA (by decide) (by decide) (by decide) t).symm)
    (by rw [hg.frame.ctl, Mem.size_arr64_set64]) (fun x hx => grow_ctl m m' hg x ?_)
    (fun t i k => LsRecRel_grow m m' hg hpool t i k) (fun t i => by simp only [lsCS, lshash, hr])
  rcases hx with rfl | rfl | rfl | rfl <;> decide

end grow

end L.Arena
