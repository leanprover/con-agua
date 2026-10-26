import ConAgua.Arena.ConsLibRel
import ConAgua.Arena.SimLib
import ConAgua.Arena.PoolSlice
import ConAgua.Arena.LsStore

import ConAgua.Arena.NStrStore

/-!
# The name store's `str` table refines the arena's `str` tables

`StrNode { pre : NIdx, s : String }` (`ConAgua/Arena/NStrStore.lean` has the L code): the prefix
handle word in the record, the string's UTF-8 bytes in the pool, one per word (`strWords`). The
schema `nstrSch` (`NSREC`, `NSSLOT`, four words per node, counts at `CTL[36 + t]`, tag `1`), the
record relation `NsRecRel` (the prefix word; a slice below the pool top holding the string's
bytes; the hash), the node hash `nshash` (word 3), the lens `nstrLens` on the name store's two
`str` tables (`a.store.lss.ls.ns`). Matching is equality of names by the prefix word and
`slice_key` (`PoolSlice.lean`) with the injectivity of `strWords`; there is no scratch skip.

`NStrR m a` is the library's `ConsR`; `internNStr_refines`: `intern_nstr(q, o, l)` refines
`internNNode (.str (decI q) s)` for the string `s` whose bytes the slice holds, under `NStrR` and
`PoolOK`. `NStrR.grow`: the pool growing keeps the relation.

Not represented: the derived column (`NStore.derOfView`, through `mixHash` and `hash s`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

/-- The arena's name `str` cons key. -/
abbrev nstrKey (pre : NIdx) (s : String) : StrNode := ⟨pre, s⟩

/-- `a` with the scratch / persistent name `str` table replaced. -/
def withScrNStrs (a : AState) (t : Tbl StrNode NIdx UInt64) : AState :=
  { a with store := { a.store with lss := { a.store.lss with ls := { a.store.lss.ls with
      ns := { a.store.lss.ls.ns with scr := { a.store.lss.ls.ns.scr with strs := t } } } } } }
def withPersNStrs (a : AState) (t : Tbl StrNode NIdx UInt64) : AState :=
  { a with store := { a.store with lss := { a.store.lss with ls := { a.store.lss.ls with
      ns := { a.store.lss.ls.ns with pers := { a.store.lss.ls.ns.pers with strs := t } } } } } }

/-- The name store's two `str` tables. -/
def nstrLens : Lens StrNode UInt64 .name where
  on a := a.store.lss.ls.ns.scratchOn
  getP a := a.store.lss.ls.ns.pers.strs
  getS a := a.store.lss.ls.ns.scr.strs
  setP := withPersNStrs
  setS := withScrNStrs
  on_setP _ _ := rfl
  on_setS _ _ := rfl
  getP_setP _ _ := rfl
  getS_setP _ _ := rfl
  getP_setS _ _ := rfl
  getS_setS _ _ := rfl

/-- `internNNode` at a `str` node is the library's protocol, with no skip. -/
theorem internNNode_str_run (pre : NIdx) (s : String) (a : AState) :
    (internNNode (.str pre s)).run a =
      protoRun nstrLens (nstrKey pre s) NTag.str a.store.lss.ls.ns.pers.strs.cons[nstrKey pre s]?
        (a.store.lss.ls.ns.derOfView (.str pre s)) (.native "arena: name constructor array full")
        a := by
  simp only [internNNode, EStore.ns, NStore.find?, NTables.find?, Tbl.find?, NTables.sizeOf,
    EStore.internName, LsStore.internName, LStore.internName, NStore.intern, NTables.push]
  cases hp : a.store.lss.ls.ns.pers.strs.cons[nstrKey pre s]? <;>
    cases hs : a.store.lss.ls.ns.scratchOn <;>
    cases hc : a.store.lss.ls.ns.scr.strs.cons[nstrKey pre s]? <;>
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hp, hs, hc, Bool.false_eq_true,
      ↓reduceIte, nstrKey, protoRun, nstrLens] <;>
    (try split) <;> simp_all [withScrNStrs, withPersNStrs, fail,
      throwThe, MonadExceptOf.throw, StateT.run, set, StateT.set,
      StateT.lift, bind, Except.bind, pure, Except.pure, StateT.bind, StateT.pure]

/-! ## The relation between L memory and the arena's name `str` tables -/

/-- The name `str` schema: `NSREC`, `NSSLOT`, four words per node, the counts at `CTL[36 + t]`. -/
def nstrSch : Schema := ⟨NSREC, NSSLOT, 4, 36, NTag.str⟩

theorem nstrSch_wf : nstrSch.WF :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

theorem fld_nstr0 (m : Mem) (t i : Word) :
    fld nstrSch m t i 0 = rdW (m.arr64 (tierA NSREC t)) (i * 4) := by
  simp [fld, Schema.ad, nstrSch]
theorem fld_nstr (m : Mem) (t i f : Word) :
    fld nstrSch m t i f = rdW (m.arr64 (tierA NSREC t)) (i * 4 + f) := rfl

/-- The prefix, offset and length words of node `i` of tier `t`. -/
abbrev nsQ (m : Mem) (t i : Word) : Word := rdW (m.arr64 (tierA NSREC t)) (i * 4)
abbrev nsO (m : Mem) (t i : Word) : Word := rdW (m.arr64 (tierA NSREC t)) (i * 4 + 1)
abbrev nsL (m : Mem) (t i : Word) : Word := rdW (m.arr64 (tierA NSREC t)) (i * 4 + 2)

/-- Node `i` of tier `t` holds `str k.pre k.s`: the prefix's handle word, a slice below the pool
top holding the string's bytes, and the hash. -/
def NsRecRel (m : Mem) (t i : Word) (k : StrNode) : Prop :=
  tfld m NSTR t i 0 = k.pre.word.toUInt64 ∧
  RSlice m t (tfld m NSTR t i 1) (tfld m NSTR t i 2) ∧
  sliceL (vpool m) (tfld m NSTR t i 1).toNat (tfld m NSTR t i 2).toNat = strWords k.s ∧
  tfld m NSTR t i 3 =
    nstrHashW (tfld m NSTR t i 0) (hashN (tpool m) (tfld m NSTR t i 1).toNat (tfld m NSTR t i 2).toNat)

/-- `NsRecRel` in the raw words (inside the store library). -/
theorem NsRecRel_raw (m : Mem) (t i : Word) (k : StrNode) :
    NsRecRel m t i k ↔
    nsQ m t i = k.pre.word.toUInt64 ∧
    RSlice m t (nsO m t i) (nsL m t i) ∧
    sliceL (vpool m) (nsO m t i).toNat (nsL m t i).toNat = strWords k.s ∧
    rdW (m.arr64 (tierA NSREC t)) (i * 4 + 3) =
      nstrHashW (nsQ m t i) (hashN (tpool m) (nsO m t i).toNat (nsL m t i).toNat)
  := Iff.rfl

/-- **The state relation** of the name `str` table: the library's relation for its two tables. -/
def NStrR (m : Mem) (a : AState) : Prop :=
  ConsR nstrCS NsRecRel m a.store.lss.ls.ns.scratchOn a.store.lss.ls.ns.pers.strs
    a.store.lss.ls.ns.scr.strs

/-- A node's relation and hash depend on its four words, the pool and the top. -/
theorem nstrFrame : RFrame nstrSch NsRecRel nshash := by
  intro m m' t i ⟨hb, htop⟩ hf
  have h0 := hf 0 (by decide)
  have h1 := hf 1 (by decide)
  have h2 := hf 2 (by decide)
  have h3 := hf 3 (by decide)
  rw [fld_nstr0, fld_nstr0] at h0
  rw [fld_nstr, fld_nstr] at h1 h2 h3
  have hp : m'.arr64 POOL = m.arr64 POOL := hb POOL (by decide) (by decide) (by decide) (by decide) (by decide)
  have hp₁ : m'.arr64 POOL1 = m.arr64 POOL1 := hb POOL1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hpₜ : m'.arr64 PT0 = m.arr64 PT0 := hb PT0 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hpv := vpool_congr hp hp₁
  have hpq := tpool_congr hp hp₁
  have ht : m'.top = m.top := htop
  have hrs := fun t o l => RSlice_congr (m := m) (m' := m') t o l ht (ptop0_congr hpₜ)
  refine ⟨fun a h => ?_, by simp only [nshash, h3]⟩
  simpa only [NsRecRel_raw, nsQ, nsO, nsL, h0, h1, h2, h3, hpv, hpq, hrs] using h

/-! ## The query's obligations -/

/-- The match of `nstr_match` on node `i` of tier `t`. -/
def nsMt (m : Mem) (q o l h t i : Word) : Bool :=
  nsmatchW (m.arr64 (tierA NSREC t)) (tpool m) t i q o l h

section query
variable (m : Mem) (hpool : PoolOK m) (q o l : Word) (hqw : q.toNat < 2 ^ 32)
  (hq : SliceOK m o l) (s : String) (hk : sliceL (vpool m) o.toNat l.toNat = strWords s)

include hpool hqw hq hk in
/-- **Matching is equality of names**, on a node of a represented tier. -/
theorem nstrMatchOK :
    MatchOK NsRecRel (nsMt m q o l (nstrHashW q (hashN (tpool m) o.toNat l.toNat))) m
      (nstrKey (decI q) s) := by
  intro t i k hr
  obtain ⟨hpre, hsl, hw, hh⟩ := (NsRecRel_raw m t i k).mp hr
  have hle := hsl.le
  have hq1 := hq.le
  have htop := hpool.2.2.2.1
  have hpc := pcap_eq m (by have := hpool.2.2.1; omega)
  have hw' : sliceL (tpool m) (nsO m t i).toNat (nsL m t i).toNat = strWords k.s := by
    rw [sliceL_tpool m _ _ (by omega)]; exact hw
  have hk' : sliceL (tpool m) o.toNat l.toNat = strWords s := by
    rw [sliceL_tpool m _ _ (by omega)]; exact hk
  have key := slice_key (tpool m) (nsO m t i) (nsL m t i) o l (by omega) (by omega)
  have hdq := word_decI k.pre q hqw
  simp only [nsMt, nsmatchW]
  constructor
  · intro h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨h0, -⟩, h2⟩, h3⟩ := h
    have := key.mp (by simp only [Bool.and_eq_true, beq_iff_eq]; exact ⟨h2, h3⟩)
    rw [hw', hk'] at this
    obtain ⟨kp, ks⟩ := k
    simp only at hpre hdq this
    rw [strWords_inj _ _ this, ← hdq.mp (hpre.symm.trans h0)]
  · intro h
    subst h
    have e : sliceL (tpool m) (nsO m t i).toNat (nsL m t i).toNat =
        sliceL (tpool m) o.toNat l.toNat := by rw [hw', hk']
    have := key.mpr e
    have h0 : nsQ m t i = q := hpre.trans (hdq.mpr rfl)
    simp only [Bool.and_eq_true, beq_iff_eq] at this ⊢
    refine ⟨⟨⟨h0, ?_⟩, this.1⟩, this.2⟩
    rw [hh, h0, slice_key_hash _ _ _ _ _ _ e]

theorem nstrHomeOK (h : Word) : HomeOK nshash (nsMt m q o l h) m h := by
  intro t i hm
  simp only [nsMt, nsmatchW, Bool.and_eq_true, beq_iff_eq] at hm
  exact hm.1.1.2

variable (hq0 : m.flag = 0 → o.toNat < 2 ^ 40)

include hqw hq hk hq0 in
/-- The record `nstr_push` writes holds the name. -/
theorem nstrNewOK :
    NewOKR nstrSch NsRecRel nshash m
      [q, o, l, nstrHashW q (hashN (tpool m) o.toNat l.toNat)]
      (nstrKey (decI q) s) (nstrHashW q (hashN (tpool m) o.toNat l.toNat)) := by
  intro t ht hroom ht0
  have hp : (newRecM nstrSch m t [q, o, l, nstrHashW q (hashN (tpool m) o.toNat l.toNat)]).arr64
      POOL = m.arr64 POOL := wrRec_arr_ne _ _ _ POOL (ne_tierA (by decide) (by decide) (by decide) _) _ _ _
  have hp₁ : (newRecM nstrSch m t [q, o, l, nstrHashW q (hashN (tpool m) o.toNat l.toNat)]).arr64
      POOL1 = m.arr64 POOL1 := wrRec_arr_ne _ _ _ POOL1 (tierA_ne_pool _ (by decide) _).2.symm _ _ _
  have hpₜ : (newRecM nstrSch m t [q, o, l, nstrHashW q (hashN (tpool m) o.toNat l.toNat)]).arr64
      PT0 = m.arr64 PT0 := wrRec_arr_ne _ _ _ PT0 (ne_tierA (by decide) (by decide) (by decide) _) _ _ _
  have hpv := vpool_congr hp hp₁
  have hpq := tpool_congr hp hp₁
  have htop : rdW ((newRecM nstrSch m t
      [q, o, l, nstrHashW q (hashN (tpool m) o.toNat l.toNat)]).arr64 CTL) 0 =
      rdW (m.arr64 CTL) 0 := by rw [newRecM, wrRec_arr_ne _ _ _ CTL (ne_tierA (by decide) (by decide) (by decide) _)]
  have hrs : RSlice (newRecM nstrSch m t [q, o, l, nstrHashW q (hashN (tpool m) o.toNat l.toNat)]) t o l :=
    (RSlice_congr t o l (by simp only [top_rdW]; exact htop) (ptop0_congr hpₜ)).mpr (RSlice.intern hq hq0 ht0)
  have e : ∀ f, f < 4 → fld nstrSch (newRecM nstrSch m t
      [q, o, l, nstrHashW q (hashN (tpool m) o.toNat l.toNat)]) t
      (cntW nstrSch m t) f =
      [q, o, l, nstrHashW q (hashN (tpool m) o.toNat l.toNat)].getD f.toNat 0 := by
    intro f hf
    have := hroom.1
    have := hroom.2
    rw [fld_newRecM nstrSch nstrSch_wf] <;> simp only [nstrSch, Schema.ad] at * <;> grind
  have e0 := e 0 (by decide)
  have e1 := e 1 (by decide)
  have e2 := e 2 (by decide)
  have e3 := e 3 (by decide)
  rw [fld_nstr0] at e0
  rw [fld_nstr] at e1 e2 e3
  have hdq := word_decI (decI q : NIdx) q hqw
  simp only [nstrKey, NsRecRel_raw, nshash, nsQ, nsO, nsL, e0, e1, e2, e3, hpv, hpq, ← top_rdW] at htop hrs ⊢
  simp only [List.getD_cons_zero, List.getD_cons_succ, show (1 : Word).toNat = 0 + 1 from rfl,
    show (2 : Word).toNat = 1 + 1 from rfl, show (3 : Word).toNat = 2 + 1 from rfl,
    show (0 : Word).toNat = 0 from rfl]
  exact ⟨⟨(hdq.mpr rfl).symm, hrs, hk, trivial⟩, trivial⟩

end query

/-! ## The bridges from the L models -/

theorem nspushOK_room (m : Mem) (t : Word) (h : nspushOK m t = true) : PushRoom nstrSch m t := by
  simp only [nspushOK, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [PushRoom, cntW, nscnt, nstrSch, len64_eq] at *
  grind

/-- **The `nstr` table's shape.** -/
theorem nstrCS_wf : nstrCS.WF where
  sch := nstrSch_wf
  P := by decide
  S := by decide
  col A h := by simp [nstrCS] at h
  colRoom A h := by simp [nstrCS] at h
  colLt A h := by
    simp only [nstrCS, reduceCtorEq] at h; (try subst h); (try decide)
  room m t h := (nspushOK_room m t ((nspushOK_eqC m t).trans h)).2
  vs ks h hk := by simp [pushArgs, nstrCS, hk]
  ex h := by simp [nstrCS] at h

/-! ## `intern_nstr` refines `internNNode (.str _ _)` -/

section intern
variable (m : Mem) (a : AState) (hpool : PoolOK m) (hR : NStrR m a) (q o l : Word)
  (hqw : q.toNat < 2 ^ 32) (hq : SliceOK m o l) (s : String)
  (hk : sliceL (vpool m) o.toNat l.toNat = strWords s)

variable (hq0 : m.flag = 0 → o.toNat < 2 ^ 40)

include hpool hR hqw hq hk hq0 in
/-- **`intern_nstr`'s model refines the arena's `internNNode`** at the name `str q s`. -/
theorem nsintern_correct (w : Word) (m' : Mem) (hI : nsinternW m q o l = some (w, m')) :
    AM.ok (internNNode (.str (decI q) s)) a ∧ NStrR m' (AM.st (internNNode (.str (decI q) s)) a) ∧
    AM.res (internNNode (.str (decI q) s)) a = decI w :=
  consIntern_correct nstrCS_wf nstrFrame (colFree_none _ rfl) nstrLens a hR _ _ _ _ _
    (internNNode_str_run _ s a) false rfl [q, o, l]
    (by simp [show skipC nstrCS m [q, o, l] = 0 from rfl]) (by simp)
    ⟨rfl, nstrMatchOK m hpool q o l hqw hq s hk, nstrHomeOK m q o l _, nstrNewOK m q o l hqw hq s hk hq0⟩
    w m' hI

end intern

/-! ## Appending to the pool preserves the relation -/

section grow
variable (m m' : Mem) (hg : Grows m m')

include hg in
theorem NsRecRel_grow (hpool : PoolOK m) (t i : Word) (k : StrNode) (h : NsRecRel m t i k) :
    NsRecRel m' t i k := by
  have hr := grow_arr m m' hg (tierA NSREC t) (tierA_ne_pool _ (by decide) t)
    (ne_tierA (by decide) (by decide) (by decide) t).symm
  have h41 := hpool.top41
  have hta := hg.tagree (by omega)
  have hag := hg.agree
  simp only [NsRecRel_raw, nsQ, nsO, nsL, hr] at h ⊢
  obtain ⟨h0, hsl, hw, hh⟩ := h
  have hle := hsl.le
  exact ⟨h0, hsl.grows hg, by rw [Agree.sliceL _ _ _ _ _ hag hle, hw],
    by rw [Agree.hashN _ _ _ _ _ hta hle, hh]⟩

include hg in
/-- **Appending to the pool preserves the relation.** -/
theorem NStrR.grow (hpool : PoolOK m) (a : AState) (hR : NStrR m a) : NStrR m' a := by
  have hr : ∀ t, m'.arr64 (tierA NSREC t) = m.arr64 (tierA NSREC t) := fun t =>
    grow_arr m m' hg _ (tierA_ne_pool _ (by decide) t) (ne_tierA (by decide) (by decide) (by decide) t).symm
  refine ConsR.mono hR hr (fun t => grow_arr m m' hg _ (tierA_ne_pool _ (by decide) t) (ne_tierA (by decide) (by decide) (by decide) t).symm) ?_ ?_
    (fun t i k => NsRecRel_grow m m' hg hpool t i k) (fun t i => by simp only [nstrCS, nshash, hr])
  · rw [hg.frame.ctl, Mem.size_arr64_set64]
  · intro x hx
    exact grow_ctl m m' hg x (by rcases hx with rfl | rfl | rfl | rfl <;> decide)

end grow

end L.Arena
