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

`NStrR m a` is the library's `StoreR`; `internNStr_refines`: `intern_nstr(q, o, l)` refines
`internNNode (.str (decI q) s)` for the string `s` whose bytes the slice holds, under `NStrR` and
`PoolOK`. `NStrR.grow`: the pool growing keeps the relation.

Not represented: the derived column (`NStore.derOfView`, through `mixHash` and `hash s`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

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
      ↓reduceIte, nstrKey, ite_self, protoRun, nstrLens] <;>
    (try split) <;> simp_all [StateT.run_set, StateT.run_pure, withScrNStrs, withPersNStrs, fail,
      throwThe, MonadExceptOf.throw, StateT.run, Functor.map, StateT.map, set, StateT.set,
      StateT.lift, bind, Except.bind, Except.map, pure, Except.pure, StateT.bind, StateT.pure]

/-! ## The relation between L memory and the arena's name `str` tables -/

/-- The name `str` schema: `NSREC`, `NSSLOT`, four words per node, the counts at `CTL[36 + t]`. -/
def nstrSch : Schema := ⟨NSREC, NSSLOT, 4, 8, 36, NTag.str⟩

theorem nstrSch_wf : nstrSch.WF :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem fld_nstr0 (m : Mem) (t i : Word) :
    fld nstrSch m t i 0 = rdW (m.arr64 NSREC) (i * 8 + t * 4) := by
  simp [fld, Schema.ad, nstrSch]
theorem fld_nstr (m : Mem) (t i f : Word) :
    fld nstrSch m t i f = rdW (m.arr64 NSREC) (i * 8 + t * 4 + f) := rfl

/-- The prefix, offset and length words of node `i` of tier `t`. -/
abbrev nsQ (m : Mem) (t i : Word) : Word := rdW (m.arr64 NSREC) (i * 8 + t * 4)
abbrev nsO (m : Mem) (t i : Word) : Word := rdW (m.arr64 NSREC) (i * 8 + t * 4 + 1)
abbrev nsL (m : Mem) (t i : Word) : Word := rdW (m.arr64 NSREC) (i * 8 + t * 4 + 2)

/-- Node `i` of tier `t` holds `str k.pre k.s`: the prefix's handle word, a slice below the pool
top holding the string's bytes, and the hash. -/
def NsRecRel (m : Mem) (t i : Word) (k : StrNode) : Prop :=
  nsQ m t i = k.pre.word.toUInt64 ∧
  (nsO m t i).toNat + (nsL m t i).toNat ≤ m.top.toNat ∧
  sliceL (m.arr64 POOL) (nsO m t i).toNat (nsL m t i).toNat = strWords k.s ∧
  rdW (m.arr64 NSREC) (i * 8 + t * 4 + 3) =
    nstrHashW (nsQ m t i) (hashN (m.arr64 POOL) (nsO m t i).toNat (nsL m t i).toNat)

/-- The hash of node `i` of tier `t`: its word 3. -/
def nshash (m : Mem) (t i : Word) : Word := rdW (m.arr64 NSREC) (i * 8 + t * 4 + 3)

/-- **The state relation** of the name `str` table: the library's relation for its two tables. -/
def NStrR (m : Mem) (a : AState) : Prop :=
  StoreR nstrSch NsRecRel nshash m a.store.lss.ls.ns.scratchOn a.store.lss.ls.ns.pers.strs
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
  have hp : m'.arr64 POOL = m.arr64 POOL := hb POOL (by decide) (by decide) (by decide)
  have ht : m'.top = m.top := htop
  refine ⟨fun a h => ?_, by simp only [nshash, h3]⟩
  simpa only [NsRecRel, nsQ, nsO, nsL, h0, h1, h2, h3, hp, ht] using h

/-! ## The query's obligations -/

/-- The match of `nstr_match` on node `i` of tier `t`. -/
def nsMt (m : Mem) (q o l h t i : Word) : Bool :=
  nsmatchW (m.arr64 NSREC) (m.arr64 POOL) t i q o l h

section query
variable (m : Mem) (hpool : PoolOK m) (q o l : Word) (hqw : q.toNat < 2 ^ 32)
  (hq : SliceOK m o l) (s : String) (hk : sliceL (m.arr64 POOL) o.toNat l.toNat = strWords s)

include hpool hqw hq hk in
/-- **Matching is equality of names**, on a node of a represented tier. -/
theorem nstrMatchOK :
    MatchOK NsRecRel (nsMt m q o l (nstrHashW q (hashN (m.arr64 POOL) o.toNat l.toNat))) m
      (nstrKey (decI q) s) := by
  intro t i k ⟨hpre, hsl, hw, hh⟩
  obtain ⟨-, -, hps, htop⟩ := hpool
  simp only [SliceOK] at hq
  have key := slice_key (m.arr64 POOL) (nsO m t i) (nsL m t i) o l (by omega) (by omega)
  have hdq := word_decI k.pre q hqw
  simp only [nsMt, nsmatchW]
  constructor
  · intro h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨h0, -⟩, h2⟩, h3⟩ := h
    have := key.mp (by simp only [Bool.and_eq_true, beq_iff_eq]; exact ⟨h2, h3⟩)
    rw [hw, hk] at this
    obtain ⟨kp, ks⟩ := k
    simp only at hpre hdq this
    rw [strWords_inj _ _ this, ← hdq.mp (hpre.symm.trans h0)]
  · intro h
    subst h
    have e : sliceL (m.arr64 POOL) (nsO m t i).toNat (nsL m t i).toNat =
        sliceL (m.arr64 POOL) o.toNat l.toNat := by rw [hw, hk]
    have := key.mpr e
    have h0 : nsQ m t i = q := hpre.trans (hdq.mpr rfl)
    simp only [Bool.and_eq_true, beq_iff_eq] at this ⊢
    refine ⟨⟨⟨h0, ?_⟩, this.1⟩, this.2⟩
    rw [hh, h0, slice_key_hash _ _ _ _ _ _ e]

theorem nstrHomeOK (h : Word) : HomeOK nshash (nsMt m q o l h) m h := by
  intro t i hm
  simp only [nsMt, nsmatchW, Bool.and_eq_true, beq_iff_eq] at hm
  exact hm.1.1.2

include hqw hq hk in
/-- The record `nstr_push` writes holds the name. -/
theorem nstrNewOK :
    NewOK nstrSch NsRecRel nshash m
      [q, o, l, nstrHashW q (hashN (m.arr64 POOL) o.toNat l.toNat)]
      (nstrKey (decI q) s) (nstrHashW q (hashN (m.arr64 POOL) o.toNat l.toNat)) := by
  intro t j ht hroom
  have hp := pushG_arr nstrSch m t [q, o, l, nstrHashW q (hashN (m.arr64 POOL) o.toNat l.toNat)] j
    (cntW nstrSch m t) POOL (by decide) (by decide) (by decide)
  have htop := (outEq_pushG nstrSch nstrSch_wf m t ht
    [q, o, l, nstrHashW q (hashN (m.arr64 POOL) o.toNat l.toNat)] j (cntW nstrSch m t)).2
  have e : ∀ f, f < 4 → fld nstrSch (pushG nstrSch m t
      [q, o, l, nstrHashW q (hashN (m.arr64 POOL) o.toNat l.toNat)] j (cntW nstrSch m t)) t
      (cntW nstrSch m t) f =
      [q, o, l, nstrHashW q (hashN (m.arr64 POOL) o.toNat l.toNat)].getD f.toNat 0 := by
    intro f hf
    have := hroom.1
    have := hroom.2
    rw [fld_pushG nstrSch nstrSch_wf] <;> simp only [nstrSch, Schema.ad] at * <;> grind
  have e0 := e 0 (by decide)
  have e1 := e 1 (by decide)
  have e2 := e 2 (by decide)
  have e3 := e 3 (by decide)
  rw [fld_nstr0] at e0
  rw [fld_nstr] at e1 e2 e3
  have hdq := word_decI (decI q : NIdx) q hqw
  simp only [nstrKey, NsRecRel, nshash, nsQ, nsO, nsL, e0, e1, e2, e3, hp, ← top_rdW] at htop ⊢
  simp only [List.getD_cons_zero, List.getD_cons_succ, show (1 : Word).toNat = 0 + 1 from rfl,
    show (2 : Word).toNat = 1 + 1 from rfl, show (3 : Word).toNat = 2 + 1 from rfl,
    show (0 : Word).toNat = 0 from rfl, htop]
  exact ⟨⟨(hdq.mpr rfl).symm, hq, hk, trivial⟩, trivial⟩

end query

/-! ## The bridges from the L models -/

theorem nsprobeW_arm (m : Mem) (q o l h t : Word) :
    ∀ j d, nsprobeW (m.arr64 NSSLOT) (m.arr64 NSREC) (m.arr64 POOL) t q o l h (baseW m t) (nSlotsNs m) j d =
      probeArm nstrSch m t (nsMt m q o l h t)
        (nsprobeW (m.arr64 NSSLOT) (m.arr64 NSREC) (m.arr64 POOL) t q o l h (baseW m t) (nSlotsNs m)) j d := by
  intro j d; rw [nsprobeW]; rfl

theorem nspushOK_room (m : Mem) (t : Word) (h : nspushOK m t = true) : PushRoom nstrSch m t := by
  simp only [nspushOK, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [PushRoom, cntW, nscnt, nstrSch, len64_eq] at *
  grind

theorem nspushMem_eq (m : Mem) (t q o l h j c : Word) :
    nspushMem m t q o l h j c = pushG nstrSch m t [q, o, l, h] j c := by
  simp [nspushMem, pushG, wrRec, Schema.ad, nstrSch]

theorem nsinternW_eq (m : Mem) (q o l : Word) :
    nsinternW m q o l = internM nstrSch m 0 (nspushOK m)
      [q, o, l, nstrHashW q (hashN (m.arr64 POOL) o.toNat l.toNat)]
      (nsprobeW (m.arr64 NSSLOT) (m.arr64 NSREC) (m.arr64 POOL) 0 q o l
        (nstrHashW q (hashN (m.arr64 POOL) o.toNat l.toNat)) (baseW m 0) (nSlotsNs m)
        (homeW (nstrHashW q (hashN (m.arr64 POOL) o.toNat l.toNat)) (nSlotsNs m)) 0)
      (nsprobeW (m.arr64 NSSLOT) (m.arr64 NSREC) (m.arr64 POOL) 1 q o l
        (nstrHashW q (hashN (m.arr64 POOL) o.toNat l.toNat)) (baseW m 1) (nSlotsNs m)
        (homeW (nstrHashW q (hashN (m.arr64 POOL) o.toNat l.toNat)) (nSlotsNs m)) 0) := by
  have e0 : ∀ x, hdW nstrSch.tag.toUInt64 0 x = nsP + x := fun x => by
    simp [hdW, nstrSch, nsP, NTag.str]
  have e1 : ∀ x, hdW nstrSch.tag.toUInt64 1 x = nsS + x := fun x => by
    simp [hdW, nstrSch, nsS, NTag.str]
  simp only [nsinternW, internM, nspushMem_eq, e0, e1, true_and]
  rfl

/-! ## `intern_nstr` refines `internNNode (.str _ _)` -/

section intern
variable (m : Mem) (a : AState) (hpool : PoolOK m) (hR : NStrR m a) (q o l : Word)
  (hqw : q.toNat < 2 ^ 32) (hq : SliceOK m o l) (s : String)
  (hk : sliceL (m.arr64 POOL) o.toNat l.toNat = strWords s)

include hpool hR hqw hq hk in
/-- **`intern_nstr`'s model refines the arena's `internNNode`** at the name `str q s`. -/
theorem nsintern_correct (w : Word) (m' : Mem) (hI : nsinternW m q o l = some (w, m')) :
    AM.ok (internNNode (.str (decI q) s)) a ∧ NStrR m' (AM.st (internNNode (.str (decI q) s)) a) ∧
    AM.res (internNNode (.str (decI q) s)) a = decI w := by
  rw [nsinternW_eq] at hI
  exact intern_correctG nstrSch NsRecRel nshash nstrSch_wf nstrFrame nstrLens a m hR _ _ _ _ _
    (internNNode_str_run _ s a) false rfl 0 (by simp) (by simp) _ _
    (nstrMatchOK m hpool q o l hqw hq s hk) (nstrHomeOK m q o l _) _ _
    (probe_homeG nstrSch m 0 _ _ (nsprobeW_arm m q o l _ 0) _)
    (probe_homeG nstrSch m 1 _ _ (nsprobeW_arm m q o l _ 1) _) _ (nspushOK_room m) _ rfl
    (nstrNewOK m q o l hqw hq s hk) w m' hI

end intern

/-! ## Appending to the pool preserves the relation -/

section grow
variable (m m' : Mem) (hg : Grows m m')

include hg in
theorem NsRecRel_grow (t i : Word) (k : StrNode) (h : NsRecRel m t i k) : NsRecRel m' t i k := by
  have hr := grow_arr m m' hg NSREC (by decide) (by decide)
  obtain ⟨hfr, hag, ht1, ht2, hps'⟩ := hg
  simp only [NsRecRel, nsQ, nsO, nsL, hr] at h ⊢
  obtain ⟨h0, hsl, hw, hh⟩ := h
  exact ⟨h0, by omega, by rw [Agree.sliceL _ _ _ _ _ hag hsl, hw],
    by rw [Agree.hashN _ _ _ _ _ hag hsl, hh]⟩

include hg in
/-- **Appending to the pool preserves the relation.** -/
theorem NStrR.grow (a : AState) (hR : NStrR m a) : NStrR m' a := by
  obtain ⟨hctl, hfl, hT0, hT1⟩ := hR
  have hf := grow_ctl m m' hg 1 (by decide)
  have := Frame.size _ _ _ hg.1
  have := Frame.arr64 POOL CTL _ _ hg.1 (by decide)
  have hr := grow_arr m m' hg NSREC (by decide) (by decide)
  have hT : ∀ t, t ≤ 1 → ∀ tb : Tbl StrNode NIdx UInt64, TierR nstrSch NsRecRel nshash m t tb →
      TierR nstrSch NsRecRel nshash m' t tb := fun t ht tb hT =>
    tierR_mono nstrSch NsRecRel nshash m m' t tb hr
      (grow_arr m m' hg NSSLOT (by decide) (by decide))
      (grow_ctl m m' hg (36 + t) (by grind))
      (by simp only [baseW, grow_ctl m m' hg SCB (by decide)]) (fun i k => NsRecRel_grow m m' hg t i k)
      (fun i => by simp only [nshash, hr]) hT
  refine ⟨?_, by grind, hT 0 (by decide) _ hT0, hT 1 (by decide) _ hT1⟩
  exact ⟨by grind [store_grind], by rw [grow_ctl m m' hg SCB (by decide)]; exact hctl.2⟩

end grow

/-- `intern_nstr` refines `internNNode (.str _ _)` under `NStrR` (and the pool invariant). -/
theorem internNStr_refines (p : Prog) (hph : p.lookup "lit_hash" = some litHash)
    (hpe : p.lookup "limbs_eq" = some limbsEq) (hpm : p.lookup "nstr_match" = some nsMatch)
    (hpf : p.lookup "nstr_find" = some nsFind) (hpp : p.lookup "nstr_push" = some nsPush)
    (hp : p.lookup "intern_nstr" = some internNStr)
    (a₀ : AState) (n : Nat) (s₀ : St) (q o l : Word) (hpool : PoolOK s₀.mem) (hR : NStrR s₀.mem a₀)
    (hqw : q.toNat < 2 ^ 32) (hq : SliceOK s₀.mem o l) (s : String)
    (hk : sliceL (s₀.mem.arr64 POOL) o.toNat l.toNat = strWords s) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_nstr" [q, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internNNode (.str (decI q) s)) a₀ ∧
      NStrR s'.mem (AM.st (internNNode (.str (decI q) s)) a₀) ∧
      AM.res (internNNode (.str (decI q) s)) a₀ = decI (r.headD 0); ⊤⦄ := by
  have ⟨_, _, hps, htop⟩ := hpool
  have hspec := internNStr_spec p hph hpe hpm hpf hpp hp n s₀ q o l (by omega)
    (by simp only [SliceOK] at hq; omega)
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun hspec
  subst hs
  exact ⟨hloc, nsintern_correct s.mem a₀ hpool hR q o l hqw hq _ hk _ _ hI⟩

end L.Arena
