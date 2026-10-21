import ConAgua.Arena.PoolSlice
import ConAgua.Arena.LsStore

/-!
# The level-list store refines the arena's level-list tables

The first table with a variable-length key that is not a number: `ListNode { us : List LIdx }`
(`ConAgua/Arena/LsStore.lean` has the L code). The list lives in the pool, one handle word per
element (`lsWords`), and the record points at the slice. The schema `lsSch` (`LSREC`, `LSSLOT`,
three words per node, counts at `CTL[40 + t]`, tag `0`), the record relation `LsRecRel` (a slice
below the pool top holding the list's words, and its hash), the node hash `lshash` (word 2), the
lens `lsLens` on `a.store.lss`'s two tables. Matching is equality of lists by `slice_key`
(`PoolSlice.lean`) and the injectivity of `lsWords`; there is no scratch skip.

`LsR m a` is the library's `StoreR`; `internLs_refines`: `intern_ls(o, l)` refines
`internLsNode us` for the list `us` whose words the slice holds, under `LsR` and `PoolOK`.
`LsR.grow`: the pool growing keeps the relation (as `LitR.grow`).

Not represented: the derived column (`LsStore.derOfView`, through `mixHash`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

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
      ↓reduceIte, lsKey, ite_self, protoRun, lsLens] <;>
    (try split) <;> simp_all [StateT.run_set, StateT.run_pure, withScrLists, withPersLists, fail,
      throwThe, MonadExceptOf.throw, StateT.run, Functor.map, StateT.map, set, StateT.set,
      StateT.lift, bind, Except.bind, Except.map, pure, Except.pure, StateT.bind, StateT.pure]

/-! ## The relation between L memory and the arena's level-list tables -/

/-- The level-list schema: `LSREC`, `LSSLOT`, three words per node, the counts at `CTL[40 + t]`. -/
def lsSch : Schema := ⟨LSREC, LSSLOT, 3, 6, 40, LsTag.list⟩

theorem lsSch_wf : lsSch.WF :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem fld_ls0 (m : Mem) (t i : Word) : fld lsSch m t i 0 = rdW (m.arr64 LSREC) (i * 6 + t * 3) := by
  simp [fld, Schema.ad, lsSch]
theorem fld_ls (m : Mem) (t i f : Word) :
    fld lsSch m t i f = rdW (m.arr64 LSREC) (i * 6 + t * 3 + f) := rfl

/-- The offset and length words of node `i` of tier `t`. -/
abbrev lsO (m : Mem) (t i : Word) : Word := rdW (m.arr64 LSREC) (i * 6 + t * 3)
abbrev lsL (m : Mem) (t i : Word) : Word := rdW (m.arr64 LSREC) (i * 6 + t * 3 + 1)

/-- Node `i` of tier `t` holds the list `k.us`: a slice below the pool top holding its handle
words, and the slice's hash. -/
def LsRecRel (m : Mem) (t i : Word) (k : ListNode) : Prop :=
  (lsO m t i).toNat + (lsL m t i).toNat ≤ m.top.toNat ∧
  sliceL (m.arr64 POOL) (lsO m t i).toNat (lsL m t i).toNat = lsWords k.us ∧
  rdW (m.arr64 LSREC) (i * 6 + t * 3 + 2) = hashN (m.arr64 POOL) (lsO m t i).toNat (lsL m t i).toNat

/-- The hash of node `i` of tier `t`: its word 2. -/
def lshash (m : Mem) (t i : Word) : Word := rdW (m.arr64 LSREC) (i * 6 + t * 3 + 2)

/-- **The state relation** of the level-list store: the library's relation for its two tables. -/
def LsR (m : Mem) (a : AState) : Prop :=
  StoreR lsSch LsRecRel lshash m a.store.lss.scratchOn a.store.lss.pers.lists a.store.lss.scr.lists

/-- A node's relation and hash depend on its three words, the pool and the top. -/
theorem lsFrame : RFrame lsSch LsRecRel lshash := by
  intro m m' t i ⟨hb, htop⟩ hf
  have h0 := hf 0 (by decide)
  have h1 := hf 1 (by decide)
  have h2 := hf 2 (by decide)
  rw [fld_ls0, fld_ls0] at h0
  rw [fld_ls, fld_ls] at h1 h2
  have hp : m'.arr64 POOL = m.arr64 POOL := hb POOL (by decide) (by decide) (by decide)
  have ht : m'.top = m.top := htop
  refine ⟨fun a h => ?_, by simp only [lshash, h2]⟩
  simpa only [LsRecRel, lsO, lsL, h0, h1, h2, hp, ht] using h

/-! ## The query's obligations -/

/-- The match of `ls_match` on node `i` of tier `t`. -/
def lsMt (m : Mem) (o l h t i : Word) : Bool := lsmatchW (m.arr64 LSREC) (m.arr64 POOL) t i o l h

section query
variable (m : Mem) (hpool : PoolOK m) (o l : Word) (hq : SliceOK m o l) (us : List LIdx)
  (hk : sliceL (m.arr64 POOL) o.toNat l.toNat = lsWords us)

include hpool hq hk in
/-- **Matching is equality of level lists**, on a node of a represented tier. -/
theorem lsMatchOK :
    MatchOK LsRecRel (lsMt m o l (hashN (m.arr64 POOL) o.toNat l.toNat)) m (lsKey us) := by
  intro t i k ⟨hsl, hw, hh⟩
  obtain ⟨-, -, hps, htop⟩ := hpool
  simp only [SliceOK] at hq
  have key := slice_key (m.arr64 POOL) (lsO m t i) (lsL m t i) o l (by omega) (by omega)
  simp only [lsMt, lsmatchW, Bool.and_assoc]
  constructor
  · intro h
    simp only [Bool.and_eq_true] at h
    have := key.mp (by simpa only [Bool.and_eq_true] using h.2)
    rw [hw, hk] at this
    obtain ⟨k⟩ := k
    exact congrArg ListNode.mk (lsWords_inj _ _ this)
  · intro h
    subst h
    have e : sliceL (m.arr64 POOL) (lsO m t i).toNat (lsL m t i).toNat =
        sliceL (m.arr64 POOL) o.toNat l.toNat := by rw [hw, hk]
    have := key.mpr e
    simp only [Bool.and_eq_true] at this
    simp only [Bool.and_eq_true, this, and_true, beq_iff_eq, hh]
    exact slice_key_hash _ _ _ _ _ _ e

theorem lsHomeOK (h : Word) : HomeOK lshash (lsMt m o l h) m h := by
  intro t i hm
  simp only [lsMt, lsmatchW, Bool.and_eq_true, beq_iff_eq] at hm
  exact hm.1.1

include hq hk in
/-- The record `ls_push` writes holds the list. -/
theorem lsNewOK :
    NewOK lsSch LsRecRel lshash m [o, l, hashN (m.arr64 POOL) o.toNat l.toNat]
      (lsKey us) (hashN (m.arr64 POOL) o.toNat l.toNat) := by
  intro t j ht hroom
  have hp := pushG_arr lsSch m t [o, l, hashN (m.arr64 POOL) o.toNat l.toNat] j (cntW lsSch m t)
    POOL (by decide) (by decide) (by decide)
  have htop := (outEq_pushG lsSch lsSch_wf m t ht [o, l, hashN (m.arr64 POOL) o.toNat l.toNat] j
    (cntW lsSch m t)).2
  have e : ∀ f, f < 3 → fld lsSch (pushG lsSch m t [o, l, hashN (m.arr64 POOL) o.toNat l.toNat] j
      (cntW lsSch m t)) t (cntW lsSch m t) f =
      [o, l, hashN (m.arr64 POOL) o.toNat l.toNat].getD f.toNat 0 := by
    intro f hf
    have := hroom.1
    have := hroom.2
    rw [fld_pushG lsSch lsSch_wf] <;> simp only [lsSch, Schema.ad] at * <;> grind
  have e0 := e 0 (by decide)
  have e1 := e 1 (by decide)
  have e2 := e 2 (by decide)
  rw [fld_ls0] at e0
  rw [fld_ls] at e1 e2
  simp only [lsKey, LsRecRel, lshash, lsO, lsL, e0, e1, e2, hp, ← top_rdW] at htop ⊢
  simp only [List.getD_cons_zero, List.getD_cons_succ, show (1 : Word).toNat = 0 + 1 from rfl,
    show (2 : Word).toNat = 1 + 1 from rfl, show (0 : Word).toNat = 0 from rfl, htop]
  exact ⟨⟨hq, hk, trivial⟩, trivial⟩

end query

/-! ## The bridges from the L models -/

theorem lsprobeW_arm (m : Mem) (o l h t : Word) :
    ∀ j d, lsprobeW (m.arr64 LSSLOT) (m.arr64 LSREC) (m.arr64 POOL) t o l h (baseW m t) (nSlotsLs m) j d =
      probeArm lsSch m t (lsMt m o l h t)
        (lsprobeW (m.arr64 LSSLOT) (m.arr64 LSREC) (m.arr64 POOL) t o l h (baseW m t) (nSlotsLs m)) j d := by
  intro j d; rw [lsprobeW]; rfl

theorem lspushOK_room (m : Mem) (t : Word) (h : lspushOK m t = true) : PushRoom lsSch m t := by
  simp only [lspushOK, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [PushRoom, cntW, lscnt, lsSch, len64_eq] at *
  grind

theorem lspushMem_eq (m : Mem) (t o l h j c : Word) :
    lspushMem m t o l h j c = pushG lsSch m t [o, l, h] j c := by
  simp [lspushMem, pushG, wrRec, Schema.ad, lsSch]

theorem lsinternW_eq (m : Mem) (o l : Word) :
    lsinternW m o l = internM lsSch m 0 (lspushOK m)
      [o, l, hashN (m.arr64 POOL) o.toNat l.toNat]
      (lsprobeW (m.arr64 LSSLOT) (m.arr64 LSREC) (m.arr64 POOL) 0 o l
        (hashN (m.arr64 POOL) o.toNat l.toNat) (baseW m 0) (nSlotsLs m)
        (homeW (hashN (m.arr64 POOL) o.toNat l.toNat) (nSlotsLs m)) 0)
      (lsprobeW (m.arr64 LSSLOT) (m.arr64 LSREC) (m.arr64 POOL) 1 o l
        (hashN (m.arr64 POOL) o.toNat l.toNat) (baseW m 1) (nSlotsLs m)
        (homeW (hashN (m.arr64 POOL) o.toNat l.toNat) (nSlotsLs m)) 0) := by
  have e0 : ∀ x, hdW lsSch.tag.toUInt64 0 x = lsP + x := fun x => by
    simp [hdW, lsSch, lsP, LsTag.list]
  have e1 : ∀ x, hdW lsSch.tag.toUInt64 1 x = lsS + x := fun x => by
    simp [hdW, lsSch, lsS, LsTag.list]
  simp only [lsinternW, internM, lspushMem_eq, e0, e1, true_and]
  rfl

/-! ## `intern_ls` refines `internLsNode` -/

section intern
variable (m : Mem) (a : AState) (hpool : PoolOK m) (hR : LsR m a) (o l : Word)
  (hq : SliceOK m o l) (us : List LIdx) (hk : sliceL (m.arr64 POOL) o.toNat l.toNat = lsWords us)

include hpool hR hq hk in
/-- **`intern_ls`'s model refines the arena's `internLsNode`** at the list the slice holds. -/
theorem lsintern_correct (w : Word) (m' : Mem) (hI : lsinternW m o l = some (w, m')) :
    AM.ok (internLsNode us) a ∧ LsR m' (AM.st (internLsNode us) a) ∧
    AM.res (internLsNode us) a = decI w := by
  rw [lsinternW_eq] at hI
  exact intern_correctG lsSch LsRecRel lshash lsSch_wf lsFrame lsLens a m hR _ _ _ _ _
    (internLsNode_run us a) false rfl 0 (by simp) (by simp) _ _
    (lsMatchOK m hpool o l hq us hk) (lsHomeOK m o l _) _ _
    (probe_homeG lsSch m 0 _ _ (lsprobeW_arm m o l _ 0) _)
    (probe_homeG lsSch m 1 _ _ (lsprobeW_arm m o l _ 1) _) _ (lspushOK_room m) _ rfl
    (lsNewOK m o l hq us hk) w m' hI

end intern

/-! ## Appending to the pool preserves the relation -/

section grow
variable (m m' : Mem) (hg : Grows m m')

include hg in
theorem LsRecRel_grow (t i : Word) (k : ListNode) (h : LsRecRel m t i k) : LsRecRel m' t i k := by
  have hr := grow_arr m m' hg LSREC (by decide) (by decide)
  obtain ⟨hfr, hag, ht1, ht2, hps'⟩ := hg
  simp only [LsRecRel, lsO, lsL, hr] at h ⊢
  obtain ⟨hsl, hw, hh⟩ := h
  exact ⟨by omega, by rw [Agree.sliceL _ _ _ _ _ hag hsl, hw],
    by rw [Agree.hashN _ _ _ _ _ hag hsl, hh]⟩

include hg in
/-- **Appending to the pool preserves the relation.** -/
theorem LsR.grow (a : AState) (hR : LsR m a) : LsR m' a := by
  obtain ⟨hctl, hfl, hT0, hT1⟩ := hR
  have hf := grow_ctl m m' hg 1 (by decide)
  have := Frame.size _ _ _ hg.1
  have := Frame.arr64 POOL CTL _ _ hg.1 (by decide)
  have hr := grow_arr m m' hg LSREC (by decide) (by decide)
  have hT : ∀ t, t ≤ 1 → ∀ tb : Tbl ListNode LsIdx LDer, TierR lsSch LsRecRel lshash m t tb →
      TierR lsSch LsRecRel lshash m' t tb := fun t ht tb hT =>
    tierR_mono lsSch LsRecRel lshash m m' t tb hr (grow_arr m m' hg LSSLOT (by decide) (by decide))
      (grow_ctl m m' hg (40 + t) (by grind)) (fun i k => LsRecRel_grow m m' hg t i k)
      (fun i => by simp only [lshash, hr]) hT
  refine ⟨?_, by grind, hT 0 (by decide) _ hT0, hT 1 (by decide) _ hT1⟩
  grind [store_grind]

end grow

/-- `intern_ls` refines `internLsNode` under `LsR` (and the pool invariant). -/
theorem internLs_refines (p : Prog) (hph : p.lookup "lit_hash" = some litHash)
    (hpe : p.lookup "limbs_eq" = some limbsEq) (hpm : p.lookup "ls_match" = some lsMatch)
    (hpf : p.lookup "ls_find" = some lsFind) (hpp : p.lookup "ls_push" = some lsPush)
    (hp : p.lookup "intern_ls" = some internLs)
    (a₀ : AState) (n : Nat) (s₀ : St) (o l : Word) (hpool : PoolOK s₀.mem) (hR : LsR s₀.mem a₀)
    (hq : SliceOK s₀.mem o l) (us : List LIdx)
    (hk : sliceL (s₀.mem.arr64 POOL) o.toNat l.toNat = lsWords us) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_ls" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internLsNode us) a₀ ∧
      LsR s'.mem (AM.st (internLsNode us) a₀) ∧
      AM.res (internLsNode us) a₀ = decI (r.headD 0); ⊤⦄ := by
  have ⟨_, _, hps, htop⟩ := hpool
  have hspec := internLs_spec p hph hpe hpm hpf hpp hp n s₀ o l (by omega)
    (by simp only [SliceOK] at hq; omega)
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun hspec
  subst hs
  exact ⟨hloc, lsintern_correct s.mem a₀ hpool hR o l hq us hk _ _ hI⟩

end L.Arena
