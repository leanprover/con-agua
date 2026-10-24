import ConAgua.Arena.StoreLib
import ConAgua.Arena.SimLib
import ConAgua.Arena.MaxStore
import ConAgua.Arena.LpColRel

/-!
# The level `max` store refines the arena's `max` tables

The fifth table on the store library, the `app` shape (two handle fields, no scratch skip) for
the record `BinLNode { u v : LIdx }` of the level store's `max` constructor
(`ConAgua/Arena/MaxStore.lean` has the L code). The schema `maxSch` (`MREC`, `MSLOT`, two words
per node, counts at `CTL[10 + t]`, tag `2`), the record relation `MRecRel` (the two words are the
children's handle words), the node hash `mhash`, the lens `maxLens` on the level store's two
`max` tables (`a.store.lss.ls.pers.maxs`/`scr.maxs`). `MaxR m a` is the library's `StoreR` for
them. `internMax_refines`: `intern_max(u, v)` refines `internLNode (.max u v)` under `MaxR`. The
level store has no scratch skip (`LStore.find?` probes the persistent tier unconditionally), so
`skB = false`, as for `succ`/`zero`.

Not represented: the derived column and every other table.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

/-- The arena's `max` cons key. -/
abbrev maxKey (u v : LIdx) : BinLNode := ⟨u, v⟩

/-- `a` with the scratch / persistent `max` table of the level store replaced. -/
def withScrMaxs (a : AState) (t : Tbl BinLNode LIdx LDer) : AState :=
  { a with store := { a.store with lss := { a.store.lss with ls := { a.store.lss.ls with
      scr := { a.store.lss.ls.scr with maxs := t } } } } }
def withPersMaxs (a : AState) (t : Tbl BinLNode LIdx LDer) : AState :=
  { a with store := { a.store with lss := { a.store.lss with ls := { a.store.lss.ls with
      pers := { a.store.lss.ls.pers with maxs := t } } } } }

/-- The level store's two `max` tables. -/
def maxLens : Lens BinLNode LDer .level where
  on a := a.store.lss.ls.scratchOn
  getP a := a.store.lss.ls.pers.maxs
  getS a := a.store.lss.ls.scr.maxs
  setP := withPersMaxs
  setS := withScrMaxs
  on_setP _ _ := rfl
  on_setS _ _ := rfl
  getP_setP _ _ := rfl
  getS_setP _ _ := rfl
  getP_setS _ _ := rfl
  getS_setS _ _ := rfl

/-- `internLNode` at a `max` node is the library's protocol, with no skip. -/
theorem internLNode_max_run (u v : LIdx) (a : AState) :
    (internLNode (.max u v)).run a =
      protoRun maxLens (maxKey u v) LTag.max a.store.lss.ls.pers.maxs.cons[maxKey u v]?
        (a.store.lss.ls.derOfView (.max u v)) (.native "arena: level constructor array full") a := by
  simp only [internLNode, LStore.find?, LTables.find?, Tbl.find?, LTables.sizeOf, EStore.ls,
    EStore.internLevel, LsStore.internLevel, LStore.intern, LTables.push]
  cases hp : a.store.lss.ls.pers.maxs.cons[maxKey u v]? <;> cases hs : a.store.lss.ls.scratchOn <;>
    cases hc : a.store.lss.ls.scr.maxs.cons[maxKey u v]? <;>
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hp, hs, hc, Bool.false_eq_true,
      ↓reduceIte, maxKey, ite_self, protoRun, maxLens] <;>
    (try split) <;> simp_all [StateT.run_set, StateT.run_pure, withScrMaxs, withPersMaxs, fail,
      throwThe, MonadExceptOf.throw, StateT.run, Functor.map, StateT.map, set, StateT.set,
      StateT.lift, bind, Except.bind, Except.map, pure, Except.pure, StateT.bind, StateT.pure]

/-! ## The relation between L memory and the arena's `max` tables -/

/-- The `max` schema: `MREC`, `MSLOT`, two words per node, the counts at `CTL[10 + t]`. -/
def maxSch : Schema := ⟨MREC, MSLOT, 2, 4, 10, LTag.max⟩

theorem maxSch_wf : maxSch.WF :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem fld_max0 (m : Mem) (t i : Word) : fld maxSch m t i 0 = rdW (m.arr64 MREC) (i * 4 + t * 2) := by
  simp [fld, Schema.ad, maxSch]
theorem fld_max (m : Mem) (t i f : Word) :
    fld maxSch m t i f = rdW (m.arr64 MREC) (i * 4 + t * 2 + f) := rfl

/-- Node `i` of tier `t` holds the `max` node `k`: its two handle words. -/
def MRecRel (m : Mem) (t i : Word) (k : BinLNode) : Prop :=
  rdW (m.arr64 MREC) (i * 4 + t * 2) = k.u.word.toUInt64 ∧
  rdW (m.arr64 MREC) (i * 4 + t * 2 + 1) = k.v.word.toUInt64

/-- **The state relation** of the `max` store: the library's relation for the two `max` tables. -/
def MaxR (m : Mem) (a : AState) : Prop :=
  StoreR maxSch MRecRel mhash m a.store.lss.ls.scratchOn a.store.lss.ls.pers.maxs
    a.store.lss.ls.scr.maxs

/-- A node's relation and hash depend only on its two words. -/
theorem maxFrame : RFrame maxSch MRecRel mhash := by
  intro m m' t i _ hf
  have h0 := hf 0 (by decide)
  have h1 := hf 1 (by decide)
  rw [fld_max0, fld_max0] at h0
  rw [fld_max, fld_max] at h1
  exact ⟨fun a h => by simpa only [MRecRel, h0, h1] using h, by simp only [mhash, h0, h1]⟩

/-! ## The query's obligations -/

/-- The match of `max_find` on node `i` of tier `t`. -/
def mMt (m : Mem) (u v t i : Word) : Bool := mmatchW (m.arr64 MREC) t i u v

section query
variable (m : Mem) (u v : Word) (hu : u.toNat < 2 ^ 32) (hv : v.toNat < 2 ^ 32)

include hu hv in
/-- **Matching is equality of `max` nodes.** -/
theorem maxMatchOK : MatchOK MRecRel (mMt m u v) m (maxKey (decI u) (decI v)) := by
  intro t i k hr
  have := word_decI k.u u hu
  have := word_decI k.v v hv
  obtain ⟨ku, kv⟩ := k
  grind [mMt, mmatchW, MRecRel, decE_eq]

theorem maxHomeOK : HomeOK mhash (mMt m u v) m (maxHashW u v) := by
  intro t i hm
  simp only [mMt, mmatchW, Bool.and_eq_true, beq_iff_eq] at hm
  simp only [mhash, hm.1, hm.2]

include hu hv in
/-- The record `max_push` writes holds the node. -/
theorem maxNewOK : NewOK maxSch MRecRel mhash m [u, v] (maxKey (decI u) (decI v)) (maxHashW u v) := by
  intro t j ht hroom
  have e : ∀ g, g < 2 → fld maxSch (pushG maxSch m t [u, v] j (cntW maxSch m t)) t
      (cntW maxSch m t) g = [u, v].getD g.toNat 0 := by
    intro g hg
    have := hroom.1
    have := hroom.2
    rw [fld_pushG maxSch maxSch_wf] <;> simp only [maxSch, Schema.ad] at * <;> grind
  have e0 := e 0 (by decide)
  have e1 := e 1 (by decide)
  rw [fld_max0] at e0
  rw [fld_max] at e1
  simp only [List.getD_cons_zero, List.getD_cons_succ, show (1 : Word).toNat = 0 + 1 from rfl,
    show (0 : Word).toNat = 0 from rfl] at e0 e1
  have := word_decI (decI u : LIdx) u hu
  have := word_decI (decI v : LIdx) v hv
  simp only [MRecRel, mhash, maxKey, e0, e1]
  grind [decE_eq]

end query

/-! ## The bridges from the L models -/

theorem mprobeW_arm (m : Mem) (u v t : Word) :
    ∀ j d, mprobeW (m.arr64 MSLOT) (m.arr64 MREC) t u v (baseW m t) (nSlotsM m) j d =
      probeArm maxSch m t (mMt m u v t) (mprobeW (m.arr64 MSLOT) (m.arr64 MREC) t u v (baseW m t) (nSlotsM m)) j d := by
  intro j d; rw [mprobeW, cprobeW]; rfl

theorem mpushOK_room (m : Mem) (t : Word) (h : mpushOK m t = true) : PushRoom maxSch m t := by
  simp only [mpushOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have := UInt64.toNat_shiftRight (m.len64 MREC) 2
  simp only [PushRoom, cntW, mcnt, maxSch, len64_eq] at *
  grind

theorem mpushMem_eq (m : Mem) (t u v j c : Word) :
    mpushMem m t u v j c = (pushG maxSch m t [u, v] j c).set64 MHP (c * 2 + t) (lvlHPW m u ||| lvlHPW m v) := by
  simp [mpushMem, pushG, wrRec, Schema.ad, maxSch]

theorem minternW_eq (m : Mem) (u v : Word) :
    minternW m u v = internMD maxSch MHP (lvlHPW m u ||| lvlHPW m v) m 0 (mpushOK m) [u, v]
      (mprobeW (m.arr64 MSLOT) (m.arr64 MREC) 0 u v (baseW m 0) (nSlotsM m) (homeW (maxHashW u v) (nSlotsM m)) 0)
      (mprobeW (m.arr64 MSLOT) (m.arr64 MREC) 1 u v (baseW m 1) (nSlotsM m) (homeW (maxHashW u v) (nSlotsM m)) 0)
      mhash := by
  have e0 : ∀ x, hdW maxSch.tag.toUInt64 0 x = maxP + x := fun x => by
    simp [hdW, maxSch, maxP, LTag.max]
  have e1 : ∀ x, hdW maxSch.tag.toUInt64 1 x = maxS + x := fun x => by
    simp [hdW, maxSch, maxS, LTag.max]
  have ep : ∀ t, pushOKC maxCS m t = mpushOK m t := fun t => (mpushOK_eqC m t).symm
  have em : ∀ t j c, pushMX maxCS m t (maxCS.vsM (pushArgs maxCS [u, v] (maxHashW u v)))
      (maxCS.colM m (pushArgs maxCS [u, v] (maxHashW u v))) j c =
      (pushG maxSch m t [u, v] j c).set64 MHP (c * 2 + t) (lvlHPW m u ||| lvlHPW m v) := by
    intro t j c; rw [← mpushMem_eq, mpushMem_eqC]; rfl
  have ec : ∀ t, cntC maxCS m t = cntW maxSch m t := fun t => rfl
  have eh : maxCS.qhM m [u, v] = maxHashW u v := rfl
  have es : skipC maxCS m [u, v] = 0 := rfl
  simp only [minternW, consInternM, internMD, pushC, ep, em, ec, e0, e1, eh, es, true_and]
  rfl

/-- **What `intern_max` changes**: the table's arrays, the column, the counts. -/
theorem minternW_frame (m : Mem) (u v : Word) (w : Word) (m' : Mem) (hI : minternW m u v = some (w, m')) :
    MemFrame [MREC, MSLOT, MHP] [10, 11] m m' := by
  rw [minternW_eq] at hI
  exact internMD_frame maxSch maxSch_wf MHP (by decide) _ _ _ _ _ _ _ _ _ hI

/-- `intern_max`'s model as the library's interning and the `mk_*` tail (`mkK`), given the count
words. -/
theorem minternW_eqK (m : Mem) (u v : Word) (hctl : maxSch.ca.toNat + 2 ≤ (m.arr64 CTL).size) :
    minternW m u v = mkK MHP maxSch.ca (cnt2 m maxSch.ca) (lvlHPW m u ||| lvlHPW m v)
      (internM maxSch m 0 (mpushOK m) [u, v]
      (mprobeW (m.arr64 MSLOT) (m.arr64 MREC) 0 u v (baseW m 0) (nSlotsM m) (homeW (maxHashW u v) (nSlotsM m)) 0)
      (mprobeW (m.arr64 MSLOT) (m.arr64 MREC) 1 u v (baseW m 1) (nSlotsM m) (homeW (maxHashW u v) (nSlotsM m)) 0) mhash) := by
  rw [minternW_eq]
  refine internMD_mkK maxSch maxSch_wf _ _ _ _ _ _ _ _ mhash (by decide) (by decide)
    (fun m k x t i => by simp only [mhash, Mem.arr64_set64_ne _ _ _ _ _ (show MREC ≠ MHP by decide)])
    hctl (fun t ht hp => ?_)
  simp only [mpushOK, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨h1, -⟩, h2⟩ := hp
  exact ⟨h1, col_room _ _ _ ht h1 h2⟩

theorem maxLocal : RLocal maxSch MRecRel mhash [] [] := by
  intro m m' hra _ _; simp only [maxSch] at hra
  exact ⟨fun t i k h => by simpa only [MRecRel, hra] using h, fun t i => by simp only [mhash, hra]⟩

/-! ## `intern_max` refines `internLNode (.max _ _)` -/

section intern
variable (m : Mem) (a : AState) (hR : MaxR m a) (u v : Word) (hu : u.toNat < 2 ^ 32)
  (hv : v.toNat < 2 ^ 32)

include hR hu hv in
/-- The library's half of `intern_max` (before the column). -/
theorem mintern_core (w : Word) (m₁ : Mem)
    (hI : internM maxSch m 0 (mpushOK m) [u, v]
      (mprobeW (m.arr64 MSLOT) (m.arr64 MREC) 0 u v (baseW m 0) (nSlotsM m) (homeW (maxHashW u v) (nSlotsM m)) 0)
      (mprobeW (m.arr64 MSLOT) (m.arr64 MREC) 1 u v (baseW m 1) (nSlotsM m) (homeW (maxHashW u v) (nSlotsM m)) 0) mhash =
      some (w, m₁)) :
    AM.ok (internLNode (.max (decI u) (decI v))) a ∧
    MaxR m₁ (AM.st (internLNode (.max (decI u) (decI v))) a) ∧
    AM.res (internLNode (.max (decI u) (decI v))) a = decI w :=
  intern_correctG maxSch MRecRel mhash maxSch_wf maxFrame maxLens a m hR _ _ _ _ _
    (internLNode_max_run _ _ a) false rfl 0 (by simp) (by simp) _ _ (maxMatchOK m u v hu hv)
    (maxHomeOK m u v) _ _ (probe_homeG maxSch m 0 _ _ (mprobeW_arm m u v 0) _)
    (probe_homeG maxSch m 1 _ _ (mprobeW_arm m u v 1) _) _ (mpushOK_room m) _ rfl
    (maxNewOK m u v hu hv) w m₁ hI

include hR hu hv in
/-- **`intern_max`'s model refines the arena's `internLNode` at a `max` node.** -/
theorem mintern_correct (w : Word) (m' : Mem) (hI : minternW m u v = some (w, m')) :
    AM.ok (internLNode (.max (decI u) (decI v))) a ∧
    MaxR m' (AM.st (internLNode (.max (decI u) (decI v))) a) ∧
    AM.res (internLNode (.max (decI u) (decI v))) a = decI w := by
  rw [minternW_eqK m u v hR.1.1] at hI
  obtain ⟨m₁, h₁, hput⟩ := mkK_split _ _ _ _ _ _ _ hI
  obtain ⟨hok, hX, hres⟩ := mintern_core m a hR u v hu hv w m₁ h₁
  exact ⟨hok, storeR_frame maxSch MRecRel mhash maxSch_wf [] [] maxLocal [MHP] []
    (by simp [Apart, maxSch, MREC, MSLOT, MHP, SCB, POOL, CTL]) m₁ m'
    (derPutW_frame MHP (by decide) _ m₁ m' _ _ _ hput) _ _ _ hX, hres⟩

include hR hu hv in
/-- **The column across `intern_max`**: the new node's word is its record's bit (`hb`). -/
theorem mintern_hp (hC : ColT2 maxLens MHP hpW m a)
    (hb : lvlHPW m u ||| lvlHPW m v = b2w ((a.store.lss.ls.derived (decI u)).hasParam || (a.store.lss.ls.derived (decI v)).hasParam)) (w : Word) (m' : Mem)
    (hI : minternW m u v = some (w, m')) :
    ColT2 maxLens MHP hpW m' (AM.st (internLNode (.max (decI u) (decI v))) a) := by
  rw [minternW_eqK m u v hR.1.1] at hI
  obtain ⟨m₁, h₁, hput⟩ := mkK_split _ _ _ _ _ _ _ hI
  obtain ⟨hok, hX, hres⟩ := mintern_core m a hR u v hu hv w m₁ h₁
  have hcs := AM.proto_casesG maxLens _ _ _ _ _ _ a (internLNode_max_run _ _ a) hok
  have hfr : m₁.arr64 MHP = m.arr64 MHP :=
    (internM_frame _ maxSch_wf _ _ _ _ _ _ _ _ h₁).1 MHP (by simp [maxSch, MREC, MSLOT, MHP])
      (by decide)
  exact colMk maxSch maxSch_wf MRecRel mhash maxLens MHP hpW m m₁ m' a _ _ _ _ _ _ hR hX hC hfr
    hcs hres.symm (by rw [hb]; rfl) hput

end intern

/-- `intern_max` refines `internLNode (.max _ _)` under `MaxR`. -/
theorem internMax_refines (p : Prog) (hpf : p.lookup "max_find" = some maxFind)
    (hpp : p.lookup "max_push" = some maxPush) (hp : p.lookup "intern_max" = some internMax)
    (a₀ : AState) (n : Nat) (s₀ : St) (u v : Word) (hR : MaxR s₀.mem a₀) (hu : u.toNat < 2 ^ 32)
    (hv : v.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_max" [u, v]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internLNode (.max (decI u) (decI v))) a₀ ∧
      MaxR s'.mem (AM.st (internLNode (.max (decI u) (decI v))) a₀) ∧
      AM.res (internLNode (.max (decI u) (decI v))) a₀ = decI (r.headD 0); ⊤⦄ :=
  Sim.tripleD (internMax_spec p hpf hpp hp n s₀ u v)
    (Sim.ofOkD (mintern_correct s₀.mem a₀ hR u v hu hv))

end L.Arena
