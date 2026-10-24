import ConAgua.Arena.ConsLibRel
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
`max` tables (`a.store.lss.ls.pers.maxs`/`scr.maxs`). `MaxR m a` is the library's `ConsR` for
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
  ConsR maxCS MRecRel m a.store.lss.ls.scratchOn a.store.lss.ls.pers.maxs
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
theorem maxNewOK : NewOKR maxSch MRecRel mhash m [u, v] (maxKey (decI u) (decI v)) (maxHashW u v) := by
  intro t ht hroom
  have e : ∀ g, g < 2 → fld maxSch (newRecM maxSch m t [u, v]) t
      (cntW maxSch m t) g = [u, v].getD g.toNat 0 := by
    intro g hg
    have := hroom.1
    have := hroom.2
    rw [fld_recW maxSch maxSch_wf] <;> simp only [maxSch, Schema.ad] at * <;> grind
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

theorem mpushOK_room (m : Mem) (t : Word) (h : mpushOK m t = true) : PushRoom maxSch m t := by
  simp only [mpushOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have := UInt64.toNat_shiftRight (m.len64 MREC) 2
  simp only [PushRoom, cntW, mcnt, maxSch, len64_eq] at *
  grind

/-- **The `max` table's shape.** -/
theorem maxCS_wf : maxCS.WF where
  sch := maxSch_wf
  P := by decide
  S := by decide
  col A h := by
    simp only [maxCS, Option.some.injEq] at h; subst h
    exact ⟨by decide, by decide, by decide, fun m k x t i => by
      simp only [maxCS, mhash, Mem.arr64_set64_ne _ _ _ _ _ (show MREC ≠ MHP by decide)]⟩
  room m t h := (mpushOK_room m t ((mpushOK_eqC m t).trans h)).2
  colRoom A h m t ht hp := by
    simp only [maxCS, Option.some.injEq] at h; subst h
    rw [← mpushOK_eqC] at hp
    simp only [mpushOK, Bool.and_eq_true, decide_eq_true_eq] at hp
    exact colRoom_of m MHP _ t ht hp.1.1 hp.2
  vs ks h hk := by simp [pushArgs, maxCS, hk]

/-- `MRecRel` does not read the column. -/
theorem maxColFree : ColFree maxCS MRecRel := by
  intro A h m k x t i a hr
  simp only [maxCS, Option.some.injEq] at h; subst h
  simpa only [MRecRel, Mem.arr64_set64_ne _ _ _ _ _ (show MREC ≠ MHP by decide)] using hr

/-- **What `intern_max` changes**: the table's arrays, the column, the counts. -/
theorem minternW_frame (m : Mem) (u v : Word) (w : Word) (m' : Mem) (hI : minternW m u v = some (w, m')) :
    MemFrame [MREC, MSLOT, MHP] [10, 11] m m' :=
  consInternM_frame maxCS_wf hI

theorem maxLocal : RLocal maxSch MRecRel mhash [] [] := by
  intro m m' hra _ _; simp only [maxSch] at hra
  exact ⟨fun t i k h => by simpa only [MRecRel, hra] using h, fun t i => by simp only [mhash, hra]⟩

/-! ## `intern_max` refines `internLNode (.max _ _)` -/

section intern
variable (m : Mem) (a : AState) (hR : MaxR m a) (u v : Word) (hu : u.toNat < 2 ^ 32)
  (hv : v.toNat < 2 ^ 32)

include hR hu hv in
/-- **`intern_max`'s model refines the arena's `internLNode` at a `max` node.** -/
theorem mintern_correct (w : Word) (m' : Mem) (hI : minternW m u v = some (w, m')) :
    AM.ok (internLNode (.max (decI u) (decI v))) a ∧
    MaxR m' (AM.st (internLNode (.max (decI u) (decI v))) a) ∧
    AM.res (internLNode (.max (decI u) (decI v))) a = decI w :=
  consIntern_correct maxCS_wf maxFrame maxColFree maxLens a hR _ _ _ _ _
    (internLNode_max_run _ _ a) false rfl [u, v] (by simp [skipC, maxCS]) (by simp)
    ⟨rfl, maxMatchOK m u v hu hv, maxHomeOK m u v, maxNewOK m u v hu hv⟩ w m' hI

include hR hu hv in
/-- **The column across `intern_max`**: the new node's word is its record's bit (`hb`). -/
theorem mintern_hp (hC : ColT2 maxLens MHP hpW m a)
    (hb : lvlHPW m u ||| lvlHPW m v = b2w ((a.store.lss.ls.derived (decI u)).hasParam || (a.store.lss.ls.derived (decI v)).hasParam)) (w : Word) (m' : Mem)
    (hI : minternW m u v = some (w, m')) :
    ColT2 maxLens MHP hpW m' (AM.st (internLNode (.max (decI u) (decI v))) a) := by
  obtain ⟨hok, hX, hres⟩ := mintern_correct m a hR u v hu hv w m' hI
  have hcs := AM.proto_casesG maxLens _ _ _ _ _ _ a (internLNode_max_run _ _ a) hok
  exact colMkC maxCS_wf rfl maxLens hpW hR hX hC hI hcs
    (by show lvlHPW m u ||| lvlHPW m v = _; rw [hb]; rfl)

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
