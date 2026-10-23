import ConAgua.Arena.StoreLib
import ConAgua.Arena.SimLib
import ConAgua.Arena.ImaxStore
import ConAgua.Arena.LpColRel

/-!
# The level `imax` store refines the arena's `imax` tables

The sixth table on the store library, the `app` shape (two handle fields, no scratch skip) for
the record `BinLNode { u v : LIdx }` of the level store's `imax` constructor
(`ConAgua/Arena/ImaxStore.lean` has the L code). The schema `imaxSch` (`IREC`, `ISLOT`, two words
per node, counts at `CTL[12 + t]`, tag `3`), the record relation `IRecRel` (the two words are the
children's handle words), the node hash `imhash`, the lens `imaxLens` on the level store's two
`imax` tables (`a.store.lss.ls.pers.imaxs`/`scr.imaxs`). `ImaxR m a` is the library's `StoreR` for
them. `internImax_refines`: `intern_imax(u, v)` refines `internLNode (.imax u v)` under `ImaxR`.
The level store has no scratch skip (`LStore.find?` probes the persistent tier unconditionally),
so `skB = false`, as for `succ`/`zero`/`max`.

Not represented: the derived column and every other table.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

/-- The arena's `imax` cons key. -/
abbrev imaxKey (u v : LIdx) : BinLNode := ⟨u, v⟩

/-- `a` with the scratch / persistent `imax` table of the level store replaced. -/
def withScrImaxs (a : AState) (t : Tbl BinLNode LIdx LDer) : AState :=
  { a with store := { a.store with lss := { a.store.lss with ls := { a.store.lss.ls with
      scr := { a.store.lss.ls.scr with imaxs := t } } } } }
def withPersImaxs (a : AState) (t : Tbl BinLNode LIdx LDer) : AState :=
  { a with store := { a.store with lss := { a.store.lss with ls := { a.store.lss.ls with
      pers := { a.store.lss.ls.pers with imaxs := t } } } } }

/-- The level store's two `imax` tables. -/
def imaxLens : Lens BinLNode LDer .level where
  on a := a.store.lss.ls.scratchOn
  getP a := a.store.lss.ls.pers.imaxs
  getS a := a.store.lss.ls.scr.imaxs
  setP := withPersImaxs
  setS := withScrImaxs
  on_setP _ _ := rfl
  on_setS _ _ := rfl
  getP_setP _ _ := rfl
  getS_setP _ _ := rfl
  getP_setS _ _ := rfl
  getS_setS _ _ := rfl

/-- `internLNode` at an `imax` node is the library's protocol, with no skip. -/
theorem internLNode_imax_run (u v : LIdx) (a : AState) :
    (internLNode (.imax u v)).run a =
      protoRun imaxLens (imaxKey u v) LTag.imax a.store.lss.ls.pers.imaxs.cons[imaxKey u v]?
        (a.store.lss.ls.derOfView (.imax u v)) (.native "arena: level constructor array full") a := by
  simp only [internLNode, LStore.find?, LTables.find?, Tbl.find?, LTables.sizeOf, EStore.ls,
    EStore.internLevel, LsStore.internLevel, LStore.intern, LTables.push]
  cases hp : a.store.lss.ls.pers.imaxs.cons[imaxKey u v]? <;> cases hs : a.store.lss.ls.scratchOn <;>
    cases hc : a.store.lss.ls.scr.imaxs.cons[imaxKey u v]? <;>
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hp, hs, hc, Bool.false_eq_true,
      ↓reduceIte, imaxKey, ite_self, protoRun, imaxLens] <;>
    (try split) <;> simp_all [StateT.run_set, StateT.run_pure, withScrImaxs, withPersImaxs, fail,
      throwThe, MonadExceptOf.throw, StateT.run, Functor.map, StateT.map, set, StateT.set,
      StateT.lift, bind, Except.bind, Except.map, pure, Except.pure, StateT.bind, StateT.pure]

/-! ## The relation between L memory and the arena's `imax` tables -/

/-- The `imax` schema: `IREC`, `ISLOT`, two words per node, the counts at `CTL[12 + t]`. -/
def imaxSch : Schema := ⟨IREC, ISLOT, 2, 4, 12, LTag.imax⟩

theorem iimaxSch_wf : imaxSch.WF :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem fld_imax0 (m : Mem) (t i : Word) : fld imaxSch m t i 0 = rdW (m.arr64 IREC) (i * 4 + t * 2) := by
  simp [fld, Schema.ad, imaxSch]
theorem fld_imax (m : Mem) (t i f : Word) :
    fld imaxSch m t i f = rdW (m.arr64 IREC) (i * 4 + t * 2 + f) := rfl

/-- Node `i` of tier `t` holds the `imax` node `k`: its two handle words. -/
def IRecRel (m : Mem) (t i : Word) (k : BinLNode) : Prop :=
  rdW (m.arr64 IREC) (i * 4 + t * 2) = k.u.word.toUInt64 ∧
  rdW (m.arr64 IREC) (i * 4 + t * 2 + 1) = k.v.word.toUInt64

/-- **The state relation** of the `imax` store: the library's relation for the two `imax` tables. -/
def ImaxR (m : Mem) (a : AState) : Prop :=
  StoreR imaxSch IRecRel imhash m a.store.lss.ls.scratchOn a.store.lss.ls.pers.imaxs
    a.store.lss.ls.scr.imaxs

/-- A node's relation and hash depend only on its two words. -/
theorem imaxFrame : RFrame imaxSch IRecRel imhash := by
  intro m m' t i _ hf
  have h0 := hf 0 (by decide)
  have h1 := hf 1 (by decide)
  rw [fld_imax0, fld_imax0] at h0
  rw [fld_imax, fld_imax] at h1
  exact ⟨fun a h => by simpa only [IRecRel, h0, h1] using h, by simp only [imhash, h0, h1]⟩

/-! ## The query's obligations -/

/-- The match of `imax_find` on node `i` of tier `t`. -/
def imMt (m : Mem) (u v t i : Word) : Bool := immatchW (m.arr64 IREC) t i u v

section query
variable (m : Mem) (u v : Word) (hu : u.toNat < 2 ^ 32) (hv : v.toNat < 2 ^ 32)

include hu hv in
/-- **Matching is equality of `imax` nodes.** -/
theorem imaxMatchOK : MatchOK IRecRel (imMt m u v) m (imaxKey (decI u) (decI v)) := by
  intro t i k hr
  have := word_decI k.u u hu
  have := word_decI k.v v hv
  obtain ⟨ku, kv⟩ := k
  grind [imMt, immatchW, IRecRel, decE_eq]

theorem imaxHomeOK : HomeOK imhash (imMt m u v) m (imaxHashW u v) := by
  intro t i hm
  simp only [imMt, immatchW, Bool.and_eq_true, beq_iff_eq] at hm
  simp only [imhash, hm.1, hm.2]

include hu hv in
/-- The record `imax_push` writes holds the node. -/
theorem imaxNewOK : NewOK imaxSch IRecRel imhash m [u, v] (imaxKey (decI u) (decI v)) (imaxHashW u v) := by
  intro t j ht hroom
  have e : ∀ g, g < 2 → fld imaxSch (pushG imaxSch m t [u, v] j (cntW imaxSch m t)) t
      (cntW imaxSch m t) g = [u, v].getD g.toNat 0 := by
    intro g hg
    have := hroom.1
    have := hroom.2
    rw [fld_pushG imaxSch iimaxSch_wf] <;> simp only [imaxSch, Schema.ad] at * <;> grind
  have e0 := e 0 (by decide)
  have e1 := e 1 (by decide)
  rw [fld_imax0] at e0
  rw [fld_imax] at e1
  simp only [List.getD_cons_zero, List.getD_cons_succ, show (1 : Word).toNat = 0 + 1 from rfl,
    show (0 : Word).toNat = 0 from rfl] at e0 e1
  have := word_decI (decI u : LIdx) u hu
  have := word_decI (decI v : LIdx) v hv
  simp only [IRecRel, imhash, imaxKey, e0, e1]
  grind [decE_eq]

end query

/-! ## The bridges from the L models -/

theorem iimprobeW_arm (m : Mem) (u v t : Word) :
    ∀ j d, improbeW (m.arr64 ISLOT) (m.arr64 IREC) t u v (baseW m t) (nSlotsI m) j d =
      probeArm imaxSch m t (imMt m u v t) (improbeW (m.arr64 ISLOT) (m.arr64 IREC) t u v (baseW m t) (nSlotsI m)) j d := by
  intro j d; rw [improbeW]; rfl

theorem iimpushOK_room (m : Mem) (t : Word) (h : impushOK m t = true) : PushRoom imaxSch m t := by
  simp only [impushOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have := UInt64.toNat_shiftRight (m.len64 IREC) 2
  simp only [PushRoom, cntW, imcnt, imaxSch, len64_eq] at *
  grind

theorem iimpushMem_eq (m : Mem) (t u v j c : Word) :
    impushMem m t u v j c = (pushG imaxSch m t [u, v] j c).set64 IHP (c * 2 + t) (lvlHPW m u ||| lvlHPW m v) := by
  simp [impushMem, pushG, wrRec, Schema.ad, imaxSch]

theorem iiminternW_eq (m : Mem) (u v : Word) :
    iminternW m u v = internMD imaxSch IHP (lvlHPW m u ||| lvlHPW m v) m 0 (impushOK m) [u, v]
      (improbeW (m.arr64 ISLOT) (m.arr64 IREC) 0 u v (baseW m 0) (nSlotsI m) (homeW (imaxHashW u v) (nSlotsI m)) 0)
      (improbeW (m.arr64 ISLOT) (m.arr64 IREC) 1 u v (baseW m 1) (nSlotsI m) (homeW (imaxHashW u v) (nSlotsI m)) 0) := by
  have e0 : ∀ x, hdW imaxSch.tag.toUInt64 0 x = imaxP + x := fun x => by
    simp [hdW, imaxSch, imaxP, LTag.imax]
  have e1 : ∀ x, hdW imaxSch.tag.toUInt64 1 x = imaxS + x := fun x => by
    simp [hdW, imaxSch, imaxS, LTag.imax]
  simp only [iminternW, internMD, iimpushMem_eq, e0, e1, true_and]
  rfl

/-- **What `intern_imax` changes**: the table's arrays, the column, the counts. -/
theorem iminternW_frame (m : Mem) (u v : Word) (w : Word) (m' : Mem) (hI : iminternW m u v = some (w, m')) :
    MemFrame [IREC, ISLOT, IHP] [12, 13] m m' := by
  rw [iiminternW_eq] at hI
  exact internMD_frame imaxSch iimaxSch_wf IHP (by decide) _ _ _ _ _ _ _ _ _ hI

/-- `intern_imax`'s model as the library's interning and the `mk_*` tail (`mkK`), given the count
words. -/
theorem iminternW_eqK (m : Mem) (u v : Word) (hctl : imaxSch.ca.toNat + 2 ≤ (m.arr64 CTL).size) :
    iminternW m u v = mkK IHP imaxSch.ca (cnt2 m imaxSch.ca) (lvlHPW m u ||| lvlHPW m v)
      (internM imaxSch m 0 (impushOK m) [u, v]
      (improbeW (m.arr64 ISLOT) (m.arr64 IREC) 0 u v (baseW m 0) (nSlotsI m) (homeW (imaxHashW u v) (nSlotsI m)) 0)
      (improbeW (m.arr64 ISLOT) (m.arr64 IREC) 1 u v (baseW m 1) (nSlotsI m) (homeW (imaxHashW u v) (nSlotsI m)) 0)) := by
  rw [iiminternW_eq]
  refine internMD_mkK imaxSch iimaxSch_wf _ _ _ _ _ _ _ _ hctl (fun t ht hp => ?_)
  simp only [impushOK, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨⟨h1, -⟩, h2⟩, -⟩ := hp
  exact ⟨h1, col_room _ _ _ ht h1 h2⟩

theorem imaxLocal : RLocal imaxSch IRecRel imhash [] [] := by
  intro m m' hra _ _; simp only [imaxSch] at hra
  exact ⟨fun t i k h => by simpa only [IRecRel, hra] using h, fun t i => by simp only [imhash, hra]⟩

/-! ## `intern_imax` refines `internLNode (.imax _ _)` -/

section intern
variable (m : Mem) (a : AState) (hR : ImaxR m a) (u v : Word) (hu : u.toNat < 2 ^ 32)
  (hv : v.toNat < 2 ^ 32)

include hR hu hv in
/-- The library's half of `intern_imax` (before the column). -/
theorem imintern_core (w : Word) (m₁ : Mem)
    (hI : internM imaxSch m 0 (impushOK m) [u, v]
      (improbeW (m.arr64 ISLOT) (m.arr64 IREC) 0 u v (baseW m 0) (nSlotsI m) (homeW (imaxHashW u v) (nSlotsI m)) 0)
      (improbeW (m.arr64 ISLOT) (m.arr64 IREC) 1 u v (baseW m 1) (nSlotsI m) (homeW (imaxHashW u v) (nSlotsI m)) 0) =
      some (w, m₁)) :
    AM.ok (internLNode (.imax (decI u) (decI v))) a ∧
    ImaxR m₁ (AM.st (internLNode (.imax (decI u) (decI v))) a) ∧
    AM.res (internLNode (.imax (decI u) (decI v))) a = decI w :=
  intern_correctG imaxSch IRecRel imhash iimaxSch_wf imaxFrame imaxLens a m hR _ _ _ _ _
    (internLNode_imax_run _ _ a) false rfl 0 (by simp) (by simp) _ _ (imaxMatchOK m u v hu hv)
    (imaxHomeOK m u v) _ _ (probe_homeG imaxSch m 0 _ _ (iimprobeW_arm m u v 0) _)
    (probe_homeG imaxSch m 1 _ _ (iimprobeW_arm m u v 1) _) _ (iimpushOK_room m) _ rfl
    (imaxNewOK m u v hu hv) w m₁ hI

include hR hu hv in
/-- **`intern_imax`'s model refines the arena's `internLNode` at an `imax` node.** -/
theorem imintern_correct (w : Word) (m' : Mem) (hI : iminternW m u v = some (w, m')) :
    AM.ok (internLNode (.imax (decI u) (decI v))) a ∧
    ImaxR m' (AM.st (internLNode (.imax (decI u) (decI v))) a) ∧
    AM.res (internLNode (.imax (decI u) (decI v))) a = decI w := by
  rw [iminternW_eqK m u v hR.1.1] at hI
  obtain ⟨m₁, h₁, hput⟩ := mkK_split _ _ _ _ _ _ _ hI
  obtain ⟨hok, hX, hres⟩ := imintern_core m a hR u v hu hv w m₁ h₁
  exact ⟨hok, storeR_frame imaxSch IRecRel imhash iimaxSch_wf [] [] imaxLocal [IHP] []
    (by simp [Apart, imaxSch, IREC, ISLOT, IHP, SCB, POOL, CTL]) m₁ m'
    (derPutW_frame IHP (by decide) _ m₁ m' _ _ _ hput) _ _ _ hX, hres⟩

include hR hu hv in
/-- **The column across `intern_imax`**: the new node's word is its record's bit (`hb`). -/
theorem imintern_hp (hC : ColT2 imaxLens IHP hpW m a)
    (hb : lvlHPW m u ||| lvlHPW m v = b2w ((a.store.lss.ls.derived (decI u)).hasParam || (a.store.lss.ls.derived (decI v)).hasParam)) (w : Word) (m' : Mem)
    (hI : iminternW m u v = some (w, m')) :
    ColT2 imaxLens IHP hpW m' (AM.st (internLNode (.imax (decI u) (decI v))) a) := by
  rw [iminternW_eqK m u v hR.1.1] at hI
  obtain ⟨m₁, h₁, hput⟩ := mkK_split _ _ _ _ _ _ _ hI
  obtain ⟨hok, hX, hres⟩ := imintern_core m a hR u v hu hv w m₁ h₁
  have hcs := AM.proto_casesG imaxLens _ _ _ _ _ _ a (internLNode_imax_run _ _ a) hok
  have hfr : m₁.arr64 IHP = m.arr64 IHP :=
    (internM_frame _ iimaxSch_wf _ _ _ _ _ _ _ _ h₁).1 IHP (by simp [imaxSch, IREC, ISLOT, IHP])
      (by decide)
  exact colMk imaxSch iimaxSch_wf IRecRel imhash imaxLens IHP hpW m m₁ m' a _ _ _ _ _ _ hR hX hC hfr
    hcs hres.symm (by rw [hb]; rfl) hput

end intern

/-- `intern_max` refines `internLNode (.imax _ _)` under `ImaxR`. -/
theorem internImax_refines (p : Prog) (hpf : p.lookup "imax_find" = some imaxFind)
    (hpp : p.lookup "imax_push" = some imaxPush) (hp : p.lookup "intern_imax" = some internImax)
    (a₀ : AState) (n : Nat) (s₀ : St) (u v : Word) (hR : ImaxR s₀.mem a₀) (hu : u.toNat < 2 ^ 32)
    (hv : v.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_imax" [u, v]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internLNode (.imax (decI u) (decI v))) a₀ ∧
      ImaxR s'.mem (AM.st (internLNode (.imax (decI u) (decI v))) a₀) ∧
      AM.res (internLNode (.imax (decI u) (decI v))) a₀ = decI (r.headD 0); ⊤⦄ :=
  Sim.tripleD (internImax_spec p hpf hpp hp n s₀ u v)
    (Sim.ofOkD (imintern_correct s₀.mem a₀ hR u v hu hv))

end L.Arena
