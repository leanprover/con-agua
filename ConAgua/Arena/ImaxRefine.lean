import ConAgua.Arena.ConsLibRel
import ConAgua.Arena.SimLib
import ConAgua.Arena.ImaxStore
import ConAgua.Arena.LpColRel

/-!
# The level `imax` store refines the arena's `imax` tables

The sixth table on the store library, the `app` shape (two handle fields, no scratch skip) for
the record `BinLNode { u v : LIdx }` of the level store's `imax` constructor
(`ConAgua/Arena/ImaxStore.lean` has the L code). The schema `imaxSch` (`IREC`, `ISLOT`, one packed word
per node, counts at `CTL[12 + t]`, tag `3`), the record relation `IRecRel` (the two halves of the word are the
children's handle words), the node hash `imhash`, the lens `imaxLens` on the level store's two
`imax` tables (`a.store.lss.ls.pers.imaxs`/`scr.imaxs`). `ImaxR m a` is the library's `ConsR` for
them. `internImax_refines`: `intern_imax(u, v)` refines `internLNode (.imax u v)` under `ImaxR`.
The level store has no scratch skip (`LStore.find?` probes the persistent tier unconditionally),
so `skB = false`, as for `succ`/`zero`/`max`.

Not represented: the derived column and every other table.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


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
      ↓reduceIte, imaxKey, protoRun, imaxLens] <;>
    (try split) <;> simp_all [withScrImaxs, withPersImaxs, fail,
      throwThe, MonadExceptOf.throw, StateT.run, set, StateT.set,
      StateT.lift, bind, Except.bind, pure, Except.pure, StateT.bind, StateT.pure]

/-! ## The relation between L memory and the arena's `imax` tables -/

/-- The `imax` schema: `IREC`, `ISLOT`, one packed word per node, the counts at `CTL[12 + t]`. -/
def imaxSch : Schema := ⟨IREC, ISLOT, 1, 12, LTag.imax⟩

theorem iimaxSch_wf : imaxSch.WF :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

theorem fld_imax0 (m : Mem) (t i : Word) : fld imaxSch m t i 0 = rdW (m.arr64 (tierA IREC t)) i := by
  simp [fld, Schema.ad, imaxSch]

/-- Node `i` of tier `t` holds the `imax` node `k`: its two handle words. -/
def IRecRel (m : Mem) (t i : Word) (k : BinLNode) : Prop :=
  tfld m IMAX t i 0 = k.u.word.toUInt64 ∧
  tfld m IMAX t i 1 = k.v.word.toUInt64

/-- `IRecRel` in the raw words (inside the store library). -/
theorem IRecRel_raw (m : Mem) (t i : Word) (k : BinLNode) :
    IRecRel m t i k ↔
    rdW (m.arr64 (tierA IREC t)) i &&& 4294967295 = k.u.word.toUInt64 ∧
    rdW (m.arr64 (tierA IREC t)) i >>> 32 = k.v.word.toUInt64
  := Iff.rfl

/-- **The state relation** of the `imax` store: the library's relation for the two `imax` tables. -/
def ImaxR (m : Mem) (a : AState) : Prop :=
  ConsR imaxCS IRecRel m a.store.lss.ls.scratchOn a.store.lss.ls.pers.imaxs
    a.store.lss.ls.scr.imaxs

/-- A node's relation and hash depend only on its record word. -/
theorem imaxFrame : RFrame imaxSch IRecRel imhash := by
  intro m m' t i _ hf
  have h0 := hf 0 (by decide)
  rw [fld_imax0, fld_imax0] at h0
  exact ⟨fun a h => by simpa only [IRecRel_raw, h0] using h, by simp only [imhash, h0]⟩

/-! ## The query's obligations -/

/-- The match of `imax_find` on node `i` of tier `t`. -/
def imMt (m : Mem) (u v t i : Word) : Bool := immatchW (m.arr64 (tierA IREC t)) t i u v

section query
variable (m : Mem) (u v : Word) (hu : u.toNat < 2 ^ 32) (hv : v.toNat < 2 ^ 32)

include hu hv in
/-- **Matching is equality of `imax` nodes.** -/
theorem imaxMatchOK : MatchOK IRecRel (imMt m u v) m (imaxKey (decI u) (decI v)) := by
  intro t i k hr
  have := word_decI k.u u hu
  have := word_decI k.v v hv
  obtain ⟨ku, kv⟩ := k
  grind [imMt, immatchW, IRecRel_raw, decE_eq]

theorem imaxHomeOK : HomeOK imhash (imMt m u v) m (imaxHashW u v) := by
  intro t i hm
  simp only [imMt, immatchW, Bool.and_eq_true, beq_iff_eq] at hm
  simp only [imhash, hm.1, hm.2]

include hu hv in
/-- The record `imax_push` writes holds the node. -/
theorem imaxNewOK : NewOKR imaxSch IRecRel imhash m [u ||| v <<< 32] (imaxKey (decI u) (decI v)) (imaxHashW u v) := by
  intro t ht hroom _
  have e0 : fld imaxSch (newRecM imaxSch m t [u ||| v <<< 32]) t (cntW imaxSch m t) 0 =
      u ||| v <<< 32 := by
    have := hroom.1
    have := hroom.2
    rw [fld_newRecM imaxSch iimaxSch_wf] <;> simp only [imaxSch, Schema.ad] at * <;> grind
  rw [fld_imax0] at e0
  have := word_decI (decI u : LIdx) u hu
  have := word_decI (decI v : LIdx) v hv
  simp only [IRecRel_raw, imhash, imaxKey, e0, pack_lo u v hu hv, pack_hi u v hu hv]
  grind [decE_eq]

end query

/-! ## The bridges from the L models -/

theorem iimpushOK_room (m : Mem) (t : Word) (h : impushOK m t = true) : PushRoom imaxSch m t := by
  simp only [impushOK, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [PushRoom, cntW, imcnt, imaxSch, len64_eq] at *
  grind

/-- **The `imax` table's shape.** -/
theorem imaxCS_wf : imaxCS.WF where
  sch := iimaxSch_wf
  P := by decide
  S := by decide
  col A h := by
    simp only [imaxCS, Option.some.injEq] at h; subst h
    exact ⟨by decide, by decide, by decide, fun m u k x t i => by
      simp only [imaxCS, imhash, Mem.arr64_set64_ne _ _ _ _ _
        (tierA_ne (by decide) (by decide) (show IREC ≠ IHP by decide) t u)]⟩
  room m t h := (iimpushOK_room m t ((impushOK_eqC m t).trans h)).2
  colRoom A h m t ht hp := by
    simp only [imaxCS, Option.some.injEq] at h; subst h
    rw [← impushOK_eqC] at hp
    simp only [impushOK, Bool.and_eq_true, decide_eq_true_eq] at hp
    exact colRoom_of m IHP _ t hp.2
  colLt A h := by
    simp only [imaxCS, Option.some.injEq] at h; subst h; decide
  vs ks h hk := by simp [pushArgs, imaxCS, hk]
  ex _ := {
    nk := by decide
    nkw := by decide
    kpk := fun _ => rfl
    mt := by
      intro m ks h t i hl
      obtain ⟨a, b, rfl⟩ := list_two ks (by simpa [imaxCS] using hl)
      simp [imaxCS, immatchW, fieldsL, kfld, fld, Schema.ad, ConsSch.sch, List.range_succ]
    hs := by intro m t i; simp [imaxCS, immatchW, imhash, fieldsL, kfld, fld, Schema.ad, ConsSch.sch, List.range_succ]
    qh := fun _ _ _ => rfl
    vs := by
      intro ks h hl f hf
      simp only [nkW, imaxCS, ↓reduceIte, Nat.lt_one_iff] at hf
      subst hf; simp [pushArgs, imaxCS, recK, kwQ] }

/-- `IRecRel` does not read the column. -/
theorem imaxColFree : ColFree imaxCS IRecRel := by
  intro A h m u k x t i a hr
  simp only [imaxCS, Option.some.injEq] at h; subst h
  simpa only [IRecRel_raw, Mem.arr64_set64_ne _ _ _ _ _ (tierA_ne (by decide) (by decide) (show IREC ≠ IHP by decide) t u)] using hr

/-- **What `intern_imax` changes**: the table's arrays, the column, the counts. -/
theorem iminternW_frame (m : Mem) (u v : Word) (w : Word) (m' : Mem) (hI : iminternW m u v = some (w, m')) :
    MemFrame [IREC, IREC + 256, ISLOT, ISLOT + 256, IHP, IHP + 256] [12, 13] m m' :=
  consInternM_frame imaxCS_wf hI

theorem imaxLocal : RLocal imaxSch IRecRel imhash [] [] := by
  intro m m' hra _ _; simp only [imaxSch] at hra
  exact ⟨fun t i k h => by simpa only [IRecRel_raw, hra] using h, fun t i => by simp only [imhash, hra]⟩

/-! ## `intern_imax` refines `internLNode (.imax _ _)` -/

section intern
variable (m : Mem) (a : AState) (hR : ImaxR m a) (u v : Word) (hu : u.toNat < 2 ^ 32)
  (hv : v.toNat < 2 ^ 32)

include hR hu hv in
/-- **`intern_imax`'s model refines the arena's `internLNode` at an `imax` node.** -/
theorem imintern_correct (w : Word) (m' : Mem) (hI : iminternW m u v = some (w, m')) :
    AM.ok (internLNode (.imax (decI u) (decI v))) a ∧
    ImaxR m' (AM.st (internLNode (.imax (decI u) (decI v))) a) ∧
    AM.res (internLNode (.imax (decI u) (decI v))) a = decI w :=
  consIntern_correct imaxCS_wf imaxFrame imaxColFree imaxLens a hR _ _ _ _ _
    (internLNode_imax_run _ _ a) false rfl [u, v] (by simp [skipC, imaxCS]) (by simp)
    ⟨rfl, imaxMatchOK m u v hu hv, imaxHomeOK m u v, imaxNewOK m u v hu hv⟩ w m' hI

include hR hu hv in
/-- **The column across `intern_imax`**: the new node's word is its record's bit (`hb`). -/
theorem imintern_hp (hC : ColT2 imaxLens IHP hpW m a)
    (hb : lvlHPW m u ||| lvlHPW m v = b2w ((a.store.lss.ls.derived (decI u)).hasParam || (a.store.lss.ls.derived (decI v)).hasParam)) (w : Word) (m' : Mem)
    (hI : iminternW m u v = some (w, m')) :
    ColT2 imaxLens IHP hpW m' (AM.st (internLNode (.imax (decI u) (decI v))) a) := by
  obtain ⟨hok, hX, hres⟩ := imintern_correct m a hR u v hu hv w m' hI
  have hcs := AM.proto_casesG imaxLens _ _ _ _ _ _ a (internLNode_imax_run _ _ a) hok
  exact colMkC imaxCS_wf rfl imaxLens hpW hR hX hC hI hcs
    (by show lvlHPW m u ||| lvlHPW m v = _; rw [hb]; rfl)

end intern

end L.Arena
