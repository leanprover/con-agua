import ConAgua.Arena.ConsLibRel
import ConAgua.Arena.LevelStore
import ConAgua.Arena.LpColRel

/-!
# The level `succ` store refines the arena's `succ` tables

The third table on the store library (`StoreLib.lean`), written fresh: the record
`SuccNode { u : LIdx }` of the level store (`ConAgua/Arena/LevelStore.lean` has the L code). The
schema `succSch` (`SREC`, `SSLOT`, one word per node, counts at `CTL[6 + t]`, tag `1`), the
record relation `SRecRel` (the word is the child's handle word), the node hash `shash`, the lens
`succLens` on the level store's two `succ` tables (`a.store.lss.ls`). `SuccR m a` is the
library's `ConsR` for them. `internSucc_refines`: `intern_succ(u)` refines
`internLNode (.succ (decI u))` under `SuccR`.

Not represented: the derived column (`LStore.derOfView`, through `mixHash`) and every other
table.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

/-- The arena's `succ` cons key. -/
abbrev succKey (u : LIdx) : SuccNode := ⟨u⟩

/-- `a` with the scratch / persistent `succ` table of the level store replaced. -/
def withScrSuccs (a : AState) (t : Tbl SuccNode LIdx LDer) : AState :=
  { a with store := { a.store with lss := { a.store.lss with ls := { a.store.lss.ls with
      scr := { a.store.lss.ls.scr with succs := t } } } } }
def withPersSuccs (a : AState) (t : Tbl SuccNode LIdx LDer) : AState :=
  { a with store := { a.store with lss := { a.store.lss with ls := { a.store.lss.ls with
      pers := { a.store.lss.ls.pers with succs := t } } } } }

/-- The level store's two `succ` tables. -/
def succLens : Lens SuccNode LDer .level where
  on a := a.store.lss.ls.scratchOn
  getP a := a.store.lss.ls.pers.succs
  getS a := a.store.lss.ls.scr.succs
  setP := withPersSuccs
  setS := withScrSuccs
  on_setP _ _ := rfl
  on_setS _ _ := rfl
  getP_setP _ _ := rfl
  getS_setP _ _ := rfl
  getP_setS _ _ := rfl
  getS_setS _ _ := rfl

/-- `internLNode` at a `succ` node is the library's protocol, with no skip. -/
theorem internLNode_succ_run (u : LIdx) (a : AState) :
    (internLNode (.succ u)).run a =
      protoRun succLens (succKey u) LTag.succ a.store.lss.ls.pers.succs.cons[succKey u]?
        (a.store.lss.ls.derOfView (.succ u)) (.native "arena: level constructor array full") a := by
  simp only [internLNode, LStore.find?, LTables.find?, Tbl.find?, LTables.sizeOf, EStore.ls,
    EStore.internLevel, LsStore.internLevel, LStore.intern, LTables.push]
  cases hp : a.store.lss.ls.pers.succs.cons[succKey u]? <;> cases hs : a.store.lss.ls.scratchOn <;>
    cases hc : a.store.lss.ls.scr.succs.cons[succKey u]? <;>
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hp, hs, hc, Bool.false_eq_true,
      ↓reduceIte, succKey, ite_self, protoRun, succLens] <;>
    (try split) <;> simp_all [StateT.run_set, StateT.run_pure, withScrSuccs, withPersSuccs, fail,
      throwThe, MonadExceptOf.throw, StateT.run, Functor.map, StateT.map, set, StateT.set,
      StateT.lift, bind, Except.bind, Except.map, pure, Except.pure, StateT.bind, StateT.pure]

/-! ## The relation between L memory and the arena's `succ` tables -/

/-- The `succ` schema: `SREC`, `SSLOT`, one word per node, the counts at `CTL[6 + t]`. -/
def succSch : Schema := ⟨SREC, SSLOT, 1, 6, LTag.succ⟩

theorem succSch_wf : succSch.WF :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

theorem fld_succ0 (m : Mem) (t i : Word) : fld succSch m t i 0 = rdW (m.arr64 (tierA SREC t)) i := by
  simp [fld, Schema.ad, succSch]

/-- Node `i` of tier `t` holds `succ k.u`: its word is the child's handle word. -/
def SRecRel (m : Mem) (t i : Word) (k : SuccNode) : Prop :=
  tfld m SUCC t i 0 = k.u.word.toUInt64

/-- `SRecRel` in the raw words (inside the store library). -/
theorem SRecRel_raw (m : Mem) (t i : Word) (k : SuccNode) :
    SRecRel m t i k ↔
    rdW (m.arr64 (tierA SREC t)) i = k.u.word.toUInt64
  := Iff.rfl

/-- **The state relation** of the `succ` store: the library's relation for the level store's two
`succ` tables. -/
def SuccR (m : Mem) (a : AState) : Prop :=
  ConsR succCS SRecRel m a.store.lss.ls.scratchOn a.store.lss.ls.pers.succs
    a.store.lss.ls.scr.succs

/-- A node's relation and hash depend only on its word. -/
theorem succFrame : RFrame succSch SRecRel shash := by
  intro m m' t i _ hf
  have h0 := hf 0 (by decide)
  rw [fld_succ0, fld_succ0] at h0
  exact ⟨fun a h => by simpa only [SRecRel_raw, h0] using h, by simp only [shash, h0]⟩

/-! ## The query's obligations -/

/-- The match of `succ_find` on node `i` of tier `t`. -/
def sMt (m : Mem) (u t i : Word) : Bool := smatchW (m.arr64 (tierA SREC t)) t i u

section query
variable (m : Mem) (u : Word) (hu : u.toNat < 2 ^ 32)

include hu in
/-- **Matching is equality of `succ` nodes.** -/
theorem succMatchOK : MatchOK SRecRel (sMt m u) m (succKey (decI u)) := by
  intro t i k hr
  have := word_decI k.u u hu
  obtain ⟨ku⟩ := k
  grind [sMt, smatchW, SRecRel_raw]

theorem succHomeOK : HomeOK shash (sMt m u) m (succHashW u) := by
  intro t i hm
  simp only [sMt, smatchW, beq_iff_eq] at hm
  simp only [shash, hm]

include hu in
/-- The record `succ_push` writes holds the node. -/
theorem succNewOK : NewOKR succSch SRecRel shash m [u] (succKey (decI u)) (succHashW u) := by
  intro t ht hroom _
  have e : fld succSch (newRecM succSch m t [u]) t (cntW succSch m t) 0 = u := by
    have := hroom.1
    have := hroom.2
    rw [fld_newRecM succSch succSch_wf] <;> simp only [succSch, Schema.ad] at * <;> grind
  rw [fld_succ0] at e
  have := word_decI (decI u : LIdx) u hu
  simp only [SRecRel_raw, shash, succKey, e]
  grind

end query

/-! ## The bridges from the L models -/

theorem spushOK_room (m : Mem) (t : Word) (h : spushOK m t = true) : PushRoom succSch m t := by
  simp only [spushOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have := UInt64.toNat_shiftRight (m.len64 (tierA SREC t)) 0
  simp only [PushRoom, cntW, scnt, succSch, len64_eq] at *
  grind

/-- **The `succ` table's shape.** -/
theorem succCS_wf : succCS.WF where
  sch := succSch_wf
  P := by decide
  S := by decide
  col A h := by
    simp only [succCS, Option.some.injEq] at h; subst h
    exact ⟨by decide, by decide, by decide, fun m u k x t i => by
      simp only [succCS, shash, Mem.arr64_set64_ne _ _ _ _ _
        (tierA_ne (by decide) (by decide) (show SREC ≠ SHP by decide) t u)]⟩
  room m t h := (spushOK_room m t ((spushOK_eqC m t).trans h)).2
  colRoom A h m t ht hp := by
    simp only [succCS, Option.some.injEq] at h; subst h
    rw [← spushOK_eqC] at hp
    simp only [spushOK, Bool.and_eq_true, decide_eq_true_eq] at hp
    exact colRoom_of m SHP _ t hp.2
  colLt A h := by
    simp only [succCS, Option.some.injEq] at h; subst h; decide
  vs ks h hk := by simp [pushArgs, succCS, hk]
  ex _ := {
    nk := by decide
    nkw := by decide
    kpk := fun h => absurd h (by decide)
    mt := by
      intro m ks h t i hl
      obtain ⟨a, rfl⟩ := list_one ks (by simpa [succCS] using hl)
      simp [succCS, smatchW, shash, fieldsL, kfld, fld, Schema.ad, ConsSch.sch, List.range_succ, show UInt64.ofNat 0 = 0 from rfl, show UInt64.ofNat 1 = 1 from rfl]
    hs := by intro m t i; simp [succCS, smatchW, shash, fieldsL, kfld, fld, Schema.ad, ConsSch.sch, List.range_succ, show UInt64.ofNat 0 = 0 from rfl, show UInt64.ofNat 1 = 1 from rfl]
    qh := fun _ _ _ => rfl
    vs := by intro ks h hl f hf; simp [pushArgs, succCS, nkW, recK] at hf ⊢ <;> omega }

/-- `SRecRel` does not read the column. -/
theorem succColFree : ColFree succCS SRecRel := by
  intro A h m u k x t i a hr
  simp only [succCS, Option.some.injEq] at h; subst h
  simpa only [SRecRel_raw, Mem.arr64_set64_ne _ _ _ _ _ (tierA_ne (by decide) (by decide) (show SREC ≠ SHP by decide) t u)] using hr

/-- **What `intern_succ` changes**: the table's arrays, the column, the counts. -/
theorem sinternW_frame (m : Mem) (u : Word) (w : Word) (m' : Mem) (hI : sinternW m u = some (w, m')) :
    MemFrame [SREC, SREC + 256, SSLOT, SSLOT + 256, SHP, SHP + 256] [6, 7] m m' :=
  consInternM_frame succCS_wf hI

theorem succLocal : RLocal succSch SRecRel shash [] [] := by
  intro m m' hra _ _; simp only [succSch] at hra
  exact ⟨fun t i k h => by simpa only [SRecRel_raw, hra] using h, fun t i => by simp only [shash, hra]⟩

/-! ## `intern_succ` refines `internLNode (.succ _)` -/

section intern
variable (m : Mem) (a : AState) (hR : SuccR m a) (u : Word) (hu : u.toNat < 2 ^ 32)

include hR hu in
/-- **`intern_succ`'s model refines the arena's `internLNode` at a `succ` node.** -/
theorem sintern_correct (w : Word) (m' : Mem) (hI : sinternW m u = some (w, m')) :
    AM.ok (internLNode (.succ (decI u))) a ∧
    SuccR m' (AM.st (internLNode (.succ (decI u))) a) ∧
    AM.res (internLNode (.succ (decI u))) a = decI w :=
  consIntern_correct succCS_wf succFrame succColFree succLens a hR _ _ _ _ _
    (internLNode_succ_run _ a) false rfl [u] (by simp [skipC, succCS]) (by simp)
    ⟨rfl, succMatchOK m u hu, succHomeOK m u, succNewOK m u hu⟩ w m' hI

include hR hu in
/-- **The column across `intern_succ`**: the new node's word is its record's bit (`hb`). -/
theorem sintern_hp (hC : ColT2 succLens SHP hpW m a)
    (hb : lvlHPW m u = b2w (a.store.lss.ls.derived (decI u)).hasParam) (w : Word) (m' : Mem)
    (hI : sinternW m u = some (w, m')) :
    ColT2 succLens SHP hpW m' (AM.st (internLNode (.succ (decI u))) a) := by
  obtain ⟨hok, hX, hres⟩ := sintern_correct m a hR u hu w m' hI
  have hcs := AM.proto_casesG succLens _ _ _ _ _ _ a (internLNode_succ_run _ a) hok
  exact colMkC succCS_wf rfl succLens hpW hR hX hC hI hcs
    (by show lvlHPW m u = _; rw [hb]; rfl)

end intern

end L.Arena
