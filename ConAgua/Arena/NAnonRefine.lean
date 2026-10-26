import ConAgua.Arena.ConsLibRel
import ConAgua.Arena.SimLib
import ConAgua.Arena.NAnonStore

/-!
# The name store's `anonymous` store refines the arena's `anonymous` tables

The fieldless case on the name store: the record `AnonNode` (no fields,
`ConAgua/Arena/NAnonStore.lean` has the L code). The schema `nanonSch` (`NAREC`, `NASLOT`, one
dummy word per node, counts at `CTL[34 + t]`, tag `0`), the record relation `NaRecRel` (trivially
`True`: there is only one possible `AnonNode`), the node hash `nahash` (the constant `nahashW`),
the lens `nanonLens` on the name store's two `anonymous` tables
(`a.store.lss.ls.ns.pers.anons`/`scr.anons`). `NAnonR m a` is the library's `ConsR` for them.
`internNAnon_refines`: `intern_nanon()` refines `internNNode .anonymous` under `NAnonR`. Unlike
the expression store, the name store's `NStore.find?` probes the persistent tier unconditionally
(no scratch skip), as the level store's `LStore.find?` does.

Not represented: the derived column and every other table.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

/-- The arena's `anonymous` cons key: the only value of `AnonNode`. -/
abbrev naKey : AnonNode := .mk

theorem naNode_eq (a : AnonNode) : a = naKey := by cases a; rfl

/-- `a` with the scratch / persistent `anonymous` table of the name store replaced. -/
def withScrNAnons (a : AState) (t : Tbl AnonNode NIdx UInt64) : AState :=
  { a with store := { a.store with lss := { a.store.lss with ls := { a.store.lss.ls with
      ns := { a.store.lss.ls.ns with scr := { a.store.lss.ls.ns.scr with anons := t } } } } } }
def withPersNAnons (a : AState) (t : Tbl AnonNode NIdx UInt64) : AState :=
  { a with store := { a.store with lss := { a.store.lss with ls := { a.store.lss.ls with
      ns := { a.store.lss.ls.ns with pers := { a.store.lss.ls.ns.pers with anons := t } } } } } }

/-- The name store's two `anonymous` tables. -/
def nanonLens : Lens AnonNode UInt64 .name where
  on a := a.store.lss.ls.ns.scratchOn
  getP a := a.store.lss.ls.ns.pers.anons
  getS a := a.store.lss.ls.ns.scr.anons
  setP := withPersNAnons
  setS := withScrNAnons
  on_setP _ _ := rfl
  on_setS _ _ := rfl
  getP_setP _ _ := rfl
  getS_setP _ _ := rfl
  getP_setS _ _ := rfl
  getS_setS _ _ := rfl

/-- `internNNode` at the `anonymous` node is the library's protocol, with no skip (as the level
store's `internLNode`). -/
theorem internNNode_anon_run (a : AState) :
    (internNNode .anonymous).run a =
      protoRun nanonLens naKey NTag.anonymous a.store.lss.ls.ns.pers.anons.cons[naKey]?
        (a.store.lss.ls.ns.derOfView .anonymous) (.native "arena: name constructor array full") a := by
  simp only [internNNode, NStore.find?, NTables.find?, Tbl.find?, NTables.sizeOf, EStore.ns,
    EStore.internName, LsStore.internName, LStore.internName, NStore.intern, NTables.push]
  cases hp : a.store.lss.ls.ns.pers.anons.cons[naKey]? <;> cases hs : a.store.lss.ls.ns.scratchOn <;>
    cases hc : a.store.lss.ls.ns.scr.anons.cons[naKey]? <;>
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hp, hs, hc, Bool.false_eq_true,
      ↓reduceIte, naKey, protoRun, nanonLens] <;>
    (try split) <;> simp_all [withScrNAnons, withPersNAnons, fail,
      throwThe, MonadExceptOf.throw, StateT.run, set, StateT.set,
      StateT.lift, bind, Except.bind, pure, Except.pure, StateT.bind, StateT.pure]

/-! ## The relation between L memory and the arena's `anonymous` tables -/

/-- The `anonymous` schema: `NAREC`, `NASLOT`, one dummy word per node, the counts at
`CTL[34 + t]`. -/
def nanonSch : Schema := ⟨NAREC, NASLOT, 1, 34, NTag.anonymous⟩

theorem nanonSch_wf : nanonSch.WF :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

/-- Node `i` of tier `t` holds the `anonymous` node: trivially (there is only one `AnonNode`). -/
def NaRecRel (_m : Mem) (_t _i : Word) (_k : AnonNode) : Prop := True

/-- **The state relation** of the `anonymous` store: the library's relation for the name store's
two `anonymous` tables. -/
def NAnonR (m : Mem) (a : AState) : Prop :=
  ConsR nanonCS NaRecRel m a.store.lss.ls.ns.scratchOn a.store.lss.ls.ns.pers.anons
    a.store.lss.ls.ns.scr.anons

/-- A node's relation and hash depend on nothing. -/
theorem naFrame : RFrame nanonSch NaRecRel nahash := by
  intro m m' t i _ _
  exact ⟨fun _ _ => trivial, rfl⟩

/-! ## The query's obligations -/

/-- The match of `nanon_find` on node `i` of tier `t`: always. -/
def naMt (m : Mem) (t i : Word) : Bool := namatchW (m.arr64 (tierA NAREC t)) t i

/-- **Matching is equality of `anonymous` nodes**: both sides are always true. -/
theorem naMatchOK (m : Mem) : MatchOK NaRecRel (naMt m) m naKey := by
  intro t i k _
  simp only [naMt, namatchW, naNode_eq k]

theorem naHomeOK (m : Mem) : HomeOK nahash (naMt m) m nahashW := by
  intro t i _; rfl

/-- The record `nanon_push` writes holds the node (trivially). -/
theorem naNewOK (m : Mem) : NewOKR nanonSch NaRecRel nahash m [0] naKey nahashW := by
  intro t _ _ _
  exact ⟨trivial, rfl⟩

/-! ## The bridges from the L models -/

theorem napushOK_room (m : Mem) (t : Word) (h : napushOK m t = true) : PushRoom nanonSch m t := by
  simp only [napushOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have := UInt64.toNat_shiftRight (m.len64 (tierA NAREC t)) 0
  simp only [PushRoom, cntW, nacnt, nanonSch, len64_eq] at *
  grind

/-- **The `nanon` table's shape.** -/
theorem nanonCS_wf : nanonCS.WF where
  sch := nanonSch_wf
  P := by decide
  S := by decide
  col A h := by simp [nanonCS] at h
  colRoom A h := by simp [nanonCS] at h
  colLt A h := by
    simp only [nanonCS, reduceCtorEq] at h; (try subst h); (try decide)
  room m t h := (napushOK_room m t ((napushOK_eqC m t).trans h)).2
  vs ks h hk := by simp [pushArgs, nanonCS]
  ex _ := {
    nk := by decide
    nkw := by decide
    kpk := fun h => absurd h (by decide)
    mt := by
      intro m ks h t i hl
      obtain rfl := list_zero ks (by simpa [nanonCS] using hl)
      simp [nanonCS, namatchW, fieldsL]
    hs := by intro m t i; simp [nanonCS, namatchW, nahash, fieldsL]
    qh := fun _ _ _ => rfl
    vs := by intro ks h hl f hf; simp [nanonCS, nkW] at hf }

/-! ## `intern_nanon` refines `internNNode .anonymous` -/

section intern
variable (m : Mem) (a : AState) (hR : NAnonR m a)

include hR in
/-- **`intern_nanon`'s model refines the arena's `internNNode` at the `anonymous` node.** -/
theorem naintern_correct (w : Word) (m' : Mem) (hI : nainternW m = some (w, m')) :
    AM.ok (internNNode .anonymous) a ∧
    NAnonR m' (AM.st (internNNode .anonymous) a) ∧
    AM.res (internNNode .anonymous) a = decI w :=
  consIntern_correct nanonCS_wf naFrame (colFree_none _ rfl) nanonLens a hR _ _ _ _ _
    (internNNode_anon_run a) false rfl [] (by simp [show skipC nanonCS m [] = 0 from rfl])
    (by simp) ⟨rfl, naMatchOK m, naHomeOK m, naNewOK m⟩ w m' hI

end intern

end L.Arena
