import ConAgua.Arena.ConsLibRel
import ConAgua.Arena.SimLib
import ConAgua.Arena.AppStore

/-!
# The `app` store refines the arena's `app` tables

The second store relation, an instance of the store library (`StoreLib.lean`) for the record
`AppNode { f a : EIdx }` (`ConAgua/Arena/AppStore.lean` has the L code). The schema `appSch`
(`AREC`, `ASLOT`, two words per node, counts at `CTL[4 + t]`, tag `4`); the record relation
`ARecRel` (the two words are the children's handle words); the node hash `ahash` (`appHashW` of
the two words); the lens `appLens`; the scratch skip (`skA`, `askipW_eq`). `AppR m a` is the
library's `ConsR` for the two `app` tables. `internApp_refines`: `intern_app(f, a)` refines
`internE (.app (decE f) (decE a))` under `AppR`.

Not represented: the derived column (`derOfApp`, through `mixHash`) and every other table.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

/-- The arena's `app` cons key. -/
abbrev appKey (f a : EIdx) : AppNode := ⟨f, a⟩

/-- `a` with the scratch / persistent `app` table replaced. -/
def withScrApps (a : AState) (t : Tbl AppNode EIdx UInt64) : AState :=
  { a with store := { a.store with scr := { a.store.scr with apps := t } } }
def withPersApps (a : AState) (t : Tbl AppNode EIdx UInt64) : AState :=
  { a with store := { a.store with pers := { a.store.pers with apps := t } } }

/-- The arena's two `app` tables. -/
def appLens : Lens AppNode UInt64 .expr where
  on a := a.store.scratchOn
  getP a := a.store.pers.apps
  getS a := a.store.scr.apps
  setP := withPersApps
  setS := withScrApps
  on_setP _ _ := rfl
  on_setS _ _ := rfl
  getP_setP _ _ := rfl
  getS_setP _ _ := rfl
  getP_setS _ _ := rfl
  getS_setS _ _ := rfl

/-- The arena's scratch skip at an `app` view (`EStore.persFindMaybe`). -/
def skA (a : AState) (f x : EIdx) : Bool :=
  if a.store.scratchOn then (if f.isPersistent then !x.isPersistent else true) else false

/-- The arena's persistent probe at an `app` view, after the skip. -/
def pfA (a : AState) (f x : EIdx) : Option EIdx :=
  if skA a f x then none else a.store.pers.apps.cons[appKey f x]?

theorem persFindMaybe_app (a : AState) (f x : EIdx) :
    a.store.persFindMaybe (.app f x) = pfA a f x := by
  simp [EStore.persFindMaybe, pfA, skA, EStore.eViewHasScratchChild, ETables.find?, Tbl.find?]

/-- `internE` at an `app` node is the library's protocol, the persistent probe after the skip. -/
theorem internE_app_run (f x : EIdx) (a : AState) :
    (internE (.app f x)).run a =
      protoRun appLens (appKey f x) ETag.app (pfA a f x) (a.store.derOfView (.app f x))
        (.native "arena: expression constructor array full") a := by
  simp only [internE, internNodeE, EStore.find?, EStore.intern, ETables.find?, Tbl.find?,
    ETables.sizeOf, ETables.push, StateT.run_bind, StateT.run_get, pure_bind, persFindMaybe_app]
  cases hp : pfA a f x <;> cases hs : a.store.scratchOn <;>
    cases hc : a.store.scr.apps.cons[appKey f x]? <;>
    simp only [hp, hs, hc, Bool.false_eq_true, ↓reduceIte, appKey, ite_self, protoRun, appLens] <;>
    (try split) <;> simp_all [StateT.run_set, StateT.run_pure, withScrApps, withPersApps, fail,
      throwThe, MonadExceptOf.throw, StateT.run, Functor.map, StateT.map, set, StateT.set,
      StateT.lift, bind, Except.bind, Except.map, pure, Except.pure, StateT.bind, StateT.pure]

/-! ## The relation between L memory and the arena's `app` tables -/

/-- The `app` schema: `AREC`, `ASLOT`, two words per node, the counts at `CTL[4 + t]`. -/
def appSch : Schema := ⟨AREC, ASLOT, 2, 4, 4, ETag.app⟩

theorem appSch_wf : appSch.WF :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem fld_app0 (m : Mem) (t i : Word) : fld appSch m t i 0 = rdW (m.arr64 AREC) (i * 4 + t * 2) := by
  simp [fld, Schema.ad, appSch]
theorem fld_app (m : Mem) (t i f : Word) :
    fld appSch m t i f = rdW (m.arr64 AREC) (i * 4 + t * 2 + f) := rfl

/-- Node `i` of tier `t` holds the `app` node `k`: its two handle words. -/
def ARecRel (m : Mem) (t i : Word) (k : AppNode) : Prop :=
  tfld m APP t i 0 = k.f.word.toUInt64 ∧
  tfld m APP t i 1 = k.a.word.toUInt64

/-- `ARecRel` in the raw words (inside the store library). -/
theorem ARecRel_raw (m : Mem) (t i : Word) (k : AppNode) :
    ARecRel m t i k ↔
    rdW (m.arr64 AREC) (i * 4 + t * 2) = k.f.word.toUInt64 ∧
    rdW (m.arr64 AREC) (i * 4 + t * 2 + 1) = k.a.word.toUInt64 := by sorry

/-- **The state relation** of the `app` store: the library's relation for the two `app` tables. -/
def AppR (m : Mem) (a : AState) : Prop :=
  ConsR appCS ARecRel m a.store.scratchOn a.store.pers.apps a.store.scr.apps

/-- A node's relation and hash depend only on its two words. -/
theorem appFrame : RFrame appSch ARecRel ahash := by
  intro m m' t i _ hf
  have h0 := hf 0 (by decide)
  have h1 := hf 1 (by decide)
  rw [fld_app0, fld_app0] at h0
  rw [fld_app, fld_app] at h1
  exact ⟨fun a h => by simpa only [ARecRel_raw, h0, h1] using h, by simp only [ahash, h0, h1]⟩

/-! ## The query's obligations -/

/-- The match of `app_find` on node `i` of tier `t`. -/
def aMt (m : Mem) (f a t i : Word) : Bool := amatchW (m.arr64 AREC) t i f a

section query
variable (m : Mem) (f a : Word) (hf : f.toNat < 2 ^ 32) (ha : a.toNat < 2 ^ 32)

include hf ha in
/-- **Matching is equality of `app` nodes.** -/
theorem appMatchOK : MatchOK ARecRel (aMt m f a) m (appKey (decE f) (decE a)) := by
  intro t i k hr
  have := word_decI k.f f hf
  have := word_decI k.a a ha
  obtain ⟨kf, ka⟩ := k
  grind [aMt, amatchW, ARecRel_raw, decE_eq]

theorem appHomeOK : HomeOK ahash (aMt m f a) m (appHashW f a) := by
  intro t i hm
  simp only [aMt, amatchW, Bool.and_eq_true, beq_iff_eq] at hm
  simp only [ahash, hm.1, hm.2]

include hf ha in
/-- The record `app_push` writes holds the node. -/
theorem appNewOK : NewOKR appSch ARecRel ahash m [f, a] (appKey (decE f) (decE a)) (appHashW f a) := by
  intro t ht hroom
  have e : ∀ g, g < 2 → fld appSch (newRecM appSch m t [f, a]) t
      (cntW appSch m t) g = [f, a].getD g.toNat 0 := by
    intro g hg
    have := hroom.1
    have := hroom.2
    rw [fld_newRecM appSch appSch_wf] <;> simp only [appSch, Schema.ad] at * <;> grind
  have e0 := e 0 (by decide)
  have e1 := e 1 (by decide)
  rw [fld_app0] at e0
  rw [fld_app] at e1
  simp only [List.getD_cons_zero, List.getD_cons_succ, show (1 : Word).toNat = 0 + 1 from rfl,
    show (0 : Word).toNat = 0 from rfl] at e0 e1
  have := word_decI (decE f) f hf
  have := word_decI (decE a) a ha
  simp only [ARecRel_raw, ahash, appKey, e0, e1]
  grind [decE_eq]

end query

/-! ## The bridges from the L models -/

theorem apushOK_room (m : Mem) (t : Word) (h : apushOK m t = true) : PushRoom appSch m t := by
  simp only [apushOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have := UInt64.toNat_shiftRight (m.len64 AREC) 2
  simp only [PushRoom, cntW, acnt, appSch, len64_eq] at *
  grind

/-- **The `app` table's shape.** -/
theorem appCS_wf : appCS.WF where
  sch := appSch_wf
  P := by decide
  S := by decide
  col A h := by simp [appCS] at h
  colRoom A h := by simp [appCS] at h
  room m t h := (apushOK_room m t ((apushOK_eqC m t).trans h)).2
  vs ks h hk := by simp [pushArgs, appCS, hk]
  ex _ := {
    nk := by decide
    nkw := by decide
    mt := by
      intro m ks h t i hl
      obtain ⟨a, b, rfl⟩ := list_two ks (by simpa [appCS] using hl)
      simp [appCS, amatchW, ahash, fieldsL, fld, Schema.ad, ConsSch.sch, List.range_succ, show UInt64.ofNat 0 = 0 from rfl, show UInt64.ofNat 1 = 1 from rfl]
    hs := by intro m t i; simp [appCS, amatchW, ahash, fieldsL, fld, Schema.ad, ConsSch.sch, List.range_succ, show UInt64.ofNat 0 = 0 from rfl, show UInt64.ofNat 1 = 1 from rfl]
    qh := fun _ _ _ => rfl
    vs := by intro ks h hl f hf; simp [pushArgs, appCS] at hf ⊢ <;> omega }

/-- The L skip test is the arena's. -/
theorem askipW_eq (m : Mem) (a : AState) (f x : Word) (hf : f.toNat < 2 ^ 32)
    (hx : x.toNat < 2 ^ 32) (hfl : (rdW (m.arr64 CTL) 1 != 0) = a.store.scratchOn) :
    (askipW m f x = 0) = (skA a (decE f) (decE x) = false) := by
  have := bit27_or f x
  simp only [askipW, skA, isPersistent_decE f hf, isPersistent_decE x hx, ← hfl]
  grind

/-! ## `intern_app` refines `internE (.app _ _)` -/

section intern
variable (m : Mem) (a : AState) (hR : AppR m a) (f x : Word) (hf : f.toNat < 2 ^ 32)
  (hx : x.toNat < 2 ^ 32)

include hR hf hx in
/-- **`intern_app`'s model refines the arena's `internE` at an `app` node.** -/
theorem aintern_correct (w : Word) (m' : Mem) (hI : ainternW m f x = some (w, m')) :
    AM.ok (internE (.app (decE f) (decE x))) a ∧
    AppR m' (AM.st (internE (.app (decE f) (decE x))) a) ∧
    AM.res (internE (.app (decE f) (decE x))) a = decE w :=
  consIntern_correct appCS_wf appFrame (colFree_none _ rfl) appLens a hR _ _ _ _ _
    (internE_app_run _ _ a) (skA a (decE f) (decE x)) rfl [f, x]
    (askipW_eq m a f x hf hx (ConsR.flag hR))
    (fun h => by simp only [skA] at h; split at h <;> simp_all [appLens])
    ⟨rfl, appMatchOK m f x hf hx, appHomeOK m f x, appNewOK m f x hf hx⟩ w m' hI

end intern

end L.Arena
