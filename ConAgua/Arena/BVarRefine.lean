import ConAgua.Arena.ConsLibRel
import ConAgua.Arena.SimLib
import ConAgua.Arena.BVarStore

/-!
# The `bvar` store refines the arena's `bvar` tables

The record `BVarNode { i : Nat }` (`ConAgua/Arena/BVarStore.lean` has the L code), the first
table whose field is a `Nat`, not a handle. The schema `bvarSch` (`BREC`, `BSLOT`, one word per
node, counts at `CTL[22 + t]`, tag `0`), the record relation `BRecRel` (the word is the index,
which is below `2^64`), the node hash `bhash`, the lens `bvarLens`. A `bvar` has no child, so the
persistent probe is never skipped (`skB = false`, as for the level store). `BVarR m a` is the
library's `ConsR` for the two `bvar` tables. `internBVar_refines`: `intern_bvar(u)` refines
`internE (.bvar u.toNat)` under `BVarR`.

Not represented: the derived column and every other table.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

/-- The arena's `bvar` cons key. -/
abbrev bvarKey (i : Nat) : BVarNode := ⟨i⟩

/-- `a` with the scratch / persistent `bvar` table replaced. -/
def withScrBVars (a : AState) (t : Tbl BVarNode EIdx UInt64) : AState :=
  { a with store := { a.store with scr := { a.store.scr with bvars := t } } }
def withPersBVars (a : AState) (t : Tbl BVarNode EIdx UInt64) : AState :=
  { a with store := { a.store with pers := { a.store.pers with bvars := t } } }

/-- The arena's two `bvar` tables. -/
def bvarLens : Lens BVarNode UInt64 .expr where
  on a := a.store.scratchOn
  getP a := a.store.pers.bvars
  getS a := a.store.scr.bvars
  setP := withPersBVars
  setS := withScrBVars
  on_setP _ _ := rfl
  on_setS _ _ := rfl
  getP_setP _ _ := rfl
  getS_setP _ _ := rfl
  getP_setS _ _ := rfl
  getS_setS _ _ := rfl

theorem persFindMaybe_bvar (a : AState) (i : Nat) :
    a.store.persFindMaybe (.bvar i) = a.store.pers.bvars.cons[bvarKey i]? := by
  simp [EStore.persFindMaybe, EStore.eViewHasScratchChild, ETables.find?, Tbl.find?]

/-- `internE` at a `bvar` node is the library's protocol, with no skip. -/
theorem internE_bvar_run (i : Nat) (a : AState) :
    (internE (.bvar i)).run a =
      protoRun bvarLens (bvarKey i) ETag.bvar a.store.pers.bvars.cons[bvarKey i]?
        (a.store.derOfView (.bvar i)) (.native "arena: expression constructor array full") a := by
  simp only [internE, internNodeE, EStore.find?, EStore.intern, ETables.find?, Tbl.find?,
    ETables.sizeOf, ETables.push, StateT.run_bind, StateT.run_get, pure_bind, persFindMaybe_bvar]
  cases hp : a.store.pers.bvars.cons[bvarKey i]? <;> cases hs : a.store.scratchOn <;>
    cases hc : a.store.scr.bvars.cons[bvarKey i]? <;>
    simp only [hp, hs, hc, Bool.false_eq_true, ↓reduceIte, bvarKey, ite_self, protoRun, bvarLens] <;>
    (try split) <;> simp_all [StateT.run_set, StateT.run_pure, withScrBVars, withPersBVars, fail,
      throwThe, MonadExceptOf.throw, StateT.run, Functor.map, StateT.map, set, StateT.set,
      StateT.lift, bind, Except.bind, Except.map, pure, Except.pure, StateT.bind, StateT.pure]

/-! ## The relation between L memory and the arena's `bvar` tables -/

/-- The `bvar` schema: `BREC`, `BSLOT`, one word per node, the counts at `CTL[22 + t]`. -/
def bvarSch : Schema := ⟨BREC, BSLOT, 1, 22, ETag.bvar⟩

theorem bvarSch_wf : bvarSch.WF :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

theorem fld_bvar0 (m : Mem) (t i : Word) : fld bvarSch m t i 0 = rdW (m.arr64 (tierA BREC t)) i := by
  simp [fld, Schema.ad, bvarSch]

/-- Node `i` of tier `t` holds `bvar k.i`: its word is the index, which fits in a word. -/
def BRecRel (m : Mem) (t i : Word) (k : BVarNode) : Prop :=
  (tfld m BVAR t i 0).toNat = k.i

/-- `BRecRel` in the raw words (inside the store library). -/
theorem BRecRel_raw (m : Mem) (t i : Word) (k : BVarNode) :
    BRecRel m t i k ↔
    (rdW (m.arr64 (tierA BREC t)) i).toNat = k.i
  := Iff.rfl

/-- **The state relation** of the `bvar` store: the library's relation for the two `bvar`
tables. -/
def BVarR (m : Mem) (a : AState) : Prop :=
  ConsR bvarCS BRecRel m a.store.scratchOn a.store.pers.bvars a.store.scr.bvars

/-- A node's relation and hash depend only on its word. -/
theorem bvarFrame : RFrame bvarSch BRecRel bhash := by
  intro m m' t i _ hf
  have h0 := hf 0 (by decide)
  rw [fld_bvar0, fld_bvar0] at h0
  exact ⟨fun a h => by simpa only [BRecRel_raw, h0] using h, by simp only [bhash, h0]⟩

/-! ## The query's obligations -/

/-- The match of `bvar_find` on node `i` of tier `t`. -/
def bMt (m : Mem) (u t i : Word) : Bool := bmatchW (m.arr64 (tierA BREC t)) t i u

section query
variable (m : Mem) (u : Word)

/-- **Matching is equality of `bvar` nodes** (both indices are words). -/
theorem bvarMatchOK : MatchOK BRecRel (bMt m u) m (bvarKey u.toNat) := by
  intro t i k hr
  obtain ⟨ki⟩ := k
  simp only [BRecRel_raw] at hr
  simp only [bMt, bmatchW, beq_iff_eq, bvarKey, BVarNode.mk.injEq, ← hr]
  exact ⟨fun h => by rw [h], fun h => UInt64.toNat_inj.mp h⟩

theorem bvarHomeOK : HomeOK bhash (bMt m u) m (bvarHashW u) := by
  intro t i hm
  simp only [bMt, bmatchW, beq_iff_eq] at hm
  simp only [bhash, hm]

/-- The record `bvar_push` writes holds the node. -/
theorem bvarNewOK : NewOKR bvarSch BRecRel bhash m [u] (bvarKey u.toNat) (bvarHashW u) := by
  intro t ht hroom _
  have e : fld bvarSch (newRecM bvarSch m t [u]) t (cntW bvarSch m t) 0 = u := by
    have := hroom.1
    have := hroom.2
    rw [fld_newRecM bvarSch bvarSch_wf] <;> simp only [bvarSch, Schema.ad] at * <;> grind
  rw [fld_bvar0] at e
  simp only [BRecRel_raw, bhash, bvarKey, e]
  exact ⟨trivial, trivial⟩

end query

/-! ## The bridges from the L models -/

theorem bpushOK_room (m : Mem) (t : Word) (h : bpushOK m t = true) : PushRoom bvarSch m t := by
  simp only [bpushOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have := UInt64.toNat_shiftRight (m.len64 (tierA BREC t)) 0
  simp only [PushRoom, cntW, bcnt, bvarSch, len64_eq] at *
  grind

/-- **The `bvar` table's shape.** -/
theorem bvarCS_wf : bvarCS.WF where
  sch := bvarSch_wf
  P := by decide
  S := by decide
  col A h := by simp [bvarCS] at h
  colRoom A h := by simp [bvarCS] at h
  colLt A h := by
    simp only [bvarCS, reduceCtorEq, Option.some.injEq] at h; (try subst h); (try decide)
  room m t h := (bpushOK_room m t ((bpushOK_eqC m t).trans h)).2
  vs ks h hk := by simp [pushArgs, bvarCS, hk]
  ex _ := {
    nk := by decide
    nkw := by decide
    kpk := fun h => absurd h (by decide)
    mt := by
      intro m ks h t i hl
      obtain ⟨a, rfl⟩ := list_one ks (by simpa [bvarCS] using hl)
      simp [bvarCS, bmatchW, bhash, fieldsL, kfld, fld, Schema.ad, ConsSch.sch, List.range_succ, show UInt64.ofNat 0 = 0 from rfl, show UInt64.ofNat 1 = 1 from rfl]
    hs := by intro m t i; simp [bvarCS, bmatchW, bhash, fieldsL, kfld, fld, Schema.ad, ConsSch.sch, List.range_succ, show UInt64.ofNat 0 = 0 from rfl, show UInt64.ofNat 1 = 1 from rfl]
    qh := fun _ _ _ => rfl
    vs := by intro ks h hl f hf; simp [pushArgs, bvarCS, nkW, recK] at hf ⊢ <;> omega }

/-! ## `intern_bvar` refines `internE (.bvar _)` -/

section intern
variable (m : Mem) (a : AState) (hR : BVarR m a) (u : Word)

include hR in
/-- **`intern_bvar`'s model refines the arena's `internE` at a `bvar` node.** -/
theorem bintern_correct (w : Word) (m' : Mem) (hI : binternW m u = some (w, m')) :
    AM.ok (internE (.bvar u.toNat)) a ∧
    BVarR m' (AM.st (internE (.bvar u.toNat)) a) ∧
    AM.res (internE (.bvar u.toNat)) a = decE w :=
  consIntern_correct bvarCS_wf bvarFrame (colFree_none _ rfl) bvarLens a hR _ _ _ _ _
    (internE_bvar_run _ a) false rfl [u] (by simp [show skipC bvarCS m [u] = 0 from rfl])
    (by simp) ⟨rfl, bvarMatchOK m u, bvarHomeOK m u, bvarNewOK m u⟩ w m' hI

end intern

end L.Arena
