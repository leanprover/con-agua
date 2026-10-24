import ConAgua.Arena.StoreLib
import ConAgua.Arena.SimLib
import ConAgua.Arena.BVarStore

/-!
# The `bvar` store refines the arena's `bvar` tables

The record `BVarNode { i : Nat }` (`ConAgua/Arena/BVarStore.lean` has the L code), the first
table whose field is a `Nat`, not a handle. The schema `bvarSch` (`BREC`, `BSLOT`, one word per
node, counts at `CTL[22 + t]`, tag `0`), the record relation `BRecRel` (the word is the index,
which is below `2^64`), the node hash `bhash`, the lens `bvarLens`. A `bvar` has no child, so the
persistent probe is never skipped (`skB = false`, as for the level store). `BVarR m a` is the
library's `StoreR` for the two `bvar` tables. `internBVar_refines`: `intern_bvar(u)` refines
`internE (.bvar u.toNat)` under `BVarR`.

Not represented: the derived column and every other table.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

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
def bvarSch : Schema := ⟨BREC, BSLOT, 1, 2, 22, ETag.bvar⟩

theorem bvarSch_wf : bvarSch.WF :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem fld_bvar0 (m : Mem) (t i : Word) : fld bvarSch m t i 0 = rdW (m.arr64 BREC) (i * 2 + t) := by
  simp [fld, Schema.ad, bvarSch]

/-- Node `i` of tier `t` holds `bvar k.i`: its word is the index, which fits in a word. -/
def BRecRel (m : Mem) (t i : Word) (k : BVarNode) : Prop :=
  (rdW (m.arr64 BREC) (i * 2 + t)).toNat = k.i

/-- **The state relation** of the `bvar` store: the library's relation for the two `bvar`
tables. -/
def BVarR (m : Mem) (a : AState) : Prop :=
  StoreR bvarSch BRecRel bhash m a.store.scratchOn a.store.pers.bvars a.store.scr.bvars

/-- A node's relation and hash depend only on its word. -/
theorem bvarFrame : RFrame bvarSch BRecRel bhash := by
  intro m m' t i _ hf
  have h0 := hf 0 (by decide)
  rw [fld_bvar0, fld_bvar0] at h0
  exact ⟨fun a h => by simpa only [BRecRel, h0] using h, by simp only [bhash, h0]⟩

/-! ## The query's obligations -/

/-- The match of `bvar_find` on node `i` of tier `t`. -/
def bMt (m : Mem) (u t i : Word) : Bool := bmatchW (m.arr64 BREC) t i u

section query
variable (m : Mem) (u : Word)

/-- **Matching is equality of `bvar` nodes** (both indices are words). -/
theorem bvarMatchOK : MatchOK BRecRel (bMt m u) m (bvarKey u.toNat) := by
  intro t i k hr
  obtain ⟨ki⟩ := k
  simp only [BRecRel] at hr
  simp only [bMt, bmatchW, beq_iff_eq, bvarKey, BVarNode.mk.injEq, ← hr]
  exact ⟨fun h => by rw [h], fun h => UInt64.toNat_inj.mp h⟩

theorem bvarHomeOK : HomeOK bhash (bMt m u) m (bvarHashW u) := by
  intro t i hm
  simp only [bMt, bmatchW, beq_iff_eq] at hm
  simp only [bhash, hm]

/-- The record `bvar_push` writes holds the node. -/
theorem bvarNewOK : NewOK bvarSch BRecRel bhash m [u] (bvarKey u.toNat) (bvarHashW u) := by
  intro t j ht hroom
  have e : fld bvarSch (pushG bvarSch m t [u] j (cntW bvarSch m t)) t (cntW bvarSch m t) 0 = u := by
    have := hroom.1
    have := hroom.2
    rw [fld_pushG bvarSch bvarSch_wf] <;> simp only [bvarSch, Schema.ad] at * <;> grind
  rw [fld_bvar0] at e
  simp only [BRecRel, bhash, bvarKey, e]
  exact ⟨trivial, trivial⟩

end query

/-! ## The bridges from the L models -/

theorem bprobeW_arm (m : Mem) (u t : Word) :
    ∀ j d, bprobeW (m.arr64 BSLOT) (m.arr64 BREC) t u (baseW m t) (nSlotsB m) j d =
      probeArm bvarSch m t (bMt m u t) (bprobeW (m.arr64 BSLOT) (m.arr64 BREC) t u (baseW m t) (nSlotsB m)) j d := by
  intro j d; rw [bprobeW, cprobeW]; rfl

theorem bpushOK_room (m : Mem) (t : Word) (h : bpushOK m t = true) : PushRoom bvarSch m t := by
  simp only [bpushOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have := UInt64.toNat_shiftRight (m.len64 BREC) 1
  simp only [PushRoom, cntW, bcnt, bvarSch, len64_eq] at *
  grind

theorem bpushMem_eq (m : Mem) (t u j c : Word) :
    bpushMem m t u j c = pushG bvarSch m t [u] j c := by
  simp [bpushMem, pushG, wrRec, Schema.ad, bvarSch]

theorem binternW_eq (m : Mem) (u : Word) :
    binternW m u = internM bvarSch m 0 (bpushOK m) [u]
      (bprobeW (m.arr64 BSLOT) (m.arr64 BREC) 0 u (baseW m 0) (nSlotsB m) (homeW (bvarHashW u) (nSlotsB m)) 0)
      (bprobeW (m.arr64 BSLOT) (m.arr64 BREC) 1 u (baseW m 1) (nSlotsB m) (homeW (bvarHashW u) (nSlotsB m)) 0)
      bhash := by
  have e0 : ∀ x, hdW bvarSch.tag.toUInt64 0 x = bvarP + x := fun x => by
    simp [hdW, bvarSch, bvarP, ETag.bvar]
  have e1 : ∀ x, hdW bvarSch.tag.toUInt64 1 x = bvarS + x := fun x => by
    simp [hdW, bvarSch, bvarS, ETag.bvar]
  have ep : ∀ t, pushOKC bvarCS m t = bpushOK m t := fun t => (bpushOK_eqC m t).symm
  have em : ∀ t j c, pushMC bvarCS m t (bvarCS.vsM (pushArgs bvarCS [u] (bvarHashW u))) j c =
      pushG bvarSch m t [u] j c := by
    intro t j c; rw [← bpushMem_eq, bpushMem_eqC]; rfl
  have ec : ∀ t, cntC bvarCS m t = cntW bvarSch m t := fun t => rfl
  have eh : bvarCS.qhM m [u] = bvarHashW u := rfl
  have es : skipC bvarCS m [u] = 0 := rfl
  simp only [binternW, consInternM, internM, pushM, pushC, pushMX_none (C := bvarCS) rfl,
    ep, em, ec, e0, e1, eh, es, true_and]
  rfl

/-! ## `intern_bvar` refines `internE (.bvar _)` -/

section intern
variable (m : Mem) (a : AState) (hR : BVarR m a) (u : Word)

include hR in
/-- **`intern_bvar`'s model refines the arena's `internE` at a `bvar` node.** -/
theorem bintern_correct (w : Word) (m' : Mem) (hI : binternW m u = some (w, m')) :
    AM.ok (internE (.bvar u.toNat)) a ∧
    BVarR m' (AM.st (internE (.bvar u.toNat)) a) ∧
    AM.res (internE (.bvar u.toNat)) a = decE w := by
  rw [binternW_eq] at hI
  exact intern_correctG bvarSch BRecRel bhash bvarSch_wf bvarFrame bvarLens a m hR _ _ _ _ _
    (internE_bvar_run _ a) false rfl 0 (by simp) (by simp) _ _ (bvarMatchOK m u)
    (bvarHomeOK m u) _ _ (probe_homeG bvarSch m 0 _ _ (bprobeW_arm m u 0) _)
    (probe_homeG bvarSch m 1 _ _ (bprobeW_arm m u 1) _) _ (bpushOK_room m) _ rfl
    (bvarNewOK m u) w m' hI

end intern

/-- `intern_bvar` refines `internE (.bvar _)` under `BVarR`. -/
theorem internBVar_refines (p : Prog) (hpf : p.lookup "bvar_find" = some bvarFind)
    (hpp : p.lookup "bvar_push" = some bvarPush) (hp : p.lookup "intern_bvar" = some internBVar)
    (a₀ : AState) (n : Nat) (s₀ : St) (u : Word) (hR : BVarR s₀.mem a₀) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_bvar" [u]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internE (.bvar u.toNat)) a₀ ∧
      BVarR s'.mem (AM.st (internE (.bvar u.toNat)) a₀) ∧
      AM.res (internE (.bvar u.toNat)) a₀ = decE (r.headD 0); ⊤⦄ :=
  Sim.tripleD (internBVar_spec p hpf hpp hp n s₀ u)
    (Sim.ofOkD (bintern_correct s₀.mem a₀ hR u))

end L.Arena
