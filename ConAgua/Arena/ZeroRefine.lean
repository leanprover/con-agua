import ConAgua.Arena.StoreLib
import ConAgua.Arena.SimLib
import ConAgua.Arena.ZeroStore
import ConAgua.Arena.LpColRel

/-!
# The level `zero` store refines the arena's `zero` tables

The fourth table on the store library, the fieldless case: the record `ZeroNode` (no fields) of
the level store (`ConAgua/Arena/ZeroStore.lean` has the L code). The schema `zeroSch` (`ZREC`,
`ZSLOT`, one dummy word per node, counts at `CTL[8 + t]`, tag `0`), the record relation `ZRecRel`
(trivially `True`: there is only one possible `ZeroNode`), the node hash `zhash` (the constant
`zeroHashW`), the lens `zeroLens` on the level store's two `zero` tables
(`a.store.lss.ls.pers.zeros`/`scr.zeros`). `ZeroR m a` is the library's `StoreR` for them.
`internZero_refines`: `intern_zero()` refines `internLNode .zero` under `ZeroR`.

Not represented: the derived column and every other table.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

/-- The arena's `zero` cons key: the only value of `ZeroNode`. -/
abbrev zeroKey : ZeroNode := .mk

theorem zeroNode_eq (a : ZeroNode) : a = zeroKey := by cases a; rfl

/-- `a` with the scratch / persistent `zero` table of the level store replaced. -/
def withScrZeros (a : AState) (t : Tbl ZeroNode LIdx LDer) : AState :=
  { a with store := { a.store with lss := { a.store.lss with ls := { a.store.lss.ls with
      scr := { a.store.lss.ls.scr with zeros := t } } } } }
def withPersZeros (a : AState) (t : Tbl ZeroNode LIdx LDer) : AState :=
  { a with store := { a.store with lss := { a.store.lss with ls := { a.store.lss.ls with
      pers := { a.store.lss.ls.pers with zeros := t } } } } }

/-- The level store's two `zero` tables. -/
def zeroLens : Lens ZeroNode LDer .level where
  on a := a.store.lss.ls.scratchOn
  getP a := a.store.lss.ls.pers.zeros
  getS a := a.store.lss.ls.scr.zeros
  setP := withPersZeros
  setS := withScrZeros
  on_setP _ _ := rfl
  on_setS _ _ := rfl
  getP_setP _ _ := rfl
  getS_setP _ _ := rfl
  getP_setS _ _ := rfl
  getS_setS _ _ := rfl

/-- `internLNode` at a `zero` node is the library's protocol, with no skip. -/
theorem internLNode_zero_run (a : AState) :
    (internLNode .zero).run a =
      protoRun zeroLens zeroKey LTag.zero a.store.lss.ls.pers.zeros.cons[zeroKey]?
        (a.store.lss.ls.derOfView .zero) (.native "arena: level constructor array full") a := by
  simp only [internLNode, LStore.find?, LTables.find?, Tbl.find?, LTables.sizeOf, EStore.ls,
    EStore.internLevel, LsStore.internLevel, LStore.intern, LTables.push]
  cases hp : a.store.lss.ls.pers.zeros.cons[zeroKey]? <;> cases hs : a.store.lss.ls.scratchOn <;>
    cases hc : a.store.lss.ls.scr.zeros.cons[zeroKey]? <;>
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hp, hs, hc, Bool.false_eq_true,
      ↓reduceIte, zeroKey, ite_self, protoRun, zeroLens] <;>
    (try split) <;> simp_all [StateT.run_set, StateT.run_pure, withScrZeros, withPersZeros, fail,
      throwThe, MonadExceptOf.throw, StateT.run, Functor.map, StateT.map, set, StateT.set,
      StateT.lift, bind, Except.bind, Except.map, pure, Except.pure, StateT.bind, StateT.pure]

/-! ## The relation between L memory and the arena's `zero` tables -/

/-- The `zero` schema: `ZREC`, `ZSLOT`, one dummy word per node, the counts at `CTL[8 + t]`. -/
def zeroSch : Schema := ⟨ZREC, ZSLOT, 1, 2, 8, LTag.zero⟩

theorem zeroSch_wf : zeroSch.WF :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Node `i` of tier `t` holds the `zero` node: trivially (there is only one `ZeroNode`). -/
def ZRecRel (_m : Mem) (_t _i : Word) (_k : ZeroNode) : Prop := True

/-- The (constant) hash of node `i` of tier `t`. -/
def zhash (_m : Mem) (_t _i : Word) : Word := zeroHashW

/-- **The state relation** of the `zero` store: the library's relation for the level store's two
`zero` tables. -/
def ZeroR (m : Mem) (a : AState) : Prop :=
  StoreR zeroSch ZRecRel zhash m a.store.lss.ls.scratchOn a.store.lss.ls.pers.zeros
    a.store.lss.ls.scr.zeros

/-- A node's relation and hash depend on nothing. -/
theorem zeroFrame : RFrame zeroSch ZRecRel zhash := by
  intro m m' t i _ _
  exact ⟨fun _ _ => trivial, rfl⟩

/-! ## The query's obligations -/

/-- The match of `zero_find` on node `i` of tier `t`: always. -/
def zMt (m : Mem) (t i : Word) : Bool := zmatchW (m.arr64 ZREC) t i

/-- **Matching is equality of `zero` nodes**: both sides are always true. -/
theorem zeroMatchOK (m : Mem) : MatchOK ZRecRel (zMt m) m zeroKey := by
  intro t i k _
  simp only [zMt, zmatchW, eq_iff_iff, iff_true, zeroNode_eq k]

theorem zeroHomeOK (m : Mem) : HomeOK zhash (zMt m) m zeroHashW := by
  intro t i _; rfl

/-- The record `zero_push` writes holds the node (trivially). -/
theorem zeroNewOK (m : Mem) : NewOK zeroSch ZRecRel zhash m [0] zeroKey zeroHashW := by
  intro t j _ _
  exact ⟨trivial, rfl⟩

/-! ## The bridges from the L models -/

theorem zprobeW_arm (m : Mem) (t : Word) :
    ∀ j d, zprobeW (m.arr64 ZSLOT) (m.arr64 ZREC) t (baseW m t) (nSlotsZ m) j d =
      probeArm zeroSch m t (zMt m t) (zprobeW (m.arr64 ZSLOT) (m.arr64 ZREC) t (baseW m t) (nSlotsZ m)) j d := by
  intro j d; rw [zprobeW]; rfl

theorem zpushOK_room (m : Mem) (t : Word) (h : zpushOK m t = true) : PushRoom zeroSch m t := by
  simp only [zpushOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have := UInt64.toNat_shiftRight (m.len64 ZREC) 1
  simp only [PushRoom, cntW, zcnt, zeroSch, len64_eq] at *
  grind

theorem zpushMem_eq (m : Mem) (t j c : Word) :
    zpushMem m t j c = pushG zeroSch m t [0] j c := by
  simp [zpushMem, pushG, wrRec, Schema.ad, zeroSch]

theorem zinternW_eq (m : Mem) :
    zinternW m = internM zeroSch m 0 (zpushOK m) [0]
      (zprobeW (m.arr64 ZSLOT) (m.arr64 ZREC) 0 (baseW m 0) (nSlotsZ m) (homeW zeroHashW (nSlotsZ m)) 0)
      (zprobeW (m.arr64 ZSLOT) (m.arr64 ZREC) 1 (baseW m 1) (nSlotsZ m) (homeW zeroHashW (nSlotsZ m)) 0) := by
  have e0 : ∀ x, hdW zeroSch.tag.toUInt64 0 x = zeroP + x := fun x => by
    simp [hdW, zeroSch, zeroP, LTag.zero]
  have e1 : ∀ x, hdW zeroSch.tag.toUInt64 1 x = zeroS + x := fun x => by
    simp [hdW, zeroSch, zeroS, LTag.zero]
  simp only [zinternW, internM, zpushMem_eq, e0, e1, true_and]
  rfl

/-! ## `intern_zero` refines `internLNode .zero` -/

section intern
variable (m : Mem) (a : AState) (hR : ZeroR m a)

include hR in
/-- **`intern_zero`'s model refines the arena's `internLNode` at the `zero` node.** -/
theorem zintern_correct (w : Word) (m' : Mem) (hI : zinternW m = some (w, m')) :
    AM.ok (internLNode .zero) a ∧
    ZeroR m' (AM.st (internLNode .zero) a) ∧
    AM.res (internLNode .zero) a = decI w := by
  rw [zinternW_eq] at hI
  exact intern_correctG zeroSch ZRecRel zhash zeroSch_wf zeroFrame zeroLens a m hR _ _ _ _ _
    (internLNode_zero_run a) false rfl 0 (by simp) (by simp) _ _ (zeroMatchOK m)
    (zeroHomeOK m) _ _ (probe_homeG zeroSch m 0 _ _ (zprobeW_arm m 0) _)
    (probe_homeG zeroSch m 1 _ _ (zprobeW_arm m 1) _) _ (zpushOK_room m) _ rfl
    (zeroNewOK m) w m' hI


include hR in
/-- **The `zero` table's constant bit across `intern_zero`**: `hasParam = false`. -/
theorem zintern_hp (hC : ConstT2 zeroLens (fun d : LDer => hpW d = 0) a) (w : Word) (m' : Mem)
    (hI : zinternW m = some (w, m')) :
    ConstT2 zeroLens (fun d : LDer => hpW d = 0) (AM.st (internLNode .zero) a) := by
  obtain ⟨hok, -, -⟩ := zintern_correct m a hR w m' hI
  exact constMk zeroLens _ a _ _ _ _ _ hC rfl
    (AM.proto_casesG zeroLens _ _ _ _ _ _ a (internLNode_zero_run a) hok)
end intern

/-- `intern_zero` refines `internLNode .zero` under `ZeroR`. -/
theorem internZero_refines (p : Prog) (hpf : p.lookup "zero_find" = some zeroFind)
    (hpp : p.lookup "zero_push" = some zeroPush) (hp : p.lookup "intern_zero" = some internZero)
    (a₀ : AState) (n : Nat) (s₀ : St) (hR : ZeroR s₀.mem a₀) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_zero" []
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internLNode .zero) a₀ ∧
      ZeroR s'.mem (AM.st (internLNode .zero) a₀) ∧
      AM.res (internLNode .zero) a₀ = decI (r.headD 0); ⊤⦄ :=
  Sim.tripleD (internZero_spec p hpf hpp hp n s₀) (Sim.ofOkD (zintern_correct s₀.mem a₀ hR))

end L.Arena
