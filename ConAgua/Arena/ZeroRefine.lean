import ConAgua.Arena.ConsLibRel
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
(`a.store.lss.ls.pers.zeros`/`scr.zeros`). `ZeroR m a` is the library's `ConsR` for them.
`internZero_refines`: `intern_zero()` refines `internLNode .zero` under `ZeroR`.

Not represented: the derived column and every other table.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


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
def zeroSch : Schema := ⟨ZREC, ZSLOT, 1, 8, LTag.zero⟩

theorem zeroSch_wf : zeroSch.WF :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

/-- Node `i` of tier `t` holds the `zero` node: trivially (there is only one `ZeroNode`). -/
def ZRecRel (_m : Mem) (_t _i : Word) (_k : ZeroNode) : Prop := True

/-- **The state relation** of the `zero` store: the library's relation for the level store's two
`zero` tables. -/
def ZeroR (m : Mem) (a : AState) : Prop :=
  ConsR zeroCS ZRecRel m a.store.lss.ls.scratchOn a.store.lss.ls.pers.zeros
    a.store.lss.ls.scr.zeros

/-- A node's relation and hash depend on nothing. -/
theorem zeroFrame : RFrame zeroSch ZRecRel zhash := by
  intro m m' t i _ _
  exact ⟨fun _ _ => trivial, rfl⟩

/-! ## The query's obligations -/

/-- The match of `zero_find` on node `i` of tier `t`: always. -/
def zMt (m : Mem) (t i : Word) : Bool := zmatchW (m.arr64 (tierA ZREC t)) t i

/-- **Matching is equality of `zero` nodes**: both sides are always true. -/
theorem zeroMatchOK (m : Mem) : MatchOK ZRecRel (zMt m) m zeroKey := by
  intro t i k _
  simp only [zMt, zmatchW, eq_iff_iff, iff_true, zeroNode_eq k]

theorem zeroHomeOK (m : Mem) : HomeOK zhash (zMt m) m zeroHashW := by
  intro t i _; rfl

/-- The record `zero_push` writes holds the node (trivially). -/
theorem zeroNewOK (m : Mem) : NewOKR zeroSch ZRecRel zhash m [0] zeroKey zeroHashW := by
  intro t _ _ _
  exact ⟨trivial, rfl⟩

/-! ## The bridges from the L models -/

theorem zpushOK_room (m : Mem) (t : Word) (h : zpushOK m t = true) : PushRoom zeroSch m t := by
  simp only [zpushOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have := UInt64.toNat_shiftRight (m.len64 (tierA ZREC t)) 0
  simp only [PushRoom, cntW, zcnt, zeroSch, len64_eq] at *
  grind

/-- **The `zero` table's shape.** -/
theorem zeroCS_wf : zeroCS.WF where
  sch := zeroSch_wf
  P := by decide
  S := by decide
  col A h := by simp [zeroCS] at h
  colRoom A h := by simp [zeroCS] at h
  colLt A h := by
    simp only [zeroCS, reduceCtorEq, Option.some.injEq] at h; (try subst h); (try decide)
  room m t h := (zpushOK_room m t ((zpushOK_eqC m t).trans h)).2
  vs ks h hk := by simp [pushArgs, zeroCS, hk]
  ex _ := {
    nk := by decide
    nkw := by decide
    kpk := fun h => absurd h (by decide)
    mt := by
      intro m ks h t i hl
      obtain rfl := list_zero ks (by simpa [zeroCS] using hl)
      simp [zeroCS, zmatchW, zhash, fieldsL, kfld, fld, Schema.ad, ConsSch.sch, List.range_succ, show UInt64.ofNat 0 = 0 from rfl, show UInt64.ofNat 1 = 1 from rfl]
    hs := by intro m t i; simp [zeroCS, zmatchW, zhash, fieldsL, kfld, fld, Schema.ad, ConsSch.sch, List.range_succ, show UInt64.ofNat 0 = 0 from rfl, show UInt64.ofNat 1 = 1 from rfl]
    qh := fun _ _ _ => rfl
    vs := by intro ks h hl f hf; simp [zeroCS, nkW] at hf }

/-! ## `intern_zero` refines `internLNode .zero` -/

section intern
variable (m : Mem) (a : AState) (hR : ZeroR m a)

include hR in
/-- **`intern_zero`'s model refines the arena's `internLNode` at the `zero` node.** -/
theorem zintern_correct (w : Word) (m' : Mem) (hI : zinternW m = some (w, m')) :
    AM.ok (internLNode .zero) a ∧
    ZeroR m' (AM.st (internLNode .zero) a) ∧
    AM.res (internLNode .zero) a = decI w :=
  consIntern_correct zeroCS_wf zeroFrame (colFree_none _ rfl) zeroLens a hR _ _ _ _ _
    (internLNode_zero_run a) false rfl [] (by simp [show skipC zeroCS m [] = 0 from rfl])
    (by simp) ⟨rfl, zeroMatchOK m, zeroHomeOK m, zeroNewOK m⟩ w m' hI

include hR in
/-- **The `zero` table's constant bit across `intern_zero`**: `hasParam = false`. -/
theorem zintern_hp (hC : ConstT2 zeroLens (fun d : LDer => hpW d = 0) a) (w : Word) (m' : Mem)
    (hI : zinternW m = some (w, m')) :
    ConstT2 zeroLens (fun d : LDer => hpW d = 0) (AM.st (internLNode .zero) a) := by
  obtain ⟨hok, -, -⟩ := zintern_correct m a hR w m' hI
  exact constMk zeroLens _ a _ _ _ _ _ hC rfl
    (AM.proto_casesG zeroLens _ _ _ _ _ _ a (internLNode_zero_run a) hok)
end intern

end L.Arena
