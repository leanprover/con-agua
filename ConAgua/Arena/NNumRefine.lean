import ConAgua.Arena.ConsLibRel
import ConAgua.Arena.NNumStore
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The name store's `num` store refines the arena's `num` tables

The record `NumNode { pre : NIdx, n : Nat }` (`ConAgua/Arena/NNumStore.lean` has the L code): the
`max` shape (two fields, width 2, no scratch skip) at the record level, but the second field is a
`Nat` (`bvar`'s shape, `BVarRefine.lean`), not a handle. The schema `nnumSch` (`NNREC`, `NNSLOT`,
two words per node, counts at `CTL[38 + t]`, tag `2`), the record relation `NnRecRel` (the first
word is the prefix's handle word, decoded at `.name` with `decI`; the second word's `toNat` is the
number), the node hash `nnhash`, the lens `nnumLens` on the name store's two `num` tables
(`a.store.lss.ls.ns.pers.nums`/`scr.nums`). `NNumR m a` is the library's `ConsR` for them.
`internNNum_refines`: `intern_nnum(pre, u)` refines `internNNode (.num (decI pre) u.toNat)` under
`NNumR`, for a **name**-handle word `pre` below `2 ^ 32` (`u`, the `Nat` field, needs no bound:
`UInt64.toNat_inj` relates the stored word to `u.toNat` directly, as `BVarRefine.lean`'s index
field does). As every table of the name/level stores, `NStore.find?` probes the persistent tier
unconditionally, so `skB = false`.

Not represented: the derived column and every other table.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

/-- The arena's `num` cons key. -/
abbrev nnKey (pre : NIdx) (n : Nat) : NumNode := ⟨pre, n⟩

/-- `a` with the scratch / persistent `num` table of the name store replaced. -/
def withScrNNums (a : AState) (t : Tbl NumNode NIdx UInt64) : AState :=
  { a with store := { a.store with lss := { a.store.lss with ls := { a.store.lss.ls with
      ns := { a.store.lss.ls.ns with scr := { a.store.lss.ls.ns.scr with nums := t } } } } } }
def withPersNNums (a : AState) (t : Tbl NumNode NIdx UInt64) : AState :=
  { a with store := { a.store with lss := { a.store.lss with ls := { a.store.lss.ls with
      ns := { a.store.lss.ls.ns with pers := { a.store.lss.ls.ns.pers with nums := t } } } } } }

/-- The name store's two `num` tables. -/
def nnumLens : Lens NumNode UInt64 .name where
  on a := a.store.lss.ls.ns.scratchOn
  getP a := a.store.lss.ls.ns.pers.nums
  getS a := a.store.lss.ls.ns.scr.nums
  setP := withPersNNums
  setS := withScrNNums
  on_setP _ _ := rfl
  on_setS _ _ := rfl
  getP_setP _ _ := rfl
  getS_setP _ _ := rfl
  getP_setS _ _ := rfl
  getS_setS _ _ := rfl

/-- `internNNode` at a `num` node is the library's protocol, with no skip (as the level store's
`internLNode`). -/
theorem internNNode_num_run (pre : NIdx) (n : Nat) (a : AState) :
    (internNNode (.num pre n)).run a =
      protoRun nnumLens (nnKey pre n) NTag.num a.store.lss.ls.ns.pers.nums.cons[nnKey pre n]?
        (a.store.lss.ls.ns.derOfView (.num pre n)) (.native "arena: name constructor array full")
        a := by
  simp only [internNNode, NStore.find?, NTables.find?, Tbl.find?, NTables.sizeOf, EStore.ns,
    EStore.internName, LsStore.internName, LStore.internName, NStore.intern, NTables.push]
  cases hp : a.store.lss.ls.ns.pers.nums.cons[nnKey pre n]? <;>
    cases hs : a.store.lss.ls.ns.scratchOn <;>
    cases hc : a.store.lss.ls.ns.scr.nums.cons[nnKey pre n]? <;>
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hp, hs, hc, Bool.false_eq_true,
      ↓reduceIte, nnKey, protoRun, nnumLens] <;>
    (try split) <;> simp_all [withScrNNums, withPersNNums, fail,
      throwThe, MonadExceptOf.throw, StateT.run, set, StateT.set,
      StateT.lift, bind, Except.bind, pure, Except.pure, StateT.bind, StateT.pure]

/-! ## The relation between L memory and the arena's `num` tables -/

/-- The `num` schema: `NNREC`, `NNSLOT`, two words per node, the counts at `CTL[38 + t]`. -/
def nnumSch : Schema := ⟨NNREC, NNSLOT, 2, 38, NTag.num⟩

theorem nnumSch_wf : nnumSch.WF :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

theorem fld_nn0 (m : Mem) (t i : Word) :
    fld nnumSch m t i 0 = rdW (m.arr64 (tierA NNREC t)) (i * 2) := by
  simp [fld, Schema.ad, nnumSch]
theorem fld_nn (m : Mem) (t i f : Word) :
    fld nnumSch m t i f = rdW (m.arr64 (tierA NNREC t)) (i * 2 + f) := rfl

/-- Node `i` of tier `t` holds the `num` node `k`: its prefix's handle word, and its number as a
word. -/
def NnRecRel (m : Mem) (t i : Word) (k : NumNode) : Prop :=
  tfld m NNUM t i 0 = k.pre.word.toUInt64 ∧
  (tfld m NNUM t i 1).toNat = k.n

/-- `NnRecRel` in the raw words (inside the store library). -/
theorem NnRecRel_raw (m : Mem) (t i : Word) (k : NumNode) :
    NnRecRel m t i k ↔
    rdW (m.arr64 (tierA NNREC t)) (i * 2) = k.pre.word.toUInt64 ∧
    (rdW (m.arr64 (tierA NNREC t)) (i * 2 + 1)).toNat = k.n
  := Iff.rfl

/-- **The state relation** of the `num` store: the library's relation for the name store's two
`num` tables. -/
def NNumR (m : Mem) (a : AState) : Prop :=
  ConsR nnumCS NnRecRel m a.store.lss.ls.ns.scratchOn a.store.lss.ls.ns.pers.nums
    a.store.lss.ls.ns.scr.nums

/-- A node's relation and hash depend only on its two words. -/
theorem nnFrame : RFrame nnumSch NnRecRel nnhash := by
  intro m m' t i _ hf
  have h0 := hf 0 (by decide)
  have h1 := hf 1 (by decide)
  rw [fld_nn0, fld_nn0] at h0
  rw [fld_nn, fld_nn] at h1
  exact ⟨fun a h => by simpa only [NnRecRel_raw, h0, h1] using h, by simp only [nnhash, h0, h1]⟩

/-! ## The query's obligations -/

/-- The match of `nnum_find` on node `i` of tier `t`. -/
def nnMt (m : Mem) (pre u t i : Word) : Bool := nnmatchW (m.arr64 (tierA NNREC t)) t i pre u

section query
variable (m : Mem) (pre u : Word) (hpre : pre.toNat < 2 ^ 32)

include hpre in
/-- **Matching is equality of `num` nodes.** -/
theorem nnumMatchOK : MatchOK NnRecRel (nnMt m pre u) m (nnKey (decI pre) u.toNat) := by
  intro t i k hr
  have := word_decI k.pre pre hpre
  obtain ⟨kp, kn⟩ := k
  simp only [NnRecRel_raw] at hr
  simp only [nnMt, nnmatchW, Bool.and_eq_true, beq_iff_eq, nnKey, NumNode.mk.injEq]
  grind [UInt64.toNat_inj]

theorem nnumHomeOK : HomeOK nnhash (nnMt m pre u) m (nnumHashW pre u) := by
  intro t i hm
  simp only [nnMt, nnmatchW, Bool.and_eq_true, beq_iff_eq] at hm
  simp only [nnhash, hm.1, hm.2]

include hpre in
/-- The record `nnum_push` writes holds the node. -/
theorem nnumNewOK : NewOKR nnumSch NnRecRel nnhash m [pre, u] (nnKey (decI pre) u.toNat)
    (nnumHashW pre u) := by
  intro t ht hroom _
  have e : ∀ g, g < 2 → fld nnumSch (newRecM nnumSch m t [pre, u]) t
      (cntW nnumSch m t) g = [pre, u].getD g.toNat 0 := by
    intro g hg
    have := hroom.1
    have := hroom.2
    rw [fld_newRecM nnumSch nnumSch_wf] <;> simp only [nnumSch, Schema.ad] at * <;> grind
  have e0 := e 0 (by decide)
  have e1 := e 1 (by decide)
  rw [fld_nn0] at e0
  rw [fld_nn] at e1
  simp only [List.getD_cons_zero, List.getD_cons_succ, show (1 : Word).toNat = 0 + 1 from rfl,
    show (0 : Word).toNat = 0 from rfl] at e0 e1
  have := word_decI (decI pre : NIdx) pre hpre
  simp only [NnRecRel_raw, nnhash, nnKey, e0, e1]
  grind

end query

/-! ## The bridges from the L models -/

theorem nnpushOK_room (m : Mem) (t : Word) (h : nnpushOK m t = true) : PushRoom nnumSch m t := by
  simp only [nnpushOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have := UInt64.toNat_shiftRight (m.len64 (tierA NNREC t)) 1
  simp only [PushRoom, cntW, nncnt, nnumSch, len64_eq] at *
  grind

/-- **The `nnum` table's shape.** -/
theorem nnumCS_wf : nnumCS.WF where
  sch := nnumSch_wf
  P := by decide
  S := by decide
  col A h := by simp [nnumCS] at h
  colRoom A h := by simp [nnumCS] at h
  colLt A h := by
    simp only [nnumCS, reduceCtorEq] at h; (try subst h); (try decide)
  room m t h := (nnpushOK_room m t ((nnpushOK_eqC m t).trans h)).2
  vs ks h hk := by simp [pushArgs, nnumCS, hk]
  ex h := by simp [nnumCS] at h

/-! ## `intern_nnum` refines `internNNode (.num _ _)` -/

section intern
variable (m : Mem) (a : AState) (hR : NNumR m a) (pre u : Word) (hpre : pre.toNat < 2 ^ 32)

include hR hpre in
/-- **`intern_nnum`'s model refines the arena's `internNNode` at a `num` node.** -/
theorem nnintern_correct (w : Word) (m' : Mem) (hI : nninternW m pre u = some (w, m')) :
    AM.ok (internNNode (.num (decI pre) u.toNat)) a ∧
    NNumR m' (AM.st (internNNode (.num (decI pre) u.toNat)) a) ∧
    AM.res (internNNode (.num (decI pre) u.toNat)) a = decI w :=
  consIntern_correct nnumCS_wf nnFrame (colFree_none _ rfl) nnumLens a hR _ _ _ _ _
    (internNNode_num_run _ _ a) false rfl [pre, u] (by simp [skipC, nnumCS]) (by simp)
    ⟨rfl, nnumMatchOK m pre u hpre, nnumHomeOK m pre u, nnumNewOK m pre u hpre⟩ w m' hI

end intern

end L.Arena
