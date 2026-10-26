import ConAgua.Arena.ConsLibRel
import ConAgua.Arena.SimLib
import ConAgua.Arena.ParamStore
import ConAgua.Arena.LpColRel

/-!
# The level `param` store refines the arena's `param` tables

The seventh table on the store library, the `succ` shape (one handle field, no scratch skip) for
the record `ParamNode { n : NIdx }` of the level store's `param` constructor
(`ConAgua/Arena/ParamStore.lean` has the L code). Unlike `succ`'s field (a level handle), `param`'s
field is a **name** handle: the schema `paramSch` (`PREC`, `PSLOT`, one word per node, counts at
`CTL[14 + t]`, tag `4`), the record relation `PRecRel` (the word is the name's handle word), the
node hash `phash`, the lens `paramLens` on the level store's two `param` tables
(`a.store.lss.ls.pers.params`/`scr.params`). `ParamR m a` is the library's `ConsR` for them.
`internParam_refines`: `intern_param(u)` refines `internLNode (.param (decI u))` under `ParamR`,
for a **name**-handle word `u`. `word_decI`/`isPersistent_decE`/`decI` (`StoreRel.lean`) are
already stated generically over the handle kind, so instantiating them at `.name` here (instead of
`.level`, as `succ` does) needed no library change.

Not represented: the derived column and every other table.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

/-- The arena's `param` cons key. -/
abbrev paramKey (n : NIdx) : ParamNode := ⟨n⟩

/-- `a` with the scratch / persistent `param` table of the level store replaced. -/
def withScrParams (a : AState) (t : Tbl ParamNode LIdx LDer) : AState :=
  { a with store := { a.store with lss := { a.store.lss with ls := { a.store.lss.ls with
      scr := { a.store.lss.ls.scr with params := t } } } } }
def withPersParams (a : AState) (t : Tbl ParamNode LIdx LDer) : AState :=
  { a with store := { a.store with lss := { a.store.lss with ls := { a.store.lss.ls with
      pers := { a.store.lss.ls.pers with params := t } } } } }

/-- The level store's two `param` tables. -/
def paramLens : Lens ParamNode LDer .level where
  on a := a.store.lss.ls.scratchOn
  getP a := a.store.lss.ls.pers.params
  getS a := a.store.lss.ls.scr.params
  setP := withPersParams
  setS := withScrParams
  on_setP _ _ := rfl
  on_setS _ _ := rfl
  getP_setP _ _ := rfl
  getS_setP _ _ := rfl
  getP_setS _ _ := rfl
  getS_setS _ _ := rfl

/-- `internLNode` at a `param` node is the library's protocol, with no skip. -/
theorem internLNode_param_run (n : NIdx) (a : AState) :
    (internLNode (.param n)).run a =
      protoRun paramLens (paramKey n) LTag.param a.store.lss.ls.pers.params.cons[paramKey n]?
        (a.store.lss.ls.derOfView (.param n)) (.native "arena: level constructor array full") a := by
  simp only [internLNode, LStore.find?, LTables.find?, Tbl.find?, LTables.sizeOf, EStore.ls,
    EStore.internLevel, LsStore.internLevel, LStore.intern, LTables.push]
  cases hp : a.store.lss.ls.pers.params.cons[paramKey n]? <;> cases hs : a.store.lss.ls.scratchOn <;>
    cases hc : a.store.lss.ls.scr.params.cons[paramKey n]? <;>
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hp, hs, hc, Bool.false_eq_true,
      ↓reduceIte, paramKey, protoRun, paramLens] <;>
    (try split) <;> simp_all [withScrParams, withPersParams, fail,
      throwThe, MonadExceptOf.throw, StateT.run, set, StateT.set,
      StateT.lift, bind, Except.bind, pure, Except.pure, StateT.bind, StateT.pure]

/-! ## The relation between L memory and the arena's `param` tables -/

/-- The `param` schema: `PREC`, `PSLOT`, one word per node, the counts at `CTL[14 + t]`. -/
def paramSch : Schema := ⟨PREC, PSLOT, 1, 14, LTag.param⟩

theorem paramSch_wf : paramSch.WF :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

theorem fld_param0 (m : Mem) (t i : Word) :
    fld paramSch m t i 0 = rdW (m.arr64 (tierA PREC t)) i := by
  simp [fld, Schema.ad, paramSch]

/-- Node `i` of tier `t` holds `param k.n`: its word is the name's handle word. -/
def PRecRel (m : Mem) (t i : Word) (k : ParamNode) : Prop :=
  tfld m PARAM t i 0 = k.n.word.toUInt64

/-- `PRecRel` in the raw words (inside the store library). -/
theorem PRecRel_raw (m : Mem) (t i : Word) (k : ParamNode) :
    PRecRel m t i k ↔
    rdW (m.arr64 (tierA PREC t)) i = k.n.word.toUInt64
  := Iff.rfl

/-- **The state relation** of the `param` store: the library's relation for the level store's two
`param` tables. -/
def ParamR (m : Mem) (a : AState) : Prop :=
  ConsR paramCS PRecRel m a.store.lss.ls.scratchOn a.store.lss.ls.pers.params
    a.store.lss.ls.scr.params

/-- A node's relation and hash depend only on its word. -/
theorem paramFrame : RFrame paramSch PRecRel phash := by
  intro m m' t i _ hf
  have h0 := hf 0 (by decide)
  rw [fld_param0, fld_param0] at h0
  exact ⟨fun a h => by simpa only [PRecRel_raw, h0] using h, by simp only [phash, h0]⟩

/-! ## The query's obligations -/

/-- The match of `param_find` on node `i` of tier `t`. -/
def pMt (m : Mem) (u t i : Word) : Bool := pmatchW (m.arr64 (tierA PREC t)) t i u

section query
variable (m : Mem) (u : Word) (hu : u.toNat < 2 ^ 32)

include hu in
/-- **Matching is equality of `param` nodes.** -/
theorem paramMatchOK : MatchOK PRecRel (pMt m u) m (paramKey (decI u)) := by
  intro t i k hr
  have := word_decI k.n u hu
  obtain ⟨kn⟩ := k
  grind [pMt, pmatchW, PRecRel_raw]

theorem paramHomeOK : HomeOK phash (pMt m u) m (paramHashW u) := by
  intro t i hm
  simp only [pMt, pmatchW, beq_iff_eq] at hm
  simp only [phash, hm]

include hu in
/-- The record `param_push` writes holds the node. -/
theorem paramNewOK : NewOKR paramSch PRecRel phash m [u] (paramKey (decI u)) (paramHashW u) := by
  intro t ht hroom _
  have e : fld paramSch (newRecM paramSch m t [u]) t
      (cntW paramSch m t) 0 = u := by
    have := hroom.1
    have := hroom.2
    rw [fld_newRecM paramSch paramSch_wf] <;> simp only [paramSch, Schema.ad] at * <;> grind
  rw [fld_param0] at e
  have := word_decI (decI u : NIdx) u hu
  simp only [PRecRel_raw, phash, paramKey, e]
  grind

end query

/-! ## The bridges from the L models -/

theorem ppushOK_room (m : Mem) (t : Word) (h : ppushOK m t = true) : PushRoom paramSch m t := by
  simp only [ppushOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have := UInt64.toNat_shiftRight (m.len64 (tierA PREC t)) 0
  simp only [PushRoom, cntW, pcnt, paramSch, len64_eq] at *
  grind

/-- **The `param` table's shape.** -/
theorem paramCS_wf : paramCS.WF where
  sch := paramSch_wf
  P := by decide
  S := by decide
  col A h := by simp [paramCS] at h
  colRoom A h := by simp [paramCS] at h
  colLt A h := by
    simp only [paramCS, reduceCtorEq] at h; (try subst h); (try decide)
  room m t h := (ppushOK_room m t ((ppushOK_eqC m t).trans h)).2
  vs ks h hk := by simp [pushArgs, paramCS, hk]
  ex _ := {
    nk := by decide
    nkw := by decide
    kpk := fun h => absurd h (by decide)
    mt := by
      intro m ks h t i hl
      obtain ⟨a, rfl⟩ := list_one ks (by simpa [paramCS] using hl)
      simp [paramCS, pmatchW, fieldsL, kfld, fld, Schema.ad, ConsSch.sch, List.range_succ, show UInt64.ofNat 0 = 0 from rfl]
    hs := by intro m t i; simp [paramCS, pmatchW, phash, fieldsL, kfld, fld, Schema.ad, ConsSch.sch, List.range_succ, show UInt64.ofNat 0 = 0 from rfl]
    qh := fun _ _ _ => rfl
    vs := by intro ks h hl f hf; simp [pushArgs, paramCS, nkW, recK] at hf ⊢ <;> omega }

/-! ## `intern_param` refines `internLNode (.param _)` -/

section intern
variable (m : Mem) (a : AState) (hR : ParamR m a) (u : Word) (hu : u.toNat < 2 ^ 32)

include hR hu in
/-- **`intern_param`'s model refines the arena's `internLNode` at a `param` node.** -/
theorem pintern_correct (w : Word) (m' : Mem) (hI : pinternW m u = some (w, m')) :
    AM.ok (internLNode (.param (decI u))) a ∧
    ParamR m' (AM.st (internLNode (.param (decI u))) a) ∧
    AM.res (internLNode (.param (decI u))) a = decI w :=
  consIntern_correct paramCS_wf paramFrame (colFree_none _ rfl) paramLens a hR _ _ _ _ _
    (internLNode_param_run _ a) false rfl [u] (by simp [show skipC paramCS m [u] = 0 from rfl])
    (by simp) ⟨rfl, paramMatchOK m u hu, paramHomeOK m u, paramNewOK m u hu⟩ w m' hI

include hR hu in
/-- **The `param` table's constant bit across `intern_param`**: `hasParam = true`. -/
theorem pintern_hp (hC : ConstT2 paramLens (fun d : LDer => hpW d = 1) a) (w : Word) (m' : Mem)
    (hI : pinternW m u = some (w, m')) :
    ConstT2 paramLens (fun d : LDer => hpW d = 1) (AM.st (internLNode (.param (decI u))) a) := by
  obtain ⟨hok, -, -⟩ := pintern_correct m a hR u hu w m' hI
  exact constMk paramLens _ a _ _ _ _ _ hC rfl
    (AM.proto_casesG paramLens _ _ _ _ _ _ a (internLNode_param_run _ a) hok)
end intern

end L.Arena
