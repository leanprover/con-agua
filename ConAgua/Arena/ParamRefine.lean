import ConAgua.Arena.StoreLib
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
(`a.store.lss.ls.pers.params`/`scr.params`). `ParamR m a` is the library's `StoreR` for them.
`internParam_refines`: `intern_param(u)` refines `internLNode (.param (decI u))` under `ParamR`,
for a **name**-handle word `u`. `word_decI`/`isPersistent_decE`/`decI` (`StoreRel.lean`) are
already stated generically over the handle kind, so instantiating them at `.name` here (instead of
`.level`, as `succ` does) needed no library change.

Not represented: the derived column and every other table.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

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
      ↓reduceIte, paramKey, ite_self, protoRun, paramLens] <;>
    (try split) <;> simp_all [StateT.run_set, StateT.run_pure, withScrParams, withPersParams, fail,
      throwThe, MonadExceptOf.throw, StateT.run, Functor.map, StateT.map, set, StateT.set,
      StateT.lift, bind, Except.bind, Except.map, pure, Except.pure, StateT.bind, StateT.pure]

/-! ## The relation between L memory and the arena's `param` tables -/

/-- The `param` schema: `PREC`, `PSLOT`, one word per node, the counts at `CTL[14 + t]`. -/
def paramSch : Schema := ⟨PREC, PSLOT, 1, 2, 14, LTag.param⟩

theorem paramSch_wf : paramSch.WF :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem fld_param0 (m : Mem) (t i : Word) :
    fld paramSch m t i 0 = rdW (m.arr64 PREC) (i * 2 + t) := by
  simp [fld, Schema.ad, paramSch]

/-- Node `i` of tier `t` holds `param k.n`: its word is the name's handle word. -/
def PRecRel (m : Mem) (t i : Word) (k : ParamNode) : Prop :=
  rdW (m.arr64 PREC) (i * 2 + t) = k.n.word.toUInt64

/-- **The state relation** of the `param` store: the library's relation for the level store's two
`param` tables. -/
def ParamR (m : Mem) (a : AState) : Prop :=
  StoreR paramSch PRecRel phash m a.store.lss.ls.scratchOn a.store.lss.ls.pers.params
    a.store.lss.ls.scr.params

/-- A node's relation and hash depend only on its word. -/
theorem paramFrame : RFrame paramSch PRecRel phash := by
  intro m m' t i _ hf
  have h0 := hf 0 (by decide)
  rw [fld_param0, fld_param0] at h0
  exact ⟨fun a h => by simpa only [PRecRel, h0] using h, by simp only [phash, h0]⟩

/-! ## The query's obligations -/

/-- The match of `param_find` on node `i` of tier `t`. -/
def pMt (m : Mem) (u t i : Word) : Bool := pmatchW (m.arr64 PREC) t i u

section query
variable (m : Mem) (u : Word) (hu : u.toNat < 2 ^ 32)

include hu in
/-- **Matching is equality of `param` nodes.** -/
theorem paramMatchOK : MatchOK PRecRel (pMt m u) m (paramKey (decI u)) := by
  intro t i k hr
  have := word_decI k.n u hu
  obtain ⟨kn⟩ := k
  grind [pMt, pmatchW, PRecRel]

theorem paramHomeOK : HomeOK phash (pMt m u) m (paramHashW u) := by
  intro t i hm
  simp only [pMt, pmatchW, beq_iff_eq] at hm
  simp only [phash, hm]

include hu in
/-- The record `param_push` writes holds the node. -/
theorem paramNewOK : NewOK paramSch PRecRel phash m [u] (paramKey (decI u)) (paramHashW u) := by
  intro t j ht hroom
  have e : fld paramSch (pushG paramSch m t [u] j (cntW paramSch m t)) t
      (cntW paramSch m t) 0 = u := by
    have := hroom.1
    have := hroom.2
    rw [fld_pushG paramSch paramSch_wf] <;> simp only [paramSch, Schema.ad] at * <;> grind
  rw [fld_param0] at e
  have := word_decI (decI u : NIdx) u hu
  simp only [PRecRel, phash, paramKey, e]
  grind

end query

/-! ## The bridges from the L models -/

theorem pprobeW_arm (m : Mem) (u t : Word) :
    ∀ j d, pprobeW (m.arr64 PSLOT) (m.arr64 PREC) t u (baseW m t) (nSlotsP m) j d =
      probeArm paramSch m t (pMt m u t) (pprobeW (m.arr64 PSLOT) (m.arr64 PREC) t u (baseW m t) (nSlotsP m)) j d := by
  intro j d; rw [pprobeW]; rfl

theorem ppushOK_room (m : Mem) (t : Word) (h : ppushOK m t = true) : PushRoom paramSch m t := by
  simp only [ppushOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have := UInt64.toNat_shiftRight (m.len64 PREC) 1
  simp only [PushRoom, cntW, pcnt, paramSch, len64_eq] at *
  grind

theorem ppushMem_eq (m : Mem) (t u j c : Word) :
    ppushMem m t u j c = pushG paramSch m t [u] j c := by
  simp [ppushMem, pushG, wrRec, Schema.ad, paramSch]

theorem pinternW_eq (m : Mem) (u : Word) :
    pinternW m u = internM paramSch m 0 (ppushOK m) [u]
      (pprobeW (m.arr64 PSLOT) (m.arr64 PREC) 0 u (baseW m 0) (nSlotsP m) (homeW (paramHashW u) (nSlotsP m)) 0)
      (pprobeW (m.arr64 PSLOT) (m.arr64 PREC) 1 u (baseW m 1) (nSlotsP m) (homeW (paramHashW u) (nSlotsP m)) 0)
      phash := by
  have e0 : ∀ x, hdW paramSch.tag.toUInt64 0 x = paramP + x := fun x => by
    simp [hdW, paramSch, paramP, LTag.param]
  have e1 : ∀ x, hdW paramSch.tag.toUInt64 1 x = paramS + x := fun x => by
    simp [hdW, paramSch, paramS, LTag.param]
  simp only [pinternW, internM, pushM, ppushMem_eq, e0, e1, true_and]
  rfl

/-! ## `intern_param` refines `internLNode (.param _)` -/

section intern
variable (m : Mem) (a : AState) (hR : ParamR m a) (u : Word) (hu : u.toNat < 2 ^ 32)

include hR hu in
/-- **`intern_param`'s model refines the arena's `internLNode` at a `param` node.** -/
theorem pintern_correct (w : Word) (m' : Mem) (hI : pinternW m u = some (w, m')) :
    AM.ok (internLNode (.param (decI u))) a ∧
    ParamR m' (AM.st (internLNode (.param (decI u))) a) ∧
    AM.res (internLNode (.param (decI u))) a = decI w := by
  rw [pinternW_eq] at hI
  exact intern_correctG paramSch PRecRel phash paramSch_wf paramFrame paramLens a m hR _ _ _ _ _
    (internLNode_param_run _ a) false rfl 0 (by simp) (by simp) _ _ (paramMatchOK m u hu)
    (paramHomeOK m u) _ _ (probe_homeG paramSch m 0 _ _ (pprobeW_arm m u 0) _)
    (probe_homeG paramSch m 1 _ _ (pprobeW_arm m u 1) _) _ (ppushOK_room m) _ rfl
    (paramNewOK m u hu) w m' hI


include hR hu in
/-- **The `param` table's constant bit across `intern_param`**: `hasParam = true`. -/
theorem pintern_hp (hC : ConstT2 paramLens (fun d : LDer => hpW d = 1) a) (w : Word) (m' : Mem)
    (hI : pinternW m u = some (w, m')) :
    ConstT2 paramLens (fun d : LDer => hpW d = 1) (AM.st (internLNode (.param (decI u))) a) := by
  obtain ⟨hok, -, -⟩ := pintern_correct m a hR u hu w m' hI
  exact constMk paramLens _ a _ _ _ _ _ hC rfl
    (AM.proto_casesG paramLens _ _ _ _ _ _ a (internLNode_param_run _ a) hok)
end intern

/-- `intern_param` refines `internLNode (.param _)` under `ParamR`. -/
theorem internParam_refines (p : Prog) (hpf : p.lookup "param_find" = some paramFind)
    (hpp : p.lookup "param_push" = some paramPush) (hp : p.lookup "intern_param" = some internParam)
    (a₀ : AState) (n : Nat) (s₀ : St) (u : Word) (hR : ParamR s₀.mem a₀) (hu : u.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_param" [u]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internLNode (.param (decI u))) a₀ ∧
      ParamR s'.mem (AM.st (internLNode (.param (decI u))) a₀) ∧
      AM.res (internLNode (.param (decI u))) a₀ = decI (r.headD 0); ⊤⦄ :=
  Sim.tripleD (internParam_spec p hpf hpp hp n s₀ u)
    (Sim.ofOkD (pintern_correct s₀.mem a₀ hR u hu))

end L.Arena
