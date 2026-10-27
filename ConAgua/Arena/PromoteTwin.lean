import ConRon.Arena.Monad
import Std.Data.DTreeMap.Internal.Operations
import Std.Do.Triple.SpecLemmas
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# `internPersistent` is the ordinary interner with the scratch flags cleared

The twin's four `internPersistentE/N/L/Ls` (`Arena/Monad.lean`) are `intern`'s branch for a
closed scratch tier, called while the scratch tier is open. L has no separate code for them: the
promotion's `pi_*` (`Promote.lean`) clears the scratch flag `CTL[1]`, calls the ordinary
interner, and restores the flag. This file is the twin side of that: **`internPersistentX v` run
at `a` is `internX v` run at `a` with the four stores' `scratchOn` flags cleared (`onA false a`),
with the flags restored afterwards** (`onA a.store.scratchOn`), provided

* the four flags of `a` agree (`FlagsEq`; the arena relation has them all equal to `CTL[1]`), and
* the view's children are persistent handles (`*Kids`): the derived word of a scratch child
  reads differently with the flag cleared (`derived` answers `0`). The promotion meets it by
  construction: it promotes the children first.
-/

open ConRon.Arena


namespace L.Arena

/-- The four stores' scratch flags set to `b`. -/
def setOn (b : Bool) (st : EStore) : EStore :=
  { st with scratchOn := b, lss := { st.lss with scratchOn := b, ls := { st.lss.ls with
      scratchOn := b, ns := { st.lss.ls.ns with scratchOn := b } } } }

/-- The state with the four scratch flags set to `b`. -/
def onA (b : Bool) (a : AState) : AState := { a with store := setOn b a.store }

/-- The four scratch flags agree. -/
structure FlagsEq (st : EStore) : Prop where
  lss : st.lss.scratchOn = st.scratchOn
  ls : st.lss.ls.scratchOn = st.scratchOn
  ns : st.lss.ls.ns.scratchOn = st.scratchOn

/-- The children of a name view are persistent. -/
def nKids : NNodeView → Prop
  | .anonymous => True
  | .str p _ => p.isPersistent
  | .num p _ => p.isPersistent

theorem nder_off (st : NStore) (v : NNodeView) (hk : nKids v) :
    ({ st with scratchOn := false } : NStore).derOfView v = st.derOfView v := by
  cases v <;> simp_all [NStore.derOfView, NStore.derived, nKids]

/-- **`internPersistentN` is `internNNode` with the flags cleared.** -/
theorem internPersistentN_eq (v : NNodeView) (a : AState) (hF : FlagsEq a.store) (hk : nKids v) :
    (internPersistentN v).run a =
      ((internNNode v).run (onA false a)).map (fun r => (r.1, onA a.store.scratchOn r.2)) := by
  have hd := nder_off a.store.lss.ls.ns v hk
  obtain ⟨⟨⟨⟨⟨np, ns, nb⟩, lp, ls, lb⟩, sp, ss, sb⟩, ep, es, eb⟩, me, ca, pi⟩ := a
  obtain ⟨h1, h2, h3⟩ := hF
  simp only at h1 h2 h3 hd
  subst h1 h2 h3
  cases hf : np.find? v with
  | some h =>
    simp [internPersistentN, internNNode, onA, setOn, EStore.ns, NStore.find?, hf,
      StateT.run_bind, StateT.run_get, Except.map]; rfl
  | none =>
    by_cases hc : np.sizeOf v < Idx.idxCap
    · simp [internPersistentN, internNNode, onA, setOn, EStore.ns, NStore.find?, hf, hc,
        StateT.run_bind, StateT.run_get, Except.map, EStore.internNamePersistent,
        LsStore.internNamePersistent, LStore.internNamePersistent, NStore.internPersistent,
        EStore.internName, LsStore.internName, LStore.internName, NStore.intern, hd]
      rfl
    · simp [internPersistentN, internNNode, onA, setOn, EStore.ns, NStore.find?, hf, hc,
        StateT.run_bind, StateT.run_get, Except.map, fail, throwThe, MonadExceptOf.throw]
      rfl

/-- The children of a level view are persistent. -/
def lKids : LNodeView → Prop
  | .zero => True
  | .succ u => u.isPersistent
  | .max u v => u.isPersistent ∧ v.isPersistent
  | .imax u v => u.isPersistent ∧ v.isPersistent
  | .param n => n.isPersistent

theorem lder_off (st : LStore) (v : LNodeView) (hk : lKids v) :
    ({ st with scratchOn := false, ns := { st.ns with scratchOn := false } } : LStore).derOfView v =
      st.derOfView v := by
  cases v <;> simp_all [LStore.derOfView, LStore.derived, NStore.derived, lKids]

/-- **`internPersistentL` is `internLNode` with the flags cleared.** -/
theorem internPersistentL_eq (v : LNodeView) (a : AState) (hF : FlagsEq a.store) (hk : lKids v) :
    (internPersistentL v).run a =
      ((internLNode v).run (onA false a)).map (fun r => (r.1, onA a.store.scratchOn r.2)) := by
  have hd := lder_off a.store.lss.ls v hk
  obtain ⟨⟨⟨⟨⟨np, ns, nb⟩, lp, ls, lb⟩, sp, ss, sb⟩, ep, es, eb⟩, me, ca, pi⟩ := a
  obtain ⟨h1, h2, h3⟩ := hF
  simp only at h1 h2 h3 hd
  subst h1 h2 h3
  cases hf : lp.find? v with
  | some h =>
    simp [internPersistentL, internLNode, onA, setOn, EStore.ls, LStore.find?, hf,
      StateT.run_bind, StateT.run_get, Except.map]; rfl
  | none =>
    by_cases hc : lp.sizeOf v < Idx.idxCap
    · simp [internPersistentL, internLNode, onA, setOn, EStore.ls, LStore.find?, hf, hc,
        StateT.run_bind, StateT.run_get, Except.map, EStore.internLevelPersistent,
        LsStore.internLevelPersistent, LStore.internPersistent,
        EStore.internLevel, LsStore.internLevel, LStore.intern, hd]
      rfl
    · simp [internPersistentL, internLNode, onA, setOn, EStore.ls, LStore.find?, hf, hc,
        StateT.run_bind, StateT.run_get, Except.map, fail, throwThe, MonadExceptOf.throw]
      rfl

/-- The elements of a level-list view are persistent. -/
def lsKids (v : LsNodeView) : Prop := ∀ u ∈ v, u.isPersistent

theorem lsder_off (st : LsStore) (v : LsNodeView) (hk : lsKids v) :
    (LsStore.mk { st.ls with scratchOn := false, ns := { st.ls.ns with scratchOn := false } }
      st.pers st.scr false).derOfView v = st.derOfView v := by
  induction v with
  | nil => rfl
  | cons u us ih =>
    have hu : u.isPersistent := hk u (by simp)
    have hus : lsKids us := fun x hx => hk x (by simp [hx])
    simp only [LsStore.derOfView, ih hus, LStore.derived, hu, ↓reduceIte]

/-- **`internPersistentLs` is `internLsNode` with the flags cleared.** -/
theorem internPersistentLs_eq (v : LsNodeView) (a : AState) (hF : FlagsEq a.store)
    (hk : lsKids v) :
    (internPersistentLs v).run a =
      ((internLsNode v).run (onA false a)).map (fun r => (r.1, onA a.store.scratchOn r.2)) := by
  have hd := lsder_off a.store.lss v hk
  obtain ⟨⟨⟨⟨⟨np, ns, nb⟩, lp, ls, lb⟩, sp, ss, sb⟩, ep, es, eb⟩, me, ca, pi⟩ := a
  obtain ⟨h1, h2, h3⟩ := hF
  simp only at h1 h2 h3 hd
  subst h1 h2 h3
  cases hf : sp.find? v with
  | some h =>
    simp [internPersistentLs, internLsNode, onA, setOn, LsStore.find?, hf,
      StateT.run_bind, StateT.run_get, Except.map]; rfl
  | none =>
    by_cases hc : sp.sizeOf v < Idx.idxCap
    · simp [internPersistentLs, internLsNode, onA, setOn, LsStore.find?, hf, hc,
        StateT.run_bind, StateT.run_get, Except.map, EStore.internLevelsPersistent,
        LsStore.internPersistent, EStore.internLevels, LsStore.intern, hd]
      rfl
    · simp [internPersistentLs, internLsNode, onA, setOn, LsStore.find?, hf, hc,
        StateT.run_bind, StateT.run_get, Except.map, fail, throwThe, MonadExceptOf.throw]
      rfl

/-- The children of an expression view are persistent. -/
def eKids : ENodeView → Prop
  | .bvar _ => True
  | .fvar _ ty => ty.isPersistent
  | .sort u => u.isPersistent
  | .const n us => n.isPersistent ∧ us.isPersistent
  | .app f a => f.isPersistent ∧ a.isPersistent
  | .lam ty b => ty.isPersistent ∧ b.isPersistent
  | .forallE ty b => ty.isPersistent ∧ b.isPersistent
  | .letE ty v b => ty.isPersistent ∧ v.isPersistent ∧ b.isPersistent
  | .lit _ => True
  | .proj n _ e => n.isPersistent ∧ e.isPersistent

theorem eder_off (st : EStore) (v : ENodeView) (hk : eKids v) :
    (setOn false st).derOfView v = st.derOfView v := by
  cases v <;> simp_all [EStore.derOfView, EStore.derived, EStore.lder, EStore.nder, EStore.lsder,
    EStore.ls, EStore.ns, LStore.derived, NStore.derived, LsStore.derived, setOn, eKids,
    EStore.derOfBVar, EStore.derOfFVar, EStore.derOfSort, EStore.derOfConst, EStore.derOfApp,
    EStore.derOfBindAt, EStore.derOfLetAt, EStore.derOfLit, EStore.derOfProj]

theorem findBind_lam (t : ETables) (ty b : EIdx) : t.findBind ETag.lam ⟨ty, b⟩ = t.find? (.lam ty b) :=
  rfl
theorem findBind_forall (t : ETables) (ty b : EIdx) :
    t.findBind ETag.forallE ⟨ty, b⟩ = t.find? (.forallE ty b) := rfl
theorem bindSizeOf_lam (t : ETables) (ty b : EIdx) : t.bindSizeOf ETag.lam = t.sizeOf (.lam ty b) :=
  rfl
theorem bindSizeOf_forall (t : ETables) (ty b : EIdx) :
    t.bindSizeOf ETag.forallE = t.sizeOf (.forallE ty b) := rfl
theorem pushBind_lam (t : ETables) (ty b : EIdx) (d : UInt64) (tr : UInt32) :
    t.pushBind ETag.lam ⟨ty, b⟩ d tr = t.push (.lam ty b) d tr := rfl
theorem pushBind_forall (t : ETables) (ty b : EIdx) (d : UInt64) (tr : UInt32) :
    t.pushBind ETag.forallE ⟨ty, b⟩ d tr = t.push (.forallE ty b) d tr := rfl
theorem tag_fa_lam : (ETag.forallE = ETag.lam) = False := by decide
theorem tag_fa_lam' : (ETag.forallE == ETag.lam) = false := by decide

theorem derOfBindAt_19 (st : EStore) (ty b : EIdx) :
    st.derOfBindAt 19 ty b = st.derOfView (.lam ty b) := rfl
theorem derOfBindAt_23 (st : EStore) (ty b : EIdx) :
    st.derOfBindAt 23 ty b = st.derOfView (.forallE ty b) := rfl
theorem derOfBindAt_lam (st : EStore) (ty b : EIdx) :
    st.derOfBindAt (if ETag.lam == ETag.lam then 19 else 23) ty b = st.derOfView (.lam ty b) := rfl
theorem derOfBindAt_forall (st : EStore) (ty b : EIdx) :
    st.derOfBindAt (if ETag.forallE == ETag.lam then 19 else 23) ty b =
      st.derOfView (.forallE ty b) := rfl

set_option hygiene false in
/-- One constructor of `internPersistentE_eq`: the probe hit, the append, the capacity decline. -/
local macro "pe_case " v:term : tactic => `(tactic| (
  cases hf : ep.find? $v with
  | some h => simp [hf, StateT.run_pure, Except.map]; rfl
  | none =>
    by_cases hc : ep.sizeOf $v < Idx.idxCap
    · simp only [ETables.bindSizeOf, ETables.sizeOf, tag_fa_lam, tag_fa_lam'] at hc ⊢
      simp [hf, hc, EStore.internPersistent, EStore.intern, EStore.persFindMaybe,
        EStore.internLam, EStore.internForallE, EStore.internBind, EStore.persFindBindMaybe,
        findBind_lam, findBind_forall, pushBind_lam, pushBind_forall, derOfBindAt_lam,
        derOfBindAt_forall, derOfBindAt_19, derOfBindAt_23, hd, StateT.run_bind, StateT.run_set,
        StateT.run_pure, Except.map]
      rfl
    · simp only [ETables.bindSizeOf, ETables.sizeOf, tag_fa_lam, tag_fa_lam'] at hc ⊢
      simp [hf, hc, fail, throwThe, MonadExceptOf.throw, Except.map]
      rfl))

/-- **`internPersistentE` is `internE` with the flags cleared.** -/
theorem internPersistentE_eq (v : ENodeView) (a : AState) (hF : FlagsEq a.store) (hk : eKids v) :
    (internPersistentE v).run a =
      ((internE v).run (onA false a)).map (fun r => (r.1, onA a.store.scratchOn r.2)) := by
  have hd := eder_off a.store v hk
  obtain ⟨⟨⟨⟨⟨np, ns, nb⟩, lp, ls, lb⟩, sp, ss, sb⟩, ep, es, eb⟩, me, ca, pi⟩ := a
  obtain ⟨h1, h2, h3⟩ := hF
  simp only [setOn] at h1 h2 h3 hd
  subst h1 h2 h3
  cases v <;>
    simp only [internPersistentE, internE, internNodeE, internLamE, internForallEE, onA, setOn,
      EStore.find?, EStore.persFindMaybe, EStore.findBind, EStore.persFindBindMaybe, findBind_lam,
      findBind_forall, bindSizeOf_lam, bindSizeOf_forall, StateT.run_bind, StateT.run_get,
      Bool.false_eq_true, ↓reduceIte, pure_bind]
  case bvar i => pe_case (.bvar i)
  case fvar i t => pe_case (.fvar i t)
  case sort u => pe_case (.sort u)
  case const n us => pe_case (.const n us)
  case app f x => pe_case (.app f x)
  case lam t b => pe_case (.lam t b)
  case forallE t b =>
    cases hf : ep.find? (.forallE t b) with
    | some h => simp [StateT.run_pure, Except.map]; rfl
    | none =>
      by_cases hc : ep.sizeOf (.forallE t b) < Idx.idxCap
      · simp only [ETables.bindSizeOf, ETables.sizeOf, tag_fa_lam'] at hc ⊢
        simp only [hf, hc, EStore.internPersistent, EStore.internForallE, EStore.internBind, EStore.persFindBindMaybe, findBind_forall, pushBind_forall, Bool.false_eq_true,
          ↓reduceIte, tag_fa_lam', derOfBindAt_23, hd]
        rfl
      · simp only [ETables.bindSizeOf, ETables.sizeOf, tag_fa_lam'] at hc ⊢
        simp only [hc, Bool.false_eq_true, ↓reduceIte]
        rfl
  case letE t x b => pe_case (.letE t x b)
  case lit l => pe_case (.lit l)
  case proj n i e => pe_case (.proj n i e)

end L.Arena
