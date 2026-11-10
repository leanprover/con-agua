module

public import ConAgua.Arena.Keeps
public meta import Lean
import ConRon.Arena.WFProofs
public import ConRon.Arena.Core

@[expose] public section

/-!
# The twin's store only grows: `SMono`

`SMono op`: every successful run of `op` extends the store (`Ext`) and keeps every expression
node's view (`SExt`). Closed under `pure`, `fail`, `bind`, `if` and `match`; the leaves are the
state primitives (`get`, the interners, the memo and cache writers, which leave the store alone).

`smono_auto` decomposes a goal `SMono op` structurally and closes the leaves by the lemmas
`L.Arena.KM.<f>` (one per twin function `f`, found by name) and the local hypotheses; `smono_derive
f₁ … fₙ` states and proves `KM.fᵢ` for twin functions, the hypotheses read off the argument types (a
core record `R` gets `RecSMono R`, a monadic argument `g` gets `∀ …, SMono (g …)`). The knot's
slots are `SMono` at every fuel (`KnotMono.lean`), which is the twin fact the knot's callers need:
a level handle's readback and a node's view survive a knot run.
-/

open ConRon.Arena

namespace L.Arena

/-- The store after extends the store before, views included. -/
structure SExt (a a' : AState) : Prop where
  ext : Ext a.store a'.store
  view : ∀ i v, a.store.view i = some v → a'.store.view i = some v

theorem SExt.refl (a : AState) : SExt a a := ⟨Ext.refl _, fun _ _ h => h⟩

theorem SExt.trans {a b c : AState} (h₁ : SExt a b) (h₂ : SExt b c) : SExt a c :=
  ⟨h₁.ext.trans h₂.ext, fun i v h => h₂.view i v (h₁.view i v h)⟩

theorem SExt.of_store {a a' : AState} (h : a'.store = a.store) : SExt a a' :=
  ⟨by rw [h]; exact Ext.refl _, fun _ _ hv => by rw [h]; exact hv⟩

/-- Every successful run of `op` extends the store (`SExt`). -/
@[irreducible] def SMono {α : Type} (op : AM α) : Prop :=
  ∀ a r a', op.run a = .ok (r, a') → SExt a a'

theorem SMono.run {α : Type} {op : AM α} (h : SMono op) {a : AState} {r : α} {a' : AState}
    (hr : op.run a = .ok (r, a')) : SExt a a' := by
  unfold SMono at h; exact h a r a' hr

theorem SMono.pure {α : Type} (x : α) : SMono (Pure.pure x : AM α) := by
  unfold SMono; intro a r a' h; cases h; exact SExt.refl _

theorem SMono.fail {α : Type} (e : CheckError) : SMono (ConRon.Arena.fail e : AM α) := by
  unfold SMono; intro a r a' h; cases h

theorem SMono.throw {α : Type} (e : CheckError) : SMono (throw e : AM α) := by
  unfold SMono; intro a r a' h; cases h

theorem SMono.throwThe {α : Type} (e : CheckError) : SMono (throwThe CheckError e : AM α) := by
  unfold SMono; intro a r a' h; cases h

theorem SMono.bind {α γ : Type} {x : AM α} {f : α → AM γ} (hx : SMono x)
    (hf : ∀ v, SMono (f v)) : SMono (x >>= f) := by
  unfold SMono at *; intro a r a' h
  simp only [StateT.run_bind] at h
  cases h1 : x.run a with
  | error e => rw [h1] at h; cases h
  | ok p =>
    obtain ⟨v, a₁⟩ := p
    rw [h1] at h
    exact (hx a v a₁ h1).trans (hf v a₁ r a' h)

theorem SMono.map {α γ : Type} {x : AM α} (f : α → γ) (hx : SMono x) : SMono (f <$> x) := by
  rw [map_eq_pure_bind]; exact SMono.bind hx fun _ => SMono.pure _

theorem SMono.seqRight {α γ : Type} {x : AM α} {y : AM γ} (hx : SMono x) (hy : SMono y) :
    SMono (x *> y) := by
  rw [seqRight_eq_bind]; exact SMono.bind hx fun _ => hy

theorem SMono.ite {α : Type} {c : Prop} [Decidable c] {t e : AM α} (ht : c → SMono t)
    (he : ¬ c → SMono e) : SMono (if c then t else e) := by
  split <;> rename_i h <;> first | exact ht h | exact he h

theorem SMono.dite {α : Type} {c : Prop} [Decidable c] {t : c → AM α} {e : ¬ c → AM α}
    (ht : ∀ h, SMono (t h)) (he : ∀ h, SMono (e h)) : SMono (if h : c then t h else e h) := by
  split <;> rename_i h <;> first | exact ht h | exact he h

theorem SMono.of_keeps {α : Type} {op : AM α} (h : Keeps (fun a => a.store) op) : SMono op := by
  unfold SMono; intro a r a' hr; exact SExt.of_store (h.run hr)

theorem SMono.get : SMono (get : AM AState) := by
  unfold SMono; intro a r a' h; cases h; exact SExt.refl _

theorem SMono.getThe : SMono (getThe AState : AM AState) := by
  unfold SMono; intro a r a' h; cases h; exact SExt.refl _

theorem SMono.monadStateGet : SMono (MonadState.get : AM AState) := by
  unfold SMono; intro a r a' h; cases h; exact SExt.refl _

theorem SMono.monadStateOfGet : SMono (MonadStateOf.get : AM AState) := by
  unfold SMono; intro a r a' h; cases h; exact SExt.refl _

/-- A run from the state `s` extends it (the code after a `get` that writes the state back). -/
@[irreducible] def SMonoAt {α : Type} (s : AState) (op : AM α) : Prop :=
  ∀ r a', op.run s = .ok (r, a') → SExt s a'

theorem SMono.at {α : Type} {op : AM α} (h : SMono op) (s : AState) : SMonoAt s op := by
  unfold SMonoAt; intro r a' hr; exact h.run hr

theorem SMonoAt.bind {α γ : Type} {s : AState} {x : AM α} {f : α → AM γ} (hx : SMonoAt s x)
    (hf : ∀ v, SMono (f v)) : SMonoAt s (x >>= f) := by
  unfold SMonoAt at *; intro r a' h
  simp only [StateT.run_bind] at h
  cases h1 : x.run s with
  | error e => rw [h1] at h; cases h
  | ok p =>
    obtain ⟨v, a₁⟩ := p
    rw [h1] at h
    exact (hx v a₁ h1).trans ((hf v).run h)

theorem SMonoAt.map {α γ : Type} {s : AState} {x : AM α} (f : α → γ) (hx : SMonoAt s x) :
    SMonoAt s (f <$> x) := by
  rw [map_eq_pure_bind]; exact SMonoAt.bind hx fun _ => SMono.pure _

theorem SMonoAt.seqRight {α γ : Type} {s : AState} {x : AM α} {y : AM γ} (hx : SMonoAt s x)
    (hy : SMono y) : SMonoAt s (x *> y) := by
  rw [seqRight_eq_bind]; exact SMonoAt.bind hx fun _ => hy

theorem SMonoAt.set {s t : AState} (h : SExt s t) : SMonoAt s (MonadStateOf.set t : AM PUnit) := by
  unfold SMonoAt; intro r a' hr; cases hr; exact h

theorem SMono.bind_get {β : Type} {f : AState → AM β} (h : ∀ s, SMonoAt s (f s)) :
    SMono ((MonadState.get : AM AState) >>= f) := by
  unfold SMono; intro a r a' hr
  have := h a; unfold SMonoAt at this
  exact this r a' (by simpa only [StateT.run_bind, StateT.run_get, pure_bind] using hr)

/-! ## The store's appends -/

theorem SExt.intern (a : AState) (v : ENodeView) (a' : AState) (h : a'.store = (a.store.intern v).1) :
    SExt a a' :=
  ⟨by rw [h]; exact EStore.intern_ext _ _, fun _ _ hv => by rw [h]; exact EStore.view_intern_mono _ _ hv⟩

theorem SExt.internBind (a : AState) (tag : UInt32) (ty b : EIdx) (ht : tag = ETag.lam ∨ tag = ETag.forallE)
    (a' : AState) (h : a'.store = (a.store.internBind tag ty b).1) : SExt a a' :=
  SExt.intern a _ a' (by rw [h, EStore.internBind_eq_intern _ _ _ _ ht])

/-- An append to the level/name part leaves the expression views alone. -/
theorem SExt.lss (a a' : AState) (hx : Ext a.store a'.store)
    (hv : ∀ i, a'.store.view i = a.store.view i) : SExt a a' :=
  ⟨hx, fun i v h => by rw [hv]; exact h⟩

end L.Arena

/-! ## The tactic -/

namespace KnotMonoTac
open Lean Meta Elab Tactic

/-- The lemma for a twin function `c`. -/
meta def lemmaName (c : Name) : Name := `L.Arena.KM ++ c

/-- The fixed structural lemmas, by head constant. -/
meta def structLemma? (c : Name) : Option Name :=
  if c == ``Bind.bind then some ``L.Arena.SMono.bind
  else if c == ``Pure.pure then some ``L.Arena.SMono.pure
  else if c == ``ConRon.Arena.fail then some ``L.Arena.SMono.fail
  else if c == ``MonadExcept.throw then some ``L.Arena.SMono.throw
  else if c == ``throwThe then some ``L.Arena.SMono.throwThe
  else if c == ``Functor.map then some ``L.Arena.SMono.map
  else if c == ``SeqRight.seqRight then some ``L.Arena.SMono.seqRight
  else if c == ``ite then some ``L.Arena.SMono.ite
  else if c == ``dite then some ``L.Arena.SMono.dite
  else if c == ``MonadState.get then some ``L.Arena.SMono.monadStateGet
  else if c == ``MonadStateOf.get then some ``L.Arena.SMono.monadStateOfGet
  else if c == ``getThe then some ``L.Arena.SMono.getThe
  else none

/-- Try `apply e` on `g`; the new goals, or `none`. -/
meta def tryApply (g : MVarId) (e : Lean.Expr) : MetaM (Option (List MVarId)) := do
  let s ← saveState
  try
    let gs ← g.apply e
    return some gs
  catch _ =>
    restoreState s
    return none

/-- The head of a statement: its predicate, and for `SMono` the operation's head. -/
meta def keyOf (t : Lean.Expr) : MetaM (Option (Name × Lean.Expr)) := do
  let t ← zetaReduce (← instantiateMVars t)
  forallTelescopeReducing t fun _ b => do
    let b ← zetaReduce (← instantiateMVars b)
    let some c := b.getAppFn.constName? | return none
    if c == ``L.Arena.SMono then return some (c, b.appArg!.headBeta.getAppFn)
    return some (c, Lean.mkConst c)

/-- Is `c` recursive (its unfolding equation mentions it)? -/
meta def isRecC (f : Name) : MetaM Bool := do
  let some eq ← getUnfoldEqnFor? f (nonRec := true) | return false
  let ty ← inferType (mkConst eq ((← getConstInfo eq).levelParams.map mkLevelParam))
  forallTelescope ty fun _ b => do
    let some (_, _, rhs) := b.eq? | return false
    return (rhs.find? (·.isConstOf f)).isSome

meta def sameKey (a b : Option (Name × Lean.Expr)) : Bool :=
  match a, b with
  | some (c, x), some (d, y) =>
    c == d && (match x.constName?, y.constName? with
      | some n, some m => n == m
      | _, _ => x.isFVar && y.isFVar && x.fvarId! == y.fvarId!)
  | _, _ => false

/-- Close a side goal (`RecSMono R`, `∀ …, SMono (g …)`) by a hypothesis, through intros. -/
meta partial def closeSide (g : MVarId) : MetaM Bool := do
  let s ← saveState
  try
    let (_, g) ← g.intros
    g.withContext do
      let gk ← keyOf (← g.getType)
      for d in (← getLCtx) do
        if d.isImplementationDetail then continue
        unless sameKey gk (← keyOf (← instantiateMVars d.type)) do continue
        let s2 ← saveState
        try
          let gs ← withReducible (g.apply d.toExpr)
          if gs.isEmpty then return true
          let mut ok := true
          for g' in gs do
            unless (← closeSide g') do ok := false
          if ok then return true
          restoreState s2
        catch _ => restoreState s2
      restoreState s
      return false
  catch _ =>
    restoreState s
    return false

/-- Head beta through metadata. -/
meta partial def hb (e : Lean.Expr) : Lean.Expr :=
  let e := e.consumeMData
  let f := e.getAppFn.consumeMData
  if f.isLambda && e.getAppNumArgs > 0 then hb (f.betaRev e.getAppRevArgs) else e

/-- One step on a goal `SMono op`: the subgoals, or `none` if no rule applies. -/
meta partial def step (g : MVarId) : TacticM (Option (List MVarId)) := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let t := t.headBeta
  if t.isAppOf ``L.Arena.SMonoAt then
    let op := hb t.appArg!
    if op != t.appArg! then
      return some [← g.replaceTargetDefEq (Lean.mkApp t.appFn! op)]
    let hd := op.getAppFn
    let c := hd.constName?.getD .anonymous
    let tryL (l : Name) : TacticM (Option (List MVarId)) := do
      if let some gs ← tryApply g (← mkConstWithFreshMVarLevels l) then
        let mut out := []
        for g' in gs do
          if (← g'.isAssigned) then continue
          let ty ← instantiateMVars (← g'.getType)
          if ty.isForall then
            let (_, g'') ← g'.intro1
            out := out ++ [g'']
          else out := out ++ [g']
        return some out
      return none
    if c == ``MonadStateOf.set || c == ``MonadState.set || c == ``set || c == ``StateT.set then
      if let some gs ← tryL ``L.Arena.SMonoAt.set then
        let mut out := []
        for g' in gs do
          let s ← saveState
          try
            let gs' ← evalTacticAt (← `(tactic| exact L.Arena.SExt.of_store rfl)) g'
            out := out ++ gs'
          catch _ =>
            restoreState s
            out := out ++ [g']
        return some out
    if c == ``Bind.bind then
      if let some gs ← tryL ``L.Arena.SMonoAt.bind then return some gs
    if c == ``Functor.map then
      if let some gs ← tryL ``L.Arena.SMonoAt.map then return some gs
    if c == ``SeqRight.seqRight then
      if let some gs ← tryL ``L.Arena.SMonoAt.seqRight then return some gs
    if c == ``ite || c == ``dite || (← isMatcher c) then
      let s ← saveState
      try
        return some (← evalTacticAt (← `(tactic| split)) g)
      catch _ => restoreState s
    if op.isLet then
      return some [← g.replaceTargetDefEq (Lean.mkApp t.appFn! (op.letBody!.instantiate1 op.letValue!))]
    if let some gs ← tryL ``L.Arena.SMono.at then return some gs
    return none
  unless t.isAppOf ``L.Arena.SMono do
    -- a side goal: intro and close it by a hypothesis, else hand it back as an `SMono` goal
    if ← closeSide g then return some []
    let (_, g') ← g.intros
    if g' != g then return some [g']
    return none
  let op := hb t.appArg!
  if op != t.appArg! then
    return some [← g.replaceTargetDefEq (Lean.mkApp t.appFn! op)]
  if op.isLet then
    return some [← g.replaceTargetDefEq (Lean.mkApp t.appFn! (op.letBody!.instantiate1 op.letValue!))]
  if op.isMData then
    return some [← g.replaceTargetDefEq (Lean.mkApp t.appFn! op.consumeMData)]
  let hd := op.getAppFn
  -- a let-bound local (a join point): its value
  if hd.isFVar then
    if let some v ← hd.fvarId!.getValue? then
      return some [← g.replaceTargetDefEq (Lean.mkApp t.appFn! (hb (Lean.mkAppN v op.getAppArgs)))]
  -- a local function: its hypothesis
  if hd.isFVar then
    let gk ← keyOf t
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      unless sameKey gk (← keyOf (← instantiateMVars d.type)) do continue
      if let some gs ← withReducible (tryApply g d.toExpr) then
        let mut rest := []
        for g' in gs do
          unless (← closeSide g') do rest := rest ++ [g']
        return some rest
    return none
  let some c := hd.constName? | return none
  if c == ``Bind.bind then
    let x := op.getAppArgs[4]!.getAppFn.constName?.getD .anonymous
    if x == ``MonadState.get || x == ``MonadStateOf.get || x == ``getThe || x == ``get then
      if let some gs ← tryApply g (← mkConstWithFreshMVarLevels ``L.Arena.SMono.bind_get) then
        let mut out := []
        for g' in gs do
          if (← g'.isAssigned) then continue
          let (_, g'') ← g'.intro1
          out := out ++ [g'']
        return some out
  if let some l := structLemma? c then
    if let some gs ← tryApply g (← mkConstWithFreshMVarLevels l) then
      let mut out := []
      for g' in gs do
        if (← g'.isAssigned) then continue
        let ty ← instantiateMVars (← g'.getType)
        if ty.isForall then
          let (_, g'') ← g'.intro1
          out := out ++ [g'']
        else if ty.isAppOf ``L.Arena.SMono then out := out ++ [g']
        else if (← isProp ty) then out := out ++ [g']
      return some out
  if (← isMatcher c) then
    let s ← saveState
    try
      let gs ← evalTacticAt (← `(tactic| split)) g
      return some gs
    catch _ => restoreState s
  -- a hypothesis about the function itself (an induction hypothesis)
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let dt ← zetaReduce (← instantiateMVars d.type)
    let (_, _, concl) ← forallMetaTelescopeReducing dt
    let concl ← zetaReduce (← instantiateMVars concl)
    if concl.isAppOf ``L.Arena.SMono && concl.appArg!.getAppFn.constName? == some c then
      if let some gs ← withReducible (tryApply g d.toExpr) then
        let mut rest := []
        for g' in gs do
          unless (← closeSide g') do rest := rest ++ [g']
        return some rest
  let ln := lemmaName c
  if (← getEnv).contains ln then
    if let some gs ← tryApply g (← mkConstWithFreshMVarLevels ln) then
      let mut rest := []
      for g' in gs do
        if (← g'.isAssigned) then continue
        unless (← closeSide g') do rest := rest ++ [g']
      return some rest
  -- unfold a definition without a lemma (never a recursive one: its lemma is missing)
  if let some ci := (← getEnv).find? c then
    if ci.isDefinition && !(← isRecC c) && !(← isMatcher c) then
      let s ← saveState
      try
        let g' ← unfoldTarget g c
        if g' != g then return some [g']
      catch _ => restoreState s
      let s ← saveState
      try
        let g' ← g.deltaTarget (· == c)
        if g' != g then return some [g']
      catch _ => restoreState s
  -- last resort: weak-head reduce the operation
  let op' ← whnfR op
  if op' != op then
    return some [← g.replaceTargetDefEq (Lean.mkApp t.appFn! op')]
  return none

/-- Run `step` to a fixpoint; the goals no rule closes. -/
meta partial def auto (gs : List MVarId) (fuel : Nat := 20000) : TacticM (List MVarId) := do
  let mut todo := gs
  let mut stuck := []
  let mut n := fuel
  while !todo.isEmpty && n > 0 do
    n := n - 1
    let g :: rest := todo | break
    todo := rest
    if ← g.isAssigned then continue
    match ← step g with
    | some gs' => todo := gs' ++ todo
    | none => stuck := stuck ++ [g]
  if n == 0 then
    if let g :: _ := todo then
      logInfo m!"smono_auto: out of fuel at {g}"
  return stuck ++ todo

syntax (name := smonoAuto) "smono_auto" : tactic

@[tactic smonoAuto] meta def evalSmonoAuto : Tactic := fun _ => do
  let gs ← getGoals
  let rest ← auto gs
  setGoals rest

end KnotMonoTac

namespace L.Arena

/-- Every slot of a core record is `SMono`. -/
structure RecSMono (R : CoreFnsA) : Prop where
  whnfCore : ∀ c d e, SMono (R.whnfCore c d e)
  whnf : ∀ d e, SMono (R.whnf d e)
  infer : ∀ d e, SMono (R.infer d e)
  defeq : ∀ d a b, SMono (R.defeq d a b)
  defeqE : ∀ d a b, SMono (R.defeqE d a b)
  inferIO : ∀ d e, SMono (R.inferIO d e)

theorem RecSMono.ioView {R : CoreFnsA} (h : RecSMono R) : RecSMono R.ioView :=
  ⟨h.whnfCore, h.whnf, h.inferIO, h.defeq, h.defeqE, h.inferIO⟩

namespace KM
theorem ConRon.Arena.CoreFnsA.whnfCore {R : CoreFnsA} (h : RecSMono R) (c d e) :
    SMono (R.whnfCore c d e) := h.whnfCore c d e
theorem ConRon.Arena.CoreFnsA.whnf {R : CoreFnsA} (h : RecSMono R) (d e) : SMono (R.whnf d e) :=
  h.whnf d e
theorem ConRon.Arena.CoreFnsA.infer {R : CoreFnsA} (h : RecSMono R) (d e) : SMono (R.infer d e) :=
  h.infer d e
theorem ConRon.Arena.CoreFnsA.defeq {R : CoreFnsA} (h : RecSMono R) (d a b) :
    SMono (R.defeq d a b) := h.defeq d a b
theorem ConRon.Arena.CoreFnsA.defeqE {R : CoreFnsA} (h : RecSMono R) (d a b) :
    SMono (R.defeqE d a b) := h.defeqE d a b
theorem ConRon.Arena.CoreFnsA.inferIO {R : CoreFnsA} (h : RecSMono R) (d e) :
    SMono (R.inferIO d e) := h.inferIO d e
end KM

end L.Arena

set_option hygiene false in
/-- A state primitive: run it, split, close each leaf by the store it leaves. -/
macro "smono_prim " f:ident : tactic => `(tactic| (
  intros
  unfold L.Arena.SMono; intro a r a' h
  simp only [$f:ident, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind,
    StateT.run_map, bind_pure_comp] at h
  repeat' split at h
  all_goals first
    | (cases h; exact L.Arena.SExt.refl _)
    | (cases h; exact L.Arena.SExt.of_store rfl)
    | (cases h; exact L.Arena.SExt.intern _ _ _ rfl)
    | (cases h; exact L.Arena.SExt.internBind _ _ _ _ (.inl rfl) _ rfl)
    | (cases h; exact L.Arena.SExt.internBind _ _ _ _ (.inr rfl) _ rfl)
    | (cases h; exact L.Arena.SExt.lss _ _ (ConRon.Arena.EStore.internLevel_ext _ _) (fun _ => rfl))
    | (cases h; exact L.Arena.SExt.lss _ _ (ConRon.Arena.EStore.internLevels_ext _ _) (fun _ => rfl))
    | (cases h; exact L.Arena.SExt.lss _ _ (ConRon.Arena.EStore.internName_ext _ _) (fun _ => rfl))
    | (simp only [StateT.run, StateT.bind, set, StateT.set, pure, StateT.pure, bind, Except.bind,
        MonadStateOf.set, Except.pure] at h
       cases h
       first
         | exact L.Arena.SExt.refl _
         | exact L.Arena.SExt.of_store rfl
         | exact L.Arena.SExt.intern _ _ _ rfl)
    | (exfalso; revert h; simp [ConRon.Arena.fail, StateT.run, StateT.lift, throwThe, MonadExceptOf.throw,
        throw, Function.comp, liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, bind,
        Except.bind]; done)))

namespace KnotMonoTac
open Lean Meta Elab Command Term

/-- Does `t` end in `AM _` (`StateT AState (Except CheckError) _`)? -/
meta def isAM (t : Lean.Expr) : MetaM Bool :=
  forallTelescope t fun _ b => do
    let b ← instantiateMVars b
    if b.isAppOf ``ConRon.Arena.AM then return true
    let b ← whnfR b
    return b.isAppOfArity ``StateT 4 && (b.getArg! 1).isConstOf ``ConRon.Arena.AState

/-- The statement of `KM.f`. -/
meta def stmt (f : Name) : MetaM Lean.Expr := do
  let ci ← getConstInfo f
  let us := ci.levelParams.map mkLevelParam
  forallTelescope ci.type fun xs _ => do
    let rec go (i : Nat) (hs : Array Lean.Expr) : MetaM Lean.Expr := do
      if h : i < xs.size then
        let x := xs[i]
        let xt ← inferType x
        if xt.isConstOf ``ConRon.Arena.CoreFnsA then
          withLocalDeclD `hR (Lean.mkApp (mkConst ``L.Arena.RecSMono) x) fun h => go (i + 1) (hs.push h)
        else if (← isAM xt) && xt.isForall then
          let ht ← forallTelescope xt fun ys _ => do
            mkForallFVars ys (← mkAppM ``L.Arena.SMono #[Lean.mkAppN x ys])
          withLocalDeclD `hg ht fun h => go (i + 1) (hs.push h)
        else go (i + 1) hs
      else
        mkForallFVars (xs ++ hs) (← mkAppM ``L.Arena.SMono #[Lean.mkAppN (mkConst f us) xs])
    go 0 #[]

/-- Does `f` write the state? -/
meta def usesSet (f : Name) : MetaM Bool := do
  let some v := (← getConstInfo f).value? | return false
  return v.getUsedConstants.any fun c =>
    c == ``MonadStateOf.set || c == ``MonadState.set || c == ``StateT.set || c == ``set ||
      c == ``modifyGet || c == ``MonadStateOf.modifyGet || c == ``modify

/-- Is `f` recursive (its unfolding equation mentions it)? -/
meta def isRec (f : Name) : MetaM Bool := do
  let some eq ← getUnfoldEqnFor? f (nonRec := true) | return false
  let ty ← inferType (mkConst eq ((← getConstInfo eq).levelParams.map mkLevelParam))
  forallTelescope ty fun _ b => do
    let some (_, _, rhs) := b.eq? | return false
    return (rhs.find? (·.isConstOf f)).isSome

/-- The proof scripts to try for `KM.f`, in order. -/
meta def scripts (f : Name) (ty : Lean.Expr) : TermElabM (List (TSyntax `tactic)) := do
  let ci ← getConstInfo f
  let fid := mkIdent f
  let mut out := []
  -- a fuel walk (its arms recurse into it, mutually): induction on the fuel; a function recursive
  -- in a `Nat` argument: induction on it, one unfolding (`rw`) per case
  let fi? ← forallTelescope ci.type fun xs _ => xs.findIdxM? fun x => do
    return (← x.fvarId!.getUserName) == `fuel
  let rec_ ← isRec f
  let nats ← forallTelescope ci.type fun xs _ => do
    let mut out := #[]
    for i in [0:xs.size] do
      if (← inferType xs[i]!).isConstOf ``Nat then out := out.push i
    return out
  let m ← forallTelescope ty fun xs _ => pure xs.size
  let names := (List.range m).map fun j => mkIdent (Name.mkSimple s!"a{j}")
  let introT ← `(tactic| intro $(names.toArray)*)
  let mk (fi : Nat) (useRw : Bool) : TermElabM (TSyntax `tactic) := do
    let fuelId := names[fi]!
    let gen := (names.eraseIdx fi).toArray
    let unf ← if useRw then `(tactic| rw [$fid:ident]) else `(tactic| simp only [$fid:ident])
    if gen.isEmpty then
      `(tactic| ($introT:tactic; induction $fuelId:ident with
          | zero => $unf:tactic; smono_auto; done
          | succ _ ih => $unf:tactic; smono_auto; done))
    else
      `(tactic| ($introT:tactic; induction $fuelId:ident generalizing $gen* with
          | zero => $unf:tactic; smono_auto; done
          | succ _ ih => $unf:tactic; smono_auto; done))
  if let some fi := fi? then
    out := out ++ [← mk fi false]
  if rec_ then
    for i in nats do
      if some i != fi? then out := out ++ [← mk i true]
  if rec_ then
    out := out ++ [← `(tactic| (intros; fun_induction $fid:ident <;> (smono_auto; done)))]
  else
    out := out ++ [← `(tactic| (intros; unfold $fid:ident; smono_auto; done))]
  if (← usesSet f) then
    out := out ++ [← `(tactic| (smono_prim $fid; done))]
  return out

/-- State and prove `KM.f`; `false` (and a warning) if no script closes it. -/
meta def derive (f : Name) : TermElabM Bool := do
  let ci ← getConstInfo f
  let ty ← instantiateMVars (← stmt f)
  for tac in ← scripts f ty do
    let s ← saveState
    let ok ← withCurrHeartbeats <| tryCatchRuntimeEx (do
        let msgs ← Core.getMessageLog
        let pf ← withoutErrToSorry do
          let pf ← elabTermEnsuringType (← `(by $tac:tactic)) ty
          synthesizeSyntheticMVarsNoPostponing
          instantiateMVars pf
        if pf.hasMVar || pf.hasSorry then throwError "unsolved"
        if (← Core.getMessageLog).hasErrors && !msgs.hasErrors then throwError "errors"
        addDecl <| .thmDecl { name := lemmaName f, levelParams := ci.levelParams, type := ty, value := pf }
        pure true)
      (fun _ => do s.restore (restoreInfo := true); pure false)
    if ok then return true
  return false

/-- `smono_derive f₁ … fₙ`: state and prove `L.Arena.KM.fᵢ` (an error for one no script closes). -/
syntax (name := smonoDerive) "smono_derive " ident+ : command

@[command_elab smonoDerive] meta def elabSmonoDerive : CommandElab := fun stx => do
  for id in stx[1].getArgs do
    let f ← liftCoreM <| realizeGlobalConstNoOverload id
    unless ← liftTermElabM (derive f) do
      logErrorAt id m!"smono_derive: no script proves KM.{f}"

/-- `smono_try f₁ … fₙ`: as `smono_derive`, a warning for each one no script closes. -/
syntax (name := smonoTry) "smono_try " ident+ : command

@[command_elab smonoTry] meta def elabSmonoTry : CommandElab := fun stx => do
  for id in stx[1].getArgs do
    let f ← liftCoreM <| realizeGlobalConstNoOverload id
    unless ← liftTermElabM (derive f) do
      logWarningAt id m!"smono_try: no script proves KM.{f}"

end KnotMonoTac
