import ConRon.Arena.ExprOps

/-!
# Twin-side frames by composition: what an `ExprOps` walk keeps

`Keeps π op`: every successful run of `op` leaves the projection `π` of the state alone. It is
closed under `bind`, `pure`, `fail`, `if` and `match` (by `split`), so a walk family keeps a
projection by one induction on the fuel, the `succ` case by `keeps_auto`. The walks over the
store and the walk memos keep `cp a = (a.caches, a.pins)`, the per-declaration and global tiers
(`Tiers.lean`). With the L side's text frame (`WriteSets.lean`), a tier relation `X m (cp a)` over
arrays outside a walk's write set survives the walk with no lemma about it (`CoreR.across`,
`PinsR.across`). Lane `scale`'s spike `Spike/TwinKeep.lean`, generalised and automated.
-/

namespace L.Arena

open ConRon.Arena

/-- The checker-tier part of the state an `ExprOps` walk must not touch. -/
def cp (a : AState) : Caches × Pins := (a.caches, a.pins)

/-- Every successful run of `op` keeps `π`. Irreducible, so that `intro` in `keeps_auto` stops
at it. -/
@[irreducible] def Keeps {β α : Type} (π : AState → β) (op : AM α) : Prop :=
  ∀ a r a', op.run a = .ok (r, a') → π a' = π a

section
variable {β : Type} {π : AState → β}

theorem Keeps.pure {α : Type} (x : α) : Keeps π (Pure.pure x : AM α) := by
  unfold Keeps; intro a r a' h; cases h; rfl

theorem Keeps.fail {α : Type} (e : CheckError) : Keeps π (ConRon.Arena.fail e : AM α) := by
  unfold Keeps; intro a r a' h; cases h

theorem Keeps.bind {α γ : Type} {x : AM α} {f : α → AM γ} (hx : Keeps π x)
    (hf : ∀ v, Keeps π (f v)) : Keeps π (x >>= f) := by
  unfold Keeps at *; intro a r a' h
  simp only [StateT.run_bind] at h
  cases h1 : x.run a with
  | error e => rw [h1] at h; cases h
  | ok p =>
    obtain ⟨v, a₁⟩ := p
    rw [h1] at h
    exact (hf v a₁ r a' h).trans (hx a v a₁ h1)

/-- Use a `Keeps` fact on a successful run. -/
theorem Keeps.run {α : Type} {op : AM α} (h : Keeps π op) {a : AState} {r : α} {a' : AState}
    (hr : op.run a = .ok (r, a')) : π a' = π a := by
  unfold Keeps at h; exact h a r a' hr

/-- A run that keeps the projection keeps whatever is computed from it. -/
theorem Keeps.map {γ : Type} (g : β → γ) {α : Type} {op : AM α} (h : Keeps π op) :
    Keeps (fun a => g (π a)) op := by
  unfold Keeps at *; exact fun a r a' hr => by simp only [h a r a' hr]

end

/-- A primitive: read the state, then answer, fail, or write back with only the store or the
memos changed. -/
macro "prim_keeps " d:ident : tactic => `(tactic| (
  unfold Keeps; intro a r a' h
  simp only [$d:ident, StateT.run_bind, StateT.run_get, pure_bind] at h
  repeat' split at h
  all_goals simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
    ConRon.Arena.fail, throwThe, MonadExceptOf.throw] at h
  all_goals first | (cases h; rfl) | (simp [throwThe, throw, Functor.map, Except.map] at h)))


/-! ## The primitives keep `cp` -/

theorem keeps_internNodeE (v : ENodeView) : Keeps cp (internNodeE v) := by prim_keeps internNodeE
theorem keeps_internLamE (ty b : EIdx) : Keeps cp (internLamE ty b) := by prim_keeps internLamE
theorem keeps_internForallEE (ty b : EIdx) : Keeps cp (internForallEE ty b) := by
  prim_keeps internForallEE
theorem keeps_internE (v : ENodeView) : Keeps cp (internE v) := by
  cases v <;> simp only [internE] <;> first | exact keeps_internNodeE _ | exact keeps_internLamE _ _ |
    exact keeps_internForallEE _ _
theorem keeps_view {β : Type} {π : AState → β} (h : EIdx) : Keeps π (view h) := by
  prim_keeps view
theorem keeps_derivedE {β : Type} {π : AState → β} (h : EIdx) : Keeps π (derivedE h) := by unfold Keeps; intro a r a' h; cases h; rfl
theorem keeps_viewApp {β : Type} {π : AState → β} (h : EIdx) : Keeps π (viewApp h) := by unfold Keeps; intro a r a' h; cases h; rfl
theorem keeps_viewBind {β : Type} {π : AState → β} (h : EIdx) : Keeps π (viewBind h) := by unfold Keeps; intro a r a' h; cases h; rfl
theorem keeps_viewLet {β : Type} {π : AState → β} (h : EIdx) : Keeps π (viewLet h) := by unfold Keeps; intro a r a' h; cases h; rfl
theorem keeps_viewProj {β : Type} {π : AState → β} (h : EIdx) : Keeps π (viewProj h) := by unfold Keeps; intro a r a' h; cases h; rfl
theorem keeps_viewBVar {β : Type} {π : AState → β} (h : EIdx) : Keeps π (viewBVar h) := by unfold Keeps; intro a r a' h; cases h; rfl

/-- A projection that does not read the walk memos. -/
def MemoBlind {β : Type} (π : AState → β) : Prop := ∀ a (ms : Memos), π { a with memos := ms } = π a

theorem cp_blind : MemoBlind cp := fun _ _ => rfl

/-- The store, the caches and the pins: what the walks that intern nothing keep. -/
def sp (a : AState) : EStore × Caches × Pins := (a.store, a.caches, a.pins)

theorem sp_blind : MemoBlind sp := fun _ _ => rfl

/-- The walk memos' operations change only `memos`. -/
theorem keeps_liftGet {β : Type} {π : AState → β} (k : EIdx × Nat) : Keeps π (liftGet k) := by unfold Keeps; intro a r a' h; cases h; rfl
theorem keeps_liftSet {β : Type} {π : AState → β} (hπ : MemoBlind π) (k : EIdx × Nat) (v : EIdx) :
    Keeps π (liftSet k v) := by
  unfold Keeps; intro a r a' h; cases h; first | exact hπ _ _ | exact (hπ _ _).trans (hπ _ _)
theorem keeps_liftClear {β : Type} {π : AState → β} (hπ : MemoBlind π) : Keeps π liftClear := by
  unfold Keeps; intro a r a' h; cases h; first | exact hπ _ _ | exact (hπ _ _).trans (hπ _ _)
theorem keeps_inst1Get {β : Type} {π : AState → β} (k : EIdx × Nat) : Keeps π (inst1Get k) := by unfold Keeps; intro a r a' h; cases h; rfl
theorem keeps_inst1Set {β : Type} {π : AState → β} (hπ : MemoBlind π) (k : EIdx × Nat) (v : EIdx) :
    Keeps π (inst1Set k v) := by
  unfold Keeps; intro a r a' h; cases h; first | exact hπ _ _ | exact (hπ _ _).trans (hπ _ _)
theorem keeps_inst1Clear {β : Type} {π : AState → β} (hπ : MemoBlind π) : Keeps π inst1Clear := by
  unfold Keeps; intro a r a' h; cases h; first | exact hπ _ _ | exact (hπ _ _).trans (hπ _ _)
theorem keeps_bvarBGet {β : Type} {π : AState → β} (k : EIdx) : Keeps π (bvarBGet k) := by unfold Keeps; intro a r a' h; cases h; rfl
theorem keeps_bvarBSet {β : Type} {π : AState → β} (hπ : MemoBlind π) (k : EIdx) (v : Nat) :
    Keeps π (bvarBSet k v) := by
  unfold Keeps; intro a r a' h; cases h; first | exact hπ _ _ | exact (hπ _ _).trans (hπ _ _)
theorem keeps_bvarBClear {β : Type} {π : AState → β} (hπ : MemoBlind π) : Keeps π bvarBClear := by
  unfold Keeps; intro a r a' h; cases h; first | exact hπ _ _ | exact (hπ _ _).trans (hπ _ _)
theorem keeps_fvarBGet {β : Type} {π : AState → β} (k : EIdx) : Keeps π (fvarBGet k) := by unfold Keeps; intro a r a' h; cases h; rfl
theorem keeps_fvarBSet {β : Type} {π : AState → β} (hπ : MemoBlind π) (k : EIdx) (v : Nat) :
    Keeps π (fvarBSet k v) := by
  unfold Keeps; intro a r a' h; cases h; first | exact hπ _ _ | exact (hπ _ _).trans (hπ _ _)
theorem keeps_fvarBClear {β : Type} {π : AState → β} (hπ : MemoBlind π) : Keeps π fvarBClear := by
  unfold Keeps; intro a r a' h; cases h; first | exact hπ _ _ | exact (hπ _ _).trans (hπ _ _)

/-- **One step of a walk family's `succ` case**: split binds, `if`s and `match`es, unfold the
named arms, close leaves by the primitives and the induction hypothesis `ih`. -/
macro "keeps_auto " "[" arms:ident,* "]" " using " ih:term ", " hb:term : tactic => `(tactic| (
  repeat' (first
    | exact Keeps.pure _ | exact Keeps.fail _ | exact $ih _ _ | exact $ih _
    | exact keeps_internE _ | exact keeps_internLamE _ _ | exact keeps_internForallEE _ _
    | exact keeps_view _ | exact keeps_derivedE _ | exact keeps_viewApp _ | exact keeps_viewBind _
    | exact keeps_viewLet _ | exact keeps_viewProj _ | exact keeps_viewBVar _
    | exact keeps_liftGet _ | exact keeps_liftSet $hb _ _ | exact keeps_inst1Get _
    | exact keeps_inst1Set $hb _ _ | exact keeps_bvarBGet _ | exact keeps_bvarBSet $hb _ _
    | exact keeps_fvarBGet _ | exact keeps_fvarBSet $hb _ _ | exact Keeps.fail _
    | (unfold failDanglingE) | (unfold internBVarE) | (unfold internBindE) | (dsimp only)
    | with_reducible apply Keeps.bind | intro _ | split $[| unfold $arms:ident]* )))

/-! ## The walk families keep `cp` -/

theorem keeps_inst1ArmBVar (v h : EIdx) (d : Nat) : Keeps cp (instantiate1ArmBVar v h d) := by
  unfold instantiate1ArmBVar; keeps_auto [instantiate1ArmBVar] using Keeps.pure (π := cp), cp_blind

/-- **`instantiate1Go` keeps `(caches, pins)`**, at every fuel. -/
theorem keeps_inst1Go (v : EIdx) (F : Nat) : ∀ h d, Keeps cp (instantiate1Go v F h d) := by
  induction F with
  | zero => intro h d; rw [instantiate1Go_zero]; exact Keeps.fail _
  | succ F ih =>
    intro h d; rw [instantiate1Go_succ]
    keeps_auto [instantiate1ArmApp, instantiate1ArmBind, instantiate1ArmLet, instantiate1ArmProj] using ih, cp_blind
    all_goals exact keeps_inst1ArmBVar _ _ _

theorem keeps_inst1Fast (F : Nat) (e v : EIdx) (d : Nat) : Keeps cp (instantiate1Fast F e v d) := by
  unfold instantiate1Fast
  exact Keeps.bind (keeps_inst1Clear cp_blind) fun _ => Keeps.bind (keeps_inst1Go v F e d) fun _ =>
    Keeps.bind (keeps_inst1Clear cp_blind) fun _ => Keeps.pure _

/-- **`liftLooseBVarsGo` keeps `(caches, pins)`.** -/
theorem keeps_liftGo (amount F : Nat) : ∀ h c, Keeps cp (liftLooseBVarsGo amount F h c) := by
  induction F with
  | zero => intro h c; rw [liftLooseBVarsGo_zero]; exact Keeps.fail _
  | succ F ih =>
    intro h c; rw [liftLooseBVarsGo_succ]
    keeps_auto [liftArmApp, liftArmLam, liftArmForallE, liftArmLet, liftArmProj] using ih, cp_blind

theorem keeps_liftFast (F amount c : Nat) (e : EIdx) : Keeps cp (liftLooseBVarsFast F amount c e) := by
  unfold liftLooseBVarsFast
  exact Keeps.bind (keeps_liftClear cp_blind) fun _ => Keeps.bind (keeps_liftGo amount F e c) fun _ =>
    Keeps.bind (keeps_liftClear cp_blind) fun _ => Keeps.pure _

/-- **`bvarBoundGo` keeps the store, the caches and the pins** (it interns nothing). -/
theorem keeps_bvarBoundGo (F : Nat) : ∀ h, Keeps sp (bvarBoundGo F h) := by
  induction F with
  | zero => intro h; rw [bvarBoundGo_zero]; exact Keeps.fail _
  | succ F ih =>
    intro h; rw [bvarBoundGo_succ]
    keeps_auto [bvarBoundArmApp, bvarBoundArmBind, bvarBoundArmLet] using ih, sp_blind

theorem keeps_bvarBoundMemo (F : Nat) (e : EIdx) : Keeps sp (bvarBoundMemo F e) := by
  unfold bvarBoundMemo
  exact Keeps.bind (keeps_bvarBClear sp_blind) fun _ => Keeps.bind (keeps_bvarBoundGo F e) fun _ =>
    Keeps.bind (keeps_bvarBClear sp_blind) fun _ => Keeps.pure _

/-- **`fvarRangeGo` keeps the store, the caches and the pins.** -/
theorem keeps_fvarRangeGo (F : Nat) : ∀ h, Keeps sp (fvarRangeGo F h) := by
  induction F with
  | zero => intro h; rw [fvarRangeGo_zero]; exact Keeps.fail _
  | succ F ih =>
    intro h; rw [fvarRangeGo_succ]
    keeps_auto [fvarRangeArmApp, fvarRangeArmBind, fvarRangeArmLet] using ih, sp_blind

theorem keeps_fvarRangeMemo (F : Nat) (e : EIdx) : Keeps sp (fvarRangeMemo F e) := by
  unfold fvarRangeMemo
  exact Keeps.bind (keeps_fvarBClear sp_blind) fun _ => Keeps.bind (keeps_fvarRangeGo F e) fun _ =>
    Keeps.bind (keeps_fvarBClear sp_blind) fun _ => Keeps.pure _

end L.Arena
