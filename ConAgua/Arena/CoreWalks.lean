import ConAgua.Arena.WhnfCoreApp
import ConAgua.Arena.InstListRefine
import ConAgua.Arena.ArRangeRefine
import ConAgua.Arena.HasFvarRefine
import ConAgua.Arena.BvarBRefine
import ConAgua.Arena.Inst1Refine
import ConAgua.Arena.WriteSets

/-!
# The verified walks as the core's callees (lane `whnf2`)

Lane `exprops4`'s walks (`instantiateList`, `abstract1`, `abstractRange`, `hasFvar`,
`looseBVarsBounded`) and lane `exprops`' `instantiate1` refine their twins at exactly
`coreWalkFuel` (helper `whnf2-walks`: an L depth counter in every walk, ROADMAP §3 (b)) under the
walk tiers (`ArenaD`, `ArenaL`, `ArenaA`). Here they are lifted to `CoreS`:

* **The twin side** keeps `cpl` (caches, pins, level store): a walk interns expression nodes and
  touches its own memos only (`Keeps cpl`, by the `Keeps.lean` recipe with `cpl`'s primitives).
* **The memory side**: every walk writes below array 64 and `CTL` word 64 (`WriteSets.lean`), so
  the upper tiers, the stack and the binder stack survive by their frames (`CoreS.of_walk`).
* **The walk memos**: `instLC` (array 50) and `abs1C` (array 49) are cleared on the walk's entry,
  so the twin's map is irrelevant: the run from `a₀` is the run from `a₀` with the memo replaced by
  the map `CoreMemos` provides (`*_memo_irrel`). The walk's own post gives that memo back; the
  other is framed.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## The walks keep `cpl` -/

theorem cplW_blind : MemoBlind cpl := fun _ _ => rfl

theorem EStore.lss_internBindW (st : EStore) (tag : UInt32) (ty b : EIdx) :
    (st.internBind tag ty b).1.lss = st.lss := by
  unfold EStore.internBind
  dsimp only
  repeat' split
  all_goals rfl

theorem keepsW_internLamE (ty b : EIdx) : Keeps cpl (internLamE ty b) := by
  unfold Keeps; intro a r a' h
  simp only [internLamE, StateT.run_bind, StateT.run_get, pure_bind] at h
  repeat' split at h
  all_goals simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
    ConRon.Arena.fail, throwThe, MonadExceptOf.throw] at h
  all_goals first
    | (cases h; rfl)
    | (cases h; simp only [cpl, EStore.internLam, EStore.lss_internBindW])
    | (simp [throwThe, Functor.map, Except.map] at h)

theorem keepsW_internForallEE (ty b : EIdx) : Keeps cpl (internForallEE ty b) := by
  unfold Keeps; intro a r a' h
  simp only [internForallEE, StateT.run_bind, StateT.run_get, pure_bind] at h
  repeat' split at h
  all_goals simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
    ConRon.Arena.fail, throwThe, MonadExceptOf.throw] at h
  all_goals first
    | (cases h; rfl)
    | (cases h; simp only [cpl, EStore.internForallE, EStore.lss_internBindW])
    | (simp [throwThe, Functor.map, Except.map] at h)

theorem keepsW_internE (v : ENodeView) : Keeps cpl (internE v) := by
  cases v <;> simp only [internE] <;>
    first | exact keeps_cpl_internNodeE _ | exact keepsW_internLamE _ _ | exact keepsW_internForallEE _ _

theorem keepsW_instLGet {β : Type} {π : AState → β} (k : EIdx × Nat) : Keeps π (instLGet k) := by
  unfold Keeps; intro a r a' h; cases h; rfl
theorem keepsW_instLSet {β : Type} {π : AState → β} (hπ : MemoBlind π) (k : EIdx × Nat) (v : EIdx) :
    Keeps π (instLSet k v) := by
  unfold Keeps; intro a r a' h; cases h; first | exact hπ _ _ | exact (hπ _ _).trans (hπ _ _)
theorem keepsW_instLClear {β : Type} {π : AState → β} (hπ : MemoBlind π) : Keeps π instLClear := by
  unfold Keeps; intro a r a' h; cases h; first | exact hπ _ _ | exact (hπ _ _).trans (hπ _ _)
theorem keepsW_abs1Get {β : Type} {π : AState → β} (k : EIdx × Nat) : Keeps π (abs1Get k) := by
  unfold Keeps; intro a r a' h; cases h; rfl
theorem keepsW_abs1Set {β : Type} {π : AState → β} (hπ : MemoBlind π) (k : EIdx × Nat) (v : EIdx) :
    Keeps π (abs1Set k v) := by
  unfold Keeps; intro a r a' h; cases h; first | exact hπ _ _ | exact (hπ _ _).trans (hπ _ _)
theorem keepsW_abs1Clear {β : Type} {π : AState → β} (hπ : MemoBlind π) : Keeps π abs1Clear := by
  unfold Keeps; intro a r a' h; cases h; first | exact hπ _ _ | exact (hπ _ _).trans (hπ _ _)

theorem keepsW_viewFVarIdx {β : Type} {π : AState → β} (h : EIdx) : Keeps π (viewFVarIdx h) := by
  unfold Keeps; intro a r a' h; cases h; rfl

/-- `sp` determines `cpl`. -/
theorem Keeps.cplW_of_sp {α : Type} {op : AM α} (h : Keeps sp op) : Keeps cpl op :=
  h.map fun x => (x.2.1, x.2.2, x.1.lss)

theorem keepsW_fvarB (F : Nat) (e : EIdx) : Keeps cpl (fvarB F e) := by
  unfold fvarB
  refine Keeps.bind (keeps_derivedE _) fun x => ?_
  by_cases hc : ((ConLeche.fvarOfData x).toNat == ConLeche.satRange) = true
  · simp only [hc, ↓reduceIte]; exact (keeps_fvarRangeMemo F e).cplW_of_sp
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]; exact Keeps.pure _

theorem keepsW_bvarB (F : Nat) (e : EIdx) : Keeps cpl (bvarB F e) := by
  unfold bvarB
  refine Keeps.bind (keeps_derivedE _) fun x => ?_
  by_cases hc : ((ConLeche.bvarOfData x).toNat == ConLeche.satRange) = true
  · simp only [hc, ↓reduceIte]; exact (keeps_bvarBoundMemo F e).cplW_of_sp
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]; exact Keeps.pure _

/-- **One step of a walk family's `succ` case, for `cpl`** (`keeps_auto` with `cpl`'s primitives). -/
macro "keepsL_auto " "[" arms:ident,* "]" " using " ih:term : tactic => `(tactic| (
  repeat' (first
    | exact Keeps.pure _ | exact Keeps.fail _ | exact $ih _ _
    | exact keepsW_internE _ | exact keepsW_internLamE _ _ | exact keepsW_internForallEE _ _
    | exact keeps_view _ | exact keeps_derivedE _ | exact keeps_viewApp _ | exact keeps_viewBind _
    | exact keeps_viewLet _ | exact keeps_viewProj _ | exact keeps_viewBVar _
    | with_reducible exact keeps_inst1Get _ | with_reducible exact keeps_inst1Set cplW_blind _ _
    | with_reducible exact keepsW_instLGet _ | with_reducible exact keepsW_instLSet cplW_blind _ _
    | with_reducible exact keepsW_abs1Get _ | with_reducible exact keepsW_abs1Set cplW_blind _ _
    | with_reducible exact keepsW_fvarB _ _ | with_reducible exact keepsW_viewFVarIdx _
    | (unfold internRebuiltApp) | (unfold internRebuiltBind) | (unfold internRebuiltLetE)
    | (unfold internRebuiltProj) | (unfold internAppE) | (unfold internLetEE) | (unfold internProjE)
    | (unfold failDanglingE) | (unfold internBVarE) | (unfold internBindE) | (dsimp only)
    | with_reducible apply Keeps.bind | intro _ | split $[| unfold $arms:ident]* )))

theorem keepsW_inst1Go (v : EIdx) (F : Nat) : ∀ h d, Keeps cpl (instantiate1Go v F h d) := by
  induction F with
  | zero => intro h d; rw [instantiate1Go_zero]; exact Keeps.fail _
  | succ F ih =>
    intro h d; rw [instantiate1Go_succ]
    keepsL_auto [instantiate1ArmApp, instantiate1ArmBind, instantiate1ArmLet, instantiate1ArmProj,
      instantiate1ArmBVar] using ih

theorem keepsW_inst1Fast (F : Nat) (e v : EIdx) (d : Nat) :
    Keeps cpl (instantiate1Fast F e v d) := by
  unfold instantiate1Fast
  exact Keeps.bind (keeps_inst1Clear cplW_blind) fun _ => Keeps.bind (keepsW_inst1Go v F e d)
    fun _ => Keeps.bind (keeps_inst1Clear cplW_blind) fun _ => Keeps.pure _

theorem keepsW_instList (F : Nat) :
    (∀ vs h d, Keeps cpl (instantiateList vs F h d)) ∧
      (∀ vs h d, Keeps cpl (instantiateListGo vs F h d)) := by
  induction F with
  | zero =>
    exact ⟨fun vs h d => by rw [instantiateList_zero]; exact Keeps.fail _,
      fun vs h d => by rw [instantiateListGo_zero]; exact Keeps.fail _⟩
  | succ F ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨fun vs h d => ?_, fun vs h d => ?_⟩
    · rw [instantiateList_succ]
      keepsL_auto [instListCutoff, instListArmApp, instListArmBind, instListArmLet,
        instListArmProj, instListArmBVar] using Keeps.pure
      all_goals exact ih1 _ _ _
    · rw [instantiateListGo_succ]
      keepsL_auto [instListCutoff, instListGoArmApp, instListGoArmBind, instListGoArmLet,
        instListGoArmProj] using Keeps.pure
      all_goals first | exact ih1 _ _ _ | exact ih2 _ _ _

theorem keepsW_instListFast (F : Nat) (e : EIdx) (vs : Array EIdx) (d : Nat) :
    Keeps cpl (instantiateListFast F e vs d) := by
  unfold instantiateListFast
  exact Keeps.bind (keepsW_instLClear cplW_blind) fun _ =>
    Keeps.bind ((keepsW_instList F).2 vs e d) fun _ =>
      Keeps.bind (keepsW_instLClear cplW_blind) fun _ => Keeps.pure _

theorem keepsW_abs1Go (d F : Nat) : ∀ h k, Keeps cpl (abstract1Go d F h k) := by
  induction F with
  | zero => intro h k; rw [abstract1Go]; exact Keeps.fail _
  | succ F ih =>
    intro h k; rw [abstract1Go]
    keepsL_auto [abstract1ArmApp, abstract1ArmBind, abstract1ArmLet, abstract1ArmProj,
      abstract1ArmFVar] using ih

theorem keepsW_abs1Fast (F : Nat) (e : EIdx) (d k : Nat) :
    Keeps cpl (abstract1Fast F e d k) := by
  unfold abstract1Fast
  exact Keeps.bind (keepsW_abs1Clear cplW_blind) fun _ => Keeps.bind (keepsW_abs1Go d F e k)
    fun _ => Keeps.bind (keepsW_abs1Clear cplW_blind) fun _ => Keeps.pure _

theorem keepsW_arGo (d k F : Nat) : ∀ h c, Keeps cpl (abstractRangeGo d k F h c) := by
  induction F with
  | zero => intro h c; rw [abstractRangeGo_zero]; exact Keeps.fail _
  | succ F ih =>
    intro h c; rw [abstractRangeGo_succ]
    keepsL_auto [absRangeGoArmApp, absRangeGoArmBind, absRangeGoArmLet, absRangeGoArmProj, absRangeArmFVar]
      using ih

theorem keepsW_arFast (F : Nat) (e : EIdx) (d k c : Nat) :
    Keeps cpl (abstractRangeFast F e d k c) := by
  unfold abstractRangeFast
  keepsL_auto [] using keepsW_arGo d k F
  all_goals first | exact keepsW_abs1Clear cplW_blind | exact keepsW_arGo _ _ _ _ _

end L.Arena
