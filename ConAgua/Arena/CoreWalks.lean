import ConAgua.Arena.WhnfCoreApp
import ConAgua.Arena.InstListRefine
import ConAgua.Arena.ArRangeRefine
import ConAgua.Arena.HasFvarRefine
import ConAgua.Arena.BvarBRefine
import ConAgua.Arena.Inst1Refine
import ConAgua.Arena.WriteSets
import ConAgua.Arena.WhnfIota
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# The verified walks as the core's callees (lane `whnf2`)

Lane `exprops4`'s walks (`instantiateList`, `abstract1`, `abstractRange`, `hasFvar`,
`looseBVarsBounded`) and lane `exprops`' `instantiate1` refine their twins at exactly
`coreWalkFuel` (helper `whnf2-walks`: an L depth counter in every walk, decremented where the twin decrements its fuel) under the
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

set_option experimental.vcgen true

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

/-! ## `CoreS` across a walk -/

/-- **`CoreS` across a walk**: the walk tier from the walk's own theorem, the walk memos from its
post and frame (`hmem`), everything else by the frame below 64 and the twin's `cpl`. -/
theorem CoreS.of_walk {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} {A : List ArrId} {C : List Word}
    (hS : CoreS dn m a vis fe M eb) (hD : ArenaD m' a') (hk : cpl a' = cpl a)
    (hf : MemFrame A C m m') (hA : ∀ b ∈ A, b < 64 ∨ (256 ≤ b ∧ b < 320)) (hC : ∀ x ∈ C, x.toNat < 64)
    (hmem : CoreMemos m') (hP : POOL ∉ A := by decide) (hP0 : (0 : Word) ∉ C := by decide)
    (hscA : SOREC ∉ A ∧ CREC ∉ A ∧ SOREC + 256 ∉ A ∧ CREC + 256 ∉ A := by decide)
    (hscC : (1 : Word) ∉ C ∧ (16 : Word) ∉ C ∧ (17 : Word) ∉ C ∧ (18 : Word) ∉ C ∧ (19 : Word) ∉ C :=
      by decide) (hLv : LvlFree C := by lvl_free) (hP1 : POOL1 ∉ A := by decide)
    (hPT : PT0 ∉ A := by decide) :
    CoreS dn m' a' vis fe M eb ∧ StackKept m m' := by
  simp only [cpl, Prod.mk.injEq] at hk
  obtain ⟨hc, hp, hl⟩ := hk
  have hspn : m'.arr64 SPN = m.arr64 SPN :=
    hf.1 SPN (fun h => absurd (hA _ h) (by decide)) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 :=
    hf.2.1 136 (fun h => absurd (hC _ h) (by decide))
  refine ⟨⟨hD, ?_, ?_, hS.env.frame (.of_low hA (by decide) (by decide)) (.of_lt hC (by decide)) hf (.of_lowT hA), ?_, ?_, ?_,
    hf.2.2.1 EREC ▸ hS.erec, hf.2.2.1 SPN ▸ hS.spn, hmem, hf.2.2.1 145 ▸ hS.bstk,
    hS.den.of_arena hS.arena.1 hD.1 hc hp hl hf hscA hscC, hS.mode.frame hf hP0 hscC.1⟩,
    StackKept.of_frame hf
      ⟨fun h => absurd (hA _ h) (by decide), fun h => absurd (hA _ h) (by decide), hP⟩
      ⟨fun h => absurd (hC _ h) (by decide), fun h => absurd (hC _ h) (by decide), hP0⟩ hLv hP1 hPT⟩
  · rw [hc]; exact hS.core.frame (.of_low hA (by decide) (by decide)) (.of_lt hC (by decide)) hf
  · rw [hp]; exact hS.pins.congr (hf.1 PINS (fun h => absurd (hA _ h) (by decide)) (by decide))
  · intro h l e; rw [hc] at e; have := hS.readL h l e; simp only [EStore.ls] at this ⊢; rw [hl]
    exact this
  · intro h l e; rw [hc] at e; have := hS.readLs h l e; rw [hl]; exact this
  · rw [hl]; exact hS.nwf

theorem CoreSpec.zeroW {α : Type} [Inhabited α] {p : Prog} {f : FnName} {fd : FunDecl}
    (hf : p.lookup f = some fd) (args : List Word) (T : AM α) (dec : List Word → α) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb : Word) (ok : List Word → Prop) :
    CoreSpec p 0 f args T dec s₀ a₀ dn vis fe MM eb ok := by
  unfold CoreSpec
  rw [invoke_eq _ hf]
  simp only [callFn]
  vcgen [exec] <;> grind

/-- Runs that agree give the same `AM` readings. -/
theorem AM.readings {α : Type} [Inhabited α] {x : AM α} {a b : AState} (h : x.run a = x.run b)
    (hok : AM.ok x b) : AM.ok x a ∧ AM.st x a = AM.st x b ∧ AM.res x a = AM.res x b := by
  have := AM.run_of_ok _ _ hok
  rw [← h] at this
  obtain ⟨h1, h2, h3⟩ := AM.of_run_ok _ _ _ _ this
  exact ⟨h1, h2, h3⟩

/-- `ArenaD` does not read the memos `instLC`, `abs1C`. -/
theorem ArenaD.memo_irrel {m : Mem} {a : AState} (h : ArenaD m a) (X Y : Std.HashMap (EIdx × Nat) EIdx) :
    ArenaD m { a with memos := { a.memos with instLC := X, abs1C := Y } } := by
  obtain ⟨hR, hD⟩ := h
  exact ⟨⟨hR.lit, hR.app, hR.sort, hR.const, hR.letE, hR.bvar, hR.fvar, hR.lam, hR.forallE, hR.proj,
    hR.zero, hR.succ, hR.max, hR.imax, hR.param, hR.ls, hR.nanon, hR.nstr, hR.nnum,
    ⟨hR.memos.bvar, hR.memos.lift, hR.memos.inst1, hR.memos.fvar⟩, hR.zeroHp, hR.paramHp,
    hR.succHp, hR.maxHp, hR.imaxHp, hR.lsHp, hR.sortLp, hR.constLp, hR.fvarLp⟩,
    DerR.of_store _ _ _ hD rfl⟩

/-- The abstraction memo's well-formedness across a writer that avoids it. -/
theorem coreAb_frame {A : List ArrId} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : (49 : ArrId) ∉ A) (hC : (48 : Word) ∉ C) (h : CoreMemos m) :
    ∃ mp : Std.HashMap (EIdx × Nat) EIdx, MemoRG coreAbSch lfKey decE m' mp :=
  let ⟨mp, hm⟩ := h.2.1; ⟨mp, memoRG_frame coreAbSch coreAbSch_wf lfKey decE A C hA hC m m' hf mp hm⟩

theorem coreIl_frame {A : List ArrId} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : (50 : ArrId) ∉ A) (hC : (50 : Word) ∉ C) (h : CoreMemos m) :
    ∃ mp : Std.HashMap (EIdx × Nat) EIdx, MemoRG coreIlSch lfKey decE m' mp :=
  let ⟨mp, hm⟩ := h.1; ⟨mp, memoRG_frame coreIlSch coreIlSch_wf lfKey decE A C hA hC m m' hf mp hm⟩

theorem lt64_of_all {C : List Word} (h : C.all (fun x => decide (x.toNat < 64)) = true) :
    ∀ x ∈ C, x.toNat < 64 := fun x hx => by
  have := List.all_eq_true.mp h x hx; simpa using this

theorem lt64A_of_all {A : List ArrId}
    (h : A.all (fun b => decide (b < 64 ∨ (256 ≤ b ∧ b < 320))) = true) :
    ∀ b ∈ A, b < 64 ∨ (256 ≤ b ∧ b < 320) := fun b hb => by
  have := List.all_eq_true.mp h b hb; simpa using this

/-! ## The callees -/

section bridges
variable {p : Prog}

/-- **`inst_list` refines `instantiateListFast coreWalkFuel` under `CoreS`** (`InstListOK`, the
stub of `WhnfCallees`). -/
theorem instListOK_core (hp : InstListProg p) (he : p.lookup "inst_list" = some instListL) :
    InstListOK p := by
  intro n s₀ a₀ dn vis fe M eb e off cnt d xs hS hE hsp htop
  cases n with
  | zero => exact CoreSpec.zeroW he _ _ _ _ _ _ _ _ _ _ _
  | succ n =>
  obtain ⟨mp, hmp⟩ := hS.memos.1
  have hrun : (instantiateListFast coreWalkFuel (decE e) xs d.toNat).run a₀ =
      (instantiateListFast coreWalkFuel (decE e) xs d.toNat).run
        { a₀ with memos := { a₀.memos with instLC := mp } } := rfl
  have hA : ArenaL s₀.mem { a₀ with memos := { a₀.memos with instLC := mp } } :=
    ⟨hS.arena.memo_irrel mp a₀.memos.abs1C, hmp⟩
  have hbd : off.toNat + cnt.toNat < 2 ^ 64 := by have := hsp.bound; have := hS.spn; omega
  unfold CoreSpec
  apply L.M.triple_of_run
  intro s r s' hs hr
  obtain ⟨hloc, hok, hA', hres, -, hw⟩ := L.M.of_run (P := fun s => s = s₀) hs hr
    (instList_refines p hp he n s₀ _ hA e off cnt d xs hsp hbd hE)
  obtain ⟨hf, -⟩ := L.M.of_run (P := fun s => s = s₀) hs hr
    (invoke_memFrame (hp.closed he) (n + 1) (by decide) _ s₀)
  subst hs
  obtain ⟨hok, e2, e3⟩ := AM.readings hrun hok
  rw [← e2] at hA'; rw [← e3] at hres
  have hk := Keeps.run (keepsW_instListFast coreWalkFuel (decE e) xs d.toNat) (AM.run_of_ok _ _ hok)
  obtain ⟨hS', hSt⟩ := hS.of_walk hA'.1 hk hf (lt64A_of_all rfl) (lt64_of_all rfl)
    ⟨⟨_, hA'.2⟩, coreAb_frame hf (by decide) (by decide) hS.memos, hS.memos.2.2.frame hf (by decide) (by decide)⟩
  exact ⟨hloc, hok, ⟨M, hS', KeptAll.refl _ _, hSt⟩, hres, hw⟩

/-- **`inst_entry` refines `instantiate1Fast coreWalkFuel` under `CoreS`** at either of its names
(`inst_entry`, the walk's; `inst1`, the core's call sites: one `FunDecl` at two names). -/
theorem inst1_core (hp : InstProg p) (he : p.lookup "inst_entry" = some instEntry)
    (hle : p.lookup "lift_entry" = some liftEntry) (f : FnName) (hf : p.lookup f = some instEntry) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
      (M : ModeMaps) (eb e v d : Word), CoreS dn s₀.mem a₀ vis fe M eb → HW e →
      CoreSpec p n f [e, v, d] (instantiate1Fast coreWalkFuel (decE e) (decE v) d.toNat) decH
        s₀ a₀ dn vis fe M eb := by
  intro n s₀ a₀ dn vis fe M eb e v d hS hE
  cases n with
  | zero => exact CoreSpec.zeroW hf _ _ _ _ _ _ _ _ _ _ _
  | succ n =>
  unfold CoreSpec
  have hinv : invoke p (exec p (n + 1)) f [e, v, d] = invoke p (exec p (n + 1)) "inst_entry" [e, v, d] := by
    rw [invoke_eq _ hf, invoke_eq _ he]
  rw [hinv]
  apply L.M.triple_of_run
  intro s r s' hs hr
  obtain ⟨hloc, hok, hD', hres, hw⟩ := L.M.of_run (P := fun s => s = s₀) hs hr
    (instEntry_refines p hp he n s₀ a₀ hS.arena e v d hE)
  obtain ⟨hf', -⟩ := L.M.of_run (P := fun s => s = s₀) hs hr
    (invoke_memFrame (hp.closed he hle) (n + 1) (by decide) _ s₀)
  subst hs
  have hk := Keeps.run (keepsW_inst1Fast coreWalkFuel (decE e) (decE v) d.toNat) (AM.run_of_ok _ _ hok)
  obtain ⟨hS', hSt⟩ := hS.of_walk hD' hk hf' (lt64A_of_all rfl) (lt64_of_all rfl)
    (hS.memos.frame hf' (by decide) (by decide))
  exact ⟨hloc, hok, ⟨M, hS', KeptAll.refl _ _, hSt⟩, hres, hw⟩

/-- `abs_entry` under `CoreS` (lane `defeq`'s `Abstract1OK`). -/
theorem abs1_core (hp : AbsProg p) (he : p.lookup "abs_entry" = some absEntry) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
      (M : ModeMaps) (eb e d k : Word), CoreS dn s₀.mem a₀ vis fe M eb → HW e →
      CoreSpec p n "abs_entry" [e, d, k] (abstract1Fast coreWalkFuel (decE e) d.toNat k.toNat) decH
        s₀ a₀ dn vis fe M eb := by
  intro n s₀ a₀ dn vis fe M eb e d k hS hE
  cases n with
  | zero => exact CoreSpec.zeroW he _ _ _ _ _ _ _ _ _ _ _
  | succ n =>
  obtain ⟨mp, hmp⟩ := hS.memos.2.1
  have hrun : (abstract1Fast coreWalkFuel (decE e) d.toNat k.toNat).run a₀ =
      (abstract1Fast coreWalkFuel (decE e) d.toNat k.toNat).run
        { a₀ with memos := { a₀.memos with abs1C := mp } } := rfl
  have hA : ArenaA s₀.mem { a₀ with memos := { a₀.memos with abs1C := mp } } :=
    ⟨hS.arena.memo_irrel a₀.memos.instLC mp, hmp⟩
  unfold CoreSpec
  apply L.M.triple_of_run
  intro s r s' hs hr
  obtain ⟨hloc, hok, hA', hres, hw⟩ := L.M.of_run (P := fun s => s = s₀) hs hr
    (absEntry_refines p hp he n s₀ _ hA e d k hE)
  obtain ⟨hf, -⟩ := L.M.of_run (P := fun s => s = s₀) hs hr
    (invoke_memFrame (hp.closed he) (n + 1) (by decide) _ s₀)
  subst hs
  obtain ⟨hok, e2, e3⟩ := AM.readings hrun hok
  rw [← e2] at hA'; rw [← e3] at hres
  have hk := Keeps.run (keepsW_abs1Fast coreWalkFuel (decE e) d.toNat k.toNat) (AM.run_of_ok _ _ hok)
  obtain ⟨hS', hSt⟩ := hS.of_walk hA'.1 hk hf (lt64A_of_all rfl) (lt64_of_all rfl)
    ⟨coreIl_frame hf (by decide) (by decide) hS.memos, ⟨_, hA'.2⟩, hS.memos.2.2.frame hf (by decide) (by decide)⟩
  exact ⟨hloc, hok, ⟨M, hS', KeptAll.refl _ _, hSt⟩, hres, hw⟩

/-- `ar_entry` under `CoreS` (lane `defeq`'s `AbstractRangeOK`). -/
theorem absRange_core (hp : ArProg p) (he : p.lookup "ar_entry" = some arEntry) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
      (M : ModeMaps) (eb e d k c : Word), CoreS dn s₀.mem a₀ vis fe M eb → HW e →
      CoreSpec p n "ar_entry" [e, d, k, c]
        (abstractRangeFast coreWalkFuel (decE e) d.toNat k.toNat c.toNat) decH s₀ a₀ dn vis fe M eb := by
  intro n s₀ a₀ dn vis fe M eb e d k c hS hE
  cases n with
  | zero => exact CoreSpec.zeroW he _ _ _ _ _ _ _ _ _ _ _
  | succ n =>
  obtain ⟨mp, hmp⟩ := hS.memos.2.1
  by_cases hk0 : k.toNat = 0
  · -- `k = 0`: the twin returns `e` and changes nothing
    have hA : ArenaA s₀.mem { a₀ with memos := { a₀.memos with abs1C := mp } } :=
      ⟨hS.arena.memo_irrel a₀.memos.instLC mp, hmp⟩
    have hrun : (abstractRangeFast coreWalkFuel (decE e) d.toNat k.toNat c.toNat).run a₀ =
        .ok (decE e, a₀) := by simp [abstractRangeFast, hk0]; rfl
    have hrun1 : (abstractRangeFast coreWalkFuel (decE e) d.toNat k.toNat c.toNat).run
        { a₀ with memos := { a₀.memos with abs1C := mp } } =
        .ok (decE e, { a₀ with memos := { a₀.memos with abs1C := mp } }) := by
      simp [abstractRangeFast, hk0]; rfl
    obtain ⟨ok0, st0, res0⟩ := AM.of_run_ok _ _ _ _ hrun
    obtain ⟨ok1, st1, res1⟩ := AM.of_run_ok _ _ _ _ hrun1
    unfold CoreSpec
    apply L.M.triple_of_run
    intro s r s' hs hr
    obtain ⟨hloc, -, hA', hres, hw⟩ := L.M.of_run (P := fun s => s = s₀) hs hr
      (arEntry_refines p hp he n s₀ _ hA e d k c hE)
    obtain ⟨hf, -⟩ := L.M.of_run (P := fun s => s = s₀) hs hr
      (invoke_memFrame (hp.closed he) (n + 1) (by decide) _ s₀)
    subst hs
    rw [st1] at hA'; rw [res1] at hres
    have hD0 : ArenaD s'.mem a₀ := hA'.1.memo_irrel a₀.memos.instLC a₀.memos.abs1C
    obtain ⟨hS', hSt⟩ := hS.of_walk hD0 rfl hf (lt64A_of_all rfl) (lt64_of_all rfl)
      ⟨coreIl_frame hf (by decide) (by decide) hS.memos, ⟨_, hA'.2⟩, hS.memos.2.2.frame hf (by decide) (by decide)⟩
    refine ⟨hloc, ok0, ⟨M, ?_, KeptAll.refl _ _, hSt⟩, by rw [res0]; exact hres, hw⟩
    rw [st0]; exact hS'
  have hrun : (abstractRangeFast coreWalkFuel (decE e) d.toNat k.toNat c.toNat).run a₀ =
      (abstractRangeFast coreWalkFuel (decE e) d.toNat k.toNat c.toNat).run
        { a₀ with memos := { a₀.memos with abs1C := mp } } := by
    simp only [abstractRangeFast, hk0, ↓reduceIte]; rfl
  have hA : ArenaA s₀.mem { a₀ with memos := { a₀.memos with abs1C := mp } } :=
    ⟨hS.arena.memo_irrel a₀.memos.instLC mp, hmp⟩
  unfold CoreSpec
  apply L.M.triple_of_run
  intro s r s' hs hr
  obtain ⟨hloc, hok, hA', hres, hw⟩ := L.M.of_run (P := fun s => s = s₀) hs hr
    (arEntry_refines p hp he n s₀ _ hA e d k c hE)
  obtain ⟨hf, -⟩ := L.M.of_run (P := fun s => s = s₀) hs hr
    (invoke_memFrame (hp.closed he) (n + 1) (by decide) _ s₀)
  subst hs
  obtain ⟨hok, e2, e3⟩ := AM.readings hrun hok
  rw [← e2] at hA'; rw [← e3] at hres
  have hk := Keeps.run (keepsW_arFast coreWalkFuel (decE e) d.toNat k.toNat c.toNat)
    (AM.run_of_ok _ _ hok)
  obtain ⟨hS', hSt⟩ := hS.of_walk hA'.1 hk hf (lt64A_of_all rfl) (lt64_of_all rfl)
    ⟨coreIl_frame hf (by decide) (by decide) hS.memos, ⟨_, hA'.2⟩, hS.memos.2.2.frame hf (by decide) (by decide)⟩
  exact ⟨hloc, hok, ⟨M, hS', KeptAll.refl _ _, hSt⟩, hres, hw⟩

/-- `loose_bvars_bounded_fast(4·10⁹, c, e)` under `CoreS` (`IotaCallees`' `LooseBVarsBoundedFastOK`). -/
theorem lbb_core (hp : BvbProg p) : LooseBVarsBoundedFastOK p := by
  intro n s₀ a₀ dn vis fe M eb c e hS hE
  cases n with
  | zero => exact CoreSpec.zeroW hp.lbb _ _ _ _ _ _ _ _ _ _ _
  | succ n =>
  unfold CoreSpec
  apply L.M.triple_of_run
  intro s r s' hs hr
  obtain ⟨hloc, hok, hD', hres, hw⟩ := L.M.of_run (P := fun s => s = s₀) hs hr
    (lbbFast_refines p hp n s₀ a₀ hS.arena 4000000000 c e hE)
  obtain ⟨hf, -⟩ := L.M.of_run (P := fun s => s = s₀) hs hr
    (invoke_memFrame (bvb_closed hp) (n + 1) (by decide) _ s₀)
  subst hs
  rw [coreWalkFuel_toNat] at hok hD' hres
  have hk := Keeps.run (Keeps.bind (keepsW_bvarB coreWalkFuel (decE e)) fun _ => Keeps.pure _ :
    Keeps cpl (looseBVarsBoundedFast coreWalkFuel c.toNat (decE e))) (AM.run_of_ok _ _ hok)
  obtain ⟨hS', hSt⟩ := hS.of_walk hD' hk hf (lt64A_of_all rfl) (lt64_of_all rfl)
    (hS.memos.frame hf (by decide) (by decide))
  refine ⟨hloc, hok, ⟨M, hS', KeptAll.refl _ _, hSt⟩, hres, ?_⟩
  unfold ResH HW; have := UInt64.le_iff_toNat_le.mp hw
  have h1 : (1 : Word).toNat = 1 := rfl
  omega

/-- `fvbW_ok` (`Abs1Refine.lean`) without the abstraction memo: `ab_fvb` under `ArenaD`. -/
theorem fvbW_okD (n : Nat) (m m' : Mem) (a : AState) (hA : ArenaD m a)
    (h f x : Word) (hh : h.toNat < 2 ^ 32) (hb : fvbW n m h f = some (x, m')) :
    ∃ a', (fvarB f.toNat (decE h)).run a = .ok (x.toNat, a') ∧ ArenaD m' a' ∧ FrFrame m m' := by
  obtain ⟨n, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by cases n <;> simp_all [fvbW]⟩
  have hd := derFW_ok m a hA.1 hA.2 h hh
  rw [fvarB_run, ← hd]
  by_cases hs : derFW m h = 32767
  · rw [fvbW_sat n m h f hs] at hb
    have hs' : ((derFW m h).toNat == ConLeche.satRange) = true := by rw [hs]; rfl
    rw [ite_eq_left hs']
    obtain ⟨n, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by cases n <;> simp_all [fvbN]⟩
    rw [fvbN_succ] at hb
    obtain ⟨a', ha', hR'⟩ := frMemoW_correct n m m' a hA.1 h f x hh hb
    have hk := (keeps_fvarRangeMemo_fsp f.toNat (decE h)).run ha'
    simp only [fsp, Prod.mk.injEq] at hk
    have hf := frMemoW_frame n m m' h f x hb
    exact ⟨a', ha', ⟨hR', DerR.of_store m' a a' (DerR.frameM _ _ m m' hf (by decide) a hA.2) hk.1⟩, hf⟩
  · rw [fvbW_pk n m h f hs] at hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    have hs' : ((derFW m h).toNat == ConLeche.satRange) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro e; apply hs; apply UInt64.toNat_inj.mp; rw [e]; rfl
    rw [ite_eq_right (by simp [hs'])]
    exact ⟨a, rfl, hA, MemFrame.refl _ _ _⟩

/-- `has_fvar(e)` under `CoreS` (lane `defeq`'s `HasFvarOK`). -/
theorem hasFvar_core (hp : AbsProg p) (hpf : p.lookup "has_fvar" = some hasFvarL) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
      (M : ModeMaps) (eb e : Word), CoreS dn s₀.mem a₀ vis fe M eb → HW e →
      CoreSpec p n "has_fvar" [e] (hasFvarFast coreWalkFuel (decE e)) decBool s₀ a₀ dn vis fe M eb := by
  intro n s₀ a₀ dn vis fe M eb e hS hE
  cases n with
  | zero => exact CoreSpec.zeroW hpf _ _ _ _ _ _ _ _ _ _ _
  | succ n =>
  unfold CoreSpec
  apply L.M.triple_of_run
  intro s r s' hs hr
  obtain ⟨hloc, hI⟩ := L.M.of_run (P := fun s => s = s₀) hs hr (hasFvarL_spec p hp hpf n s₀ e)
  subst hs
  cases hw : fvbW n s.mem e 4000000000 with
  | none => rw [hw] at hI; cases hI
  | some q =>
  obtain ⟨x, m₁⟩ := q
  have hle := hfK_le _ _ _ hI
  rw [hw, hfK_some] at hI
  obtain ⟨hr0, rfl⟩ := Prod.mk.inj (Option.some.inj hI)
  obtain ⟨a', ha', hD', hf⟩ := fvbW_okD n s.mem _ a₀ hS.arena e 4000000000 x hE hw
  rw [coreWalkFuel_toNat] at ha'
  have hrun : (hasFvarFast coreWalkFuel (decE e)).run a₀ = .ok (x.toNat != 0, a') := by
    simp only [hasFvarFast, StateT.run_bind, ha']; rfl
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  have hk := Keeps.run (Keeps.bind (keepsW_fvarB coreWalkFuel (decE e)) fun _ => Keeps.pure _ :
    Keeps cpl (hasFvarFast coreWalkFuel (decE e))) hrun
  obtain ⟨hS', hSt⟩ := hS.of_walk hD' hk hf (lt64A_of_all rfl) (lt64_of_all rfl)
    (hS.memos.frame hf (by decide) (by decide))
  refine ⟨hloc, hok, ⟨M, hst ▸ hS', KeptAll.refl _ _, hSt⟩, ?_, ?_⟩
  · rw [hres, decBool, ← hr0]
    by_cases h0 : x = 0
    · subst h0; rfl
    · have h0' : x.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp e)
      simp [h0, h0']
  · unfold ResH HW; rw [← hr0]; split <;> decide

/-- `inst1(e, v, d)`: a call of `inst_entry(e, v, d)` (the checker's `inst1A`, `Checker/Entry.lean`,
the same text). -/
-- con-ron: ConRon/Arena/ExprOps.lean:377-384 ConRon.Arena.instantiate1Fast
def inst1W : FunDecl := lfn (e, v, d) locals (r) {
  r := call inst_entry(e, v, d);
  return r
}

/-- `inst1`'s model: `inst_entry`'s run, its first word. -/
def inst1WW (p : Prog) (n : Nat) (m : Mem) (e v d : Word) : Option (Word × Mem) :=
  match callW p n "inst_entry" [e, v, d] m with
  | none => none
  | some (r, m') => some (r.headD 0, m')

theorem inst1W_spec {p : Prog} (hi : p.lookup "inst1" = some inst1W) (n : Nat) (s₀ : St)
    (e v d : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "inst1" [e, v, d]
    ⦃fun r s' => LocEq s' s₀ ∧ inst1WW p n s₀.mem e v d = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hi]
  simp only [callFn, inst1W]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "inst_entry"] <;>
    finish [inst1WW]


/-- `inst1` through its call of `inst_entry`. -/
theorem inst1_wrap {p : Prog} (hp : InstProg p) (he : p.lookup "inst_entry" = some instEntry)
    (hle : p.lookup "lift_entry" = some liftEntry) (hi : p.lookup "inst1" = some inst1W) :
    Inst1OK p := by
  intro n s₀ a₀ dn vis fe M eb e v d hS he' _
  cases n with
  | zero => exact CoreSpec.zeroW hi _ _ _ _ _ _ _ _ _ _ _
  | succ n =>
  apply L.M.triple_of_run
  intro s r s' hs hr
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs hr (inst1W_spec hi n s₀ e v d)
  subst hs
  refine ⟨hloc, ?_⟩
  unfold inst1WW at hW
  cases hc : callW p n "inst_entry" [e, v, d] s.mem with
  | none => simp [hc] at hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  simp only [hc, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hw, hm⟩ := hW
  rw [← hm]
  obtain ⟨h1, h2, h3, h4⟩ :=
    CoreSpec.of_callW (inst1_core hp he hle "inst_entry" he n s a₀ dn vis fe M eb e v d hS he') hc
  exact ⟨h1, h2, by rw [h3]; simp only [decH, hw], by unfold ResH at h4 ⊢; rw [← hw]; exact h4⟩

/-- **The walks' programs**, at their names (what `CoreWalks`' bridges need of a program). -/
structure CoreWalkProg (p : Prog) : Prop where
  il : InstListProg p
  ile : p.lookup "inst_list" = some instListL
  inst : InstProg p
  ie : p.lookup "inst_entry" = some instEntry
  le : p.lookup "lift_entry" = some liftEntry
  /-- The core's call sites name `instantiate1Fast`'s L function `inst1`: a call of
  `inst_entry`. -/
  i1 : p.lookup "inst1" = some inst1W
  bvb : BvbProg p
  abs : AbsProg p
  ae : p.lookup "abs_entry" = some absEntry
  ar : ArProg p
  are : p.lookup "ar_entry" = some arEntry
  hf : p.lookup "has_fvar" = some hasFvarL

theorem CoreWalkProg.instListOK (hp : CoreWalkProg p) : InstListOK p := instListOK_core hp.il hp.ile

theorem CoreWalkProg.iotaInst1OK (hp : CoreWalkProg p) : IotaInst1OK p :=
  inst1_core hp.inst hp.ie hp.le "inst_entry" hp.ie

theorem CoreWalkProg.inst1OK (hp : CoreWalkProg p) : Inst1OK p :=
  inst1_wrap hp.inst hp.ie hp.le hp.i1

theorem CoreWalkProg.lbbOK (hp : CoreWalkProg p) : LooseBVarsBoundedFastOK p := lbb_core hp.bvb

end bridges

end L.Arena
