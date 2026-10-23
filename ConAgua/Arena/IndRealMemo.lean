import ConAgua.Arena.IndRealAbs
import ConAgua.Arena.WalkLiftRefine

/-!
# `instantiate1_lift_fast` under the stage relation and the walk memos (lane `indproofs4`, helper `memo`)

`instantiate1_lift_fast(fuel, e, v, d)` is lane `tails`' walk (`WalkLift.lean`), which refines
`instantiate1LiftFast` under `ArenaI = ArenaD ∧ I1R` (`i1lFast_refines`): its memo (`ILFM` = 51,
epoch word `CTL[52]`) lives outside the arena's memos, so `StageR` says nothing about it. The twin
clears `inst1LC` at entry (`i1lFast_run`), so its run from `a` is the run from `a` with any other
`inst1LC`; the walk needs only *some* well-formed memo in the memory at hand, `AbsOK`'s part
`I1Memo` (`IndStubs.lean`), and leaves one. The recipe of `IndReal.lean` and helper `abs`'s
`abF_ok` (`IndRealAbs.lean`).

* **The model** `i1lF := callF i1lP "instantiate1_lift_fast"` over the walk's program `i1lP`
  (its functions, `bvar_b`'s and `lift_entry`'s), write set `i1lA`/`i1lC` (below 64).
* **The twin keeps `cp`** (`keeps_i1lFast`): the walk interns nodes and touches walk memos only.
* **`i1lF_ok`**: `RelW i1lF [f, e, v, d] (StageR ∧ AbsOK) (instantiate1LiftFast …) (KeepPost … ∧ AbsOK)`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The twin keeps `cp` -/

theorem keeps_inst1LGet {β : Type} {π : AState → β} (k : EIdx × Nat) : Keeps π (inst1LGet k) := by
  unfold Keeps; intro a r a' h; cases h; rfl
theorem keeps_inst1LSet {β : Type} {π : AState → β} (hπ : MemoBlind π) (k : EIdx × Nat) (v : EIdx) :
    Keeps π (inst1LSet k v) := by
  unfold Keeps; intro a r a' h; cases h; first | exact hπ _ _ | exact (hπ _ _).trans (hπ _ _)
theorem keeps_inst1LClear {β : Type} {π : AState → β} (hπ : MemoBlind π) : Keeps π inst1LClear := by
  unfold Keeps; intro a r a' h; cases h; first | exact hπ _ _ | exact (hπ _ _).trans (hπ _ _)

/-- **`instantiate1LiftGo` keeps `(caches, pins)`.** -/
theorem keeps_i1lGo (v : EIdx) (F : Nat) : ∀ h d, Keeps cp (instantiate1LiftGo v F h d) := by
  induction F with
  | zero => intro h d; rw [instantiate1LiftGo_zero]; exact Keeps.fail _
  | succ F ih =>
    intro h d; rw [instantiate1LiftGo_succ]
    repeat' (first
      | exact keeps_inst1LGet _ | exact keeps_inst1LSet cp_blind _ _
      | exact (keepsW_bvarB _ _).cp_of_cpl | exact keeps_liftFast _ _ _ _
      | keeps_auto [inst1LiftArmApp, inst1LiftArmLam, inst1LiftArmForallE, inst1LiftArmLet,
          inst1LiftArmProj] using ih, cp_blind)

theorem keeps_i1lFast (F : Nat) (e v : EIdx) (d : Nat) : Keeps cp (instantiate1LiftFast F e v d) := by
  unfold instantiate1LiftFast
  exact Keeps.bind (keeps_inst1LClear cp_blind) fun _ => Keeps.bind (keeps_i1lGo v F e d) fun _ =>
    Keeps.bind (keeps_inst1LClear cp_blind) fun _ => Keeps.pure _

/-! ## The program and the model -/

/-- The walk, `bvar_b`'s program and `lift_entry`'s. -/
def i1lP : Prog := i1lFns ++ bvbProg ++ liftProg

/-- The functions `instantiate1_lift_fast` reaches. -/
def i1lPFns : List FnName :=
  ["i1l_find", "i1l_put", "i1l_clear", "i1l_go", "i1l_app", "i1l_lam", "i1l_forall", "i1l_let",
    "i1l_proj", "instantiate1_lift_fast"] ++ bvbFns ++ liftFns

/-- What it writes: its memo (51), `bvar_b`'s (`walkA`) and `lift_entry`'s with the store's (`liftA`). -/
def i1lA : List ArrId := 51 :: walkA ++ liftA
/-- Its memo's epoch and count (52, 53), `walkC`, `liftC`. -/
def i1lC : List Word := 52 :: 53 :: walkC ++ liftC

theorem i1lP_closed : closedA i1lP i1lA i1lC i1lPFns = true := by decide +kernel

theorem i1lP_prog : I1lProg i1lP := by
  constructor
  · exact (ProgHas.refl i1lP).left.right
  · constructor <;> exact (ProgHas.refl i1lP).get _
  all_goals exact (ProgHas.refl i1lP).get _

/-- The program bundle. -/
abbrev I1lF (p : Prog) : Prop := ProgHas p i1lP

/-- **The model of `instantiate1_lift_fast`** (program- and fuel-free). -/
noncomputable def i1lF (m : Mem) (args : List Word) : Option (List Word × Mem) :=
  callF i1lP "instantiate1_lift_fast" m args

theorem i1lF_spec (p : Prog) (hp : I1lF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "instantiate1_lift_fast" args
    ⦃fun r s' => LocEq s' s₀ ∧ i1lF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  callF_spec i1lP_closed (hp.agree i1lPFns) (by decide) n s₀ args

/-- `instantiate1_lift_fast` writes only `i1lA`, `i1lC`. -/
theorem i1lF_frame {m m' : Mem} {args r : List Word} (h : i1lF m args = some (r, m')) :
    MemFrame i1lA i1lC m m' := by
  obtain ⟨n, hc⟩ := callF_run h
  exact (run_memFrame i1lP_closed (by decide) (run_of_callW hc)).1

/-- **`instantiate1_lift_fast` refines `instantiate1LiftFast` under the stage relation and the
walk memos** (replaces `IndStubs.instantiate1LiftFast_spec`); the memos are well formed after. -/
theorem i1lF_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (f e v d : Word)
    (he : H e) (hv : H v) :
    RelW i1lF [f, e, v, d] (fun m a => StageR dn vis fe m a ∧ AbsOK m)
      (instantiate1LiftFast f.toNat (decI e) (decI v) d.toNat)
      (fun m m' a r x => KeepPost dn vis fe decW0E m m' a r x ∧ AbsOK m') := by
  intro m m' a r h ⟨hS, hAb, ⟨mp, hmp⟩, hCr, hIl⟩
  have hfr := i1lF_frame h
  obtain ⟨n, hc⟩ := callF_run h
  match n, hc with
  | 0, hc => rw [callW_zero] at hc; cases hc
  | n + 1, hc =>
  have hA : ArenaI m (withI1C a mp) := ⟨hS.1.arena.withI1C mp, hmp⟩
  obtain ⟨s', hs', -, hok, hA', hres, hlt⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (i1lFast_refines i1lP i1lP_prog n _ _ hA f e v d he hv) hc
  rw [hs'] at hA'
  have hrun := AM.run_of_ok _ _ hok
  have hrun' : (instantiate1LiftFast f.toNat (decE e) (decE v) d.toNat).run a =
      .ok (AM.res (instantiate1LiftFast f.toNat (decE e) (decE v) d.toNat) (withI1C a mp),
        AM.st (instantiate1LiftFast f.toNat (decE e) (decE v) d.toNat) (withI1C a mp)) := by
    rw [← hrun, i1lFast_run, i1lFast_run]; rfl
  obtain ⟨hS', hg⟩ := StageR.of_walk hS hA'.1 hfr (lt64A_of_all rfl) (lt64_of_all rfl)
    ((keeps_i1lFast _ _ _ _).run hrun')
  exact ⟨_, _, hrun', ⟨hS', hg, hlt, hres.symm⟩, hAb.frame hfr (by decide) (by decide), ⟨_, hA'.2⟩,
    hCr.frame hfr (by decide) (by decide), hIl.frame hfr (by decide) (by decide)⟩

end L.Ind
