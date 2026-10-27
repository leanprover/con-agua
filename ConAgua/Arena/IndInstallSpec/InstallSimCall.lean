import ConAgua.Arena.IndInstallSpec.InstallCvDecB
import ConAgua.Arena.IndInstallSpec.NhW

/-!
# InstallSimCall

`installSimCall`, `installSortSim`, `ibt_spec`, `ibtW`, `MemOK.grow`, `_root_.L.Arena.Sim.callW_pos`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Callees as runs -/

/-- **A callee's refinement triple, as a `Sim` on its run.** -/
theorem installSimCall {α : Type} [Inhabited α] {p : Prog} {n : Nat} {f : FnName} {args : List Word}
    {m : Mem} {op : AM α} {a : AState} {Q : List Word → α → Mem → AState → Prop}
    {P : List Word → St → Prop}
    (h : ⦃fun s => s = (⟨m, Locals.init []⟩ : St)⦄ invoke p (exec p n) f args ⦃fun r s' => P r s'; ⊤⦄)
    (hP : ∀ r s', P r s' → AM.ok op a ∧ Q r (AM.res op a) s'.mem (AM.st op a)) :
    Sim (callW p n f args m) op a Q := by
  intro r m' e
  obtain ⟨s', rfl, hp⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) h e
  obtain ⟨hok, hq⟩ := hP r s' hp
  exact ⟨_, _, partsRunOfOk hok, hq⟩

/-- `intern_sort` as a `Sim` (master's, through its stage lemma). -/
theorem installSortSim {p : Prog} (hP : CstProg p) (n : Nat) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {m : Mem} {a : AState} {u : Word} (hS : StageR dn vis fe m a) (hu : H u) :
    Sim (callW p n "intern_sort" [u] m) (internSortE (decI u)) a
      (fun r x m' a' => StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decE (r.headD 0) = x ∧ AFr m m') := by
  intro r m' e
  obtain ⟨s', rfl, -, hI⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (internSort_spec p hP.sortFind hP.sortPush hP.internSort n _ u) e
  obtain ⟨a', hrun, hS', hg⟩ := internSort_stage hS u hu hI
  exact ⟨_, a', hrun, hS', hg, rfl, sointernW_afr hI⟩

/-! ## `check_block_tele` -/

/-- **`check_block_tele` is its model `ibtW`** (generated). -/
l_model ibt_spec (p : Prog) (hp : p.lookup "check_block_tele" = some checkBlockTele)
  fns [hp ↦ ibtW]
  specs [callW_spec p n "check_constant_val", callW_spec p n "check_sum_tele",
    callW_spec p n "strip_pis", callW_spec p n "intern_sort"]
  grind [ind_grind] finish [rdW_eq] gen 20

theorem MemOK.grow {m m' : Mem} {q : Nat} {ms : MemberShape} (h : MemOK m q ms) (hg : IWGrow m m') :
    MemOK m' q ms := by
  refine ⟨h.1.grow (decMS_mono _) hg, fun c hc => ?_⟩
  have hq : q < iwTop m := by
    have := h.1; simp only [DecB, decMS, bind, Option.bind_eq_some_iff] at this
    obtain ⟨c', hc', -⟩ := this; exact partsIwLt hc'
  rw [iwN_grow hg hq] at hc
  exact CVExt_grow hg (h.2 c hc)

/-- A callee proved at every positive fuel is simulated at every fuel (`callW` at `0` fails). -/
theorem _root_.L.Arena.Sim.callW_pos {α : Type} {p : Prog} {f : FnName} {args : List Word} {m : Mem} {op : AM α}
    {a : AState} {Q : List Word → α → Mem → AState → Prop}
    (h : ∀ k, Sim (callW p (k + 1) f args m) op a Q) (n : Nat) : Sim (callW p n f args m) op a Q := by
  cases n with
  | zero => rw [callW_zero]; exact Sim.of_none
  | succ k => exact h k

end L.Ind

end
