import ConAgua.Arena.CallF
import ConAgua.Arena.WhnfEntry
import ConAgua.Arena.WhnfSpineRefine
import ConAgua.Arena.DeclNatBase
import ConAgua.Arena.IndStubs
import ConAgua.Arena.IndLibSpec
import ConAgua.Arena.StripTeleSpec
import ConAgua.Arena.StageInst1

/-!
# The spine adapters' stub contracts discharged (lane `indproofs4`, helper `spine`)

`get_app_fn_f`, `pi_result_f` (and below `get_app_args_f`, `mk_app_n_f`), lane `induct`'s fuel
adapters over the whnf lane's spine walks (`WhnfEntry.lean`), as program- and fuel-free models
`callF P f` (`CallF.lean`, the recipe of `IndReal.lean`) with the relational facts of the
`IndStubs` contracts. This file sits below the stage's spec files (`IndPartsSpec3`, …), so it
does not import `IndReal`/`StubIndRefine`: the adapter specs are restated here.

The adapters abort at any fuel word other than `CWF`, so the contracts hold at every fuel word: a
returning run has `f = CWF`, and `CWF.toNat = coreWalkFuel` (`CWF_eq`) is the walks' fuel.
-/

set_option experimental.vcgen true
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `get_app_fn_f` -/

/-- The adapter `get_app_fn_f(f, e)` over its callee's run. -/
def gafAdW (p : Prog) (n : Nat) (m : Mem) (f e : Word) : Option (List Word × Mem) :=
  if f ≠ CWF then none else
  ntBW (callW p n "get_app_fn" [e] m) fun r m' => some ([r.headD 0], m')

theorem gafAd_spec (p : Prog) (hp : p.lookup "get_app_fn_f" = some getAppFnFL) (n : Nat) (s₀ : St)
    (f e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "get_app_fn_f" [f, e]
    ⦃fun r s' => LocEq s' s₀ ∧ gafAdW p n s₀.mem f e = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, getAppFnFL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, callW_spec p n "get_app_fn"] <;>
    finish (gen := 20) [gafAdW, ntBW, CWF]

/-- `get_app_fn_f` and its callee. -/
def gafProg : Prog := [("get_app_fn_f", getAppFnFL), ("get_app_fn", getAppFnL)]

def gafFns : List FnName := gafProg.map (·.1)

/-- `get_app_fn_f` writes nothing. -/
theorem gafProg_closed : closedA gafProg [] [] gafFns = true := by decide +kernel

/-- The program bundle. -/
abbrev GafF (p : Prog) : Prop := ProgHas p gafProg

/-- **The model of `get_app_fn_f`.** -/
noncomputable def gafF (m : Mem) (args : List Word) : Option (List Word × Mem) :=
  callF gafProg "get_app_fn_f" m args

theorem gafF_spec (p : Prog) (hp : GafF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "get_app_fn_f" args
    ⦃fun r s' => LocEq s' s₀ ∧ gafF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  callF_spec gafProg_closed (hp.agree gafFns) (by decide) n s₀ args

/-- **`get_app_fn_f`'s model refines `getAppFn`** (replaces `IndStubs.getAppFn_spec`): memory and
twin state unchanged. -/
theorem gafF_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (f e : Word) (he : H e) :
    RelW gafF [f, e] (StageR dn vis fe) (getAppFn f.toNat (decI e)) (KeepPost dn vis fe decW0E) := by
  intro m m' a r h hS
  obtain ⟨n, hc⟩ := callF_run h
  cases n with
  | zero => simp [callW_zero] at hc
  | succ k =>
  have c' := callW_model (M := fun mm => gafAdW gafProg k mm f e)
    (fun s => gafAd_spec gafProg rfl k s f e) hc
  simp only [gafAdW] at c'
  by_cases hf : f ≠ CWF
  · rw [if_pos hf] at c'; cases c'
  rw [if_neg hf] at c'
  have hf' : f = CWF := Decidable.not_not.mp hf
  subst hf'
  cases c'' : callW gafProg k "get_app_fn" [e] m with
  | none => rw [c''] at c'; simp at c'
  | some q =>
  obtain ⟨r', m''⟩ := q
  rw [c'', bW_some] at c'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj c')
  obtain ⟨t, ht, hm, -, hHW, hrun⟩ := triple_of_callW
    (getAppFn_refines' gafProg rfl k ⟨m, Locals.init []⟩ a hS.1.arena.1 e he) c''
  have e_m : m = m'' := by rw [← ht, hm]
  subst e_m
  exact ⟨decE (r'.headD 0), a, by rw [CWF_eq]; exact hrun, hS, IWGrow.refl _, hHW, rfl⟩

/-- `get_app_fn_f` writes nothing. -/
theorem gafF_frame {m m' : Mem} {args r : List Word} (h : gafF m args = some (r, m')) :
    MemFrame [] [] m m' := by
  obtain ⟨n, hc⟩ := callF_run h
  exact (run_memFrame gafProg_closed (by decide) (run_of_callW hc)).1

/-! ## `pi_result_f` -/

/-- The adapter `pi_result_f(f, e)` over its callee's run. -/
def pirAdW (p : Prog) (n : Nat) (m : Mem) (f e : Word) : Option (List Word × Mem) :=
  if f ≠ CWF then none else
  ntBW (callW p n "pi_result" [e] m) fun r m' => some ([r.headD 0], m')

theorem pirAd_spec (p : Prog) (hp : p.lookup "pi_result_f" = some piResultFL) (n : Nat) (s₀ : St)
    (f e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pi_result_f" [f, e]
    ⦃fun r s' => LocEq s' s₀ ∧ pirAdW p n s₀.mem f e = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, piResultFL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, callW_spec p n "pi_result"] <;>
    finish (gen := 20) [pirAdW, ntBW, CWF]

/-- `pi_result_f` and its callee. -/
def pirProg : Prog := [("pi_result_f", piResultFL), ("pi_result", piResultL)]

def pirFns : List FnName := pirProg.map (·.1)

/-- `pi_result_f` writes nothing. -/
theorem pirProg_closed : closedA pirProg [] [] pirFns = true := by decide +kernel

/-- The program bundle. -/
abbrev PirF (p : Prog) : Prop := ProgHas p pirProg

/-- **The model of `pi_result_f`.** -/
noncomputable def pirF (m : Mem) (args : List Word) : Option (List Word × Mem) :=
  callF pirProg "pi_result_f" m args

theorem pirF_spec (p : Prog) (hp : PirF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pi_result_f" args
    ⦃fun r s' => LocEq s' s₀ ∧ pirF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  callF_spec pirProg_closed (hp.agree pirFns) (by decide) n s₀ args

/-- **`pi_result_f`'s model refines `piResult`** (replaces `IndStubs.piResult_spec`): memory and
twin state unchanged. -/
theorem pirF_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (f e : Word) (he : H e) :
    RelW pirF [f, e] (StageR dn vis fe) (piResult f.toNat (decI e)) (KeepPost dn vis fe decW0E) := by
  intro m m' a r h hS
  obtain ⟨n, hc⟩ := callF_run h
  cases n with
  | zero => simp [callW_zero] at hc
  | succ k =>
  have c' := callW_model (M := fun mm => pirAdW pirProg k mm f e)
    (fun s => pirAd_spec pirProg rfl k s f e) hc
  simp only [pirAdW] at c'
  by_cases hf : f ≠ CWF
  · rw [if_pos hf] at c'; cases c'
  rw [if_neg hf] at c'
  have hf' : f = CWF := Decidable.not_not.mp hf
  subst hf'
  cases c'' : callW pirProg k "pi_result" [e] m with
  | none => rw [c''] at c'; simp at c'
  | some q =>
  obtain ⟨r', m''⟩ := q
  rw [c'', bW_some] at c'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj c')
  obtain ⟨t, ht, hm, -, hHW, hrun⟩ := triple_of_callW
    (piResult_refines' pirProg rfl k ⟨m, Locals.init []⟩ a hS.1.arena.1 e he) c''
  have e_m : m = m'' := by rw [← ht, hm]
  subst e_m
  exact ⟨decE (r'.headD 0), a, by rw [CWF_eq]; exact hrun, hS, IWGrow.refl _, hHW, rfl⟩

/-- `pi_result_f` writes nothing. -/
theorem pirF_frame {m m' : Mem} {args r : List Word} (h : pirF m args = some (r, m')) :
    MemFrame [] [] m m' := by
  obtain ⟨n, hc⟩ := callF_run h
  exact (run_memFrame pirProg_closed (by decide) (run_of_callW hc)).1

end L.Ind
