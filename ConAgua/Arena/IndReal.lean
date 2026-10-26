import ConAgua.Arena.CallF
import ConAgua.Arena.StubNamesRefine
import ConAgua.Arena.StubIndRefine
import ConAgua.Arena.StageInst1

/-!
# Stub contracts discharged by real refinements (lane `indproofs4`)

`IndStubs.lean`'s contracts stand for callees another lane owns. When that lane lands a
refinement (a `RefAM` in its program bundle), the stage's models swap `stubM f` for the callee's
program- and fuel-free model `callF P f` (`CallF.lean`, the precedent `StageInst1.lean`), where
`P` is the callee's call-closed function list:

* `xF_spec`: every call of `f` in a program with `ProgHas p P` returns `callF P f`;
* `xF_ok`: the relational fact, `RelW (callF P f) …` in the shape of the stub contract, from the
  owner's refinement in `P` itself (`relW_callF`: `RefAM P` is `RelW (callF P)`);
* the write set of `P` (`closedA`), for memo frames (`MFr`).

Callers then need `ProgHas p P` (added to their program bundles); `Checker/IndReal.lean` proves
these bundles for `checkerProg`, one `rfl` lookup per function.
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **A refinement in a closed program is a fact about its fuel-free model.** -/
theorem relW_callF {α : Type} [Inhabited α] {P : Prog} {f : FnName} {args : List Word}
    {pre : Mem → AState → Prop} {op : AM α} {post : Mem → Mem → AState → List Word → α → Prop}
    (h : RefAM P f args pre op post) : RelW (callF P f) args pre op post := by
  intro m m' a r hc hpre
  obtain ⟨n, hn⟩ := callF_run hc
  obtain ⟨s', hs', -, hok, hpost⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (h n _ a hpre) hn
  subst hs'
  exact ⟨_, _, AM.run_of_ok _ a hok, hpost⟩

/-! ## `reserved_rec_name` (lane `tails`' `reservedRecName_refines`) -/

/-- `reserved_rec_name` and its callees. -/
def rrnProg : Prog :=
  [("reserved_rec_name", L.Stubs.reservedRecNameL), ("reserved_contains", reservedContains),
   ("reserved_from", reservedFrom), ("lit_guard_has", L.Stubs.litGuardHas),
   ("pin_range_has", L.Stubs.pinRangeHas), ("pin_at", pinAtL)]

def rrnFns : List FnName := rrnProg.map (·.1)

/-- `reserved_rec_name` writes nothing. -/
theorem rrnProg_closed : closedA rrnProg [] [] rrnFns = true := by decide +kernel

/-- The program bundle. -/
abbrev RrnF (p : Prog) : Prop := ProgHas p rrnProg

/-- **The model of `reserved_rec_name`.** -/
noncomputable def rrnF (m : Mem) (args : List Word) : Option (List Word × Mem) :=
  callF rrnProg "reserved_rec_name" m args

theorem rrnF_spec (p : Prog) (hp : RrnF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "reserved_rec_name" args
    ⦃fun r s' => LocEq s' s₀ ∧ rrnF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  callF_spec rrnProg_closed (hp.agree rrnFns) (by decide) n s₀ args

/-- **`reserved_rec_name`'s model refines `reservedRecName`** (replaces
`IndStubs.reservedRecName_spec`). -/
theorem rrnF_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Word) (hn : H n) :
    RelW rrnF [n] (StageR dn vis fe) (reservedRecName (decI n)) (KeepPost dn vis fe decW0B) :=
  relW_callF (L.Stubs.reservedRecName_refines (p := rrnProg) (by constructor <;> rfl) dn vis fe n hn)

/-! ## `rec_rule_bits` (lane `tails`' `recRuleBits_refines`) -/

/-- `rec_rule_bits` and its callees. -/
def rrbProg : Prog :=
  [("rec_rule_bits", L.Stubs.recRuleBitsL), ("rec_rule_k_of", L.Stubs.recRuleKOfL),
   ("rec_rule_eta_of", L.Stubs.recRuleEtaOfL), ("ctor_family", L.Stubs.ctorFamily),
   ("er_sl_eq", L.Ind.erSlEq), ("const_name_of", constNameOfL), ("get_app_fn_f", getAppFnFL),
   ("pi_result_f", piResultFL), ("get_app_fn", getAppFnL), ("pi_result", piResultL),
   ("env_find", envFindL), ("env_row_get", envRowGetL), ("env_ix", envIxL)]

def rrbFns : List FnName := rrbProg.map (·.1)

theorem rrbProg_closed : closedA rrbProg [] [] rrbFns = true := by decide +kernel

abbrev RrbF (p : Prog) : Prop := ProgHas p rrbProg

/-- **The model of `rec_rule_bits`.** -/
noncomputable def rrbF (m : Mem) (args : List Word) : Option (List Word × Mem) :=
  callF rrbProg "rec_rule_bits" m args

theorem rrbF_spec (p : Prog) (hp : RrbF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rec_rule_bits" args
    ⦃fun r s' => LocEq s' s₀ ∧ rrbF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  callF_spec rrbProg_closed (hp.agree rrbFns) (by decide) n s₀ args

/-- **`rec_rule_bits`' model refines `recRuleBits`** (replaces `IndStubs.recRuleBits_spec`). -/
theorem rrbF_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (c : Word) (hc : H c)
    (rl : IRecRule) (hrl : rl.ctor = decI c) :
    RelW rrbF [vis, c] (StageR dn vis fe) (recRuleBits fe rl)
      (KeepPost dn vis fe (fun _ r (x : IRecRule) =>
        x = { rl with k := r.headD 0 != 0, eta := r.tail.headD 0 != 0 })) :=
  relW_callF (L.Stubs.recRuleBits_refines (p := rrbProg) (by constructor <;> rfl) dn vis fe c hc rl hrl)

theorem rrbF_frame {m m' : Mem} {args r : List Word} (h : rrbF m args = some (r, m')) :
    MemFrame [] [] m m' := by
  obtain ⟨n, hc⟩ := callF_run h
  exact (run_memFrame rrbProg_closed (by decide) (run_of_callW hc)).1

end L.Ind
