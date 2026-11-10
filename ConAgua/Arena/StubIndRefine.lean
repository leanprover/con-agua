module

import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.DeclCanonSpec
public import ConAgua.Arena.DeclNatBase
public import ConAgua.Arena.WhnfEntry
import all ConAgua.Arena.DeclArmsCanon
import all ConAgua.Arena.StubInd
import all ConAgua.Arena.WhnfEntry

@[expose] public section

/-!
# The fuel adapters and `er_sl_eq`

The models of the fuel adapters `get_app_fn_f`, `pi_result_f` (`gaffW`, `pirfW`), `er_sl_eq`'s
spec from its lookup alone (`erSlEq_spec'`) and `rdW_of_get`. (`ctor_family` is now the core's,
`WhnfIota.lean`; the old model and its twin block, and `rec_rule_k_of`, `rec_rule_eta_of`,
`rec_rule_bits`, left with the sync.)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Stubs

open L.Arena L.Ind

/-! ## Models (callees through `callW`) and their specs -/

/-- The fuel adapter `get_app_fn_f(f, e)`: `get_app_fn(e)` at `f = CWF`. -/
def gaffW (p : Prog) (n : Nat) (m : Mem) (f e : Word) : Option (List Word × Mem) :=
  if f ≠ CWF then none else
  ntBW (callW p n "get_app_fn" [e] m) fun r m' => some ([r.headD 0], m')

/-- The fuel adapter `pi_result_f(f, e)`: `pi_result(e)` at `f = CWF`. -/
def pirfW (p : Prog) (n : Nat) (m : Mem) (f e : Word) : Option (List Word × Mem) :=
  if f ≠ CWF then none else
  ntBW (callW p n "pi_result" [e] m) fun r m' => some ([r.headD 0], m')

theorem gaff_spec (p : Prog) (hp : p.lookup "get_app_fn_f" = some getAppFnFL) (n : Nat) (s₀ : St)
    (f e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "get_app_fn_f" [f, e]
    ⦃fun r s' => LocEq s' s₀ ∧ gaffW p n s₀.mem f e = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, getAppFnFL]
  sym only [lang_grind, arena_grind] =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, callW_spec p n "get_app_fn"] <;>
    finish (gen := 20) [gaffW, ntBW, CWF]

theorem pirf_spec (p : Prog) (hp : p.lookup "pi_result_f" = some piResultFL) (n : Nat) (s₀ : St)
    (f e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pi_result_f" [f, e]
    ⦃fun r s' => LocEq s' s₀ ∧ pirfW p n s₀.mem f e = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, piResultFL]
  sym only [lang_grind, arena_grind] =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, callW_spec p n "pi_result"] <;>
    finish (gen := 20) [pirfW, ntBW, CWF]

theorem rdW_of_get {b : Array Word} {q : Word} {w : Word} (h : b[q.toNat]? = some w) : rdW b q = w := by
  simp [rdW, h]

theorem erSlEq_spec' (p : Prog) (hp : p.lookup "er_sl_eq" = some L.Ind.erSlEq) (n : Nat) :
    ∀ (s₀ : St) (o1 l1 o2 l2 : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "er_sl_eq" [o1, l1, o2, l2]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if erSlEqB (erRd s₀.mem) o1 l1 o2 l2 then 1 else 0; ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ o1 l1 o2 l2; rw [invoke_eq _ hp]; simp only [callFn, L.Ind.erSlEq]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o1 l1 o2 l2
    rw [invoke_eq _ hp]
    simp only [callFn, L.Ind.erSlEq]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ld64_rdT_spec, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE, ih] <;>
      finish (gen := 20) [rdW_eq]

end L.Stubs
