import ConAgua.Arena.ConstsResolveF
import ConAgua.Arena.StageInst1
import ConAgua.Arena.WhnfIota

/-!
# `consts_resolve_ffast`'s model (lane `indproofs4`, helper `memo`)

The program- and fuel-free model `crfF := callF crfP "consts_resolve_ffast"` (the recipe of
`IndReal.lean`) over the walk's program `crfP` (lane `tails`' `crfProg` with the environment and
pin reads it calls); it writes only its memo table `CRM` (155) and the memo's epoch and count
(`CTL[158]`, `CTL[159]`). Kept low (below `IndSumSpec/StructProjArgP`, whose models call it); the refinement
`crfF_ok` is in `IndRealMemoCr.lean`, above lane `tails`' `ConstsResolveFRefine2`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- `consts_resolve_ffast`'s functions and the reads it calls. -/
def crfP : Prog := L.Stubs.crfProg ++
  [("e_view", eView), ("is_str_lit", isStrLitL), ("env_find", envFindL), ("env_row_get", envRowGetL),
    ("env_ix", envIxL), ("pin_at", pinAtL)]

/-- The functions `consts_resolve_ffast` reaches. -/
def crfPFns : List FnName :=
  ["consts_resolve_ffast", "crf_go", "cr_leaf", "cr_lit_pins", "pin_found", "crm_find", "crm_put",
    "crm_clear", "e_view", "is_str_lit", "env_find", "env_row_get", "env_ix", "pin_at"]

theorem crfP_closed : closedA crfP [155] [158, 159] crfPFns = true := by decide +kernel

/-- The program bundle. -/
abbrev CrfF (p : Prog) : Prop := ProgHas p crfP

/-- **The model of `consts_resolve_ffast`** (program- and fuel-free). -/
noncomputable def crfF (m : Mem) (args : List Word) : Option (List Word × Mem) :=
  callF crfP "consts_resolve_ffast" m args

theorem crfF_spec (p : Prog) (hp : CrfF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "consts_resolve_ffast" args
    ⦃fun r s' => LocEq s' s₀ ∧ crfF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  callF_spec crfP_closed (hp.agree crfPFns) (by decide) n s₀ args

/-- `consts_resolve_ffast` writes only its memo table. -/
theorem crfF_frame {m m' : Mem} {args r : List Word} (h : crfF m args = some (r, m')) :
    MemFrame [155] [158, 159] m m' := by
  obtain ⟨n, hc⟩ := callF_run h
  exact (run_memFrame crfP_closed (by decide) (run_of_callW hc)).1

end L.Ind
