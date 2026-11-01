module

import ConAgua.Arena.WhnfIotaRecRefine3
public import ConAgua.Arena.WhnfCoreAppLoop
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.WhnfIotaRecRefine2

@[expose] public section
/-!
# `iota_rec_at`'s verdict claims, the top (lane `verdicts-b`, helper `k2`)

`iota_rec_at`, `iota_rec_c` and `iota_rec_major` have no verdict site of their own: their claims
are `prepare_major`'s and `iota_rec_fire`'s, propagated (`at_ref`'s error half, `iotaRecAtE_of`:
`IotaRecAtE`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

theorem whnfIotaE_nv : ∀ f ∈ ["iota_rec_head", "env_find", "ls_node", "peel_pis", "intern_bvar",
    "get_app_fn", "find_rule", "get_app_args", "rule_rhs_at", "mk_app_n", "mk_app_n_from",
    "rec_fire_levels", "iota_case3", "lvls_eq_c", "const_ty_at", "rec_rule_k", "is_ctor_app",
    "is_str_lit", "erec_push", "rec_fire_args", "stack_cover"], f ∈ L.Checker.nvFns :=
  _root_.L.Checker.nv_sub (by decide +kernel)

section iotaTop
variable (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p) (hw : WhnfCallees p)
  (hsup : ∀ fe : IFEnv, SupKeep fe) (hmtc : MajorToCtorOK p) (hEI : ErecKeptInst p)
  (hER : ErecKeptRec p) (hEK : ErecKeptKnot p) (hnv : closedNV p L.Checker.nvFns = true)
  (hPM : PrepareMajorE p) (hF : IotaRecFireE p)

include hp hc hw hsup hmtc hEI hER hEK hnv hPM hF in
/-- **`IotaRecAtE`**: `iota_rec_at`'s verdicts are `iota_rec_major`'s, through `iota_rec_c`
(`at_ref`'s error half). -/
theorem iotaRecAtE_of : IotaRecAtE p :=
  fun N hk hkE F s₀ a₀ dn vis fe M eb mode d hd so sn xs hnF hn62 hpre hhd hsa hsat =>
    RefE.coreSpecE (irAtE_spec p hp.iotaRecAt hp.recC hp.major (N + 1) s₀ mode vis d hd so sn) hnv
      ⟨hkE, hnv, hPM, hF⟩ (at_ref p hp hc hw hsup hmtc hEI hER hEK N hk F s₀ a₀ dn vis fe M eb mode d hd
        so sn xs hnF hn62 hpre hhd hsa hsat)

end iotaTop

end L.Arena
