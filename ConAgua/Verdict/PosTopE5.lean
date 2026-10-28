import ConAgua.Verdict.PosTopEMono
import ConAgua.Verdict.IndA3
import ConAgua.Arena.IndT.Positivity
/-!
# `check_block_positivity`'s and `nest_seeds`' error claims, discharged (lane `verdicts-b`,
helper `ia2`, fork `top`)

The generated statements `CheckBlockPositivityE` and `NestSeedsE` (`IndA3.lean`), the error halves of
`cbp_ref` (`IndT/Positivity`, under the walk's `NbG` and `check_struct_field_sorts_i`'s
`CheckStructFieldSortsIE`) and `nsd_ref` (under `NbG`); the fuels below the ok refinement's by
`callE_err_mono`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dCtx dCtors dOutss dState)

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section claims
variable {p : Prog}

/-- **`check_block_positivity`'s error claim, discharged**: the generated statement
(`CheckBlockPositivityE`), from the walk's refinement (`NbG`), `check_struct_field_sorts_i`'s and the
`nvFns` text; the fuels below `3` by `callE_err_mono`. -/
theorem checkBlockPositivityE_claim (hG : NbG p)
    (eCsf : CheckStructFieldSortsIE p) : CheckBlockPositivityE p := by
  intro hq hIlpf dn vis fe env henv hOpf hLC hLT hApd hP fs hclP hfa s₀ a₀ q cvO cvL caO caL P cvTas css hC hqd
    hsrc hcv hcss hPM hA hk pP cvsP cssP hpP hcvP hcssP hfe hT hct F hF e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  obtain ⟨n, hn⟩ : ∃ n, max F 3 = n + 3 := ⟨max F 3 - 3, by omega⟩
  exact RefE.run_err (cbpE_spec p hP (n + 3) s₀ vis q cvO cvL caO caL) hG.nv ⟨hG, eCsf⟩
    (cbp_ref hq hIlpf henv hOpf hLC hLT hApd hP hclP hfa n (by omega) hC hqd hsrc hcv hcss hPM hA hk hpP hcvP
      hcssP hfe hT hct) (callE_err_mono (show F ≤ n + 3 by omega) he hk0)

/-- **`nest_seeds`' error claim, discharged**: the generated statement (`NestSeedsE`), the error
half of `nsd_ref` (under `NbG`). -/
theorem nestSeedsE_claim (hG : NbG p) : NestSeedsE p := by
  intro hL hq hIlpf hLC dn vis fe env henv s₀ a₀ ctx sO sL ns c seeds NS hC hU hhi hsl hsd hns hP hA ctxP seedsP nsP
    hc hctx hseedsP hnsP hw F hF e he
  exact RefE.run_err (nsdE_spec p hL F ⟨s₀.mem, Locals.init []⟩ vis ctx sO sL ns) hG.nv hG
    (nsd_ref hL hq hIlpf hLC dn vis fe henv ctx c hc F hF s₀.mem a₀ sO sL ns seeds NS seedsP nsP hC hU hhi hsl hsd hns
      hP hA hctx hseedsP hnsP hw) he

end claims

end L.Ind
