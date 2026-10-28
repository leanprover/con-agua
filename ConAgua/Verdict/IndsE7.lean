import ConAgua.Arena.IndT.Pass
/-!
# `check_block_inds`' error claim

`checkBlockIndsE_claim`: the error half of `check_block_inds`' refinement (`cbi_ref`, `Install4`),
in the shape the block pass's claim reads, under `IndsG` (the claims of `check_constant_val`,
`check_sum_tele` and the core stubs).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)


namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **`check_block_inds`' error claim** (`checkBlockInds_refinesC`'s shape): `cbi_ref`'s error
half. -/
theorem checkBlockIndsE_claim {p : Prog} (hG : IndsG p) : CheckBlockIndsE p := by
  intro hq dn vis fe env henv hV hOpf hLC hApd hCrk hLz hP s₀ a pp isRec bs b hC hqd hsrc hcx hb hA hk bsP
    hbsP hfe hcoh hlpsDn F hF e he
  cases F with
  | zero =>
    obtain ⟨e', he', h0⟩ := callE_zero p "check_block_inds" [vis, pp, isRec] s₀.mem
    rw [he] at he'; cases he'; exact ErrClaim.of_cls0 h0
  | succ n =>
  exact RefE.run_err (cbiE_spec p hP (n + 1) ⟨s₀.mem, Locals.init []⟩ vis pp isRec) hG.nv hG
    (cbi_ref hq henv hV hOpf hLC hApd hCrk hLz hP n (by omega) hC hqd hsrc hcx hb hA hk hbsP hfe hcoh hlpsDn) he

end L.Ind
