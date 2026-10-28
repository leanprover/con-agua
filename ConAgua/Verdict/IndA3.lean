import ConAgua.Verdict.IndA2
/-!
# `check_block_pass`' error claim

`checkBlockPassE_claim`: the error half of `check_block_pass`' refinement (`pass_ref`, `Pass`), in
the shape `check_block`'s claim reads (`CheckBlockPassE`), from the claims of the pass's five checks
(`PassG`).
-/

open ConRon.Arena

namespace L.Ind

open L.Arena

theorem checkBlockPassE_claim {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true) (hG : PassG p) :
    CheckBlockPassE p := by
  intro hkp env henv hV hOpf hLC hLT hApd hCrk hIlpf hLz hP fs hcl hfs s₀ a dn vis fe p0 isRec bs b hC hq hsrc
    hcx hb hPm hA hk hcoh hden shP hshP hlpsDn F hF e he
  exact RefE.run_err (icpE_spec p hP F ⟨s₀.mem, Locals.init []⟩ vis p0 isRec) hnv hG
    (pass_ref hkp henv hV hOpf hLC hLT hApd hCrk hIlpf hLz hP hcl hfs F hF hC hq hsrc hcx hb hPm hA hk hcoh
      hden hshP hlpsDn) he

end L.Ind
