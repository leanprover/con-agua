import ConAgua.Verdict.IndA4

/-!
# `check_block_idx_sorts`' error claim

`CheckBlockIdxSortsE` (the `err_stmt` of `checkBlockIdxSorts_refinesC`) is the error half of
`iisr_ref` (`Arena/IndT/IdxSorts`), from `check_struct_field_sorts_i`'s claim.
-/

open ConRon.Arena

namespace L.Ind

open L.Arena

/-- **`check_block_idx_sorts`' error claim**, from `check_struct_field_sorts_i`'s. -/
theorem checkBlockIdxSortsE_claim {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (eSF : CheckStructFieldSortsIE p) : CheckBlockIdxSortsE p := by
  intro hq dn vis fe env henv hOpf hLC hLT hP s₀ a₀ pp mo ml co cl bs mss cvs hC hA hqd hsrc hmss hcvs
    bsP cvsP hbsP hcvsP hws hfe F hF e he
  exact RefE.run_err (iisrE_spec p hP hOpf F ⟨s₀.mem, Locals.init []⟩ vis pp mo ml co cl) hnv eSF
    (iisr_ref hq henv hLC hLT hP pp bs F hF hC hA hqd hsrc hmss hcvs hbsP hcvsP hws hfe) he

end L.Ind
