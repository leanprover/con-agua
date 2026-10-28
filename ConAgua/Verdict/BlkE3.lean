import ConAgua.Verdict.IndA4
/-!
# `check_block_tables`' error claim

`checkBlockTablesE_claim`: `CheckBlockTablesE`, the error half of `ctb_ref` through the call's run,
from `check_struct_proj_table`'s claim in the `StageR` shape (`CheckStructProjTableRE`).
-/

namespace L.Ind

open L.Arena

/-- **`check_block_tables`' error claim** (`CheckBlockTablesE`), from `check_struct_proj_table`'s
in the `StageR` shape (`CheckStructProjTableRE`). -/
theorem checkBlockTablesE_claim {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (eTbl : CheckStructProjTableRE p) : CheckBlockTablesE p :=
  fun hP hp dn pp bs F hF m a vis fe mo ml co cl so sl mss css sss hS hq hsrc hmss hcss hsss hM hA hkeep hok
    hpins hsh hmsP hcsP hssP _ he =>
  RefE.run_err (ctbE_spec p hP F ⟨m, Locals.init []⟩ pp mo ml co cl so sl vis) hnv eTbl
    (ctb_ref hP hp dn pp bs F hF m a vis fe mo ml co cl so sl mss css sss hS hq hsrc hmss hcss hsss hM hA
      hkeep hok hpins hsh hmsP hcsP hssP) he

end L.Ind
