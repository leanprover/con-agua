import ConAgua.Verdict.IndA4
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
/-!
# `check_block_tables`' error claim (lane `verdicts-b`, helper `ia2`, fork `blk`)

`checkBlockTablesE_claim` (`CheckBlockTablesE`, the claim `check_block_tail`'s takes), the error
half of `ctb_ref` (`Arena/IndRealSctC`, under `check_struct_proj_table`'s claim in `tblW_okR`'s
`StageR` shape, `CheckStructProjTableRE`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **`check_block_tables`' error claim** (`CheckBlockTablesE`), the error half of `ctb_ref` (under
`check_struct_proj_table`'s claim in the `StageR` shape, `CheckStructProjTableRE`). -/
theorem checkBlockTablesE_claim {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (eTbl : CheckStructProjTableRE p) : CheckBlockTablesE p := by
  intro hP hp dn pp bs F hF m a vis fe mo ml co cl so sl mss css sss hS hq hsrc hmss hcss hsss hM hA hkeep hok
    hpins hsh hmsP hcsP hssP e he
  exact RefE.run_err (ctbE_spec p hP.one hP.tabs F ⟨m, Locals.init []⟩ pp mo ml co cl so sl vis) hnv eTbl
    (ctb_ref hP hp dn pp bs F hF m a vis fe mo ml co cl so sl mss css sss hS hq hsrc hmss hcss hsss hM hA hkeep
      hok hpins hsh hmsP hcsP hssP) he

end L.Ind
