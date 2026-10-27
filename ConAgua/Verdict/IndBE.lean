import ConAgua.Arena.CrOKFrame
import ConAgua.Arena.DeclValSpec
import ConAgua.Arena.IndInstallSpec.CapsProg
import ConAgua.Arena.IndInstallSpec.DecCNS
import ConAgua.Arena.IndRealApdT
import ConAgua.Arena.IndRealIlpL
import ConAgua.Arena.IndSumSpec.SumProg
import ConAgua.Arena.IndSumSpec.TblProg
import ConAgua.Arena.KnotEntry
import ConAgua.Arena.RecGenSpec.OcW
import ConAgua.Arena.Verdict
import ConRon.Bridge.Inductives.ClassRead
import ConAgua.Verdict.IndAGen
import ConAgua.Arena.IndRealSctC
import ConAgua.Arena.IndT.RecGen19
import ConAgua.Arena.IndT.Sum2
import ConAgua.Arena.IndT.Sum3
import ConAgua.Arena.IndT.Sum5
import ConAgua.Arena.RecGenSpec.ClassKeyCanon

/-!
# The `indB` family's error claims used by `check_ind_decl`'s pass and tail (lane `verdicts-b`,
helper `ia2`)

Statements only (generated `err_stmt`s of the ok refinements), hypotheses of the `indA` proofs,
discharged by the `indB` helper: `check_sum_tele`, `check_sum_ctors`, `check_struct_field_sorts_i`,
`check_struct_proj_table`, `class_key_of`, `class_majors`.
-/

namespace L.Ind

open L.Arena

err_stmt CheckSumTeleE := checkSumTele_refinesC fuel k
err_stmt CheckSumCtorsE := checkSumCtors_refinesC fuel k
err_stmt CheckStructFieldSortsIE := checkStructFieldSortsI_refinesC fuel n
err_stmt CheckStructProjTableE := checkStructProjTable_refinesC fuel n
err_stmt ClassKeyOfE := classKeyOf_refines fuel k
err_stmt ClassMajorsE := classMajors_refinesC fuel n

end L.Ind
