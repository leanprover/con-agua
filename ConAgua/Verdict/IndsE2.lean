import ConAgua.Arena.CrOKFrame
import ConAgua.Arena.DeclValSpec
import ConAgua.Arena.IndInstallSpec.IagW
import ConAgua.Arena.IndInstallSpec.InstallRec2Tele
import ConAgua.Arena.IndRealApdT
import ConAgua.Arena.KnotEntry
import ConAgua.Arena.Verdict
import ConRon.Bridge.Inductives.BlockInstall
import ConAgua.Verdict.IndAGen

/-!
# `check_block_inds`' callees: the error-claim statements (lane `verdicts-b`, helper `ia2-inds`)
-/

namespace L.Ind

open L.Arena

err_stmt CheckBlockTeleE := checkBlockTele_refinesC fuel n
err_stmt CheckBlockTelesE := checkBlockTeles_refinesC fuel n
err_stmt CheckBlockAgreeE := checkBlockAgree_refinesC fuel n
err_stmt CheckBlockAgreeOneE := checkBlockAgreeOne_refinesC fuel n
err_stmt CheckBlockDomsAtE := checkBlockDomsAt_refinesC fuel n

end L.Ind
