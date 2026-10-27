import ConAgua.Arena.CrOKFrame
import ConAgua.Arena.DeclValSpec
import ConAgua.Arena.IndInstallSpec10
import ConAgua.Arena.IndRealApdT
import ConAgua.Arena.KnotEntry
import ConAgua.Verdict.IndAGen
import ConRon.Bridge.Inductives.BlockInstall

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
