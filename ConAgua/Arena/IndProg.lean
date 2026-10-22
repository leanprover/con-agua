import ConAgua.Arena.IndParts
import ConAgua.Arena.IndInstall
import ConAgua.Arena.IndSum
import ConAgua.Arena.IndPos
import ConAgua.Arena.IndPos2
import ConAgua.Arena.RecClass
import ConAgua.Arena.RecGen
import ConAgua.Arena.RecCheck

/-!
# The inductive stage's whole program (lane `induct`)

Every module's functions, the library, the stubs of other lanes' callees and the master
functions (as stubs here). `indProg_wf`: the modules close over each other — every call names a
function of the program with the right number of arguments (the per-module checks used stubs for
the other modules; this one uses the real ones).
-/

namespace L.Ind

def indProg : Prog :=
  indPartsFns ++ indInstallFns ++ indSumFns ++ indPosFns ++ indPos2Fns ++ recClassFns ++
    recGenFns ++ recCheckFns ++ libFns ++ stubFns ++ masterFns

theorem indProg_wf : L.Compiler.Prog.wf indTab indProg = true :=
  L.Compiler.Prog.wf_of_wfFast (by decide +kernel)

end L.Ind
