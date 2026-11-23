module

public import ConAgua.Arena.IndParts
public import ConAgua.Arena.IndInstall
public import ConAgua.Arena.IndSum
public import ConAgua.Arena.IndPos
public import ConAgua.Arena.IndPos2
public import ConAgua.Arena.RecClass
public import ConAgua.Arena.RecGen
public import ConAgua.Arena.RecCheck
public import ConAgua.Arena.IndStream
public import ConAgua.Arena.IndDeclConsts
public import ConAgua.Arena.IotaRel

@[expose] public section

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
    recGenFns ++ recCheckFns ++ indStreamFns ++ indDeclConstsFns ++ iotaFrameFns ++ iotaRelFns ++
    libFns ++ stubFns ++ masterFns

end L.Ind
