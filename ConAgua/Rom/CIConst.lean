module

public import ConAgua.Arena.RomExpr
public import ConAgua.Rom.PinRead

@[expose] public section

/-!
# The ROM readers over the program's constant data (lane `ronsync2`)

The structured ROM constants (`romCIData`, `CIEnc.lean`) are part of `romData`, which is the
program's own constant data (`romDataLit`, `DataLit.lean`; `pb_check` compares the pin-data
buffer's prefix against it). The checks read them at each use, as the twin interns each constant
at each use (`internCI`, `internCIList`, …): in a job too, where the pin-data buffer `PB` is not
mapped (entry 2 maps no byte array) but the constant data is.

So `CIRead.lean`'s readers call a second copy of the ROM readers, over the constant data: the
ROM readers of `ConAgua/Arena/Rom*.lean` at `rom := romDataLit`, each call to one of them renamed
to its copy (`romC`: `rom_u64` ↦ `rom_u64_c`, …). The startup's readers (`romProgPB`) are the
same readers over `PB`.
-/

namespace L

/-- The calls of a statement renamed by `ρ`. -/
def Stmt.renameCalls (ρ : FnName → FnName) : Stmt → Stmt
  | .seq s t => .seq (renameCalls ρ s) (renameCalls ρ t)
  | .ite c s t => .ite c (renameCalls ρ s) (renameCalls ρ t)
  | .while c s => .while c (renameCalls ρ s)
  | .call xs f args => .call xs (ρ f) args
  | s => s

-- con-ron: none — a copy of an L function with its calls renamed, no twin
/-- A function with its calls renamed by `ρ`. -/
def FunDecl.renameCalls (ρ : FnName → FnName) (fd : FunDecl) : FunDecl :=
  { fd with body := fd.body.renameCalls ρ }

end L

namespace L.Rom

open L.Arena

/-- The ROM readers that read the bytes, directly or through each other. -/
def romCNames : List FnName :=
  ["rom_u64", "rom_put", "rom_name", "rom_level", "rom_levels", "rom_lvls_go", "rom_expr",
   "rom_ex_ref", "rom_ex_leaf", "rom_ex_one", "rom_ex_two", "rom_exprs_to"]

/-- A ROM reader's name ↦ its copy over the constant data. -/
def romC (f : FnName) : FnName := if f ∈ romCNames then f ++ "_c" else f

/-- The ROM readers over the constant data `romDataLit`. -/
-- con-ron: none — the ROM reader (L has constant bytes where the twin has con-leche values)
@[no_expose] def romU64C : FunDecl := (romU64 romDataLit).renameCalls romC
-- con-ron: none — the ROM reader (L has constant bytes where the twin has con-leche values)
@[no_expose] def romPutC : FunDecl := (romPut romDataLit).renameCalls romC
-- con-ron: none — the ROM reader (L has constant bytes where the twin has con-leche values)
@[no_expose] def romNameC : FunDecl := (romName romDataLit).renameCalls romC
-- con-ron: none — the ROM reader (L has constant bytes where the twin has con-leche values)
@[no_expose] def romLevelC : FunDecl := (romLevel romDataLit).renameCalls romC
-- con-ron: none — the ROM reader (L has constant bytes where the twin has con-leche values)
@[no_expose] def romLevelsC : FunDecl := romLevels.renameCalls romC
-- con-ron: none — the ROM reader (L has constant bytes where the twin has con-leche values)
@[no_expose] def romLvlsGoC : FunDecl := romLvlsGo.renameCalls romC
-- con-ron: none — the ROM reader (L has constant bytes where the twin has con-leche values)
@[no_expose] def romExprC : FunDecl := (romExpr romDataLit).renameCalls romC
-- con-ron: none — the ROM reader (L has constant bytes where the twin has con-leche values)
@[no_expose] def romExRefC : FunDecl := romExRef.renameCalls romC
-- con-ron: none — the ROM reader (L has constant bytes where the twin has con-leche values)
@[no_expose] def romExLeafC : FunDecl := romExLeaf.renameCalls romC
-- con-ron: none — the ROM reader (L has constant bytes where the twin has con-leche values)
@[no_expose] def romExOneC : FunDecl := romExOne.renameCalls romC
-- con-ron: none — the ROM reader (L has constant bytes where the twin has con-leche values)
@[no_expose] def romExTwoC : FunDecl := romExTwo.renameCalls romC
-- con-ron: ConRon/Arena/Frontend/Readback.lean:263-269 ConRon.Arena.Frontend.internExprList
@[no_expose] def romExprsToC : FunDecl := romExprsTo.renameCalls romC

/-- **The ROM readers over the constant data**, by their copies' names. -/
def romConstProg : Prog :=
  [("rom_u64_c", romU64C), ("rom_put_c", romPutC), ("rom_name_c", romNameC),
   ("rom_level_c", romLevelC), ("rom_levels_c", romLevelsC), ("rom_lvls_go_c", romLvlsGoC),
   ("rom_expr_c", romExprC), ("rom_ex_ref_c", romExRefC), ("rom_ex_leaf_c", romExLeafC),
   ("rom_ex_one_c", romExOneC), ("rom_ex_two_c", romExTwoC), ("rom_exprs_to_c", romExprsToC)]

end L.Rom
