import ConAgua.Arena.Prelude
import ConAgua.Compiler.WFSplit

/-!
# The startup data as a byte literal

`romDataLit` is `romData` (the encoded pin names, reserved names and structured constants,
`Arena/Prelude.lean`) evaluated once by compiled code and written as a literal (`bytes_lit%`).
`pb_check` reads it (`len(romDataLit.c8)`, `romDataLit.c8[i]`): compiling or checking that
function makes the kernel walk the bytes, and from `romData`'s definition it would first run the
encoders (6 s and 1.5 GB per kernel check). `romDataLit_eq` relates the
two, checked once here.
-/

namespace L.Rom

set_option maxRecDepth 100000 in
/-- `romData` as a literal. -/
def romDataLit : List UInt8 := bytes_lit% romData

set_option maxRecDepth 100000 in
theorem romDataLit_eq : romDataLit = romData := by decide +kernel

end L.Rom
