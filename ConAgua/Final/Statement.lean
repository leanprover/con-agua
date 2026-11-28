module

public import ConAgua.Layout
public import ConAgua.L.Semantics
meta import ConAgua.Layout
meta import ConAgua.L.Semantics

@[expose] public section

/-!
# The final theorem's target-independent vocabulary: the verdict and the loaded memory

This file holds what the target-independent and machine-level final statements share: `ACCEPT`
and the loaded memory `loadMem`.
-/

namespace ConAgua.Final

open L

/-- The verdict word `check` returns first for accept. Not `0`, `1` or `2`, so that a status word
or an unset register is never read as accept. -/
def ACCEPT : Word := 0x4143_4345_5054

/-- The memory the loader sets up: the input bytes in byte array `IN`, the pin data in byte array
`Rom.PB`, and every word array `s` of `sz s` words, all zero (every other byte array empty). -/
def loadMem (b pb : ByteArray) (sz : TieredArray → Nat) : Mem :=
  { bytes := fun a => if a = IN then b.data else if a = Rom.PB then pb.data else #[]
    words := fun s => Array.replicate (sz s) 0 }

end ConAgua.Final
