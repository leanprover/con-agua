import ConAgua.Rom.PinStream

/-!
# `romgen OUT`: write the pin-data buffer (lane `romload`)

Writes `pinBuffer (natOpPinSets.take N)` (default `N = 1`) (`ConAgua/Rom/PinStream.lean`): the checker's startup data and
con-leche's first `N` `Nat`-operation pin variants (the first is the repository toolchain's). Not trusted: the buffer
is an input of the checker like the file it checks (DESIGN.md, "The pin data as an input").
-/

open L.Rom

def main (args : List String) : IO UInt32 := do
  let some out := args.head? | IO.eprintln "usage: romgen OUT [N]"; return 2
  let k := ((args.drop 1).head?.bind String.toNat?).getD 1
  let pins := ConLeche.natOpPinSets.take k
  let t0 ← IO.monoMsNow
  let bytes := pinBuffer pins
  IO.FS.writeBinFile out (ByteArray.mk bytes.toArray)
  let t1 ← IO.monoMsNow
  IO.println s!"{out}: {bytes.length} bytes ({romData.length} startup data, {pins.length} variant(s)), {t1 - t0} ms"
  return 0
