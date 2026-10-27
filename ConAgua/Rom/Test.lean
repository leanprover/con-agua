import ConAgua.Arena.RomPins
import ConAgua.Rom.PinRead
import ConAgua.Arena.PromoteProg
import ConAgua.Arena.LiftSpec

/-!
# `romtest BUF`: the L pin stages against the twin's, on a pin-data buffer (lane `romload`)

Runs, in the L interpreter, `pb_check`, `intern_reserved_pins` and `intern_all_pins` (the pin-data
readers of `romProgPB`, the store's interners) on a memory whose byte array `PB` holds the buffer,
then the twin's `internReservedPins` and `internAllPins P` for the list `P` the generator encoded
(`natOpPinSets.take 1`), and compares every pin variant's handles (the 40-word records against the
twin's `INatOpPinSet`s) and the node counts of the expression tables. A test, not a proof.
-/

open L L.Rom L.Arena ConRon.Arena

/-- The functions the pin stages call: the pin-data readers first. -/
def romTestPool : Prog :=
  romProgPB ++
  [("intern_reserved_pins", internReservedPinsL), ("rom_names_to", romNamesTo),
   ("rom_levels", romLevels), ("rom_lvls_go", romLvlsGo), ("stk_push", stkPush), ("stk_pool", stkPool),
   ("rom_ex_leaf", romExLeaf), ("rom_ex_ref", romExRef), ("rom_ex_one", romExOne),
   ("rom_ex_two", romExTwo), ("memo_get", memoGet)] ++
  L.Ind.libFns ++ promoteProg ++ liftProg ++ litProg ++ appProg ++ bvarProg ++ constProg ++
  forallProg ++ fvarProg ++ lamProg ++ letProg ++ lsProg ++ nanonProg ++ nstrProg ++ nnumProg ++
  projProg ++ sortProg ++ succProg ++ zeroProg ++ maxProg ++ imaxProg ++ paramProg

/-- The calls of a statement. -/
def L.Stmt.callees : Stmt → List String
  | .seq s t | .ite _ s t => s.callees ++ t.callees
  | .while _ s => s.callees
  | .call _ f _ => [f]
  | _ => []

/-- The program reachable from `roots` (first binding wins), and the names with no binding. -/
partial def closure (pool : Prog) (todo : List String) (acc : Prog) (miss : List String) :
    Prog × List String :=
  match todo with
  | [] => (acc.reverse, miss)
  | f :: rest =>
    if acc.any (·.1 == f) || miss.contains f then closure pool rest acc miss
    else match pool.lookup f with
      | some fd => closure pool (fd.body.callees ++ rest) ((f, fd) :: acc) miss
      | none => closure pool rest acc (f :: miss)

def main (args : List String) : IO UInt32 := do
  let some file := args.head? | IO.eprintln "usage: romtest BUF [N]"; return 2
  let k := ((args.drop 1).head?.bind String.toNat?).getD 1
  let buf ← IO.FS.readBinFile file
  let (prog, miss) := closure romTestPool ["pb_check", "intern_reserved_pins", "intern_all_pins",
    "rom_pin_sets"] [] []
  IO.println s!"program: {prog.length} functions; unbound: {miss}"
  unless miss.isEmpty do return 1
  let sizes := (List.range 210).map fun i =>
    if i == CTL then 256 else if i == L.Ind.IW then 1 <<< 16 else 1 <<< 19
  let m0 : Mem := { initMem sizes with bytes := #[#[], buf.data] }
  let fuel := 100000
  let t0 ← IO.monoMsNow
  let step (m : Mem) (f : String) : IO Mem := do
    match L.run prog fuel f [] m with
    | .ok (_, m') => pure m'
    | .error e => throw (IO.userError s!"{f}: {repr e}")
  let m1 ← step m0 "pb_check"
  let m2 ← step m1 "intern_reserved_pins"
  let m3 ← step m2 "intern_all_pins"
  let t1 ← IO.monoMsNow
  IO.println s!"L: the three stages in {t1 - t0} ms"
  -- the twin
  let pins := ConLeche.natOpPinSets.take k
  let some (ipins, a) := (do
      let ((), sA) ← (internReservedPins.run (AState.init EStore.empty)).toOption
      (internAllPins pins).run sA |>.toOption) | IO.eprintln "twin failed"; return 1
  let rd (i : Word) : Word := rdW (m3.arr64 EREC) i
  let off := rdW (m3.arr64 CTL) 150
  let cnt := rdW (m3.arr64 CTL) 151
  IO.println s!"variants: L {cnt}, twin {ipins.length}"
  let mut bad := 0
  let mut checked := 0
  for (ip, k) in ipins.zipIdx do
    let r := rd (off + UInt64.ofNat k)
    let hs := [ip.divPin, ip.modPin, ip.gcdPin, ip.landPin, ip.lorPin, ip.xorPin, ip.shiftLeftPin,
      ip.shiftRightPin]
    let ls := [ip.divProofs, ip.modProofs, ip.gcdProofs, ip.landProofs, ip.lorProofs, ip.xorProofs,
      ip.shiftLeftProofs, ip.shiftRightProofs]
    for (h, j) in hs.zipIdx do
      checked := checked + 1
      if rd (r + UInt64.ofNat j) != h.word.toUInt64 then bad := bad + 1
    for (l, j) in ls.zipIdx do
      let o := rd (r + 8 + 2 * UInt64.ofNat j)
      if rd (r + 9 + 2 * UInt64.ofNat j) != UInt64.ofNat l.length then
        bad := bad + 1
        IO.println s!"list {j}: length L {rd (r + 9 + 2 * UInt64.ofNat j)}, twin {l.length}"
      for (h, i) in l.zipIdx do
        checked := checked + 1
        if rd (o + UInt64.ofNat i) != h.word.toUInt64 then bad := bad + 1
    let ts := [ip.divTypePins, ip.modTypePins, ip.gcdTypePins, ip.landTypePins, ip.lorTypePins,
      ip.xorTypePins, ip.shiftLeftTypePins, ip.shiftRightTypePins]
    for (l, j) in ts.zipIdx do
      let o := rd (r + 24 + 2 * UInt64.ofNat j)
      if rd (r + 25 + 2 * UInt64.ofNat j) != UInt64.ofNat l.length then
        bad := bad + 1
        IO.println s!"type pins {j}: length L {rd (r + 25 + 2 * UInt64.ofNat j)}, twin {l.length}"
      for ((n, t), i) in l.zipIdx do
        checked := checked + 2
        if rd (o + 2 * UInt64.ofNat i) != n.word.toUInt64 then bad := bad + 1
        if rd (o + 2 * UInt64.ofNat i + 1) != t.word.toUInt64 then bad := bad + 1
  IO.println s!"handles compared: {checked}, different: {bad}"
  let _ := a
  return (if bad == 0 && cnt == UInt64.ofNat ipins.length then 0 else 1)
