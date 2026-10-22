import ConRon.Arena.Main

/-!
# The e2e reference: the twin's pipeline, whole or without the prelude (lane `e2e`)

`e2e-ref FILE [--no-prelude] [--pins=N]` runs con-ron's arena checker (the vendored twin, compiled
by Lean) on the whole file as one buffer (`parseBytes`, what `front_run` refines), at the pin list
`natOpPinSets.take N` (default `0`: the empty list, while the program's readers read the ROM, whose
`L.Rom.romPins = []`; `1` once they read the pin-data buffer `lake exe romgen` writes), in
`.verified` mode, and prints
`verdict CODE MESSAGE` (0 accept, 1 reject, 2 decline, 3 error), the exit codes of
`con-ron-lean`.

`--no-prelude` is the pipeline the e2e lane's partial L program runs while the prelude stages have
no L code: no `builtinPreludeE` (an empty prelude) and no `preparePrelude` (the parsed records in
stream order). It is not the checker; it is the reference for L's partial pipeline.
-/

namespace L.E2E.Ref

open ConRon.Arena
open ConLeche (CheckMode NatOpPinSet)

def pipeline (b : ByteArray) (withPrelude : Bool) (pins : List NatOpPinSet) :
    AM (Except ConRon.Arena.CheckError Nat) := do
  internReservedPins
  let pre ← if withPrelude then
      match ← Frontend.builtinPreludeE with
      | .error (e, n) => return .error (Frontend.atLine e n)
      | .ok pre => pure pre
    else pure ⟨#[]⟩
  match ← Frontend.parseBytes b with
  | .error (e, n) => return .error (Frontend.atLine e n)
  | .ok r =>
    let records := r.decls.size
    let ds ← if withPrelude then Frontend.preparePrelude pre r.decls else pure r.decls
    let ipins ← internAllPins pins
    match ← installThenCheck .verified ipins ds with
    | .error (e, n) => pure (.error (atDecl e n))
    | .ok _ => pure (.ok records)

def run (b : ByteArray) (withPrelude : Bool) (pins : List NatOpPinSet) :
    Except ConRon.Arena.CheckError Nat :=
  match (pipeline b withPrelude pins).run (AState.init EStore.empty) with
  | .error e => .error e
  | .ok (v, _) => v

end L.E2E.Ref

open ConRon.Arena in
def main (args : List String) : IO UInt32 := do
  let withPrelude := !args.contains "--no-prelude"
  let npins := (args.findSome? fun a => if a.startsWith "--pins=" then (a.drop 7).toString.toNat? else none).getD 0
  let some file := args.find? (!·.startsWith "--") | IO.eprintln "usage: e2e-ref FILE [--no-prelude] [--pins=N]"; return 3
  let b ← IO.FS.readBinFile file
  match L.E2E.Ref.run b withPrelude (ConLeche.natOpPinSets.take npins) with
  | .ok n => IO.println s!"verdict 0 accepted {n} declarations"; return 0
  | .error e =>
    IO.println s!"verdict {e.exitCode} {(e.message.take 300).replace "\n" " "}"
    return e.exitCode
