import ConAgua.Rom.CIRead
import ConAgua.Arena.DeclRomStubs
import ConAgua.Arena.PromoteProg
import ConAgua.Rom.PinStream

/-!
# The ROM stubs' readers against the twin (lane `integrate`)

A test, not a proof: the L interpreter runs `pb_check`, `intern_reserved_pins` and
`intern_all_pins` on a memory whose byte array `PB` holds `pinBuffer []`, then every entry of
`romCIProg` (`rom_basis_decls(k)`, `rom_basis_decls_a(k)` for `k < 5`, `rom_ci(id)` for `id < 8`,
`rom_cv(id)` for `id < 10`, `rom_expr_pin(id)` for `id < 2`, `rom_and_pin()`), each from the memory after the
startup; the twin runs `internReservedPins`, `internAllPins []` and the same interns. The records
must decode (`decCI`, `decCV`, `basisDec`) to the twin's values, handle for handle; the program
the readers reach passes the compiler's static check.
-/

open L L.Rom L.Arena ConRon.Arena

namespace L.Rom.CITest

/-- The functions the test calls: the readers, the pin-data readers, the store's interners. -/
def pool : Prog :=
  romCIProg ++ romProgPB ++
  [("intern_reserved_pins", internReservedPinsL), ("rom_names_to", romNamesTo),
   ("rom_levels", romLevels), ("rom_lvls_go", romLvlsGo), ("stk_push", stkPush), ("stk_pool", stkPool),
   ("rom_ex_leaf", romExLeaf), ("rom_ex_ref", romExRef), ("rom_ex_one", romExOne),
   ("rom_ex_two", romExTwo), ("memo_get", memoGet)] ++
  L.Ind.libFns ++ promoteProg ++ liftProg ++ litProg ++ appProg ++ bvarProg ++ constProg ++
  forallProg ++ fvarProg ++ lamProg ++ letProg ++ lsProg ++ nanonProg ++ nstrProg ++ nnumProg ++
  projProg ++ sortProg ++ succProg ++ zeroProg ++ maxProg ++ imaxProg ++ paramProg

/-- The calls of a statement. -/
def callees : Stmt → List String
  | .seq s t | .ite _ s t => callees s ++ callees t
  | .while _ s => callees s
  | .call _ f _ => [f]
  | _ => []

/-- The program reachable from `todo` (first binding wins), and the names with no binding. -/
partial def closure (todo : List String) (acc : Prog) (miss : List String) : Prog × List String :=
  match todo with
  | [] => (acc.reverse, miss)
  | f :: rest =>
    if acc.any (·.1 == f) || miss.contains f then closure rest acc miss
    else match pool.lookup f with
      | some fd => closure (callees fd.body ++ rest) ((f, fd) :: acc) miss
      | none => closure rest acc (f :: miss)

/-- The readers' entries. -/
def roots : List String :=
  ["rom_basis_decls", "rom_basis_decls_a", "rom_ci", "rom_cv", "rom_expr_pin", "rom_and_pin"]

/-- The program: the startup stages and the readers, with every callee. -/
def prog : Prog × List String :=
  closure (["pb_check", "intern_reserved_pins", "intern_all_pins"] ++ roots) [] []

#guard prog.2.isEmpty

-- The readers with what they call pass the compiler's static check.
#guard L.Compiler.Prog.wfAuto (closure roots [] []).1

/-- The memory after the startup stages (`PB` holding `pinBuffer []`). -/
def startMem : Except String Mem := do
  let sizes := (List.range 210).map fun i =>
    if i == CTL then 256 else if i == L.Ind.IW then 1 <<< 16 else 1 <<< 17
  let m0 : Mem := { initMem sizes with bytes := #[#[], (pinBuffer []).toArray] }
  let step (m : Mem) (f : String) : Except String Mem :=
    match L.run prog.1 100000 f [] m with
    | .ok (_, m') => pure m'
    | .error e => throw s!"{f}: {repr e}"
  let m1 ← step m0 "pb_check"
  let m2 ← step m1 "intern_reserved_pins"
  step m2 "intern_all_pins"

/-- The twin's state after the startup. -/
def startA : Option AState := do
  let ((), sA) ← (internReservedPins.run (AState.init EStore.empty)).toOption
  let (_, a) ← ((internAllPins []).run sA).toOption
  pure a

/-- One L call from the startup memory: its results and the memory after. -/
def callL (m : Mem) (f : String) (w : Word) : Except String (List Word × Mem) :=
  match L.run prog.1 100000 f [w] m with
  | .ok r => pure r
  | .error e => throw s!"{f}({w}): {repr e}"

/-- The twin's value of a stub call and the state after. -/
def twin {α : Type} (a : AState) (x : AM α) : Except String α :=
  match x.run a with
  | .ok (v, _) => pure v
  | .error _ => throw "twin failed"

/-- Run every check; the list of failures. -/
def checks : Except String (List String) := do
  let m ← startMem
  let some a := startA | throw "twin startup failed"
  let dn := denoteN a.store.lss.ls.ns
  let mut bad : List String := []
  for k in List.range 5 do
    let (r, m') ← callL m "rom_basis_decls" (UInt64.ofNat k)
    let v ← twin a (BasisKind.decls (L.Ind.basisOfW k))
    if L.Arena.basisDec dn (r.headD 0).toNat (r.tail.headD 0).toNat m' != some v then
      bad := bad ++ [s!"rom_basis_decls({k})"]
    let (r, m') ← callL m "rom_basis_decls_a" (UInt64.ofNat k)
    let v ← twin a (BasisKind.declsA (L.Ind.basisOfW k))
    if L.Arena.basisDec dn (r.headD 0).toNat (r.tail.headD 0).toNat m' != some v then
      bad := bad ++ [s!"rom_basis_decls_a({k})"]
  for i in List.range 8 do
    let (r, m') ← callL m "rom_ci" (UInt64.ofNat i)
    let v ← twin a (L.Ind.romCiT i)
    if decCI (L.Ind.erA m') dn (r.headD 0).toNat != some v then bad := bad ++ [s!"rom_ci({i})"]
  for i in List.range 10 do
    let (r, m') ← callL m "rom_cv" (UInt64.ofNat i)
    let v ← twin a (L.Ind.romCvT i)
    if decCV (L.Ind.erA m') (r.headD 0).toNat != some v then bad := bad ++ [s!"rom_cv({i})"]
  for i in List.range 2 do
    let (r, _) ← callL m "rom_expr_pin" (UInt64.ofNat i)
    let v ← twin a (L.Ind.romExprT i)
    if r.headD 0 != v.word.toUInt64 then bad := bad ++ [s!"rom_expr_pin({i})"]
  match L.run prog.1 100000 "rom_and_pin" [] m with
  | .ok (r, m') =>
    let v ← twin a andPinDecls
    if L.Arena.basisDec dn (r.headD 0).toNat (r.tail.headD 0).toNat m' != some v then
      bad := bad ++ ["rom_and_pin()"]
  | .error e => throw s!"rom_and_pin(): {repr e}"
  pure bad

-- The checks pass.
#eval show IO Unit from do
  match checks with
  | .ok [] => IO.println "romCIProg: every record decodes to the twin's value"
  | .ok bad => throw (IO.userError s!"romCIProg: different from the twin: {bad}")
  | .error e => throw (IO.userError e)

end L.Rom.CITest
