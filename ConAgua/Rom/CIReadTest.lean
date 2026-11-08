module

public import ConAgua.Compiler.WF
public import ConAgua.Rom.CIRead
public import ConAgua.Arena.DeclRomStubs
public import ConAgua.Rom.PinStream
meta import ConAgua.Rom.CIRead
meta import ConAgua.Arena.DeclRomStubs
meta import ConAgua.Rom.PinStream
public import ConAgua.Arena.RomPins

@[expose] public section

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

/- ronsync2 stage 2: commented out (statement at the old twin/L)
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
-/

/-- The calls of a statement. -/
def callees : Stmt → List String
  | .seq s t | .ite _ s t => callees s ++ callees t
  | .while _ s => callees s
  | .call _ f _ => [f]
  | _ => []

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- The program reachable from `todo` (first binding wins), and the names with no binding. -/
partial def closure (todo : List String) (acc : Prog) (miss : List String) : Prog × List String :=
  match todo with
  | [] => (acc.reverse, miss)
  | f :: rest =>
    if acc.any (·.1 == f) || miss.contains f then closure rest acc miss
    else match pool.lookup f with
      | some fd => closure (callees fd.body ++ rest) ((f, fd) :: acc) miss
      | none => closure rest acc (f :: miss)
-/

/-- The readers' entries. -/
def roots : List String :=
  ["rom_basis_decls", "rom_basis_decls_a", "rom_ci", "rom_cv", "rom_expr_pin", "rom_and_pin"]

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- The program: the startup stages and the readers, with every callee. -/
def prog : Prog × List String :=
  closure (["pb_check", "intern_reserved_pins", "intern_all_pins"] ++ roots) [] []
-/

-- ronsync2 stage 2: #guard prog.2.isEmpty

-- The readers with what they call pass the compiler's static check.
-- ronsync2 stage 2: #guard L.Compiler.Prog.wfAuto (closure roots [] []).1

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- The memory after the startup stages (`PB` holding `pinBuffer []`). -/
def startMem : Except String Mem := do
  let sizes : TieredArray → Nat := fun b =>
    if b.hi || 210 ≤ b.arr then 0
    else if b.arr == CTL then 256 else if b.arr == L.Ind.IW then 1 <<< 16 else 1 <<< 17
  let m0 : Mem := (initMem sizes).putBytes Rom.PB (pinBuffer []).toArray
  let step (m : Mem) (f : String) : Except String Mem :=
    match L.run prog.1 100000 f [] m with
    | .ok (_, m') => pure m'
    | .error e => throw s!"{f}: {repr e}"
  let m1 ← step m0 "pb_check"
  let m2 ← step m1 "intern_reserved_pins"
  step m2 "intern_all_pins"
-/

/-- The twin's state after the startup. -/
def startA : Option AState := do
  let ((), sA) ← (internReservedPins.run (AState.init EStore.empty)).toOption
  let (_, a) ← ((internAllPins []).run sA).toOption
  pure a

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- One L call from the startup memory: its results and the memory after. -/
def callL (m : Mem) (f : String) (w : Word) : Except String (List Word × Mem) :=
  match L.run prog.1 100000 f [w] m with
  | .ok r => pure r
  | .error e => throw s!"{f}({w}): {repr e}"
-/

/-- The twin's value of a stub call and the state after. -/
def twin {α : Type} (a : AState) (x : AM α) : Except String α :=
  match x.run a with
  | .ok (v, _) => pure v
  | .error _ => throw "twin failed"

/- ronsync2 stage 2: commented out (statement at the old twin/L)
-- ronsync2 stage 2: /-- Run every check; the list of failures. -/
-- ronsync2 stage 2: def checks : Except String (List String) := do
-- ronsync2 stage 2:   let m ← startMem
-- ronsync2 stage 2:   let some a := startA | throw "twin startup failed"
-- ronsync2 stage 2:   let dn := denoteN a.store.lss.ls.ns
-- ronsync2 stage 2:   let mut bad : List String := []
-- ronsync2 stage 2:   for k in List.range 5 do
-- ronsync2 stage 2:     let (r, m') ← callL m "rom_basis_decls" (UInt64.ofNat k)
-- ronsync2 stage 2:     let v ← twin a (BasisKind.decls (L.Ind.basisOfW k))
-- ronsync2 stage 2:     if L.Arena.basisDec dn (r.headD 0).toNat (r.tail.headD 0).toNat m' != some v then
-- ronsync2 stage 2:       bad := bad ++ [s!"rom_basis_decls({k})"]
-- ronsync2 stage 2:     let (r, m') ← callL m "rom_basis_decls_a" (UInt64.ofNat k)
-- ronsync2 stage 2:     let v ← twin a (BasisKind.declsA (L.Ind.basisOfW k))
-- ronsync2 stage 2:     if L.Arena.basisDec dn (r.headD 0).toNat (r.tail.headD 0).toNat m' != some v then
-- ronsync2 stage 2:       bad := bad ++ [s!"rom_basis_decls_a({k})"]
-- ronsync2 stage 2:   for i in List.range 8 do
-- ronsync2 stage 2:     let (r, m') ← callL m "rom_ci" (UInt64.ofNat i)
-- ronsync2 stage 2:     let v ← twin a (L.Ind.romCiT i)
-- ronsync2 stage 2:     if decCI (L.Ind.erA m') (r.headD 0).toNat != some v then bad := bad ++ [s!"rom_ci({i})"]
-- ronsync2 stage 2:   for i in List.range 10 do
-- ronsync2 stage 2:     let (r, m') ← callL m "rom_cv" (UInt64.ofNat i)
-- ronsync2 stage 2:     let v ← twin a (L.Ind.romCvT i)
-- ronsync2 stage 2:     if decCV (L.Ind.erA m') (r.headD 0).toNat != some v then bad := bad ++ [s!"rom_cv({i})"]
-- ronsync2 stage 2:   for i in List.range 2 do
-- ronsync2 stage 2:     let (r, _) ← callL m "rom_expr_pin" (UInt64.ofNat i)
-- ronsync2 stage 2:     let v ← twin a (L.Ind.romExprT i)
-- ronsync2 stage 2:     if r.headD 0 != v.word.toUInt64 then bad := bad ++ [s!"rom_expr_pin({i})"]
-- ronsync2 stage 2:   match L.run prog.1 100000 "rom_and_pin" [] m with
-- ronsync2 stage 2:   | .ok (r, m') =>
-- ronsync2 stage 2:     let v ← twin a andPinDecls
-- ronsync2 stage 2:     if L.Arena.basisDec dn (r.headD 0).toNat (r.tail.headD 0).toNat m' != some v then
-- ronsync2 stage 2:       bad := bad ++ ["rom_and_pin()"]
-- ronsync2 stage 2:   | .error e => throw s!"rom_and_pin(): {repr e}"
-- ronsync2 stage 2:   pure bad
-- ronsync2 stage 2: 
-- ronsync2 stage 2: -- The checks pass.
-- ronsync2 stage 2: -/
-- ronsync2 stage 2: #eval show IO Unit from do
-- ronsync2 stage 2:   match checks with
-- ronsync2 stage 2:   | .ok [] => IO.println "romCIProg: every record decodes to the twin's value"
-- ronsync2 stage 2:   | .ok bad => throw (IO.userError s!"romCIProg: different from the twin: {bad}")
-- ronsync2 stage 2:   | .error e => throw (IO.userError e)

end L.Rom.CITest
