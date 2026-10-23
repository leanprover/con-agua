import Lean
import ConAgua.Census.Attr

/-!
# The census dump (`lake exe census`)

Usage: `lake exe census ROOT MODULE...` (normally through `scripts/census.py`).

Imports `ROOT` (the module holding the entry point `ConAgua.Final.TwinAccepts`) and computes the
**targets**: every definition of con-ron's arena (`ConRon.*`) and of con-leche (`ConLeche.*`) that
the entry point reaches through definition bodies. Then imports the `MODULE`s (the built L and proof
modules) and reads the census links (`ConAgua/Census/Attr.lean`), with the axioms of every linked
theorem. Prints tab-separated lines for the Python report:

    T   name  module  startLine  endLine  kind      a target (kind: def | partial)
    E   from  to                                    target `from` calls target `to`
    X   name  module  why                           a reached def that is not a target (verbose)
    L   kind  decl  target  label  module  status   a link (status: ok | sorry | local:a,b |
                                                    axioms:a,b | n/a)

What is reached: the VALUE of a definition (not its type), through definitions only (theorems,
types and proofs are not walked into), plus `@[implemented_by]` of an opaque (`partial def`).
What is not a target, but walked through: instances, compiler/elaborator auxiliaries (`match_`,
`proof_`, `_unary`, `_mutual`, `eq_`, recursors, `noConConfusion`, projections, names with
macro scopes). What is neither: type formers (the value is a type), `Prop`-valued definitions
(predicates: spec only), and everything outside `ConRon.*`/`ConLeche.*` (Lean's library).

Module groups: some ConAgua modules declare the same names (`L.Arena.appK₁.appK₂` in `Walk` and in
`Lift`; `main` in the emitters), so one environment cannot import them all. The link pass imports
the modules greedily in groups: on a clash it moves the failing module and everything that imports
it into the next group. Each import runs in a child process of its own (`mainLinks`): Lean never
frees an imported environment, and a failed import leaks what it read, so one process importing
group after group grew past 18 GB.
-/

open Lean

namespace ConAgua.Census

def modOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | none => .anonymous
  | some i => env.header.moduleNames[i.toNat]!

def isOurTier (m : Name) : Bool :=
  (`ConRon).isPrefixOf m || (`ConLeche).isPrefixOf m

/-- The codomain of a type, after all `∀`s, is a sort (type former / predicate). -/
partial def codomain : Expr → Expr
  | .forallE _ _ b _ => codomain b
  | .mdata _ e => codomain e
  | e => e

/-- `n` and its proper prefixes. -/
partial def prefixes : Name → List Name
  | .anonymous => []
  | n => n :: prefixes n.getPrefix

/-- Why `n` is walked through but not counted, or `none` for a target. -/
def notTargetWhy (env : Environment) (n : Name) (ci : ConstantInfo) : Option String :=
  let base := (privateToUserName? n).getD n
  if n.hasMacroScopes then some "macro-scoped"
  else if base.isInternalDetail then some "aux"
  else if isAuxRecursor env n || isNoConfusion env n then some "aux"
  else if Meta.isMatcherCore env n then some "matcher"
  else if base.components.any (fun c => c == `brecOn || c == `below || c == `binductionOn) then
    some "aux"
  -- an instance, or a function the instance's elaboration or `deriving` made inside it
  -- (`instDecidableEqIdx.decEq`, `instHashableAppNode.hash`)
  else if (prefixes n).any (Meta.isInstanceCore env) then some "instance"
  else if env.isProjectionFn n then some "projection"
  else match base with
    | .str _ s =>
      if s == "ctorIdx" || s == "toCtorIdx" || s == "ofNat" && (env.find? base.getPrefix matches
          some (.inductInfo _)) || s == "noConfusionType" || s == "sizeOf_spec" then some "aux"
      else if s.endsWith "_def" || s == "eq_def" then some "aux"
      else match ci with
        | .opaqueInfo _ => none
        | .defnInfo _ => none
        | _ => some "not a definition"
    | _ => some "aux"

/-- Type formers and predicates: neither walked nor counted. -/
def isTypeOrProp (ci : ConstantInfo) : Bool :=
  match codomain ci.type with
  | .sort _ => true
  | _ => false

def depsOf (env : Environment) (n : Name) (ci : ConstantInfo) : Array Name :=
  match ci with
  -- `v.all`: the members of a well-founded mutual block call each other through the block's
  -- `_mutual` auxiliary, which names no member
  | .defnInfo v => v.value.getUsedConstants ++ v.all.toArray.filter (· != n)
  | .opaqueInfo v =>
    match Compiler.getImplementedBy? env n with
    | some i => #[i]
    | none => v.value.getUsedConstants
  | _ => #[]

def rangeOf (env : Environment) (n : Name) : Option DeclarationRanges :=
  declRangeExt.find? (level := .exported) env n <|> declRangeExt.find? (level := .server) env n

/-- The targets reached from `root`, and the target-level call graph. -/
def targets (env : Environment) (root : Name) (verbose : Bool) : IO Unit := do
  -- A node is "target" (counted), "through" (walked, not counted) or skipped.
  let classify (n : Name) : Option (Option String) := do
    let ci ← env.find? n
    let isDef := ci matches .defnInfo _ | .opaqueInfo _
    -- the entry's own glue (`TwinAccepts`, `SeqAccepts`: predicates naming the stages)
    if (`ConAgua).isPrefixOf (modOf env n) then
      if isDef then return some "entry" else none
    unless isOurTier (modOf env n) do none
    if isTypeOrProp ci then none
    if isDef then some (notTargetWhy env n ci) else none
  -- For each target (and the root), the targets it reaches through non-targets.
  let mut done : NameSet := {}
  let mut work : Array Name := #[root]
  let mut tgts : Array Name := #[]
  let mut edges : Array (Name × Name) := #[]
  let mut skipped : NameMap String := {}
  while h : work.size > 0 do
    let t := work.back
    work := work.pop
    if done.contains t then continue
    done := done.insert t
    if t != root then tgts := tgts.push t
    -- walk through non-targets from `t`
    let mut seen : NameSet := NameSet.empty.insert t
    let mut st : Array Name := match env.find? t with
      | some ci => depsOf env t ci
      | none => #[]
    let mut out : NameSet := {}
    while h2 : st.size > 0 do
      let n := st.back
      st := st.pop
      if seen.contains n then continue
      seen := seen.insert n
      match classify n with
      | none => pure ()
      | some none => out := out.insert n
      | some (some why) =>
        skipped := skipped.insert n why
        if let some ci := env.find? n then
          st := st ++ depsOf env n ci
    for o in out do
      if t != root then edges := edges.push (t, o)
      else IO.println s!"R\t{o}"
      unless done.contains o do work := work.push o
  for t in tgts do
    let (s, e) := match rangeOf env t with
      | some r => (r.range.pos.line, r.range.endPos.line)
      | none => (0, 0)
    let kind := match env.find? t with
      | some (.opaqueInfo _) => "partial"
      | _ => "def"
    IO.println s!"T\t{t}\t{modOf env t}\t{s}\t{e}\t{kind}"
  for (a, b) in edges do IO.println s!"E\t{a}\t{b}"
  if verbose then
    for (n, why) in skipped do
      if isOurTier (modOf env n) then IO.println s!"X\t{n}\t{modOf env n}\t{why}"

/-- Every module of the `ConAgua` closure of `m` (cached). -/
partial def closure (memo : IO.Ref (NameMap NameSet)) (m : Name) : IO NameSet := do
  if let some s := (← memo.get).find? m then return s
  let (md, _) ← readModuleData (← findOLean m)
  let mut s : NameSet := NameSet.empty.insert m
  for i in md.imports do
    if (`ConAgua).isPrefixOf i.module then
      for x in (← closure memo i.module) do s := s.insert x
  memo.modify (·.insert m s)
  return s

def kindStr : LinkKind → String
  | .impl => "impl" | .refines => "refines" | .part => "part"

instance : MonadEnv (StateM Environment) := ⟨get, modify⟩

/-- The owner of an auxiliary declaration (`proof_N`, `match_N`, `eq_N`, `_unary`, ...): the
declaration it was generated for. Other constants are their own owner. -/
partial def owner (env : Environment) (c : Name) : Name :=
  match c with
  | .str p s =>
    if (s.startsWith "proof_" || s.startsWith "match_" || s.startsWith "eq_" || s.startsWith "_" ||
        c.hasMacroScopes) && env.contains p then owner env p
    else c
  | _ => c

/-- Library constants are assumed free of `sorryAx` (not walked). -/
def isLibrary (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | none => false
  | some i =>
    let m := env.header.moduleNames[i.toNat]!
    (`Init).isPrefixOf m || (`Std).isPrefixOf m || (`Lean).isPrefixOf m

/-- The nearest sources of `sorryAx` below `c`, memoized per constant: the owners of the constants
whose own value (not a reference) mentions `sorryAx`, found by walking references and stopping at
the first such constant on each path. Each constant's value is scanned once
(`Expr.getUsedConstants`), each constant is walked once. -/
partial def sorrySources (env : Environment) (memo : IO.Ref (NameMap (Array Name))) (c : Name) :
    IO (Array Name) := do
  if let some r := (← memo.get).find? c then return r
  memo.modify (·.insert c #[])  -- in progress (only inductive types and constructors loop)
  let r ← if isLibrary env c then pure #[] else
    match env.find? c with
    | some (.thmInfo v) => walk v.value
    | some (.defnInfo v) => walk v.value
    | some (.opaqueInfo v) => walk v.value
    | _ => pure #[]
  memo.modify (·.insert c r)
  return r
where
  walk (e : Expr) : IO (Array Name) := do
    let used := e.getUsedConstants
    if used.contains ``sorryAx then return #[owner env c]
    let mut out : Array Name := #[]
    for u in used do
      for s in ← sorrySources env memo u do
        unless out.contains s do out := out.push s
    return out

/-- The axioms `c` depends on (what `collectAxioms` returns), memoized per constant: every
constant's type and value is scanned once (`Expr.getUsedConstants`, itself memoized per subterm
pointer), and the result is a small sorted array that its users merge. `collectAxioms` called once
per linked theorem walked the whole dependency cone of each (hundreds of thousands of constants,
several hundred times over).

The only cycles are inductive types (type <-> constructors, mutual blocks): a block's result is
computed once for the whole block (types of its members and of all their constructors), and a
constructor's result is its block's. -/
partial def axiomsOf (env : Environment) (memo : IO.Ref (NameMap (Array Name))) (c : Name) :
    IO (Array Name) := do
  if let some r := (← memo.get).find? c then return r
  let r ← match env.find? c with
    | none => pure #[]
    | some (.axiomInfo _) => pure #[c]
    | some (.defnInfo v) => merge (v.type.getUsedConstants ++ v.value.getUsedConstants) #[]
    | some (.thmInfo v) => merge (v.type.getUsedConstants ++ v.value.getUsedConstants) #[]
    | some (.opaqueInfo v) => merge (v.type.getUsedConstants ++ v.value.getUsedConstants) #[]
    | some (.quotInfo v) => merge v.type.getUsedConstants #[]
    | some (.recInfo v) => merge v.type.getUsedConstants #[]
    | some (.ctorInfo v) => axiomsOf env memo v.induct
    | some (.inductInfo v) =>
      let mut block : Array Name := #[]
      for n in v.all do
        block := block.push n
        if let some (.inductInfo w) := env.find? n then block := block ++ w.ctors.toArray
      let mut used : Array Name := #[]
      for n in block do
        if let some ci := env.find? n then used := used ++ ci.type.getUsedConstants
      let r ← merge used block
      memo.modify fun m => v.all.foldl (fun m n => m.insert n r) m
      pure r
  memo.modify (·.insert c r)
  return r
where
  merge (used : Array Name) (skip : Array Name) : IO (Array Name) := do
    let mut out : Array Name := #[]
    for u in used do
      if skip.contains u then continue
      for a in ← axiomsOf env memo u do
        unless out.contains a do out := out.push a
    return out

/-- The end-to-end theorem whose remaining assumptions the report lists. -/
def asmTheorem : Name := `ConAgua.Final.checkerAsm_accepts_remaining

/-- Lines `A` for the end-to-end theorem (if `env` has it): its binders (`A hyp name type`, with
`Prop`-typed ones marked), its axioms (`A axiom name`) and the nearest sources of `sorryAx`
(`A src name`). All on top of the memos `links` already fills (one more constant). -/
def asmLines (env : Environment) (axMemo : IO.Ref (NameMap (Array Name))) : IO Unit := do
  let some ci := env.find? asmTheorem | return
  let some mi := env.getModuleIdxFor? asmTheorem | return
  let m := env.header.moduleNames[mi.toNat]!
  let clean (s : String) := (s.replace "\t" " ").replace "\n" " "
  let act : MetaM (Array (String × String × Bool)) :=
    Meta.forallTelescope ci.type fun xs _ => do
      let mut out := #[]
      for x in xs do
        let d ← x.fvarId!.getDecl
        let isP ← Meta.isProp d.type
        let t ← Meta.ppExpr d.type
        out := out.push (toString d.userName, toString t, isP)
      return out
  let (bs, _) ← (act.run' {}).toIO { fileName := "", fileMap := default } { env }
  for (n, t, isP) in bs do
    IO.println s!"A\thyp\t{n}\t{clean t}\t{if isP then "prop" else "data"}\t{m}"
  for a in ← axiomsOf env axMemo asmTheorem do IO.println s!"A\taxiom\t{a}\t\t\t{m}"
  let memo ← IO.mkRef ({} : NameMap (Array Name))
  for s in ← sorrySources env memo asmTheorem do IO.println s!"A\tsrc\t{s}\t\t\t{m}"
  -- the end-to-end cone: the project's constants (ConAgua/ConRon/ConLeche, not the Lean core)
  -- the theorem transitively mentions, and how many of them do not depend on `sorryAx`
  -- (`A cone total clean`); one walk over references, `axiomsOf` is already memoized
  let ours (c : Name) : Bool :=
    let m := modOf env c
    (`ConAgua).isPrefixOf m || isOurTier m
  let mut seen : NameSet := NameSet.empty.insert asmTheorem
  let mut todo : Array Name := #[asmTheorem]
  let mut total := 0
  let mut clean := 0
  while todo.size > 0 do
    let c := todo.back!
    todo := todo.pop
    let some ci := env.find? c | continue
    -- counted: theorems and definitions, not the auxiliary `proof_N`/`match_N`/... constants,
    -- types, constructors or recursors (the walk still goes through all of them)
    if owner env c == c && (ci matches .thmInfo _ | .defnInfo _ | .opaqueInfo _) then
      total := total + 1
      unless (← axiomsOf env axMemo c).contains ``sorryAx do clean := clean + 1
    let used := ci.type.getUsedConstants ++
      (match ci with
       | .defnInfo v => v.value.getUsedConstants
       | .thmInfo v => v.value.getUsedConstants
       | .opaqueInfo v => v.value.getUsedConstants
       | .ctorInfo v => #[v.induct]
       | .inductInfo v => v.ctors.toArray
       | _ => #[])
    for u in used do
      if !seen.contains u && ours u then
        seen := seen.insert u
        todo := todo.push u
  IO.println s!"A\tcone\t{total}\t{clean}\t\t{m}"

/-- The links of every module in `env`, with the axioms of linked theorems. -/
def links (env : Environment) (printed : IO.Ref NameSet) : IO Unit := do
  let memo ← IO.mkRef ({} : NameMap (Array Name))
  let axMemo ← IO.mkRef ({} : NameMap (Array Name))
  for i in [:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if (← printed.get).contains m then continue
    let ents := linkExt.getModuleEntries env i
    if ents.isEmpty then continue
    printed.modify (·.insert m)
    for l in ents do
      let ci? := env.find? l.decl
      let status ← match l.kind with
        | .impl =>
          pure <| if ci?.any (·.type.isConstOf `L.FunDecl) then "n/a" else "error: not an L FunDecl"
        | _ =>
          unless ci? matches some (.thmInfo _) do
            IO.println s!"L\t{kindStr l.kind}\t{l.decl}\t{l.target}\t{l.label}\t{m}\terror: not a theorem"
            continue
          let axs ← axiomsOf env axMemo l.decl
          let bad := axs.filter fun a => !(a == ``propext || a == ``Classical.choice || a == ``Quot.sound)
          -- `sorry`: `sorryAx` in the theorem's own term (or its auxiliaries); `local:`
          -- sources: only through the named constants that carry it directly
          let srcs ← if bad.contains ``sorryAx then sorrySources env memo l.decl else pure #[]
          pure <| if bad.contains ``sorryAx then
              (if srcs.contains l.decl || srcs.isEmpty then "sorry"
               else "local:" ++ ",".intercalate (srcs.toList.map toString))
            else if bad.isEmpty then "ok"
            else "axioms:" ++ ",".intercalate (bad.toList.map toString)
      IO.println s!"L\t{kindStr l.kind}\t{l.decl}\t{l.target}\t{l.label}\t{m}\t{status}"
  asmLines env axMemo

/-- Child `--targets ROOT`: the target pass, in a process of its own. -/
def mainTargets (root : Name) (verbose : Bool) : IO UInt32 := do
  -- `loadExts`: the instance and matcher tables are built by extension initializers; without them
  -- `isInstanceCore` answers `false` for everything.
  unsafe enableInitializersExecution
  let env ← importModules #[{ module := root }] {} (loadExts := true)
  targets env `ConAgua.Final.TwinAccepts verbose
  return 0

/-- Child `--links MODULE...`: import one group and print its links (exit 0); on a clash print
`C bad message` and a line `D m` for every module of the group that imports `bad` (exit 3). Each
child imports once: an environment is never freed, and a failed `importModules` leaks what it
read, so importing group after group in one process grew by about 2 GB per attempt. -/
def mainLinks (grp : Array Name) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let env ← try importModules (grp.map fun m => ({ module := m } : Import)) {}
    catch e =>
      let msg := toString e
      let bad := (((msg.drop 7).takeWhile (· != ' ')).toString).toName
      let memo ← IO.mkRef {}
      let mut defer := #[]
      for m in grp do
        if (← closure memo m).contains bad then defer := defer.push m
      if defer.isEmpty || defer.size == grp.size then throw e
      IO.println s!"C\t{bad}\t{msg.replace "\n" " "}"
      for m in defer do IO.println s!"D\t{m}"
      return 3
  let t1 ← IO.monoMsNow
  links env (← IO.mkRef {})
  let t2 ← IO.monoMsNow
  IO.eprintln s!"census:   links child: import {t1 - t0} ms, links {t2 - t1} ms"
  return 0

/-- Run this executable on `args`; forward its stderr, return its exit code and stdout. -/
def child (args : Array String) : IO (UInt32 × String) := do
  let t0 ← IO.monoMsNow
  let out ← IO.Process.output { cmd := (← IO.appPath).toString, args }
  IO.eprint out.stderr
  let t1 ← IO.monoMsNow
  let what := match args.toList with
    | "--targets" :: _ => "targets"
    | "--links" :: g => s!"links ({g.length} modules)"
    | _ => "?"
  IO.eprintln s!"census: stage {what}: {t1 - t0} ms (exit {out.exitCode})"
  return (out.exitCode, out.stdout)

/-- The driver: the target pass and every link group each run in a child process (see
`mainLinks`), one at a time, so the peak memory is that of one import (about 2.5 GB), not the sum
of all imports. -/
def main (args : List String) : IO UInt32 := do
  let verbose := args.contains "-v"
  let args := args.filter (· != "-v")
  initSearchPath (← findSysroot)
  match args with
  | ["--targets", root] => return ← mainTargets root.toName verbose
  | "--links" :: grp => return ← mainLinks (grp.toArray.map String.toName)
  | _ => pure ()
  let root :: mods := args | do
    IO.eprintln "usage: census [-v] ROOT_MODULE MODULE..."; return 2
  let (rc, out) ← child (#["--targets", root] ++ (if verbose then #["-v"] else #[]))
  IO.print out
  if rc != 0 then return rc
  -- links: modules printed by an earlier group are skipped (a module is in every group that
  -- imports it)
  let mut printed : Std.HashSet String := {}
  let mut pending := mods.toArray
  while pending.size > 0 do
    let mut grp := pending
    let mut rest : Array String := #[]
    let mut done := false
    while !done do
      let (rc, out) ← child (#["--links"] ++ grp)
      let lines := out.splitOn "\n" |>.filter (· != "")
      if rc == 3 then
        let defer := lines.filterMap fun l => match l.splitOn "\t" with
          | ["D", m] => some m
          | _ => none
        for l in lines do
          if l.startsWith "C\t" then
            IO.eprintln s!"census: module clash, next group: {(l.splitOn "\t").drop 2 |> "\t".intercalate}"
        rest := rest ++ defer
        grp := grp.filter (!defer.contains ·)
      else if rc != 0 then return rc
      else
        let mut now : Std.HashSet String := {}
        for l in lines do
          let f := l.splitOn "\t"
          let m := f.getD 5 ""
          unless printed.contains m do
            IO.println l
            now := now.insert m
        printed := printed.union now
        done := true
    pending := rest
  return 0

end ConAgua.Census

def main (args : List String) : IO UInt32 := ConAgua.Census.main args
