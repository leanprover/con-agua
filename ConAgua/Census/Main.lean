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
    L   kind  decl  target  label  module  status   a link (status: ok | sorry | axioms:a,b | n/a)
    F   name  fingerprint                           a target's fingerprint (16 hex digits)

The FINGERPRINT of a target (`docs/twin-fingerprints.tsv`, DESIGN.md "Twin fingerprints") is a
hash of the elaborated declarations that make up its code: its own type and value, and the type
and value of every non-target it walks through (instances, matchers, auxiliaries such as a
`partial def`'s `_unsafe_rec` body, projections), each with its name; not the targets it calls
(they have their own). So it is insensitive to comments, doc comments, line moves and binder
names, and sensitive to everything the compiled twin does, including a structure gaining a field
(the anonymous constructors and projections in the value change). It is the toolchain's
`Expr.hash`, so it is stable for one toolchain only: re-record after a toolchain bump, never in
the same step as a twin bump.

What is reached: the VALUE of a definition (not its type), through definitions only (theorems,
types and proofs are not walked into), plus `@[implemented_by]` of an opaque (`partial def`).
What is not a target, but walked through: instances, compiler/elaborator auxiliaries (`match_`,
`proof_`, `_unary`, `_mutual`, `eq_`, recursors, `noConConfusion`, projections, names with
macro scopes). What is neither: type formers (the value is a type), `Prop`-valued definitions
(predicates: spec only), and everything outside `ConRon.*`/`ConLeche.*` (Lean's library).

Module groups: some ConAgua modules declare the same names (`L.Arena.appK₁.appK₂` in `Walk` and in
`Lift`; `main` in the emitters), so one environment cannot import them all. The link pass imports
the modules greedily in groups: on a clash it moves the failing module and everything that imports
it into the next group.
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

/-- The hash of one declaration: name, type and value (for a definition or an opaque). -/
def declHash (n : Name) (ci : ConstantInfo) : UInt64 :=
  let v : UInt64 := match ci with
    | .defnInfo d => hash d.value
    | .opaqueInfo d => hash d.value
    | _ => 0
  mixHash (hash n) (mixHash (hash ci.type) v)

def hex16 (x : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 x.toNat)
  "".pushn '0' (16 - s.length) ++ s

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
    -- the declarations the fingerprint hashes: `t` and the non-targets walked through from it
    let mut parts : Array (Name × UInt64) := match env.find? t with
      | some ci => #[(t, declHash t ci)]
      | none => #[]
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
          parts := parts.push (n, declHash n ci)
    if t != root then
      let fp := (parts.qsort (fun a b => a.1.toString < b.1.toString)).foldl
        (fun h (_, x) => mixHash h x) 7
      IO.println s!"F\t{t}\t{hex16 fp}"
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

/-- The links of every module in `env`, with the axioms of linked theorems. -/
def links (env : Environment) (printed : IO.Ref NameSet) : IO Unit := do
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
          let axs := ((collectAxioms l.decl : StateM Environment (Array Name)).run' env)
          let bad := axs.filter fun a => !(a == ``propext || a == ``Classical.choice || a == ``Quot.sound)
          pure <| if bad.contains ``sorryAx then "sorry"
            else if bad.isEmpty then "ok"
            else "axioms:" ++ ",".intercalate (bad.toList.map toString)
      IO.println s!"L\t{kindStr l.kind}\t{l.decl}\t{l.target}\t{l.label}\t{m}\t{status}"

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
  links env (← IO.mkRef {})
  return 0

/-- Run this executable on `args`; forward its stderr, return its exit code and stdout. -/
def child (args : Array String) : IO (UInt32 × String) := do
  let out ← IO.Process.output { cmd := (← IO.appPath).toString, args }
  IO.eprint out.stderr
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
