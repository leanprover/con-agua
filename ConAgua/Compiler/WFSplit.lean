import Lean
import ConAgua.Compiler.WFFast

/-!
# Program well-formedness, one function at a time

`decide +kernel` on `Prog.wfFast tab p` evaluates every body of `p` in one kernel check; for the
whole checker (1566 functions) that peaked at 12 GB, growing with the program. `prog_wf` splits
it (DESIGN.md, "Program well-formedness, per function"):

```
prog_wf checkerProg_wf : checkerTab checkerProg
```

declares `checkerProg_wf : Prog.wf checkerTab checkerProg = true`, proved by `Prog.wf_of_parts'`
from separate kernel checks:

* `checkerProg_wf.tree`, the name tree as a literal (evaluated by compiled code here), and
  `checkerProg_wf.tree_eq : progTree checkerProg = some checkerProg_wf.tree` (reads the names
  only);
* `checkerProg_wf.rom<k> : romOk checkerTab d = true`, one per distinct byte string `d` the
  program reads (`D.c8[i]`): the comparison with the table's constant data, once per string
  rather than once per function;
* `checkerProg_wf.c<j> : ∀ x ∈ chunk, FunOk tree checkerTab x`, one per chunk of
  `progWfChunk` (32) functions: `FunDecl.wfTN` (the check without the constant data) by
  evaluation, and the byte strings each function reads (`Stmt.roms`) from the `rom<k>`;
* the table bound, by `decide`; the main theorem puts the chunks together (one
  `forall_mem_cons_of` per function, no evaluation).

No kernel check sees every body at once. The table must be cheap to unfold (a literal, as
`indTab`, or `tab_lit% e`, which evaluates `e` with compiled code and inserts the result): every
check unfolds it. The program must reduce to a list literal by `whnf` (a constant, `a ++ b`, …).
For a small program `Prog.wf_of_wfFast (by decide +kernel)` is faster (one check shares the
callees' name codes).
-/

namespace L.Compiler

open Lean Elab Command Meta
open Lean.Elab.Term (TermElab elabTermEnsuringType synthesizeSyntheticMVarsNoPostponing)

def ntreeToExpr : NTree → Lean.Expr
  | .leaf => mkConst ``NTree.leaf
  | .node l k v r => mkApp4 (mkConst ``NTree.node) (ntreeToExpr l) (mkNatLit k) (mkNatLit v) (ntreeToExpr r)

/-- A byte list as `List.flatten [c₀, c₁, …]` of list literals of at most 256 bytes (a long list
literal is a term of linear depth, which the kernel and the compiler reject); above 512 chunks, a
balanced `++` of such. The kernel walks it about three times faster than a balanced `++` tree of
64-byte chunks (each element passes one `flatten`, not ~10 `++`s): `romIdx` of the prelude's
15 700 bytes in the checker's ROM 5 s -> 2 s, of the pin data 14 s -> 5 s. -/
partial def bytesToExpr (bs : Array UInt8) : Lean.Expr :=
  let ty := mkApp (mkConst ``List [0]) (mkConst ``UInt8)
  let k := 256
  let n := (bs.size + k - 1) / k
  if n ≤ 512 then
    let chunks := (List.range n).map fun i => toExpr (bs.extract (i * k) ((i + 1) * k)).toList
    mkApp2 (mkConst ``List.flatten [0]) (mkConst ``UInt8)
      (chunks.foldr (fun c acc => mkApp3 (mkConst ``List.cons [0]) ty c acc) (mkApp (mkConst ``List.nil [0]) ty))
  else
    let h := (n + 1) / 2 * k
    mkApp6 (mkConst ``HAppend.hAppend [0, 0, 0]) ty ty ty
      (mkApp2 (mkConst ``instHAppendOfAppend [0]) ty (mkApp (mkConst ``List.instAppend [0]) (mkConst ``UInt8)))
      (bytesToExpr (bs.extract 0 h)) (bytesToExpr (bs.extract h bs.size))

def tabToExpr (t : Tab) : Lean.Expr :=
  mkApp7 (mkConst ``Tab.mk) (mkNatLit t.nb) (mkNatLit t.nw) (bytesToExpr t.rom.toArray) (mkNatLit t.nres)
    (mkNatLit t.ng) (mkNatLit t.rom.length) (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit t.rom.length))

unsafe def evalNats (e : Lean.Expr) : MetaM (List Nat) :=
  evalExpr (List Nat) (mkApp (mkConst ``List [0]) (mkConst ``Nat)) e

/-- How many byte strings each function of `p` reads. -/
def progRomCounts (p : Prog) : List Nat := p.map fun x => (Stmt.roms x.2.body).length

unsafe def evalTab (e : Lean.Expr) : MetaM Tab := evalExpr Tab (mkConst ``Tab) e
unsafe def evalTree (e : Lean.Expr) : MetaM (Option NTree) :=
  evalExpr (Option NTree) (mkApp (mkConst ``Option [0]) (mkConst ``NTree)) e

/-- `tab_lit% e`: the table `e`, evaluated (by compiled code) and inserted as a literal. -/
syntax (name := tabLit) "tab_lit% " term:max : term

@[term_elab tabLit] unsafe def elabTabLit : TermElab := fun stx _ => do
  let `(tab_lit% $t) := stx | throwUnsupportedSyntax
  -- evaluating a large program's table recurses deeper than the default limit
  withTheReader Core.Context (fun c => { c with maxRecDepth := max c.maxRecDepth 100000 }) do
    let e ← elabTermEnsuringType t (mkConst ``Tab)
    synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    return tabToExpr (← evalTab e)

/-- `bytes_lit% e`: the byte list `e`, evaluated (by compiled code) and inserted as a literal
(`bytesToExpr`), for constant data the kernel would otherwise compute from its definition. -/
syntax (name := bytesLit) "bytes_lit% " term:max : term

@[term_elab bytesLit] unsafe def elabBytesLit : TermElab := fun stx _ => do
  let `(bytes_lit% $t) := stx | throwUnsupportedSyntax
  let ty := mkApp (mkConst ``List [0]) (mkConst ``UInt8)
  let e ← elabTermEnsuringType t ty
  synthesizeSyntheticMVarsNoPostponing
  let bs ← evalExpr (List UInt8) ty (← instantiateMVars e)
  return bytesToExpr bs.toArray

/-- A theorem declaration. -/
def thm (n : Name) (ty v : Lean.Expr) (_ : List Name) : Declaration :=
  .thmDecl { name := n, levelParams := [], type := ty, value := v }

unsafe def evalNTree (e : Lean.Expr) : MetaM NTree := evalExpr NTree (mkConst ``NTree) e

/-- `nrt_lit name : p` declares `name : NTree`, the literal of `Prog.nrt p` (the result counts of
`p`'s functions, evaluated by compiled code), and `name_eq : Prog.nrt p = name`, checked by the
kernel (once; the per-function checks of `asm_lit` then read the literal). -/
syntax (name := nrtLit) "nrt_lit " ident " : " term:max : command

@[command_elab nrtLit] unsafe def elabNrtLit : CommandElab := fun stx => do
  let `(nrt_lit $n:ident : $progS) := stx | throwUnsupportedSyntax
  let name := (← getCurrNamespace) ++ n.getId
  liftTermElabM <| withTheReader Core.Context (fun c => { c with maxRecDepth := max c.maxRecDepth 100000 }) do
    let pE ← elabTermEnsuringType progS (mkConst ``Prog)
    synthesizeSyntheticMVarsNoPostponing
    let pE ← instantiateMVars pE
    let lhs := mkApp (mkConst ``Prog.nrt) pE
    let t ← evalNTree lhs
    let treeTy := mkConst ``NTree
    addAndCompile (.defnDecl (mkDefinitionValEx name [] treeTy (ntreeToExpr t) .abbrev .safe []))
    addDecl (thm (name.appendAfter "_eq") (mkApp3 (mkConst ``Eq [1]) treeTy lhs (mkConst name))
      (mkApp2 (mkConst ``Eq.refl [1]) treeTy lhs) [])

register_option progWfChunk : Nat := {
  defValue := 32
  descr := "prog_wf: functions per kernel check"
}

/-- A proof of `xs[k] ∈ [xs[0], …]` (`List.Mem.tail` `k` times, then `List.Mem.head`). -/
def memProof (α : Lean.Expr) (xs : Array Lean.Expr) (k : Nat) : Lean.Expr := Id.run do
  -- the tails `xs[i:]`, sharing their common parts
  let mut tails : Array Lean.Expr := #[mkApp (mkConst ``List.nil [0]) α]
  for i in (List.range xs.size).reverse do
    tails := tails.push (mkApp3 (mkConst ``List.cons [0]) α xs[i]! tails.back!)
  let tail (i : Nat) := tails[xs.size - i]!
  let mut h := mkApp3 (mkConst ``List.Mem.head [0]) α xs[k]! (tail (k + 1))
  for i in (List.range k).reverse do
    h := mkApp5 (mkConst ``List.Mem.tail [0]) α xs[k]! xs[i]! (tail (i + 1)) h
  return h

/-- The elements of a list expression, by `whnf`. -/
partial def listElems (e : Lean.Expr) (acc : Array Lean.Expr := #[]) : MetaM (Array Lean.Expr) := do
  let e ← whnfD e
  if e.isAppOfArity ``List.cons 3 then listElems e.appArg! (acc.push e.appFn!.appArg!)
  else if e.isAppOfArity ``List.nil 1 then return acc
  else throwError "prog_wf: the program does not reduce to a list literal: {e}"

/-- `prog_wf name : tab p` -/
syntax (name := progWf) (docComment)? "prog_wf " ident " : " term:max term:max : command

@[command_elab progWf] unsafe def elabProgWf : CommandElab := fun stx => do
  let `($[$doc?:docComment]? prog_wf $n:ident : $tabS $progS) := stx | throwUnsupportedSyntax
  let name := (← getCurrNamespace) ++ n.getId
  liftTermElabM <| withTheReader Core.Context (fun c => { c with maxRecDepth := max c.maxRecDepth 100000 }) do
    let tabE ← instantiateMVars (← elabTermEnsuringType tabS (mkConst ``Tab))
    let pE ← instantiateMVars (← elabTermEnsuringType progS (mkConst ``Prog))
    synthesizeSyntheticMVarsNoPostponing
    let tabE ← instantiateMVars tabE
    let pE ← instantiateMVars pE
    let some tree ← evalTree (mkApp (mkConst ``progTree) pE)
      | throwError "prog_wf: two functions have the same name"
    let elems ← listElems pE
    let treeN := name ++ `tree
    let treeTy := mkConst ``NTree
    addAndCompile (.defnDecl (mkDefinitionValEx treeN [] treeTy (ntreeToExpr tree) .abbrev .safe []))
    let treeC := mkConst treeN
    let someTree := mkApp2 (mkConst ``Option.some [0]) treeTy treeC
    let optTy := mkApp (mkConst ``Option [0]) treeTy
    let treeEqN := name ++ `tree_eq
    addDecl ((thm treeEqN
      (mkApp3 (mkConst ``Eq [1]) optTy (mkApp (mkConst ``progTree) pE) someTree)
      (mkApp2 (mkConst ``Eq.refl [1]) optTy someTree) []))
    let bTrue := mkConst ``Bool.true
    let boolTy := mkConst ``Bool
    let elemTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``FunDecl)
    let snd (x : Lean.Expr) := mkApp3 (mkConst ``Prod.snd [0, 0]) (mkConst ``String) (mkConst ``FunDecl) x
    let bytesTy := mkApp (mkConst ``List [0]) (mkConst ``UInt8)
    -- the constant data: one kernel check per distinct byte string the program reads
    let nroms ← evalNats (mkApp (mkConst ``progRomCounts) pE)
    let mut dist : Array Lean.Expr := #[]
    let mut romLists : Array (Array Lean.Expr) := #[]
    for h : i in [0:elems.size] do
      if nroms.getD i 0 == 0 then romLists := romLists.push #[]; continue
      let ds ← listElems (mkApp (mkConst ``Stmt.roms) (mkApp (mkConst ``FunDecl.body) (snd elems[i])))
      for d in ds do
        unless dist.contains d do dist := dist.push d
      romLists := romLists.push ds
    let Pd ← withLocalDeclD `d bytesTy fun d => do
      mkLambdaFVars #[d] (mkApp3 (mkConst ``Eq [1]) boolTy (mkApp2 (mkConst ``romOk) tabE d) bTrue)
    let mut romThms : Array Lean.Expr := #[]
    for h : k in [0:dist.size] do
      let rN := name ++ Name.mkSimple s!"rom{k}"
      addDecl (thm rN (Pd.beta #[dist[k]]) (mkApp2 (mkConst ``Eq.refl [1]) boolTy bTrue) [])
      romThms := romThms.push (mkConst rN)
    -- `∀ d ∈ ds, romOk tab d = true`
    let romChain (ds : Array Lean.Expr) : Lean.Expr := Id.run do
      let mut c := mkApp2 (mkConst ``forall_mem_nil_of) bytesTy Pd
      let mut tl := mkApp (mkConst ``List.nil [0]) bytesTy
      for d in ds.reverse do
        let hd := romThms[(dist.idxOf? d).getD 0]!
        c := mkAppN (mkConst ``forall_mem_cons_of) #[bytesTy, Pd, d, tl, hd, c]
        tl := mkApp3 (mkConst ``List.cons [0]) bytesTy d tl
      return c
    -- one kernel check per chunk of functions
    let P := mkApp2 (mkConst ``FunOk) treeC tabE
    let Pr ← withLocalDeclD `x elemTy fun x => do
      let body ← withLocalDeclD `d bytesTy fun d => do
        let mem ← mkAppM ``Membership.mem
          #[mkApp (mkConst ``Stmt.roms) (mkApp (mkConst ``FunDecl.body) (snd x)), d]
        mkForallFVars #[d] (← mkArrow mem (Pd.beta #[d]))
      mkLambdaFVars #[x] body
    let f ← withLocalDeclD `x elemTy fun x => do
      mkLambdaFVars #[x] (mkApp3 (mkConst ``FunDecl.wfTN) treeC tabE (snd x))
    let k := progWfChunk.get (← getOptions)
    let mut parts : Array (Lean.Expr × Lean.Expr) := #[]
    let mut i := 0
    while i < elems.size do
      let chunk := elems.extract i (i + k)
      let lit ← mkListLit elemTy chunk.toList
      let ty ← withLocalDeclD `x elemTy fun x => do
        mkForallFVars #[x] (← mkArrow (← mkAppM ``Membership.mem #[lit, x]) (mkApp P x))
      let hN := name ++ Name.mkSimple s!"c{parts.size}"
      let hwf := mkAppN (mkConst ``forall_of_all) #[elemTy, f, lit,
        mkApp2 (mkConst ``Eq.refl [1]) boolTy bTrue]
      let mut hr := mkApp2 (mkConst ``forall_mem_nil_of) elemTy Pr
      let mut tl := mkApp (mkConst ``List.nil [0]) elemTy
      for j in (List.range chunk.size).reverse do
        hr := mkAppN (mkConst ``forall_mem_cons_of) #[elemTy, Pr, chunk[j]!, tl, romChain romLists[i + j]!, hr]
        tl := mkApp3 (mkConst ``List.cons [0]) elemTy chunk[j]! tl
      let pf := mkAppN (mkConst ``forall_funOk) #[treeC, tabE, lit, hwf, hr]
      addDecl ((thm hN ty pf []))
      parts := parts.push (lit, mkConst hN)
      i := i + k
    -- `∀ x ∈ p, P x`: one `forall_mem_cons_of` per function, from its chunk's theorem (no `++`
    -- for the kernel to unfold)
    let mut chain := mkApp2 (mkConst ``forall_mem_nil_of) elemTy P
    let mut tl := mkApp (mkConst ``List.nil [0]) elemTy
    for e in (List.range elems.size).reverse do
      let (_, hc) := parts[e / k]!
      let chunk := elems.extract (e / k * k) (e / k * k + k)
      let he := mkApp2 hc elems[e]! (memProof elemTy chunk (e % k))
      chain := mkAppN (mkConst ``forall_mem_cons_of) #[elemTy, P, elems[e]!, tl, he, chain]
      tl := mkApp3 (mkConst ``List.cons [0]) elemTy elems[e]! tl
    let boundTy ← mkAppM ``LT.lt #[
      ← mkAppM ``HAdd.hAdd #[← mkAppM ``HAdd.hAdd #[← mkAppM ``HAdd.hAdd #[← mkAppM ``HAdd.hAdd #[
        mkNatLit 16, ← mkAppM ``HMul.hMul #[mkNatLit 16, ← mkAppM ``HAdd.hAdd #[
          mkApp (mkConst ``Tab.nb) tabE, mkApp (mkConst ``Tab.nw) tabE]]],
        ← mkAppM ``HMul.hMul #[mkNatLit 8, mkApp (mkConst ``Tab.romWords) tabE]],
        ← mkAppM ``HMul.hMul #[mkNatLit 8, mkApp (mkConst ``Tab.nxres) tabE]],
        ← mkAppM ``HMul.hMul #[mkNatLit 8, mkApp (mkConst ``Tab.ng) tabE]],
      mkConst ``maxOff]
    -- `of_decide_eq_true rfl`, checked by the kernel (`mkDecideProof` would evaluate the table's
    -- constant data with `Meta.whnf`)
    let lhs := boundTy.appFn!.appArg!
    let inst := mkApp2 (mkConst ``Nat.decLt) lhs (mkConst ``maxOff)
    let hb := mkApp3 (mkConst ``of_decide_eq_true) boundTy inst (mkApp2 (mkConst ``Eq.refl [1]) boolTy bTrue)
    -- no `Meta` unification here: the kernel checks that the chunks make up `p`
    let pf := mkAppN (mkConst ``Prog.wf_of_parts') #[tabE, pE, treeC, mkConst treeEqN, chain, hb]
    let ty := mkApp3 (mkConst ``Eq [1]) boolTy (mkApp2 (mkConst ``Prog.wf) tabE pE) bTrue
    let pf ← instantiateMVars pf
    addDecl ((thm name ty pf []))
    addDocString' name .missing doc?

end L.Compiler
