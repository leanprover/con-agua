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

/-- A list of number pairs as a term. -/
def natPairsToExpr (l : List (Nat × Nat)) : Lean.Expr :=
  let ty := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkConst ``Nat)
  l.foldr (fun (a, b) acc => mkApp3 (mkConst ``List.cons [0]) ty
    (mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Nat) (mkConst ``Nat) (mkNatLit a) (mkNatLit b)) acc)
    (mkApp (mkConst ``List.nil [0]) ty)

/-- `Tab.tbl` as a term. -/
def tblToExpr : Option (Nat × Nat) → Lean.Expr
  | none => mkApp (mkConst ``Option.none [0]) (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkConst ``Nat))
  | some (a, c) => mkApp2 (mkConst ``Option.some [0]) (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkConst ``Nat))
      (mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Nat) (mkConst ``Nat) (mkNatLit a) (mkNatLit c))

/-- A list of arrays (`Tab.arrAt`) as a term. -/
def arrsToExpr (l : List TieredArray) : Lean.Expr :=
  let ty := mkConst ``TieredArray
  l.foldr (fun s acc => mkApp3 (mkConst ``List.cons [0]) ty
    (mkApp2 (mkConst ``TieredArray.mk) (mkNatLit s.arr) (toExpr s.hi)) acc)
    (mkApp (mkConst ``List.nil [0]) ty)

def tabToExpr (t : Tab) : Lean.Expr :=
  mkAppN (mkConst ``Tab.mk) #[mkNatLit t.nb, mkNatLit t.nw, arrsToExpr t.arrAt, ntreeToExpr t.lmap,
    mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true), bytesToExpr t.rom.toArray, mkNatLit t.nres,
    mkNatLit t.ng, natPairsToExpr t.mins, tblToExpr t.tbl, mkNatLit t.rom.length,
    mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit t.rom.length)]

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

/-- The elements of a list expression, by `whnf`. -/
partial def listElems (e : Lean.Expr) (acc : Array Lean.Expr := #[]) : MetaM (Array Lean.Expr) := do
  let e ← whnfD e
  if e.isAppOfArity ``List.cons 3 then listElems e.appArg! (acc.push e.appFn!.appArg!)
  else if e.isAppOfArity ``List.nil 1 then return acc
  else throwError "prog_wf: the program does not reduce to a list literal: {e}"

/-- `x`'s entry in `Prog.skt`'s tree, if it skips its stack check (`skipsCheck`). -/
def skEntry (entry : FnName) (x : FnName × FunDecl) : Option (Nat × Nat) :=
  if skipsCheck entry x.1 x.2 then some (nameCode x.1, fnFrame x.2) else none

/-- The tree of a list of entries, the last inserted first (`Prog.skTree`'s order). -/
def insAll : List (Nat × Nat) → Option NTree
  | [] => some .leaf
  | (k, v) :: l => (insAll l).bind (·.insert k v)

theorem skTree_eq_insAll (entry : FnName) :
    ∀ p : Prog, Prog.skTree entry p = insAll (p.filterMap (skEntry entry))
  | [] => rfl
  | (f, fd) :: p => by
    rw [Prog.skTree, skTree_eq_insAll entry p, List.filterMap_cons, skEntry]
    by_cases h : skipsCheck entry f fd <;> simp [h, insAll]

/-- `Prog.skt` from its parts: the program is the parts `cs`, whose entries are `ls`. -/
theorem skt_of_parts {p : Prog} {entry : FnName} {t : NTree} (cs : List Prog)
    (ls : List (List (Nat × Nat))) (hp : p = cs.flatten)
    (hl : cs.map (List.filterMap (skEntry entry)) = ls) (ht : (insAll ls.flatten).getD .leaf = t) :
    Prog.skt p entry = t := by
  subst hp
  rw [Prog.skt, skTree_eq_insAll, List.filterMap_flatten, hl, ht]

theorem map_cons_of {α β : Type} {f : α → β} {a : α} {b : β} {l : List α} {r : List β}
    (h : f a = b) (hr : l.map f = r) : (a :: l).map f = b :: r := by
  simp [h, hr]

unsafe def evalPairs (e : Lean.Expr) : MetaM (List (Nat × Nat)) :=
  evalExpr (List (Nat × Nat)) (mkApp (mkConst ``List [0])
    (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkConst ``Nat))) e

/-- `skt_part name : p entry lo hi` declares `name.part<lo> : (chunk).filterMap (skEntry entry) =
lit`, for the functions `lo ≤ i < hi` of `p` as a list literal (`chunk`) and `lit` evaluated by
compiled code: a part of `skt_lit name`'s kernel check, in a module of its own (Lake builds the
parts in parallel). -/
syntax (name := sktPart) "skt_part " ident " : " term:max term:max num num : command

@[command_elab sktPart] unsafe def elabSktPart : CommandElab := fun stx => do
  let `(skt_part $n:ident : $progS $entryS $lo $hi) := stx | throwUnsupportedSyntax
  let name := (← getCurrNamespace) ++ n.getId
  liftTermElabM <| withTheReader Core.Context (fun c => { c with maxRecDepth := max c.maxRecDepth 100000 }) do
    let pE ← elabTermEnsuringType progS (mkConst ``Prog)
    let entryE ← elabTermEnsuringType entryS (mkConst ``String)
    synthesizeSyntheticMVarsNoPostponing
    let pE ← instantiateMVars pE
    let entryE ← instantiateMVars entryE
    let elems ← listElems pE
    let elemTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``FunDecl)
    let pairTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkConst ``Nat)
    let chunk ← mkListLit elemTy (elems.extract lo.getNat hi.getNat).toList
    let lhs := mkApp4 (mkConst ``List.filterMap [0, 0]) elemTy pairTy (mkApp (mkConst ``skEntry) entryE) chunk
    let ps ← evalPairs lhs
    let lpTy := mkApp (mkConst ``List [0]) pairTy
    addDecl (thm (name ++ Name.mkSimple s!"part{lo.getNat}") (mkApp3 (mkConst ``Eq [1]) lpTy lhs (natPairsToExpr ps))
      (mkApp2 (mkConst ``Eq.refl [1]) lpTy lhs) [])

/-- The length of a list literal. -/
partial def litLength (e : Lean.Expr) : Nat :=
  if e.isAppOfArity ``List.cons 3 then 1 + litLength e.appArg! else 0

/-- `skt_lit name : p entry` declares `name : NTree`, the literal of `Prog.skt p entry` (the frames of
`p`'s leaves without a stack check, evaluated by compiled code), and `name_eq : Prog.skt p entry =
name`, checked by the kernel (once; the per-function checks of `asm_lit` then read the literal).
If parts `name.part0`, `name.part<i>`, … (`skt_part`, consecutive, covering `p`) are declared,
`name_eq` is put together from them (`skt_of_parts`): the kernel then inserts their entries into
the tree, without evaluating a function's frame. -/
syntax (name := sktLit) "skt_lit " ident " : " term:max term:max : command

@[command_elab sktLit] unsafe def elabSktLit : CommandElab := fun stx => do
  let `(skt_lit $n:ident : $progS $entryS) := stx | throwUnsupportedSyntax
  let name := (← getCurrNamespace) ++ n.getId
  liftTermElabM <| withTheReader Core.Context (fun c => { c with maxRecDepth := max c.maxRecDepth 100000 }) do
    let pE ← elabTermEnsuringType progS (mkConst ``Prog)
    let entryE ← elabTermEnsuringType entryS (mkConst ``String)
    synthesizeSyntheticMVarsNoPostponing
    let pE ← instantiateMVars pE
    let entryE ← instantiateMVars entryE
    let lhs := mkApp2 (mkConst ``Prog.skt) pE entryE
    let t ← evalNTree lhs
    let treeTy := mkConst ``NTree
    addAndCompile (.defnDecl (mkDefinitionValEx name [] treeTy (ntreeToExpr t) .abbrev .safe []))
    let eqTy := mkApp3 (mkConst ``Eq [1]) treeTy lhs (mkConst name)
    let partN (i : Nat) := name ++ Name.mkSimple s!"part{i}"
    if !(← getEnv).contains (partN 0) then
      addDecl (thm (name.appendAfter "_eq") eqTy (mkApp2 (mkConst ``Eq.refl [1]) treeTy lhs) [])
      return
    -- the parts, in order
    let mut cs : Array Lean.Expr := #[]
    let mut ls : Array Lean.Expr := #[]
    let mut hs : Array Lean.Expr := #[]
    let mut i := 0
    while true do
      let some ci := (← getEnv).find? (partN i) | break
      let some (_, l, r) := ci.type.eq? | throwError "skt_lit: {partN i} is not an equation"
      let c := l.appArg!
      cs := cs.push c; ls := ls.push r; hs := hs.push (mkConst (partN i))
      let len := litLength c
      if len == 0 then break
      i := i + len
    let n := (← listElems pE).size
    unless i == n do throwError "skt_lit: the parts cover {i} of the {n} functions"
    let elemTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``FunDecl)
    let progTy := mkApp (mkConst ``List [0]) elemTy
    let pairTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkConst ``Nat)
    let lpTy := mkApp (mkConst ``List [0]) pairTy
    let csE ← mkListLit progTy cs.toList
    let lsE ← mkListLit lpTy ls.toList
    -- `p = cs.flatten`, by the kernel (the same element terms)
    let hp := mkApp2 (mkConst ``Eq.refl [1]) progTy pE
    -- `cs.map (filterMap (skEntry entry)) = ls`, one part at a time
    let f := mkApp3 (mkConst ``List.filterMap [0, 0]) elemTy pairTy (mkApp (mkConst ``skEntry) entryE)
    let mut hl := mkApp2 (mkConst ``Eq.refl [1]) (mkApp (mkConst ``List [0]) lpTy) (mkApp (mkConst ``List.nil [0]) lpTy)
    let mut ctl := mkApp (mkConst ``List.nil [0]) progTy
    let mut ltl := mkApp (mkConst ``List.nil [0]) lpTy
    for j in (List.range cs.size).reverse do
      hl := mkAppN (mkConst ``map_cons_of) #[progTy, lpTy, f, cs[j]!, ls[j]!, ctl, ltl, hs[j]!, hl]
      ctl := mkApp3 (mkConst ``List.cons [0]) progTy cs[j]! ctl
      ltl := mkApp3 (mkConst ``List.cons [0]) lpTy ls[j]! ltl
    -- the tree of the entries, by the kernel (insertions of number pairs)
    let ht := mkApp2 (mkConst ``Eq.refl [1]) treeTy (mkConst name)
    let pf := mkAppN (mkConst ``skt_of_parts) #[pE, entryE, mkConst name, csE, lsE, hp, hl, ht]
    addDecl (thm (name.appendAfter "_eq") eqTy pf [])

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

/-- `name.tree` and `name.tree_eq : progTree p = some name.tree` (the name tree as a literal,
evaluated by compiled code; the kernel check reads the names only). -/
unsafe def declProgTree (name : Name) (pE : Lean.Expr) : MetaM Unit := do
  let some tree ← evalTree (mkApp (mkConst ``progTree) pE)
    | throwError "prog_wf: two functions have the same name"
  let treeN := name ++ `tree
  let treeTy := mkConst ``NTree
  addAndCompile (.defnDecl (mkDefinitionValEx treeN [] treeTy (ntreeToExpr tree) .abbrev .safe []))
  let someTree := mkApp2 (mkConst ``Option.some [0]) treeTy (mkConst treeN)
  let optTy := mkApp (mkConst ``Option [0]) treeTy
  addDecl ((thm (name ++ `tree_eq)
    (mkApp3 (mkConst ``Eq [1]) optTy (mkApp (mkConst ``progTree) pE) someTree)
    (mkApp2 (mkConst ``Eq.refl [1]) optTy someTree) []))

/-- `name.c<j> : ∀ x ∈ chunk j, FunOk name.tree tab x` for the chunks `js` of `elems` (chunks of
`k` functions), each one kernel check, after the `romOk` theorems of the byte strings they read
(`name.rom<r>`, or `name.p<lo>.rom<r>` with `pre`), one per distinct string. -/
unsafe def declWfChunks (name pre : Name) (tabE pE : Lean.Expr) (elems : Array Lean.Expr) (k : Nat)
    (js : List Nat) : MetaM Unit := do
  let treeC := mkConst (name ++ `tree)
  let bTrue := mkConst ``Bool.true
  let boolTy := mkConst ``Bool
  let elemTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``FunDecl)
  let snd (x : Lean.Expr) := mkApp3 (mkConst ``Prod.snd [0, 0]) (mkConst ``String) (mkConst ``FunDecl) x
  let bytesTy := mkApp (mkConst ``List [0]) (mkConst ``UInt8)
  let inJs (i : Nat) := js.contains (i / k)
  -- the constant data: one kernel check per distinct byte string the chunks read
  let nroms ← evalNats (mkApp (mkConst ``progRomCounts) pE)
  let mut dist : Array Lean.Expr := #[]
  let mut romLists : Array (Array Lean.Expr) := #[]
  for h : i in [0:elems.size] do
    if nroms.getD i 0 == 0 || !inJs i then romLists := romLists.push #[]; continue
    let ds ← listElems (mkApp (mkConst ``Stmt.roms) (mkApp (mkConst ``FunDecl.body) (snd elems[i])))
    for d in ds do
      unless dist.contains d do dist := dist.push d
    romLists := romLists.push ds
  let Pd ← withLocalDeclD `d bytesTy fun d => do
    mkLambdaFVars #[d] (mkApp3 (mkConst ``Eq [1]) boolTy (mkApp2 (mkConst ``romOk) tabE d) bTrue)
  let mut romThms : Array Lean.Expr := #[]
  for h : r in [0:dist.size] do
    let rN := pre ++ Name.mkSimple s!"rom{r}"
    addDecl (thm rN (Pd.beta #[dist[r]]) (mkApp2 (mkConst ``Eq.refl [1]) boolTy bTrue) [])
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
  let P := mkApp2 (mkConst ``FunOk) treeC tabE
  let Pr ← withLocalDeclD `x elemTy fun x => do
    let body ← withLocalDeclD `d bytesTy fun d => do
      let mem ← mkAppM ``Membership.mem
        #[mkApp (mkConst ``Stmt.roms) (mkApp (mkConst ``FunDecl.body) (snd x)), d]
      mkForallFVars #[d] (← mkArrow mem (Pd.beta #[d]))
    mkLambdaFVars #[x] body
  let f ← withLocalDeclD `x elemTy fun x => do
    mkLambdaFVars #[x] (mkApp3 (mkConst ``FunDecl.wfTN) treeC tabE (snd x))
  for j in js do
    let i := j * k
    let chunk := elems.extract i (i + k)
    let lit ← mkListLit elemTy chunk.toList
    let ty ← withLocalDeclD `x elemTy fun x => do
      mkForallFVars #[x] (← mkArrow (← mkAppM ``Membership.mem #[lit, x]) (mkApp P x))
    let hwf := mkAppN (mkConst ``forall_of_all) #[elemTy, f, lit,
      mkApp2 (mkConst ``Eq.refl [1]) boolTy bTrue]
    let mut hr := mkApp2 (mkConst ``forall_mem_nil_of) elemTy Pr
    let mut tl := mkApp (mkConst ``List.nil [0]) elemTy
    for jj in (List.range chunk.size).reverse do
      hr := mkAppN (mkConst ``forall_mem_cons_of) #[elemTy, Pr, chunk[jj]!, tl, romChain romLists[i + jj]!, hr]
      tl := mkApp3 (mkConst ``List.cons [0]) elemTy chunk[jj]! tl
    let pf := mkAppN (mkConst ``forall_funOk) #[treeC, tabE, lit, hwf, hr]
    addDecl ((thm (name ++ Name.mkSimple s!"c{j}") ty pf []))

/-- `prog_tree name : p`: `name.tree` and `name.tree_eq` of `prog_wf name` (`declProgTree`), in
a module of their own: they read the names only, not the table. -/
syntax (name := progTreeCmd) "prog_tree " ident " : " term:max : command

@[command_elab progTreeCmd] unsafe def elabProgTree : CommandElab := fun stx => do
  let `(prog_tree $n:ident : $progS) := stx | throwUnsupportedSyntax
  let name := (← getCurrNamespace) ++ n.getId
  liftTermElabM <| withTheReader Core.Context (fun c => { c with maxRecDepth := max c.maxRecDepth 100000 }) do
    let pE ← instantiateMVars (← elabTermEnsuringType progS (mkConst ``Prog))
    synthesizeSyntheticMVarsNoPostponing
    declProgTree name (← instantiateMVars pE)

/-- `prog_wf_part name : tab p lo hi`: the chunk theorems `name.c<j>` of `prog_wf name` for the
chunks `lo ≤ j < hi`, in a module of their own (Lake builds the parts in parallel; the kernel
checks of one module run one after the other). Needs `name.tree` (`prog_tree`). -/
syntax (name := progWfPart) "prog_wf_part " ident " : " term:max term:max num num : command

@[command_elab progWfPart] unsafe def elabProgWfPart : CommandElab := fun stx => do
  let `(prog_wf_part $n:ident : $tabS $progS $lo $hi) := stx | throwUnsupportedSyntax
  let name := (← getCurrNamespace) ++ n.getId
  liftTermElabM <| withTheReader Core.Context (fun c => { c with maxRecDepth := max c.maxRecDepth 100000 }) do
    let tabE ← instantiateMVars (← elabTermEnsuringType tabS (mkConst ``Tab))
    let pE ← instantiateMVars (← elabTermEnsuringType progS (mkConst ``Prog))
    synthesizeSyntheticMVarsNoPostponing
    let tabE ← instantiateMVars tabE
    let pE ← instantiateMVars pE
    unless (← getEnv).contains (name ++ `tree) do
      throwError "prog_wf_part: {name ++ `tree} is not declared (`prog_tree`)"
    let elems ← listElems pE
    let k := progWfChunk.get (← getOptions)
    let nch := (elems.size + k - 1) / k
    let js := (List.range nch).filter fun j => lo.getNat ≤ j && j < hi.getNat
    declWfChunks name (name ++ Name.mkSimple s!"p{lo.getNat}") tabE pE elems k js

/-- `prog_wf name : tab p`. `name.tree` and the chunk theorems `name.c<j>` already declared (by
`prog_tree`, `prog_wf_part` in imported modules) are used, the others declared here. -/
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
    let treeN := name ++ `tree
    unless (← getEnv).contains treeN do declProgTree name pE
    let elems ← listElems pE
    let treeC := mkConst treeN
    let treeEqN := name ++ `tree_eq
    let boolTy := mkConst ``Bool
    let elemTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``FunDecl)
    let k := progWfChunk.get (← getOptions)
    let nch := (elems.size + k - 1) / k
    let chN (j : Nat) := name ++ Name.mkSimple s!"c{j}"
    let env ← getEnv
    let todo := (List.range nch).filter fun j => !env.contains (chN j)
    unless todo.isEmpty do declWfChunks name name tabE pE elems k todo
    -- `∀ x ∈ p, P x`: one `forall_mem_cons_of` per function, from its chunk's theorem (no `++`
    -- for the kernel to unfold)
    let P := mkApp2 (mkConst ``FunOk) treeC tabE
    let mut chain := mkApp2 (mkConst ``forall_mem_nil_of) elemTy P
    let mut tl := mkApp (mkConst ``List.nil [0]) elemTy
    for e in (List.range elems.size).reverse do
      let chunk := elems.extract (e / k * k) (e / k * k + k)
      let he := mkApp2 (mkConst (chN (e / k))) elems[e]! (memProof elemTy chunk (e % k))
      chain := mkAppN (mkConst ``forall_mem_cons_of) #[elemTy, P, elems[e]!, tl, he, chain]
      tl := mkApp3 (mkConst ``List.cons [0]) elemTy elems[e]! tl
    let boundTy ← mkAppM ``LT.lt #[
      ← mkAppM ``HAdd.hAdd #[← mkAppM ``HAdd.hAdd #[← mkAppM ``HAdd.hAdd #[← mkAppM ``HAdd.hAdd #[
        mkNatLit 16, ← mkAppM ``HMul.hMul #[mkNatLit 24, ← mkAppM ``HAdd.hAdd #[
          mkApp (mkConst ``Tab.nb) tabE, mkApp (mkConst ``Tab.nw) tabE]]],
        ← mkAppM ``HMul.hMul #[mkNatLit 8, mkApp (mkConst ``Tab.romWords) tabE]],
        ← mkAppM ``HMul.hMul #[mkNatLit 8, mkApp (mkConst ``Tab.nxres) tabE]],
        ← mkAppM ``HMul.hMul #[mkNatLit 8, mkApp (mkConst ``Tab.ng) tabE]],
      mkConst ``maxOff]
    -- `of_decide_eq_true rfl`, checked by the kernel (`mkDecideProof` would evaluate the table's
    -- constant data with `Meta.whnf`)
    let lhs := boundTy.appFn!.appArg!
    let inst := mkApp2 (mkConst ``Nat.decLt) lhs (mkConst ``maxOff)
    let hb := mkApp3 (mkConst ``of_decide_eq_true) boundTy inst (mkApp2 (mkConst ``Eq.refl [1]) boolTy (mkConst ``Bool.true))
    -- no `Meta` unification here: the kernel checks that the chunks make up `p`
    let pf := mkAppN (mkConst ``Prog.wf_of_parts') #[tabE, pE, treeC, mkConst treeEqN, chain, hb]
    let ty := mkApp3 (mkConst ``Eq [1]) boolTy (mkApp2 (mkConst ``Prog.wf) tabE pE) (mkConst ``Bool.true)
    let pf ← instantiateMVars pf
    addDecl ((thm name ty pf []))
    addDocString' name .missing doc?

end L.Compiler
