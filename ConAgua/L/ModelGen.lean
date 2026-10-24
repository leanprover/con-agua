module

public import ConAgua.L.Notation
public import ConAgua.L.Logic
public meta import Lean

public section

/-!
# Generated word models and specs (`l_model`)

`l_model` reads the `lfn` text of a group of L functions and generates, for each function `f`,

* its **word model** `fW : Nat → Mem → Word → … → Option (Word × Mem)` (`Option Word` for a
  read-only function, `ro`; no fuel argument for a single function that needs none): the L code
  with every local inlined, `abort` as `none`, a load as `rdW`, a store as `Mem.set64`, a call to a
  group member as that member's model at fuel `n`, a call to another function as the model its
  spec states (`specs`), and the code after an effectful call as a first-order continuation
  `fW.kᵢ` (`| none => none | some (x, m₁) => …`) over the locals it reads. The code after an `if`
  whose branches both fall through is a join point `fW.kᵢ` over the locals and the memory (no
  copy of it). Equal continuations of the group are shared. A group whose continuations call its
  models is defined by well-founded recursion on `(n, depth)`, as `LevelLeq.lean` does by hand;
* one **guarded equation** `fW.armᵢ` per non-`none` leaf of the `if` tree of each model and
  continuation (the path's conditions as hypotheses, in order), each with a `grind_pattern` in the
  `grind` attributes;
* the **spec** `⦃s = s₀⦄ invoke p (exec p n) "f" args ⦃LocEq s' s₀ ∧
  fW n s₀.mem args = some (r.headD 0, s'.mem); ⊤⦄` of every member, as one conjunction over the
  group (`name`), a step theorem per member (`name.stepᵢ`: `vcgen` with the specs of the callees
  that member calls, then `finish`) and the induction on the fuel.

```
l_model liftGo_spec (p : Prog) (hp : LiftProg p)
  fns [(hp.get "lift_go") ↦ liftW, (hp.get "lift_app") ↦ liftAppW]
  specs [derB_spec p (hp.get "der_b") n, memoFindG_spec lfSch p _ (hp.get "lf_find") n]
  grind [arena_grind] fold [tierW, idxW] finish [tierW, idxW] gen 20 heartbeats 1000000
```

* `fns`: each entry is a proof of `p.lookup "f" = some F` (`F` a `def F : FunDecl := lfn …` of
  this file: its text is read back for the names of the locals and the leaf terms) and the name
  of the model. `ro` after the name: a read-only model (`Option Word`, memory unchanged).
* `specs`: the callees' specs, as terms over the binders and the fuel `n`. A callee's model is read
  off its post: `F = some (r.headD 0, s'.mem)` (effectful), `r.headD 0 = F₀ ∧ r.tail.headD 0 = F₁ …`
  with the memory unchanged (pure), `r ≠ [] ∧ r = F` (a list of results; `F = []` becomes `none`
  unless the callee is listed in `noguard`), `F = some s'.mem` (memory only),
  `G ∧ s'.mem = F` (memory only, total; `¬ G` becomes `none`), `F = some (r.headD 0)` with the
  memory unchanged (read-only), `F = some (r, s'.mem)` (several results and the memory: the
  code after the call is a continuation over `some (r, m₁)`, its results `r.headD 0`,
  `r.tail.headD 0`, …).
* `fold`: named functions whose bodies are folded back into the model: word arithmetic
  (`tierW h = (h >>> 27) &&& 1`) or a result of a list callee (`lvG m p = (lvNodeW m p).headD 0`).
* `extra`: more lemmas for `vcgen` (the default is `exec, step, evalE, evalC, evalArgs, setLoc,
  setLocs, ld64`); `finish`, `gen`: the hints and depth of `finish`; `heartbeats`: per step theorem;
  `trace`: log the generated commands.

Not supported (an error names the statement or the callee): `while`/`break` and splices of named
blocks, `return (a, b)` (a model with several results), byte stores,
`FunDecl`s with parameters (`memoFindG S`) and models with Lean parameters, members that only
change the memory. Array bounds are not modelled: a load is `rdW` (`0` out of bounds), a store is
`Mem.set64` (no change out of bounds); where L aborts, the spec says nothing.
-/

namespace L.ModelGen

open Lean Elab Command Term Meta

/-! ## The model's terms -/

/-- A word-valued term of the model. -/
meta inductive MT where
  | lit (n : Nat)
  | op (o : String) (a b : MT)
  /-- `rdW (mem.arr64 arr) i` -/
  | rd (mem : MT) (arr : Term) (i : MT)
  /-- `(mem.arr8 arr)[i]` as a word -/
  | rd8 (mem : MT) (arr : Term) (i : MT)
  /-- `f a₁ … aₖ` (a folded function, a continuation) -/
  | app (f : Name) (args : Array MT)
  | raw (t : Term)
  | hole (i : Nat)
  deriving Inhabited

/-- A condition (a `Prop`). -/
meta inductive MC where
  | cmp (o : String) (a b : MT)
  | and (p q : MC)
  | or (p q : MC)
  | not (p : MC)
  deriving Inhabited

/-- A model result. -/
meta inductive MR where
  | none
  /-- `some (v, mem)` -/
  | some (v : MT) (mem : MT)
  /-- `some v` (read-only models) -/
  | someW (v : MT)
  | ite (c : MC) (t e : MR)
  /-- a term of the model's result type (a callee's model, a continuation) -/
  | tail (t : MT)
  deriving Inhabited

meta def mkNum (n : Nat) : Term := Syntax.mkNumLit (toString n)

meta partial def MT.render : MT → MetaM Term
  | .lit n => pure (mkNum n)
  | .hole i => pure (mkIdent (Name.mkSimple s!"__hole{i}"))
  | .raw t => `(($t))
  | .app f args => do
    let as ← args.mapM MT.render
    if as.isEmpty then pure (mkIdent f) else `(($(mkIdent f) $as*))
  | .rd mem arr i => do `(($(mkIdent `rdW) (L.Mem.arr64 $(← mem.render) $arr) $(← i.render)))
  | .rd8 mem arr i => do
    `(((L.Mem.arr8 $(← mem.render) $arr)[($(← i.render)).toNat]?.getD 0).toUInt64)
  | .op o a b => do
    let a ← a.render
    let b ← b.render
    match o with
    | "+" => `(($a + $b))
    | "-" => `(($a - $b))
    | "*" => `(($a * $b))
    | "&&&" => `(($a &&& $b))
    | "|||" => `(($a ||| $b))
    | "^^^" => `(($a ^^^ $b))
    | "<<<" => `(($a <<< $b))
    | ">>>" => `(($a >>> $b))
    | "mulhi" => `((UInt64.ofNat (($a).toNat * ($b).toNat / 2 ^ 64)))
    | _ => throwError "l_model: unknown operator {o}"

meta partial def MC.render : MC → MetaM Term
  | .cmp o a b => do
    let a ← a.render
    let b ← b.render
    match o with
    | "=" => `($a = $b)
    | "≠" => `($a ≠ $b)
    | "<" => `($a < $b)
    | "≤" => `($a ≤ $b)
    | "s<" => `(($a).toInt64 < ($b).toInt64)
    | "s≤" => `(($a).toInt64 ≤ ($b).toInt64)
    | _ => throwError "l_model: unknown comparison {o}"
  | .and p q => do `($(← p.render) ∧ $(← q.render))
  | .or p q => do `($(← p.render) ∨ $(← q.render))
  | .not p => do `(¬ $(← p.render))

meta partial def MR.render : MR → MetaM Term
  | .none => `(Option.none)
  | .some v mem => do `(Option.some ($(← v.render), $(← mem.render)))
  | .someW v => do `(Option.some $(← v.render))
  | .ite c t e => do
    let c ← c.render
    let t ← t.render
    let e ← e.render
    `(if $c then $t else $e)
  | .tail t => t.render

/-- The string form of a term (for comparisons). -/
meta def key (t : Term) : String := toString t.raw

/-! ## Folding named functions back in -/

/-- A fold rule: `f x₀ … xₖ` for the pattern (with holes `xᵢ`). -/
meta structure Fold where
  name : Name
  arity : Nat
  pat : MT
  /-- `f x₁ … xₖ = (g x₁ … xₖ).tail….headD 0` (`j` tails): a result of a list callee `g` -/
  listProj : Option (Name × Nat) := none

/-- The pattern of a fold function's body (its parameters are holes). -/
meta partial def exprPat (e : Lean.Expr) : MetaM MT := do
  let e := e.consumeMData
  if let some n := e.rawNatLit? then return .lit n
  if let Lean.Expr.bvar i := e then return .hole i
  match e.getAppFnArgs with
  | (``OfNat.ofNat, #[_, n, _]) =>
    match n.rawNatLit? with
    | some k => return .lit k
    | none => throwError "l_model: fold pattern: unsupported literal {e}"
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => return .op "+" (← exprPat a) (← exprPat b)
  | (``HSub.hSub, #[_, _, _, _, a, b]) => return .op "-" (← exprPat a) (← exprPat b)
  | (``HMul.hMul, #[_, _, _, _, a, b]) => return .op "*" (← exprPat a) (← exprPat b)
  | (``HAnd.hAnd, #[_, _, _, _, a, b]) => return .op "&&&" (← exprPat a) (← exprPat b)
  | (``HOr.hOr, #[_, _, _, _, a, b]) => return .op "|||" (← exprPat a) (← exprPat b)
  | (``HXor.hXor, #[_, _, _, _, a, b]) => return .op "^^^" (← exprPat a) (← exprPat b)
  | (``HShiftLeft.hShiftLeft, #[_, _, _, _, a, b]) => return .op "<<<" (← exprPat a) (← exprPat b)
  | (``HShiftRight.hShiftRight, #[_, _, _, _, a, b]) => return .op ">>>" (← exprPat a) (← exprPat b)
  | _ => throwError "l_model: fold pattern: unsupported term {e}"

/-- `l = g.tail.….tail` (`j` tails): `(g, j)`. -/
meta partial def listTails (l : Lean.Expr) (j : Nat) : Lean.Expr × Nat :=
  match l.getAppFnArgs with
  | (``List.tail, #[_, l']) => listTails l' (j + 1)
  | _ => (l, j)

meta def mkFold (c : Name) : MetaM Fold := do
  let some v := ((← getEnv).find? c).bind (·.value?) | throwError "l_model: {c} has no body"
  let rec strip (e : Lean.Expr) (k : Nat) : Lean.Expr × Nat :=
    match e with
    | Lean.Expr.lam _ _ b _ => strip b (k + 1)
    | _ => (e, k)
  let (body, k) := strip v 0
  -- `(g x₁ … xₖ).tail….headD 0`
  if let (``List.headD, #[_, l, d]) := body.getAppFnArgs then
    if d.isAppOf ``OfNat.ofNat || d.rawNatLit?.isSome then
      let (g, j) := listTails l 0
      let args := g.getAppArgs
      if let some gc := g.getAppFn.constName? then
        if args.size == k && (List.range k).all (fun i => args[i]! == .bvar (k - 1 - i)) then
          return { name := c, arity := k, pat := .lit 0, listProj := some (gc, j) }
  -- de Bruijn: the last parameter is `bvar 0`; number the holes by parameter position
  let pat ← exprPat body
  let rec renum : MT → MT
    | .hole i => .hole (k - 1 - i)
    | .op o a b => .op o (renum a) (renum b)
    | t => t
  return { name := c, arity := k, pat := renum pat }

/-- Structural equality of model terms (raw syntax by its string form). -/
meta partial def MT.beq : MT → MT → Bool
  | .lit a, .lit b => a == b
  | .op o a b, .op o' a' b' => o == o' && a.beq a' && b.beq b'
  | .rd m a i, .rd m' a' i' => m.beq m' && key a == key a' && i.beq i'
  | .rd8 m a i, .rd8 m' a' i' => m.beq m' && key a == key a' && i.beq i'
  | .app f as, .app g bs => f == g && as.size == bs.size && (as.zip bs).all fun (a, b) => a.beq b
  | .raw t, .raw u => key t == key u
  | .hole i, .hole j => i == j
  | _, _ => false

meta partial def MT.matchPat (pat t : MT) (σ : Array (Option MT)) : Option (Array (Option MT)) :=
  match pat, t with
  | .hole i, t =>
    match σ[i]? with
    | some (some u) => if u.beq t then some σ else none
    | some none => some (σ.set! i (some t))
    | none => none
  | .lit a, .lit b => if a == b then some σ else none
  | .op o a b, .op o' a' b' =>
    if o == o' then (MT.matchPat a a' σ).bind (MT.matchPat b b' ·) else none
  | _, _ => none

/-- Fold `t` at its root with the first rule that matches. -/
meta def foldRoot (rules : Array Fold) (t : MT) : MT := Id.run do
  for r in rules do
    if r.listProj.isSome then continue
    if let some σ := MT.matchPat r.pat t (Array.replicate r.arity none) then
      if σ.all (·.isSome) then
        return .app r.name (σ.map (·.get!))
  return t

/-! ## Callee models, read off their specs -/

/-- What a call does in the model. Terms mention the memory as `__m` and the arguments as
`__a0`, `__a1`, …. -/
meta inductive CKind where
  /-- `F : Option (Word × Mem)` -/
  | eff (t : Term)
  /-- `F : Option (List Word × Mem)`: several results and the memory -/
  | effL (t : Term)
  /-- results `F₀, F₁, …`, memory unchanged -/
  | pure (ts : Array Term)
  /-- results `F.headD 0, F.tail.headD 0, …`; `guard`: `F = []` is `none` -/
  | list (t : Term) (guard : Bool)
  /-- `F : Option Mem` -/
  | memOpt (t : Term)
  /-- `F : Mem`, after the guards (`¬ gᵢ` is `none`) -/
  | memTot (t : Term) (guards : Array Term)
  /-- `F : Option Word`, memory unchanged -/
  | ro (t : Term)
  deriving Inhabited

meta structure Callee where
  kind : CKind
  deriving Inhabited

meta def substT (t : Term) (mem : Term) (args : Array Term) : MetaM Term := do
  let r ← t.raw.replaceM fun s => do
    if let .ident _ _ n _ := s then
      if n == `__m then return some mem.raw
      if let .str .anonymous str := n then
        if str.startsWith "__a" then
          if let some i := (str.drop 3).toString.toNat? then
            if let some a := args[i]? then return some a.raw
    return none
  return ⟨r⟩

meta def strLit? (e : Lean.Expr) : Option String :=
  match e.consumeMData with
  | .lit (.strVal s) => some s
  | _ => none

/-- The conjuncts of a `Prop`. -/
meta partial def conjuncts (e : Lean.Expr) : Array Lean.Expr :=
  match e.consumeMData.getAppFnArgs with
  | (``And, #[a, b]) => conjuncts a ++ conjuncts b
  | _ => #[e]

/-- `r.headD 0`, `r.tail.headD 0`, …: the index of the result word. -/
meta partial def resIdx (r e : Lean.Expr) : Option Nat :=
  match e.consumeMData.getAppFnArgs with
  | (``List.headD, #[_, l, _]) => go l 0
  | _ => none
where go (l : Lean.Expr) (k : Nat) : Option Nat :=
  if l == r then some k else
  match l.consumeMData.getAppFnArgs with
  | (``List.tail, #[_, l']) => go l' (k + 1)
  | _ => none

/-- Analyse a callee spec: its function name and its model. -/
meta def analyseSpec (spec : Lean.Expr) : TermElabM (String × Callee) := do
  let ty ← instantiateMVars (← inferType spec)
  forallTelescopeReducing ty fun xs body => do
    -- `Triple x P Q E`
    let body := body.consumeMData
    let args := body.getAppArgs
    unless body.isAppOf ``Std.WP.Triple && args.size ≥ 5 do
      throwError "l_model: not a triple: {body}"
    let x := args[args.size - 5]!
    let post := args[args.size - 2]!
    let (fname, callArgs) ← match x.getAppFnArgs with
      | (``L.invoke, #[_, _, f, vs]) =>
        let some f := strLit? f | throwError "l_model: callee name not a literal in {x}"
        let some vs := vs.listLit? | throwError "l_model: arguments not a list literal in {x}"
        pure (f, vs.2.toArray)
      | _ => throwError "l_model: not a call: {x}"
    -- the initial state is the first `St` binder
    let mut s0? : Option Lean.Expr := none
    for v in xs do
      if (← inferType v).isConstOf ``L.St then s0? := some v; break
    let some s0 := s0? | throwError "l_model: no initial state in {ty}"
    let memE := mkApp (mkConst ``L.St.mem) s0
    withLocalDeclD `__m (mkConst ``L.Mem) fun mvar => do
    let mut decls : Array (Name × Lean.Expr) := #[]
    for i in [0:callArgs.size] do
      decls := decls.push (Name.mkSimple s!"__a{i}", mkConst ``L.Word)
    withLocalDeclsDND decls fun avars => do
    let argVars := avars
    -- replace `s₀.mem` by `__m` and the argument variables by `__aᵢ`
    let repl (e : Lean.Expr) : Lean.Expr := Id.run do
      let mut e := e.replace fun t => if t == memE then some mvar else none
      for i in [0:callArgs.size] do
        e := e.replace fun t => if t == callArgs[i]! then some argVars[i]! else none
      return e
    let delabT (e : Lean.Expr) : TermElabM Term := do
      let e := repl e
      if Lean.Expr.containsFVar e s0.fvarId! then throwError "l_model: callee model mentions the state: {e}"
      withOptions (fun o => o.setBool `pp.fullNames true |>.setBool `pp.funBinderTypes true) do
        PrettyPrinter.delab e
    let Lean.Expr.lam _ _ (Lean.Expr.lam _ _ q _) _ := post.consumeMData
      | throwError "l_model: post not `fun r s' => …`: {post}"
    withLocalDeclD `r (← mkAppM ``List #[mkConst ``L.Word]) fun r => do
    withLocalDeclD `s' (mkConst ``L.St) fun s' => do
    let q := q.instantiateRev #[r, s']
    let cs := conjuncts q
    let memS' := mkApp (mkConst ``L.St.mem) s'
    let mut memSame := false
    let mut nonempty := false
    let mut listF : Option Lean.Expr := none
    let mut pures : Array (Nat × Lean.Expr) := #[]
    let mut eff : Option Lean.Expr := none
    let mut effL : Option Lean.Expr := none
    let mut memOpt : Option Lean.Expr := none
    let mut memTot : Option Lean.Expr := none
    let mut ro : Option Lean.Expr := none
    let mut guards : Array Lean.Expr := #[]
    for c in cs do
      let c := c.consumeMData
      match c.getAppFnArgs with
      | (``L.LocEq, _) => pure ()
      | (``Eq, #[_, a, b]) =>
        if a == s' && b == s0 then memSame := true
        else if a == memS' && b == memE then memSame := true
        else if a == memS' then memTot := some b
        else if a == r then listF := some b
        else if let some i := resIdx r a then pures := pures.push (i, b)
        else
          match b.getAppFnArgs with
          | (``Option.some, #[_, v]) =>
            match v.getAppFnArgs with
            | (``Prod.mk, #[_, _, v1, v2]) =>
              if resIdx r v1 == some 0 && v2 == memS' then eff := some a
              else if v1 == r && v2 == memS' then effL := some a
              else throwError "l_model: unsupported post conjunct {c}"
            | _ =>
              if v == memS' then memOpt := some a
              else if resIdx r v == some 0 then ro := some a
              else throwError "l_model: unsupported post conjunct {c}"
          | _ => throwError "l_model: unsupported post conjunct {c}"
      | (``Ne, #[_, l, nil]) =>
        if l == r && nil.isAppOf ``List.nil then nonempty := true
        else guards := guards.push c
      | (``Not, #[a]) =>
        match a.consumeMData.getAppFnArgs with
        | (``Eq, #[_, l, nil]) =>
          if l == r && nil.isAppOf ``List.nil then nonempty := true
          else guards := guards.push c
        | _ => guards := guards.push c
      | _ =>
        if c.containsFVar s'.fvarId! || c.containsFVar r.fvarId! then
          throwError "l_model: unsupported post conjunct {c}"
        guards := guards.push c
    let kind ← if let some e := effL then do
        unless eff.isNone && memOpt.isNone && memTot.isNone && ro.isNone && listF.isNone do
          throwError "l_model: callee {fname}: ambiguous post"
        pure (CKind.effL (← delabT e))
      else match eff, memOpt, memTot, ro, listF with
      | some e, none, none, none, none => pure (CKind.eff (← delabT e))
      | none, some e, none, none, none => pure (CKind.memOpt (← delabT e))
      | none, none, some e, none, none => pure (CKind.memTot (← delabT e) (← guards.mapM delabT))
      | none, none, none, some e, none =>
        unless memSame do throwError "l_model: read-only callee {fname} must keep the memory"
        pure (CKind.ro (← delabT e))
      | none, none, none, none, some e =>
        unless memSame do throwError "l_model: list callee {fname} must keep the memory"
        pure (CKind.list (← delabT e) nonempty)
      | none, none, none, none, none =>
        unless memSame do throwError "l_model: callee {fname}: no model in its post"
        let n := pures.foldl (fun k (i, _) => max k (i + 1)) 0
        let mut ts : Array Term := #[]
        for i in [0:n] do
          match pures.find? (·.1 == i) with
          | some (_, e) => ts := ts.push (← delabT e)
          | none => ts := ts.push (← `(0))
        pure (CKind.pure ts)
      | _, _, _, _, _ => throwError "l_model: callee {fname}: ambiguous post"
    if !guards.isEmpty then
      match kind with
      | .memTot .. => pure ()
      | _ => throwError "l_model: callee {fname}: unsupported side conditions {guards}"
    return (fname, { kind })

/-! ## The L text -/

/-- Every position in `s` becomes the (synthetic) range of `ref`. -/
meta partial def reposition (s ref : Syntax) : Syntax :=
  let info := SourceInfo.fromRef ref (canonical := false)
  match s with
  | .node _ k args => .node info k (args.map (reposition · ref))
  | .atom _ v => .atom info v
  | .ident _ raw v pre => .ident info raw v pre
  | .missing => .missing

/-- Shift the original positions in `s` (parsed from a substring) by `off` bytes. -/
meta partial def shiftPos (s : Syntax) (off : Nat) : Syntax :=
  let sh : SourceInfo → SourceInfo
    | .original l p t e => .original l ⟨p.byteIdx + off⟩ t ⟨e.byteIdx + off⟩
    | i => i
  match s with
  | .node i k args => .node (sh i) k (args.map (shiftPos · off))
  | .atom i v => .atom (sh i) v
  | .ident i raw v pre => .ident (sh i) raw v pre
  | .missing => .missing

/-- The `lfn` term of `c`, read back from its source file (this file, or the `.lean` file of the
module that declares it, found from the module name relative to the working directory). -/
meta def lfnSyntax (c : Name) : CommandElabM Syntax := do
  let some rs ← findDeclarationRanges? c | throwError "l_model: no source for {c}"
  let env ← getEnv
  let (fm, here) ← match env.getModuleIdxFor? c with
    | none => pure ((← getFileMap), true)
    | some idx =>
      let mod := env.header.moduleNames[idx.toNat]!
      let path : System.FilePath := (mod.toString.replace "." "/") ++ ".lean"
      pure (FileMap.ofString (← IO.FS.readFile path), false)
  let src := fm.source
  let p1 := fm.ofPosition rs.range.pos
  let p2 := fm.ofPosition rs.range.endPos
  let txt := (String.Pos.Raw.extract src p1 p2)
  let parts := txt.splitOn ":= lfn "
  let some i := parts.tail.head? |>.map (fun s => "lfn " ++ s)
    | throwError "l_model: {c} is not `… := lfn …`"
  let off := p1.byteIdx + parts.head!.utf8ByteSize + ":= ".length
  match Parser.runParserCategory (← getEnv) `term i with
  | .ok stx => return if here then shiftPos stx off else stx
  | .error e => throwError "l_model: cannot re-parse the L text of {c}: {e}"

/-! ## Translation -/

/-- A continuation definition. -/
meta structure KDef where
  name : Name
  fuel : Bool
  caps : Array Name
  capMem : Bool
  /-- `0`: `some (x, m₁)`; `1`: `some m₁`; `2`: `some x`; `3`: a join point; `4`: `some (r, m₁)`
  with `r : List Word` (a callee with several results) -/
  binder : Nat
  res : Name
  body : MR
  key : String
  /-- the continuations its body applies -/
  refs : Array Name
  deriving Inhabited

meta structure GenState where
  ks : Array KDef := #[]
  dups : Nat := 0
  base : Name := .anonymous
  /-- the functions called by the function being translated -/
  called : Array String := #[]
  deriving Inhabited

/-- A join point: its name, whether it takes the fuel, the locals it takes, whether it takes the
memory. -/
meta structure Join where
  name : Name
  fuel : Bool
  caps : Array Nat
  capMem : Bool
  deriving Inhabited

meta structure Ctx where
  names : Array Name
  env : Array MT
  mem : MT
  ro : Bool
  /-- where the end of the statement list goes (a join point), if not to the function's end -/
  ft : Option Join := none
  /-- the models' Lean parameters (`Env.mps`): L names equal to one get a prime -/
  clash : Array Name := #[]

meta def memIdent : Name := `m
meta def mem1Ident : Name := `m₁

abbrev GenM := StateRefT GenState TermElabM

meta structure Env where
  group : Array (String × Name × Bool)
  callees : Array (String × Callee)
  folds : Array Fold
  /-- list callees whose `r ≠ []` does not become a `none` branch -/
  noguard : Array String := #[]
  /-- the models' Lean parameters: the command's explicit binders that the callees' models
  mention (`p` in `callW p n "f" [..] m`); every model and continuation takes them first -/
  mps : Array Name := #[]

/-- L names that would clash with the model's own binders get a prime. -/
meta def sanitize (n : Name) (clash : Array Name := #[]) : Name :=
  if n == `n || n == `m || n == `m₁ || n == `r || clash.contains n then n.appendAfter "'" else n

meta def Ctx.idx (ctx : Ctx) (x : Ident) : Option Nat := ctx.names.idxOf? (sanitize x.getId ctx.clash)

meta def splitArr (id : Ident) : GenM (Term × String) := do
  match id.getId with
  | .str pre "u8" => return (mkIdentFrom id pre, "u8")
  | .str pre "u64" => return (mkIdentFrom id pre, "u64")
  | .str pre "c8" => return (mkIdentFrom id pre, "c8")
  | _ => throwErrorAt id "expected `A.u8`, `A.u64` or `D.c8`"

/-- A store-record field constant (`APP.a : Word`, an `abbrev` of a numeral) as that numeral, so
that models and proofs state field offsets as numbers (`tfld m APP t i 1`). -/
meta def fieldNum (fI : Ident) : GenM Term := do
  let c ← realizeGlobalConstNoOverload fI
  let some v := ((← getEnv).find? c).bind (·.value?) | throwErrorAt fI "not a field constant"
  let v := v.consumeMData
  let n? := if v.isAppOfArity ``OfNat.ofNat 3 then (v.getArg! 1).consumeMData.rawNatLit? else none
  match n? with
  | some n => pure (Syntax.mkNumLit (toString n))
  | none => throwErrorAt fI m!"field constant {c} is not a numeral: {v}"

mutual
meta partial def transE (E : Env) (ctx : Ctx) : TSyntax `lexpr → GenM MT
  | `(lexpr| $n:num) => pure (.lit n.getNat)
  | `(lexpr| $c:char) => pure (.lit c.getChar.toNat)
  | `(lexpr| ⟪$t⟫) => pure (.raw t)
  | `(lexpr| $x:ident) => do
    match ctx.idx x with
    | some k => pure ctx.env[k]!
    | none => do pure (.raw (← `(L.Mem.glob $(← ctx.mem.render) ($x : L.GVar))))
  | `(lexpr| $r:ident[$i:lexpr].$f:ident) => do
    let fI := mkIdentFrom f (r.getId ++ f.getId)
    let ad ← `(L.Record.ad $r $(← (← transE E ctx i).render) $fI)
    pure (.rd ctx.mem (← `(L.Record.arr $r)) (.raw ad))
  | `(lexpr| $r:ident⟨$t:lexpr⟩[$i:lexpr].$f:ident) => do
    let fI ← fieldNum (mkIdentFrom f (r.getId ++ f.getId))
    pure (.raw (← `($(mkIdent `L.Arena.tfld) $(← ctx.mem.render) $r $(← (← transE E ctx t).render)
      $(← (← transE E ctx i).render) $fI)))
  | `(lexpr| $r:ident⟨$t:lexpr⟩[$i:lexpr]) => do
    pure (.raw (← `($(mkIdent `L.Arena.tfld) $(← ctx.mem.render) $r $(← (← transE E ctx t).render)
      $(← (← transE E ctx i).render) 0)))
  | `(lexpr| $r:ident⟨$t:lexpr⟩.$c:ident) => do
    unless c.getId == `count do throwErrorAt c "expected `R⟨t⟩.count`"
    pure (.raw (← `($(mkIdent `L.Arena.tcnt) $(← ctx.mem.render) $r $(← (← transE E ctx t).render))))
  | `(lexpr| $r:ident⟦$h:lexpr⟧.$f:ident) => do
    let fI ← fieldNum (mkIdentFrom f (r.getId ++ f.getId))
    let h ← (← transE E ctx h).render
    pure (.raw (← `($(mkIdent `L.Arena.tfld) $(← ctx.mem.render) $r ($(mkIdent `L.Arena.tierW) $h) ($(mkIdent `L.Arena.idxW) $h) $fI)))
  | `(lexpr| $r:ident⟦$h:lexpr⟧) => do
    let h ← (← transE E ctx h).render
    pure (.raw (← `($(mkIdent `L.Arena.tfld) $(← ctx.mem.render) $r ($(mkIdent `L.Arena.tierW) $h) ($(mkIdent `L.Arena.idxW) $h) 0)))
  | `(lexpr| ⟦$h:lexpr⟧.$c:ident) => do
    let h ← (← transE E ctx h).render
    match c.getId with
    | `tier => pure (.raw (← `($(mkIdent `L.Arena.tierW) $h)))
    | `idx => pure (.raw (← `($(mkIdent `L.Arena.idxW) $h)))
    | _ => throwErrorAt c "expected `⟦h⟧.tier` or `⟦h⟧.idx`"
  | `(lexpr| $a:ident[$i:lexpr]) => do
    let (arr, k) ← splitArr a
    let i ← transE E ctx i
    match k with
    | "u64" => pure (.rd ctx.mem arr i)
    | "u8" => pure (.rd8 ctx.mem arr i)
    | _ => pure (.raw (← `(((($arr : List UInt8))[($(← i.render)).toNat]?.getD 0).toUInt64)))
  | `(lexpr| len($a:ident)) => do
    let (arr, k) ← splitArr a
    match k with
    | "u8" => pure (.raw (← `(L.Mem.len8 $(← ctx.mem.render) $arr)))
    | "u64" => pure (.raw (← `(L.Mem.len64 $(← ctx.mem.render) $arr)))
    | _ => pure (.raw (← `(UInt64.ofNat (List.length $arr))))
  | `(lexpr| mulhi($a:lexpr, $b:lexpr)) => bin "mulhi" a b
  | `(lexpr| u64($c:lcond)) => do
    let c ← transC E ctx c
    pure (.raw (← `(if $(← c.render) then (1 : Word) else 0)))
  | `(lexpr| ($e:lexpr)) => transE E ctx e
  | `(lexpr| $a:lexpr * $b:lexpr) => bin "*" a b
  | `(lexpr| $a:lexpr + $b:lexpr) => bin "+" a b
  | `(lexpr| $a:lexpr - $b:lexpr) => bin "-" a b
  | `(lexpr| $a:lexpr << $b:lexpr) => bin "<<<" a b
  | `(lexpr| $a:lexpr >> $b:lexpr) => bin ">>>" a b
  | `(lexpr| $a:lexpr & $b:lexpr) => bin "&&&" a b
  | `(lexpr| $a:lexpr ^ $b:lexpr) => bin "^^^" a b
  | `(lexpr| $a:lexpr | $b:lexpr) => bin "|||" a b
  | e => throwErrorAt e "l_model: unsupported L expression"
where
  bin (o : String) (a b : TSyntax `lexpr) : GenM MT := do
    return foldRoot E.folds (.op o (← transE E ctx a) (← transE E ctx b))

meta partial def transC (E : Env) (ctx : Ctx) : TSyntax `lcond → GenM MC
  | `(lcond| $p:lcond && $q:lcond) => do return .and (← transC E ctx p) (← transC E ctx q)
  | `(lcond| $p:lcond || $q:lcond) => do return .or (← transC E ctx p) (← transC E ctx q)
  | `(lcond| !$p:lcond) => do return .not (← transC E ctx p)
  | `(lcond| ($p:lcond)) => transC E ctx p
  | `(lcond| $a:lexpr == $b:lexpr) => cmp "=" a b
  | `(lcond| $a:lexpr != $b:lexpr) => cmp "≠" a b
  | `(lcond| $a:lexpr < $b:lexpr) => cmp "<" a b
  | `(lcond| $a:lexpr <= $b:lexpr) => cmp "≤" a b
  | `(lcond| $a:lexpr > $b:lexpr) => cmp "<" b a
  | `(lcond| $a:lexpr >= $b:lexpr) => cmp "≤" b a
  | `(lcond| $a:lexpr <ₛ $b:lexpr) => cmp "s<" a b
  | `(lcond| $a:lexpr ≤ₛ $b:lexpr) => cmp "s≤" a b
  | c => throwErrorAt c "l_model: unsupported L condition"
where
  cmp (o : String) (a b : TSyntax `lexpr) : GenM MC := do
    return .cmp o (← transE E ctx a) (← transE E ctx b)
end

meta def blockStmts : TSyntax `lblock → GenM (List (TSyntax `lstmt))
  | `(lblock| { $ss;* }) => pure ss.getElems.toList
  | b => throwErrorAt b "l_model: unsupported L block"

/-- Does the statement list end every path with `return`/`abort`? -/
meta partial def terminates : List (TSyntax `lstmt) → Bool
  | [] => false
  | ss =>
    match ss.getLast! with
    | `(lstmt| return $_:lexpr) => true
    | `(lstmt| return ($_:lexpr, $_:lexpr,*)) => true
    | `(lstmt| abort) => true
    | `(lstmt| if $_:lcond { $s;* } else { $t;* }) =>
      terminates s.getElems.toList && terminates t.getElems.toList
    | _ => false

/-- All identifiers in a syntax tree. -/
meta partial def idents (s : Syntax) (acc : NameSet := {}) : NameSet :=
  match s with
  | .ident _ _ n _ => acc.insert n
  | .node _ _ args => args.foldl (fun acc a => idents a acc) acc
  | _ => acc

meta def setEnv (ctx : Ctx) (k : Nat) (v : MT) : Ctx := { ctx with env := ctx.env.set! k v }

mutual
meta partial def transS (E : Env) (ctx : Ctx) : List (TSyntax `lstmt) → GenM MR
  | [] => match ctx.ft with
    | some j => pure (.tail (.app j.name (E.mps.map (fun x => MT.raw (mkIdent x)) ++ (if j.fuel then #[MT.raw (mkIdent `n)] else #[]) ++
        j.caps.map (ctx.env[·]!) ++ (if j.capMem then #[ctx.mem] else #[]))))
    | none => pure (if ctx.ro then .someW (.lit 0) else .some (.lit 0) ctx.mem)
  | s :: rest => do
    let assignOp (x : Ident) (o : String) (e : TSyntax `lexpr) : GenM MR := do
      let v ← transE E ctx e
      match ctx.idx x with
      | some k => transS E (setEnv ctx k (foldRoot E.folds (.op o ctx.env[k]! v))) rest
      | none => throwErrorAt x "l_model: global updates are not supported"
    let setGlob (x : Ident) (v : MT) : GenM MR := do
      if ctx.ro then throwErrorAt x "l_model: a read-only model cannot write"
      let mem ← `(L.Mem.setG $(← ctx.mem.render) ($x : L.GVar) $(← v.render))
      transS E { ctx with mem := .raw mem } rest
    let store (arr : Term) (i : MT) (e : TSyntax `lexpr) : GenM MR := do
      if ctx.ro then throwError "l_model: a read-only model cannot write"
      let v ← transE E ctx e
      let mem ← `(L.Mem.set64 $(← ctx.mem.render) $arr $(← i.render) $(← v.render))
      transS E { ctx with mem := .raw mem } rest
    let ite (c : TSyntax `lcond) (t e : List (TSyntax `lstmt)) : GenM MR := do
      let c ← transC E ctx c
      if !rest.isEmpty && !terminates t && !terminates e then
        -- both branches fall through: the rest becomes a join point
        let ft ← mkJoin E ctx rest
        let ctxJ := { ctx with ft := some ft }
        return .ite c (← transS E ctxJ t) (← transS E ctxJ e)
      return .ite c (← transS E ctx (t ++ rest)) (← transS E ctx (e ++ rest))
    match s with
    | `(lstmt| $x:ident := call $f:ident($args,*)) =>
      transCall E ctx #[x] f args.getElems rest
    | `(lstmt| ($x:ident, $xs:ident,* ) := call $f:ident($args,*)) =>
      transCall E ctx (#[x] ++ xs.getElems) f args.getElems rest
    | `(lstmt| $x:ident := $e:lexpr) => do
      let v ← transE E ctx e
      match ctx.idx x with
      | some k => transS E (setEnv ctx k v) rest
      | none => setGlob x v
    | `(lstmt| $x:ident += $e:lexpr) => assignOp x "+" e
    | `(lstmt| $x:ident -= $e:lexpr) => assignOp x "-" e
    | `(lstmt| $r:ident[$i:lexpr].$f:ident := $e:lexpr) => do
      let fI := mkIdentFrom f (r.getId ++ f.getId)
      let ad ← `(L.Record.ad $r $(← (← transE E ctx i).render) $fI)
      store (← `(L.Record.arr $r)) (.raw ad) e
    | `(lstmt| $a:ident[$i:lexpr] := $e:lexpr) => do
      let (arr, k) ← splitArr a
      unless k == "u64" do throwErrorAt s "l_model: byte stores are not supported"
      store arr (← transE E ctx i) e
    | `(lstmt| if $c:lcond $b:lblock) => ite c (← blockStmts b) []
    | `(lstmt| if $c:lcond $b:lblock else $t:lblock) => ite c (← blockStmts b) (← blockStmts t)
    | `(lstmt| if $c:lcond $b:lblock else $t:lstmt) => ite c (← blockStmts b) [t]
    | `(lstmt| return $e:lexpr) => do
      let v ← transE E ctx e
      pure (if ctx.ro then .someW v else .some v ctx.mem)
    | `(lstmt| abort) => pure .none
    | `(lstmt| skip) => transS E ctx rest
    | _ => throwErrorAt s "l_model: unsupported L statement"

meta partial def transCall (E : Env) (ctx : Ctx) (xs : Array Ident) (f : Ident)
    (args : Array (TSyntax `lexpr)) (rest : List (TSyntax `lstmt)) : GenM MR := do
  let fname := f.getId.toString
  modify fun st => { st with called := st.called.push fname }
  let argsT ← args.mapM fun a => do (← transE E ctx a).render
  let memT ← ctx.mem.render
  let xk ← xs.mapM fun x => match ctx.idx x with
    | some k => pure k
    | none => throwErrorAt x "l_model: call results go to locals"
  let assign (ctx : Ctx) (vs : Array MT) : Ctx := Id.run do
    let mut ctx := ctx
    for i in [0:xk.size] do
      ctx := setEnv ctx xk[i]! (vs[i]?.getD (.lit 0))
    return ctx
  -- `x := call f(…); return x`
  let isTail : Bool := match rest with
    | s :: _ => match s with
      | `(lstmt| return $e:lexpr) => match e with
        | `(lexpr| $y:ident) => xs.size == 1 && y.getId == xs[0]!.getId
        | _ => false
      | _ => false
    | _ => false
  let effK (callT : MT) (isTail : Bool) (xk : Array Nat) : GenM MR := do
    if isTail && !ctx.ro then return .tail callT
    if xk.size > 1 then throwErrorAt f "l_model: several results of an effectful call"
    mkK E ctx 0 xk[0]? xk callT rest
  -- the abort condition for a guard `g` of a callee's post
  let negC (g : Term) : GenM MC := do
    match g with
    | `($a ≠ $b) => return .cmp "=" (.raw a) (.raw b)
    | _ => return .not (.cmp "=" (.raw (← `(decide $g))) (.raw (← `(true))))
  if let some (_, w, wro) := E.group.find? (·.1 == fname) then
    let t ← `($(mkIdent w) $(E.mps.map (fun x => (mkIdent x : Term)))* $(mkIdent `n) $memT $argsT*)
    if wro then
      if ctx.ro && isTail then return .tail (.raw t)
      return ← mkK E ctx 2 xk[0]? xk (.raw t) rest
    if ctx.ro then throwErrorAt f "l_model: a read-only model calls an effectful one"
    return ← effK (.raw t) isTail xk
  let some (_, c) := E.callees.find? (·.1 == fname)
    | throwErrorAt f "l_model: no spec given for the callee {fname}"
  match c.kind with
  | .eff t =>
    if ctx.ro then throwErrorAt f "l_model: a read-only model calls an effectful one"
    effK (.raw (← substT t memT argsT)) isTail xk
  | .effL t =>
    if ctx.ro then throwErrorAt f "l_model: a read-only model calls an effectful one"
    mkK E ctx 4 none xk (.raw (← substT t memT argsT)) rest
  | .pure ts =>
    let vs ← ts.mapM fun t => do return MT.raw (← substT t memT argsT)
    transS E (assign ctx vs) rest
  | .list t guard =>
    let l ← substT t memT argsT
    -- the template `g __m __a0 …` of a list callee, for the fold rules of its results
    let gName? : Option Name := match t.raw with
      | .node _ _ args =>
        if args.size == 2 && args[0]!.isIdent && args[1]!.getArgs.size == argsT.size + 1 &&
            args[1]!.getArgs.toList.map (·.getId) == (`__m :: (List.range argsT.size).map fun i =>
              Name.mkSimple s!"__a{i}") then
          some args[0]!.getId else none
      | _ => none
    let vs ← (List.range xk.size).toArray.mapM fun i => do
      if let some g := gName? then
        if let some r := E.folds.find? (·.listProj == some (g, i)) then
          return MT.app r.name (#[ctx.mem] ++ (← args.mapM (transE E ctx)))
      let mut e ← `($l)
      for _ in [0:i] do e ← `(List.tail $e)
      return MT.raw (← `(List.headD $e 0))
    let body ← transS E (assign ctx vs) rest
    if guard && !E.noguard.contains fname then
      return .ite (.cmp "=" (.raw l) (.raw (← `([])))) .none body
    return body
  | .memOpt t =>
    if ctx.ro then throwErrorAt f "l_model: a read-only model cannot write"
    mkK E ctx 1 none xk (.raw (← substT t memT argsT)) rest
  | .memTot t guards =>
    if ctx.ro then throwErrorAt f "l_model: a read-only model cannot write"
    let m' ← substT t memT argsT
    let body ← transS E { (assign ctx #[]) with mem := .raw m' } rest
    let mut r := body
    for g in guards.reverse do
      let g ← substT g memT argsT
      r := .ite (← negC g) .none r
    return r
  | .ro t =>
    let callT := MT.raw (← substT t memT argsT)
    if ctx.ro && isTail then return .tail callT
    mkK E ctx 2 xk[0]? xk callT rest

/-- Make the continuation of a call: the rest of the code, as a definition over the locals it
reads. -/
meta partial def mkK (E : Env) (ctx : Ctx) (binder : Nat) (res : Option Nat) (xk : Array Nat)
    (callT : MT) (rest : List (TSyntax `lstmt)) : GenM MR := do
  let resName := match res with
    | some k => ctx.names[k]!
    | none => `r
  -- inside: every local is its own name, the result is the binder, the memory is `m₁`
  -- (or the captured `m`)
  let mut env : Array MT := ctx.names.map fun n => .raw (mkIdent n)
  for i in [0:xk.size] do
    if binder == 4 then
      -- result `i` of the list: `(r.tail….tail).headD 0`
      let mut e : Term := mkIdent resName
      for _ in [0:i] do e ← `(List.tail $e)
      env := env.set! xk[i]! (.raw (← `(List.headD $e 0)))
    else
      env := env.set! xk[i]! (if i == 0 && binder != 1 then .raw (mkIdent resName) else .lit 0)
  let mem : MT := if binder == 2 then .raw (mkIdent memIdent) else .raw (mkIdent mem1Ident)
  let ctx' : Ctx := { ctx with env, mem }
  let body ← transS E ctx' rest
  let bodyT ← body.render
  let used := idents bodyT.raw
  let fuel := used.contains `n
  let capMem := binder == 2 && used.contains memIdent
  let mut caps : Array Name := #[]
  let mut capVals : Array MT := #[]
  for i in [0:ctx.names.size] do
    let nm := ctx.names[i]!
    if xk.contains i then continue
    if used.contains nm then
      caps := caps.push nm
      capVals := capVals.push ctx.env[i]!
  let k := toString (fuel, caps, capMem, binder, resName, key bodyT)
  let st ← get
  let name ← match st.ks.find? (·.key == k) with
    | some kd => pure kd.name
    | none => do
      let cnt := (st.ks.filter (·.name.getPrefix == st.base)).size
      let name := st.base ++ Name.mkSimple s!"k{cnt + 1}"
      let refs := st.ks.filterMap fun kd => if used.contains kd.name then some kd.name else none
      let kd : KDef := { name, fuel, caps, capMem, binder, res := resName, body, key := k, refs }
      modify fun st => { st with ks := st.ks.push kd }
      pure name
  let args := E.mps.map (fun x => MT.raw (mkIdent x)) ++ (if fuel then #[MT.raw (mkIdent `n)] else #[]) ++
    capVals ++ (if capMem then #[ctx.mem] else #[]) ++ #[callT]
  return .tail (.app name args)

/-- Make a join point: the rest of the code after an `if` both of whose branches fall through,
as a definition over the locals it reads and the memory; the branches end by applying it. -/
meta partial def mkJoin (E : Env) (ctx : Ctx) (rest : List (TSyntax `lstmt)) :
    GenM Join := do
  let env : Array MT := ctx.names.map fun n => .raw (mkIdent n)
  let ctx' : Ctx := { ctx with env, mem := .raw (mkIdent memIdent) }
  let body ← transS E ctx' rest
  let bodyT ← body.render
  let used := idents bodyT.raw
  let fuel := used.contains `n
  let capMem := used.contains memIdent
  let mut caps : Array Name := #[]
  let mut capIdx : Array Nat := #[]
  for i in [0:ctx.names.size] do
    if used.contains ctx.names[i]! then
      caps := caps.push ctx.names[i]!
      capIdx := capIdx.push i
  let k := toString (fuel, caps, capMem, 3, key bodyT)
  let st ← get
  let name ← match st.ks.find? (·.key == k) with
    | some kd => pure kd.name
    | none => do
      let cnt := (st.ks.filter (·.name.getPrefix == st.base)).size
      let name := st.base ++ Name.mkSimple s!"k{cnt + 1}"
      let refs := st.ks.filterMap fun kd => if used.contains kd.name then some kd.name else none
      let kd : KDef := { name, fuel, caps, capMem, binder := 3, res := `r, body, key := k, refs }
      modify fun st => { st with ks := st.ks.push kd }
      pure name
  return { name, fuel, caps := capIdx, capMem }
end

/-! ## Leaves and guarded equations -/

meta def leaves : MR → List (List (MC × Bool) × MR)
  | .none => []
  | .ite c t e =>
    (leaves t).map (fun (p, l) => ((c, true) :: p, l)) ++
    (leaves e).map (fun (p, l) => ((c, false) :: p, l))
  | l => [([], l)]

/-! ## The command -/

syntax lmodelFn := term " ↦ " ident (&" ro")?

/-- See the module docstring. -/
syntax (name := lmodel) (docComment)? "l_model " ident bracketedBinder*
  &" fns " "[" lmodelFn,* "]"
  (&" specs " "[" term,* "]")?
  (&" grind " "[" ident,* "]")?
  (&" fold " "[" ident,* "]")?
  (&" extra " "[" term,* "]")?
  (&" finish " "[" term,* "]")?
  (&" gen " num)?
  (&" heartbeats " num)?
  (&" noguard " "[" str,* "]")?
  (&" trace")? : command

meta structure FnInfo where
  lname : String
  decl : Name
  model : Name
  ro : Bool
  lookup : Term
  params : Array Name
  lcls : Array Name
  body : TSyntax `lblock
  deriving Inhabited

meta def emit (doTrace : Bool) (cmd : Syntax) : CommandElabM Unit := do
  if doTrace then logInfo m!"{cmd}"
  elabCommand cmd

@[command_elab lmodel] meta def elabLModel : CommandElab := fun stx => do
  -- `l_model name binders* fns [..] specs? grind? fold? extra? finish? gen? trace?`
  let doc? : Option (TSyntax `Lean.Parser.Command.docComment) :=
    if stx[0].getNumArgs == 0 then none else some ⟨stx[0][0]⟩
  let stx' := stx
  let stx : Syntax := stx.setArgs (stx.getArgs.extract 1 stx.getNumArgs)
  let specName : Ident := ⟨stx[1]⟩
  let bs : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := stx[2].getArgs.map (⟨·⟩)
  let fnStx : Array (TSyntax `L.ModelGen.lmodelFn) := stx[5].getSepArgs.map (⟨·⟩)
  let optList (k : Nat) : Array Syntax := if stx[k].getNumArgs == 0 then #[] else stx[k][2].getSepArgs
  let specTs : Array Term := (optList 7).map (⟨·⟩)
  let attrIds : Array Ident := (optList 8).map (⟨·⟩)
  let foldIds : Array Ident := (optList 9).map (⟨·⟩)
  let extraTs : Array Term := (optList 10).map (⟨·⟩)
  let hintTs : Array Term := (optList 11).map (⟨·⟩)
  let genN : Option Nat := if stx[12].getNumArgs == 0 then none else stx[12][1].isNatLit?
  let hbN : Option Nat := if stx[13].getNumArgs == 0 then none else stx[13][1].isNatLit?
  let noguard : Array String := (optList 14).filterMap (·.isStrLit?)
  let doTrace := stx[15].getNumArgs != 0
  let stx := stx'
  let (infos, callees, foldRules) ← runTermElabM fun _ => do
    Term.elabBinders bs fun _ => do
    withLocalDeclD `n (mkConst ``Nat) fun _ => do
      let mut infos : Array (String × Name × Name × Bool × Term) := #[]
      for f in fnStx do
        let `(lmodelFn| $lk ↦ $w $[ro%$r]?) := f | throwUnsupportedSyntax
        let e ← elabTerm lk none
        Term.synthesizeSyntheticMVarsNoPostponing
        let ty ← whnfR (← instantiateMVars (← inferType e))
        let some (_, lhs, rhs) := ty.eq? | throwErrorAt lk "l_model: expected `p.lookup \"f\" = some F`"
        let some fname := strLit? (lhs.getAppArgs[lhs.getAppNumArgs - 2]!)
          | throwErrorAt lk "l_model: the function name is not a literal"
        let some c := (rhs.getAppArgs.back!).consumeMData.constName?
          | throwErrorAt lk "l_model: the function is not a constant"
        infos := infos.push (fname, c, w.getId, r.isSome, lk)
      let mut callees : Array (String × Callee) := #[]
      for s in specTs do
        let e ← elabTerm s none
        Term.synthesizeSyntheticMVarsNoPostponing
        let e ← instantiateMVars e
        callees := callees.push (← analyseSpec e)
      let foldRules ← foldIds.mapM fun f => do mkFold (← realizeGlobalConstNoOverloadWithInfo f)
      return (infos, callees, foldRules)
  -- the models' Lean parameters: explicit binders the callee models mention
  let mut allBs : Array (Name × Term) := #[]
  for b in bs do
    if let `(Lean.Parser.Term.bracketedBinderF| ($xs* : $ty)) := b then
      for x in xs do allBs := allBs.push (x.raw.getId, ty)
  let calleeIds : NameSet := callees.foldl (fun acc (_, c) => match c.kind with
    | .eff t | .effL t | .list t _ | .memOpt t | .ro t => idents t.raw acc
    | .pure ts => ts.foldl (fun acc t => idents t.raw acc) acc
    | .memTot t gs => gs.foldl (fun acc t => idents t.raw acc) (idents t.raw acc)) {}
  let mpBs := allBs.filter (calleeIds.contains ·.1)
  let mps := mpBs.map (·.1)
  let mpBinders ← mpBs.mapM fun (x, ty) => `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent x) : $ty))
  let mpArgs : Array Term := mps.map fun x => (mkIdent x : Term)
  -- the L texts
  let mut fis : Array FnInfo := #[]
  for (lname, decl, model, ro, lookup) in infos do
    let s ← lfnSyntax decl
    let `(lfn ($ps,*) $[locals ($ls,*)]? $body:lblock) := s
      | throwError "l_model: {decl} is not an `lfn`"
    let params := ps.getElems.map (sanitize ·.getId mps)
    let locals' := ((ls.map (·.getElems.map (sanitize ·.getId mps))).getD #[])
    fis := fis.push { lname, decl, model, ro, lookup, params, lcls := locals', body }
  let grp := fis.map fun fi => (fi.lname, fi.model, fi.ro)
  let E : Env := { group := grp, callees := callees, folds := foldRules, noguard := noguard, mps }
  -- translate
  let (bodies, st) ← runTermElabM fun _ => do
    let go : GenM (Array (MR × Array String)) := fis.mapM fun fi => do
      modify fun st => { st with base := fi.model, called := #[] }
      let names := fi.params ++ fi.lcls
      let env := names.mapIdx fun i n => if i < fi.params.size then MT.raw (mkIdent n) else .lit 0
      let b ← transS E { names, env, mem := .raw (mkIdent memIdent), ro := fi.ro, clash := mps }
        (← blockStmts fi.body)
      return (b, (← get).called)
    go.run {}
  let calledBy := bodies.map (·.2)
  let bodies := bodies.map (·.1)
  -- a single member that needs no fuel (no recursion, no fuel-dependent callee, no continuation
  -- that needs it) gets a model without the fuel argument
  let noFuel : Bool ← do
    if fis.size != 1 || st.ks.any (·.fuel) then pure false
    else
      let b ← liftTermElabM bodies[0]!.render
      pure !(idents b.raw).contains `n
  if st.dups > 0 && doTrace then
    logInfo m!"l_model: {st.dups} join point(s) duplicated the code after them"
  -- render
  let wordT ← `(L.Word)
  let nI := mkIdent `n
  let resT (ro : Bool) : CommandElabM Term := if ro then `(Option L.Word) else `(Option (L.Word × L.Mem))
  -- Ks without fuel come first (they call no model of the group)
  let kDefs ← st.ks.mapM fun kd => do
    let fi := fis.find? (fun fi => kd.name.getPrefix == fi.model) |>.getD fis[0]!
    let nB ← if kd.fuel then `(Lean.Parser.Term.bracketedBinderF| ($nI : Nat)) else `(Lean.Parser.Term.bracketedBinderF| (_n : Unit))
    let capB ← kd.caps.mapM fun c => `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent c) : $wordT))
    let memB ← if kd.capMem then pure #[← `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent memIdent) : L.Mem))] else pure #[]
    let binders := mpBinders ++ (if kd.fuel then #[nB] else #[]) ++ capB ++ memB
    let argT ← match kd.binder with
      | 0 => `(Option (L.Word × L.Mem))
      | 4 => `(Option (List L.Word × L.Mem))
      | 1 => `(Option L.Mem)
      | _ => `(Option L.Word)
    let pat ← match kd.binder with
      | 0 | 4 => `(Option.some ($(mkIdent kd.res), $(mkIdent mem1Ident)))
      | 1 => `(Option.some $(mkIdent mem1Ident))
      | _ => `(Option.some $(mkIdent kd.res))
    let body ← liftTermElabM kd.body.render
    let rT ← resT fi.ro
    pure (kd, binders, argT, pat, body, rT)
  -- the continuations in the mutual block: those that reach a model of the group
  let models := fis.map (·.model)
  let mut mutK : NameSet := {}
  let mut depth : Std.HashMap Name Nat := {}
  for kd in st.ks do
    let used := idents (← liftTermElabM kd.body.render).raw
    if models.any used.contains || kd.refs.any mutK.contains then mutK := mutK.insert kd.name
    depth := depth.insert kd.name (1 + kd.refs.foldl (fun d r => max d (depth.getD r 0)) 0)
  let fuelKs := kDefs.filter (mutK.contains ·.1.name)
  let plainKs := kDefs.filter (!mutK.contains ·.1.name)
  let wf := !fuelKs.isEmpty
  for (kd, binders, argT, pat, body, rT) in plainKs do
    if kd.binder == 3 then
      emit doTrace (← `(command| def $(mkIdent kd.name):ident $binders* : $rT := $body))
    else
      emit doTrace (← `(command|
        def $(mkIdent kd.name):ident $binders* : $argT → $rT
          | Option.none => Option.none
          | $pat => $body))
  let mut defs : Array (TSyntax `command) := #[]
  for fi in fis, b in bodies do
    let pbs ← fi.params.mapM fun x => `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent x) : L.Word))
    let wbs := mpBinders ++ #[← `(Lean.Parser.Term.bracketedBinderF| ($nI : Nat)), ← `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent memIdent) : L.Mem))] ++ pbs
    let body ← liftTermElabM b.render
    let rT ← resT fi.ro
    let mbs := mpBinders ++ #[← `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent memIdent) : L.Mem))] ++ pbs
    let d ← if noFuel then
      `(command| def $(mkIdent fi.model):ident $mbs* : $rT := $body)
    else if wf then
      `(command|
        def $(mkIdent fi.model):ident $wbs* : $rT :=
          match $nI:ident with
          | 0 => Option.none
          | $nI:ident + 1 => $body
        termination_by ($nI, 0))
    else
      `(command|
        def $(mkIdent fi.model):ident $wbs* : $rT :=
          match $nI:ident with
          | 0 => Option.none
          | $nI:ident + 1 => $body)
    defs := defs.push d
  for (kd, binders, argT, pat, body, rT) in fuelKs do
    let dep := depth.getD kd.name 1
    if kd.binder == 3 then
      defs := defs.push (← `(command|
        def $(mkIdent kd.name):ident $binders* : $rT := $body
        termination_by ($nI, $(mkNum dep))))
    else
      defs := defs.push (← `(command|
        def $(mkIdent kd.name):ident $binders* : $argT → $rT
          | Option.none => Option.none
          | $pat => $body
        termination_by _ => ($nI, $(mkNum dep))))
  if defs.size == 1 then emit doTrace defs[0]!
  else emit doTrace (← `(command| mutual $defs* end))
  -- guarded equations, one per leaf that is not `none`
  let attrsOf (thm : Ident) (lhs : Term) : CommandElabM Unit := do
    for a in attrIds do
      emit doTrace (← `(command| grind_pattern [$a:ident] $thm:ident => $lhs))
  let eqns (name : Name) (binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) (lhs : Term)
      (body : MR) (eqLemma : Name := `eq_2) : CommandElabM Nat := do
    let ls := leaves body
    let eq2 := mkIdent (name ++ eqLemma)
    let mut k := 0
    for (path, leaf) in ls do
      k := k + 1
      let mut hyps : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
      let mut rules : Array (TSyntax ``Lean.Parser.Tactic.rwRule) := #[← `(Lean.Parser.Tactic.rwRule| $eq2:ident)]
      let mut j := 0
      for (c, pos) in path do
        j := j + 1
        let ct ← liftTermElabM c.render
        let h := mkIdent (Name.mkSimple s!"hc{j}")
        let ty ← if pos then pure ct else `(¬ $ct)
        hyps := hyps.push (← `(Lean.Parser.Term.bracketedBinderF| ($h : $ty)))
        rules := rules.push (← if pos then `(Lean.Parser.Tactic.rwRule| ite_eq_left $h:ident)
          else `(Lean.Parser.Tactic.rwRule| ite_eq_right $h:ident))
      let rhs ← liftTermElabM leaf.render
      let thm := mkIdent (name ++ Name.mkSimple s!"arm{k}")
      emit doTrace (← `(command|
        theorem $thm:ident $binders* $hyps* : $lhs = $rhs := by rw [$rules,*]))
      attrsOf thm lhs
    return k
  let mut nEqns := 0
  for fi in fis, b in bodies do
    let ps := fi.params.map mkIdent
    let pbs ← ps.mapM fun x => `(Lean.Parser.Term.bracketedBinderF| ($x : L.Word))
    let nBs := #[← `(Lean.Parser.Term.bracketedBinderF| ($nI : Nat))]
    let mBs := #[← `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent memIdent) : L.Mem))] ++ pbs
    let wbs := mpBinders ++ nBs ++ mBs
    if noFuel then
      let lhs ← `($(mkIdent fi.model) $mpArgs* $(mkIdent memIdent) $ps*)
      nEqns := nEqns + (← eqns fi.model (mpBinders ++ mBs) lhs b `eq_1)
    else
      let lhs ← `($(mkIdent fi.model) $mpArgs* ($nI + 1) $(mkIdent memIdent) $ps*)
      nEqns := nEqns + (← eqns fi.model wbs lhs b)
  for (kd, binders, _, pat, _, _) in kDefs do
    let resB ← match kd.binder with
      | 0 => pure #[← `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent kd.res) : L.Word)),
                    ← `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent mem1Ident) : L.Mem))]
      | 4 => pure #[← `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent kd.res) : List L.Word)),
                    ← `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent mem1Ident) : L.Mem))]
      | 1 => pure #[← `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent mem1Ident) : L.Mem))]
      | 2 => pure #[← `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent kd.res) : L.Word))]
      | _ => pure #[]
    let args : Array Term := mpArgs ++ (if kd.fuel then #[(nI : Term)] else #[]) ++ kd.caps.map (mkIdent ·) ++
      (if kd.capMem then #[(mkIdent memIdent : Term)] else #[])
    if kd.binder == 3 then
      let lhs ← `($(mkIdent kd.name) $args*)
      nEqns := nEqns + (← eqns kd.name binders lhs kd.body `eq_1)
    else
      let lhs ← `($(mkIdent kd.name) $args* $pat)
      nEqns := nEqns + (← eqns kd.name (binders ++ resB) lhs kd.body)
  -- the spec of the group
  let userNames : NameSet := bs.foldl (fun acc b => idents b.raw acc) {}
  let pName := mkIdent `p
  let s0 := mkIdent `s₀
  let mkConj (fuel : Term) : CommandElabM (Array Term) := fis.mapM fun fi => do
    let ps : Array Ident := fi.params.map fun x => mkIdent (if userNames.contains x then x.appendAfter "'" else x)
    let pbs ← ps.mapM fun x => `(Lean.Parser.Term.bracketedBinderF| ($x : L.Word))
    let W := mkIdent fi.model
    let Wapp ← if noFuel then `($W $mpArgs* (L.St.mem $s0) $ps*) else `($W $mpArgs* $fuel (L.St.mem $s0) $ps*)
    let post ← if fi.ro then
        `(fun r s' => L.LocEq s' $s0 ∧ L.St.mem s' = L.St.mem $s0 ∧
          $Wapp = Option.some (List.headD r 0))
      else
        `(fun r s' => L.LocEq s' $s0 ∧ $Wapp = Option.some (List.headD r 0, L.St.mem s'))
    let fstr := Syntax.mkStrLit fi.lname
    `(∀ ($s0 : L.St) $pbs*, Std.WP.Triple (L.invoke $pName (L.exec $pName $fuel) $fstr [$ps,*])
        (fun s => s = $s0) $post Lean.Order.top)
  let conj ← mkConj nI
  let stmt ← conj.pop.foldrM (init := conj.back!) fun c acc => `($c ∧ $acc)
  -- the proofs, as text: one step theorem per member, then the induction
  let pp (t : Syntax) : CommandElabM String := do
    return toString (← liftCoreM (PrettyPrinter.ppTerm ⟨t⟩))
  let k := fis.size
  let goals := String.intercalate ", " ((List.range k).map fun i => s!"?g{i+1}")
  let ihs := String.intercalate ", " ((List.range k).map fun i => s!"ih{i+1}")
  let attrsTxt := String.intercalate ", " ("lang_grind" :: (attrIds.toList.map (·.getId.toString)))
  let specsTxt ← specTs.toList.mapM (pp ·.raw)
  let extraTxt ← extraTs.toList.mapM (pp ·.raw)
  let hintsTxt ← hintTs.toList.mapM (pp ·.raw)
  let vcgOf (called : Array String) : String := String.intercalate ", "
    (["L.exec", "L.step", "L.evalE", "L.evalC", "L.evalArgs", "L.setLoc", "L.setLocs", "L.ld64"] ++
      extraTxt ++ ((specsTxt.zip callees.toList).filter (called.contains ·.2.1)).map (·.1) ++
      ((List.range k).filter (called.contains fis[·]!.lname)).map fun i => s!"ih{i+1}")
  let genTxt := match genN with | some g => s!"(gen := {g}) " | none => ""
  let hintsT := if hintsTxt.isEmpty then "" else s!"[{String.intercalate ", " hintsTxt}]"
  let parseTac (txt : String) : CommandElabM Syntax := do
    if doTrace then logInfo m!"{txt}"
    match Parser.runParserCategory (← getEnv) `tactic s!"({txt})" with
    | .ok t => pure (reposition t stx)
    | .error e => throwError "l_model: generated proof does not parse: {e}\n{txt}"
  let withHB (thm : TSyntax `command) : CommandElabM (TSyntax `command) := do
    match hbN with
    | some h => `(command| set_option maxHeartbeats $(Syntax.mkNumLit (toString h)):num in $thm)
    | none => pure thm
  -- the explicit binders, passed on to the steps
  let mut explicitArgs : Array String := #[]
  for b in bs do
    if let `(Lean.Parser.Term.bracketedBinderF| ($xs* : $_)) := b then
      for x in xs do explicitArgs := explicitArgs.push (toString x.raw.getId)
  let argsTxt := String.intercalate " " explicitArgs.toList
  let nB ← `(Lean.Parser.Term.bracketedBinderF| ($nI : Nat))
  let ihB ← `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent `ih) : $stmt))
  let conjS ← mkConj (← `($nI + 1))
  let mut zero := ""
  let mut steps : Array String := #[]
  for fi in fis, i in List.range k, called in calledBy, ci in conjS do
    let vcg := vcgOf called
    let lk ← pp fi.lookup.raw
    let pre := s!"intros; rw [L.invoke_eq _ ({lk})]; simp only [L.callFn, {fi.decl}]"
    let g := if k == 1 then "" else s!"case g{i+1} => "
    zero := zero ++ s!"\n    {g}({pre}; vcgen [L.exec] <;> grind)"
    let ihTxt := if k == 1 then "have ih1 := ih" else s!"obtain ⟨{ihs}⟩ := ih"
    let tac ← parseTac s!"{ihTxt}; {pre}; sym only [{attrsTxt}] => (vcgen [{vcg}] <;> finish {genTxt}{hintsT})"
    let stepName := mkIdent (specName.getId ++ Name.mkSimple s!"step{i+1}")
    emit doTrace (← withHB (← `(command|
      theorem $stepName:ident $bs* $nB:bracketedBinder $ihB:bracketedBinder : $ci := by $(⟨tac⟩):tactic)))
    steps := steps.push s!"{specName.getId}.step{i+1} {argsTxt} n ih"
  let refineTxt := if k == 1 then "" else s!"\n    refine ⟨{goals}⟩"
  let succTxt := if k == 1 then s!"exact {steps[0]!}" else s!"exact ⟨{String.intercalate ", " steps.toList}⟩"
  let tac ← parseTac s!"induction n with\n  | zero =>{refineTxt}{zero}\n  | succ n ih => {succTxt}"
  emit doTrace (← withHB (← `(command|
    $[$doc?:docComment]? theorem $specName:ident $bs* $nB:bracketedBinder : $stmt := by $(⟨tac⟩):tactic)))
  if doTrace then
    logInfo m!"l_model: {fis.size} model(s), {st.ks.size} continuation(s), {nEqns} guarded equation(s)"

end L.ModelGen
