module

public import ConAgua.L.Notation
public import ConAgua.L.Logic
public import ConAgua.L.ErrSpec
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
  `fW.k_g` (`| none => none | some (x, m₁) => …`) over the locals it reads, named after the
  callee `g` (`fW.k_g_2`, … for its later calls, in source order; after a loop `fW.k_loopᵢ`), so
  that a change elsewhere in the code does not rename it. The code after an `if`
  whose branches both fall through is a join point `fW.jᵢ` over the locals and the memory (no
  copy of it). Equal continuations of the group are shared;
* a function with **several results** (`return (a, b, …)`) gets a list model
  `Option (List Word × Mem)` (`return e` is `some ([e], m)`, the end of the body `some ([], m)`;
  `↦ fW list` forces it), or with `↦ fW tuple` a tuple model `Option (Word × … × Mem)` (the
  longest `return`'s arity, shorter ones padded with `0`);
* a **loop** (`while c { … }` in the `lfn`, or a spliced named block `⟪X⟫` that is one `while`)
  is a model of its own, `fW.loopᵢ n m x₁ …` (`exec p n` on the loop: `| 0 => none | n + 1 =>
  if c then … fW.loopᵢ n … else exit`; the enclosing code applies it at `n + 1`), over the locals
  live at its head. Its result is `(signal, outs…, memory)`: the signal (`Sig.normal`,
  `Sig.ret vs`) if the body has a `return`, the locals it assigns that the code after it reads,
  the memory unless read-only; the code after it is a continuation of that result. A loop with a
  `return` followed by the function's last statement (`return …`, `abort`) is **fused**: its model
  returns the function's result. Its spec `fW.loopᵢ.spec` (`⦃s = s₀⦄ exec p n X ⦃…⦄`, by
  induction, the model is the loop's meaning) is generated, and a `while` written in the `lfn`
  becomes the named block `fW.loopᵢ.stmt` (with `fW.lfn_eq : F = lfn … ⟪fW.loopᵢ.stmt⟫ …`).
  Named blocks without a loop are inlined;
* one **guarded equation** `fW.armᵢ` per non-`none` leaf of the `if` tree of each model, loop and
  continuation (the path's conditions as hypotheses, in order; on the negative side in their
  natural form: `a = b` for `¬ a ≠ b`, `a ≠ b` for `¬ a = b`, `p` for `¬ ¬ p`), each with a `grind_pattern` in the
  `grind` attributes; `fW.abortᵢ` for each `none` leaf, `fW.k_g.none` for each continuation (no
  patterns);
* the **spec** `⦃s = s₀⦄ invoke p (exec p n) "f" args ⦃LocEq s' s₀ ∧
  fW n s₀.mem args = some (r.headD 0, s'.mem); ⊤⦄` of every member (`some (r, s'.mem)` for a list
  model, `some (r.headD 0, r.tail.headD 0, …, s'.mem)` for a tuple model), as one conjunction
  over the group (`name`), a step theorem per member (`name.stepᵢ`: `vcgen` with the specs of the
  callees and loops that member calls, then `finish`) and the induction on the fuel.

The definitions come in dependency order: each strongly connected component of the reference
graph is one definition or one `mutual` block, well-founded on `(fuel, depth)` if it has a
continuation or a loop (models `(n, D)`, continuations `(n + 1, d)`, loops `(n, d)`; `LevelLeq.lean`
does this by hand), structural on the fuel if it has only models.

```
l_model liftGo_spec (p : Prog) (hp : LiftProg p)
  fns [(hp.get "lift_go") ↦ liftW, (hp.get "lift_app") ↦ liftAppW]
  specs [derB_spec p (hp.get "der_b") n, memoFindG_spec lfSch p _ (hp.get "lf_find") n]
  grind [arena_grind] fold [tierW, idxW] finish [tierW, idxW] gen 20 heartbeats 1000000
```

* `fns`: each entry is a proof of `p.lookup "f" = some F` (`F` a `def F : FunDecl := lfn …`: its
  text is read back from its module's file for the names of the locals and the leaf terms) and
  the name of the model; `ro`, `list`, `tuple` after the name (above).
* `specs`: the callees' specs, as terms over the binders and the fuel `n`. A callee's model is read
  off its post: `F = some (r.headD 0, s'.mem)` (effectful), `r.headD 0 = F₀ ∧ r.tail.headD 0 = F₁ …`
  with the memory unchanged (pure), `r ≠ [] ∧ r = F` (a list of results; `F = []` becomes `none`
  unless the callee is listed in `noguard`), `F = some s'.mem` (memory only),
  `G ∧ s'.mem = F` (memory only, total; `¬ G` becomes `none`), `F = some (r.headD 0)` with the
  memory unchanged (read-only), `F = some (r, s'.mem)` (several results and the memory: the
  code after the call is a continuation over `some (r, m₁)`, its results `r.headD 0`,
  `r.tail.headD 0`, …), `F = some r` (several results, read-only), `F = some (r.headD 0,
  r.tail.headD 0, …[, s'.mem])` (a tuple: a continuation over `some (r₀, r₁, …, m₁)`). A spec for
  any argument list (`invoke p (exec p n) "f" vs`, `callW_spec p n "f"`) applies to every call.
  A member of the group listed here is called through its spec, not as its model (a recursive
  call stays `callW p n "f" …`; also lets a loop call its own function). A conjunct
  `r = [r.headD 0, …]` (the result's length) is ignored.
* `fold`: named functions whose bodies are folded back into the model: word arithmetic
  (`tierW h = (h >>> 27) &&& 1`) or a result of a list callee (`lvG m p = (lvNodeW m p).headD 0`).
* `bind c`: the code after a call with several results is an inline continuation
  `c (call) fun ρᵢ μᵢ => …` instead of a named one (`bind ntBW`: the hand models of `Decl*`).
* `extra`: more lemmas for `vcgen` (the default is `exec, step, evalE, evalC, evalArgs, setLoc,
  setLocs, ld64, st64, setG`); `finish`, `gen`, `instances`: the hints and configuration of
  `finish`; `sym "…"`: options of `sym`; `simp [lemmas]`: prove each step by `vcgen` and
  `simp_all` over the models' equations, the locals' lemmas and `lemmas` instead of
  `sym … finish` (cheaper for many paths and small functions); `heartbeats`: per step theorem; `trace`: log the
  generated commands.
* `errors`: (pass `L.Arena.ld64_rdW_specE` in `extra`: word loads are not unfolded) the models keep the errors (the verdict proofs, `Arena/Verdict.lean`). A model is
  `Except L.Err …` (`.ok` for `some`); an `abort R` is `.error (.abort R)` (`abort` is code `0`);
  a continuation passes a callee's error on (`| .error ε => .error ε`, its equation `k.none`); a
  model at fuel `0` is `.error .outOfFuel`; every abort leaf has a guarded equation `fW.abortᵢ`
  with patterns. A callee without a spec is called through its whole run, `callE p n "f" [..] m`
  (`callE_spec`), so a plain `l_model … errors` needs no `specs` (and the binder `p`). The spec's
  exceptional post is `fun ε => ε.code ≠ 0 → fW n s₀.mem args = .error ε`: an error with a code
  (an abort) is the model's; out of bounds, where the model reads a default, has code `0` and is
  left out.

Not supported (an error names the statement or the callee): nested loops, a loop that calls a
member of its own group (unless through its spec, above), byte stores, `FunDecl`s with parameters (`memoFindG S`) and models with
Lean parameters, members that only change the memory. Array bounds are not modelled: a load is
`rdW` (`0` out of bounds), a store is `Mem.set64` (no change out of bounds); where L aborts, the
spec says nothing.
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
  /-- `[a₀, a₁, …]` (the results of a model with several results) -/
  | list (xs : Array MT)
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
  /-- `some (v₁, …, vₖ)` (a loop's result) -/
  | tup (vs : Array MT)
  /-- `errors` mode: `.error (.abort k)`, an `abort` with the code `k` -/
  | err (code : MT)
  deriving Inhabited

meta def mkNum (n : Nat) : Term := Syntax.mkNumLit (toString n)

meta partial def MT.render : MT → MetaM Term
  | .lit n => pure (mkNum n)
  | .hole i => pure (mkIdent (Name.mkSimple s!"__hole{i}"))
  | .raw t => `(($t))
  | .list xs => do
    let xs ← xs.mapM MT.render
    `([$xs,*])
  | .app f args => do
    let as ← args.mapM MT.render
    if as.isEmpty then pure (mkIdent f) else `(($(mkIdent f) $as*))
  | .rd mem arr i => do `(($(mkIdent `rdW) (L.Mem.arr64 $(← mem.render) $arr) $(← i.render)))
  | .rd8 mem arr i => do
    `(((L.Mem.arr8 $(← mem.render) $arr)[($(← i.render)).toNat]?.getD 0).toUInt64)
  | .op o a b => do
    -- numerals as words (the elaborator does not always find the type through `&&&`, `>>>`)
    let ra (x : MT) : MetaM Term := match x with
      | .lit n => `(($(mkNum n) : L.Word))
      | x => x.render
    let a ← ra a
    let b ← ra b
    match o with
    | "+" => `(($a + $b))
    | "-" => `(($a - $b))
    | "*" => `(($a * $b))
    | "&&&" => `(($a &&& $b : L.Word))
    | "|||" => `(($a ||| $b : L.Word))
    | "^^^" => `(($a ^^^ $b : L.Word))
    | "<<<" => `(($a <<< $b : L.Word))
    | ">>>" => `(($a >>> $b : L.Word))
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

/-- `exc`: the `errors` mode's models (`Except L.Err`, `ok` for `some`). -/
meta partial def MR.render (r : MR) (exc : Bool := false) : MetaM Term := do
  let okC : Ident := mkIdent (if exc then `Except.ok else `Option.some)
  match r with
  | .none => if exc then throwError "l_model: a failure without an error in `errors` mode" else `(Option.none)
  | .err k => do `(Except.error (L.Err.abort $(← k.render)))
  | .some v mem => do `($okC ($(← v.render), $(← mem.render)))
  | .someW v => do `($okC $(← v.render))
  | .ite c t e => do
    let c ← c.render
    let t ← t.render exc
    let e ← e.render exc
    `(if $c then $t else $e)
  | .tail t => t.render
  | .tup vs => do
    let vs ← vs.mapM MT.render
    match vs.size with
    | 0 => `($okC ())
    | 1 => `($okC $(vs[0]!))
    | _ => `($okC ($(vs[0]!), $(vs.extract 1 vs.size),*))

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
  | .list as, .list bs => as.size == bs.size && (as.zip bs).all fun (a, b) => a.beq b
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
  /-- `F : Option (List Word)`, memory unchanged: several results, read-only -/
  | roL (t : Term)
  /-- `F : Option (Word × … × Mem)`: `k` results and the memory -/
  | effT (t : Term) (k : Nat)
  /-- `F : Option (Word × …)`: `k` results, memory unchanged -/
  | roT (t : Term) (k : Nat)
  deriving Inhabited

meta structure Callee where
  kind : CKind
  deriving Inhabited

meta def substT (t : Term) (mem : Term) (args : Array Term) : MetaM Term := do
  let r ← t.raw.replaceM fun s => do
    if let .ident _ _ n _ := s then
      if n == `__m then return some mem.raw
      if n == `__al then return some (← `([$args,*])).raw
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

/-- The components of a tuple `(c₀, c₁, …)`. -/
meta partial def tupComps (v : Lean.Expr) : List Lean.Expr :=
  match v.consumeMData.getAppFnArgs with
  | (``Prod.mk, #[_, _, v1, v2]) => v1 :: tupComps v2
  | _ => [v]

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
    -- the arguments: a list literal, or a variable (a spec for any argument list, `callF_spec`)
    let (fname, callArgs, argList?) ← match x.getAppFnArgs with
      | (``L.invoke, #[_, _, f, vs]) =>
        let some f := strLit? f | throwError "l_model: callee name not a literal in {x}"
        match vs.listLit? with
        | some vs => pure (f, vs.2.toArray, none)
        | none =>
          unless vs.isFVar do throwError "l_model: arguments not a list literal in {x}"
          pure (f, #[], some vs)
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
    withLocalDeclD `__al (← mkAppM ``List #[mkConst ``L.Word]) fun alvar => do
    let argVars := avars
    -- replace `s₀.mem` by `__m` and the argument variables by `__aᵢ`
    let repl (e : Lean.Expr) : Lean.Expr := Id.run do
      let mut e := e.replace fun t => if t == memE then some mvar else none
      for i in [0:callArgs.size] do
        e := e.replace fun t => if t == callArgs[i]! then some argVars[i]! else none
      if let some al := argList? then
        e := e.replace fun t => if t == al then some alvar else none
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
    let mut roL : Option Lean.Expr := none
    let mut tupF : Option (Lean.Expr × Nat × Bool) := none
    let mut guards : Array Lean.Expr := #[]
    for c in cs do
      let c := c.consumeMData
      match c.getAppFnArgs with
      | (``L.LocEq, _) => pure ()
      | (``Eq, #[_, a, b]) =>
        if a == s' && b == s0 then memSame := true
        else if a == memS' && b == memE then memSame := true
        else if a == memS' then memTot := some b
        else if a == r then
          -- `r = [r.headD 0, r.tail.headD 0, …]` (the result's length) says nothing for the model
          let shape := match b.listLit? with
            | some (_, es) => (es.toArray.mapIdx fun i e => resIdx r e == some i).all id
            | none => false
          unless shape do listF := some b
        else if let some i := resIdx r a then pures := pures.push (i, b)
        else
          -- `(c₀, c₁, …)`
          let tupleOf (v : Lean.Expr) : Option (Nat × Bool) :=
            let cs := tupComps v
            let (rs, mem) := if cs.getLast? == some memS' then (cs.dropLast, true) else (cs, false)
            if rs.length ≥ 2 && (List.range rs.length).all (fun i => resIdx r rs[i]! == some i) then
              some (rs.length, mem)
            else none
          -- `some v`, or `.ok v` (a model with errors, `errors` mode; `callE_spec`)
          let someV? : Option Lean.Expr := match b.getAppFnArgs with
            | (``Option.some, #[_, v]) => some v
            | (``Except.ok, #[_, _, v]) => some v
            | _ => none
          match someV? with
          | some v =>
            if let some (k, withMem) := tupleOf v then tupF := some (a, k, withMem) else
            match v.getAppFnArgs with
            | (``Prod.mk, #[_, _, v1, v2]) =>
              if resIdx r v1 == some 0 && v2 == memS' then eff := some a
              else if v1 == r && v2 == memS' then effL := some a
              else throwError "l_model: unsupported post conjunct {c}"
            | _ =>
              if v == memS' then memOpt := some a
              else if resIdx r v == some 0 then ro := some a
              else if v == r then roL := some a
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
    let kind ← if let some (e, k, withMem) := tupF then do
        unless eff.isNone && memOpt.isNone && memTot.isNone && ro.isNone && listF.isNone && effL.isNone && roL.isNone do
          throwError "l_model: callee {fname}: ambiguous post"
        if withMem then pure (CKind.effT (← delabT e) k)
        else
          unless memSame do throwError "l_model: read-only callee {fname} must keep the memory"
          pure (CKind.roT (← delabT e) k)
      else if let some e := roL then do
        unless eff.isNone && memOpt.isNone && memTot.isNone && ro.isNone && listF.isNone && effL.isNone do
          throwError "l_model: callee {fname}: ambiguous post"
        unless memSame do throwError "l_model: read-only callee {fname} must keep the memory"
        pure (CKind.roL (← delabT e))
      else if let some e := effL then do
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
meta def declSyntax (c : Name) (kw : String := "lfn") : TermElabM Syntax := do
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
  -- the text after the first `:=` that is followed (after white space) by `kw`
  let parts := txt.splitOn ":="
  let mut pos := parts.head!.utf8ByteSize
  let mut found : Option Nat := none
  for part in parts.tail do
    pos := pos + ":=".length
    let body := String.ofList (part.toList.dropWhile Char.isWhitespace)
    if body.startsWith s!"{kw}(" ||
        (body.startsWith kw && ((body.drop kw.length).toString.front).isWhitespace) then
      found := some (pos + (part.utf8ByteSize - body.utf8ByteSize))
      break
    pos := pos + part.utf8ByteSize
  let some start := found | throwError "l_model: {c} is not `… := {kw} …`"
  let i := String.Pos.Raw.extract txt ⟨start⟩ ⟨txt.utf8ByteSize⟩
  let off := p1.byteIdx + start
  match Parser.runParserCategory (← getEnv) `term i with
  | .ok stx => return if here then shiftPos stx off else stx
  | .error e => throwError "l_model: cannot re-parse the L text of {c}: {e}"

meta def lfnSyntax (c : Name) : CommandElabM Syntax := liftTermElabM (declSyntax c)

/-! ## Translation -/

/-- A continuation definition. -/
meta structure KDef where
  name : Name
  fuel : Bool
  caps : Array Name
  capMem : Bool
  /-- `0`: `some (x, m₁)`; `1`: `some m₁`; `2`: `some x`; `3`: a join point; `4`: `some (r, m₁)`
  with `r : List Word` (a callee with several results); `6`: `some r` with `r : List Word` (a
  read-only callee with several results) -/
  binder : Nat
  res : Name
  body : MR
  key : String
  /-- the continuations its body applies -/
  refs : Array Name
  /-- binder `5` (after a loop): the loop's results (`lsig`: its signal first; `lro`: no memory) -/
  lres : Array Name := #[]
  lsig : Bool := false
  lro : Bool := false
  /-- inside a loop's body: the loop (the definition returns the loop's result) -/
  inLoop : Option Name := none
  deriving Inhabited

/-- A loop (binder `7` in `GenState.ks`): `name n m x₁ … xₖ` runs `exec p n` on the loop
statement from the locals `params` (indices into the function's locals). -/
meta structure LoopMeta where
  name : Name
  model : Name
  /-- the loop statement's constant (a named block, or generated: `name.stmt`) -/
  stmt : Name
  /-- for a `while` written in the `lfn`: its syntax (it becomes `name.stmt`) -/
  direct : Option Syntax
  params : Array Nat
  outs : Array Nat
  /-- the locals the code after the loop reads that the loop does not assign -/
  frames : Array Nat
  sig : Bool
  ro : Bool
  called : Array String
  /-- fused: the code after the loop is `return (e₀, …)` (its results over the final state `s'`)
  or `abort` (`#[]`, `abortRest`); the loop's model returns the function's result -/
  fusedD : Option (Array Term) := none
  abortRest : Bool := false
  deriving Inhabited

/-- Inside a loop's body: where `break`, `return` and the end of the body go. -/
meta structure LoopInfo where
  name : Name
  params : Array Nat
  outs : Array Nat
  sig : Bool
  /-- fused: `return` is the function's result, the exit runs these statements (the function's
  last) -/
  exitStmts : Option (List (TSyntax `lstmt)) := none
  deriving Inhabited

meta structure GenState where
  ks : Array KDef := #[]
  loops : Array LoopMeta := #[]
  /-- the loops called by the function (or loop) being translated -/
  loopsCalled : Array Name := #[]
  dups : Nat := 0
  /-- the binders of the inline continuations (`bind`) so far -/
  lams : Nat := 0
  base : Name := .anonymous
  /-- the functions called by the function being translated -/
  called : Array String := #[]
  /-- the callee of the call being translated (names its continuation `fW.k_f`) -/
  callHint : String := ""
  /-- the next pre-order number of a continuation (`provName`) -/
  seq : Nat := 0
  /-- `errors` mode: the callees without a spec, called through `callE_spec p n "f"` -/
  autoE : Array String := #[]
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
  /-- the model returns `List Word` (a function with several results) -/
  multi : Bool := false
  /-- the model returns a tuple of this many words (`0`: not a tuple model) -/
  tup : Nat := 0
  /-- where the end of the statement list goes (a join point), if not to the function's end -/
  ft : Option Join := none
  /-- the models' Lean parameters (`Env.mps`): L names equal to one get a prime -/
  clash : Array Name := #[]
  /-- the loop whose body this is -/
  loop : Option LoopInfo := none

meta def memIdent : Name := `m
meta def mem1Ident : Name := `m₁

abbrev GenM := StateRefT GenState TermElabM

/-- A provisional continuation name `base.stem.i` (`i` in source order of creation); `finalNames`
turns them into `base.stem`, `base.stem_2`, … (join points `base.j1`, `base.j2`, …). -/
meta def provName (stem : String) (seq : Nat) : GenM Name := do
  return Name.mkNum ((← get).base ++ Name.mkSimple stem) seq

meta structure Env where
  /-- the members: L name, model, read-only, several results (a list), tuple arity -/
  group : Array (String × Name × Bool × Bool × Nat)
  callees : Array (String × Callee)
  folds : Array Fold
  /-- list callees whose `r ≠ []` does not become a `none` branch -/
  noguard : Array String := #[]
  /-- the models' Lean parameters: the command's explicit binders that the callees' models
  mention (`p` in `callW p n "f" [..] m`); every model and continuation takes them first -/
  mps : Array Name := #[]
  /-- the named blocks spliced (`⟪X⟫`): the key of `X`, its constant, its statements, whether
  it is a single `while` -/
  blocks : Array (String × Name × List (TSyntax `lstmt) × Bool) := #[]
  /-- `bind c`: the code after a call with several results is an inline continuation
  `c (call) fun ρᵢ μᵢ => …` (`ntBW`, the hand models' bind), not a named one -/
  bind : Option Name := none
  /-- `errors`: the models are `Except L.Err` (an `abort`'s code kept, a callee's error passed
  on), and a callee without a spec is called through `callE_spec p n "f"` -/
  exc : Bool := false

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
    let fI := mkIdentFrom f (r.getId ++ f.getId)
    let ad ← `(L.Record.ad $r $(← (← transE E ctx i).render) $fI)
    pure (.rd ctx.mem (← `(L.tierA (L.Record.arr $r) $(← (← transE E ctx t).render))) (.raw ad))
  | `(lexpr| $a:ident⟨$t:lexpr⟩[$i:lexpr]) => do
    pure (.rd ctx.mem (← `(L.tierA $a $(← (← transE E ctx t).render))) (← transE E ctx i))
  | `(lexpr| len($a:ident⟨$t:lexpr⟩)) => do
    pure (.raw (← `(L.Mem.len64 $(← ctx.mem.render) (L.tierA $a $(← (← transE E ctx t).render)))))
  | `(lexpr| $r:ident⟨$t:lexpr, $i:lexpr⟩.$f:ident) => do
    let fI ← fieldNum (mkIdentFrom f (r.getId ++ f.getId))
    pure (.raw (← `($(mkIdent `L.Arena.tfld) $(← ctx.mem.render) $r $(← (← transE E ctx t).render)
      $(← (← transE E ctx i).render) $fI)))
  | `(lexpr| $r:ident⟨$t:lexpr, $i:lexpr⟩) => do
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
    | `(lstmt| abort) | `(lstmt| abort $_:ident) => true
    | `(lstmt| if $_:lcond { $s;* } else { $t;* }) =>
      terminates s.getElems.toList && terminates t.getElems.toList
    | s => s.raw.isOfKind ``L.Notation.lfail

/-- All identifiers in a syntax tree. -/
meta partial def idents (s : Syntax) (acc : NameSet := {}) : NameSet :=
  match s with
  | .ident _ _ n _ => acc.insert n
  | .node _ _ args => args.foldl (fun acc a => idents a acc) acc
  | _ => acc

meta def setEnv (ctx : Ctx) (k : Nat) (v : MT) : Ctx := { ctx with env := ctx.env.set! k v }

/-- The model's leaf for `return (v₀, v₁, …)` (`vs = #[]`: falling off the end). -/
meta def Ctx.ret (ctx : Ctx) (vs : Array MT) : MR :=
  if ctx.tup > 0 then
    let vs := (List.range ctx.tup).toArray.map fun i => vs[i]?.getD (.lit 0)
    .tup (vs ++ (if ctx.ro then #[] else #[ctx.mem]))
  else
  let v := if ctx.multi then MT.list vs else vs[0]?.getD (.lit 0)
  if ctx.ro then .someW v else .some v ctx.mem

/-- The most results a `return` of a statement list has. -/
meta partial def retArity (s : Syntax) : Nat :=
  let here : Nat := match (⟨s⟩ : TSyntax `lstmt) with
    | `(lstmt| return ($_:lexpr, $es:lexpr,*)) => es.getElems.size + 1
    | `(lstmt| return $_:lexpr) => 1
    | _ => 0
  s.getArgs.foldl (fun k a => max k (retArity a)) here

/-- Does a statement list contain `return (a, b, …)` (several results)? -/
meta def hasMultiRet (s : Syntax) : Bool := retArity s ≥ 2

/-- `i` in subscript digits. -/
meta def subDigits (i : Nat) : String :=
  String.ofList ((toString i).toList.map fun c => Char.ofNat (c.toNat - '0'.toNat + 0x2080))

/-- A loop's leaf: its result `(signal, outs…, memory)` (the signal only if the loop has a
`return`, the memory only if the model writes). -/
meta def loopLeaf (ctx : Ctx) (L : LoopInfo) (sig : Option MT) : MR :=
  let sigV : Array MT := if L.sig then #[sig.getD (.raw (mkIdent `L.Sig.normal))] else #[]
  .tup (sigV ++ L.outs.map (ctx.env[·]!) ++ (if ctx.ro then #[] else #[ctx.mem]))

/-- `return (v₀, …)`: the function's result, or inside a loop the loop's result `Sig.ret […]`. -/
meta def retLeaf (ctx : Ctx) (vs : Array MT) : GenM MR := do
  match ctx.loop with
  | some L =>
    if L.exitStmts.isSome then return ctx.ret vs
    let l ← (MT.list vs).render
    return loopLeaf ctx L (some (.raw (← `(L.Sig.ret $l))))
  | none => return ctx.ret vs

/-- The function's result for a list of results `l` (a loop's `Sig.retVal r`). -/
meta def Ctx.retList (ctx : Ctx) (l : Term) : GenM MR := do
  if ctx.tup > 0 then
    let mut vs : Array MT := #[]
    for i in [0:ctx.tup] do
      let mut e : Term := l
      for _ in [0:i] do e ← `(List.tail $e)
      vs := vs.push (.raw (← `(List.headD $e 0)))
    return ctx.ret vs
  let hd ← `(List.headD $l 0)
  let v : MT := if ctx.multi then .raw l else .raw hd
  return if ctx.ro then .someW v else .some v ctx.mem

/-! ### Syntactic facts about statement lists (for loops) -/

/-- The locals (indices) a statement list assigns, at any depth. -/
meta partial def assignedIn (ctx : Ctx) (s : Syntax) (acc : Array Nat := #[]) : Array Nat :=
  let add (acc : Array Nat) (x : Ident) : Array Nat :=
    match ctx.idx x with
    | some k => if acc.contains k then acc else acc.push k
    | none => acc
  let acc := match (⟨s⟩ : TSyntax `lstmt) with
    | `(lstmt| $x:ident := call $_:ident($_,*)) => add acc x
    | `(lstmt| ($x:ident, $xs:ident,* ) := call $_:ident($_,*)) => xs.getElems.foldl add (add acc x)
    | `(lstmt| $x:ident := $_:lexpr) => add acc x
    | `(lstmt| $x:ident += $_:lexpr) => add acc x
    | `(lstmt| $x:ident -= $_:lexpr) => add acc x
    | _ => acc
  s.getArgs.foldl (fun acc a => assignedIn ctx a acc) acc

/-- Replace the first-found nodes `f` maps to something. -/
meta partial def replaceStx (s : Syntax) (f : Syntax → Option Syntax) : Syntax :=
  match f s with
  | some t => t
  | none => match s with
    | .node i k args => .node i k (args.map (replaceStx · f))
    | s => s

/-- The named blocks spliced as statements (`⟪X⟫`). -/
meta partial def splices (s : Syntax) (acc : Array Ident := #[]) : Array Ident :=
  let acc := match (⟨s⟩ : TSyntax `lstmt) with
    | `(lstmt| ⟪$t⟫) => match t with
      | `($x:ident) => acc.push x
      | _ => acc
    | _ => acc
  s.getArgs.foldl (fun acc a => splices a acc) acc

/-- Does a statement list contain `return`? -/
meta partial def hasReturn (s : Syntax) : Bool :=
  let here : Bool := match (⟨s⟩ : TSyntax `lstmt) with
    | `(lstmt| return $_:lexpr) => true
    | `(lstmt| return ($_:lexpr, $_:lexpr,*)) => true
    | _ => false
  here || s.getArgs.any hasReturn

/-- The locals (indices) an expression or condition reads. -/
meta def usesOf (ctx : Ctx) (s : Syntax) : Array Nat :=
  (idents s).toList.filterMap (fun x => ctx.names.idxOf? (sanitize x ctx.clash)) |>.toArray

meta def unionN (a b : Array Nat) : Array Nat := b.foldl (fun a x => if a.contains x then a else a.push x) a

/-- The locals live before a statement list, given those live after it (`out`) and at a `break`
(`brk`): read before they are written. -/
meta partial def liveS (E : Env) (ctx : Ctx) (ss : List (TSyntax `lstmt)) (out brk : Array Nat) :
    Array Nat :=
  match ss with
  | [] => out
  | s :: rest =>
    let after := liveS E ctx rest out brk
    let kill (xs : Array Ident) (l : Array Nat) : Array Nat :=
      let ks := xs.filterMap ctx.idx
      l.filter (!ks.contains ·)
    let blk (b : TSyntax `lblock) : List (TSyntax `lstmt) := match b with
      | `(lblock| { $ss;* }) => ss.getElems.toList
      | _ => []
    match s with
    | `(lstmt| $x:ident := call $_:ident($args,*)) =>
      unionN (kill #[x] after) (usesOf ctx (mkNullNode (args.getElems.map (·.raw))))
    | `(lstmt| ($x:ident, $xs:ident,* ) := call $_:ident($args,*)) =>
      unionN (kill (#[x] ++ xs.getElems) after) (usesOf ctx (mkNullNode (args.getElems.map (·.raw))))
    | `(lstmt| $x:ident := $e:lexpr) => unionN (kill #[x] after) (usesOf ctx e)
    | `(lstmt| if $c:lcond $b:lblock) =>
      unionN (unionN (usesOf ctx c) (liveS E ctx (blk b) after brk)) after
    | `(lstmt| if $c:lcond $b:lblock else $t:lblock) =>
      unionN (usesOf ctx c) (unionN (liveS E ctx (blk b) after brk) (liveS E ctx (blk t) after brk))
    | `(lstmt| if $c:lcond $b:lblock else $t:lstmt) =>
      unionN (usesOf ctx c) (unionN (liveS E ctx (blk b) after brk) (liveS E ctx [t] after brk))
    | `(lstmt| while $c:lcond $b:lblock) => loopLive ctx c (blk b) after
    | `(lstmt| break) => brk
    | `(lstmt| return $e:lexpr) => usesOf ctx e
    | `(lstmt| return ($e:lexpr, $es:lexpr,*)) => unionN (usesOf ctx e) (usesOf ctx (mkNullNode (es.getElems.map (·.raw))))
    | `(lstmt| abort) | `(lstmt| abort $_:ident) => #[]
    | `(lstmt| ⟪$t⟫) =>
      match E.blocks.find? (·.1 == key t) with
      | some (_, _, ss, _) => liveS E ctx (ss ++ rest) out brk
      | none => unionN after (usesOf ctx s)
    -- `x += e`, stores, `skip`: read everything they mention
    | _ => unionN after (usesOf ctx s)
where
  /-- The locals live at a loop's head: a fixpoint (the end of the body goes back to the head). -/
  loopLive (ctx : Ctx) (c : TSyntax `lcond) (body : List (TSyntax `lstmt)) (out : Array Nat) :
      Array Nat := Id.run do
    let mut h := unionN (usesOf ctx c) out
    for _ in [0:ctx.names.size + 2] do
      let h' := unionN h (liveS E ctx body h out)
      if h'.size == h.size then return h
      h := h'
    return h

mutual
meta partial def transS (E : Env) (ctx : Ctx) : List (TSyntax `lstmt) → GenM MR
  | [] => match ctx.ft with
    | some j => pure (.tail (.app j.name (E.mps.map (fun x => MT.raw (mkIdent x)) ++ (if j.fuel then #[MT.raw (mkIdent `n)] else #[]) ++
        j.caps.map (ctx.env[·]!) ++ (if j.capMem then #[ctx.mem] else #[]))))
    | none =>
      match ctx.loop with
      | some L =>
        -- the end of a loop's body: the next iteration
        pure (.tail (.app L.name (E.mps.map (fun x => MT.raw (mkIdent x)) ++ #[MT.raw (mkIdent `n)] ++
          #[ctx.mem] ++ L.params.map (ctx.env[·]!))))
      | none => pure (ctx.ret #[])
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
    | `(lstmt| $r:ident⟨$t:lexpr⟩[$i:lexpr].$f:ident := $e:lexpr) => do
      let fI := mkIdentFrom f (r.getId ++ f.getId)
      let ad ← `(L.Record.ad $r $(← (← transE E ctx i).render) $fI)
      store (← `(L.tierA (L.Record.arr $r) $(← (← transE E ctx t).render))) (.raw ad) e
    | `(lstmt| $a:ident⟨$t:lexpr⟩[$i:lexpr] := $e:lexpr) => do
      store (← `(L.tierA $a $(← (← transE E ctx t).render))) (← transE E ctx i) e
    | `(lstmt| $a:ident[$i:lexpr] := $e:lexpr) => do
      let (arr, k) ← splitArr a
      unless k == "u64" do throwErrorAt s "l_model: byte stores are not supported"
      store arr (← transE E ctx i) e
    | `(lstmt| if $c:lcond $b:lblock) => ite c (← blockStmts b) []
    | `(lstmt| if $c:lcond $b:lblock else $t:lblock) => ite c (← blockStmts b) (← blockStmts t)
    | `(lstmt| if $c:lcond $b:lblock else $t:lstmt) => ite c (← blockStmts b) [t]
    | `(lstmt| return $e:lexpr) => do
      retLeaf ctx #[← transE E ctx e]
    | `(lstmt| return ($e:lexpr, $es:lexpr,*)) => do
      unless ctx.multi || ctx.tup > 0 do throwErrorAt s "l_model: several results in a model with one"
      retLeaf ctx (← (#[e] ++ es.getElems).mapM (transE E ctx))
    | `(lstmt| break) => do
      match ctx.loop with
      | some L =>
        match L.exitStmts with
        | some ex => transS E { ctx with ft := none } ex
        | none => return loopLeaf ctx L none
      | none => throwErrorAt s "l_model: `break` outside a loop"
    | `(lstmt| while $c:lcond $b:lblock) => do
      transLoop E ctx none (some s) c (← blockStmts b) rest
    | `(lstmt| ⟪$t⟫) => do
      match E.blocks.find? (·.1 == key t) with
      | some (_, c, ss, isLoop) =>
        if isLoop then
          let some w := ss.head? | throwErrorAt s "l_model: empty block"
          let `(lstmt| while $c':lcond $b:lblock) := w | throwErrorAt s "l_model: not a loop block"
          transLoop E ctx (some c) none c' (← blockStmts b) rest
        else transS E ctx (ss ++ rest)
      | none => throwErrorAt s "l_model: unknown named block"
    | `(lstmt| abort) => pure (if E.exc then .err (.lit 0) else .none)
    | `(lstmt| abort $r:ident) => pure (if E.exc then .err (.raw r) else .none)
    | `(lstmt| skip) => transS E ctx rest
    | _ =>
      if s.raw.isOfKind ``L.Notation.lfail then
        pure (if E.exc then .err (.raw ⟨s.raw[1]⟩) else .none)
      else throwErrorAt s "l_model: unsupported L statement"

meta partial def transCall (E : Env) (ctx : Ctx) (xs : Array Ident) (f : Ident)
    (args : Array (TSyntax `lexpr)) (rest : List (TSyntax `lstmt)) : GenM MR := do
  let fname := f.getId.toString
  modify fun st => { st with called := st.called.push fname, callHint := fname }
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
        | `(lexpr| $y:ident) => !ctx.multi && ctx.tup == 0 && xs.size == 1 && y.getId == xs[0]!.getId
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
  -- a member of the group with a spec in `specs` is called through that spec (`callW_spec p n
  -- "f"`: the self-call stays a `callW` in the model, as in hand models whose refinements do
  -- induction over `callW`)
  let viaSpec := E.callees.any (·.1 == fname)
  if let some (_, w, wro, wlist, wtup) := (if viaSpec then none else E.group.find? (·.1 == fname)) then
    if ctx.loop.isSome then
      throwErrorAt f "l_model: a loop calls a member of the group (not supported)"
    let t ← `($(mkIdent w) $(E.mps.map (fun x => (mkIdent x : Term)))* $(mkIdent `n) $memT $argsT*)
    if wtup > 0 then
      if ctx.ro && !wro then throwErrorAt f "l_model: a read-only model calls an effectful one"
      return ← mkK E ctx 5 none xk (.raw t) rest wtup wro
    if wro && wlist then return ← mkK E ctx 6 none xk (.raw t) rest
    if wlist then
      if ctx.ro then throwErrorAt f "l_model: a read-only model calls an effectful one"
      return ← bindK E ctx xk (.raw t) rest
    if wro then
      if ctx.ro && isTail then return .tail (.raw t)
      return ← mkK E ctx 2 xk[0]? xk (.raw t) rest
    if ctx.ro then throwErrorAt f "l_model: a read-only model calls an effectful one"
    return ← effK (.raw t) isTail xk
  let c ← match E.callees.find? (·.1 == fname) with
    | some (_, c) => pure c
    | none =>
      unless E.exc do throwErrorAt f "l_model: no spec given for the callee {fname}"
      -- `errors` mode: the call's whole run, `callE p n "f" [args] m` (`callE_spec`)
      unless (← get).autoE.contains fname do
        modify fun st => { st with autoE := st.autoE.push fname }
      pure ({ kind := .effL (← `(L.callE $(mkIdent `p) $(mkIdent `n) $(Syntax.mkStrLit fname) $(mkIdent `__al) $(mkIdent `__m))) } : Callee)
  if E.exc then
    match c.kind with
    | .pure .. | .list .. | .memOpt .. | .memTot .. =>
      throwErrorAt f "l_model: in `errors` mode the callee {fname} needs a spec with an error post (`callE_spec`)"
    | _ => pure ()
  match c.kind with
  | .eff t =>
    if ctx.ro then throwErrorAt f "l_model: a read-only model calls an effectful one"
    effK (.raw (← substT t memT argsT)) isTail xk
  | .effL t =>
    if ctx.ro then throwErrorAt f "l_model: a read-only model calls an effectful one"
    bindK E ctx xk (.raw (← substT t memT argsT)) rest
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
  | .roL t => mkK E ctx 6 none xk (.raw (← substT t memT argsT)) rest
  | .effT t k =>
    if ctx.ro then throwErrorAt f "l_model: a read-only model calls an effectful one"
    mkK E ctx 5 none xk (.raw (← substT t memT argsT)) rest k false
  | .roT t k => mkK E ctx 5 none xk (.raw (← substT t memT argsT)) rest k true

/-- Make the continuation of a call: the rest of the code, as a definition over the locals it
reads. -/
meta partial def mkK (E : Env) (ctx : Ctx) (binder : Nat) (res : Option Nat) (xk : Array Nat)
    (callT : MT) (rest : List (TSyntax `lstmt)) (tupN : Nat := 0) (tupRo : Bool := false) : GenM MR := do
  let hint := (← get).callHint
  let seq ← modifyGet fun st => (st.seq, { st with seq := st.seq + 1 })
  -- binder `5` (a callee with `tupN` results): `some (r₀, r₁, …, m₁)`
  let lres : Array Name := (List.range tupN).toArray.map fun i => Name.mkSimple s!"r{subDigits i}"
  let resName := match res with
    | some k => ctx.names[k]!
    | none => `r
  -- inside: every local is its own name, the result is the binder, the memory is `m₁`
  -- (or the captured `m`)
  let mut env : Array MT := ctx.names.map fun n => .raw (mkIdent n)
  for i in [0:xk.size] do
    if binder == 5 then
      env := env.set! xk[i]! (if h : i < lres.size then .raw (mkIdent lres[i]) else .lit 0)
    else if binder == 4 || binder == 6 then
      -- result `i` of the list: `(r.tail….tail).headD 0`
      let mut e : Term := mkIdent resName
      for _ in [0:i] do e ← `(List.tail $e)
      env := env.set! xk[i]! (.raw (← `(List.headD $e 0)))
    else
      env := env.set! xk[i]! (if i == 0 && binder != 1 then .raw (mkIdent resName) else .lit 0)
  let keepMem := binder == 2 || binder == 6 || (binder == 5 && tupRo)
  let mem : MT := if keepMem then .raw (mkIdent memIdent) else .raw (mkIdent mem1Ident)
  let ctx' : Ctx := { ctx with env, mem }
  let body ← transS E ctx' rest
  let bodyT ← body.render E.exc
  let used := idents bodyT.raw
  let fuel := used.contains `n
  let capMem := keepMem && used.contains memIdent
  let mut caps : Array Name := #[]
  let mut capVals : Array MT := #[]
  for i in [0:ctx.names.size] do
    let nm := ctx.names[i]!
    if xk.contains i then continue
    if used.contains nm then
      caps := caps.push nm
      capVals := capVals.push ctx.env[i]!
  let k := toString (fuel, caps, capMem, binder, resName, lres, tupRo, key bodyT)
  let st ← get
  let name ← match st.ks.find? (·.key == k) with
    | some kd => pure kd.name
    | none => do
      let name ← provName s!"k_{hint}" seq
      let refs := st.ks.filterMap fun kd => if used.contains kd.name then some kd.name else none
      let kd : KDef := { name, fuel, caps, capMem, binder, res := resName, body, key := k, refs, inLoop := ctx.loop.map (·.name), lres, lro := tupRo }
      modify fun st => { st with ks := st.ks.push kd }
      pure name
  let args := E.mps.map (fun x => MT.raw (mkIdent x)) ++ (if fuel then #[MT.raw (mkIdent `n)] else #[]) ++
    capVals ++ (if capMem then #[ctx.mem] else #[]) ++ #[callT]
  return .tail (.app name args)

/-- The code after a call with several results: an inline continuation `c call fun ρᵢ μᵢ => …`
under `bind c`, else a named one (`mkK`, binder `4`). -/
meta partial def bindK (E : Env) (ctx : Ctx) (xk : Array Nat) (callT : MT)
    (rest : List (TSyntax `lstmt)) : GenM MR := do
  let some c := E.bind | mkK E ctx 4 none xk callT rest
  let i := (← get).lams + 1
  modify fun st => { st with lams := i }
  let ρ := mkIdent (Name.mkSimple s!"ρ{subDigits i}")
  let μ := mkIdent (Name.mkSimple s!"μ{subDigits i}")
  let mut env := ctx.env
  for j in [0:xk.size] do
    let mut e : Term := ρ
    for _ in [0:j] do e ← `(List.tail $e)
    env := env.set! xk[j]! (.raw (← `(List.headD $e 0)))
  let body ← transS E { ctx with env, mem := .raw μ } rest
  return .tail (.raw (← `($(mkIdent c) $(← callT.render) fun $ρ $μ => $(← body.render E.exc))))

/-- Make a join point: the rest of the code after an `if` both of whose branches fall through,
as a definition over the locals it reads and the memory; the branches end by applying it. -/
meta partial def mkJoin (E : Env) (ctx : Ctx) (rest : List (TSyntax `lstmt)) :
    GenM Join := do
  let seq ← modifyGet fun st => (st.seq, { st with seq := st.seq + 1 })
  let env : Array MT := ctx.names.map fun n => .raw (mkIdent n)
  let ctx' : Ctx := { ctx with env, mem := .raw (mkIdent memIdent) }
  let body ← transS E ctx' rest
  let bodyT ← body.render E.exc
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
      let name ← provName "j" seq
      let refs := st.ks.filterMap fun kd => if used.contains kd.name then some kd.name else none
      let kd : KDef := { name, fuel, caps, capMem, binder := 3, res := `r, body, key := k, refs, inLoop := ctx.loop.map (·.name) }
      modify fun st => { st with ks := st.ks.push kd }
      pure name
  return { name, fuel, caps := capIdx, capMem }

/-- A loop `while c { body }` (written in the `lfn`: `direct`; or the named block `cst`) followed
by `rest`. The loop is a model of its own, `fW.loopᵢ n m x₁ …` (`exec p n` on the loop, so the
enclosing code applies it at `n + 1`), over the locals it reads before writing them; its result
is `(signal, outs…, memory)`: the signal (`Sig.normal` or `Sig.ret vs`) if the loop has a
`return`, the locals it assigns that `rest` reads, the memory unless the model is read-only. The
code after the loop is a continuation of that result. -/
meta partial def transLoop (E : Env) (ctx : Ctx) (cst : Option Name) (direct : Option Syntax)
    (c : TSyntax `lcond) (body : List (TSyntax `lstmt)) (rest : List (TSyntax `lstmt)) :
    GenM MR := do
  if ctx.loop.isSome then throwError "l_model: nested loops are not supported"
  let bodyNode := mkNullNode (body.toArray.map (·.raw))
  let A := (assignedIn ctx bodyNode).qsort (· < ·)
  let sig := hasReturn bodyNode
  let st0 ← get
  let lcnt := (st0.loops.filter (·.model == st0.base)).size
  let name := st0.base ++ Name.mkSimple s!"loop{lcnt + 1}"
  let raws (xs : Array Name) : Array MT := xs.map fun x => MT.raw (mkIdent x)
  -- fused: a loop with a `return`, followed by the function's last statement, `return …` or
  -- `abort`: the loop's model returns the function's result (the hand models' shape, the spec
  -- `fW.loopᵢ … = some ((r.retOr [e…]).headD 0, s'.mem)`)
  let fuse? : Option (Option (Array (TSyntax `lexpr))) :=
    if !(sig && ctx.ft.isNone) then none else
    match rest with
    | [s] => match s with
      | `(lstmt| return $e:lexpr) => some (some #[e])
      | `(lstmt| return ($e:lexpr, $es:lexpr,*)) => some (some (#[e] ++ es.getElems))
      | `(lstmt| abort) | `(lstmt| abort $_:ident) => some none
      | s => if s.raw.isOfKind ``L.Notation.lfail then some none else none
    | _ => none
  if let some retEs? := fuse? then
    let outUses : Array Nat := (retEs?.getD #[]).foldl (fun acc e => unionN acc (usesOf ctx e)) #[]
    let P := (liveS.loopLive E ctx c body outUses).qsort (· < ·)
    let envL : Array MT := ctx.names.mapIdx fun i n => if P.contains i then .raw (mkIdent n) else .lit 0
    let L : LoopInfo := { name, params := P, outs := #[], sig, exitStmts := some rest }
    let ctxL : Ctx := { ctx with env := envL, mem := .raw (mkIdent memIdent), ft := none, loop := some L }
    let saved := (← get).called
    modify fun st => { st with called := #[] }
    let cond ← transC E ctxL c
    let bodyR ← transS E ctxL body
    let exitR ← transS E ctxL rest
    let lbody := MR.ite cond bodyR exitR
    let calledL := (← get).called
    modify fun st => { st with called := saved }
    -- the results of `rest` over the final state `s'`
    let ctxS : Ctx := { ctx with env := ctx.names.mapIdx (fun j _ => MT.raw (Syntax.mkApp (mkIdent `L.St.loc)
      #[mkIdent `s', mkNum j])), mem := .raw (Syntax.mkApp (mkIdent `L.St.mem) #[mkIdent `s']) }
    let D ← (retEs?.getD #[]).mapM fun e => do (← transE E ctxS e).render
    let usedL := idents (← lbody.render E.exc).raw
    let st ← get
    let refs := st.ks.filterMap fun kd => if usedL.contains kd.name then some kd.name else none
    let kd : KDef := { name, fuel := true, caps := P.map (ctx.names[·]!), capMem := true, binder := 7, res := `r, body := lbody, key := toString name, refs }
    let lm : LoopMeta := { name, model := st.base, stmt := cst.getD (name ++ `stmt), direct, params := P, outs := #[], frames := #[], sig, ro := ctx.ro, called := calledL, fusedD := some D, abortRest := retEs?.isNone }
    modify fun st => { st with ks := st.ks.push kd, loops := st.loops.push lm, loopsCalled := st.loopsCalled.push name }
    return .tail (.app name (raws E.mps ++ #[.raw (← `($(mkIdent `n) + 1))] ++ #[ctx.mem] ++
      P.map (ctx.env[·]!)))
  -- 1. the code after the loop, over the loop's result
  let envK : Array MT := ctx.names.map fun n => .raw (mkIdent n)
  let memK : MT := if ctx.ro then .raw (mkIdent memIdent) else .raw (mkIdent mem1Ident)
  let ctxK : Ctx := { ctx with env := envK, mem := memK }
  let bodyK ← transS E ctxK rest
  let rI := mkIdent `r
  let bodyK ← if sig then do
      let retB ← ctxK.retList (← `(L.Sig.retVal $rI))
      pure (MR.ite (.cmp "=" (.raw rI) (.raw (mkIdent `L.Sig.normal))) bodyK retB)
    else pure bodyK
  let bodyKT ← bodyK.render E.exc
  let used := idents bodyKT.raw
  let outs := A.filter (used.contains ctx.names[·]!)
  let fuelK := used.contains `n
  let capMemK := ctx.ro && used.contains memIdent
  let mut caps : Array Name := #[]
  let mut capVals : Array MT := #[]
  let mut frames : Array Nat := #[]
  for i in [0:ctx.names.size] do
    if A.contains i then continue
    if used.contains ctx.names[i]! then
      caps := caps.push ctx.names[i]!
      capVals := capVals.push ctx.env[i]!
      frames := frames.push i
  let lres := outs.map (ctx.names[·]!)
  let kkey := toString (fuelK, caps, capMemK, 5, lres, sig, ctx.ro, key bodyKT)
  let kName ← match (← get).ks.find? (·.key == kkey) with
    | some kd => pure kd.name
    | none => do
      let st ← get
      let kn ← provName s!"k_{name.getString!}" 0
      let refs := st.ks.filterMap fun kd => if used.contains kd.name then some kd.name else none
      let kd : KDef := { name := kn, fuel := fuelK, caps, capMem := capMemK, binder := 5, res := `r, body := bodyK, key := kkey, refs, lres, lsig := sig, lro := ctx.ro, inLoop := ctx.loop.map (·.name) }
      modify fun st => { st with ks := st.ks.push kd }
      pure kn
  -- 2. the loop's parameters: the locals live at its head
  let P := (liveS.loopLive E ctx c body outs).qsort (· < ·)
  -- 3. the loop's body
  let envL : Array MT := ctx.names.mapIdx fun i n => if P.contains i then .raw (mkIdent n) else .lit 0
  let L : LoopInfo := { name, params := P, outs, sig }
  let ctxL : Ctx := { ctx with env := envL, mem := .raw (mkIdent memIdent), ft := none, loop := some L }
  let saved := (← get).called
  modify fun st => { st with called := #[] }
  let cond ← transC E ctxL c
  let bodyR ← transS E ctxL body
  let lbody := MR.ite cond bodyR (loopLeaf ctxL L none)
  let calledL := (← get).called
  modify fun st => { st with called := saved }
  let usedL := idents (← lbody.render E.exc).raw
  let st ← get
  let refs := st.ks.filterMap fun kd => if usedL.contains kd.name then some kd.name else none
  let kd : KDef := { name, fuel := true, caps := P.map (ctx.names[·]!), capMem := true, binder := 7, res := `r, body := lbody, key := toString name, refs }
  let lm : LoopMeta := { name, model := st.base, stmt := cst.getD (name ++ `stmt), direct, params := P, outs, frames, sig, ro := ctx.ro, called := calledL }
  modify fun st => { st with ks := st.ks.push kd, loops := st.loops.push lm, loopsCalled := st.loopsCalled.push name }
  -- 4. the enclosing code: the continuation, applied to the loop at `n + 1`
  let loopCall : MT := .app name (raws E.mps ++ #[.raw (← `($(mkIdent `n) + 1))] ++ #[ctx.mem] ++
    P.map (ctx.env[·]!))
  return .tail (.app kName (raws E.mps ++ (if fuelK then #[MT.raw (mkIdent `n)] else #[]) ++ capVals ++
    (if capMemK then #[ctx.mem] else #[]) ++ #[loopCall]))
end

/-! ## Final continuation names -/

/-- Rename the identifiers of a term. -/
meta def renameT (rn : Name → Option Name) (t : Term) : Term :=
  ⟨replaceStx t.raw fun s => match s with
    | .ident _ _ n _ => (rn n).map fun n' => (mkIdent n').raw
    | _ => none⟩

meta partial def MT.rename (rn : Name → Option Name) : MT → MT
  | .op o a b => .op o (a.rename rn) (b.rename rn)
  | .rd m a i => .rd (m.rename rn) (renameT rn a) (i.rename rn)
  | .rd8 m a i => .rd8 (m.rename rn) (renameT rn a) (i.rename rn)
  | .app f as => .app ((rn f).getD f) (as.map (·.rename rn))
  | .raw t => .raw (renameT rn t)
  | .list xs => .list (xs.map (·.rename rn))
  | t => t

meta partial def MC.rename (rn : Name → Option Name) : MC → MC
  | .cmp o a b => .cmp o (a.rename rn) (b.rename rn)
  | .and p q => .and (p.rename rn) (q.rename rn)
  | .or p q => .or (p.rename rn) (q.rename rn)
  | .not p => .not (p.rename rn)

meta partial def MR.rename (rn : Name → Option Name) : MR → MR
  | .some v m => .some (v.rename rn) (m.rename rn)
  | .someW v => .someW (v.rename rn)
  | .ite c t e => .ite (c.rename rn) (t.rename rn) (e.rename rn)
  | .tail t => .tail (t.rename rn)
  | .tup vs => .tup (vs.map (·.rename rn))
  | .none => .none
  | .err k => .err (k.rename rn)

/-- The final names of the provisional ones (`provName`): per model and stem in source order,
`stem`, `stem_2`, … (join points `j1`, `j2`, …). -/
meta def finalNames (ks : Array KDef) : Std.HashMap Name Name := Id.run do
  let prov := ks.filterMap fun kd => match kd.name with
    | .num p i => some (p, i, kd.name)
    | _ => none
  let prov := prov.qsort fun (p, i, _) (q, j, _) => p.toString < q.toString || (p == q && i < j)
  let mut m : Std.HashMap Name Name := {}
  let mut cnt : Std.HashMap Name Nat := {}
  for (p, _, n) in prov do
    let c := cnt.getD p 0 + 1
    cnt := cnt.insert p c
    let stem := p.getString!
    let fin := if stem == "j" then p.getPrefix ++ Name.mkSimple s!"j{c}"
      else if c == 1 then p else p.getPrefix ++ Name.mkSimple s!"{stem}_{c}"
    m := m.insert n fin
  return m

/-! ## Leaves and guarded equations -/

meta def leaves : MR → List (List (MC × Bool) × MR)
  | .none => []
  | .err _ => []
  | .ite c t e =>
    (leaves t).map (fun (p, l) => ((c, true) :: p, l)) ++
    (leaves e).map (fun (p, l) => ((c, false) :: p, l))
  | l => [([], l)]

/-- The paths to the `none` leaves (the aborts), with the leaf. -/
meta def aborts : MR → List (List (MC × Bool) × MR)
  | .none => [([], .none)]
  | .err k => [([], .err k)]
  | .ite c t e =>
    (aborts t).map (fun (p, l) => ((c, true) :: p, l)) ++ (aborts e).map (fun (p, l) => ((c, false) :: p, l))
  | _ => []

/-! ## The command -/

syntax lmodelFn := term " ↦ " ident (&" ro")? (&" list")? (&" tuple")?

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
  (&" sym " str)?
  (&" bind " ident)?
  (&" instances " num)?
  (&" simp " "[" term,* "]")?
  (&" errors")?
  (&" trace")? : command

meta structure FnInfo where
  lname : String
  decl : Name
  model : Name
  ro : Bool
  /-- several results: the model returns `List Word` -/
  multi : Bool
  /-- several results as a tuple of this many words -/
  tup : Nat
  lookup : Term
  params : Array Name
  lcls : Array Name
  body : TSyntax `lblock
  /-- the `lfn` term as read back, and its variables as written -/
  lfnStx : Syntax
  vars : Array Ident
  deriving Inhabited

/-- `L.x` (not part of a longer name) as `_root_.L.x`. -/
meta def rootL (txt : String) : String := Id.run do
  let cs := txt.toList.toArray
  let mut out : String := ""
  for i in [0:cs.size] do
    let c := cs[i]!
    let prevId := i > 0 && (cs[i-1]!.isAlphanum || cs[i-1]! == '_' || cs[i-1]! == '.' || cs[i-1]! == '\'')
    if c == 'L' && cs[i+1]? == some '.' && !prevId then out := out ++ "_root_."
    out := out.push c
  return out

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
  let symCfg : String := if stx[15].getNumArgs == 0 then "" else (stx[15][1].isStrLit?.getD "") ++ " "
  let bindC : Option Name := if stx[16].getNumArgs == 0 then none else some stx[16][1].getId
  let instN : Option Nat := if stx[17].getNumArgs == 0 then none else stx[17][1].isNatLit?
  let simpTs? : Option (Array Term) := if stx[18].getNumArgs == 0 then none else some ((optList 18).map (⟨·⟩))
  let exc := stx[19].getNumArgs != 0
  let doTrace := stx[20].getNumArgs != 0
  let stx := stx'
  let (infos, callees, foldRules) ← runTermElabM fun _ => do
    Term.elabBinders bs fun _ => do
    withLocalDeclD `n (mkConst ``Nat) fun _ => do
      let mut infos : Array (String × Name × Name × Bool × Bool × Bool × Term) := #[]
      for f in fnStx do
        let `(lmodelFn| $lk ↦ $w $[ro%$r]? $[list%$l]? $[tuple%$tu]?) := f | throwUnsupportedSyntax
        let e ← elabTerm lk none
        Term.synthesizeSyntheticMVarsNoPostponing
        let ty ← whnfR (← instantiateMVars (← inferType e))
        let some (_, lhs, rhs) := ty.eq? | throwErrorAt lk "l_model: expected `p.lookup \"f\" = some F`"
        let some fname := strLit? (lhs.getAppArgs[lhs.getAppNumArgs - 2]!)
          | throwErrorAt lk "l_model: the function name is not a literal"
        let some c := (rhs.getAppArgs.back!).consumeMData.constName?
          | throwErrorAt lk "l_model: the function is not a constant"
        infos := infos.push (fname, c, w.getId, r.isSome, l.isSome, tu.isSome, lk)
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
    | .eff t | .effL t | .list t _ | .memOpt t | .ro t | .roL t | .effT t _ | .roT t _ => idents t.raw acc
    | .pure ts => ts.foldl (fun acc t => idents t.raw acc) acc
    | .memTot t gs => gs.foldl (fun acc t => idents t.raw acc) (idents t.raw acc)) {}
  -- `errors` mode: the callees without a spec are called through `callE p n "f"`
  let calleeIds := if exc then calleeIds.insert `p else calleeIds
  let mpBs := allBs.filter (calleeIds.contains ·.1)
  let mps := mpBs.map (·.1)
  let mpBinders ← mpBs.mapM fun (x, ty) => `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent x) : $ty))
  let mpArgs : Array Term := mps.map fun x => (mkIdent x : Term)
  -- the L texts
  let mut fis : Array FnInfo := #[]
  for (lname, decl, model, ro, list, tuple, lookup) in infos do
    let s ← lfnSyntax decl
    let `(lfn ($ps,*) $[locals ($ls,*)]? $body:lblock) := s
      | throwError "l_model: {decl} is not an `lfn`"
    let params := ps.getElems.map (sanitize ·.getId mps)
    let locals' := ((ls.map (·.getElems.map (sanitize ·.getId mps))).getD #[])
    let tup := if tuple then max 2 (retArity body) else 0
    let multi := tup == 0 && (list || hasMultiRet body)
    let vars := ps.getElems ++ ((ls.map (·.getElems)).getD #[])
    fis := fis.push { lname, decl, model, ro, multi, tup, lookup, params, lcls := locals', body, lfnStx := s, vars }
  let grp := fis.map fun fi => (fi.lname, fi.model, fi.ro, fi.multi, fi.tup)
  -- the named blocks spliced into the bodies
  let mut blocks : Array (String × Name × List (TSyntax `lstmt) × Bool) := #[]
  for fi in fis do
    for t in splices fi.body do
      if blocks.any (·.1 == key t) then continue
      let c ← liftTermElabM (realizeGlobalConstNoOverload t)
      let bs ← liftTermElabM (declSyntax c "lblk")
      let `(lblk ($_,*) { $ss;* }) := bs | throwErrorAt t "l_model: {c} is not `… := lblk …`"
      let ss := ss.getElems.toList
      let isLoop := match ss with
        | [w] => match w with
          | `(lstmt| while $_:lcond $_:lblock) => true
          | _ => false
        | _ => false
      blocks := blocks.push (key t, c, ss, isLoop)
  let E : Env := { group := grp, callees := callees, folds := foldRules, noguard := noguard, mps, blocks, bind := bindC, exc }
  -- translate
  let (bodies, st) ← runTermElabM fun _ => do
    let go : GenM (Array (MR × Array String × Array Name)) := fis.mapM fun fi => do
      modify fun st => { st with base := fi.model, called := #[], loopsCalled := #[] }
      let names := fi.params ++ fi.lcls
      let env := names.mapIdx fun i n => if i < fi.params.size then MT.raw (mkIdent n) else .lit 0
      let ctx0 : Ctx := { names, env, mem := .raw (mkIdent memIdent), ro := fi.ro, multi := fi.multi, tup := fi.tup, clash := mps }
      let b ← transS E ctx0 (← blockStmts fi.body)
      return (b, (← get).called, (← get).loopsCalled)
    go.run {}
  let calledBy := bodies.map (·.2.1)
  let loopsBy := bodies.map (·.2.2)
  -- the final names of the continuations
  let fin := finalNames st.ks
  let rn (n : Name) : Option Name := fin.get? n
  let rnKD (kd : KDef) : KDef :=
    { kd with name := (rn kd.name).getD kd.name, refs := kd.refs.map (fun r => (rn r).getD r),
              body := kd.body.rename rn }
  let st : GenState := { st with ks := st.ks.map rnKD }
  let bodies := bodies.map (·.1.rename rn)
  -- a single member that needs no fuel (no recursion, no fuel-dependent callee, no continuation
  -- that needs it) gets a model without the fuel argument
  let noFuel : Bool ← do
    if fis.size != 1 || st.ks.any (·.fuel) then pure false
    else
      let b ← liftTermElabM (bodies[0]!.render exc)
      pure !(idents b.raw).contains `n
  if st.dups > 0 && doTrace then
    logInfo m!"l_model: {st.dups} join point(s) duplicated the code after them"
  -- render
  let wordT ← `(L.Word)
  let sigTy ← `(L.Sig)
  let memTy ← `(L.Mem)
  let nI := mkIdent `n
  let tupT (ts : Array Term) : CommandElabM Term :=
    match ts.size with
    | 0 => `(Unit)
    | 1 => pure ts[0]!
    | _ => ts.pop.foldrM (init := ts.back!) fun t acc => `($t × $acc)
  -- the result type: `Option T`, or `Except L.Err T` in `errors` mode
  let optT (t : Term) : CommandElabM Term := if exc then `(Except L.Err $t) else `(Option $t)
  let okI : Ident := mkIdent (if exc then `Except.ok else `Option.some)
  let failT : CommandElabM Term := if exc then `(Except.error L.Err.outOfFuel) else `(Option.none)
  let resT (fi : FnInfo) : CommandElabM Term := do
    if fi.tup > 0 then
      return ← optT (← tupT ((Array.replicate fi.tup wordT) ++ (if fi.ro then #[] else #[memTy])))
    match fi.ro, fi.multi with
    | true, false => optT (← `(L.Word))
    | false, false => optT (← `(L.Word × L.Mem))
    | true, true => optT (← `(List L.Word))
    | false, true => optT (← `(List L.Word × L.Mem))
  -- a continuation's failure arm: `none ↦ none`, or `.error e ↦ .error e`
  let failPat : CommandElabM Term := if exc then `(Except.error $(mkIdent `ε)) else `(Option.none)
  let failRhs : CommandElabM Term := if exc then `(Except.error $(mkIdent `ε)) else `(Option.none)
  let tupP (xs : Array Term) : CommandElabM Term :=
    match xs.size with
    | 0 => `(())
    | 1 => pure xs[0]!
    | _ => `(($(xs[0]!), $(xs.extract 1 xs.size),*))
  -- a loop's result: `(signal, outs…, memory)`
  let loopResT (lm : LoopMeta) : CommandElabM Term := do
    tupT ((if lm.sig then #[sigTy] else #[]) ++ lm.outs.map (fun _ => wordT) ++
      (if lm.ro then #[] else #[memTy]))
  let kDefs ← st.ks.mapM fun kd => do
    let fi := fis.find? (fun fi => kd.name.getPrefix == fi.model) |>.getD fis[0]!
    let nB ← if kd.fuel then `(Lean.Parser.Term.bracketedBinderF| ($nI : Nat)) else `(Lean.Parser.Term.bracketedBinderF| (_n : Unit))
    let capB ← kd.caps.mapM fun c => `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent c) : $wordT))
    let memB ← if kd.capMem then pure #[← `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent memIdent) : L.Mem))] else pure #[]
    let binders := if kd.binder == 7 then mpBinders ++ #[nB] ++ memB ++ capB
      else mpBinders ++ (if kd.fuel then #[nB] else #[]) ++ capB ++ memB
    -- binder 5: the result of a loop
    let lresB : Array Term := (if kd.lsig then #[(mkIdent kd.res : Term)] else #[]) ++
      kd.lres.map (fun x => (mkIdent x : Term)) ++ (if kd.lro then #[] else #[(mkIdent mem1Ident : Term)])
    let argT ← match kd.binder with
      | 0 => optT (← `(L.Word × L.Mem))
      | 4 => optT (← `(List L.Word × L.Mem))
      | 6 => optT (← `(List L.Word))
      | 5 => do optT (← tupT ((if kd.lsig then #[sigTy] else #[]) ++
          kd.lres.map (fun _ => wordT) ++ (if kd.lro then #[] else #[memTy])))
      | 1 => optT (← `(L.Mem))
      | _ => optT (← `(L.Word))
    let pat ← match kd.binder with
      | 0 | 4 => `($okI ($(mkIdent kd.res), $(mkIdent mem1Ident)))
      | 1 => `($okI $(mkIdent mem1Ident))
      | 5 => do `($okI $(← tupP lresB))
      | _ => `($okI $(mkIdent kd.res))
    let body ← liftTermElabM (kd.body.render exc)
    let loopOf : Option Name := if kd.binder == 7 then some kd.name else kd.inLoop
    let rT ← match loopOf with
      | some l => do
        let some lm := st.loops.find? (·.name == l) | throwError "l_model: lost loop {l}"
        if lm.fusedD.isSome then resT fi else
        optT (← loopResT lm)
      | none => resT fi
    pure (kd, binders, argT, pat, body, rT)
  -- the definitions, in dependency order: each strongly connected component of the reference
  -- graph is one definition or one `mutual` block; a recursive one with a continuation or a loop
  -- in it is well-founded on `(fuel, depth)`, one of models only is structural on the fuel
  let models := fis.map (·.model)
  let modelBodies ← bodies.mapM fun b => liftTermElabM (b.render exc)
  let nodes : Array Name := models ++ st.ks.map (·.name)
  let mut usedOf : Array NameSet := modelBodies.map (idents ·.raw)
  for kd in st.ks do
    usedOf := usedOf.push (idents (← liftTermElabM (kd.body.render exc)).raw)
  let edges : Array (Array Nat) := usedOf.map fun u =>
    (List.range nodes.size).toArray.filter (u.contains nodes[·]!)
  -- reachability (by at least one edge)
  let reach : Array (Array Bool) := (List.range nodes.size).toArray.map fun i => Id.run do
    let mut seen := Array.replicate nodes.size false
    let mut todo := edges[i]!
    while !todo.isEmpty do
      let j := todo.back!
      todo := todo.pop
      if seen[j]! then continue
      seen := seen.set! j true
      todo := todo ++ edges[j]!
    return seen
  let mut depth : Std.HashMap Name Nat := {}
  for kd in st.ks do
    depth := depth.insert kd.name (1 + kd.refs.foldl (fun d r => max d (depth.getD r 0)) 0)
  let maxDep := st.ks.foldl (fun d kd => max d (depth.getD kd.name 0)) 0
  -- the definitions' texts, by node; `wf`: with its `termination_by`
  let defOf (i : Nat) (wf : Bool) : CommandElabM (TSyntax `command) := do
    if h : i < fis.size then
      let fi := fis[i]
      let pbs ← fi.params.mapM fun x => `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent x) : L.Word))
      let wbs := mpBinders ++ #[← `(Lean.Parser.Term.bracketedBinderF| ($nI : Nat)), ← `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent memIdent) : L.Mem))] ++ pbs
      let body := modelBodies[i]!
      let rT ← resT fi
      let mbs := mpBinders ++ #[← `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent memIdent) : L.Mem))] ++ pbs
      if noFuel then
        `(command| def $(mkIdent fi.model):ident $mbs* : $rT := $body)
      else if wf then
        `(command|
          def $(mkIdent fi.model):ident $wbs* : $rT :=
            match $nI:ident with
            | 0 => $(← failT)
            | $nI:ident + 1 => $body
          termination_by ($nI, $(mkNum (maxDep + 1))))
      else
        `(command|
          def $(mkIdent fi.model):ident $wbs* : $rT :=
            match $nI:ident with
            | 0 => $(← failT)
            | $nI:ident + 1 => $body)
    else
      let (kd, binders, argT, pat, body, rT) := kDefs[i - fis.size]!
      let dep := mkNum (depth.getD kd.name 1)
      match kd.binder, wf with
      | 7, true => `(command|
          def $(mkIdent kd.name):ident $binders* : $rT :=
            match $nI:ident with
            | 0 => $(← failT)
            | $nI:ident + 1 => $body
          termination_by ($nI, $dep))
      | 7, false => `(command|
          def $(mkIdent kd.name):ident $binders* : $rT :=
            match $nI:ident with
            | 0 => $(← failT)
            | $nI:ident + 1 => $body)
      | 3, true => `(command|
          def $(mkIdent kd.name):ident $binders* : $rT := $body
          termination_by ($nI + 1, $dep))
      | 3, false => `(command| def $(mkIdent kd.name):ident $binders* : $rT := $body)
      | _, true => `(command|
          def $(mkIdent kd.name):ident $binders* : $argT → $rT
            | $(← failPat) => $(← failRhs)
            | $pat => $body
          termination_by _ => ($nI + 1, $dep))
      | _, false => `(command|
          def $(mkIdent kd.name):ident $binders* : $argT → $rT
            | $(← failPat) => $(← failRhs)
            | $pat => $body)
  -- emit the components, each after the ones it refers to
  let mut emitted := Array.replicate nodes.size false
  let mut left := nodes.size
  while left > 0 do
    let mut progress := false
    for i in [0:nodes.size] do
      if emitted[i]! then continue
      let comp := (List.range nodes.size).toArray.filter fun j =>
        j == i || (reach[i]![j]! && reach[j]![i]!)
      -- ready: every edge out of the component goes to an emitted node
      let ready := comp.all fun c => edges[c]!.all fun e => emitted[e]! || comp.contains e
      unless ready do continue
      let recursive := comp.size > 1 || reach[i]![i]!
      let wf := recursive && comp.any (· ≥ fis.size)
      let defs ← comp.mapM (defOf · wf)
      if defs.size == 1 then emit doTrace defs[0]!
      else emit doTrace (← `(command| mutual $defs* end))
      for c in comp do emitted := emitted.set! c true
      left := left - comp.size
      progress := true
    unless progress do throwError "l_model: cannot order the definitions"
  -- guarded equations, one per leaf that is not `none`
  -- a path condition as a hypothesis, in its natural form on the negative side (`a = b` for
  -- `¬ a ≠ b`, `a ≠ b` for `¬ a = b`, `p` for `¬ ¬ p`), and its rewrite rule
  let hypOf (c : MC) (pos : Bool) (h : Ident) :
      CommandElabM (Term × TSyntax ``Lean.Parser.Tactic.rwRule) := liftTermElabM do
    if pos then return (← c.render, ← `(Lean.Parser.Tactic.rwRule| ite_eq_left $h:ident))
    match c with
    | .cmp "≠" a b =>
      return (← `($(← a.render) = $(← b.render)),
        ← `(Lean.Parser.Tactic.rwRule| ite_eq_right (not_not_intro $h:ident)))
    | .cmp "=" a b =>
      return (← `($(← a.render) ≠ $(← b.render)), ← `(Lean.Parser.Tactic.rwRule| ite_eq_right $h:ident))
    | .not p =>
      return (← p.render, ← `(Lean.Parser.Tactic.rwRule| ite_eq_right (not_not_intro $h:ident)))
    | _ => return (← `(¬ $(← c.render)), ← `(Lean.Parser.Tactic.rwRule| ite_eq_right $h:ident))
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
        let h := mkIdent (Name.mkSimple s!"hc{j}")
        let (ty, rule) ← hypOf c pos h
        hyps := hyps.push (← `(Lean.Parser.Term.bracketedBinderF| ($h : $ty)))
        rules := rules.push rule
      let rhs ← liftTermElabM (leaf.render exc)
      let thm := mkIdent (name ++ Name.mkSimple s!"arm{k}")
      emit doTrace (← `(command|
        theorem $thm:ident $binders* $hyps* : $lhs = $rhs := by rw [$rules,*]))
      attrsOf thm lhs
    -- the aborts: `name.abortᵢ`, without patterns
    let mut a := 0
    for (path, leaf) in aborts body do
      a := a + 1
      let mut hyps : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
      let mut rules : Array (TSyntax ``Lean.Parser.Tactic.rwRule) := #[← `(Lean.Parser.Tactic.rwRule| $eq2:ident)]
      let mut j := 0
      for (c, pos) in path do
        j := j + 1
        let h := mkIdent (Name.mkSimple s!"hc{j}")
        let (ty, rule) ← hypOf c pos h
        hyps := hyps.push (← `(Lean.Parser.Term.bracketedBinderF| ($h : $ty)))
        rules := rules.push rule
      let thm := mkIdent (name ++ Name.mkSimple s!"abort{a}")
      let rhs ← liftTermElabM (leaf.render exc)
      emit doTrace (← `(command|
        theorem $thm:ident $binders* $hyps* : $lhs = $rhs := by rw [$rules,*]))
      -- `errors` mode: an abort is an error the spec states, so its equation gets patterns
      if exc then attrsOf thm lhs
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
    let resB : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) ← match kd.binder with
      | 0 => pure #[← `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent kd.res) : L.Word)),
                    ← `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent mem1Ident) : L.Mem))]
      | 4 => pure #[← `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent kd.res) : List L.Word)),
                    ← `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent mem1Ident) : L.Mem))]
      | 1 => pure #[← `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent mem1Ident) : L.Mem))]
      | 2 => pure #[← `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent kd.res) : L.Word))]
      | 6 => pure #[← `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent kd.res) : List L.Word))]
      | 5 => do
        let mut bs : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
        if kd.lsig then bs := bs.push (← `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent kd.res) : L.Sig)))
        for x in kd.lres do bs := bs.push (← `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent x) : L.Word)))
        unless kd.lro do bs := bs.push (← `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent mem1Ident) : L.Mem)))
        pure bs
      | _ => pure #[]
    let args : Array Term := mpArgs ++ (if kd.fuel then #[(nI : Term)] else #[]) ++ kd.caps.map (mkIdent ·) ++
      (if kd.capMem then #[(mkIdent memIdent : Term)] else #[])
    if kd.binder == 7 then
      let largs : Array Term := mpArgs ++ #[← `($nI + 1)] ++
        (if kd.capMem then #[(mkIdent memIdent : Term)] else #[]) ++ kd.caps.map (mkIdent ·)
      let lhs ← `($(mkIdent kd.name) $largs*)
      nEqns := nEqns + (← eqns kd.name binders lhs kd.body)
    else if kd.binder == 3 then
      let lhs ← `($(mkIdent kd.name) $args*)
      nEqns := nEqns + (← eqns kd.name binders lhs kd.body `eq_1)
    else
      let lhs ← `($(mkIdent kd.name) $args* $pat)
      nEqns := nEqns + (← eqns kd.name (binders ++ resB) lhs kd.body)
      -- the failed call
      let thm := mkIdent (kd.name ++ `none)
      if exc then
        emit doTrace (← `(command|
          theorem $thm:ident $binders* ($(mkIdent `ε) : L.Err) :
              $(mkIdent kd.name) $args* (Except.error $(mkIdent `ε)) = Except.error $(mkIdent `ε) := by
            rw [$(mkIdent (kd.name ++ `eq_1)):ident]))
        attrsOf thm (← `($(mkIdent kd.name) $args* (Except.error $(mkIdent `ε))))
      else
        emit doTrace (← `(command|
          theorem $thm:ident $binders* : $(mkIdent kd.name) $args* Option.none = Option.none := by
            rw [$(mkIdent (kd.name ++ `eq_1)):ident]))
  -- the proofs, as text
  let pp (t : Syntax) : CommandElabM String := do
    return toString (← liftCoreM (PrettyPrinter.ppTerm ⟨t⟩))
  let attrsTxt := String.intercalate ", " ("lang_grind" :: (attrIds.toList.map (·.getId.toString)))
  let specsTxt ← specTs.toList.mapM (pp ·.raw)
  let extraTxt ← extraTs.toList.mapM (pp ·.raw)
  let hintsTxt ← hintTs.toList.mapM (pp ·.raw)
  let genTxt := (match genN with | some g => s!"(gen := {g}) " | none => "") ++
    (match instN with | some i => s!"(instances := {i}) " | none => "")
  let hintsT := if hintsTxt.isEmpty then "" else s!"[{String.intercalate ", " hintsTxt}]"
  -- `simp [..]`: the steps by `vcgen` then `simp_all` over the models' equations (PLAN.md, "no
  -- `sym … finish` on a function with many paths"), instead of `sym … => vcgen … <;> finish`
  let simpTxt? ← simpTs?.mapM fun ts => do
    let user ← ts.toList.mapM (pp ·.raw)
    let base := ["L.LocEq", "L.St.setLoc_loc", "L.St.setLoc_mem", "L.St.setLocs_nil",
      "L.St.setLocs_cons", "L.Locals.init_nil", "L.Locals.init_cons_zero", "L.Locals.init_cons_succ",
      "L.Sig.retVal", "L.Sig.retOr", "L.BinOp.eval", "L.Cmp.eval", "List.headD_cons", "List.headD_nil",
      "List.tail_cons", "List.tail_nil"]
    let models := (fis.toList.map (s!"{·.model}")) ++ (st.ks.toList.map (s!"{·.name}"))
    pure (String.intercalate ", " (base ++ models ++ user))
  let stepTac (attrs vcg : String) : String := match simpTxt? with
    | some l => s!"(vcgen [{vcg}] <;> (try simp_all [{l}]) <;> grind [{attrs}])"
    | none => s!"sym {symCfg}only [{attrs}] => (vcgen [{vcg}] <;> finish {genTxt}{hintsT})"
  let parseTac (txt : String) : CommandElabM Syntax := do
    -- the library's names root-qualified, so that a binder `L` does not capture them
    let txt := rootL txt
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
  let calleeSpecs (called : Array String) : List String :=
    ((specsTxt.zip callees.toList).filter (called.contains ·.2.1)).map (·.1) ++
      ((st.autoE.filter called.contains).toList.map fun f => s!"L.callE_spec p n \"{f}\"")
  let stepExec := if exc then "L.Triple.step_exec'" else "L.Triple.step_exec"
  -- the loads: unfolded, or in `errors` mode by their error-precise specs (a byte load's here; a
  -- word load's as `rdW` comes with the caller's `extra`, `L.Arena.ld64_rdW_specE`)
  let loadTxt : List String := if exc then ["L.ld8_specE"] else ["L.ld64"]
  let loopSpecTxt (l : Name) : String := s!"fun s => {stepExec} ({l}.spec {argsTxt} (n + 1) s)"
  let pName := mkIdent `p
  let s0 := mkIdent `s₀
  let sP := mkIdent `s'
  -- the loops: their statements (a `while` written in the `lfn` becomes a named block), specs
  for lm in st.loops do
    let fi := fis.find? (·.model == lm.model) |>.getD fis[0]!
    if let some w := lm.direct then
      let w : TSyntax `lstmt := ⟨w⟩
      emit doTrace (← `(command|
        /-- A loop of the L code, named for its spec (generated by `l_model`). -/
        def $(mkIdent lm.stmt):ident : L.Stmt := lblk ($fi.vars,*) { $w:lstmt }))
    let locT (st : Ident) (i : Nat) : CommandElabM Term := `(L.St.loc $st $(mkNum i))
    let args ← lm.params.mapM (locT s0)
    let outs ← lm.outs.mapM (locT sP)
    let memSP ← `(L.St.mem $sP)
    let memS0 ← `(L.St.mem $s0)
    let res : Array Term := (if lm.sig then #[(mkIdent `r : Term)] else #[]) ++ outs ++
      (if lm.ro then #[] else #[memSP])
    let memA : Array Term := #[memS0]
    let lhs ← `($(mkIdent lm.name) $mpArgs* $nI $memA* $args*)
    let rI := mkIdent `r
    let sigC ← if lm.sig then `($rI ≠ L.Sig.brk) else `($rI = L.Sig.normal)
    let mut conj : Array Term := #[sigC]
    if lm.abortRest then conj := conj.push (← `($rI ≠ L.Sig.normal))
    for j in lm.frames do conj := conj.push (← `($(← locT sP j) = $(← locT s0 j)))
    if lm.ro then conj := conj.push (← `(L.St.mem $sP = L.St.mem $s0))
    match lm.fusedD with
    | none => conj := conj.push (← `($lhs = $okI $(← tupP res)))
    | some D =>
      -- the function's result: `r.retOr [the results of the code after the loop]`
      let l ← `(L.Sig.retOr $rI [$D,*])
      let comps : Array Term ← if fi.tup > 0 then
          (List.range fi.tup).toArray.mapM fun i => do
            let mut e : Term := l
            for _ in [0:i] do e ← `(List.tail $e)
            `(List.headD $e 0)
        else if fi.multi then pure #[l] else pure #[← `(List.headD $l 0)]
      conj := conj.push (← `($lhs = $okI $(← tupP (comps ++ (if lm.ro then #[] else #[memSP])))))
    let post ← conj.pop.foldrM (init := conj.back!) fun c acc => `($c ∧ $acc)
    let epost ← if exc then `(fun $(mkIdent `ε) => L.Err.code $(mkIdent `ε) ≠ 0 → $lhs = Except.error $(mkIdent `ε))
      else `(Lean.Order.top)
    let vcg := String.intercalate ", "
      ((["L.step", "L.evalE", "L.evalC", "L.evalArgs", "L.setLoc", "L.setLocs"] ++ loadTxt ++ ["L.st64", "L.setG"] ++
        extraTxt).eraseDups ++ calleeSpecs lm.called ++ ["ih"])
    let tac ← parseTac s!"induction n generalizing s₀ with\n  | zero => vcgen [L.exec] <;> grind\n  | succ n ih => rw [L.exec, L.step_while (w := {lm.stmt}) rfl]; {stepTac attrsTxt vcg}"
    emit doTrace (← withHB (← `(command|
      /-- The loop's spec (generated by `l_model`): its model is its meaning. -/
      theorem $(mkIdent (lm.name ++ `spec)):ident $bs* ($nI : Nat) ($s0 : L.St) :
        Std.WP.Triple (L.exec $pName $nI $(mkIdent lm.stmt)) (fun s => s = $s0) (fun $(mkIdent `r) $sP => $post)
          $epost := by $(⟨tac⟩):tactic)))
  -- a function with a `while` in its text: its `lfn` with the loop as a named block
  let mut unfoldOf : Array String := #[]
  for fi in fis do
    let direct := st.loops.filter (fun lm => lm.model == fi.model && lm.direct.isSome)
    if direct.isEmpty then
      unfoldOf := unfoldOf.push s!"{fi.decl}"
      continue
    let mut lstx := fi.lfnStx
    for lm in direct do
      let some w := lm.direct | continue
      let sp ← `(lstmt| ⟪$(mkIdent lm.stmt)⟫)
      lstx := replaceStx lstx fun t =>
        if t.getKind == w.getKind && t.getPos? == w.getPos? && t.getTailPos? == w.getTailPos? then
          some sp.raw else none
    let eqName := mkIdent (fi.model ++ `lfn_eq)
    emit doTrace (← `(command|
      /-- The function, with its loops as named blocks (generated by `l_model`). -/
      theorem $eqName:ident : $(mkIdent fi.decl) = $(⟨lstx⟩) := rfl))
    unfoldOf := unfoldOf.push s!"{fi.model}.lfn_eq"
  -- the spec of the group
  let userNames : NameSet := bs.foldl (fun acc b => idents b.raw acc) {}
  let mkConj (fuel : Term) : CommandElabM (Array Term) := fis.mapM fun fi => do
    let ps : Array Ident := fi.params.map fun x => mkIdent (if userNames.contains x then x.appendAfter "'" else x)
    let pbs ← ps.mapM fun x => `(Lean.Parser.Term.bracketedBinderF| ($x : L.Word))
    let W := mkIdent fi.model
    let Wapp ← if noFuel then `($W $mpArgs* (L.St.mem $s0) $ps*) else `($W $mpArgs* $fuel (L.St.mem $s0) $ps*)
    let rI := mkIdent `r
    let rs ← (List.range fi.tup).toArray.mapM fun i => do
      let mut e : Term := rI
      for _ in [0:i] do e ← `(List.tail $e)
      `(List.headD $e 0)
    let post ← if fi.tup > 0 then
        if fi.ro then
          `(fun $rI s' => L.LocEq s' $s0 ∧ L.St.mem s' = L.St.mem $s0 ∧ $Wapp = $okI $(← tupP rs))
        else
          `(fun $rI s' => L.LocEq s' $s0 ∧ $Wapp = $okI $(← tupP (rs.push (← `(L.St.mem s')))))
      else match fi.ro, fi.multi with
      | true, false =>
        `(fun r s' => L.LocEq s' $s0 ∧ L.St.mem s' = L.St.mem $s0 ∧
          $Wapp = $okI (List.headD r 0))
      | false, false =>
        `(fun r s' => L.LocEq s' $s0 ∧ $Wapp = $okI (List.headD r 0, L.St.mem s'))
      | true, true =>
        `(fun r s' => L.LocEq s' $s0 ∧ L.St.mem s' = L.St.mem $s0 ∧ $Wapp = $okI r)
      | false, true =>
        `(fun r s' => L.LocEq s' $s0 ∧ $Wapp = $okI (r, L.St.mem s'))
    -- the exceptional post: `⊤`, or in `errors` mode every error with a code is the model's
    let epost ← if exc then `(fun $(mkIdent `ε) => L.Err.code $(mkIdent `ε) ≠ 0 → $Wapp = Except.error $(mkIdent `ε))
      else `(Lean.Order.top)
    let fstr := Syntax.mkStrLit fi.lname
    `(∀ ($s0 : L.St) $pbs*, Std.WP.Triple (L.invoke $pName (L.exec $pName $fuel) $fstr [$ps,*])
        (fun s => s = $s0) $post $epost)
  let conj ← mkConj nI
  let stmt ← conj.pop.foldrM (init := conj.back!) fun c acc => `($c ∧ $acc)
  -- one step theorem per member, then the induction
  let k := fis.size
  let goals := String.intercalate ", " ((List.range k).map fun i => s!"?g{i+1}")
  let ihs := String.intercalate ", " ((List.range k).map fun i => s!"ih{i+1}")
  let vcgOf (called : Array String) (loops : Array Name) : String := String.intercalate ", "
    ((["L.exec", "L.step", "L.evalE", "L.evalC", "L.evalArgs", "L.setLoc", "L.setLocs"] ++ loadTxt ++ ["L.st64", "L.setG"] ++
      extraTxt).eraseDups ++ calleeSpecs called ++ (loops.toList.map loopSpecTxt) ++
      ((List.range k).filter (called.contains fis[·]!.lname)).map fun i => s!"ih{i+1}")
  let nB ← `(Lean.Parser.Term.bracketedBinderF| ($nI : Nat))
  let ihB ← `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent `ih) : $stmt))
  let conjS ← mkConj (← `($nI + 1))
  let mut zero := ""
  let mut steps : Array String := #[]
  for fi in fis, i in List.range k, called in calledBy, loops in loopsBy, ci in conjS, unf in unfoldOf do
    let vcg := vcgOf called loops
    let lk ← pp fi.lookup.raw
    let pre := s!"intros; rw [L.invoke_eq _ ({lk})]; simp only [L.callFn, {unf}]"
    let g := if k == 1 then "" else s!"case g{i+1} => "
    zero := zero ++ s!"\n    {g}({pre}; vcgen [L.exec] <;> grind)"
    -- under `simp`, an unused induction hypothesis is cleared (`simp_all` would rewrite it)
    let ihTxt := if simpTs?.isSome && !fis.any (called.contains ·.lname) then "clear ih"
      else if k == 1 then "have ih1 := ih" else s!"obtain ⟨{ihs}⟩ := ih"
    let tac ← parseTac s!"{ihTxt}; {pre}; {stepTac attrsTxt vcg}"
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
    logInfo m!"l_model: {fis.size} model(s), {st.ks.size} continuation(s) and loop(s), {nEqns} guarded equation(s)"

end L.ModelGen
