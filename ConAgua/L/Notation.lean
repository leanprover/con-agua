module

public import ConAgua.L.Syntax
public meta import Lean

public section

/-!
# L: concrete syntax

A Rust-like surface for writing L functions by hand:

```
lfn (b_dummy, j) locals (c) {
  while j < len(IN.u8) {
    c := IN.u8[j];
    if c == '"' { return j } else { j += 1 }
  };
  return 0
}
```

* `lfn (params) locals (more) { body }` is a term of type `L.FunDecl`. Variable names resolve to
  local indices in declaration order (parameters first).
* `A.u8[i]` / `A.u64[i]` read byte / word array `A`, where `A` is a Lean constant of type
  `L.ArrId`; `len(A.u8)` / `len(A.u64)` are the lengths. Stores are `A.u8[i] := e`.
* `D.c8[i]` reads byte `i` of the constant byte string `D : List UInt8` (a Lean constant);
  `len(D.c8)` is its length (a constant).
* Literals: numbers, characters (`'{'` is `123`), and `⟪t⟫` for any Lean term of type `Word`.
* Operators `+ - * & | ^ << >>` (wrapping, as in Rust's `wrapping_*`), `mulhi(a, b)` (the high
  word of the 128-bit product), `u64(a < b)` (a comparison as `1`/`0`, Rust's `(a < b) as u64`),
  comparisons
  `== != < <= > >=` (unsigned) and `<ₛ ≤ₛ` (signed), and short-circuit `&& || !`.
* Statements are separated by `;`: `x := e`, `x += e`, `x -= e`, `x := call f(e, …)`,
  `if c { … } else { … }` (with `else if`), `while c { … }`, `break`, `return e`, `abort`, `skip`,
  and `⟪t⟫` for a named block `t : L.Stmt` (see `lblk`).
-/

namespace L.Notation

declare_syntax_cat lexpr
declare_syntax_cat lcond
declare_syntax_cat lstmt
declare_syntax_cat lblock

syntax num : lexpr
syntax char : lexpr
syntax "⟪" term "⟫" : lexpr
syntax ident : lexpr
syntax ident noWs "[" lexpr "]" : lexpr
syntax "len" "(" ident ")" : lexpr
syntax "mulhi" "(" lexpr ", " lexpr ")" : lexpr
syntax "u64" "(" lcond ")" : lexpr
syntax "(" lexpr ")" : lexpr
syntax:70 lexpr:70 " * " lexpr:71 : lexpr
syntax:65 lexpr:65 " + " lexpr:66 : lexpr
syntax:65 lexpr:65 " - " lexpr:66 : lexpr
syntax:60 lexpr:60 " << " lexpr:61 : lexpr
syntax:60 lexpr:60 " >> " lexpr:61 : lexpr
syntax:58 lexpr:58 " & " lexpr:59 : lexpr
syntax:57 lexpr:57 " ^ " lexpr:58 : lexpr
syntax:56 lexpr:56 " | " lexpr:57 : lexpr

syntax:50 lexpr:51 " == " lexpr:51 : lcond
syntax:50 lexpr:51 " != " lexpr:51 : lcond
syntax:50 lexpr:51 " < " lexpr:51 : lcond
syntax:50 lexpr:51 " <= " lexpr:51 : lcond
syntax:50 lexpr:51 " > " lexpr:51 : lcond
syntax:50 lexpr:51 " >= " lexpr:51 : lcond
syntax:50 lexpr:51 " <ₛ " lexpr:51 : lcond
syntax:50 lexpr:51 " ≤ₛ " lexpr:51 : lcond
syntax:35 lcond:36 " && " lcond:35 : lcond
syntax:30 lcond:31 " || " lcond:30 : lcond
syntax:max "!" lcond:max : lcond
syntax "(" lcond ")" : lcond

syntax "{" sepBy(lstmt, "; ", "; ", allowTrailingSep) "}" : lblock

syntax ident " := " "call " ident "(" lexpr,* ")" : lstmt
syntax ident " := " lexpr : lstmt
syntax ident " += " lexpr : lstmt
syntax ident " -= " lexpr : lstmt
syntax ident noWs "[" lexpr "]" " := " lexpr : lstmt
syntax "if " lcond lblock : lstmt
syntax "if " lcond lblock " else " lblock : lstmt
syntax "if " lcond lblock " else " lstmt : lstmt
syntax "while " lcond lblock : lstmt
syntax "break" : lstmt
syntax "return " lexpr : lstmt
syntax "abort" : lstmt
syntax "skip" : lstmt
syntax "⟪" term "⟫" : lstmt

open Lean

/-- Split `A.u8` into the array `A` and the width suffix. -/
meta def splitArr (id : Ident) : MacroM (Term × String) := do
  match id.getId with
  | .str pre "u8" => return (mkIdentFrom id pre, "u8")
  | .str pre "u64" => return (mkIdentFrom id pre, "u64")
  | .str pre "c8" => return (mkIdentFrom id pre, "c8")
  | _ => Macro.throwErrorAt id "expected `A.u8`, `A.u64` or `D.c8`"

meta def lookupVar (env : Array Name) (id : Ident) : MacroM Term := do
  match env.idxOf? id.getId with
  | some k => return Syntax.mkNumLit (toString k)
  | none => Macro.throwErrorAt id s!"unknown L variable {id.getId}"

/-- A single comparison: the operator and the operands (`a > b` is `b < a`). -/
meta def cmpSplit : TSyntax `lcond → MacroM (Term × TSyntax `lexpr × TSyntax `lexpr)
  | `(lcond| $a:lexpr == $b:lexpr) => return (← `(L.Cmp.eq), a, b)
  | `(lcond| $a:lexpr != $b:lexpr) => return (← `(L.Cmp.ne), a, b)
  | `(lcond| $a:lexpr < $b:lexpr) => return (← `(L.Cmp.ult), a, b)
  | `(lcond| $a:lexpr <= $b:lexpr) => return (← `(L.Cmp.ule), a, b)
  | `(lcond| $a:lexpr > $b:lexpr) => return (← `(L.Cmp.ult), b, a)
  | `(lcond| $a:lexpr >= $b:lexpr) => return (← `(L.Cmp.ule), b, a)
  | `(lcond| $a:lexpr <ₛ $b:lexpr) => return (← `(L.Cmp.slt), a, b)
  | `(lcond| $a:lexpr ≤ₛ $b:lexpr) => return (← `(L.Cmp.sle), a, b)
  | c => Macro.throwErrorAt c "unsupported L condition (expected a comparison)"

mutual
meta partial def transExpr (env : Array Name) : TSyntax `lexpr → MacroM Term
  | `(lexpr| $n:num) => `(L.Expr.const $n)
  | `(lexpr| $c:char) => do
    let v := Syntax.mkNumLit (toString c.getChar.toNat)
    `(L.Expr.const $v)
  | `(lexpr| ⟪$t⟫) => `(L.Expr.const $t)
  | `(lexpr| $x:ident) => do `(L.Expr.var $(← lookupVar env x))
  | `(lexpr| $a:ident[$i:lexpr]) => do
    let (arr, k) ← splitArr a
    let i ← transExpr env i
    match k with
    | "u8" => `(L.Expr.ld8 $arr $i)
    | "u64" => `(L.Expr.ld64 $arr $i)
    | _ => `(L.Expr.ldc $arr $i)
  | `(lexpr| len($a:ident)) => do
    let (arr, k) ← splitArr a
    match k with
    | "u8" => `(L.Expr.len8 $arr)
    | "u64" => `(L.Expr.len64 $arr)
    | _ => `(L.Expr.const (UInt64.ofNat (List.length $arr)))
  | `(lexpr| mulhi($a:lexpr, $b:lexpr)) => bin `(L.BinOp.mulhi) a b
  | `(lexpr| u64($c:lcond)) => do
    let (op, a, b) ← cmpSplit c
    `(L.Expr.cmpw $op $(← transExpr env a) $(← transExpr env b))
  | `(lexpr| ($e:lexpr)) => transExpr env e
  | `(lexpr| $a:lexpr * $b:lexpr) => bin `(L.BinOp.mul) a b
  | `(lexpr| $a:lexpr + $b:lexpr) => bin `(L.BinOp.add) a b
  | `(lexpr| $a:lexpr - $b:lexpr) => bin `(L.BinOp.sub) a b
  | `(lexpr| $a:lexpr << $b:lexpr) => bin `(L.BinOp.shl) a b
  | `(lexpr| $a:lexpr >> $b:lexpr) => bin `(L.BinOp.shr) a b
  | `(lexpr| $a:lexpr & $b:lexpr) => bin `(L.BinOp.and) a b
  | `(lexpr| $a:lexpr ^ $b:lexpr) => bin `(L.BinOp.xor) a b
  | `(lexpr| $a:lexpr | $b:lexpr) => bin `(L.BinOp.or) a b
  | e => Macro.throwErrorAt e "unsupported L expression"
where
  bin (op : MacroM Term) (a b : TSyntax `lexpr) : MacroM Term := do
    `(L.Expr.bin $(← op) $(← transExpr env a) $(← transExpr env b))

meta partial def transCond (env : Array Name) : TSyntax `lcond → MacroM Term
  | `(lcond| $p:lcond && $q:lcond) => do `(L.Cond.and $(← transCond env p) $(← transCond env q))
  | `(lcond| $p:lcond || $q:lcond) => do `(L.Cond.or $(← transCond env p) $(← transCond env q))
  | `(lcond| !$p:lcond) => do `(L.Cond.not $(← transCond env p))
  | `(lcond| ($p:lcond)) => transCond env p
  | c => do
    let (op, a, b) ← cmpSplit c
    `(L.Cond.cmp $op $(← transExpr env a) $(← transExpr env b))
end

mutual
meta partial def transStmt (env : Array Name) : TSyntax `lstmt → MacroM Term
  | `(lstmt| $x:ident := call $f:ident($args,*)) => do
    let args ← args.getElems.mapM (transExpr env)
    let fname := Syntax.mkStrLit f.getId.toString
    `(L.Stmt.call $(← lookupVar env x) $fname [$args,*])
  | `(lstmt| $x:ident := $e:lexpr) => do `(L.Stmt.set $(← lookupVar env x) $(← transExpr env e))
  | `(lstmt| $x:ident += $e:lexpr) => do
    let v ← lookupVar env x
    `(L.Stmt.set $v (L.Expr.bin .add (L.Expr.var $v) $(← transExpr env e)))
  | `(lstmt| $x:ident -= $e:lexpr) => do
    let v ← lookupVar env x
    `(L.Stmt.set $v (L.Expr.bin .sub (L.Expr.var $v) $(← transExpr env e)))
  | `(lstmt| $a:ident[$i:lexpr] := $e:lexpr) => do
    let (arr, b) ← splitArr a
    let i ← transExpr env i
    let e ← transExpr env e
    match b with
    | "u8" => `(L.Stmt.st8 $arr $i $e)
    | "u64" => `(L.Stmt.st64 $arr $i $e)
    | _ => Macro.throwErrorAt a "constant data cannot be written"
  | `(lstmt| if $c:lcond $s:lblock) => do `(L.Stmt.ite $(← transCond env c) $(← transBlock env s) L.Stmt.skip)
  | `(lstmt| if $c:lcond $s:lblock else $t:lblock) => do
    `(L.Stmt.ite $(← transCond env c) $(← transBlock env s) $(← transBlock env t))
  | `(lstmt| if $c:lcond $s:lblock else $t:lstmt) => do
    `(L.Stmt.ite $(← transCond env c) $(← transBlock env s) $(← transStmt env t))
  | `(lstmt| while $c:lcond $s:lblock) => do `(L.Stmt.while $(← transCond env c) $(← transBlock env s))
  | `(lstmt| break) => `(L.Stmt.brk)
  | `(lstmt| return $e:lexpr) => do `(L.Stmt.ret $(← transExpr env e))
  | `(lstmt| abort) => `(L.Stmt.abort)
  | `(lstmt| skip) => `(L.Stmt.skip)
  | `(lstmt| ⟪$t⟫) => `(($t : L.Stmt))
  | s => Macro.throwErrorAt s "unsupported L statement"

/-- A block is a right-nested `seq`; the empty block is `skip`. -/
meta partial def transBlock (env : Array Name) : TSyntax `lblock → MacroM Term
  | `(lblock| { $ss;* }) => do
    let ss := ss.getElems
    match ss.back? with
    | none => `(L.Stmt.skip)
    | some last =>
      ss.pop.foldrM (init := ← transStmt env last) fun s acc => do
        `(L.Stmt.seq $(← transStmt env s) $acc)
  | b => Macro.throwErrorAt b "unsupported L block"
end

/-- `lfn (params) locals (more) { body }`: an `L.FunDecl`. -/
syntax "lfn " "(" ident,* ")" (" locals " "(" ident,* ")")? lblock : term

macro_rules
  | `(lfn ($ps,*) $[locals ($ls,*)]? $b:lblock) => do
    let ps := ps.getElems.map (·.getId)
    let ls := (ls.map (·.getElems.map (·.getId))).getD #[]
    let env := ps ++ ls
    let body ← transBlock env b
    `(({ nparams := $(Syntax.mkNumLit (toString ps.size)),
         nlocals := $(Syntax.mkNumLit (toString env.size)),
         body := $body } : L.FunDecl))

/-- `lblk (vars) { stmts }`: an `L.Stmt`, with the variables numbered as in the enclosing
`lfn`. Use it to name a block (typically a loop) so that a spec can be stated about it; splice
it into the function with `⟪name⟫`. -/
syntax "lblk " "(" ident,* ")" lblock : term

macro_rules
  | `(lblk ($vs,*) $b:lblock) => do
    let body ← transBlock (vs.getElems.map (·.getId)) b
    `(($body : L.Stmt))

end L.Notation
