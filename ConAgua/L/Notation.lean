module

public import ConAgua.L.Syntax
public import ConAgua.L.TRec
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
* `R[i].f` reads field `f` of record `i` of the record layout `R : L.Record` (a Lean constant;
  the field is the constant `R.f : L.Field`), `R[i].f := e` writes it: the word
  `i * stride + f.off` of the word array `R.arr` (`L/Records.lean`).
* `A⟨t⟩[i]` reads word `i` of tier `t` of the tiered word array `A` (`L.tierA A t`: `A`, or
  `A + tierOff` when `t & 1 = 1`); `len(A⟨t⟩)` is that tier's length, `A⟨t⟩[i] := e` writes it,
  and `R⟨t⟩[i].f` / `R⟨t⟩[i].f := e` are records in a tiered array (lane tierarr).
* The node stores' records (`L/TRec.lean`, the stores in `Arena/StoreFields.lean`; lane tieracc):
  `R⟨t, i⟩.f` is field `f` of node `i` of tier `t` of the store `R : L.TRec` (`R⟨t, i⟩` a one-word
  column), `R⟦h⟧.f` / `R⟦h⟧` the node the handle word `h` names, `R⟨t⟩.count` the node count of
  tier `t`, `⟦h⟧.tier` / `⟦h⟧.idx` a handle's tier bit and index; `R⟨t, i⟩.f := e` writes a field
  (the store library only).
* `⦃x⦄.tier`, `⦃x⦄.idx`, `⦃x⦄.base` are the tier (bit 40), the index (the low 40 bits) and the
  tier's base address (`(x >> 40) << 40`) of a tier-tagged address `x`, and `A⦃x⦄` reads the word
  at the tagged address `x` of the tiered word array `A` (`A⟨⦃x⦄.tier⟩[⦃x⦄.idx]`). The limb
  pool's slices are named by such addresses: the tier is `1` for a slice of the scratch tier (open
  while the arena's scratch flag is set) and `0` otherwise (lane tierpool). A
  store's tier must be simple, so a writer decodes the tier and base of its top once into locals
  and indexes relative to the base: `t := ⦃top⦄.tier; b := ⦃top⦄.base; … A⟨t⟩[top + j - b] := e`
  (for a tier-0 top this is exactly `A[top + j]`, out-of-bounds aborts included). This macro is
  the one place that fixes the encoding.
* `D.c8[i]` reads byte `i` of the constant byte string `D : List UInt8` (a Lean constant);
  `len(D.c8)` is its length (a constant).
* Literals: numbers, characters (`'{'` is `123`), and `⟪t⟫` for any Lean term of type `Word`.
* An identifier that is not a local names a global variable: a Lean constant `g : L.GVar`
  (`abbrev HTOP : L.GVar := ⟨3⟩`). `g` reads it, `g := e`, `g += e`, `g -= e` write it.
* Operators `+ - * & | ^ << >>` (wrapping, as in Rust's `wrapping_*`), `mulhi(a, b)` (the high
  word of the 128-bit product), `u64(a < b)` (a comparison as `1`/`0`, Rust's `(a < b) as u64`),
  comparisons
  `== != < <= > >=` (unsigned) and `<ₛ ≤ₛ` (signed), and short-circuit `&& || !`.
* Statements are separated by `;`: `x := e`, `x += e`, `x -= e`, `x := call f(e, …)`,
  `(x, y, …) := call f(e, …)` (several results), `if c { … } else { … }` (with `else if`),
  `while c { … }`, `break`, `return e`, `return (e, e', …)`, `abort`, `abort R`, `fail R`, `skip`, and `⟪t⟫` for a
  named block `t : L.Stmt` (see `lblk`; a block written with other variables than a prefix of
  the enclosing ones is an error).
-/

namespace L.Notation

/-- A named block (`lblk`): the statement `s`, with the names of the variables it was written
with, so that splicing it with `⟪t⟫` can check them against the enclosing variables. -/
@[expose, reducible] def blk (_vars : List String) (s : Stmt) : Stmt := s

/-- `⟪t⟫` in a block with variables `vars`: `t`, after checking that a named block `t` was
written with a prefix of `vars` (its variables are numbered by position). -/
syntax (name := lsplice) "lsplice% " "[" str,* "]" term:max : term

declare_syntax_cat lexpr
declare_syntax_cat lcond
declare_syntax_cat lstmt (behavior := both)
declare_syntax_cat lblock

syntax num : lexpr
syntax char : lexpr
syntax "⟪" term "⟫" : lexpr
syntax ident : lexpr
syntax ident noWs "[" lexpr "]" : lexpr
syntax ident noWs "[" lexpr "]" noWs "." noWs ident : lexpr
syntax ident noWs "⟨" lexpr "⟩" noWs "[" lexpr "]" : lexpr
syntax ident noWs "⟨" lexpr "⟩" noWs "[" lexpr "]" noWs "." noWs ident : lexpr
syntax ident noWs "⟨" lexpr ", " lexpr "⟩" noWs "." noWs ident : lexpr
syntax ident noWs "⟨" lexpr ", " lexpr "⟩" : lexpr
syntax ident noWs "⟨" lexpr "⟩" noWs "." noWs ident : lexpr
syntax ident noWs "⟦" lexpr "⟧" noWs "." noWs ident : lexpr
syntax ident noWs "⟦" lexpr "⟧" : lexpr
syntax "⟦" lexpr "⟧" noWs "." noWs ident : lexpr
syntax "len" "(" ident ")" : lexpr
syntax "len" "(" ident noWs "⟨" lexpr "⟩" ")" : lexpr
syntax "mulhi" "(" lexpr ", " lexpr ")" : lexpr
/-- `le64!(A.u8, i)`: the little-endian word of the bytes `i … i + 7` (`D.c8` for constant bytes). -/
syntax "le64!" "(" ident ", " lexpr ")" : lexpr
syntax "u64" "(" lcond ")" : lexpr
syntax ident noWs "⦃" lexpr "⦄" : lexpr
syntax "⦃" lexpr "⦄" noWs "." noWs ident : lexpr
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
syntax "(" ident ", " ident,+ ")" " := " "call " ident "(" lexpr,* ")" : lstmt
syntax ident " := " lexpr : lstmt
syntax ident " += " lexpr : lstmt
syntax ident " -= " lexpr : lstmt
syntax ident noWs "[" lexpr "]" " := " lexpr : lstmt
syntax ident noWs "[" lexpr "]" noWs "." noWs ident " := " lexpr : lstmt
syntax ident noWs "⟨" lexpr ", " lexpr "⟩" noWs "." noWs ident " := " lexpr : lstmt
syntax ident noWs "⟨" lexpr "⟩" noWs "[" lexpr "]" " := " lexpr : lstmt
syntax ident noWs "⟨" lexpr "⟩" noWs "[" lexpr "]" noWs "." noWs ident " := " lexpr : lstmt
syntax "if " lcond lblock : lstmt
syntax "if " lcond lblock " else " lblock : lstmt
syntax "if " lcond lblock " else " lstmt : lstmt
syntax "while " lcond lblock : lstmt
syntax "break" : lstmt
syntax "return " lexpr : lstmt
syntax "return " "(" lexpr ", " lexpr,+ ")" : lstmt
syntax "abort" : lstmt
/-- `abort R`: abort with the code `R` (a Lean constant of type `L.Word`, `Arena/Reasons.lean`). -/
syntax "abort " ident : lstmt
/-- `fail R`: a reject or decline site, the twin's `fail`: abort with the code `R` (as `abort R`). -/
syntax (name := lfail) &"fail" ident : lstmt
/-- `x := scan!(A.u8, i, e, C)`: the first `j ∈ [i, e)` whose byte is in the class `C` (a Lean
constant: a 256-byte table), else `e` (`D.c8` for constant bytes; lane blkcopy). -/
syntax ident " := " "scan!" "(" ident ", " lexpr ", " lexpr ", " ident ")" : lstmt
/-- `copy!(D, di, S, si, n)`: `D[di + j] := S[si + j]` for `j < n` (`S` a word array `B.u64` or bytes
`B.u8`/`B.c8`; `D⟨t⟩`, `S⟨t⟩` for tiered word arrays; lane blkcopy). -/
syntax "copy!" "(" ident (noWs "⟨" lexpr "⟩")? ", " lexpr ", " ident (noWs "⟨" lexpr "⟩")? ", " lexpr ", "
  lexpr ")" : lstmt
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

/-- The byte source of `A.u8` / `D.c8`. -/
meta def bsrcOf (id : Ident) : MacroM Term := do
  let (arr, k) ← splitArr id
  match k with
  | "u8" => `(L.BSrc.arr $arr)
  | "c8" => `(L.BSrc.rom $arr)
  | _ => Macro.throwErrorAt id "expected bytes `A.u8` or `D.c8`"

meta def lookupVar (env : Array Name) (id : Ident) : MacroM Term := do
  match env.idxOf? id.getId with
  | some k => return Syntax.mkNumLit (toString k)
  | none => Macro.throwErrorAt id s!"unknown L variable {id.getId}"

/-- A local (its index) or, if no local has this name, a global variable (the Lean constant of
type `L.GVar` of that name). -/
meta def localOrGlobal (env : Array Name) (id : Ident) : Option Term :=
  (env.idxOf? id.getId).map fun k => Syntax.mkNumLit (toString k)

/-- `R[i].f`: the record layout `R : L.Record` and its field, the constant `R.f : L.Field`. -/
meta def recField (r f : Ident) : Term × Term :=
  ((r : Term), (mkIdentFrom f (r.getId ++ f.getId) : Term))

/-- `R⟨t, i⟩.f`: the field constant `R.f : L.Word` of the store record `R : L.TRec`. -/
meta def trecField (r f : Ident) : Term := mkIdentFrom f (r.getId ++ f.getId)

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
  | `(lexpr| $x:ident) => do
    match localOrGlobal env x with
    | some k => `(L.Expr.var $k)
    | none => `(L.Expr.glob ($x : L.GVar))
  | `(lexpr| $r:ident[$i:lexpr].$f:ident) => do
    let (R, F) := recField r f
    `(L.Expr.ld64 (L.Record.arr $R) (L.Record.at $R $(← transExpr env i) $F))
  | `(lexpr| $r:ident⟨$t:lexpr⟩[$i:lexpr].$f:ident) => do
    let (R, F) := recField r f
    `(L.Expr.ld64t (L.Record.arr $R) $(← transExpr env t) (L.Record.at $R $(← transExpr env i) $F))
  | `(lexpr| $a:ident⟨$t:lexpr⟩[$i:lexpr]) => do
    `(L.Expr.ld64t $a $(← transExpr env t) $(← transExpr env i))
  | `(lexpr| len($a:ident⟨$t:lexpr⟩)) => do
    `(L.Expr.len64t $a $(← transExpr env t))
  | `(lexpr| $r:ident⟨$t:lexpr, $i:lexpr⟩.$f:ident) => do
    `(L.TRec.ld $r $(← transExpr env t) $(← transExpr env i) $(trecField r f))
  | `(lexpr| $r:ident⟨$t:lexpr, $i:lexpr⟩) => do
    `(L.TRec.ld $r $(← transExpr env t) $(← transExpr env i) 0)
  | `(lexpr| $r:ident⟨$t:lexpr⟩.$c:ident) => do
    unless c.getId == `count do Macro.throwErrorAt c "expected `R⟨t⟩.count`"
    `(L.TRec.cntE $r $(← transExpr env t))
  | `(lexpr| $r:ident⟦$h:lexpr⟧.$f:ident) => do
    let h ← transExpr env h
    `(L.TRec.ld $r (L.tierE $h) (L.idxE $h) $(trecField r f))
  | `(lexpr| $r:ident⟦$h:lexpr⟧) => do
    let h ← transExpr env h
    `(L.TRec.ld $r (L.tierE $h) (L.idxE $h) 0)
  | `(lexpr| ⟦$h:lexpr⟧.$c:ident) => do
    match c.getId with
    | `tier => `(L.tierE $(← transExpr env h))
    | `idx => `(L.idxE $(← transExpr env h))
    | _ => Macro.throwErrorAt c "expected `⟦h⟧.tier` or `⟦h⟧.idx`"
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
  | `(lexpr| $a:ident⦃$x:lexpr⦄) => do
    let x ← transExpr env x
    `(L.Expr.ld64t $a (L.Expr.bin L.BinOp.shr $x (L.Expr.const 40))
      (L.Expr.bin L.BinOp.and $x (L.Expr.const 0xFFFFFFFFFF)))
  | `(lexpr| ⦃$x:lexpr⦄.$c:ident) => do
    match c.getId with
    | `tier => `(L.Expr.bin L.BinOp.shr $(← transExpr env x) (L.Expr.const 40))
    | `idx => `(L.Expr.bin L.BinOp.and $(← transExpr env x) (L.Expr.const 0xFFFFFFFFFF))
    | `base => `(L.Expr.bin L.BinOp.shl
        (L.Expr.bin L.BinOp.shr $(← transExpr env x) (L.Expr.const 40)) (L.Expr.const 40))
    | _ => Macro.throwErrorAt c "expected `⦃x⦄.tier`, `⦃x⦄.idx` or `⦃x⦄.base`"
  | `(lexpr| mulhi($a:lexpr, $b:lexpr)) => bin `(L.BinOp.mulhi) a b
  | `(lexpr| le64!($a:ident, $i:lexpr)) => do `(L.Expr.ld8x8 $(← bsrcOf a) $(← transExpr env i))
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
    `(L.Stmt.call [$(← lookupVar env x)] $fname [$args,*])
  | `(lstmt| ($x:ident, $xs:ident,* ) := call $f:ident($args,*)) => do
    let args ← args.getElems.mapM (transExpr env)
    let xs ← (#[x] ++ xs.getElems).mapM (lookupVar env)
    let fname := Syntax.mkStrLit f.getId.toString
    `(L.Stmt.call [$xs,*] $fname [$args,*])
  | `(lstmt| $x:ident := $e:lexpr) => do
    match localOrGlobal env x with
    | some k => `(L.Stmt.set $k $(← transExpr env e))
    | none => `(L.Stmt.gset ($x : L.GVar) $(← transExpr env e))
  | `(lstmt| $x:ident += $e:lexpr) => assignOp x `(L.BinOp.add) e
  | `(lstmt| $x:ident -= $e:lexpr) => assignOp x `(L.BinOp.sub) e
  | `(lstmt| $r:ident[$i:lexpr].$f:ident := $e:lexpr) => do
    let (R, F) := recField r f
    `(L.Stmt.st64 (L.Record.arr $R) (L.Record.at $R $(← transExpr env i) $F) $(← transExpr env e))
  | `(lstmt| $r:ident⟨$t:lexpr⟩[$i:lexpr].$f:ident := $e:lexpr) => do
    let (R, F) := recField r f
    `(L.Stmt.st64t (L.Record.arr $R) $(← transExpr env t) (L.Record.at $R $(← transExpr env i) $F)
      $(← transExpr env e))
  | `(lstmt| $a:ident⟨$t:lexpr⟩[$i:lexpr] := $e:lexpr) => do
    `(L.Stmt.st64t $a $(← transExpr env t) $(← transExpr env i) $(← transExpr env e))
  | `(lstmt| $r:ident⟨$t:lexpr, $i:lexpr⟩.$f:ident := $e:lexpr) => do
    `(L.TRec.st $r $(← transExpr env t) $(← transExpr env i) $(trecField r f) $(← transExpr env e))
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
  | `(lstmt| return $e:lexpr) => do `(L.Stmt.ret [$(← transExpr env e)])
  | `(lstmt| return ($e:lexpr, $es:lexpr,*)) => do
    let es ← (#[e] ++ es.getElems).mapM (transExpr env)
    `(L.Stmt.ret [$es,*])
  | `(lstmt| abort) => `(L.Stmt.abort (L.Expr.const 0))
  | `(lstmt| abort $r:ident) => `(L.Stmt.abort (L.Expr.const $r))
  | `(lstmt| $x:ident := scan!($a:ident, $i:lexpr, $e:lexpr, $c:ident)) => do
    `(L.Stmt.scan8 $(← lookupVar env x) $(← bsrcOf a) $(← transExpr env i) $(← transExpr env e) $c)
  | `(lstmt| copy!($d:ident $[⟨$dt:lexpr⟩]?, $di:lexpr, $src:ident $[⟨$st:lexpr⟩]?, $si:lexpr, $n:lexpr)) => do
    let (da, dk) ← splitArr d
    unless dk == "u64" do Macro.throwErrorAt d "the destination of a copy is a word array `A.u64`"
    let dw ← match dt with
      | some t => do `(L.WArr.tier $da $(← transExpr env t))
      | none => `(L.WArr.plain $da)
    let di ← transExpr env di
    let si ← transExpr env si
    let n ← transExpr env n
    let (sa, sk) ← splitArr src
    match sk with
    | "u64" =>
      let sw ← match st with
        | some t => do `(L.WArr.tier $sa $(← transExpr env t))
        | none => `(L.WArr.plain $sa)
      `(L.Stmt.copy64 $dw $di $sw $si $n)
    | _ => `(L.Stmt.copy8w $dw $di $(← bsrcOf src) $si $n)
  | `(lstmt| skip) => `(L.Stmt.skip)
  | `(lstmt| ⟪$t⟫) => do
    let names := env.map fun n => Syntax.mkStrLit n.toString
    `(lsplice% [$names,*] $t)
  | s =>
    -- `fail R` (its keyword is not reserved: `fail` stays an identifier elsewhere)
    if s.raw.isOfKind ``lfail then
      let r : Ident := ⟨s.raw[1]⟩
      `(L.Stmt.abort (L.Expr.const $r))
    else Macro.throwErrorAt s "unsupported L statement"
where
  /-- `x op= e`, for a local or a global `x`. -/
  assignOp (x : Ident) (op : MacroM Term) (e : TSyntax `lexpr) : MacroM Term := do
    let e ← transExpr env e
    match localOrGlobal env x with
    | some k => `(L.Stmt.set $k (L.Expr.bin $(← op) (L.Expr.var $k) $e))
    | none => `(L.Stmt.gset ($x : L.GVar) (L.Expr.bin $(← op) (L.Expr.glob ($x : L.GVar)) $e))

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
    let names := vs.getElems.map fun v => Syntax.mkStrLit v.getId.toString
    `(L.Notation.blk [$names,*] ($body : L.Stmt))

open Elab Term Meta in
/-- The string literals of a list literal. -/
meta partial def strList? (e : Lean.Expr) : Option (List String) :=
  match e.consumeMData.getAppFnArgs with
  | (``List.nil, _) => some []
  | (``List.cons, #[_, h, t]) =>
    match h.consumeMData with
    | Lean.Expr.lit (.strVal s) => (strList? t).map (s :: ·)
    | _ => none
  | _ => none

open Elab Term Meta in
@[term_elab lsplice] meta def elabLsplice : TermElab := fun stx _ => do
  let `(lsplice% [$names,*] $t) := stx | throwUnsupportedSyntax
  let e ← elabTerm t (some (mkConst ``L.Stmt))
  let vars := names.getElems.toList.map (·.getString)
  if let some c := e.constName? then
    if let some v := ((← getEnv).find? c).bind (·.value?) then
      let v := v.consumeMData
      if v.isAppOfArity ``L.Notation.blk 2 then
        if let some bvars := strList? (v.getArg! 0) then
          unless bvars.isPrefixOf vars do
            throwErrorAt t m!"the named block `{c}` was written with the variables {bvars}, \
              which are not a prefix of the variables here, {vars}"
  return e

end L.Notation
