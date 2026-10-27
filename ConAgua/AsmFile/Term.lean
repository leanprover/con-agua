import ConAgua.Compiler.Compile
import Lean.Util.ReplaceExpr

/-!
# Programs as terms (TRUSTED: `include_asm` builds its term with these)

`programTerm segs` turns a program, cut into segments, into a term of type `Program` that denotes
it: the segments joined by `++` (right-nested, ending in `[]`), each segment a balanced `++` tree of
list literals of at most 64 directives (a long list literal is a term of linear depth). Each
directive is Lean's `toExpr` of it, with two rewrites that keep its value and make the term the
one the code generator's own evaluation gives (so that the kernel compares the file's term with
the compiler's output structurally, `ConAgua/Compiler/AsmLit.lean`):

* a label string becomes the term that names it (`errorL`, `fnL g`, `lbl f n m`, …) only when that
  term evaluates to the same string (checked here, by running it); otherwise it stays a literal;
* a 64-bit integer `OfNat.ofNat n` (or `-OfNat.ofNat n`) becomes `Int64.ofInt n` (`Int64.ofInt (-n)`).

`asm_lit` (`ConAgua/Compiler/AsmLit.lean`) builds its literals with the same functions.
-/

namespace L.Compiler

open Lean

/-- The term for the label `s` in the code of function `f`: a named label, `fnL g`, `lbl f n m`,
or the literal; never a term whose value is not `s`. -/
def labelExpr (f : String) (s : String) : Lean.Expr := Id.run do
  for (v, n) in [(errorL, ``errorL), (exhaustedL, ``exhaustedL), (finishL, ``finishL), (okL, ``okL),
      (enterL, ``enterL)] do
    if s == v then return mkConst n
  if s.startsWith "ca_f_" then
    let g := (s.drop 5).toString
    if fnL g == s then return mkApp (mkConst ``fnL) (mkStrLit g)
  let pre := ".Lca_" ++ f ++ "_"
  if s.startsWith pre then
    let rest := (s.drop pre.length).toString
    let ds := (rest.takeWhile Char.isDigit).toString
    let m := (rest.drop ds.length).toString
    if ds != "" && m != "" && m.all Char.isUpper && lbl f ds.toNat! m == s then
      return mkApp3 (mkConst ``lbl) (mkStrLit f) (mkRawNatLit ds.toNat!) (mkStrLit m)
  return mkStrLit s

/-- `n : Int64` as an `OfNat` literal (what `toExpr` gives), its value. -/
def int64Lit? (e : Lean.Expr) : Option Nat :=
  if e.isAppOfArity ``OfNat.ofNat 3 && e.appFn!.appFn!.appArg! == mkConst ``Int64 then
    match e.appFn!.appArg! with
    | .lit (.natVal n) => some n
    | _ => none
  else none

/-- A directive of function `f`'s code as a term (see the module doc). -/
def directiveExpr (f : String) (d : Directive) : Lean.Expr :=
  (toExpr d).replace fun e =>
    match e with
    | .lit (.strVal s) => some (labelExpr f s)
    | _ =>
      if let some n := int64Lit? e then some (mkApp (mkConst ``Int64.ofInt) (toExpr (n : Int)))
      else if e.isAppOfArity ``Neg.neg 3 && e.appFn!.appFn!.appArg! == mkConst ``Int64 then
        (int64Lit? e.appArg!).map fun n => mkApp (mkConst ``Int64.ofInt) (toExpr (-(n : Int)))
      else none

def dirTy : Lean.Expr := mkConst ``Directive
def progTy : Lean.Expr := mkApp (mkConst ``List [0]) dirTy

/-- `a ++ b` at `Program`. -/
def appendE (a b : Lean.Expr) : Lean.Expr :=
  mkApp6 (mkConst ``HAppend.hAppend [0, 0, 0]) progTy progTy progTy
    (mkApp2 (mkConst ``instHAppendOfAppend [0]) progTy (mkApp (mkConst ``List.instAppend [0]) dirTy)) a b

def nilE : Lean.Expr := mkApp (mkConst ``List.nil [0]) dirTy

/-- A list literal as a balanced tree of `++` over chunks of at most 64 elements. -/
partial def programExpr (xs : Array Lean.Expr) : Lean.Expr :=
  if xs.size ≤ 64 then
    xs.foldr (fun d acc => mkApp3 (mkConst ``List.cons [0]) dirTy d acc) nilE
  else
    let h := (xs.size / 64 + 1) / 2 * 64
    appendE (programExpr (xs.extract 0 h)) (programExpr (xs.extract h xs.size))

/-- The code of function `f` as a term. -/
def codeExpr (f : String) (v : Program) : Lean.Expr := programExpr (v.toArray.map (directiveExpr f))

/-- `s₀ ++ (s₁ ++ (… ++ (sₖ ++ [])))`. -/
def joinE (segs : List Lean.Expr) : Lean.Expr := segs.foldr appendE nilE

end L.Compiler
