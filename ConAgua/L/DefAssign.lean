module

public import ConAgua.L.Syntax

@[expose] public section

/-!
# Definite assignment

`Stmt.da s D R`: a definite-assignment analysis over the structured body (lane leafgen, step Z;
compopt2's E2). From the locals `D` defined before `s` (`none`: `s` is unreachable) it returns
the locals defined after `s` (`none`: `s` never ends normally) and accumulates in `R` the locals
that `s` may read before they are defined. The compiler zeroes only those locals of a function
(`fnBody0`); `L/DefAssignSim.lean` proves that the others do not matter.

Lists of `Nat` and structural recursion only: the kernel evaluates it when it checks the compiled
checker (`Checker/AsmFileEq.lean`).
-/

namespace L

/-- The locals an expression reads. -/
def Expr.rv : Expr → List Var
  | .const _ => []
  | .var x => [x]
  | .bin _ a b => Expr.rv a ++ Expr.rv b
  | .ld8 _ i => Expr.rv i
  | .ld64 _ i => Expr.rv i
  | .len8 _ => []
  | .len64 _ => []
  | .cmpw _ a b => Expr.rv a ++ Expr.rv b
  | .ldc _ i => Expr.rv i
  | .glob _ => []
  | .ld64t _ t i => Expr.rv t ++ Expr.rv i
  | .len64t _ t => Expr.rv t
  | .ld8x8 _ i => Expr.rv i

/-- The locals a block operand reads. -/
def WArr.rv : WArr → List Var
  | .plain _ => []
  | .tier _ t => Expr.rv t

/-- The locals a condition reads. -/
def Cond.rv : Cond → List Var
  | .cmp _ a b => Expr.rv a ++ Expr.rv b
  | .and p q => Cond.rv p ++ Cond.rv q
  | .or p q => Cond.rv p ++ Cond.rv q
  | .not p => Cond.rv p

/-- `R` and the locals of `vs` not in `D`. -/
def rdA (D vs R : List Var) : List Var := R ++ vs.filter (fun x => !D.contains x)

/-- `x` added to `D`. -/
def insV (x : Var) (D : List Var) : List Var := if D.contains x then D else x :: D

/-- The locals defined after either of two branches. -/
def meetD : Option (List Var) → Option (List Var) → Option (List Var)
  | none, d => d
  | some x, none => some x
  | some x, some y => some (x.filter y.contains)

/-- Definite assignment: from the defined locals `D` (`none`: unreachable), the defined locals
after the statement (`none`: it never ends normally) and the locals read before they are defined
(accumulated in `R`). -/
def Stmt.da : Stmt → Option (List Var) → List Var → Option (List Var) × List Var
  | _, none, R => (none, R)
  | .skip, some D, R => (some D, R)
  | .set x e, some D, R => (some (insV x D), rdA D e.rv R)
  | .st8 _ i e, some D, R => (some D, rdA D (i.rv ++ e.rv) R)
  | .st64 _ i e, some D, R => (some D, rdA D (i.rv ++ e.rv) R)
  | .seq a b, some D, R =>
    match Stmt.da a (some D) R with
    | (D1, R1) => Stmt.da b D1 R1
  | .ite c a b, some D, R =>
    match Stmt.da a (some D) (rdA D c.rv R) with
    | (D1, R1) =>
      match Stmt.da b (some D) R1 with
      | (D2, R2) => (meetD D1 D2, R2)
  | .while c a, some D, R => (some D, (Stmt.da a (some D) (rdA D c.rv R)).2)
  | .brk, some _, R => (none, R)
  | .ret es, some D, R => (none, rdA D (es.flatMap Expr.rv) R)
  | .call xs _ args, some D, R => (some (xs ++ D), rdA D (args.flatMap Expr.rv) R)
  | .abort e, some D, R => (none, rdA D e.rv R)
  | .gset _ e, some D, R => (some D, rdA D e.rv R)
  | .st64t _ t i e, some D, R => (some D, rdA D (t.rv ++ i.rv ++ e.rv) R)
  | .copy64 d di s si n, some D, R =>
    (some D, rdA D (d.rv ++ di.rv ++ s.rv ++ si.rv ++ n.rv) R)
  | .copy8w d di _ si n, some D, R => (some D, rdA D (d.rv ++ di.rv ++ si.rv ++ n.rv) R)
  | .scan8 x _ i e _, some D, R => (some (insV x D), rdA D (i.rv ++ e.rv) R)

/-- The locals of a function body that may be read before they are assigned (the parameters
`0, …, np - 1` are assigned on entry). -/
def needZero (np : Nat) (body : Stmt) : List Var := (Stmt.da body (some (List.range np)) []).2

end L
