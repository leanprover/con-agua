import ConAgua.Checker.Prog
import ConAgua.L.ErrSpec
/-! `scripts/nv_fns.py`'s query: the functions of `checkerProg` outside the verdict closure (no
abort of class 1 or 2 in their call closure), one `FN name` line each. -/
open L

partial def nvAborts : Stmt → Bool
  | .seq a b | .ite _ a b => nvAborts a && nvAborts b
  | .while _ s => nvAborts s
  | .abort e => e.cls0
  | _ => true

partial def nvCallees : Stmt → List FnName
  | .seq a b | .ite _ a b => nvCallees a ++ nvCallees b
  | .while _ s => nvCallees s
  | .call _ f _ => [f]
  | _ => []

#eval show IO Unit from do
  let p := L.Checker.checkerProg
  let mut bad : Std.HashSet FnName := {}
  for (f, fd) in p do
    if !nvAborts fd.body then bad := bad.insert f
  let mut changed := true
  while changed do
    changed := false
    for (f, fd) in p do
      if !bad.contains f && (nvCallees fd.body).any bad.contains then
        bad := bad.insert f; changed := true
  let mut seen : Std.HashSet FnName := {}
  for (f, _) in p do
    if !bad.contains f && !seen.contains f then
      seen := seen.insert f
      IO.println s!"FN {f}"
