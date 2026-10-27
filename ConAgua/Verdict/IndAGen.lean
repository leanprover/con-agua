import Lean
import ConAgua.Arena.Verdict

/-!
# `err_stmt`: the error-claim statement of an ok refinement (lane `verdicts-b`, helper `ia`)

`err_stmt FooE := foo_refines fuel n` defines `FooE (p : Prog) : Prop`, the error half of the
triple-shaped refinement theorem `foo_refines`: its binders (except `p`, the fuel `n` and the
binders whose types mention `n`), then for every fuel `F ≤ 2 ^ 62` and every error `e` of the call
`callE p F f args s₀.mem`, the twin computation `T` (the first `AM.ok T a₀` in the postcondition)
satisfies `ErrClaim T a₀ e`. The statement is the ok theorem's, the conclusion its error
counterpart.
-/

open Lean Meta Elab Command Term

private def findApp? (e : Lean.Expr) (c : Name) : Option Lean.Expr :=
  e.find? fun s => s.isAppOf c

elab "err_stmt " nm:ident " := " thm:ident " fuel " nvar:ident : command => do
  liftTermElabM do
    let info ← getConstInfo (← realizeGlobalConstNoOverloadWithInfo thm)
    let nName := nvar.getId
    forallTelescope info.type fun xs body => do
      let some inv := findApp? body ``L.invoke | throwError "no invoke"
      let (T, a0) ← do
        match findApp? body ``L.Arena.AM.ok with
        | some okA => pure (okA.getAppArgs[1]!, okA.getAppArgs[2]!)
        | none =>
          let some rn := findApp? body ``StateT.run | throwError "no AM.ok / StateT.run"
          pure (rn.getAppArgs[3]!, rn.getAppArgs[4]!)
      let invArgs := inv.getAppArgs
      let pE := invArgs[0]!
      let fE := invArgs[2]!
      let argsE := invArgs[3]!
      let mut nFv : Option FVarId := none
      let mut s0 : Option Lean.Expr := none
      for x in xs do
        let d ← x.fvarId!.getDecl
        if d.userName == nName then nFv := some x.fvarId!
        if d.userName == `s₀ then s0 := some x
      let some nF := nFv | throwError "no fuel variable {nName}"
      let some s0E := s0 | throwError "no s₀"
      let mut keep : Array Lean.Expr := #[]
      for x in xs do
        if x == pE then continue
        if x.fvarId! == nF then continue
        let d ← x.fvarId!.getDecl
        if d.type.containsFVar nF then continue
        keep := keep.push x
      let natT := Lean.mkConst ``Nat
      withLocalDeclD `F natT fun F => do
        let two62 ← mkAppOptM ``HPow.hPow #[natT, natT, natT, none, mkNatLit 2, mkNatLit 62]
        let hFty ← mkAppM ``LE.le #[F, two62]
        withLocalDeclD `hF hFty fun hF => do
          withLocalDeclD `e (Lean.mkConst ``L.Err) fun e => do
            let memE ← mkAppM ``L.St.mem #[s0E]
            let cl ← mkAppM ``L.callE #[pE, F, fE, argsE, memE]
            let clTy ← inferType cl
            let errv := mkApp3 (Lean.mkConst ``Except.error [0, 0]) (Lean.mkConst ``L.Err) clTy.getAppArgs[1]! e
            let hcty ← mkEq cl errv
            let claim ← mkAppM ``L.Arena.ErrClaim #[T, a0, e]
            withLocalDeclD `hc hcty fun hc => do
              let inner ← mkForallFVars #[F, hF, e, hc] claim
              let full ← mkForallFVars keep inner
              let lam ← mkLambdaFVars #[pE] full
              let lam := match lam with
                | .lam n t b _ => Lean.Expr.lam n t b .default
                | e => e
              let ty ← inferType lam
              addAndCompile <| .defnDecl {
                name := nm.getId, levelParams := [], type := ty, value := lam
                hints := .abbrev, safety := .safe }
  logInfo m!"defined {nm.getId}"
