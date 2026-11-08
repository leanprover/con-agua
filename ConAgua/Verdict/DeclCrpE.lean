module

import ConAgua.Arena.DeclCrpT
public import ConRon.Bridge.StateOK
public import ConRon.Bridge.Checker.Hyp
public import ConRon.Bridge.Checker.Inv
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
public import ConAgua.Arena.CrOKFrame
public import ConAgua.Arena.DeclReducePin
public import ConAgua.Arena.KnotEntry
public import ConAgua.Arena.LeafFns
public import ConAgua.Arena.TwinStep
public import ConAgua.Verdict.VCtx
public import ConLeche.Verify.Shift

@[expose] public section

/-!
# The verdict claim of `check_reduce_pin`

`crp_ref`'s error half (`Arena/DeclCrpT.lean`) through the run, under the core stubs' error
claims: the three guards and the spelling test decline (`notImplemented`), the identity
certificate failing is the twin's `internal` (class `0`: the L code aborts plainly).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind
open ConRon.Bridge (CheckOK StepOK CoreSpec)

local notation "V" => ConLeche.CheckMode.verified

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`check_reduce_pin`'s error claim**, from `crp_ref` through the run. -/
theorem crpE_okT {p : Prog} (hC : CrpProg p) (hq : KnotStageProg p) (hcl : LeafClosed p)
    (hkp : CrKeep p) (hnv : closedNV p L.Checker.nvFns = true) (hcE : CoreStubsE p)
    {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn) {vis vis2 : Word} {fe2 : IFEnv}
    {env env2 : ConLeche.Env} {a : AState} {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem} {c v : Word}
    {nm : ConLeche.Name} {x : ConLeche.Expr}
    (hS : StageR vis2 fe2 m a)
    (hck : CheckOK V env (fe2.restrictTo vis.toNat) a) (henv : ConLeche.EnvWF env)
    (hok2 : StepOK env2 fe2 a) (hmem : TwinMem dn m a) (hflag : pinW m 0 ≠ 0)
    (hnm : denoteN a.store.ns (decI c) = some nm) (hvx : denoteE a.store (decI v) = some x)
    (hws : ConLeche.Expr.WScoped 0 x) (hc : c.toNat < 2 ^ 32) (hv : v.toNat < 2 ^ 32)
    (hCr : L.Stubs.CrOK m) {e : Err}
    (hce : callE p n "check_reduce_pin" [vis, vis2, c, v] m = .error e) :
    ErrClaim (checkReducePin V (fe2.restrictTo vis.toNat) fe2 (decI c) (decI v)) a e :=
  RefE.run_err (s₀ := ⟨m, Locals.init []⟩) (checkReducePin_specE p hC n _ vis vis2 c v) hnv hcE
    (crp_ref hC hq hcl hkp hdn hn hS hck henv hok2 hmem hflag hnm hvx hws hc hv hCr) hce
-/

end L.Arena
