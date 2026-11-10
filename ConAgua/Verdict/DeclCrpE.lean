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
public import ConAgua.Verdict.VCtx
public import ConLeche.Verify.Shift
public import ConAgua.Arena.IndRealApdT

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

/-- **`check_reduce_pin`'s error claim**, from `crp_ref` through the run. -/
theorem crpE_okT {p : Prog} (hC : CrpProg p) (hq : KnotStageProg p) (hcl : LeafClosed p)
    (hap : ApdF p) (hkp : CrKeep p) (hcrf : L.Ind.CrfF p) (hnv : closedNV p L.Checker.nvFns = true)
    (hcE : CoreStubsE p) (hU : UceProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {env env2 : ConLeche.Env} {a : AState} {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem} {q c v : Word}
    {ci : IConstantInfo} {nm : ConLeche.Name} {x : ConLeche.Expr}
    (hS : StageT dn vis fe m a) (hck : CheckOK false env fe a) (henv : ConLeche.EnvWF env)
    (hok2 : StepOK env2 (fe.push ci) a) (hci : decCI (erecP m) q.toNat = some ci)
    (hcn : ci.name = decI c) (hnm : denoteN a.store.ns (decI c) = some nm)
    (hvx : denoteE a.store (decI v) = some x) (hws : ConLeche.Expr.WScoped 0 x)
    (hc : c.toNat < 2 ^ 32) (hv : v.toNat < 2 ^ 32) (hCr : L.Stubs.CrOK m) {e : Err}
    (hce : callE p n "check_reduce_pin" [vis, q, c, v] m = .error e) :
    ErrClaim (checkReducePin V fe ci (decI c) (decI v)) a e :=
  RefE.run_err (s₀ := ⟨m, Locals.init []⟩) (checkReducePin_specE p hC n _ vis q c v) hnv
    { nv := hnv, core := hcE, uce := hU } (crp_ref hC hq hcl hap hkp hcrf hn hS hck henv hok2 hci hcn hnm hvx hws hc hv hCr) hce

end L.Arena
