module

import ConAgua.Verdict.PosTopE4
public import ConAgua.Arena.IndPosSpec.NestSeeds
public import ConAgua.Arena.IndPosSpec.UCtx
public import ConAgua.Arena.IndPosSpec.UnW2
public import ConAgua.Arena.IndRealIlpL
public import ConAgua.Arena.KnotEntry
public import ConAgua.Arena.TwinStep
public import ConRon.Bridge.Inductives.Positivity

@[expose] public section

/-!
# `nest_root` and `nest_seeds` under `StageC` (lane `indstaget`, helper `indstaget-pos`)

The census links `nestRoot_refinesC` and `nestSeeds_refinesC`, the ok halves of `nrt_ref` and
`nsd_ref` (`Verdict/PosTopE4`).
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dCtx dProg dState dCtx_ext dProg_ext dState_ext dCtors dOut dOutss kindOf)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Census -/

section census
variable {p : Prog} (L : RsLook p) (hq : KnotStageProg p) (hIlpf : IlpfF p) (hLC : LvlCacheProg p) (n : Nat) (dn : NIdx → Option ConLeche.Name) (vis : Word)
  (fe : IFEnv) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
include L hq hIlpf hLC henv

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`nest_root` refines `nestRoot`** under `StageC` (the knot's core calls; con-ron's
`nestRoot_spec`'s preconditions). -/
@[refines ConRon.Arena.nestRoot]
theorem nestRoot_refinesC (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (ctx hO hL cO cL ns oO oL : Word)
    (c : NestCtx) (holes : List EIdx) (css : List (List (IConstantVal × Nat))) (NS : NestState)
    (outss : List (List (List NestFieldKind × EIdx))) (hC : StageC dn vis fe env s₀.mem a₀)
    (hU : UCtx dn vis fe s₀.mem ctx c) (hhi : c.hiAt 0 < 2 ^ 64) (hpn : c.params.length + c.names.length < 2 ^ 64)
    (hho : decHL s₀.mem hO.toNat hL.toNat = some holes) (hhob : hO.toNat + hL.toNat ≤ iwTop s₀.mem)
    (hcl : cL.toNat = css.length) (hcb : cO.toNat + css.length ≤ iwTop s₀.mem) (hcss : CssAt s₀.mem cO.toNat css)
    (hns : NSB s₀.mem ns NS) (hout : RootOutsB s₀.mem oO.toNat oL.toNat outss)
    (houtb : oO.toNat + oL.toNat ≤ iwTop s₀.mem) (hP : PosMR s₀.mem) (hA : AbsOK s₀.mem)
    {ctxP : ConLeche.NestCtx} {holesP : List ConLeche.Expr} {cssP : List (List (ConLeche.ConstantVal × Nat))}
    {nsP : ConLeche.NestState} {outssP : List (List (List ConLeche.NestFieldKind × ConLeche.Expr))}
    (hc : ConLeche.NestCtxOk ctxP) (hholesW : ∀ x ∈ holesP, ConLeche.Expr.WScoped (ctxP.hiAt 0) x)
    (hlen : ctxP.names.length ≤ holesP.length) (hpar : ∀ x ∈ ctxP.params, ConLeche.Expr.WScoped (ctxP.hiAt 0) x)
    (hctx : dCtx a₀.store env.find? c = some ctxP) (hholesP : Frontend.denoteEList a₀.store holes = some holesP)
    (hcssP : css.mapM (dCtors a₀.store) = some cssP) (hnsP : dState a₀.store NS = some nsP)
    (houtsP : dOutss a₀.store outss = some outssP) (hcF : ∀ cs ∈ cssP, ∀ x ∈ cs, x.1.type.hasFvar = false) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_root" [vis, ctx, hO, hL, cO, cL, ns, oO, oL]
    ⦃fun r s' => LocEq s' s₀ ∧
      ∃ x a', (nestRoot V fe c holes css NS outss).run a₀ = .ok (x, a') ∧ StageC dn vis fe env s'.mem a' ∧
      IWGrow s₀.mem s'.mem ∧ RootOutsB s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat x.1 ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop s'.mem ∧ NSB s'.mem (r.tail.tail.headD 0) x.2 ∧
      PosMR s'.mem ∧ AbsOK s'.mem ∧ ConRon.Bridge.CoreStep V env fe a₀ a'; ⊤⦄ := by
  refine triple_post (RefE.triple (nrtE_spec p L n s₀ vis ctx hO hL cO cL ns oO oL)
    (nrt_ref L hq hIlpf hLC dn vis fe henv ctx hO hL c holes hc hholesW hlen hpar n hn s₀.mem a₀ cO cL ns oO oL css
      NS outss cssP nsP outssP hC hU hhi hpn hho hhob hcl hcb hcss hns hout houtb hP hA hctx hholesP hcssP hnsP
      houtsP hcF)) ?_
  rintro r s' ⟨hlc, x, a', hrun, hR⟩
  exact ⟨hlc, x, a', hrun, hR.stage, hR.grow, hR.outs, hR.outsb, hR.ns, hR.pos, hR.abs, hR.core⟩
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`nest_seeds` refines `nestSeeds`** under `StageC` (con-ron's `nestSeeds_spec`'s
preconditions). -/
@[refines ConRon.Arena.nestSeeds]
theorem nestSeeds_refinesC (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (ctx sO sL ns : Word)
    (c : NestCtx) (seeds : List (NestKey × Nat)) (NS : NestState) (hC : StageC dn vis fe env s₀.mem a₀)
    (hU : UCtx dn vis fe s₀.mem ctx c) (hhi : c.hiAt 0 < 2 ^ 64) (hsl : sL.toNat = seeds.length)
    (hsd : SeedsAt s₀.mem sO.toNat seeds) (hns : NSB s₀.mem ns NS) (hP : PosMR s₀.mem) (hA : AbsOK s₀.mem)
    {ctxP : ConLeche.NestCtx} {seedsP : List (ConLeche.NestKey × Nat)} {nsP : ConLeche.NestState}
    (hc : ConLeche.NestCtxOk ctxP) (hctx : dCtx a₀.store env.find? c = some ctxP)
    (hseedsP : seeds.mapM (fun k => (ConRon.Bridge.Inductives.dKey a₀.store k.1).map (·, k.2)) = some seedsP)
    (hnsP : dState a₀.store NS = some nsP)
    (hw : ∀ k ∈ seedsP, ∀ x ∈ k.1.ds, ConLeche.Expr.WScoped (ctxP.hiAt 0) x) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_seeds" [vis, ctx, sO, sL, ns]
    ⦃fun r s' => LocEq s' s₀ ∧
      ∃ x a', (nestSeeds V fe c seeds NS).run a₀ = .ok (x, a') ∧ StageC dn vis fe env s'.mem a' ∧
      IWGrow s₀.mem s'.mem ∧ NSB s'.mem (r.headD 0) x ∧ PosMR s'.mem ∧ AbsOK s'.mem ∧
      ConRon.Bridge.CoreStep V env fe a₀ a'; ⊤⦄ := by
  refine triple_post (RefE.triple (nsdE_spec p L n s₀ vis ctx sO sL ns)
    (nsd_ref L hq hIlpf hLC dn vis fe henv ctx c hc n hn s₀.mem a₀ sO sL ns seeds NS seedsP nsP hC hU hhi hsl hsd
      hns hP hA hctx hseedsP hnsP hw)) ?_
  rintro r s' ⟨hlc, x, a', hrun, hR⟩
  exact ⟨hlc, x, a', hrun, hR.stage, hR.grow, hR.ns, hR.pos, hR.abs, hR.core⟩
-/

end census

end L.Ind
