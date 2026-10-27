import ConAgua.Arena.IndT.PosAll
import ConAgua.Census.Attr

/-!
# The positivity walk's census links under `StageC` (lane `indstaget`, helper `indstaget-pos`)

`IndPos2SpecT`'s theorems at `realCall p` (the knot's core calls): each function of the block, run by
`exec` at a fuel `n ≤ 2^62`, refines its twin from `StageC` and con-ron's preconditions of the twin
op (`nbSpec_all`: L ⊑ the word models; `nbOKC_all`: the models ⊑ the twin).
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (dCtx dProg dState dCtors dOut dGrp)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section census
variable {p : Prog} (L : NbLook p) (hq : KnotStageProg p) (hIlpf : IlpfF p) (hLC : LvlCacheProg p) (n : Nat) (dn : NIdx → Option ConLeche.Name)
  (vis : Word) (fe : IFEnv) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
include L hq hIlpf hLC henv

@[refines ConRon.Arena.nestPos]
theorem nestPos_refinesC (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (ctx fu po pl dep kb e ns : Word)
    (c : NestCtx) (prog : List NestHole) (NS : NestState)
    (h0 : StageC dn vis fe env s₀.mem a₀)
    (h1 : WCtx dn vis fe s₀.mem ctx po pl c prog)
    (h2 : H e)
    (h3 : NSB s₀.mem ns NS) (hP : PosMR s₀.mem) (hA : AbsOK s₀.mem)
    {ctxP : ConLeche.NestCtx} {progP : List ConLeche.NestHole} {eP : ConLeche.Expr} {nsP : ConLeche.NestState}
    (hc : ConLeche.NestCtxOk ctxP) (hctx : dCtx a₀.store env.find? c = some ctxP) (hprog : dProg a₀.store prog = some progP)
    (heP : denoteE a₀.store (decI e) = some eP) (hnsP : dState a₀.store NS = some nsP)
    (hwe : ConLeche.Expr.WScoped dep.toNat eP) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_pos" [vis, ctx, fu, po, pl, dep, kb, e, ns]
    ⦃fun r s' => LocEq s' s₀ ∧
      ∃ x a', (nestPos V fe c fu.toNat prog dep.toNat kb.toNat (decI e) NS).run a₀ = .ok (x, a') ∧
      StageC dn vis fe env s'.mem a' ∧ IWGrow s₀.mem s'.mem ∧ decNFK (r.headD 0) = some x.1 ∧ H (r.tail.headD 0) ∧
      decI (r.tail.headD 0) = x.2.1 ∧ NSB s'.mem (r.tail.tail.headD 0) x.2.2 ∧ PosMR s'.mem ∧ AbsOK s'.mem ∧ ConRon.Bridge.CoreStep V env fe a₀ a'; ⊤⦄ := by
  refine triple_post ((nbSpec_all L (realCall p) (realCall_spec p) n).1 s₀ vis ctx fu po pl dep kb e ns) ?_
  rintro r s' ⟨hlc, hm⟩
  have := (nbOKC_all hq hIlpf hLC henv n hn).1 s₀.mem s'.mem a₀ ctx fu po pl dep kb e ns c prog NS _ _ _ _ _ hm h0 h1 h2 h3 hP hA
    hc hctx hprog heP hnsP hwe
  exact ⟨hlc, by simpa using this⟩

@[refines_part ConRon.Arena.nestPos "binder arm (nest_pos_bind)"]
theorem nestPosBind_refinesC (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (ctx fu po pl dep kb w ns : Word)
    (c : NestCtx) (prog : List NestHole) (NS : NestState)
    (h0 : StageC dn vis fe env s₀.mem a₀)
    (h1 : WCtx dn vis fe s₀.mem ctx po pl c prog)
    (h2 : H w)
    (h3 : w >>> 28 = 6)
    (h4 : NSB s₀.mem ns NS) (hP : PosMR s₀.mem) (hA : AbsOK s₀.mem)
    {ctxP : ConLeche.NestCtx} {progP : List ConLeche.NestHole} {wP : ConLeche.Expr} {nsP : ConLeche.NestState}
    (hc : ConLeche.NestCtxOk ctxP) (hctx : dCtx a₀.store env.find? c = some ctxP) (hprog : dProg a₀.store prog = some progP)
    (hwP : denoteE a₀.store (decI w) = some wP) (hnsP : dState a₀.store NS = some nsP)
    (hww : ConLeche.Expr.WScoped dep.toNat wP) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_pos_bind" [vis, ctx, fu, po, pl, dep, kb, w, ns]
    ⦃fun r s' => LocEq s' s₀ ∧
      ∃ x a', (posBindT V fe c fu.toNat prog dep.toNat kb.toNat (c.hiAt prog.length) (decI w) NS).run a₀ = .ok (x, a') ∧
      StageC dn vis fe env s'.mem a' ∧ IWGrow s₀.mem s'.mem ∧ decNFK (r.headD 0) = some x.1 ∧ H (r.tail.headD 0) ∧
      decI (r.tail.headD 0) = x.2.1 ∧ NSB s'.mem (r.tail.tail.headD 0) x.2.2 ∧ PosMR s'.mem ∧ AbsOK s'.mem ∧ ConRon.Bridge.CoreStep V env fe a₀ a'; ⊤⦄ := by
  refine triple_post ((nbSpec_all L (realCall p) (realCall_spec p) n).2.1 s₀ vis ctx fu po pl dep kb w ns) ?_
  rintro r s' ⟨hlc, hm⟩
  have := (nbOKC_all hq hIlpf hLC henv n hn).2.1 s₀.mem s'.mem a₀ ctx fu po pl dep kb w ns c prog NS _ _ _ _ _ hm h0 h1 h2 h3 h4 hP hA
    hc hctx hprog hwP hnsP hww
  exact ⟨hlc, by simpa using this⟩

@[refines_part ConRon.Arena.nestPos "application arm (nest_pos_app)"]
theorem nestPosApp_refinesC (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (ctx fu po pl kb hi w ns : Word)
    (c : NestCtx) (prog : List NestHole) (NS : NestState)
    (h0 : StageC dn vis fe env s₀.mem a₀)
    (h1 : WCtx dn vis fe s₀.mem ctx po pl c prog)
    (h2 : hi.toNat = c.hiAt prog.length)
    (h3 : H w)
    (h4 : NSB s₀.mem ns NS) (hP : PosMR s₀.mem) (hA : AbsOK s₀.mem)
    {ctxP : ConLeche.NestCtx} {progP : List ConLeche.NestHole} {wP : ConLeche.Expr} {nsP : ConLeche.NestState}
    {dep : Nat} (hc : ConLeche.NestCtxOk ctxP) (hctx : dCtx a₀.store env.find? c = some ctxP) (hprog : dProg a₀.store prog = some progP)
    (hwP : denoteE a₀.store (decI w) = some wP) (hnsP : dState a₀.store NS = some nsP)
    (hww : ConLeche.Expr.WScoped dep wP) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_pos_app" [vis, ctx, fu, po, pl, kb, hi, w, ns]
    ⦃fun r s' => LocEq s' s₀ ∧
      ∃ x a', (posAppT V fe c fu.toNat prog kb.toNat hi.toNat (decI w) NS).run a₀ = .ok (x, a') ∧
      StageC dn vis fe env s'.mem a' ∧ IWGrow s₀.mem s'.mem ∧ decNFK (r.headD 0) = some x.1 ∧ x.2.1 = decI w ∧
      NSB s'.mem (r.tail.headD 0) x.2.2 ∧ PosMR s'.mem ∧ AbsOK s'.mem ∧ ConRon.Bridge.CoreStep V env fe a₀ a'; ⊤⦄ := by
  refine triple_post ((nbSpec_all L (realCall p) (realCall_spec p) n).2.2.1 s₀ vis ctx fu po pl kb hi w ns) ?_
  rintro r s' ⟨hlc, hm⟩
  have := (nbOKC_all hq hIlpf hLC henv n hn).2.2.1 s₀.mem s'.mem a₀ ctx fu po pl kb hi w ns c prog NS _ _ _ _ _ _ hm h0 h1 h2 h3 h4 hP hA
    hc hctx hprog hwP hnsP hww
  exact ⟨hlc, by simpa using this⟩

@[refines ConRon.Arena.nestCont]
theorem nestCont_refinesC (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (ctx fu po pl kb nn us aO aL ns : Word)
    (c : NestCtx) (prog : List NestHole) (args : List EIdx) (NS : NestState)
    (h0 : StageC dn vis fe env s₀.mem a₀)
    (h1 : WCtx dn vis fe s₀.mem ctx po pl c prog)
    (h2 : H nn)
    (h3 : H us)
    (h4 : decHL s₀.mem aO.toNat aL.toNat = some args)
    (h5 : aO.toNat + aL.toNat ≤ iwTop s₀.mem)
    (h6 : NSB s₀.mem ns NS) (hP : PosMR s₀.mem) (hA : AbsOK s₀.mem)
    {ctxP : ConLeche.NestCtx} {progP : List ConLeche.NestHole} {nP : ConLeche.Name}
    {usP : List ConLeche.Level} {argsP : List ConLeche.Expr} {nsP : ConLeche.NestState} {dep : Nat}
    (hc : ConLeche.NestCtxOk ctxP) (hctx : dCtx a₀.store env.find? c = some ctxP) (hprog : dProg a₀.store prog = some progP)
    (hnP : denoteN a₀.store.ns (decI nn) = some nP) (husP : denoteLs a₀.store.lss (decI us) = some usP)
    (hargsP : Frontend.denoteEList a₀.store args = some argsP) (hnsP : dState a₀.store NS = some nsP)
    (hwargs : ∀ x ∈ argsP, ConLeche.Expr.WScoped dep x) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_cont" [vis, ctx, fu, po, pl, kb, nn, us, aO, aL, ns]
    ⦃fun r s' => LocEq s' s₀ ∧
      ∃ x a', (nestCont V fe c fu.toNat prog kb.toNat (decI nn) (decI us) args NS).run a₀ = .ok (x, a') ∧
      StageC dn vis fe env s'.mem a' ∧ IWGrow s₀.mem s'.mem ∧ decNFK (r.headD 0) = some x.1 ∧
      NSB s'.mem (r.tail.headD 0) x.2 ∧ PosMR s'.mem ∧ AbsOK s'.mem ∧ ConRon.Bridge.CoreStep V env fe a₀ a'; ⊤⦄ := by
  refine triple_post ((nbSpec_all L (realCall p) (realCall_spec p) n).2.2.2.1 s₀ vis ctx fu po pl kb nn us aO aL ns) ?_
  rintro r s' ⟨hlc, hm⟩
  have := (nbOKC_all hq hIlpf hLC henv n hn).2.2.2.1 s₀.mem s'.mem a₀ ctx fu po pl kb nn us aO aL ns c prog args NS _ _ _ _ _ _ _ _ hm h0 h1 h2 h3 h4 h5 h6 hP hA
    hc hctx hprog hnP husP hargsP hnsP hwargs
  exact ⟨hlc, by simpa using this⟩

@[refines ConRon.Arena.nestContKey]
theorem nestContKey_refinesC (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (ctx fu po pl kb nn us dO dL nPc cty ns : Word)
    (c : NestCtx) (prog : List NestHole) (ds : List EIdx) (NS : NestState)
    (h0 : StageC dn vis fe env s₀.mem a₀)
    (h1 : WCtx dn vis fe s₀.mem ctx po pl c prog)
    (h2 : H nn)
    (h3 : H us)
    (h4 : DecB (fun m => (decHL m dO.toNat dL.toNat : Option (List EIdx))) s₀.mem ds)
    (h5 : dO.toNat + dL.toNat ≤ iwTop s₀.mem)
    (h6 : H cty)
    (h7 : NSB s₀.mem ns NS) (hP : PosMR s₀.mem) (hA : AbsOK s₀.mem)
    {ctxP : ConLeche.NestCtx} {progP : List ConLeche.NestHole} {nP : ConLeche.Name}
    {usP : List ConLeche.Level} {dsP : List ConLeche.Expr} {ctyP : ConLeche.Expr} {nsP : ConLeche.NestState}
    (hc : ConLeche.NestCtxOk ctxP) (hctx : dCtx a₀.store env.find? c = some ctxP) (hprog : dProg a₀.store prog = some progP)
    (hnP : denoteN a₀.store.ns (decI nn) = some nP) (husP : denoteLs a₀.store.lss (decI us) = some usP)
    (hdsP : Frontend.denoteEList a₀.store ds = some dsP) (hctyP : denoteE a₀.store (decI cty) = some ctyP)
    (hnsP : dState a₀.store NS = some nsP)
    (hwds : ∀ d ∈ dsP, ConLeche.Expr.WScoped (ctxP.hiAt progP.length) d)
    (hni : ∀ d, (∀ y ∈ dsP, ConLeche.Expr.WScoped d y) → ConLeche.Expr.WScoped d ctyP) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_cont_key" [vis, ctx, fu, po, pl, kb, nn, us, dO, dL, nPc, cty, ns]
    ⦃fun r s' => LocEq s' s₀ ∧
      ∃ x a', (nestContKey V fe c fu.toNat prog kb.toNat (decI nn) (decI us) ds nPc.toNat (decI cty) NS).run a₀ = .ok (x, a') ∧
      StageC dn vis fe env s'.mem a' ∧ IWGrow s₀.mem s'.mem ∧ decNFK (r.headD 0) = some x.1 ∧
      NSB s'.mem (r.tail.headD 0) x.2 ∧ PosMR s'.mem ∧ AbsOK s'.mem ∧ ConRon.Bridge.CoreStep V env fe a₀ a'; ⊤⦄ := by
  refine triple_post ((nbSpec_all L (realCall p) (realCall_spec p) n).2.2.2.2.1 s₀ vis ctx fu po pl kb nn us dO dL nPc cty ns) ?_
  rintro r s' ⟨hlc, hm⟩
  have := (nbOKC_all hq hIlpf hLC henv n hn).2.2.2.2.1 s₀.mem s'.mem a₀ ctx fu po pl kb nn us dO dL nPc cty ns c prog ds NS _ _ _ _ _ _ _ _ hm h0 h1 h2 h3 h4 h5 h6 h7 hP hA
    hc hctx hprog hnP husP hdsP hctyP hnsP hwds hni
  exact ⟨hlc, by simpa using this⟩

@[refines ConRon.Arena.nestContNew]
theorem nestContNew_refinesC (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (ctx fu po pl kb nn us dO dL nPc cty ns : Word)
    (c : NestCtx) (prog : List NestHole) (ds : List EIdx) (NS : NestState)
    (h0 : StageC dn vis fe env s₀.mem a₀)
    (h1 : WCtx dn vis fe s₀.mem ctx po pl c prog)
    (h2 : H nn)
    (h3 : H us)
    (h4 : DecB (fun m => (decHL m dO.toNat dL.toNat : Option (List EIdx))) s₀.mem ds)
    (h5 : dO.toNat + dL.toNat ≤ iwTop s₀.mem)
    (h6 : H cty)
    (h7 : NSB s₀.mem ns NS) (hP : PosMR s₀.mem) (hA : AbsOK s₀.mem)
    {ctxP : ConLeche.NestCtx} {progP : List ConLeche.NestHole} {nP : ConLeche.Name}
    {usP : List ConLeche.Level} {dsP : List ConLeche.Expr} {ctyP : ConLeche.Expr} {nsP : ConLeche.NestState}
    (hc : ConLeche.NestCtxOk ctxP) (hctx : dCtx a₀.store env.find? c = some ctxP) (hprog : dProg a₀.store prog = some progP)
    (hnP : denoteN a₀.store.ns (decI nn) = some nP) (husP : denoteLs a₀.store.lss (decI us) = some usP)
    (hdsP : Frontend.denoteEList a₀.store ds = some dsP) (hctyP : denoteE a₀.store (decI cty) = some ctyP)
    (hnsP : dState a₀.store NS = some nsP)
    (hwds : ∀ d ∈ dsP, ConLeche.Expr.WScoped (ctxP.hiAt progP.length) d)
    (hni : ∀ d, (∀ y ∈ dsP, ConLeche.Expr.WScoped d y) → ConLeche.Expr.WScoped d ctyP) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_cont_new" [vis, ctx, fu, po, pl, kb, nn, us, dO, dL, nPc, cty, ns]
    ⦃fun r s' => LocEq s' s₀ ∧
      ∃ x a', (nestContNew V fe c fu.toNat prog kb.toNat (decI nn) (decI us) ds nPc.toNat (decI cty) NS).run a₀ = .ok (x, a') ∧
      StageC dn vis fe env s'.mem a' ∧ IWGrow s₀.mem s'.mem ∧ decNFK (r.headD 0) = some x.1 ∧
      NSB s'.mem (r.tail.headD 0) x.2 ∧ PosMR s'.mem ∧ AbsOK s'.mem ∧ ConRon.Bridge.CoreStep V env fe a₀ a'; ⊤⦄ := by
  refine triple_post ((nbSpec_all L (realCall p) (realCall_spec p) n).2.2.2.2.2.1 s₀ vis ctx fu po pl kb nn us dO dL nPc cty ns) ?_
  rintro r s' ⟨hlc, hm⟩
  have := (nbOKC_all hq hIlpf hLC henv n hn).2.2.2.2.2.1 s₀.mem s'.mem a₀ ctx fu po pl kb nn us dO dL nPc cty ns c prog ds NS _ _ _ _ _ _ _ _ hm h0 h1 h2 h3 h4 h5 h6 h7 hP hA
    hc hctx hprog hnP husP hdsP hctyP hnsP hwds hni
  exact ⟨hlc, by simpa using this⟩

@[refines ConRon.Arena.nestFrame]
theorem nestFrame_refinesC (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (ctx fu po pl hi us dO dL nPc gO gL ns : Word)
    (c : NestCtx) (prog : List NestHole) (ds : List EIdx) (grp : List (NIdx × EIdx)) (NS : NestState)
    (h0 : StageC dn vis fe env s₀.mem a₀)
    (h1 : WCtx dn vis fe s₀.mem ctx po pl c prog)
    (h2 : hi.toNat = c.hiAt prog.length)
    (h3 : H us)
    (h4 : DecB (fun m => (decHL m dO.toNat dL.toNat : Option (List EIdx))) s₀.mem ds)
    (h5 : dO.toNat + dL.toNat ≤ iwTop s₀.mem)
    (h6 : gL.toNat = grp.length)
    (h7 : gO.toNat + grp.length ≤ iwTop s₀.mem)
    (h8 : GrpAt s₀.mem gO.toNat grp)
    (h9 : NSB s₀.mem ns NS) (hP : PosMR s₀.mem) (hA : AbsOK s₀.mem)
    {ctxP : ConLeche.NestCtx} {progP : List ConLeche.NestHole} {usP : List ConLeche.Level}
    {dsP : List ConLeche.Expr} {grpP : List (ConLeche.Name × ConLeche.Expr)} {nsP : ConLeche.NestState}
    (hc : ConLeche.NestCtxOk ctxP) (hctx : dCtx a₀.store env.find? c = some ctxP) (hprog : dProg a₀.store prog = some progP)
    (husP : denoteLs a₀.store.lss (decI us) = some usP) (hdsP : Frontend.denoteEList a₀.store ds = some dsP)
    (hgrpP : dGrp a₀.store grp = some grpP) (hnsP : dState a₀.store NS = some nsP)
    (hwds : ∀ d ∈ dsP, ConLeche.Expr.WScoped hi.toNat d) (hwg : ∀ x ∈ grpP, ConLeche.Expr.WScoped hi.toNat x.2) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_frame" [vis, ctx, fu, po, pl, hi, us, dO, dL, nPc, gO, gL, ns]
    ⦃fun r s' => LocEq s' s₀ ∧
      ∃ x a', (nestFrame V fe c fu.toNat prog hi.toNat (decI us) ds nPc.toNat grp NS).run a₀ = .ok (x, a') ∧
      StageC dn vis fe env s'.mem a' ∧ IWGrow s₀.mem s'.mem ∧ NSB s'.mem (r.headD 0) x ∧ PosMR s'.mem ∧ AbsOK s'.mem ∧ ConRon.Bridge.CoreStep V env fe a₀ a'; ⊤⦄ := by
  refine triple_post ((nbSpec_all L (realCall p) (realCall_spec p) n).2.2.2.2.2.2.1 s₀ vis ctx fu po pl hi us dO dL nPc gO gL ns) ?_
  rintro r s' ⟨hlc, hm⟩
  have := (nbOKC_all hq hIlpf hLC henv n hn).2.2.2.2.2.2.1 s₀.mem s'.mem a₀ ctx fu po pl hi us dO dL nPc gO gL ns c prog ds grp NS _ _ _ _ _ _ _ hm h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hP hA
    hc hctx hprog husP hdsP hgrpP hnsP hwds hwg
  exact ⟨hlc, by simpa using this⟩

@[refines ConRon.Arena.nestCtors]
theorem nestCtors_refinesC (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (ctx root fu po pl hi us dO dL no nl hO hL cO cL ns oO oL : Word)
    (c : NestCtx) (prog : List NestHole) (ds : List EIdx) (names : List NIdx) (holes : List EIdx) (cs : List (IConstantVal × Nat)) (NS : NestState) (outs : List (List NestFieldKind × EIdx))
    (h0 : StageC dn vis fe env s₀.mem a₀)
    (h1 : WCtx dn vis fe s₀.mem ctx po pl c prog)
    (h2 : CtorsCtx s₀.mem us dO dL no nl hO hL ds names holes)
    (h3 : cL.toNat = cs.length)
    (h4 : cO.toNat + cs.length ≤ iwTop s₀.mem)
    (h5 : CsAt s₀.mem cO.toNat cs (· < iwTop s₀.mem))
    (h6 : NSB s₀.mem ns NS)
    (h7 : OutsB s₀.mem oO.toNat oL.toNat outs)
    (h8 : oO.toNat + oL.toNat ≤ iwTop s₀.mem) (hP : PosMR s₀.mem) (hA : AbsOK s₀.mem)
    {ctxP : ConLeche.NestCtx} {progP : List ConLeche.NestHole} {usP : List ConLeche.Level}
    {dsP : List ConLeche.Expr} {namesP : List ConLeche.Name} {holesP : List ConLeche.Expr}
    {csP : List (ConLeche.ConstantVal × Nat)} {nsP : ConLeche.NestState}
    {outsP : List (List ConLeche.NestFieldKind × ConLeche.Expr)}
    (hc : ConLeche.NestCtxOk ctxP) (hctx : dCtx a₀.store env.find? c = some ctxP) (hprog : dProg a₀.store prog = some progP)
    (hpre : CtorsPre a₀.store (decI us) ds names holes hi.toNat usP dsP namesP holesP)
    (hcsP : dCtors a₀.store cs = some csP) (hcsF : ∀ x ∈ csP, x.1.type.hasFvar = false)
    (hnsP : dState a₀.store NS = some nsP) (houtsP : outs.mapM (dOut a₀.store) = some outsP) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctors" [vis, ctx, root, fu, po, pl, hi, us, dO, dL, no, nl, hO, hL, cO, cL, ns, oO, oL]
    ⦃fun r s' => LocEq s' s₀ ∧
      ∃ x a', (nestCtors V fe c (decide (root ≠ 0)) fu.toNat prog hi.toNat (decI us) ds names holes cs NS outs).run a₀ = .ok (x, a') ∧
      StageC dn vis fe env s'.mem a' ∧ IWGrow s₀.mem s'.mem ∧
      OutsB s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat x.1 ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop s'.mem ∧ NSB s'.mem (r.tail.tail.headD 0) x.2 ∧ PosMR s'.mem ∧ AbsOK s'.mem ∧ ConRon.Bridge.CoreStep V env fe a₀ a'; ⊤⦄ := by
  refine triple_post ((nbSpec_all L (realCall p) (realCall_spec p) n).2.2.2.2.2.2.2.1 s₀ vis ctx root fu po pl hi us dO dL no nl hO hL cO cL ns oO oL) ?_
  rintro r s' ⟨hlc, hm⟩
  have := (nbOKC_all hq hIlpf hLC henv n hn).2.2.2.2.2.2.2.1 s₀.mem s'.mem a₀ ctx root fu po pl hi us dO dL no nl hO hL cO cL ns oO oL c prog ds names holes cs NS outs _ _ _ _ _ _ _ _ _ _ hm h0 h1 h2 h3 h4 h5 h6 h7 h8 hP hA
    hc hctx hprog hpre hcsP hcsF hnsP houtsP
  exact ⟨hlc, by simpa using this⟩

@[refines_part ConRon.Arena.nestCtors "one constructor (nest_ctors_one)"]
theorem nestCtorsOne_refinesC (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (ctx root fu po pl hi us dO dL no nl hO hL cv nF ns : Word)
    (c : NestCtx) (prog : List NestHole) (ds : List EIdx) (names : List NIdx) (holes : List EIdx) (cvv : IConstantVal) (NS : NestState)
    (h0 : StageC dn vis fe env s₀.mem a₀)
    (h1 : WCtx dn vis fe s₀.mem ctx po pl c prog)
    (h2 : CtorsCtx s₀.mem us dO dL no nl hO hL ds names holes)
    (h3 : decCV (erecP s₀.mem) cv.toNat = some cvv)
    (h4 : cv.toNat + 3 < 2 ^ 64)
    (h5 : NSB s₀.mem ns NS) (hP : PosMR s₀.mem) (hA : AbsOK s₀.mem)
    {ctxP : ConLeche.NestCtx} {progP : List ConLeche.NestHole} {usP : List ConLeche.Level}
    {dsP : List ConLeche.Expr} {namesP : List ConLeche.Name} {holesP : List ConLeche.Expr}
    {cvP : ConLeche.ConstantVal} {nsP : ConLeche.NestState}
    (hc : ConLeche.NestCtxOk ctxP) (hctx : dCtx a₀.store env.find? c = some ctxP) (hprog : dProg a₀.store prog = some progP)
    (hpre : CtorsPre a₀.store (decI us) ds names holes hi.toNat usP dsP namesP holesP)
    (hcvP : Frontend.denoteCV a₀.store cvv = some cvP) (hcl : cvP.type.hasFvar = false)
    (hnsP : dState a₀.store NS = some nsP) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctors_one" [vis, ctx, root, fu, po, pl, hi, us, dO, dL, no, nl, hO, hL, cv, nF, ns]
    ⦃fun r s' => LocEq s' s₀ ∧
      ∃ ks closed NS3 a', (∀ {β : Type} (K : List NestFieldKind × EIdx → NestState → AM β), (oneK V fe c fu.toNat prog (decide (root ≠ 0)) hi.toNat (decI us) ds names holes cvv nF.toNat NS K).run a₀ = (K (ks, closed) NS3).run a') ∧
      StageC dn vis fe env s'.mem a' ∧ IWGrow s₀.mem s'.mem ∧
      KlB s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat ks ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop s'.mem ∧ H (r.tail.tail.headD 0) ∧
      decI (r.tail.tail.headD 0) = closed ∧ NSB s'.mem (r.tail.tail.tail.headD 0) NS3 ∧ PosMR s'.mem ∧ AbsOK s'.mem ∧
      ConRon.Bridge.CoreStep V env fe a₀ a' ∧
      (∃ oP, dOut a'.store (ks, closed) = some oP ∧ ConLeche.Expr.WScoped hi.toNat oP.2) ∧
      (∃ nsP3, dState a'.store NS3 = some nsP3); ⊤⦄ := by
  refine triple_post ((nbSpec_all L (realCall p) (realCall_spec p) n).2.2.2.2.2.2.2.2.1 s₀ vis ctx root fu po pl hi us dO dL no nl hO hL cv nF ns) ?_
  rintro r s' ⟨hlc, hm⟩
  have := (nbOKC_all hq hIlpf hLC henv n hn).2.2.2.2.2.2.2.2.1 s₀.mem s'.mem a₀ ctx root fu po pl hi us dO dL no nl hO hL cv nF ns c prog ds names holes cvv NS _ _ _ _ _ _ _ _ _ hm h0 h1 h2 h3 h4 h5 hP hA
    hc hctx hprog hpre hcvP hcl hnsP
  exact ⟨hlc, by simpa using this⟩

@[refines_part ConRon.Arena.nestCtors "field walk (nest_ctors_walk)"]
theorem nestCtorsWalk_refinesC (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (ctx root fu po pl hi nF crest ns : Word)
    (c : NestCtx) (prog : List NestHole) (NS : NestState)
    (h0 : StageC dn vis fe env s₀.mem a₀)
    (h1 : WCtx dn vis fe s₀.mem ctx po pl c prog)
    (h2 : H crest)
    (h3 : NSB s₀.mem ns NS) (hP : PosMR s₀.mem) (hA : AbsOK s₀.mem)
    {ctxP : ConLeche.NestCtx} {progP : List ConLeche.NestHole} {crestP : ConLeche.Expr} {nsP : ConLeche.NestState}
    (hc : ConLeche.NestCtxOk ctxP) (hctx : dCtx a₀.store env.find? c = some ctxP) (hprog : dProg a₀.store prog = some progP)
    (hcrP : denoteE a₀.store (decI crest) = some crestP) (hnsP : dState a₀.store NS = some nsP)
    (hwc : ConLeche.Expr.WScoped hi.toNat crestP) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctors_walk" [vis, ctx, root, fu, po, pl, hi, nF, crest, ns]
    ⦃fun r s' => LocEq s' s₀ ∧
      ∃ ks nds cur ns2 closed a', (∀ {β : Type} (K : List NestFieldKind → List EIdx → EIdx → NestState → EIdx → AM β), (walkK V fe c fu.toNat prog (decide (root ≠ 0)) hi.toNat nF.toNat (decI crest) NS K).run a₀ = (K ks nds cur ns2 closed).run a') ∧
      StageC dn vis fe env s'.mem a' ∧ IWGrow s₀.mem s'.mem ∧
      KlB s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat ks ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop s'.mem ∧ ks.length = nF.toNat ∧
      H (r.tail.tail.headD 0) ∧ decI (r.tail.tail.headD 0) = cur ∧ H (r.tail.tail.tail.headD 0) ∧
      decI (r.tail.tail.tail.headD 0) = closed ∧ NSB s'.mem (r.tail.tail.tail.tail.headD 0) ns2 ∧ PosMR s'.mem ∧ AbsOK s'.mem ∧
      ConRon.Bridge.CoreStep V env fe a₀ a' ∧
      ∃ ndsP curP nsP2, Frontend.denoteEList a'.store nds = some ndsP ∧ denoteE a'.store cur = some curP ∧
        dState a'.store ns2 = some nsP2 ∧
        denoteE a'.store closed = some (ConLeche.closeTelescope ndsP hi.toNat curP) ∧
        (∀ (i : Nat) (nd : ConLeche.Expr), ndsP[i]? = some nd → ConLeche.Expr.WScoped (hi.toNat + i) nd) ∧
        ConLeche.Expr.WScoped (hi.toNat + ndsP.length) curP; ⊤⦄ := by
  refine triple_post ((nbSpec_all L (realCall p) (realCall_spec p) n).2.2.2.2.2.2.2.2.2.1 s₀ vis ctx root fu po pl hi nF crest ns) ?_
  rintro r s' ⟨hlc, hm⟩
  have := (nbOKC_all hq hIlpf hLC henv n hn).2.2.2.2.2.2.2.2.2.1 s₀.mem s'.mem a₀ ctx root fu po pl hi nF crest ns c prog NS _ _ _ _ _ hm h0 h1 h2 h3 hP hA
    hc hctx hprog hcrP hnsP hwc
  exact ⟨hlc, by simpa using this⟩

@[refines ConRon.Arena.nestFields]
theorem nestFields_refinesC (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (ctx fu po pl base nF j cur ns kO kL dO dL : Word)
    (c : NestCtx) (prog : List NestHole) (NS : NestState) (ks : List NestFieldKind) (nds : List EIdx)
    (h0 : StageC dn vis fe env s₀.mem a₀)
    (h1 : WCtx dn vis fe s₀.mem ctx po pl c prog)
    (h2 : H cur)
    (h3 : NSB s₀.mem ns NS)
    (h4 : KlB s₀.mem kO.toNat kL.toNat ks)
    (h5 : kO.toNat + kL.toNat ≤ iwTop s₀.mem)
    (h6 : decHL s₀.mem dO.toNat dL.toNat = some nds)
    (h7 : dO.toNat + dL.toNat ≤ iwTop s₀.mem) (hP : PosMR s₀.mem) (hA : AbsOK s₀.mem)
    {ctxP : ConLeche.NestCtx} {progP : List ConLeche.NestHole} {curP : ConLeche.Expr}
    {nsP : ConLeche.NestState} {ndsP : List ConLeche.Expr}
    (hc : ConLeche.NestCtxOk ctxP) (hctx : dCtx a₀.store env.find? c = some ctxP) (hprog : dProg a₀.store prog = some progP)
    (hcurP : denoteE a₀.store (decI cur) = some curP) (hnsP : dState a₀.store NS = some nsP)
    (hndsP : Frontend.denoteEList a₀.store nds = some ndsP)
    (hw : ConLeche.Expr.WScoped (base.toNat + j.toNat) curP) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_fields" [vis, ctx, fu, po, pl, base, nF, j, cur, ns, kO, kL, dO, dL]
    ⦃fun r s' => LocEq s' s₀ ∧
      ∃ x a', (nestFields V fe c fu.toNat prog base.toNat nF.toNat j.toNat (decI cur) NS ks nds).run a₀ = .ok (x, a') ∧
      StageC dn vis fe env s'.mem a' ∧ IWGrow s₀.mem s'.mem ∧
      KlB s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat x.1 ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop s'.mem ∧
      decHL s'.mem (r.tail.tail.headD 0).toNat (r.tail.tail.tail.headD 0).toNat = some x.2.1 ∧
      (r.tail.tail.headD 0).toNat + (r.tail.tail.tail.headD 0).toNat ≤ iwTop s'.mem ∧
      H (r.tail.tail.tail.tail.headD 0) ∧ decI (r.tail.tail.tail.tail.headD 0) = x.2.2.1 ∧
      NSB s'.mem (r.tail.tail.tail.tail.tail.headD 0) x.2.2.2 ∧ x.1.length = ks.length + nF.toNat ∧
      x.2.1.length = nds.length + nF.toNat ∧ (nF.toNat = 0 ∨ base.toNat + j.toNat + nF.toNat < 2 ^ 64) ∧ PosMR s'.mem ∧ AbsOK s'.mem ∧ ConRon.Bridge.CoreStep V env fe a₀ a'; ⊤⦄ := by
  refine triple_post ((nbSpec_all L (realCall p) (realCall_spec p) n).2.2.2.2.2.2.2.2.2.2 s₀ vis ctx fu po pl base nF j cur ns kO kL dO dL) ?_
  rintro r s' ⟨hlc, hm⟩
  have := (nbOKC_all hq hIlpf hLC henv n hn).2.2.2.2.2.2.2.2.2.2 s₀.mem s'.mem a₀ ctx fu po pl base nF j cur ns kO kL dO dL c prog NS ks nds _ _ _ _ _ _ hm h0 h1 h2 h3 h4 h5 h6 h7 hP hA
    hc hctx hprog hcurP hnsP hndsP hw
  exact ⟨hlc, by simpa using this⟩

end census

end L.Ind
