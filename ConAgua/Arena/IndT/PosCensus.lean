module

import ConAgua.Arena.IndT.PosAll
public import ConAgua.Arena.IndT.PosFkc
public import ConAgua.Verdict.PosE
public import ConRon.Bridge.Inductives.Positivity

@[expose] public section

/-!
# The positivity walk's census links under `StageC` (lane `indstaget`, helper `indstaget-pos`)

`IndPos2SpecT`'s theorems at `realCall p` (the knot's core calls): each function of the block, run by
`exec` at a fuel `n ≤ 2^62`, refines its twin from `StageC` and con-ron's preconditions of the twin
op, from the block's refinements (`nbRef_all`, through `RefE.triple`).
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (dCtx dProg dState dCtors dOut dGrp)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section census
variable {p : Prog} (L : NbLook p) (hq : KnotStageProg p) (hIlpf : IlpfF p) (hLC : LvlCacheProg p)
  (hFt : FtProg p) (hFk : FkcProg p) (n : Nat) (dn : NIdx → Option ConLeche.Name)
  (vis : Word) (fe : IFEnv) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
include L hq hIlpf hLC hFt hFk henv

@[refines ConRon.Arena.nestPos]
theorem nestPos_refinesC (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (ctx fu po pl dep kb e ns : Word) (c : NestCtx) (prog : List NestHole) (NS : NestState) (ctxP : ConLeche.NestCtx) (progP : List ConLeche.NestHole) (eP : ConLeche.Expr) (nsP : ConLeche.NestState)
    (h0 : StageC dn vis fe env s₀.mem a₀) (h1 : WCtx dn vis fe s₀.mem ctx po pl c prog) (h2 : H e) (h3 : NSB s₀.mem ns NS) (h4 : PosMR s₀.mem) (h5 : AbsOK s₀.mem) (h6 : ConLeche.NestCtxOk ctxP) (h7 : dCtx a₀.store env.find? c = some ctxP) (h8 : dProg a₀.store prog = some progP) (h9 : denoteE a₀.store (decI e) = some eP) (h10 : dState a₀.store NS = some nsP) (h11 : ConLeche.Expr.WScoped dep.toNat eP) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_pos" [vis, ctx, fu, po, pl, dep, kb, e, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ ∃ x a', (nestPos V fe c fu.toNat prog dep.toNat kb.toNat (decI e) NS).run a₀ = .ok (x, a') ∧
      PosPost dn vis fe env a₀ s₀.mem r s'.mem x a'; ⊤⦄ := by
  refine triple_post (RefE.triple (npE_spec p L.ppos n s₀ vis ctx fu po pl dep kb e ns)
    ((nbRef_all L hq hIlpf hLC hFt hFk henv n hn).pos s₀.mem a₀ ctx fu po pl dep kb e ns c prog NS ctxP progP eP nsP
      h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11)) ?_
  rintro r s' ⟨hlc, x, a', hrun, hR⟩
  exact ⟨hlc, x, a', hrun, hR⟩

@[refines_part ConRon.Arena.nestPos "binder arm (nest_pos_bind)"]
theorem nestPosBind_refinesC (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (ctx fu po pl dep kb w ns : Word) (c : NestCtx) (prog : List NestHole) (NS : NestState) (ctxP : ConLeche.NestCtx) (progP : List ConLeche.NestHole) (wP : ConLeche.Expr) (nsP : ConLeche.NestState)
    (h0 : StageC dn vis fe env s₀.mem a₀) (h1 : WCtx dn vis fe s₀.mem ctx po pl c prog) (h2 : H w) (h3 : tagW w = 6) (h4 : NSB s₀.mem ns NS) (h5 : PosMR s₀.mem) (h6 : AbsOK s₀.mem) (h7 : ConLeche.NestCtxOk ctxP) (h8 : dCtx a₀.store env.find? c = some ctxP) (h9 : dProg a₀.store prog = some progP) (h10 : denoteE a₀.store (decI w) = some wP) (h11 : dState a₀.store NS = some nsP) (h12 : ConLeche.Expr.WScoped dep.toNat wP) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_pos_bind" [vis, ctx, fu, po, pl, dep, kb, w, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ ∃ x a', (posBindT V fe c fu.toNat prog dep.toNat kb.toNat (c.hiAt prog.length) (decI w) NS).run a₀ = .ok (x, a') ∧
      PosPost dn vis fe env a₀ s₀.mem r s'.mem x a'; ⊤⦄ := by
  refine triple_post (RefE.triple (npbE_spec p L.pbind n s₀ vis ctx fu po pl dep kb w ns)
    ((nbRef_all L hq hIlpf hLC hFt hFk henv n hn).bind s₀.mem a₀ ctx fu po pl dep kb w ns c prog NS ctxP progP wP nsP
      h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12)) ?_
  rintro r s' ⟨hlc, x, a', hrun, hR⟩
  exact ⟨hlc, x, a', hrun, hR⟩

@[refines_part ConRon.Arena.nestPos "application arm (nest_pos_app)"]
theorem nestPosApp_refinesC (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (ctx fu po pl kb hi w ns : Word) (c : NestCtx) (prog : List NestHole) (NS : NestState) (ctxP : ConLeche.NestCtx) (progP : List ConLeche.NestHole) (wP : ConLeche.Expr) (nsP : ConLeche.NestState) (dep : Nat)
    (h0 : StageC dn vis fe env s₀.mem a₀) (h1 : WCtx dn vis fe s₀.mem ctx po pl c prog) (h2 : hi.toNat = c.hiAt prog.length) (h3 : H w) (h4 : NSB s₀.mem ns NS) (h5 : PosMR s₀.mem) (h6 : AbsOK s₀.mem) (h7 : ConLeche.NestCtxOk ctxP) (h8 : dCtx a₀.store env.find? c = some ctxP) (h9 : dProg a₀.store prog = some progP) (h10 : denoteE a₀.store (decI w) = some wP) (h11 : dState a₀.store NS = some nsP) (h12 : ConLeche.Expr.WScoped dep wP) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_pos_app" [vis, ctx, fu, po, pl, kb, hi, w, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ ∃ x a', (posAppT V fe c fu.toNat prog kb.toNat hi.toNat (decI w) NS).run a₀ = .ok (x, a') ∧
      AppPost dn vis fe env a₀ s₀.mem w r s'.mem x a'; ⊤⦄ := by
  refine triple_post (RefE.triple (npaE_spec p L.papp n s₀ vis ctx fu po pl kb hi w ns)
    ((nbRef_all L hq hIlpf hLC hFt hFk henv n hn).app s₀.mem a₀ ctx fu po pl kb hi w ns c prog NS ctxP progP wP nsP dep
      h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12)) ?_
  rintro r s' ⟨hlc, x, a', hrun, hR⟩
  exact ⟨hlc, x, a', hrun, hR⟩

@[refines ConRon.Arena.nestCont]
theorem nestCont_refinesC (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (ctx fu po pl kb nn us aO aL ns : Word) (c : NestCtx) (prog : List NestHole) (args : List EIdx) (NS : NestState) (ctxP : ConLeche.NestCtx) (progP : List ConLeche.NestHole) (nP : ConLeche.Name) (usP : List ConLeche.Level) (argsP : List ConLeche.Expr) (nsP : ConLeche.NestState) (dep : Nat)
    (h0 : StageC dn vis fe env s₀.mem a₀) (h1 : WCtx dn vis fe s₀.mem ctx po pl c prog) (h2 : H nn) (h3 : H us) (h4 : decHL s₀.mem aO.toNat aL.toNat = some args) (h5 : aO.toNat + aL.toNat ≤ iwTop s₀.mem) (h6 : NSB s₀.mem ns NS) (h7 : PosMR s₀.mem) (h8 : AbsOK s₀.mem) (h9 : ConLeche.NestCtxOk ctxP) (h10 : dCtx a₀.store env.find? c = some ctxP) (h11 : dProg a₀.store prog = some progP) (h12 : denoteN a₀.store.ns (decI nn) = some nP) (h13 : denoteLs a₀.store.lss (decI us) = some usP) (h14 : Frontend.denoteEList a₀.store args = some argsP) (h15 : dState a₀.store NS = some nsP) (h16 : (∀ x ∈ argsP, ConLeche.Expr.WScoped dep x)) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_cont" [vis, ctx, fu, po, pl, kb, nn, us, aO, aL, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ ∃ x a', (nestCont V fe c fu.toNat prog kb.toNat (decI nn) (decI us) args NS).run a₀ = .ok (x, a') ∧
      KindPost dn vis fe env a₀ s₀.mem r s'.mem x a'; ⊤⦄ := by
  refine triple_post (RefE.triple (ncE_spec p L.pcont n s₀ vis ctx fu po pl kb nn us aO aL ns)
    ((nbRef_all L hq hIlpf hLC hFt hFk henv n hn).cont s₀.mem a₀ ctx fu po pl kb nn us aO aL ns c prog args NS ctxP progP nP usP argsP nsP dep
      h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16)) ?_
  rintro r s' ⟨hlc, x, a', hrun, hR⟩
  exact ⟨hlc, x, a', hrun, hR⟩

@[refines ConRon.Arena.nestContKey]
theorem nestContKey_refinesC (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (ctx fu po pl kb nn us dO dL nPc cty ns : Word) (c : NestCtx) (prog : List NestHole) (ds : List EIdx) (NS : NestState) (ctxP : ConLeche.NestCtx) (progP : List ConLeche.NestHole) (nP : ConLeche.Name) (usP : List ConLeche.Level) (dsP : List ConLeche.Expr) (ctyP : ConLeche.Expr) (nsP : ConLeche.NestState)
    (h0 : StageC dn vis fe env s₀.mem a₀) (h1 : WCtx dn vis fe s₀.mem ctx po pl c prog) (h2 : H nn) (h3 : H us) (h4 : DecB (fun m => (decHL m dO.toNat dL.toNat : Option (List EIdx))) s₀.mem ds) (h5 : dO.toNat + dL.toNat ≤ iwTop s₀.mem) (h6 : H cty) (h7 : NSB s₀.mem ns NS) (h8 : PosMR s₀.mem) (h9 : AbsOK s₀.mem) (h10 : ConLeche.NestCtxOk ctxP) (h11 : dCtx a₀.store env.find? c = some ctxP) (h12 : dProg a₀.store prog = some progP) (h13 : denoteN a₀.store.ns (decI nn) = some nP) (h14 : denoteLs a₀.store.lss (decI us) = some usP) (h15 : Frontend.denoteEList a₀.store ds = some dsP) (h16 : denoteE a₀.store (decI cty) = some ctyP) (h17 : dState a₀.store NS = some nsP) (h18 : (∀ d ∈ dsP, ConLeche.Expr.WScoped (ctxP.hiAt progP.length) d)) (h19 : (∀ d, (∀ y ∈ dsP, ConLeche.Expr.WScoped d y) → ConLeche.Expr.WScoped d ctyP)) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_cont_key" [vis, ctx, fu, po, pl, kb, nn, us, dO, dL, nPc, cty, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ ∃ x a', (nestContKey V fe c fu.toNat prog kb.toNat (decI nn) (decI us) ds nPc.toNat (decI cty) NS).run a₀ = .ok (x, a') ∧
      KindPost dn vis fe env a₀ s₀.mem r s'.mem x a'; ⊤⦄ := by
  refine triple_post (RefE.triple (nckE_spec p L.pkey n s₀ vis ctx fu po pl kb nn us dO dL nPc cty ns)
    ((nbRef_all L hq hIlpf hLC hFt hFk henv n hn).key s₀.mem a₀ ctx fu po pl kb nn us dO dL nPc cty ns c prog ds NS ctxP progP nP usP dsP ctyP nsP
      h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19)) ?_
  rintro r s' ⟨hlc, x, a', hrun, hR⟩
  exact ⟨hlc, x, a', hrun, hR⟩

@[refines ConRon.Arena.nestContNew]
theorem nestContNew_refinesC (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (ctx fu po pl kb nn us dO dL nPc cty ns : Word) (c : NestCtx) (prog : List NestHole) (ds : List EIdx) (NS : NestState) (ctxP : ConLeche.NestCtx) (progP : List ConLeche.NestHole) (nP : ConLeche.Name) (usP : List ConLeche.Level) (dsP : List ConLeche.Expr) (ctyP : ConLeche.Expr) (nsP : ConLeche.NestState)
    (h0 : StageC dn vis fe env s₀.mem a₀) (h1 : WCtx dn vis fe s₀.mem ctx po pl c prog) (h2 : H nn) (h3 : H us) (h4 : DecB (fun m => (decHL m dO.toNat dL.toNat : Option (List EIdx))) s₀.mem ds) (h5 : dO.toNat + dL.toNat ≤ iwTop s₀.mem) (h6 : H cty) (h7 : NSB s₀.mem ns NS) (h8 : PosMR s₀.mem) (h9 : AbsOK s₀.mem) (h10 : ConLeche.NestCtxOk ctxP) (h11 : dCtx a₀.store env.find? c = some ctxP) (h12 : dProg a₀.store prog = some progP) (h13 : denoteN a₀.store.ns (decI nn) = some nP) (h14 : denoteLs a₀.store.lss (decI us) = some usP) (h15 : Frontend.denoteEList a₀.store ds = some dsP) (h16 : denoteE a₀.store (decI cty) = some ctyP) (h17 : dState a₀.store NS = some nsP) (h18 : (∀ d ∈ dsP, ConLeche.Expr.WScoped (ctxP.hiAt progP.length) d)) (h19 : (∀ d, (∀ y ∈ dsP, ConLeche.Expr.WScoped d y) → ConLeche.Expr.WScoped d ctyP)) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_cont_new" [vis, ctx, fu, po, pl, kb, nn, us, dO, dL, nPc, cty, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ ∃ x a', (nestContNew V fe c fu.toNat prog kb.toNat (decI nn) (decI us) ds nPc.toNat (decI cty) NS).run a₀ = .ok (x, a') ∧
      KindPost dn vis fe env a₀ s₀.mem r s'.mem x a'; ⊤⦄ := by
  refine triple_post (RefE.triple (nnewE_spec p L.pnew n s₀ vis ctx fu po pl kb nn us dO dL nPc cty ns)
    ((nbRef_all L hq hIlpf hLC hFt hFk henv n hn).new s₀.mem a₀ ctx fu po pl kb nn us dO dL nPc cty ns c prog ds NS ctxP progP nP usP dsP ctyP nsP
      h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19)) ?_
  rintro r s' ⟨hlc, x, a', hrun, hR⟩
  exact ⟨hlc, x, a', hrun, hR⟩

@[refines ConRon.Arena.nestFrame]
theorem nestFrame_refinesC (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (ctx fu po pl hi us dO dL nPc gO gL ns : Word) (c : NestCtx) (prog : List NestHole) (ds : List EIdx) (grp : List (NIdx × EIdx)) (NS : NestState) (ctxP : ConLeche.NestCtx) (progP : List ConLeche.NestHole) (usP : List ConLeche.Level) (dsP : List ConLeche.Expr) (grpP : List (ConLeche.Name × ConLeche.Expr)) (nsP : ConLeche.NestState)
    (h0 : StageC dn vis fe env s₀.mem a₀) (h1 : WCtx dn vis fe s₀.mem ctx po pl c prog) (h2 : hi.toNat = c.hiAt prog.length) (h3 : H us) (h4 : DecB (fun m => (decHL m dO.toNat dL.toNat : Option (List EIdx))) s₀.mem ds) (h5 : dO.toNat + dL.toNat ≤ iwTop s₀.mem) (h6 : gL.toNat = grp.length) (h7 : gO.toNat + grp.length ≤ iwTop s₀.mem) (h8 : GrpAt s₀.mem gO.toNat grp) (h9 : NSB s₀.mem ns NS) (h10 : PosMR s₀.mem) (h11 : AbsOK s₀.mem) (h12 : ConLeche.NestCtxOk ctxP) (h13 : dCtx a₀.store env.find? c = some ctxP) (h14 : dProg a₀.store prog = some progP) (h15 : denoteLs a₀.store.lss (decI us) = some usP) (h16 : Frontend.denoteEList a₀.store ds = some dsP) (h17 : dGrp a₀.store grp = some grpP) (h18 : dState a₀.store NS = some nsP) (h19 : (∀ d ∈ dsP, ConLeche.Expr.WScoped hi.toNat d)) (h20 : (∀ x ∈ grpP, ConLeche.Expr.WScoped hi.toNat x.2)) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_frame" [vis, ctx, fu, po, pl, hi, us, dO, dL, nPc, gO, gL, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ ∃ x a', (nestFrame V fe c fu.toNat prog hi.toNat (decI us) ds nPc.toNat grp NS).run a₀ = .ok (x, a') ∧
      FramePost dn vis fe env a₀ s₀.mem r s'.mem x a'; ⊤⦄ := by
  refine triple_post (RefE.triple (nfrE_spec p L.pframe n s₀ vis ctx fu po pl hi us dO dL nPc gO gL ns)
    ((nbRef_all L hq hIlpf hLC hFt hFk henv n hn).frame s₀.mem a₀ ctx fu po pl hi us dO dL nPc gO gL ns c prog ds grp NS ctxP progP usP dsP grpP nsP
      h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20)) ?_
  rintro r s' ⟨hlc, x, a', hrun, hR⟩
  exact ⟨hlc, x, a', hrun, hR⟩

@[refines ConRon.Arena.nestCtors]
theorem nestCtors_refinesC (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (ctx root fu po pl hi us dO dL no nl hO hL cO cL ns oO oL : Word) (c : NestCtx) (prog : List NestHole) (ds : List EIdx) (names : List NIdx) (holes : List EIdx) (cs : List (IConstantVal × Nat)) (NS : NestState) (outs : List (List NestFieldKind × EIdx)) (ctxP : ConLeche.NestCtx) (progP : List ConLeche.NestHole) (usP : List ConLeche.Level) (dsP : List ConLeche.Expr) (namesP : List ConLeche.Name) (holesP : List ConLeche.Expr) (csP : List (ConLeche.ConstantVal × Nat)) (nsP : ConLeche.NestState) (outsP : List (List ConLeche.NestFieldKind × ConLeche.Expr))
    (h0 : StageC dn vis fe env s₀.mem a₀) (h1 : WCtx dn vis fe s₀.mem ctx po pl c prog) (h2 : CtorsCtx s₀.mem us dO dL no nl hO hL ds names holes) (h3 : cL.toNat = cs.length) (h4 : cO.toNat + cs.length ≤ iwTop s₀.mem) (h5 : CsAt s₀.mem cO.toNat cs (· < iwTop s₀.mem)) (h6 : NSB s₀.mem ns NS) (h7 : OutsB s₀.mem oO.toNat oL.toNat outs) (h8 : oO.toNat + oL.toNat ≤ iwTop s₀.mem) (h9 : PosMR s₀.mem) (h10 : AbsOK s₀.mem) (h11 : ConLeche.NestCtxOk ctxP) (h12 : dCtx a₀.store env.find? c = some ctxP) (h13 : dProg a₀.store prog = some progP) (h14 : CtorsPre a₀.store (decI us) ds names holes hi.toNat usP dsP namesP holesP) (h15 : dCtors a₀.store cs = some csP) (h16 : (∀ x ∈ csP, x.1.type.hasFvar = false)) (h17 : dState a₀.store NS = some nsP) (h18 : outs.mapM (dOut a₀.store) = some outsP) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctors" [vis, ctx, root, fu, po, pl, hi, us, dO, dL, no, nl, hO, hL, cO, cL, ns, oO, oL]
    ⦃fun r s' => LocEq s' s₀ ∧ ∃ x a', (nestCtors V fe c (decide (root ≠ 0)) fu.toNat prog hi.toNat (decI us) ds names holes cs NS outs).run a₀ = .ok (x, a') ∧
      CtorsPost dn vis fe env a₀ s₀.mem r s'.mem x a'; ⊤⦄ := by
  refine triple_post (RefE.triple (nctE_spec p L.pctors n s₀ vis ctx root fu po pl hi us dO dL no nl hO hL cO cL ns oO oL)
    ((nbRef_all L hq hIlpf hLC hFt hFk henv n hn).ctors s₀.mem a₀ ctx root fu po pl hi us dO dL no nl hO hL cO cL ns oO oL c prog ds names holes cs NS outs ctxP progP usP dsP namesP holesP csP nsP outsP
      h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18)) ?_
  rintro r s' ⟨hlc, x, a', hrun, hR⟩
  exact ⟨hlc, x, a', hrun, hR⟩

@[refines_part ConRon.Arena.nestCtors "one constructor (nest_ctors_one)"]
theorem nestCtorsOne_refinesC (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (ctx root fu po pl hi us dO dL no nl hO hL cv nF ns : Word) (c : NestCtx) (prog : List NestHole) (ds : List EIdx) (names : List NIdx) (holes : List EIdx) (cvv : IConstantVal) (NS : NestState) (ctxP : ConLeche.NestCtx) (progP : List ConLeche.NestHole) (usP : List ConLeche.Level) (dsP : List ConLeche.Expr) (namesP : List ConLeche.Name) (holesP : List ConLeche.Expr) (cvP : ConLeche.ConstantVal) (nsP : ConLeche.NestState)
    (h0 : StageC dn vis fe env s₀.mem a₀) (h1 : WCtx dn vis fe s₀.mem ctx po pl c prog) (h2 : CtorsCtx s₀.mem us dO dL no nl hO hL ds names holes) (h3 : decCV (erecP s₀.mem) cv.toNat = some cvv) (h4 : cv.toNat + 3 < 2 ^ 64) (h5 : NSB s₀.mem ns NS) (h6 : PosMR s₀.mem) (h7 : AbsOK s₀.mem) (h8 : ConLeche.NestCtxOk ctxP) (h9 : dCtx a₀.store env.find? c = some ctxP) (h10 : dProg a₀.store prog = some progP) (h11 : CtorsPre a₀.store (decI us) ds names holes hi.toNat usP dsP namesP holesP) (h12 : Frontend.denoteCV a₀.store cvv = some cvP) (h13 : cvP.type.hasFvar = false) (h14 : dState a₀.store NS = some nsP) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctors_one" [vis, ctx, root, fu, po, pl, hi, us, dO, dL, no, nl, hO, hL, cv, nF, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ ∃ x a', (oneT V fe c fu.toNat prog (decide (root ≠ 0)) hi.toNat (decI us) ds names holes cvv nF.toNat NS).run a₀ = .ok (x, a') ∧
      OnePost dn vis fe env a₀ s₀.mem hi r s'.mem x a'; ⊤⦄ := by
  refine triple_post (RefE.triple (noE_spec p L.pone n s₀ vis ctx root fu po pl hi us dO dL no nl hO hL cv nF ns)
    ((nbRef_all L hq hIlpf hLC hFt hFk henv n hn).one s₀.mem a₀ ctx root fu po pl hi us dO dL no nl hO hL cv nF ns c prog ds names holes cvv NS ctxP progP usP dsP namesP holesP cvP nsP
      h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14)) ?_
  rintro r s' ⟨hlc, x, a', hrun, hR⟩
  exact ⟨hlc, x, a', hrun, hR⟩

@[refines_part ConRon.Arena.nestCtors "field walk (nest_ctors_walk)"]
theorem nestCtorsWalk_refinesC (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (ctx root fu po pl hi nF crest ns : Word) (c : NestCtx) (prog : List NestHole) (NS : NestState) (ctxP : ConLeche.NestCtx) (progP : List ConLeche.NestHole) (crestP : ConLeche.Expr) (nsP : ConLeche.NestState)
    (h0 : StageC dn vis fe env s₀.mem a₀) (h1 : WCtx dn vis fe s₀.mem ctx po pl c prog) (h2 : H crest) (h3 : NSB s₀.mem ns NS) (h4 : PosMR s₀.mem) (h5 : AbsOK s₀.mem) (h6 : ConLeche.NestCtxOk ctxP) (h7 : dCtx a₀.store env.find? c = some ctxP) (h8 : dProg a₀.store prog = some progP) (h9 : denoteE a₀.store (decI crest) = some crestP) (h10 : dState a₀.store NS = some nsP) (h11 : ConLeche.Expr.WScoped hi.toNat crestP) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctors_walk" [vis, ctx, root, fu, po, pl, hi, nF, crest, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ ∃ x a', (walkT V fe c fu.toNat prog (decide (root ≠ 0)) hi.toNat nF.toNat (decI crest) NS).run a₀ = .ok (x, a') ∧
      WalkPost dn vis fe env a₀ s₀.mem hi nF r s'.mem x a'; ⊤⦄ := by
  refine triple_post (RefE.triple (nwE_spec p L.pwalk n s₀ vis ctx root fu po pl hi nF crest ns)
    ((nbRef_all L hq hIlpf hLC hFt hFk henv n hn).walk s₀.mem a₀ ctx root fu po pl hi nF crest ns c prog NS ctxP progP crestP nsP
      h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11)) ?_
  rintro r s' ⟨hlc, x, a', hrun, hR⟩
  exact ⟨hlc, x, a', hrun, hR⟩

@[refines ConRon.Arena.nestFields]
theorem nestFields_refinesC (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (ctx fu po pl base nF j cur ns kO kL dO dL : Word) (c : NestCtx) (prog : List NestHole) (NS : NestState) (ks : List NestFieldKind) (nds : List EIdx) (ctxP : ConLeche.NestCtx) (progP : List ConLeche.NestHole) (curP : ConLeche.Expr) (nsP : ConLeche.NestState) (ndsP : List ConLeche.Expr)
    (h0 : StageC dn vis fe env s₀.mem a₀) (h1 : WCtx dn vis fe s₀.mem ctx po pl c prog) (h2 : H cur) (h3 : NSB s₀.mem ns NS) (h4 : KlB s₀.mem kO.toNat kL.toNat ks) (h5 : kO.toNat + kL.toNat ≤ iwTop s₀.mem) (h6 : decHL s₀.mem dO.toNat dL.toNat = some nds) (h7 : dO.toNat + dL.toNat ≤ iwTop s₀.mem) (h8 : PosMR s₀.mem) (h9 : AbsOK s₀.mem) (h10 : ConLeche.NestCtxOk ctxP) (h11 : dCtx a₀.store env.find? c = some ctxP) (h12 : dProg a₀.store prog = some progP) (h13 : denoteE a₀.store (decI cur) = some curP) (h14 : dState a₀.store NS = some nsP) (h15 : Frontend.denoteEList a₀.store nds = some ndsP) (h16 : ConLeche.Expr.WScoped (base.toNat + j.toNat) curP) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_fields" [vis, ctx, fu, po, pl, base, nF, j, cur, ns, kO, kL, dO, dL]
    ⦃fun r s' => LocEq s' s₀ ∧ ∃ x a', (nestFields V fe c fu.toNat prog base.toNat nF.toNat j.toNat (decI cur) NS ks nds).run a₀ = .ok (x, a') ∧
      FieldsPost dn vis fe env a₀ s₀.mem base nF j ks nds r s'.mem x a'; ⊤⦄ := by
  refine triple_post (RefE.triple (nfE_spec p L.pfields n s₀ vis ctx fu po pl base nF j cur ns kO kL dO dL)
    ((nbRef_all L hq hIlpf hLC hFt hFk henv n hn).fields s₀.mem a₀ ctx fu po pl base nF j cur ns kO kL dO dL c prog NS ks nds ctxP progP curP nsP ndsP
      h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16)) ?_
  rintro r s' ⟨hlc, x, a', hrun, hR⟩
  exact ⟨hlc, x, a', hrun, hR⟩


end census

end L.Ind

end
