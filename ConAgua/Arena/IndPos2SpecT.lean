import ConAgua.Arena.IndPos2SpecS

/-! # `IndPos2`, the `nestPos` block (lane `indproofs2`, helper `pos2`): the census theorems — each
function of the block, run by `exec` at a fuel `n` with `2^31 + n ≤ coreWalkFuel`, refines its twin
(`nbSpec_all`: L ⊑ the word models; `nbOK_all`: the models ⊑ the twin). -/

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section census
variable {p : Prog} (L : NbLook p) (n : Nat) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
  (hcs : CtorSums fe)
include L hcs

@[refines ConRon.Arena.nestPos]
theorem nestPos_refines (hn : 2 ^ 31 + n ≤ coreWalkFuel) (s₀ : St) (a₀ : AState) (ctx fu po pl dep kb e ns : Word)
    (c : NestCtx) (prog : List NestHole) (NS : NestState)
    (h0 : StageR dn vis fe s₀.mem a₀)
    (h1 : WCtx dn vis fe s₀.mem ctx po pl c prog)
    (h2 : H e)
    (h3 : NSB s₀.mem ns NS) (hP : PosMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_pos" [vis, ctx, fu, po, pl, dep, kb, e, ns]
    ⦃fun r s' => LocEq s' s₀ ∧
      ∃ x a', (nestPos V fe c fu.toNat prog dep.toNat kb.toNat (decI e) NS).run a₀ = .ok (x, a') ∧
      StageR dn vis fe s'.mem a' ∧ IWGrow s₀.mem s'.mem ∧ decNFK (r.headD 0) = some x.1 ∧ H (r.tail.headD 0) ∧
      decI (r.tail.headD 0) = x.2.1 ∧ NSB s'.mem (r.tail.tail.headD 0) x.2.2 ∧ PosMR s'.mem; ⊤⦄ := by
  refine triple_post ((nbSpec_all L n).1 s₀ vis ctx fu po pl dep kb e ns) ?_
  rintro r s' ⟨hlc, hm⟩
  have := (nbOK_all dn vis fe hcs n hn).1 s₀.mem s'.mem a₀ ctx fu po pl dep kb e ns c prog NS _ hm h0 h1 h2 h3 hP
  exact ⟨hlc, by simpa using this⟩

@[refines_part ConRon.Arena.nestPos "binder arm (nest_pos_bind)"]
theorem nestPosBind_refines (hn : 2 ^ 31 + n ≤ coreWalkFuel) (s₀ : St) (a₀ : AState) (ctx fu po pl dep kb w ns : Word)
    (c : NestCtx) (prog : List NestHole) (NS : NestState)
    (h0 : StageR dn vis fe s₀.mem a₀)
    (h1 : WCtx dn vis fe s₀.mem ctx po pl c prog)
    (h2 : H w)
    (h3 : w >>> 28 = 6)
    (h4 : NSB s₀.mem ns NS) (hP : PosMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_pos_bind" [vis, ctx, fu, po, pl, dep, kb, w, ns]
    ⦃fun r s' => LocEq s' s₀ ∧
      ∃ x a', (posBindT V fe c fu.toNat prog dep.toNat kb.toNat (c.hiAt prog.length) (decI w) NS).run a₀ = .ok (x, a') ∧
      StageR dn vis fe s'.mem a' ∧ IWGrow s₀.mem s'.mem ∧ decNFK (r.headD 0) = some x.1 ∧ H (r.tail.headD 0) ∧
      decI (r.tail.headD 0) = x.2.1 ∧ NSB s'.mem (r.tail.tail.headD 0) x.2.2 ∧ PosMR s'.mem; ⊤⦄ := by
  refine triple_post ((nbSpec_all L n).2.1 s₀ vis ctx fu po pl dep kb w ns) ?_
  rintro r s' ⟨hlc, hm⟩
  have := (nbOK_all dn vis fe hcs n hn).2.1 s₀.mem s'.mem a₀ ctx fu po pl dep kb w ns c prog NS _ hm h0 h1 h2 h3 h4 hP
  exact ⟨hlc, by simpa using this⟩

@[refines_part ConRon.Arena.nestPos "application arm (nest_pos_app)"]
theorem nestPosApp_refines (hn : 2 ^ 31 + n ≤ coreWalkFuel) (s₀ : St) (a₀ : AState) (ctx fu po pl kb hi w ns : Word)
    (c : NestCtx) (prog : List NestHole) (NS : NestState)
    (h0 : StageR dn vis fe s₀.mem a₀)
    (h1 : WCtx dn vis fe s₀.mem ctx po pl c prog)
    (h2 : hi.toNat = c.hiAt prog.length)
    (h3 : H w)
    (h4 : NSB s₀.mem ns NS) (hP : PosMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_pos_app" [vis, ctx, fu, po, pl, kb, hi, w, ns]
    ⦃fun r s' => LocEq s' s₀ ∧
      ∃ x a', (posAppT V fe c fu.toNat prog kb.toNat hi.toNat (decI w) NS).run a₀ = .ok (x, a') ∧
      StageR dn vis fe s'.mem a' ∧ IWGrow s₀.mem s'.mem ∧ decNFK (r.headD 0) = some x.1 ∧ x.2.1 = decI w ∧
      NSB s'.mem (r.tail.headD 0) x.2.2 ∧ PosMR s'.mem; ⊤⦄ := by
  refine triple_post ((nbSpec_all L n).2.2.1 s₀ vis ctx fu po pl kb hi w ns) ?_
  rintro r s' ⟨hlc, hm⟩
  have := (nbOK_all dn vis fe hcs n hn).2.2.1 s₀.mem s'.mem a₀ ctx fu po pl kb hi w ns c prog NS _ hm h0 h1 h2 h3 h4 hP
  exact ⟨hlc, by simpa using this⟩

@[refines ConRon.Arena.nestCont]
theorem nestCont_refines (hn : 2 ^ 31 + n ≤ coreWalkFuel) (s₀ : St) (a₀ : AState) (ctx fu po pl kb nn us aO aL ns : Word)
    (c : NestCtx) (prog : List NestHole) (args : List EIdx) (NS : NestState)
    (h0 : StageR dn vis fe s₀.mem a₀)
    (h1 : WCtx dn vis fe s₀.mem ctx po pl c prog)
    (h2 : H nn)
    (h3 : H us)
    (h4 : decHL s₀.mem aO.toNat aL.toNat = some args)
    (h5 : aO.toNat + aL.toNat ≤ iwTop s₀.mem)
    (h6 : NSB s₀.mem ns NS) (hP : PosMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_cont" [vis, ctx, fu, po, pl, kb, nn, us, aO, aL, ns]
    ⦃fun r s' => LocEq s' s₀ ∧
      ∃ x a', (nestCont V fe c fu.toNat prog kb.toNat (decI nn) (decI us) args NS).run a₀ = .ok (x, a') ∧
      StageR dn vis fe s'.mem a' ∧ IWGrow s₀.mem s'.mem ∧ decNFK (r.headD 0) = some x.1 ∧
      NSB s'.mem (r.tail.headD 0) x.2 ∧ PosMR s'.mem; ⊤⦄ := by
  refine triple_post ((nbSpec_all L n).2.2.2.1 s₀ vis ctx fu po pl kb nn us aO aL ns) ?_
  rintro r s' ⟨hlc, hm⟩
  have := (nbOK_all dn vis fe hcs n hn).2.2.2.1 s₀.mem s'.mem a₀ ctx fu po pl kb nn us aO aL ns c prog args NS _ hm h0 h1 h2 h3 h4 h5 h6 hP
  exact ⟨hlc, by simpa using this⟩

@[refines ConRon.Arena.nestContKey]
theorem nestContKey_refines (hn : 2 ^ 31 + n ≤ coreWalkFuel) (s₀ : St) (a₀ : AState) (ctx fu po pl kb nn us dO dL nPc cty ns : Word)
    (c : NestCtx) (prog : List NestHole) (ds : List EIdx) (NS : NestState)
    (h0 : StageR dn vis fe s₀.mem a₀)
    (h1 : WCtx dn vis fe s₀.mem ctx po pl c prog)
    (h2 : H nn)
    (h3 : H us)
    (h4 : DecB (fun m => (decHL m dO.toNat dL.toNat : Option (List EIdx))) s₀.mem ds)
    (h5 : dO.toNat + dL.toNat ≤ iwTop s₀.mem)
    (h6 : H cty)
    (h7 : NSB s₀.mem ns NS) (hP : PosMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_cont_key" [vis, ctx, fu, po, pl, kb, nn, us, dO, dL, nPc, cty, ns]
    ⦃fun r s' => LocEq s' s₀ ∧
      ∃ x a', (nestContKey V fe c fu.toNat prog kb.toNat (decI nn) (decI us) ds nPc.toNat (decI cty) NS).run a₀ = .ok (x, a') ∧
      StageR dn vis fe s'.mem a' ∧ IWGrow s₀.mem s'.mem ∧ decNFK (r.headD 0) = some x.1 ∧
      NSB s'.mem (r.tail.headD 0) x.2 ∧ PosMR s'.mem; ⊤⦄ := by
  refine triple_post ((nbSpec_all L n).2.2.2.2.1 s₀ vis ctx fu po pl kb nn us dO dL nPc cty ns) ?_
  rintro r s' ⟨hlc, hm⟩
  have := (nbOK_all dn vis fe hcs n hn).2.2.2.2.1 s₀.mem s'.mem a₀ ctx fu po pl kb nn us dO dL nPc cty ns c prog ds NS _ hm h0 h1 h2 h3 h4 h5 h6 h7 hP
  exact ⟨hlc, by simpa using this⟩

@[refines ConRon.Arena.nestContNew]
theorem nestContNew_refines (hn : 2 ^ 31 + n ≤ coreWalkFuel) (s₀ : St) (a₀ : AState) (ctx fu po pl kb nn us dO dL nPc cty ns : Word)
    (c : NestCtx) (prog : List NestHole) (ds : List EIdx) (NS : NestState)
    (h0 : StageR dn vis fe s₀.mem a₀)
    (h1 : WCtx dn vis fe s₀.mem ctx po pl c prog)
    (h2 : H nn)
    (h3 : H us)
    (h4 : DecB (fun m => (decHL m dO.toNat dL.toNat : Option (List EIdx))) s₀.mem ds)
    (h5 : dO.toNat + dL.toNat ≤ iwTop s₀.mem)
    (h6 : H cty)
    (h7 : NSB s₀.mem ns NS) (hP : PosMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_cont_new" [vis, ctx, fu, po, pl, kb, nn, us, dO, dL, nPc, cty, ns]
    ⦃fun r s' => LocEq s' s₀ ∧
      ∃ x a', (nestContNew V fe c fu.toNat prog kb.toNat (decI nn) (decI us) ds nPc.toNat (decI cty) NS).run a₀ = .ok (x, a') ∧
      StageR dn vis fe s'.mem a' ∧ IWGrow s₀.mem s'.mem ∧ decNFK (r.headD 0) = some x.1 ∧
      NSB s'.mem (r.tail.headD 0) x.2 ∧ PosMR s'.mem; ⊤⦄ := by
  refine triple_post ((nbSpec_all L n).2.2.2.2.2.1 s₀ vis ctx fu po pl kb nn us dO dL nPc cty ns) ?_
  rintro r s' ⟨hlc, hm⟩
  have := (nbOK_all dn vis fe hcs n hn).2.2.2.2.2.1 s₀.mem s'.mem a₀ ctx fu po pl kb nn us dO dL nPc cty ns c prog ds NS _ hm h0 h1 h2 h3 h4 h5 h6 h7 hP
  exact ⟨hlc, by simpa using this⟩

@[refines ConRon.Arena.nestFrame]
theorem nestFrame_refines (hn : 2 ^ 31 + n ≤ coreWalkFuel) (s₀ : St) (a₀ : AState) (ctx fu po pl hi us dO dL nPc gO gL ns : Word)
    (c : NestCtx) (prog : List NestHole) (ds : List EIdx) (grp : List (NIdx × EIdx)) (NS : NestState)
    (h0 : StageR dn vis fe s₀.mem a₀)
    (h1 : WCtx dn vis fe s₀.mem ctx po pl c prog)
    (h2 : hi.toNat = c.hiAt prog.length)
    (h3 : H us)
    (h4 : DecB (fun m => (decHL m dO.toNat dL.toNat : Option (List EIdx))) s₀.mem ds)
    (h5 : dO.toNat + dL.toNat ≤ iwTop s₀.mem)
    (h6 : gL.toNat = grp.length)
    (h7 : gO.toNat + grp.length ≤ iwTop s₀.mem)
    (h8 : GrpAt s₀.mem gO.toNat grp)
    (h9 : NSB s₀.mem ns NS) (hP : PosMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_frame" [vis, ctx, fu, po, pl, hi, us, dO, dL, nPc, gO, gL, ns]
    ⦃fun r s' => LocEq s' s₀ ∧
      ∃ x a', (nestFrame V fe c fu.toNat prog hi.toNat (decI us) ds nPc.toNat grp NS).run a₀ = .ok (x, a') ∧
      StageR dn vis fe s'.mem a' ∧ IWGrow s₀.mem s'.mem ∧ NSB s'.mem (r.headD 0) x ∧ PosMR s'.mem; ⊤⦄ := by
  refine triple_post ((nbSpec_all L n).2.2.2.2.2.2.1 s₀ vis ctx fu po pl hi us dO dL nPc gO gL ns) ?_
  rintro r s' ⟨hlc, hm⟩
  have := (nbOK_all dn vis fe hcs n hn).2.2.2.2.2.2.1 s₀.mem s'.mem a₀ ctx fu po pl hi us dO dL nPc gO gL ns c prog ds grp NS _ hm h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hP
  exact ⟨hlc, by simpa using this⟩

@[refines ConRon.Arena.nestCtors]
theorem nestCtors_refines (hn : 2 ^ 31 + n ≤ coreWalkFuel) (s₀ : St) (a₀ : AState) (ctx root fu po pl hi us dO dL no nl hO hL cO cL ns oO oL : Word)
    (c : NestCtx) (prog : List NestHole) (ds : List EIdx) (names : List NIdx) (holes : List EIdx) (cs : List (IConstantVal × Nat)) (NS : NestState) (outs : List (List NestFieldKind × EIdx))
    (h0 : StageR dn vis fe s₀.mem a₀)
    (h1 : WCtx dn vis fe s₀.mem ctx po pl c prog)
    (h2 : CtorsCtx s₀.mem us dO dL no nl hO hL ds names holes)
    (h3 : cL.toNat = cs.length)
    (h4 : cO.toNat + cs.length ≤ iwTop s₀.mem)
    (h5 : CsAt s₀.mem cO.toNat cs (· < iwTop s₀.mem))
    (h6 : NSB s₀.mem ns NS)
    (h7 : OutsB s₀.mem oO.toNat oL.toNat outs)
    (h8 : oO.toNat + oL.toNat ≤ iwTop s₀.mem) (hP : PosMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctors" [vis, ctx, root, fu, po, pl, hi, us, dO, dL, no, nl, hO, hL, cO, cL, ns, oO, oL]
    ⦃fun r s' => LocEq s' s₀ ∧
      ∃ x a', (nestCtors V fe c (decide (root ≠ 0)) fu.toNat prog hi.toNat (decI us) ds names holes cs NS outs).run a₀ = .ok (x, a') ∧
      StageR dn vis fe s'.mem a' ∧ IWGrow s₀.mem s'.mem ∧
      OutsB s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat x.1 ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop s'.mem ∧ NSB s'.mem (r.tail.tail.headD 0) x.2 ∧ PosMR s'.mem; ⊤⦄ := by
  refine triple_post ((nbSpec_all L n).2.2.2.2.2.2.2.1 s₀ vis ctx root fu po pl hi us dO dL no nl hO hL cO cL ns oO oL) ?_
  rintro r s' ⟨hlc, hm⟩
  have := (nbOK_all dn vis fe hcs n hn).2.2.2.2.2.2.2.1 s₀.mem s'.mem a₀ ctx root fu po pl hi us dO dL no nl hO hL cO cL ns oO oL c prog ds names holes cs NS outs _ hm h0 h1 h2 h3 h4 h5 h6 h7 h8 hP
  exact ⟨hlc, by simpa using this⟩

@[refines_part ConRon.Arena.nestCtors "one constructor (nest_ctors_one)"]
theorem nestCtorsOne_refines (hn : 2 ^ 31 + n ≤ coreWalkFuel) (s₀ : St) (a₀ : AState) (ctx root fu po pl hi us dO dL no nl hO hL cv nF ns : Word)
    (c : NestCtx) (prog : List NestHole) (ds : List EIdx) (names : List NIdx) (holes : List EIdx) (cvv : IConstantVal) (NS : NestState)
    (h0 : StageR dn vis fe s₀.mem a₀)
    (h1 : WCtx dn vis fe s₀.mem ctx po pl c prog)
    (h2 : CtorsCtx s₀.mem us dO dL no nl hO hL ds names holes)
    (h3 : decCV (erecP s₀.mem) cv.toNat = some cvv)
    (h4 : cv.toNat + 3 < 2 ^ 64)
    (h5 : NSB s₀.mem ns NS) (hP : PosMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctors_one" [vis, ctx, root, fu, po, pl, hi, us, dO, dL, no, nl, hO, hL, cv, nF, ns]
    ⦃fun r s' => LocEq s' s₀ ∧
      ∃ ks closed NS3 a', (∀ {β : Type} (K : List NestFieldKind × EIdx → NestState → AM β), (oneK V fe c fu.toNat prog (decide (root ≠ 0)) hi.toNat (decI us) ds names holes cvv nF.toNat NS K).run a₀ = (K (ks, closed) NS3).run a') ∧
      StageR dn vis fe s'.mem a' ∧ IWGrow s₀.mem s'.mem ∧
      KlB s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat ks ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop s'.mem ∧ H (r.tail.tail.headD 0) ∧
      decI (r.tail.tail.headD 0) = closed ∧ NSB s'.mem (r.tail.tail.tail.headD 0) NS3 ∧ PosMR s'.mem; ⊤⦄ := by
  refine triple_post ((nbSpec_all L n).2.2.2.2.2.2.2.2.1 s₀ vis ctx root fu po pl hi us dO dL no nl hO hL cv nF ns) ?_
  rintro r s' ⟨hlc, hm⟩
  have := (nbOK_all dn vis fe hcs n hn).2.2.2.2.2.2.2.2.1 s₀.mem s'.mem a₀ ctx root fu po pl hi us dO dL no nl hO hL cv nF ns c prog ds names holes cvv NS _ hm h0 h1 h2 h3 h4 h5 hP
  exact ⟨hlc, by simpa using this⟩

@[refines_part ConRon.Arena.nestCtors "field walk (nest_ctors_walk)"]
theorem nestCtorsWalk_refines (hn : 2 ^ 31 + n ≤ coreWalkFuel) (s₀ : St) (a₀ : AState) (ctx root fu po pl hi nF crest ns : Word)
    (c : NestCtx) (prog : List NestHole) (NS : NestState)
    (h0 : StageR dn vis fe s₀.mem a₀)
    (h1 : WCtx dn vis fe s₀.mem ctx po pl c prog)
    (h2 : H crest)
    (h3 : NSB s₀.mem ns NS) (hP : PosMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctors_walk" [vis, ctx, root, fu, po, pl, hi, nF, crest, ns]
    ⦃fun r s' => LocEq s' s₀ ∧
      ∃ ks nds cur ns2 closed a', (∀ {β : Type} (K : List NestFieldKind → List EIdx → EIdx → NestState → EIdx → AM β), (walkK V fe c fu.toNat prog (decide (root ≠ 0)) hi.toNat nF.toNat (decI crest) NS K).run a₀ = (K ks nds cur ns2 closed).run a') ∧
      StageR dn vis fe s'.mem a' ∧ IWGrow s₀.mem s'.mem ∧
      KlB s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat ks ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop s'.mem ∧ ks.length = nF.toNat ∧
      H (r.tail.tail.headD 0) ∧ decI (r.tail.tail.headD 0) = cur ∧ H (r.tail.tail.tail.headD 0) ∧
      decI (r.tail.tail.tail.headD 0) = closed ∧ NSB s'.mem (r.tail.tail.tail.tail.headD 0) ns2 ∧ PosMR s'.mem; ⊤⦄ := by
  refine triple_post ((nbSpec_all L n).2.2.2.2.2.2.2.2.2.1 s₀ vis ctx root fu po pl hi nF crest ns) ?_
  rintro r s' ⟨hlc, hm⟩
  have := (nbOK_all dn vis fe hcs n hn).2.2.2.2.2.2.2.2.2.1 s₀.mem s'.mem a₀ ctx root fu po pl hi nF crest ns c prog NS _ hm h0 h1 h2 h3 hP
  exact ⟨hlc, by simpa using this⟩

@[refines ConRon.Arena.nestFields]
theorem nestFields_refines (hn : 2 ^ 31 + n ≤ coreWalkFuel) (s₀ : St) (a₀ : AState) (ctx fu po pl base nF j cur ns kO kL dO dL : Word)
    (c : NestCtx) (prog : List NestHole) (NS : NestState) (ks : List NestFieldKind) (nds : List EIdx)
    (h0 : StageR dn vis fe s₀.mem a₀)
    (h1 : WCtx dn vis fe s₀.mem ctx po pl c prog)
    (h2 : H cur)
    (h3 : NSB s₀.mem ns NS)
    (h4 : KlB s₀.mem kO.toNat kL.toNat ks)
    (h5 : kO.toNat + kL.toNat ≤ iwTop s₀.mem)
    (h6 : decHL s₀.mem dO.toNat dL.toNat = some nds)
    (h7 : dO.toNat + dL.toNat ≤ iwTop s₀.mem) (hP : PosMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_fields" [vis, ctx, fu, po, pl, base, nF, j, cur, ns, kO, kL, dO, dL]
    ⦃fun r s' => LocEq s' s₀ ∧
      ∃ x a', (nestFields V fe c fu.toNat prog base.toNat nF.toNat j.toNat (decI cur) NS ks nds).run a₀ = .ok (x, a') ∧
      StageR dn vis fe s'.mem a' ∧ IWGrow s₀.mem s'.mem ∧
      KlB s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat x.1 ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop s'.mem ∧
      decHL s'.mem (r.tail.tail.headD 0).toNat (r.tail.tail.tail.headD 0).toNat = some x.2.1 ∧
      (r.tail.tail.headD 0).toNat + (r.tail.tail.tail.headD 0).toNat ≤ iwTop s'.mem ∧
      H (r.tail.tail.tail.tail.headD 0) ∧ decI (r.tail.tail.tail.tail.headD 0) = x.2.2.1 ∧
      NSB s'.mem (r.tail.tail.tail.tail.tail.headD 0) x.2.2.2 ∧ x.1.length = ks.length + nF.toNat ∧
      x.2.1.length = nds.length + nF.toNat ∧ (nF.toNat = 0 ∨ base.toNat + j.toNat + nF.toNat < 2 ^ 64) ∧ PosMR s'.mem; ⊤⦄ := by
  refine triple_post ((nbSpec_all L n).2.2.2.2.2.2.2.2.2.2 s₀ vis ctx fu po pl base nF j cur ns kO kL dO dL) ?_
  rintro r s' ⟨hlc, hm⟩
  have := (nbOK_all dn vis fe hcs n hn).2.2.2.2.2.2.2.2.2.2 s₀.mem s'.mem a₀ ctx fu po pl base nF j cur ns kO kL dO dL c prog NS ks nds _ hm h0 h1 h2 h3 h4 h5 h6 h7 hP
  exact ⟨hlc, by simpa using this⟩

end census

end L.Ind
