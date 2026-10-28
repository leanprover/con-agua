import ConAgua.Arena.IndPosSpec.P2sdW
import ConAgua.Verdict.PosTopE4

/-!
# `nest_root` and `nest_seeds` under `StageC` (lane `indstaget`, helper `indstaget-pos`)

`p2sdW_ok`'s proof (`IndPosSpec/NestSeeds`) at `realCall p`, its twin side con-ron's
`nestSeeds_spec` (the seed's fuel by `seedFuel_spec`, its former by `nestInstType_spec`, the
instantiation met by `nestContKey_spec`), and the census links `nestRoot_refinesC` (from
`nrt_ref`, `Verdict/PosTopE4`), `nestSeeds_refinesC`.
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dCtx dProg dState dCtx_ext dProg_ext dState_ext dCtors dOut dOutss kindOf)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section seeds
variable {p : Prog} (Lb : NbLook p) (hq : KnotStageProg p) (hIlpf : IlpfF p) (hLC : LvlCacheProg p) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
  {env : ConLeche.Env} (henv : ConLeche.EnvWF env) (ctx : Word) (c : NestCtx)
  {ctxP : ConLeche.NestCtx} (hc : ConLeche.NestCtxOk ctxP)

include Lb hq hIlpf hLC henv hc in
/-- **`nest_seeds`** simulated by `nestSeeds` under `StageC`. -/
theorem p2sdW_okC : ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (m m' : Mem) (a : AState) (sO sL ns : Word)
    (seeds : List (NestKey × Nat)) (NS : NestState) (r : List Word)
    (seedsP : List (ConLeche.NestKey × Nat)) (nsP : ConLeche.NestState),
    p2sdW (realCall p) n m vis ctx sO sL ns = some (r, m') → StageC dn vis fe env m a → UCtx dn vis fe m ctx c →
    c.hiAt 0 < 2 ^ 64 → sL.toNat = seeds.length → SeedsAt m sO.toNat seeds → NSB m ns NS → PosMR m → AbsOK m →
    dCtx a.store env.find? c = some ctxP →
    seeds.mapM (fun k => (ConRon.Bridge.Inductives.dKey a.store k.1).map (·, k.2)) = some seedsP →
    dState a.store NS = some nsP → (∀ k ∈ seedsP, ∀ x ∈ k.1.ds, ConLeche.Expr.WScoped (ctxP.hiAt 0) x) →
    ∃ x a', (nestSeeds V fe c seeds NS).run a = .ok (x, a') ∧ StageC dn vis fe env m' a' ∧ IWGrow m m' ∧
      NSB m' (r.headD 0) x ∧ PosMR m' ∧ AbsOK m' ∧ ConRon.Bridge.CoreStep V env fe a a'
  | 0, _, m, m', a, sO, sL, ns, seeds, NS, r, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _ => by
    simp [p2sdW] at h
  | n + 1, hn, m, m', a, sO, sL, ns, seeds, NS, r, seedsP, nsP, h, hC, hU, hhi, hsl, hsd, hns, hP, hA, hctx,
      hseedsP, hnsP, hw => by
    have hS := hC.stage
    have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
    rw [p2sdW_succ] at h
    by_cases h0 : sL = 0
    · rw [ite_eq_left h0] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst h0
      have : seeds = [] := List.eq_nil_of_length_eq_zero (by simpa using hsl.symm)
      subst this
      exact ⟨NS, a, by rw [ConRon.Arena.nestSeeds.eq_def]; rfl, hC, IWGrow.refl _, by simpa using hns, hP, hA,
        ConRon.Bridge.CoreStep.refl hC.check⟩
    rw [ite_eq_right h0] at h
    obtain ⟨⟨kk, nPcN⟩, seeds', rfl⟩ : ∃ x seeds', seeds = x :: seeds' := by
      cases seeds with
      | nil => exact absurd (UInt64.toNat_inj.mp (by simpa using hsl)) h0
      | cons x seeds' => exact ⟨x, seeds', rfl⟩
    simp only [List.length_cons] at hsl
    -- the twin's key
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at hseedsP
    rcases hk1 : (ConRon.Bridge.Inductives.dKey a.store kk).map (·, nPcN) with _ | kP; · rw [hk1] at hseedsP; simp at hseedsP
    cases hks1 : seeds'.mapM (fun k => (ConRon.Bridge.Inductives.dKey a.store k.1).map (·, k.2)) with
    | none => rw [hk1, hks1] at hseedsP; simp at hseedsP
    | some ksP' =>
    simp only [hk1, hks1, Option.bind_some, Option.some.injEq] at hseedsP
    subst hseedsP
    simp only [Option.map_eq_some_iff] at hk1
    obtain ⟨keyP, hkey, rfl⟩ := hk1
    obtain ⟨hkc, hkl, hkd⟩ := ConRon.Bridge.Inductives.dKey_inv hkey
    obtain ⟨sp, key, nPc, h0w, hsO, hsp1, h1w, h2w, hkd', hksl, hnpc⟩ := hsd 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0w hkd' hnpc
    have rd0 : rdW (m.arr64 IW) sO = sp := by simp [rdW, h0w]
    have rd1 : rdW (m.arr64 IW) sp = key := by simp [rdW, h1w]
    have hsp1' : (sp + 1).toNat = sp.toNat + 1 := word_add_toNat (by simp; omega)
    have rd2 : rdW (m.arr64 IW) (sp + 1) = nPc := by simp [rdW, hsp1', h2w]
    rw [rd0, rd1, rd2] at h
    obtain ⟨hnnH, hnnd, husH, husd, hdsd, hdsb, hk4⟩ := pos2_nk_fields hkd' htop
    obtain ⟨hk, hkin⟩ := pos2_nk_in hkd'
    obtain ⟨hdl, hdel⟩ := pos2_hslice_get hdsd
    -- the fuel
    rcases hf : p2sfW n m (rdW (m.arr64 IW) (key + 2)) (rdW (m.arr64 IW) (key + 3)) 0 SLACK with _ | ⟨rf, m1⟩ <;> rw [hf] at h; · simp [p2sdK1] at h
    rw [p2sdK1_some] at h
    obtain ⟨a1, hfold, hS1, hg1, hP1⟩ := p2sfW_ok dn vis fe _ _ kk.ds m hdl hdel hksl n m m1 a 0 SLACK rf hf hS
      (IWGrow.refl _) (by simp) hP
    have hA1 := p2sfW_afr _ _ _ _ _ _ _ _ hf hA
    have hfold' : (kk.ds.foldlM (fun a d => do
        let w ← ConRon.Arena.whnfWalkFuel d
        pure (max a w)) fuelSlack).run a = .ok ((rf.headD 0).toNat, a1) := by
      simp only [UInt64.toNat_zero, List.drop_zero] at hfold
      exact hfold
    obtain ⟨p1, -⟩ := ConRon.Bridge.Inductives.seedFuel_spec kk.ds keyP.ds fuelSlack a a1 _ hC.check.state hkd hfold'
    have hC1 : StageC dn vis fe env m1 a1 := hC.of_pstep hS1 hA1 p1
    have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1
    -- the instance's type
    cases n with
    | zero => simp [nitWf, p2sdK2] at h
    | succ n' =>
    rcases hni : nitW (realCall p) n' m1 vis ctx (nhiW m ctx 0) key with _ | ⟨r2, m2⟩; · simp only [nitWf] at h; rw [hni] at h; simp [p2sdK2] at h
    simp only [nitWf, hni, p2sdK2_some] at h
    have hW : WCtx dn vis fe m ctx 0 0 c [] := ⟨hU, by simp [HSl, HolesAt], by simpa using hhi⟩
    have hhi0 : (nhiW m ctx 0).toNat = c.hiAt 0 := by simpa using hW.hi htop
    obtain ⟨x2, a2, hrun2, hS2, hg2, -, hctyH, hctyd, hP2, -, hA2⟩ := nitW_ok n' dn fe vis ctx _ (c.hiAt 0) hhi0 c m1 m2
      a1 key kk r2 (realCall p) (nty_ok Lb.nit.ty (IlpRd.realC hIlpf hC1)) _
      (nitLe_realC hq.closed hLC n' _ _ key c kk hC1 hA1 (dCtx_ext _ p1.ext _ _ hctx)
        (ConRon.Bridge.Inductives.dKey_ext p1.ext _ _ hkey)) hni hS1 (hU.grow hg1) (hkd'.get (decNK_mono _) |>.symm ▸ (hkd'.stab (decNK_mono _) m1 hg1))
      (pos2_nk_in (hkd'.grow (decNK_mono _) hg1)).2 ((hsd.grow hg1 htop) 0 (by simp) |>.elim fun _ h' => by
        obtain ⟨key', nPc', h0', -, -, h1', -, -, hksl', -⟩ := h'
        have : (m1.arr64 IW)[sO.toNat]? = some sp := by rw [hg1.2.2.1 _ (by omega)]; exact h0w
        simp only [Nat.add_zero] at h0'
        rw [this] at h0'; cases h0'
        rw [hg1.2.2.1 _ (by omega), h1w] at h1'; cases h1'
        exact hksl') hP1
    have c1 := p1.toCore hC.check
    obtain ⟨c2, niP, ⟨-, hni2, hni3⟩, -⟩ := ConRon.Bridge.Inductives.nestInstType_spec hc c (c.hiAt 0) kk keyP
      a1 a2 x2 c1.ok ⟨dCtx_ext _ p1.ext _ _ hctx, ConRon.Bridge.Inductives.dKey_ext p1.ext _ _ hkey⟩ hrun2
    have c12 := c1.trans c2
    have hx02 := c12.ext
    have hC2 : StageC dn vis fe env m2 a2 := hC.of_cstep hS2 hA2 c12
    have hg12 := hg1.trans hg2
    have hksl2 : (rdW (m.arr64 IW) (key + 2)).toNat + (rdW (m.arr64 IW) (key + 3)).toNat ≤ iwTop m2 :=
      Nat.le_trans hksl hg12.1
    have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
    -- the container instance
    have e0 : rdW (m2.arr64 IW) key = rdW (m.arr64 IW) key := pos2_rd_grow hg12 (by omega)
    have e1 := pos2_key_rd hg12 htop hk4 (j := 1) (by omega)
    have e2 := pos2_key_rd hg12 htop hk4 (j := 2) (by omega)
    have e3 := pos2_key_rd hg12 htop hk4 (j := 3) (by omega)
    rw [show (key + 1 : Word) = key + UInt64.ofNat 1 from rfl, show (key + 2 : Word) = key + UInt64.ofNat 2 from rfl,
      show (key + 3 : Word) = key + UInt64.ofNat 3 from rfl, e0, e1, e2, e3] at h
    rcases hk3 : keyR (realCall p) (n' + 1) m2 vis ctx (rf.headD 0) 0 0 0 (rdW (m.arr64 IW) key)
        (rdW (m.arr64 IW) (key + UInt64.ofNat 1)) (rdW (m.arr64 IW) (key + UInt64.ofNat 2))
        (rdW (m.arr64 IW) (key + UInt64.ofNat 3)) nPc (r2.tail.headD 0) ns with _ | ⟨r3, m3⟩; · rw [hk3] at h; simp [p2sdK3] at h
    rw [hk3, p2sdK3_some] at h
    have hnnd' : decI (rdW (m.arr64 IW) key) = kk.cname := hnnd
    have husd' : decI (rdW (m.arr64 IW) (key + UInt64.ofNat 1)) = kk.lvls := husd
    obtain ⟨s3, hs3, -, x3, a3, hrun3, hR3⟩ := RefE.run_okW
      (nckE_spec p Lb.pkey (n' + 1) ⟨m2, Locals.init []⟩ _ _ _ _ _ _ _ _ _ _ _ _ _)
      ((nbRef_all (dn := dn) (vis := vis) (fe := fe) Lb hq hIlpf hLC henv (n' + 1) (by omega)).key m2 a2 ctx
      (rf.headD 0) 0 0 0 (rdW (m.arr64 IW) key) (rdW (m.arr64 IW) (key + UInt64.ofNat 1))
      (rdW (m.arr64 IW) (key + UInt64.ofNat 2)) (rdW (m.arr64 IW) (key + UInt64.ofNat 3)) nPc (r2.tail.headD 0) ns
      c [] kk.ds NS ctxP [] keyP.cname keyP.lvls keyP.ds niP.2 nsP
      hC2 (hW.grow hg12) hnnH husH
      (by show decHL (truncM m2) _ _ = _; rw [decHL_truncM (by simpa using hksl2)]
          rw [decHL_agree (RdS.of_grow hg12) (fun j hj => by simpa using hdsb j hj)]; simpa using hdsd)
      (by simpa using hksl2) hctyH (hns.grow hg12 htop) hP2 hA2
      hc (dCtx_ext _ hx02 _ _ hctx) rfl (by rw [hnnd']; exact ConRon.Bridge.denoteN_ext hkc hx02)
      (by rw [husd']; exact ConRon.Bridge.denoteLs_ext hkl hx02) (ConRon.Bridge.denoteEList_ext hx02 _ _ hkd)
      (by rw [hctyd]; exact hni2) (dState_ext hx02 _ _ hnsP) (by simpa using hw _ List.mem_cons_self) hni3) hk3
    rw [hs3] at hR3; dsimp only at hR3
    obtain ⟨hC3, hg3, -, hns3, hP3, hA3, c3⟩ := hR3
    have htop3 : iwTop m3 < 2 ^ 64 := Nat.lt_of_le_of_lt hC3.stage.2.1 hC3.stage.2.2.2.1
    have hg13 := hg12.trans hg3
    have hsO1 : (sO + 1).toNat = sO.toNat + 1 := word_add_toNat (by simp; omega)
    have hsL1 : (sL - 1).toNat = seeds'.length := by rw [pos2_word_pred h0]; omega
    have hx03 := c12.ext.trans c3.ext
    have hrun3' : (nestContKey V fe c (rf.headD 0).toNat [] 0 kk.cname kk.lvls kk.ds nPcN x2.2 NS).run a2 =
        .ok (x3, a3) := by
      have e1 : decI (rdW (m.arr64 IW) (key + UInt64.ofNat 1)) = kk.lvls := husd
      rw [← hnnd, ← e1, ← hctyd, ← hnpc]
      exact hrun3
    obtain ⟨-, v1, ⟨-, hns1P⟩, -⟩ := ConRon.Bridge.Inductives.nestContKey_spec coreSpecV henv hc
      (ConRon.Bridge.Inductives.nestPos_spec coreSpecV henv hc _)
      [] [] 0 kk.cname keyP.cname kk.lvls keyP.lvls kk.ds keyP.ds nPcN x2.2 niP.2 NS nsP
      (by simpa using hw _ List.mem_cons_self) hni3 a2 a3 x3 c12.ok
      ⟨dCtx_ext _ hx02 _ _ hctx, rfl, ConRon.Bridge.denoteN_ext hkc hx02, ConRon.Bridge.denoteLs_ext hkl hx02,
        ConRon.Bridge.denoteEList_ext hx02 _ _ hkd, hni2, dState_ext hx02 _ _ hnsP⟩ hrun3'
    obtain ⟨x, a', hrun, hC', hg', hns', hP', hA', c4⟩ := p2sdW_okC (n' + 1) (by omega) m3 m' a3 (sO + 1) (sL - 1)
      (r3.tail.headD 0) seeds' x3.2 r ksP' v1.2 h hC3 (hU.grow hg13) hhi hsL1
      (by rw [hsO1]; exact (hsd.grow hg13 htop).tail) hns3 hP3 hA3 (dCtx_ext _ hx03 _ _ hctx)
      (ConRon.Bridge.Inductives.mapM_option_ext (fun a b h => by
          simp only [Option.map_eq_some_iff] at h ⊢
          obtain ⟨x, hx, rfl⟩ := h
          exact ⟨x, ConRon.Bridge.Inductives.dKey_ext hx03 _ _ hx, rfl⟩) _ _ hks1)
      hns1P
      (fun k hk x hx => hw k (List.mem_cons_of_mem _ hk) x hx)
    refine ⟨x, a', ?_, hC', hg13.trans hg', hns', hP', hA', (c12.trans c3).trans c4⟩
    simp only [ConRon.Arena.nestSeeds, StateT.run_bind, hfold', except_ok_bind, hrun2, hrun3']
    exact hrun

end seeds

/-! ## Census -/

section census
variable {p : Prog} (L : RsLook p) (hq : KnotStageProg p) (hIlpf : IlpfF p) (hLC : LvlCacheProg p) (n : Nat) (dn : NIdx → Option ConLeche.Name) (vis : Word)
  (fe : IFEnv) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
include L hq hIlpf hLC henv

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
  refine triple_post (nestSeeds_spec L (realCall p) (realCall_spec p) n s₀ vis ctx sO sL ns) ?_
  rintro r s' ⟨hlc, hm⟩
  have := p2sdW_okC L.nb hq hIlpf hLC dn vis fe henv ctx c hc n hn s₀.mem s'.mem a₀ sO sL ns seeds NS _ seedsP nsP hm hC hU hhi hsl
    hsd hns hP hA hctx hseedsP hnsP hw
  exact ⟨hlc, by simpa using this⟩

end census

end L.Ind
