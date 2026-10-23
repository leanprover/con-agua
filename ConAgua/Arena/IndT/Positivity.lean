import ConAgua.Arena.IndT.PosRoot
import ConAgua.Arena.IndT.Install6
import ConAgua.Arena.IndInstallSpec34

/-!
# `check_block_positivity` under `StageC` (lane `indstaget`, helper `indstaget-cbpos`)

`cbposW_ok`'s proof (`IndInstallSpec34`) under `StageC`, its twin side transcribed from con-ron's
`checkBlockPositivity_spec`: the walk's context (`bncW_sim`, con-ron's `blockNestCtx_spec` on its
run for the `CoreStep` and the context's denotation), `nest_uniform` (`nestUniform_refines`,
`nestUniform_spec`), the fresh state (an L-only step), `nest_root` (`nestRoot_refinesC`; con-ron's
`nestRoot_spec` on its run for the kinds' denotation), `pin_word(53)` (`zeroLevel_run`),
`lvl_eq_c` (its `StageR` contract `lvlEqStub_spec` with `lvlEq?_crun`), the fields' universes
(`iaaW_simC`), the normal forms (an L-only step). The `CoreStep` of the whole run from
`checkBlockPositivity_spec`. No fuel premise against the core walk's: `nest_root`'s `StageC`
version needs none.
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dCtx dCtors dOutss dState)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section sim
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq henv in
/-- **`check_block_positivity`'s model refines `checkBlockPositivity` under `StageC`** (con-ron's
`checkBlockPositivity_spec`'s preconditions). -/
theorem cbposW_okC (hP : PosBlkProg p) (n : Nat) (hn : n + 2 ≤ 2 ^ 62) {m m' : Mem} {a : AState}
    {q cvO cvL caO caL : Word} {P : BlockParts} {cvTas : List IConstantVal}
    {css : List (List (IConstantVal × Nat))} {r : List Word} {pP : ConLeche.BlockParts}
    {cvsP : List ConLeche.ConstantVal} {cssP : List (List (ConLeche.ConstantVal × Nat))}
    (h : cbposW p (n + 2) m vis q cvO cvL caO caL = some (r, m')) (hC : StageC dn vis fe env m a)
    (hqd : DecB (fun m => decBS m q.toNat) m P.shape) (hsrc : ShapeSrc m q)
    (hcv : PSlR decCVp cvTas cvO cvL m) (hcss : PSlR decCNSB css caO caL m) (hPM : PosMR m)
    (hA : AbsOK m) (hk : ∀ f ∈ posKeepCallees, AbsKeep p f)
    (hpP : ConRon.Bridge.Inductives.dParts a.store P = some pP)
    (hcvP : cvTas.mapM (Frontend.denoteCV a.store) = some cvsP)
    (hcssP : css.mapM (dCtors a.store) = some cssP)
    (hfe : ConRon.Bridge.denoteFEnv a.store fe = some env)
    (hT : ∀ cv ∈ cvsP, ConLeche.Expr.WScoped 0 cv.type)
    (hct : ∀ cs ∈ cssP, ∀ c ∈ cs, ConLeche.Expr.WScoped 0 c.1.type) :
    ∃ x a', (ConRon.Arena.checkBlockPositivity V fe P cvTas css).run a = .ok (x, a') ∧
      StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ PosMR m' ∧ AbsOK m' ∧
      PSlR decKSS x.1 (r.headD 0) (r.tail.headD 0) m' ∧
      PSlR decNFS x.2.1 (r.tail.tail.headD 0) (r.tail.tail.tail.headD 0) m' ∧
      NSB m' ((r.drop 4).headD 0) x.2.2 ∧ ConRon.Bridge.CoreStep V env fe a a' := by
  have hS := hC.stage
  have hpP0 := hpP
  simp only [ConRon.Bridge.Inductives.dParts, Option.map_eq_some_iff] at hpP
  obtain ⟨qP, hqP, rfl⟩ := hpP
  have hcl : ∀ cs ∈ cssP, ∀ c ∈ cs, c.1.type.hasFvar = false :=
    fun cs hcs c hc => ConLeche.Cached.ws0_hasFvar (hct cs hcs c hc)
  unfold cbposW at h
  -- the walk's context
  cases h1 : callW p (n + 2) "block_nest_ctx" [vis, q, cvO, cvL] m with
  | none => rw [h1] at h; simp [cbposK1] at h
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  rw [h1, cbposK1_some] at h
  obtain ⟨s1, rfl, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (bnc_spec p hP.nck hP.nh hP.bnc n _ vis q cvO cvL) h1
  obtain ⟨⟨c, holes⟩, a1, hrun1, hc1, hho1, hhob1, hS1, hg1, hin1, hsl1, hhi1, hpn1⟩ :=
    bncW_sim n hS hqd hsrc hcv r1 s1.mem hW1
  obtain ⟨c1, ⟨ctxP, holesP⟩, ⟨hctx, hholes, hctxOk, hhw, hpar, -, hnh, -⟩, -⟩ :=
    ConRon.Bridge.Inductives.blockNestCtx_spec fe henv P.shape qP cvTas cvsP hT a a1 (c, holes)
      hC.check ⟨hqP, hcvP⟩ hrun1
  dsimp only at hctx hholes hhw hpar hnh
  have hP1 : PosMR s1.mem := hPM.fr (bncW_mfr hW1)
  have hA1 : AbsOK s1.mem := hk _ (by simp [posKeepCallees]) _ _ _ _ _ h1 hA
  have hC1 : StageC dn vis fe env s1.mem a1 := hC.of_cstep hS1 hA1 c1
  have hU1 : UCtx dn vis fe s1.mem (r1.headD 0) c := ⟨hc1.get (decCtx_mono _), hin1, hsl1⟩
  obtain ⟨hlen, hcb1, hcss1⟩ := pos3_cssAt (hcss.grow decCNSB_mono hg1)
  -- `nest_uniform`
  cases h2 : callW p (n + 2) "nest_uniform" [r1.headD 0, caO, caL] s1.mem with
  | none => rw [h2] at h; simp [cbposK2] at h
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  rw [h2, cbposK2_some] at h
  obtain ⟨s2, rfl, -, hok2, hS2, hg2, hP2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (nestUniform_refines p hP.nu hP.nuCs hP.nuP (n + 2) _ a1 dn fe vis (r1.headD 0) caO caL c css hS1 hU1
      hhi1 hlen hcss1 hP1) h2
  have hrun2 := partsRunOfOk hok2
  obtain ⟨c2, -, -, -⟩ := ConRon.Bridge.Inductives.nestUniform_spec (μ := V) (env := env) (fe := fe)
    env.find? c ctxP css cssP a1 _ _ hC1.check
    ⟨hctx, ConRon.Bridge.Inductives.dCtors_ext.list c1.ext _ _ hcssP⟩ hrun2
  have hA2 : AbsOK s2.mem := hk _ (by simp [posKeepCallees]) _ _ _ _ _ h2 hA1
  have hC2 := hC1.of_cstep hS2 hA2 c2
  -- the empty state
  cases h3 : callW p (n + 2) "check_block_positivity_init" [] s2.mem with
  | none => rw [h3] at h; simp [cbposK3] at h
  | some x3 =>
  obtain ⟨r3, m3⟩ := x3
  rw [h3, cbposK3_some] at h
  obtain ⟨hS3, hg3, hf3, hns3⟩ := pos3_init hP h3 hS2
  have hA3 : AbsOK m3 := hk _ (by simp [posKeepCallees]) _ _ _ _ _ h3 hA2
  have hC3 := hC2.of_pstep hS3 hA3 (PStep.refl hC2.check.state)
  have hg13 := hg2.trans hg3
  -- the root frame
  have hx12 := c1.ext.trans c2.ext
  have hcssP2 := ConRon.Bridge.Inductives.dCtors_ext.list hx12 _ _ hcssP
  have hctx2 := ConRon.Bridge.Inductives.dCtx_ext _ c2.ext _ _ hctx
  have hholes2 := ConRon.Bridge.denoteEList_ext c2.ext _ _ hholes
  have hlenP : ctxP.names.length ≤ holesP.length := by
    rw [ConLeche.nestHoles_length hnh]; exact Nat.le_refl _
  cases h4 : callW p (n + 2) "nest_root" [vis, r1.headD 0, r1.tail.headD 0, r1.tail.tail.headD 0, caO, caL,
      r3.headD 0, 0, 0] m3 with
  | none => rw [h4] at h; simp [cbpK4] at h
  | some x4 =>
  obtain ⟨r4, m4⟩ := x4
  rw [h4, cbpK4_some] at h
  obtain ⟨s4, rfl, -, ⟨outs, ns⟩, a4, hrun4, hC4, hg4, hO4, hOb4, hns4, hP4, hA4, c3⟩ :=
    triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (nestRoot_refinesC hP.rs hq (n + 2) dn vis fe henv hn _ _ (r1.headD 0) (r1.tail.headD 0)
      (r1.tail.tail.headD 0) caO caL (r3.headD 0) 0 0 c holes css {} [] hC3 (hU1.grow hg13) hhi1 hpn1
      (by rw [decHL_grow3 hg13 hhob1]; exact hho1) (Nat.le_trans hhob1 hg13.1) hlen
      (Nat.le_trans hcb1 hg13.1) (hcss1.grow hg13) hns3 (by simp [RootOutsB, DecB, decPL]) (by simp)
      (hP2.fr hf3) hA3 hctxOk (fun y hy => (hhw y hy).1) hlenP hpar hctx2 hholes2 hcssP2
      (nsP := {}) (by simp [dState]) rfl hcl) h4
  obtain ⟨-, ⟨outsP, nsP⟩, ⟨houts, -, hwN⟩, -⟩ := ConRon.Bridge.Inductives.nestRoot_spec coreSpecV henv
    hctxOk holes holesP (fun y hy => (hhw y hy).1) hlenP hpar css cssP {} {} [] [] hcl _ a4 (outs, ns)
    hC3.check ⟨hctx2, hholes2, hcssP2, by simp [dState], rfl⟩ hrun4
  simp only [List.nil_append] at houts
  dsimp only at houts hwN
  have hS4 := hC4.stage
  have hg14 := hg13.trans hg4
  -- `pin_word(53)`
  cases h5 : callW p (n + 2) "pin_word" [53] s4.mem with
  | none => rw [h5] at h; simp [cbpK5] at h
  | some x5 =>
  obtain ⟨r5, m5⟩ := x5
  rw [h5, cbpK5_some] at h
  obtain ⟨s5, rfl, -, hm5, hz5⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (pinWord_specV p hP.pin (n + 2) _ 53) h5
  simp only at hm5 hz5
  rw [hm5] at h
  obtain ⟨hrunz, hzH⟩ := pinZero_stage hS4 hz5
  obtain ⟨-, hz⟩ := ConRon.Bridge.Inductives.zeroLevel_run hC4.check.pins hrunz
  -- `lvl_eq_true`
  obtain ⟨huH, hue⟩ := installCtxWord9 (hc1.grow (decCtx_mono _) hg14) hS4.2.2.2.1
  cases h6 : callW p (n + 2) "lvl_eq_true" [rdW (s4.mem.arr64 IW) (r1.headD 0 + 9), r5.headD 0] s4.mem with
  | none => rw [h6] at h; simp [cbpK6] at h
  | some x6 =>
  obtain ⟨r6, m6⟩ := x6
  rw [h6, cbpK6_some] at h
  obtain ⟨s6, rfl, -, he6⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (eqTrue_specW p hP.eqt (n + 2) _ _ _) h6
  simp only at he6
  unfold eqTrueW at he6
  cases hs6 : stubM "lvl_eq_c" s4.mem [rdW (s4.mem.arr64 IW) (r1.headD 0 + 9), r5.headD 0] with
  | none => rw [hs6] at he6; simp [eqTrueK] at he6
  | some y6 =>
  obtain ⟨r6', m6'⟩ := y6
  rw [hs6, eqTrueK_some] at he6
  simp only [Option.some.injEq, Prod.mk.injEq] at he6
  obtain ⟨hr6, hm6⟩ := he6
  subst hm6
  obtain ⟨y, a6, hrun6, hS6, hg6, hy6⟩ := lvlEqStub_spec dn vis fe _ _ huH hzH s4.mem s6.mem a4 r6' hs6 hS4
  have hP6 : PosMR s6.mem := hP4.fr (MFr.ofStub hs6)
  have hA6 : AbsOK s6.mem := stub_afr hs6 (by decide) hA4
  obtain ⟨namesP, lpsP, paramsP, sortP, hceq, -, -, -, hsort, -⟩ := ConRon.Bridge.Inductives.dCtx_inv hctx
  have hfind : ctxP.find? = env.find? := by rw [hceq]
  have hx14 := c2.ext.trans c3.ext
  have hsort' : ConRon.Arena.denoteL a4.store.ls (decI (rdW (s4.mem.arr64 IW) (r1.headD 0 + 9))) =
      some ctxP.sort := by
    rw [hue, hceq]; exact ConRon.Bridge.denoteL_ext hsort hx14
  obtain ⟨c5, -⟩ := ConRon.Bridge.Inductives.lvlEq?_crun hC4.check hsort' hz hrun6
  have hC6 := hC4.of_check hS6 hA6 c5.ok c5.ext
  have hb6 : (r6.headD 0 != 0) = (y == some true) := by
    rw [← hr6]
    simp only [decLvlEq] at hy6
    rcases y with _ | _ | _ <;> simp_all
  -- the fields' universes at the holes
  have hg16 := hg14.trans hg6
  cases h7 : callW p (n + 2) "check_abs_ctor_sorts_all" [vis, r1.headD 0, r6.headD 0, caO, caL, r4.headD 0,
      r4.tail.headD 0] s6.mem with
  | none => rw [h7] at h; simp [cbpK7] at h
  | some x7 =>
  obtain ⟨r7, m7⟩ := x7
  rw [h7, cbpK7_some] at h
  obtain ⟨s7, rfl, -, hW7⟩ := triple_of_callW (s₀ := ⟨s6.mem, Locals.init []⟩)
    (iaa_spec p hP.abs.all (n + 2) _ _ _ _ _ _ _ _) h7
  have hP7 : PosMR s7.mem := hP6.fr (iaaW_mfr hP.abs _ hW7)
  have hOb6 : (r4.headD 0).toNat + (r4.tail.headD 0).toNat ≤ iwTop s6.mem := Nat.le_trans hOb4 hg6.1
  have hx16 := hx14.trans c5.ext
  obtain ⟨u7, a7, hrun7, hC7, hg7, hA7⟩ := iaaW_simC hq henv hP.abs (r1.headD 0) (r6.headD 0) c
    (y == some true) hb6 hhi1 (n + 2) hn s6.mem a6 caO caL (r4.headD 0) (r4.tail.headD 0) css outs cssP outsP
    hC6 hA6 (hc1.grow (decCtx_mono _) hg16) ((pos3_cns hcss).grow decCNS_mono (hg1.trans hg16))
    ⟨hO4.grow hg6, Or.inr hOb6⟩ (by rw [hfind]; exact ConRon.Bridge.Inductives.dCtx_ext _ hx16 _ _ hctx)
    (ConRon.Bridge.Inductives.dCtors_ext.list (c1.ext.trans hx16) _ _ hcssP)
    (ConRon.Bridge.Inductives.dOutss_ext c5.ext _ _ houts) hwN
    (ConRon.Bridge.denoteFEnv_mono (c1.ext.trans hx16) hfe) r7 s7.mem hW7
  -- the normal forms
  cases h8 : callW p (n + 2) "check_block_positivity_nfs" [r4.headD 0, r4.tail.headD 0] s7.mem with
  | none => rw [h8] at h; simp [cbpK8] at h
  | some x8 =>
  obtain ⟨r8, m8⟩ := x8
  rw [h8, cbpK8_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨s8, rfl, -, hW8⟩ := triple_of_callW (s₀ := ⟨s7.mem, Locals.init []⟩)
    (pnf_spec p hP.nfs.nfs (n + 2) _ _ _) h8
  have hOb7 : (r4.headD 0).toNat + (r4.tail.headD 0).toNat ≤ iwTop s7.mem := Nat.le_trans hOb6 hg7.1
  obtain ⟨hS8, hg8, hf8, hd8⟩ := pnfW_ok hP.nfs (n + 2) _ _ a7 _ _ outs r8 hW8 hC7.stage
    ⟨(hO4.grow (hg6.trans hg7)), hOb7⟩
  have hA8 : AbsOK s8.mem := hk _ (by simp [posKeepCallees]) _ _ _ _ _ h8 hA7
  have hg48 := (hg6.trans hg7).trans hg8
  have hrun : (ConRon.Arena.checkBlockPositivity V fe P cvTas css).run a =
      .ok ((outs.map (·.map (·.1)), outs.map (·.map (·.2)), ns), a7) := by
    simp only [ConRon.Arena.checkBlockPositivity, StateT.run_bind, hrun1, except_ok_bind]
    rw [hrun2]; simp only [except_ok_bind]
    rw [hrun4]; simp only [except_ok_bind]
    rw [hrunz]; simp only [except_ok_bind]
    rw [← hue, hrun6]; simp only [except_ok_bind]
    rw [hrun7]; simp only [except_ok_bind]
    rfl
  obtain ⟨cAll, -⟩ := ConRon.Bridge.Inductives.checkBlockPositivity_spec fe coreSpecV henv P _ cvTas cvsP
    css cssP hT hct a a7 _ hC.check ⟨hpP0, hcvP, hcssP, hfe⟩ hrun
  refine ⟨_, a7, hrun, hC7.of_pstep hS8 hA8 (PStep.refl hC7.check.state), (hg1.trans hg14).trans hg48,
    hP7.fr hf8, hA8, ⟨?_, ?_⟩, ?_, ?_, cAll⟩
  · exact pos3_kinds (hO4.grow hg48)
  · simp only [List.headD_cons, List.tail_cons]; exact Nat.le_trans hOb7 hg8.1
  · simpa using hd8
  · simpa using hns4.grow hg48 (Nat.lt_of_le_of_lt hS4.2.1 hS4.2.2.2.1)

end sim

/-! ## Census -/

section census
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq henv in
/-- **`check_block_positivity` refines `checkBlockPositivity`** under `StageC` (the knot's core
calls; con-ron's `checkBlockPositivity_spec`'s preconditions: the parts, the formers and the
members' constructors denoted, their stored types closed, the index denoting `env`). The shape
record and the formers decoded below the tops, the members' constructors with their slices' bounds
(`decCNSB`), the walk memos well formed (`PosMR`). After: `StageC` at the twin's state, the pools
grown, the walk memos still well formed, the kinds (`decKSS`), the normal forms (`decNFS`), the
walk's state (`NSB`), the twin's run a `CoreStep`. -/
@[refines ConRon.Arena.checkBlockPositivity]
theorem checkBlockPositivity_refinesC (hP : PosBlkProg p) (n : Nat) (hn : n + 2 ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (q cvO cvL caO caL : Word) (P : BlockParts)
    (cvTas : List IConstantVal) (css : List (List (IConstantVal × Nat)))
    (hC : StageC dn vis fe env s₀.mem a₀) (hqd : DecB (fun m => decBS m q.toNat) s₀.mem P.shape)
    (hsrc : ShapeSrc s₀.mem q) (hcv : PSlR decCVp cvTas cvO cvL s₀.mem)
    (hcss : PSlR decCNSB css caO caL s₀.mem) (hPM : PosMR s₀.mem) (hA : AbsOK s₀.mem)
    (hk : ∀ f ∈ posKeepCallees, AbsKeep p f) {pP : ConLeche.BlockParts}
    {cvsP : List ConLeche.ConstantVal} {cssP : List (List (ConLeche.ConstantVal × Nat))}
    (hpP : ConRon.Bridge.Inductives.dParts a₀.store P = some pP)
    (hcvP : cvTas.mapM (Frontend.denoteCV a₀.store) = some cvsP)
    (hcssP : css.mapM (dCtors a₀.store) = some cssP)
    (hfe : ConRon.Bridge.denoteFEnv a₀.store fe = some env)
    (hT : ∀ cv ∈ cvsP, ConLeche.Expr.WScoped 0 cv.type)
    (hct : ∀ cs ∈ cssP, ∀ c ∈ cs, ConLeche.Expr.WScoped 0 c.1.type) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 3)) "check_block_positivity" [vis, q, cvO, cvL, caO, caL]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.checkBlockPositivity V fe P cvTas css) a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (ConRon.Arena.checkBlockPositivity V fe P cvTas css) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ PosMR s'.mem ∧ AbsOK s'.mem ∧
      PSlR decKSS (AM.res (ConRon.Arena.checkBlockPositivity V fe P cvTas css) a₀).1 (r.headD 0)
        (r.tail.headD 0) s'.mem ∧
      PSlR decNFS (AM.res (ConRon.Arena.checkBlockPositivity V fe P cvTas css) a₀).2.1 (r.tail.tail.headD 0)
        (r.tail.tail.tail.headD 0) s'.mem ∧
      NSB s'.mem ((r.drop 4).headD 0) (AM.res (ConRon.Arena.checkBlockPositivity V fe P cvTas css) a₀).2.2 ∧
      ConRon.Bridge.CoreStep V env fe a₀ (AM.st (ConRon.Arena.checkBlockPositivity V fe P cvTas css) a₀);
      ⊤⦄ := by
  refine triple_post (cbpos_spec p hP.cbp (n + 2) s₀ vis q cvO cvL caO caL) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hQ⟩ := cbposW_okC hq henv hP n hn hm hC hqd hsrc hcv hcss hPM hA hk hpP hcvP hcssP hfe
    hT hct
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hl, hok, ?_⟩
  rw [hst, hres]
  exact hQ

end census


end L.Ind
