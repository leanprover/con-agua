import ConAgua.Arena.IndT.KeepC
import ConAgua.Arena.IndT.PosRoot
import ConAgua.Arena.IndT.BncAfr
import ConAgua.Arena.IndT.Install6
import ConAgua.Arena.IndInstallSpec.Pos3Init
import ConAgua.Arena.IndInstallSpec.Pos3NhGoWMfr
import ConAgua.Arena.IndPartsSpec.BrsW
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# `check_block_positivity` under `StageC` (lane `indstaget`, helper `indstaget-cbpos`)

`cbposW_ok`'s proof (`IndInstallSpec/Pos3Init`) under `StageC`, its twin side transcribed from con-ron's
`checkBlockPositivity_spec`: the walk's context (`bncW_sim`, con-ron's `blockNestCtx_spec` on its
run for the `CoreStep` and the context's denotation), `nest_uniform` (`nestUniform_refines`,
`nestUniform_spec`), the fresh state (an L-only step), `nest_root` (`nestRoot_refinesC`; con-ron's
`nestRoot_spec` on its run for the kinds' denotation), `pin_word(53)` (`zeroLevel_run`),
`lvl_eq_c` (its `StageR` contract `lvlEqStub_spec` with `lvlEq?_crun`), the fields' universes
(`iaaW_simC`), the normal forms (an L-only step). The `CoreStep` of the whole run from
`checkBlockPositivity_spec`. No fuel premise against the core walk's: `nest_root`'s `StageC`
version needs none.
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dCtx dCtors dOutss dState)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

private theorem pos_mapM_mem {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ x ∈ l, ∃ y, f x = some y
  | [], _, _, _, hx => absurd hx List.not_mem_nil
  | a :: l, _, h, x, hx => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, hy, ys, hys, -⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨y, hy⟩
    · exact pos_mapM_mem hys x hx
/-! ## `block_nest_ctx` with the real `open_pis_at_fvars_f` -/

theorem opfA_stage : ∀ b ∈ opfA, b < 201 ∨ 208 < b := by
  simp [tier1, tierOff, opfA, instListA, mkA, instA, liftA, SPN, IW, FVREC, FVSLOT, FVLP]
theorem opfC_stage : ∀ x ∈ opfC, x.toNat < 202 ∨ 219 < x.toNat := by
  simp [opfC, instListC, mkC, instC, liftC]

/-- **The model of `block_nest_ctx`, its `open_pis_at_fvars_f` call read through `cR`**
(`bncW` is the stubs' reading) (at exec fuel `n + 2`). -/
noncomputable def bncC (cR : CallM) (n : Nat) (m : Mem) (vis p cvO cvL : Word) : Option (List Word × Mem) :=
  if cvL = 0 then none
  else if rdW (m.arr64 IW) (p + 4) + rdW (m.arr64 IW) (p + 1) < rdW (m.arr64 IW) (p + 4) then none
  else bncK1 n vis p (cR (n + 1) "open_pis_at_fvars_f" [rdW (m.arr64 IW) (p + 4),
    rdW (m.arr64 EREC) (rdW (m.arr64 IW) cvO + 3), 0] m)

set_option experimental.vcgen true in
theorem bnc_specC (p : Prog) (hP : NckProg p) (hl : NhLook p)
    (hp : p.lookup "block_nest_ctx" = some blockNestCtx) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) (s₀ : St) (vis q cvO cvL : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 2)) "block_nest_ctx" [vis, q, cvO, cvL]
    ⦃fun r s' => LocEq s' s₀ ∧ bncC cR n s₀.mem vis q cvO cvL = some (r, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, blockNestCtx]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      hcR (n + 1) "open_pis_at_fvars_f", nck_spec p hP n, nestHoles_spec p hl n] <;>
    finish (gen := 20) [bncC, rdW_eq]

/-- `bncC_sim` with the walk memos: `AbsOK` after, `open_pis_at_fvars_f`'s from its `Sim`, the
rest by `nckW_afr`/`nhW_afr` (lane `indstaget`). -/
theorem bncC_simA (cR : CallM) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) {m : Mem} {a : AState}
    {q cvO cvL : Word} {bs : BlockShape} {cvTas : List IConstantVal} (_hS : StageR dn vis fe m a)
    (hq : DecB (fun m => decBS m q.toNat) m bs)
    (hsrc : ∀ o l, iwN m q.toNat = some o → iwN m (q.toNat + 1) = some l → o + l ≤ iwTop m)
    (hcv : PSlR decCVp cvTas cvO cvL m)
    (hopf : ∀ e : Word, H e → Sim (cR (n + 1) "open_pis_at_fvars_f" [rdW (m.arr64 IW) (q + 4), e, 0] m)
      (openPisAtFvarsF (rdW (m.arr64 IW) (q + 4)).toNat (decI e) (0 : Word).toNat) a
      (fun r x m' a' => (StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decOLE m' r x) ∧ AbsOK m')) :
    Sim (bncC cR n m vis q cvO cvL) (ConRon.Arena.blockNestCtx fe bs cvTas) a
      (fun r x m' a' => DecB (fun m => decCtx m (r.headD 0).toNat) m' x.1 ∧
        decHL m' (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat = some x.2 ∧
        (r.tail.headD 0).toNat + (r.tail.tail.headD 0).toNat ≤ iwTop m' ∧
        StageR dn vis fe m' a' ∧ IWGrow m m' ∧
        CtxIn m' (r.headD 0).toNat (· < iwTop m') ∧ CtxSl m' (r.headD 0).toNat ∧ x.1.hiAt 0 < 2 ^ 64 ∧
        x.1.params.length + x.1.names.length < 2 ^ 64 ∧ AbsOK m') := by
  intro r m' e
  unfold bncC at e
  split at e
  · cases e
  rename_i hl
  split at e
  · cases e
  rename_i hov
  obtain ⟨pc, cv0, cvs, rfl, hw, hpb, hcv0, -⟩ := partsPSl_cons hcv hl
  obtain ⟨htyl, htye⟩ := partsCVType hcv0 (UInt64.toNat_ofNat_of_lt' hpb)
  obtain ⟨hq', hq9, -⟩ := partsShapeFacts hq hsrc
  obtain ⟨hnpw, hnpb, -, -⟩ := partsShapeWords (IWGrow.refl m) hq hq9
  have hkw := partsShapeK hq' hq9
  have hkb : bs.k < 2 ^ 64 := by
    obtain ⟨o, l, -, hl', hg'⟩ := decAt_some (decBS_some hq').1
    have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
    have := iwN_rdW hl' (by omega); rw [BlockShape.k, decPL_length _ hg']; exact this.2
  have hhi : bs.nP + bs.k < 2 ^ 64 := by
    have := partsAddNoOv hov
    rw [hnpw, hkw, UInt64.toNat_ofNat_of_lt' hnpb, UInt64.toNat_ofNat_of_lt' hkb] at this
    have := (rdW (m.arr64 IW) (q + 4) + rdW (m.arr64 IW) (q + 1)).toNat_lt
    rw [hnpw, hkw] at this; omega
  rw [hw] at e
  revert r m' e
  unfold ConRon.Arena.blockNestCtx
  dsimp only
  have h1 := hopf (rdW (m.arr64 EREC) (UInt64.ofNat pc + 3)) htyl
  rw [show (rdW (m.arr64 IW) (q + 4)).toNat = bs.nP from by rw [hnpw, UInt64.toNat_ofNat_of_lt' hnpb],
    show decI (rdW (m.arr64 EREC) (UInt64.ofNat pc + 3)) = cv0.type from htye,
    show (0 : Word).toNat = 0 from rfl] at h1
  refine Sim.bindK (K := bncK1 n vis q) (body := fun r1 m1 => if r1.headD 0 = 0 then none
      else if r1.tail.tail.headD 0 + rdW (m1.arr64 IW) (q + 1) < r1.tail.tail.headD 0 then none
      else bncK2 n vis (nckW n m1 q (r1.tail.headD 0) (r1.tail.tail.headD 0))) rfl (fun _ _ => rfl) h1 ?_
  rintro r1 x1 m1 a1 ⟨⟨hS1, hg1, hd1⟩, hA1⟩
  cases x1 with
  | none =>
    have h0 : r1.headD 0 = 0 := hd1
    simp only [h0, ite_true]
    exact Sim.of_none
  | some pq =>
  obtain ⟨fvs, body⟩ := pq
  obtain ⟨h1', hfv, -⟩ := hd1
  obtain ⟨hfd, hfb⟩ := hfv
  simp only [h1', show (1 : Word) ≠ 0 by decide, ite_false]
  have g1 : r1.getD 1 0 = r1.tail.headD 0 := by rcases r1 with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
  have g2 : r1.getD (1 + 1) 0 = r1.tail.tail.headD 0 := by rcases r1 with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
  rw [g1, g2] at hfd hfb
  by_cases hov2 : r1.tail.tail.headD 0 + rdW (m1.arr64 IW) (q + 1) < r1.tail.tail.headD 0
  · simp only [hov2, ite_true]; exact Sim.of_none
  simp only [hov2, ite_false]
  have hTm : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hk1 : rdW (m1.arr64 IW) (q + 1) = UInt64.ofNat bs.k := by
    rw [← hkw]; simp only [rdW]
    rw [show (q + 1 : Word).toNat = q.toNat + 1 by rw [UInt64.toNat_add]; simp; omega, hg1.2.2.1 _ (by omega)]
  have hpk : fvs.length + bs.k < 2 ^ 64 := by
    have := partsAddNoOv hov2
    rw [hk1, UInt64.toNat_ofNat_of_lt' hkb] at this
    have := (r1.tail.tail.headD 0 + UInt64.ofNat bs.k).toNat_lt
    rw [decHL_length _ hfd]; omega
  intro r m' e
  rcases h2 : nckW n m1 q (r1.tail.headD 0) (r1.tail.tail.headD 0) with _ | ⟨r2, m2⟩ <;> rw [h2] at e; · cases e
  rw [bncK2_some] at e
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨hok2, hd2, hS2, hg2, hin2, hsl2⟩ := nckW_ok n ⟨m1, Locals.init []⟩ ⟨m2, Locals.init []⟩ a1 dn vis fe q
    (r1.tail.headD 0) (r1.tail.tail.headD 0) bs fvs hS1 (hq.grow (decBS_mono _) hg1)
    (partsHsrc_grow hg1 hq9 hsrc) hfd hfb r2 h2
  have hrun2 := partsRunOfOk hok2
  generalize hc : AM.res (bs.nestCtx fvs) a1 = c at hrun2 hd2
  generalize ha2 : AM.st (bs.nestCtx fvs) a1 = a2 at hrun2 hS2
  have hnc : c = ⟨bs.memberNames, bs.lps, bs.nP, bs.nIdxs, fvs, bs.resSort, c.lvls⟩ := by
    have h' := hrun2
    unfold ConRon.Arena.BlockShape.nestCtx at h'
    obtain ⟨lv, a', -, h'⟩ := partsBindOk h'
    simp [StateT.run, pure, StateT.pure, Except.pure] at h'
    rw [← h'.1]
  have hhi' : c.hiAt 0 < 2 ^ 64 := by
    rw [hnc]; simp only [NestCtx.hiAt, BlockShape.memberNames, List.length_map]
    have : bs.k = bs.members.length := rfl
    omega
  rcases h3 : nhW n m2 vis (r2.headD 0) with _ | ⟨r3, m3⟩ <;> rw [h3] at e; · simp [bncK3] at e
  obtain ⟨holes, a3, hrun3, hR3, hS3, hg3⟩ := nhW_sim n hS2 (hd2.get (decCtx_mono _)) hin2 hsl2 hhi' r3 m3 h3
  cases holes with
  | none =>
    have h0 : r3.headD 0 = 0 := hR3
    rw [bncK3_none (h := h0)] at e; cases e
  | some hs =>
  obtain ⟨h31, hd3, hb3⟩ := hR3
  rw [bncK3_some (h := by rw [h31]; decide)] at e
  simp only [Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  refine ⟨(c, hs), a3, ?_, ?_, hd3, hb3, hS3, (hg1.trans hg2).trans hg3, (CtxIn.grow hin2 hg3).2,
    hsl2.grow hin2 hg3, hhi', ?_, nhW_afr h3 (nckW_afr h2 hA1)⟩
  · simp only [unwrapOr, StateT.run_bind, pure_bind]
    simp only [StateT.run_pure, except_ok_bind, hrun2, hrun3]
    rfl
  · exact hd2.grow (decCtx_mono _) hg3
  · rw [hnc]; simp only [BlockShape.memberNames, List.length_map]
    have : bs.k = bs.members.length := rfl
    omega

/-- **`block_nest_ctx`'s model, its `open_pis_at_fvars_f` the real call, leaves the walk memos
alone** (`bncW_mfr`'s). -/
theorem bncC_mfr {p : Prog} (hOpf : OpfF p) {n : Nat} {m m' : Mem} {vis q cvO cvL : Word} {r : List Word}
    (h : bncC (realCall p) n m vis q cvO cvL = some (r, m')) : MFr [] [] m m' := by
  unfold bncC at h
  split at h; · cases h
  split at h; · cases h
  rcases h1 : realCall p (n + 1) "open_pis_at_fvars_f" [rdW (m.arr64 IW) (q + 4),
      rdW (m.arr64 EREC) (rdW (m.arr64 IW) cvO + 3), 0] m with _ | ⟨r1, m1⟩; · rw [h1] at h; simp [bncK1] at h
  rw [h1] at h
  have f1 := MFr.of_frame (opfF_frame (callW_opfF hOpf h1)) opfA_stage opfC_stage
  by_cases h0 : r1.headD 0 = 0
  · rw [bncK1_none n m1 vis q r1 h0] at h; cases h
  by_cases hov : r1.tail.tail.headD 0 + rdW (m1.arr64 IW) (q + 1) < r1.tail.tail.headD 0
  · rw [bncK1_ov n m1 vis q r1 h0 hov] at h; cases h
  rw [bncK1_some n m1 vis q r1 h0 hov] at h
  rcases h2 : nckW n m1 q (r1.tail.headD 0) (r1.tail.tail.headD 0) with _ | ⟨r2, m2⟩ <;> rw [h2] at h; · simp [bncK2] at h
  rw [bncK2_some] at h
  have f2 := f1.trans (pos3_nckW_mfr h2)
  rcases h3 : nhW n m2 vis (r2.headD 0) with _ | ⟨r3, m3⟩ <;> rw [h3] at h; · simp [bncK3] at h
  by_cases h30 : r3.headD 0 = 0
  · rw [bncK3_none m3 (r2.headD 0) r3 h30] at h; cases h
  simp only [bncK3_some m3 (r2.headD 0) r3 h30, Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.2]
  exact f2.trans (pos3_nhGoW_mfr _ _ _ _ _ _ _ _ _ _ _ h3)

section sim
variable {p : Prog} (hq : KnotStageProg p) (hIlpf : IlpfF p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hOpf : OpfF p) (hLC : LvlCacheProg p) (hLT : p.lookup "lv_leq_top" = some lvLeqTop) (hApd : ApdF p)

include hq hIlpf henv hOpf hLC hLT hApd in
/-- **`check_block_positivity`'s model refines `checkBlockPositivity` under `StageC`** (con-ron's
`checkBlockPositivity_spec`'s preconditions). -/
theorem cbposW_okC (hP : PosBlkProg p) {fs : List FnName} (hclP : closedA p posFreeA posFreeC fs = true)
    (hfa : "check_abs_ctor_sorts_all" ∈ fs) (n : Nat) (hn : n + 2 ≤ 2 ^ 62) {m m' : Mem} {a : AState}
    {q cvO cvL caO caL : Word} {P : BlockParts} {cvTas : List IConstantVal}
    {css : List (List (IConstantVal × Nat))} {r : List Word} {pP : ConLeche.BlockParts}
    {cvsP : List ConLeche.ConstantVal} {cssP : List (List (ConLeche.ConstantVal × Nat))}
    (h : cbposW p (n + 3) m vis q cvO cvL caO caL = some (r, m')) (hC : StageC dn vis fe env m a)
    (hqd : DecB (fun m => decBS m q.toNat) m P.shape) (hsrc : ShapeSrc m q)
    (hcv : PSlR decCVp cvTas cvO cvL m) (hcss : PSlR decCNSB css caO caL m) (hPM : PosMR m)
    (hA : AbsOK m) (hk : ∀ f ∈ posKeepCalleesC, AbsKeep p f)
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
  rw [cbposW.arm1] at h
  -- the walk's context
  rcases h1 : callW p (n + 2) "block_nest_ctx" [vis, q, cvO, cvL] m with _ | ⟨r1, m1⟩ <;> rw [h1] at h; · simp [cbposW.k_block_nest_ctx.none] at h
  rw [cbposW.k_block_nest_ctx.arm1] at h
  obtain ⟨s1, rfl, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (bnc_specC p hP.nck hP.nh hP.bnc (realCall p) (realCall_spec p) n _ vis q cvO cvL) h1
  obtain ⟨⟨c, holes⟩, a1, hrun1, hc1, hho1, hhob1, hS1, hg1, hin1, hsl1, hhi1, hpn1, hA1⟩ :=
    bncC_simA (realCall p) n hS hqd hsrc hcv
      (fun _ he => Sim.mono (opfSimRA (n := n + 1) hOpf he hS hA) fun _ _ _ _ h => ⟨h.1.1, h.2⟩) r1 s1.mem hW1
  obtain ⟨c1, ⟨ctxP, holesP⟩, ⟨hctx, hholes, hctxOk, hhw, hpar, -, hnh, -⟩, -⟩ :=
    ConRon.Bridge.Inductives.blockNestCtx_spec fe henv P.shape qP cvTas cvsP hT a a1 (c, holes)
      hC.check ⟨hqP, hcvP⟩ hrun1
  dsimp only at hctx hholes hhw hpar hnh
  have hP1 : PosMR s1.mem := hPM.fr (bncC_mfr hOpf hW1)
  have hC1 : StageC dn vis fe env s1.mem a1 := hC.of_cstep hS1 hA1 c1
  have hU1 : UCtx dn vis fe s1.mem (r1.headD 0) c := ⟨hc1.get (decCtx_mono _), hin1, hsl1⟩
  obtain ⟨hlen, hcb1, hcss1⟩ := pos3_cssAt (hcss.grow decCNSB_mono hg1)
  -- `nest_uniform`
  rcases h2 : callW p (n + 2) "nest_uniform" [r1.headD 0, caO, caL] s1.mem with _ | ⟨r2, m2⟩ <;> rw [h2] at h; · simp [cbposW.k_nest_uniform.none] at h
  rw [cbposW.k_nest_uniform.arm1] at h
  obtain ⟨s2, rfl, -, hw2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (nestUniform_spec p hP.nu hP.nuCs hP.nuP (realCall p) (realCall_spec p) (n + 2) _ (r1.headD 0) caO caL) h2
  have hcss1P := ConRon.Bridge.Inductives.dCtors_ext.list c1.ext _ _ hcssP
  have hPc : ∀ cs ∈ css, ∀ x ∈ cs, ∃ cvP, Frontend.denoteCV a1.store x.1 = some cvP := by
    intro cs hcs x hx
    obtain ⟨y, hy⟩ := pos_mapM_mem hcss1P cs hcs
    obtain ⟨z, hz⟩ := pos_mapM_mem hy x hx
    simp only [ConRon.Bridge.Inductives.dCtor, Option.map_eq_some_iff] at hz
    obtain ⟨cvP, hcvP', -⟩ := hz
    exact ⟨cvP, hcvP'⟩
  obtain ⟨a2, hrun2, hS2, hg2, hP2, hJ2⟩ := unW_ok dn fe vis (r1.headD 0) c hhi1 (realCall p)
    (fun m' a' => StageC dn vis fe env m' a' ∧ AbsOK m' ∧ ConRon.Arena.Ext a1.store a'.store)
    (fun cvv => ∃ cvP, Frontend.denoteCV a1.store cvv = some cvP)
    (fun _ a' _ cvv hJ hPx _ _ m1' a1' _ b hpd hrun hS1' => by
      obtain ⟨hCm, hAm, hxm⟩ := hJ
      obtain ⟨cvP, hcvP'⟩ := hPx
      obtain ⟨-, -, hty⟩ := ConRon.Bridge.Core.denoteCV_inv hcvP'
      obtain ⟨hcn, -⟩ := ConRon.Bridge.Inductives.dCtx_fields
        (ConRon.Bridge.Inductives.dCtx_ext _ hxm _ _ hctx)
      obtain ⟨p1', -⟩ := ConRon.Bridge.Inductives.piDomsOcc_spec c.names ctxP.names c.nP (c.hiAt 0) c.nP
        cvv.type cvP.type a' a1' b hCm.check.state ⟨hcn, ConRon.Bridge.denote_ext hty hxm⟩ hrun
      exact IlpRd.realC hIlpf (hCm.of_pstep hS1' (pdoW_afr _ _ _ _ _ _ _ _ _ _ hpd hAm) p1'))
    (fun _ _ _ a' a'' _ cvv _ _ hJ hPx _ hrun hS' hA' => by
      obtain ⟨hCm, hAm, hxm⟩ := hJ
      obtain ⟨cvP, hcvP'⟩ := hPx
      obtain ⟨c3, -⟩ := ConRon.Bridge.Inductives.nestUniformOk_spec (μ := V) (env := env) (fe := fe)
        env.find? c ctxP cvv cvP a' a'' _ hCm.check
        ⟨ConRon.Bridge.Inductives.dCtx_ext _ hxm _ _ hctx, ConRon.Bridge.denoteCV_ext hcvP' hxm⟩ hrun
      have hAm' := hA' nuAfr hAm
      exact ⟨hCm.of_cstep hS' hAm' c3, hAm', hxm.trans c3.ext⟩)
    (n + 2) s1.mem s2.mem a1 caO caL css hw2 hS1 ⟨hC1, hA1, ConRon.Arena.Ext.refl _⟩ hPc hU1 hlen hcss1 hP1
  obtain ⟨c2, -, -, -⟩ := ConRon.Bridge.Inductives.nestUniform_spec (μ := V) (env := env) (fe := fe)
    env.find? c ctxP css cssP a1 _ _ hC1.check
    ⟨hctx, hcss1P⟩ hrun2
  have hA2 : AbsOK s2.mem := hJ2.2.1
  have hC2 := hC1.of_cstep hS2 hA2 c2
  -- the empty state
  rcases h3 : callW p (n + 2) "check_block_positivity_init" [] s2.mem with _ | ⟨r3, m3⟩ <;> rw [h3] at h; · simp [cbposW.k_check_block_positivity_init.none] at h
  rw [cbposW.k_check_block_positivity_init.arm1] at h
  obtain ⟨hS3, hg3, hf3, hns3⟩ := pos3_init hP h3 hS2
  have hA3 : AbsOK m3 := hk _ (by simp [posKeepCalleesC]) _ _ _ _ _ h3 hA2
  have hC3 := hC2.of_pstep hS3 hA3 (PStep.refl hC2.check.state)
  have hg13 := hg2.trans hg3
  -- the root frame
  have hx12 := c1.ext.trans c2.ext
  have hcssP2 := ConRon.Bridge.Inductives.dCtors_ext.list hx12 _ _ hcssP
  have hctx2 := ConRon.Bridge.Inductives.dCtx_ext _ c2.ext _ _ hctx
  have hholes2 := ConRon.Bridge.denoteEList_ext c2.ext _ _ hholes
  have hlenP : ctxP.names.length ≤ holesP.length := by
    rw [ConLeche.nestHoles_length hnh]; exact Nat.le_refl _
  rcases h4 : callW p (n + 2) "nest_root" [vis, r1.headD 0, r1.tail.headD 0, r1.tail.tail.headD 0, caO, caL,
      r3.headD 0, 0, 0] m3 with _ | ⟨r4, m4⟩; · rw [h4] at h; simp [cbposW.k_nest_root.none] at h
  rw [h4, cbposW.k_nest_root.arm1] at h
  obtain ⟨s4, rfl, -, ⟨outs, ns⟩, a4, hrun4, hC4, hg4, hO4, hOb4, hns4, hP4, hA4, c3⟩ :=
    triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (nestRoot_refinesC hP.rs hq hIlpf hLC (n + 2) dn vis fe henv hn _ _ (r1.headD 0) (r1.tail.headD 0)
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
  rcases h5 : callW p (n + 2) "pin_word" [53] s4.mem with _ | ⟨r5, m5⟩ <;> rw [h5] at h; · simp [cbposW.k_pin_word.none] at h
  rw [cbposW.k_pin_word.arm1] at h
  obtain ⟨s5, rfl, -, hm5, hz5⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (pinWord_specV p hP.pin (n + 2) _ 53) h5
  simp only at hm5 hz5
  rw [hm5] at h
  obtain ⟨hrunz, hzH⟩ := pinZero_stage hS4 hz5
  obtain ⟨-, hz⟩ := ConRon.Bridge.Inductives.zeroLevel_run hC4.check.pins hrunz
  -- `lvl_eq_true`
  obtain ⟨huH, hue⟩ := installCtxWord9 (hc1.grow (decCtx_mono _) hg14) hS4.2.2.2.1
  rcases h6 : callW p (n + 2) "lvl_eq_true" [rdW (s4.mem.arr64 IW) (r1.headD 0 + 9), r5.headD 0] s4.mem with _ | ⟨r6, m6⟩ <;> rw [h6] at h; · simp [cbposW.k_lvl_eq_true.none] at h
  rw [cbposW.k_lvl_eq_true.arm1] at h
  obtain ⟨s6, rfl, -, he6⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (eqTrue_specC p hP.eqt (realCall p) (realCall_spec p) (n + 2) _ _ _) h6
  simp only at he6
  rw [eqTrueC_succ] at he6
  rcases hs6 : realCall p (n + 1) "lvl_eq_c" [rdW (s4.mem.arr64 IW) (r1.headD 0 + 9), r5.headD 0] s4.mem with _ | ⟨r6', m6'⟩ <;> rw [hs6] at he6; · simp [eqTrueK] at he6
  rw [eqTrueK_some] at he6
  obtain ⟨hr6, hm6⟩ := Prod.mk.inj (Option.some.inj he6)
  subst hm6
  obtain ⟨namesP, lpsP, paramsP, sortP, hceq, -, -, -, hsort, -⟩ := ConRon.Bridge.Inductives.dCtx_inv hctx
  have hfind : ctxP.find? = env.find? := by rw [hceq]
  have hx14 := c2.ext.trans c3.ext
  have hsort' : ConRon.Arena.denoteL a4.store.ls (decI (rdW (s4.mem.arr64 IW) (r1.headD 0 + 9))) =
      some ctxP.sort := by
    rw [hue, hceq]; exact ConRon.Bridge.denoteL_ext hsort hx14
  obtain ⟨y, a6, hrun6, hC6, hg6, hy6, hA6, -⟩ :=
    lvlEqC_simC p hq.closed hLC (n + 1) hC4 hA4 _ _ huH hzH _ _ hsort' hz r6' s6.mem hs6
  have hS6 := hC6.stage
  have hP6 : PosMR s6.mem :=
    hP4.fr (MFr.of_frame (run_memFrame hq.closed (by decide) (run_of_callW hs6)).1 coreStageA_stage
      coreStageC_stage)
  obtain ⟨c5, -⟩ := ConRon.Bridge.Inductives.lvlEq?_crun hC4.check hsort' hz hrun6
  have hb6 : (r6.headD 0 != 0) = (y == some true) := by
    rw [← hr6]
    simp only [decLvlEq] at hy6
    rcases y with _ | _ | _ <;> simp_all
  -- the fields' universes at the holes
  have hg16 := hg14.trans hg6
  rcases h7 : callW p (n + 2) "check_abs_ctor_sorts_all" [vis, r1.headD 0, r6.headD 0, caO, caL, r4.headD 0,
      r4.tail.headD 0] s6.mem with _ | ⟨r7, m7⟩; · rw [h7] at h; simp [cbposW.k_check_abs_ctor_sorts_all.none] at h
  rw [h7, cbposW.k_check_abs_ctor_sorts_all.arm1] at h
  obtain ⟨s7, rfl, -, hW7⟩ := triple_of_callW (s₀ := ⟨s6.mem, Locals.init []⟩)
    (iaa_spec p hP.abs.all (n + 2) _ _ _ _ _ _ _ _) h7
  have hP7 : PosMR s7.mem := PosMR.ofClosed hclP hfa h7 hP6
  have hOb6 : (r4.headD 0).toNat + (r4.tail.headD 0).toNat ≤ iwTop s6.mem := Nat.le_trans hOb4 hg6.1
  have hx16 := hx14.trans c5.ext
  obtain ⟨u7, a7, hrun7, hC7, hg7, hA7⟩ := iaaW_simC hq henv hOpf hLC hLT hApd hP.abs (r1.headD 0) (r6.headD 0) c
    (y == some true) hb6 hhi1 (n + 2) hn s6.mem a6 caO caL (r4.headD 0) (r4.tail.headD 0) css outs cssP outsP
    hC6 hA6 (hc1.grow (decCtx_mono _) hg16) ((pos3_cns hcss).grow decCNS_mono (hg1.trans hg16))
    ⟨hO4.grow hg6, Or.inr hOb6⟩ (by rw [hfind]; exact ConRon.Bridge.Inductives.dCtx_ext _ hx16 _ _ hctx)
    (ConRon.Bridge.Inductives.dCtors_ext.list (c1.ext.trans hx16) _ _ hcssP)
    (ConRon.Bridge.Inductives.dOutss_ext c5.ext _ _ houts) hwN
    (ConRon.Bridge.denoteFEnv_mono (c1.ext.trans hx16) hfe) r7 s7.mem hW7
  -- the normal forms
  rcases h8 : callW p (n + 2) "check_block_positivity_nfs" [r4.headD 0, r4.tail.headD 0] s7.mem with _ | ⟨r8, m8⟩ <;> rw [h8] at h; · simp [cbposW.k_check_block_positivity_nfs.none] at h
  rw [cbposW.k_check_block_positivity_nfs.arm1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨s8, rfl, -, hW8⟩ := triple_of_callW (s₀ := ⟨s7.mem, Locals.init []⟩)
    (pnf_spec p hP.nfs.nfs (n + 2) _ _ _) h8
  have hOb7 : (r4.headD 0).toNat + (r4.tail.headD 0).toNat ≤ iwTop s7.mem := Nat.le_trans hOb6 hg7.1
  obtain ⟨hS8, hg8, hf8, hd8⟩ := pnfW_ok hP.nfs (n + 2) _ _ a7 _ _ outs r8 hW8 hC7.stage
    ⟨(hO4.grow (hg6.trans hg7)), hOb7⟩
  have hA8 : AbsOK s8.mem := hk _ (by simp [posKeepCalleesC]) _ _ _ _ _ h8 hA7
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
variable {p : Prog} (hq : KnotStageProg p) (hIlpf : IlpfF p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hOpf : OpfF p) (hLC : LvlCacheProg p) (hLT : p.lookup "lv_leq_top" = some lvLeqTop) (hApd : ApdF p)

include hq hIlpf henv hOpf hLC hLT hApd in
/-- **`check_block_positivity` refines `checkBlockPositivity`** under `StageC` (the knot's core
calls; con-ron's `checkBlockPositivity_spec`'s preconditions: the parts, the formers and the
members' constructors denoted, their stored types closed, the index denoting `env`). The shape
record and the formers decoded below the tops, the members' constructors with their slices' bounds
(`decCNSB`), the walk memos well formed (`PosMR`). After: `StageC` at the twin's state, the pools
grown, the walk memos still well formed, the kinds (`decKSS`), the normal forms (`decNFS`), the
walk's state (`NSB`), the twin's run a `CoreStep`. -/
@[refines ConRon.Arena.checkBlockPositivity]
theorem checkBlockPositivity_refinesC (hP : PosBlkProg p) {fs : List FnName}
    (hclP : closedA p posFreeA posFreeC fs = true) (hfa : "check_abs_ctor_sorts_all" ∈ fs) (n : Nat) (hn : n + 2 ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (q cvO cvL caO caL : Word) (P : BlockParts)
    (cvTas : List IConstantVal) (css : List (List (IConstantVal × Nat)))
    (hC : StageC dn vis fe env s₀.mem a₀) (hqd : DecB (fun m => decBS m q.toNat) s₀.mem P.shape)
    (hsrc : ShapeSrc s₀.mem q) (hcv : PSlR decCVp cvTas cvO cvL s₀.mem)
    (hcss : PSlR decCNSB css caO caL s₀.mem) (hPM : PosMR s₀.mem) (hA : AbsOK s₀.mem)
    (hk : ∀ f ∈ posKeepCalleesC, AbsKeep p f) {pP : ConLeche.BlockParts}
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
  refine triple_post (cbpos_spec p hP.cbp (n + 3) s₀ vis q cvO cvL caO caL) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hQ⟩ := cbposW_okC hq hIlpf henv hOpf hLC hLT hApd hP hclP hfa n hn hm hC hqd hsrc hcv hcss hPM hA hk hpP hcvP hcssP hfe
    hT hct
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hl, hok, ?_⟩
  rw [hst, hres]
  exact hQ

end census

end L.Ind
