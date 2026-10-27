import ConAgua.Verdict.IndA2
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Verdict.IndAGen

/-!
# `check_block_pass`'s error refinement (lane `verdicts-b`, helper `ia`)

`checkBlockPassE_claim`: `CheckBlockPassE p` from the claims of `check_block_inds`,
`check_block_ctors`, `check_block_classes`, `check_block_positivity` and `nest_seeds` (generated
`err_stmt`s of their `…_refinesC`). `flush_caches`, `block_nest_ctx`, `class_seeds` and
`check_block_pass_rec` are outside the verdict closure.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model icpE_spec (p : Prog) (hf : p.lookup "check_block_pass" = some checkBlockPass)
  fns [hf ↦ icpE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

-- the error claims of the pass's callees, in the shape of their ok refinements
err_stmt CheckBlockIndsE := checkBlockInds_refinesC fuel n
err_stmt CheckBlockCtorsE := checkBlockCtors_refinesC fuel n
err_stmt CheckBlockClassesE := checkBlockClasses_refinesC fuel n
err_stmt CheckBlockPositivityE := checkBlockPositivity_refinesC fuel n
err_stmt NestSeedsE := nestSeeds_refinesC fuel n

section
variable {p : Prog}

theorem checkBlockPassE_claim (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (eInds : CheckBlockIndsE p) (eCtors : CheckBlockCtorsE p) (eCls : CheckBlockClassesE p)
    (ePos : CheckBlockPositivityE p) (eSeeds : NestSeedsE p) : CheckBlockPassE p := by
  intro hkp env henv hV hOpf hLC hLT hApd hCrk hIlpf hLz hP fs hcl hfs s₀ a dn vis fe p0 isRec bs b hC hq hsrc hcx hb hPm hA hk hcoh hden shP hshP hlpsDn F hF e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  replace he := triple_of_callE_err (icpE_spec p hP.pass F ⟨s₀.mem, Locals.init []⟩ vis p0 isRec) he
    (Err.code_ne_of_cls hk0)
  simp only at he
  generalize hm : s₀.mem = m at hC hq hsrc hcx hPm hA he
  cases F with
  | zero => rw [icpE.eq_1] at he; cases he; exact absurd Err.cls_outOfFuel hk0
  | succ F =>
  obtain ⟨n, hn, hle⟩ : ∃ n, n + 4 ≤ 2 ^ 62 ∧ F ≤ n + 3 := ⟨F - 3, by omega, by omega⟩
  rw [icpE.arm1] at he
  unfold ConRon.Arena.checkBlockPass
  have hk' : ∀ f, f ∈ passKeepCalleesC → AbsKeep p f := hk
  have hkP : ∀ f, f ∈ passKeepCalleesC → AbsKeep p f := fun f hf => hk' f hf
  have hcs : ConRon.Bridge.CoreSpec V ConRon.Arena.checkFuel := ConRon.Bridge.CoreSpec.of_core rfl
  have dnE : ∀ {st : ConRon.Arena.EStore}, ConRon.Arena.Ext a.store st →
      ∀ (k : NIdx) (x : ConLeche.Name), dn k = some x → denoteN st.ns k = some x :=
    fun hx k x e => hx.lss.ls.ns k x (hC.mem.dnN k x e)
  have hpP : ConRon.Bridge.Inductives.dParts a.store ⟨bs⟩ = some ⟨shP⟩ := by
    simp only [ConRon.Bridge.Inductives.dParts, hshP, Option.map_some]
  -- the formers
  cases c1 : callE p F "check_block_inds" [vis, p0, isRec] m with
  | error e1 =>
    rw [c1, icpE.k_check_block_inds.none] at he
    cases he
    exact ErrClaim.bind_left (eInds hkp henv hV hOpf hLC hApd hCrk hLz hP.inds ⟨m, Locals.init []⟩ a p0 isRec bs b hC hq hsrc hcx hb hA
      (fun f hf => hkP f (List.mem_append_left _ (List.mem_append_right _ hf))) hshP hden hcoh hlpsDn F (by omega) _ c1)
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [c1, icpE.k_check_block_inds.eq_2] at he
  have d1 := callW_mono (callW_of_callE c1) hle
  obtain ⟨s1, hs1, -, hok1, hout, hA1, hrb1, -⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (checkBlockInds_refinesC hkp henv hV hOpf hLC hApd hCrk hLz hP.inds (n + 2) (by omega) _ a p0 isRec bs b hC hq hsrc hcx hb hA
      (fun f hf => hkP f (List.mem_append_left _ (List.mem_append_right _ hf))) hshP hden hcoh hlpsDn) d1
  simp only at hs1 hout
  subst hs1
  have hrun1 := AM.run_of_ok _ a hok1
  generalize AM.res (ConRon.Arena.checkBlockInds V fe ⟨bs⟩ b) a = x1 at hrun1 hout
  generalize AM.st (ConRon.Arena.checkBlockInds V fe ⟨bs⟩ b) a = a1 at hrun1 hout
  obtain ⟨fe1, cvTas, bs1⟩ := x1
  refine ErrClaim.bind_right hrun1 ?_
  try dsimp only
  obtain ⟨hS1, hg1, hcv1, hbs1, hsrc1⟩ := hout
  obtain ⟨k1, ⟨env₁, cvTasP, p₁P⟩, ⟨hrel1, hOKS1, hcvs, hsh1, hT⟩, hF1⟩ :=
    ConRon.Bridge.Inductives.checkBlockInds_spec fe rfl hcs henv hcoh ⟨bs⟩ ⟨shP⟩ b a a1 _ hC.check
      ⟨hpP, hden⟩ hrun1
  dsimp only at hrel1 hOKS1 hcvs hsh1 hT hF1
  have henv₁ : ConLeche.EnvWF env₁ := by
    obtain ⟨F, hF⟩ := hF1
    rw [ConLeche.checkBlockInds_datF] at hF
    exact (ConLeche.direct_block_inds_wf henv hF).1
  have hden₁ : ConRon.Bridge.denoteFEnv a1.store fe1 = some env₁ := by
    obtain ⟨e, h, rfl⟩ := hrel1.denote; exact h
  have x01 : ConRon.Arena.Ext a.store a1.store := k1.ext
  have hP1 := PosMR.ofClosed hcl (hfs _ (by decide)) d1 hPm
  simp only at hS1 hcv1 hbs1
  have hT1 : iwTop s1.mem < 2 ^ 64 := (rdW (s1.mem.arr64 CTL) 200).toNat_lt
  obtain ⟨-, hq9, hmemv⟩ := partsShapeFacts hbs1 hsrc1
  -- the flush
  cases c2 : callE p F "flush_caches" [] s1.mem with
  | error e2 =>
    rw [c2, icpE.k_flush_caches.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) c2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [c2, icpE.k_flush_caches.eq_2] at he
  have d2 := callW_mono (callW_of_callE c2) hle
  obtain ⟨s2, hs2, -, hfok, hfm⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (flushCaches_spec p hP.flush (n + 3) _) d2
  simp only at hs2 hfok hfm
  subst hs2
  obtain ⟨hS2, hg2⟩ := flush_stage hS1 hfok
  rw [← hfm] at hS2 hg2
  have hP2 : PosMR s2.mem := by
    rw [hfm]; exact hP1.fr (MFr.of_frame (flushMem_frame s1.mem) (by simp) (by
      intro x hx; left; have := flushCtl_lt x hx; omega))
  have hA2 : AbsOK s2.mem := by rw [hfm]; exact AFr.of_frame (flushMem_frame s1.mem) (by decide) (by decide) hA1
  obtain ⟨c2', -, hst2⟩ := ConRon.Bridge.Inductives.ReadOK.flush (μ := V)
    (⟨k1.ok.state, k1.ok.pins, hOKS1 a1 rfl⟩ : ConRon.Bridge.Inductives.ReadOK env₁ fe1 a1)
    (show ConRon.Arena.flushCaches a1 = .ok ((), { a1 with caches := Caches.empty }) from rfl)
  have hC2 := StageC.of_parts hS2 c2' hA2 (dnE x01)
  generalize ha2 : ({ a1 with caches := Caches.empty } : AState) = a2 at hS2 hC2 c2' hst2
  refine ErrClaim.bind_right (a₁ := a2) (by rw [← ha2]; exact flushCaches_run a1) ?_
  try dsimp only
  simp only [BlockParts.complete]
  have hg12 := hg2
  -- the constructors
  have hbs2 := hbs1.grow (decBS_mono _) hg12
  have hsrc2 := partsHsrc_grow hg12 hq9 hsrc1
  obtain ⟨hmemb, -, -, -, -, -, -⟩ := decBS_some (show decBS (truncM s2.mem) _ = _ from hbs2)
  have hq1 : (r1.tail.tail.tail.headD 0 + 1).toNat = (r1.tail.tail.tail.headD 0).toNat + 1 := by
    have h9 := hq9
    generalize r1.tail.tail.tail.headD 0 = w at h9 ⊢
    rw [UInt64.toNat_add]; simp; omega
  have hmss := bpPSl decMS_mono hmemb hsrc2 (w := r1.tail.tail.tail.headD 0)
    (w1 := r1.tail.tail.tail.headD 0 + 1) rfl hq1
  have hcv2 := hcv1.grow (fun q => OMono.decCVp q) hg12
  obtain ⟨hms1, -⟩ := ConRon.Bridge.Inductives.dShape_inv hsh1
  have x12 : ConRon.Arena.Ext a1.store a2.store := by rw [hst2]; exact ConRon.Arena.Ext.refl _
  have hsh2 := ConRon.Bridge.Inductives.dShape_ext x12 _ _ hsh1
  have hms2 := ConRon.Bridge.Inductives.dMember_ext.list x12 _ _ hms1
  have hcvs2 := ConRon.Bridge.Inductives.dExt_denoteCV.list x12 _ _ hcvs
  have hden₂ := ConRon.Bridge.denoteFEnv_mono x12 hden₁
  cases c3 : callE p F "check_block_ctors" [r1.headD 0, r1.headD 0, r1.tail.tail.tail.headD 0,
      rdW (s2.mem.arr64 IW) (r1.tail.tail.tail.headD 0),
      rdW (s2.mem.arr64 IW) (r1.tail.tail.tail.headD 0 + 1), r1.tail.headD 0, r1.tail.tail.headD 0]
      s2.mem with
  | error e3 =>
    rw [c3, icpE.k_check_block_ctors.none] at he
    cases he
    exact ErrClaim.bind_left (eCtors hkp henv₁ hV hOpf hLC hLT hApd hCrk hP.ctors ⟨s2.mem, Locals.init []⟩ a2 _ _ _ _ _ bs1 bs1.members cvTas
      hC2 hbs2 hsrc2 hmss hcv2 hA2 hsh2 hms2 hcvs2 hT c2'.ienv.toS hden₂
      F (by omega) _ c3)
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [c3, icpE.k_check_block_ctors.eq_2] at he
  have d3 := callW_mono (callW_of_callE c3) hle
  obtain ⟨s3, hs3, -, hok3, hC3, hg3, hca3, hss3, hcb3, hA3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (checkBlockCtors_refinesC hkp henv₁ hV hOpf hLC hLT hApd hCrk hP.ctors (n + 2) (by omega) _ a2 _ _ _ _ _ bs1 bs1.members cvTas
      hC2 hbs2 hsrc2 hmss hcv2 hA2 hsh2 hms2 hcvs2 hT c2'.ienv.toS hden₂) d3
  simp only at hs3 hC3 hg3 hca3 hss3 hcb3 hA3
  subst hs3
  have hrun3 := AM.run_of_ok _ a2 hok3
  generalize AM.res (ConRon.Arena.checkBlockCtors V fe1 fe1 bs1 bs1.members cvTas) a2 = x3
    at hrun3 hca3 hss3 hcb3
  generalize AM.st (ConRon.Arena.checkBlockCtors V fe1 fe1 bs1 bs1.members cvTas) a2 = a3 at hrun3 hC3
  obtain ⟨ctorsAs, sss⟩ := x3
  refine ErrClaim.bind_right hrun3 ?_
  try dsimp only
  obtain ⟨k3, ⟨ctorsAsP, sortsssP⟩, ⟨hca, hss⟩, hF3⟩ :=
    ConRon.Bridge.Inductives.checkBlockCtors_specF fe1 fe1 rfl hcs henv₁ bs1 p₁P env₁ bs1.members
      p₁P.members cvTas cvTasP hT a2 a3 _ c2'
      ⟨hsh2, hms2, hcvs2, hden₂, hden₂, c2'.ienv.toS⟩ hrun3
  dsimp only at hca hss hF3
  have x23 : ConRon.Arena.Ext a2.store a3.store := k3.ext
  have hS3 := hC3.stage
  have hP3 := PosMR.ofClosed hcl (hfs _ (by decide)) d3 hP2
  have hg13 := hg12.trans hg3
  -- the positivity context
  have hbs3 := hbs1.grow (decBS_mono _) hg13
  have hsrc3 := partsHsrc_grow hg13 hq9 hsrc1
  have hcv3 := hcv1.grow (fun q => OMono.decCVp q) hg13
  cases c4 : callE p F "block_nest_ctx" [r1.headD 0, r1.tail.tail.tail.headD 0, r1.tail.headD 0,
      r1.tail.tail.headD 0] s3.mem with
  | error e4 =>
    rw [c4, icpE.k_block_nest_ctx.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) c4
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [c4, icpE.k_block_nest_ctx.eq_2] at he
  have d4 := callW_mono (callW_of_callE c4) hle
  obtain ⟨s4, rfl, -, hW4⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (bnc_specC p hP.nck hP.nhl hP.bnc (realCall p) (realCall_spec p) (n + 1) _ _ _ _ _) d4
  obtain ⟨⟨c, holes⟩, a4, hrun4, hctx4, hho4, hhob4, hS4, hg4, hin4, hsl4, hhi4, hpn4, hA4⟩ :=
    bncC_simA (realCall p) (n + 1) hS3 hbs3 hsrc3 hcv3
      (fun _ he => Sim.mono (opfSimRA (n := n + 2) hOpf he hS3 hA3) fun _ _ _ _ h => ⟨h.1.1, h.2⟩)
      r4 s4.mem hW4
  refine ErrClaim.bind_right hrun4 ?_
  try dsimp only
  have x13 : ConRon.Arena.Ext a1.store a3.store := x12.trans x23
  obtain ⟨k4, ⟨ctxP, holesP⟩, ⟨hctx, hholes, hctxOk, hhw, hpar, hlen, hnh, hnP⟩, hF4⟩ :=
    ConRon.Bridge.Inductives.blockNestCtx_spec (μ := V) fe1 henv₁ bs1 p₁P cvTas cvTasP hT a3 a4 _ k3.ok
      ⟨ConRon.Bridge.Inductives.dShape_ext x13 _ _ hsh1,
        ConRon.Bridge.Inductives.dExt_denoteCV.list x13 _ _ hcvs⟩ hrun4
  dsimp only at hctx hholes hctxOk hhw hpar hlen hnh hnP hF4
  have hparN := ConRon.Bridge.Inductives.BT.blockNestCtx_params_scoped hT hF4
  dsimp only at hparN
  have x34 : ConRon.Arena.Ext a3.store a4.store := k4.ext
  have x14 : ConRon.Arena.Ext a1.store a4.store := x13.trans x34
  obtain ⟨namesP, lpsP, paramsP, sortP, hctxEq, -, -, hparams, -, -⟩ :=
    ConRon.Bridge.Inductives.dCtx_inv hctx
  have hP4 := PosMR.ofClosed hcl (hfs _ (by decide)) d4 hP3
  have hC4 := StageC.of_parts hS4 k4.ok hA4 (dnE (x01.trans x14))
  have hg14 := hg13.trans hg4
  -- the classes
  have hT4 : iwTop s4.mem < 2 ^ 64 := (rdW (s4.mem.arr64 CTL) 200).toNat_lt
  have hbs4 := hbs1.grow (decBS_mono _) hg14
  have hsrc4 := partsHsrc_grow hg14 hq9 hsrc1
  obtain ⟨-, hq94, hmemv4⟩ := partsShapeFacts hbs4 hsrc4
  have hBS : BSOK s4.mem (r1.tail.tail.tail.headD 0).toNat bs1 :=
    ⟨hbs4, hsrc4, fun o l j v ho hl hj hv => by have := hmemv4 o l j v ho hl hj hv; omega⟩
  obtain ⟨-, hrcs, -, -, -, -, -⟩ := decBS_some (show decBS (truncM s4.mem) _ = _ from hbs4)
  obtain ⟨ro, rl, hro, hrl, hrd, hrb⟩ := partsAt decRS_mono hrcs
  have hp2 : (r1.tail.tail.tail.headD 0 + 2).toNat = (r1.tail.tail.tail.headD 0).toNat + 2 := by
    have h9 := hq94
    generalize r1.tail.tail.tail.headD 0 = w at h9 ⊢
    rw [UInt64.toNat_add]; simp; omega
  have hp3 : (r1.tail.tail.tail.headD 0 + 3).toNat = (r1.tail.tail.tail.headD 0).toNat + 2 + 1 := by
    have h9 := hq94
    generalize r1.tail.tail.tail.headD 0 = w at h9 ⊢
    rw [UInt64.toNat_add]; simp; omega
  obtain ⟨wro, -⟩ := bpWord hro hp2
  obtain ⟨wrl, -⟩ := bpWord hrl hp3
  have hRD : RecsDec s4.mem (rdW (s4.mem.arr64 IW) (r1.tail.tail.tail.headD 0 + 2))
      (rdW (s4.mem.arr64 IW) (r1.tail.tail.tail.headD 0 + 3)) bs1.recs := by
    rw [wro, wrl, UInt64.ofNat_toNat, UInt64.ofNat_toNat]
    refine ⟨hrd, ?_⟩
    rcases hrb with h0 | hb
    · subst h0; simpa using ro.toNat_lt
    · omega
  have hcdec : decCtx (truncM s4.mem) (r4.headD 0).toNat = some c := hctx4
  obtain ⟨-, -, -, -, hpar', -, -⟩ := decCtx_some hcdec
  obtain ⟨po, pl, hpo, hpl, hpd⟩ := decAt_some hpar'
  have hc10 : (r4.headD 0).toNat + 10 < iwTop s4.mem := hin4.1 10 (by omega)
  have hc7 : (r4.headD 0 + 7).toNat = (r4.headD 0).toNat + 7 := by
    have h10 := hc10
    generalize r4.headD 0 = w at h10 ⊢
    rw [UInt64.toNat_add]; simp; omega
  have hc8 : (r4.headD 0 + 8).toNat = (r4.headD 0).toNat + 7 + 1 := by
    have h10 := hc10
    generalize r4.headD 0 = w at h10 ⊢
    rw [UInt64.toNat_add]; simp; omega
  obtain ⟨wpo, hpob⟩ := bpWord hpo hc7
  obtain ⟨wpl, hplb⟩ := bpWord hpl hc8
  have hpoT : (UInt64.ofNat po : Word).toNat = po := UInt64.toNat_ofNat_of_lt' hpob
  have hplT : (UInt64.ofNat pl : Word).toNat = pl := UInt64.toNat_ofNat_of_lt' hplb
  have hpfD : DecB (fun m => (decHL m (rdW (s4.mem.arr64 IW) (r4.headD 0 + 7)).toNat
      (rdW (s4.mem.arr64 IW) (r4.headD 0 + 8)).toNat : Option (List EIdx))) s4.mem c.params := by
    rw [wpo, wpl, hpoT, hplT]; exact hpd
  have hpfb : (rdW (s4.mem.arr64 IW) (r4.headD 0 + 7)).toNat +
      (rdW (s4.mem.arr64 IW) (r4.headD 0 + 8)).toNat ≤ iwTop s4.mem := by
    rw [wpo, wpl, hpoT, hplT]
    rw [iwN_truncM (by omega)] at hpo
    rw [iwN_truncM (by omega)] at hpl
    exact hsl4 7 (by omega) po pl hpo hpl
  have hca4 := hca3.grow decCNS_mono hg4
  have hpl4 : ctxP.params.length = p₁P.nP := by rw [hlen, hnP]
  have hpfP : Frontend.denoteEList a4.store c.params = some ctxP.params := by rw [hctxEq]; exact hparams
  have hca4P := ConRon.Bridge.Inductives.dCtors_ext.list x34 _ _ hca
  have hsh4 := ConRon.Bridge.Inductives.dShape_ext x14 _ _ hsh1
  cases c5 : callE p F "check_block_classes" [r1.headD 0, r1.tail.tail.tail.headD 0,
      rdW (s4.mem.arr64 IW) (r4.headD 0 + 7), rdW (s4.mem.arr64 IW) (r4.headD 0 + 8), r3.headD 0,
      r3.tail.headD 0] s4.mem with
  | error e5 =>
    rw [c5, icpE.k_check_block_classes.none] at he
    cases he
    exact ErrClaim.bind_left (eCls hkp hIlpf hLC henv₁ hP.cbc hcl (hfs _ (by decide)) (hfs _ (by decide))
      ⟨s4.mem, Locals.init []⟩ a4 _ _ _ _ _ bs1 ctorsAs c.params hC4 hBS hsrc4 hRD hca4 hpfD hpfb hP4 hA4
      hOpf (hk' _ (by simp [passKeepCalleesC, indsKeepCalleesC, posKeepCalleesC]))
      (hk' _ (by simp [passKeepCalleesC, indsKeepCalleesC, posKeepCalleesC])) hpl4 hparN hsh4 hpfP hca4P
      F (by omega) _ c5)
  | ok q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [c5, icpE.k_check_block_classes.eq_2] at he
  have d5 := callW_mono (callW_of_callE c5) hle
  obtain ⟨s5, hs5, -, hok5, hC5, hg5, hrd5, hms5, hP5, hA5, -⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (checkBlockClasses_refinesC hkp hIlpf hLC henv₁ hP.cbc hcl (hfs _ (by decide)) (hfs _ (by decide))
      (n + 2) (by omega) _ a4 _ _ _ _ _ bs1 ctorsAs c.params hC4 hBS hsrc4 hRD hca4 hpfD hpfb hP4 hA4
      hOpf (hk' _ (by simp [passKeepCalleesC, indsKeepCalleesC, posKeepCalleesC]))
      (hk' _ (by simp [passKeepCalleesC, indsKeepCalleesC, posKeepCalleesC])) hpl4 hparN hsh4 hpfP hca4P) d5
  simp only at hs5 hC5 hg5 hrd5 hms5 hP5 hA5
  subst hs5
  have hrun5 := AM.run_of_ok _ a4 hok5
  generalize AM.res (ConRon.Arena.checkBlockClasses V fe1 bs1 c.params ctorsAs) a4 = x5 at hrun5 hrd5 hms5
  generalize AM.st (ConRon.Arena.checkBlockClasses V fe1 bs1 c.params ctorsAs) a4 = a5 at hrun5 hC5
  obtain ⟨rd, ms⟩ := x5
  refine ErrClaim.bind_right hrun5 ?_
  try dsimp only
  obtain ⟨k5, ⟨rdP, msP⟩, ⟨hrdP, hmsP, hMsc⟩, hF5⟩ :=
    ConRon.Bridge.Inductives.classesStage hcs fe1 env₁ bs1 p₁P c.params ctxP.params ctorsAs ctorsAsP
      henv₁ hpl4 hparN a4 a5 _ k4.ok ⟨hsh4, hpfP, hca4P, ConRon.Bridge.denoteFEnv_mono x14 hden₁⟩ hrun5
  dsimp only at hrdP hmsP hMsc hF5
  have x45 : ConRon.Arena.Ext a4.store a5.store := k5.ext
  have x15 : ConRon.Arena.Ext a1.store a5.store := x14.trans x45
  have hg15 := hg14.trans hg5
  -- the positivity check
  have hbs5 := hbs1.grow (decBS_mono _) hg15
  have hsrc5 := partsHsrc_grow hg15 hq9 hsrc1
  have hcv5 := hcv1.grow (fun q => OMono.decCVp q) hg15
  have hcb5 := hcb3.grow decCNSB_mono (hg4.trans hg5)
  have hpP5 : ConRon.Bridge.Inductives.dParts a5.store ⟨bs1⟩ = some ⟨p₁P⟩ := by
    simp only [ConRon.Bridge.Inductives.dParts, ConRon.Bridge.Inductives.dShape_ext x15 _ _ hsh1,
      Option.map_some]
  have hcvs5 := ConRon.Bridge.Inductives.dExt_denoteCV.list x15 _ _ hcvs
  have hca5 := ConRon.Bridge.Inductives.dCtors_ext.list (x34.trans x45) _ _ hca
  have hden₅ := ConRon.Bridge.denoteFEnv_mono x15 hden₁
  have hct := ConRon.Bridge.Inductives.checkBlockCtors_types hF3
  cases c6 : callE p F "check_block_positivity" [r1.headD 0, r1.tail.tail.tail.headD 0,
      r1.tail.headD 0, r1.tail.tail.headD 0, r3.headD 0, r3.tail.headD 0] s5.mem with
  | error e6 =>
    rw [c6, icpE.k_check_block_positivity.none] at he
    cases he
    exact ErrClaim.bind_left (ePos hkp hIlpf henv₁ hOpf hLC hLT hApd hP.pos hcl (hfs _ (by decide)) ⟨s5.mem, Locals.init []⟩ a5 _ _ _ _ _ ⟨bs1⟩
      cvTas ctorsAs hC5 hbs5 hsrc5 hcv5 hcb5 hP5 hA5 (fun f hf => hkP f (List.mem_append_right _ hf))
      hpP5 hcvs5 hca5 hden₅ hT hct
      F (by omega) _ c6)
  | ok q6 =>
  obtain ⟨r6, m6⟩ := q6
  rw [c6, icpE.k_check_block_positivity.eq_2] at he
  have d6 := callW_mono (callW_of_callE c6) hle
  obtain ⟨s6, hs6, -, hok6, hC6, hg6, hP6, hA6, hks6, hnf6, hns6, -⟩ := triple_of_callW
    (s₀ := ⟨s5.mem, Locals.init []⟩)
    (checkBlockPositivity_refinesC hkp hIlpf henv₁ hOpf hLC hLT hApd hP.pos hcl (hfs _ (by decide)) n (by omega) _ a5 _ _ _ _ _ ⟨bs1⟩
      cvTas ctorsAs hC5 hbs5 hsrc5 hcv5 hcb5 hP5 hA5 (fun f hf => hkP f (List.mem_append_right _ hf))
      hpP5 hcvs5 hca5 hden₅ hT hct) d6
  simp only at hs6 hC6 hg6 hP6 hA6 hks6 hnf6 hns6
  subst hs6
  have hrun6 := AM.run_of_ok _ a5 hok6
  generalize AM.res (ConRon.Arena.checkBlockPositivity V fe1 ⟨bs1⟩ cvTas ctorsAs) a5 = x6 at hrun6 hks6 hnf6 hns6
  generalize AM.st (ConRon.Arena.checkBlockPositivity V fe1 ⟨bs1⟩ cvTas ctorsAs) a5 = a6 at hrun6 hC6
  obtain ⟨kinds, nfs, NS⟩ := x6
  refine ErrClaim.bind_right hrun6 ?_
  try dsimp only
  obtain ⟨k6, ⟨kindsP, nfsP, posP⟩, ⟨hkinds, hnfs, hpos⟩, hF6⟩ :=
    ConRon.Bridge.Inductives.checkBlockPositivity_spec fe1 hcs henv₁ ⟨bs1⟩ ⟨p₁P⟩ cvTas cvTasP ctorsAs
      ctorsAsP hT hct a5 a6 _ k5.ok ⟨hpP5, hcvs5, hca5, hden₅⟩ hrun6
  dsimp only at hkinds hnfs hpos hF6
  have x56 : ConRon.Arena.Ext a5.store a6.store := k6.ext
  have hS6 := hC6.stage
  have hg16 := hg15.trans hg6
  have hT6 : iwTop s6.mem < 2 ^ 64 := (rdW (s6.mem.arr64 CTL) 200).toNat_lt
  -- the classes' seeds
  have hU4 : UCtx dn (r1.headD 0) fe1 s4.mem (r4.headD 0) c :=
    ⟨hctx4.get (decCtx_mono _), hin4, hsl4⟩
  have hg46 := hg5.trans hg6
  have hU6 := hU4.grow hg46
  have hho6 : (decHL s6.mem (r4.tail.headD 0).toNat (r4.tail.tail.headD 0).toNat : Option (List EIdx)) =
      some holes := by rw [decHL_grow3 hg46 hhob4]; exact hho4
  have hms6 := hms5.grow (fun q => decTM_mono q) hg6
  cases c7 : callE p F "class_seeds" [r4.headD 0, r4.tail.headD 0, r4.tail.tail.headD 0,
      r5.tail.headD 0, r5.tail.tail.headD 0] s6.mem with
  | error e7 =>
    rw [c7, icpE.k_class_seeds.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) c7
  | ok q7 =>
  obtain ⟨r7, m7⟩ := q7
  rw [c7, icpE.k_class_seeds.eq_2] at he
  have d7 := callW_mono (callW_of_callE c7) hle
  obtain ⟨s7, hs7, -, hok7, hS7, hg7, hsd7, hP7⟩ := triple_of_callW (s₀ := ⟨s6.mem, Locals.init []⟩)
    (classSeeds_refines hP.sds (n + 3) _ a6 dn (r1.headD 0) fe1 _ _ _ _ _ c holes ms hS6 hU6 hhi4 hho6
      (Nat.le_trans hhob4 hg46.1) hms6 hP6) d7
  simp only at hs7 hS7 hg7 hsd7 hP7
  subst hs7
  have hA7 : AbsOK s7.mem := hkP _ (by simp [passKeepCalleesC, indsKeepCalleesC, posKeepCalleesC]) _ _ _ _ _ d7 hA6
  have hrun7 := AM.run_of_ok _ a6 hok7
  generalize AM.res (ConRon.Arena.classSeeds c holes ms) a6 = seeds at hrun7 hsd7
  generalize AM.st (ConRon.Arena.classSeeds c holes ms) a6 = a7 at hrun7 hS7
  refine ErrClaim.bind_right hrun7 ?_
  try dsimp only
  have x46 : ConRon.Arena.Ext a4.store a6.store := x45.trans x56
  obtain ⟨p7, hseeds⟩ := ConRon.Bridge.Inductives.seedsStage c ctxP holes holesP ms msP env₁.find? a6 a7
    seeds k6.ok.state k6.ok.pins
    ⟨ConRon.Bridge.Inductives.dCtx_ext _ x46 _ _ hctx, ConRon.Bridge.denoteEList_ext x46 _ _ hholes,
      ConRon.Bridge.Inductives.dMajor_ext.list x56 _ _ hmsP⟩ hrun7
  have k7 := p7.toCore k6.ok
  have x67 : ConRon.Arena.Ext a6.store a7.store := k7.ext
  have hC7 := StageC.of_parts hS7 k7.ok hA7 (dnE (x01.trans (x14.trans (x46.trans x67))))
  -- the nested seeds
  have hg67 := hg7
  have hU7 := hU6.grow hg67
  have hns7 := hns6.grow hg67 hT6
  have hdrop : (r6.drop 4).headD 0 = r6.tail.tail.tail.tail.headD 0 := by
    rcases r6 with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;> rfl
  rw [hdrop] at hns7
  cases c8 : callE p F "nest_seeds" [r1.headD 0, r4.headD 0, r7.headD 0, r7.tail.headD 0,
      r6.tail.tail.tail.tail.headD 0] s7.mem with
  | error e8 =>
    rw [c8, icpE.k_nest_seeds.none] at he
    cases he
    exact ErrClaim.bind_left (eSeeds hP.rs hkp hIlpf hLC dn (r1.headD 0) fe1 henv₁ ⟨s7.mem, Locals.init []⟩ a7 _ _ _ _ c seeds NS
      hC7 hU7 hhi4 hsd7.2.1 hsd7.2.2.2 hns7 hP7 hA7 hctxOk
      (ConRon.Bridge.Inductives.dCtx_ext _ (x46.trans x67) _ _ hctx) hseeds
      (ConRon.Bridge.Inductives.dState_ext x67 _ _ hpos)
      (fun k hk x hx => by
        obtain ⟨M, hM, hMn, rfl⟩ := ConLeche.Cached.mem_classSeeds hk
        exact (ConLeche.nestSeedOf_ds hnh hlen (fun y hy => ConLeche.Expr.fvarB_le (by
          rw [hnP]; exact (((hMsc M hM).2.1 hMn).2 y hy).2)) x hx).2 (fun y hy => (hhw y hy).1) hpar)
      F (by omega) _ c8)
  | ok q8 =>
  obtain ⟨r8, m8⟩ := q8
  rw [c8, icpE.k_nest_seeds.eq_2] at he
  have d8 := callW_mono (callW_of_callE c8) hle
  obtain ⟨s8, hs8, -, ns, a8, hrun8, hC8, hg8, hns8, hP8, hA8, k8⟩ :=
    triple_of_callW (s₀ := ⟨s7.mem, Locals.init []⟩)
    (nestSeeds_refinesC hP.rs hkp hIlpf hLC (n + 3) dn (r1.headD 0) fe1 henv₁ (by omega) _ a7 _ _ _ _ c seeds NS
      hC7 hU7 hhi4 hsd7.2.1 hsd7.2.2.2 hns7 hP7 hA7 hctxOk
      (ConRon.Bridge.Inductives.dCtx_ext _ (x46.trans x67) _ _ hctx) hseeds
      (ConRon.Bridge.Inductives.dState_ext x67 _ _ hpos)
      (fun k hk x hx => by
        obtain ⟨M, hM, hMn, rfl⟩ := ConLeche.Cached.mem_classSeeds hk
        exact (ConLeche.nestSeedOf_ds hnh hlen (fun y hy => ConLeche.Expr.fvarB_le (by
          rw [hnP]; exact (((hMsc M hM).2.1 hMn).2 y hy).2)) x hx).2 (fun y hy => (hhw y hy).1) hpar)) d8
  simp only at hs8 hC8 hg8 hns8 hP8 hA8
  subst hs8
  have hS8 := hC8.stage
  have hT8 : iwTop s8.mem < 2 ^ 64 := (rdW (s8.mem.arr64 CTL) 200).toNat_lt
  obtain ⟨-, -, -, hnfsB⟩ := nsb_words hns8 hT8
  have htbl8 : PSlR decNCN ns.ctorNfs.toList (rdW (s8.mem.arr64 IW) (r8.headD 0 + 4))
      (rdW (s8.mem.arr64 IW) (r8.headD 0 + 5)) s8.mem := ⟨hnfsB, hns8.b4⟩
  have hg48 := (hg5.trans hg6).trans (hg7.trans hg8)
  have hw7 : rdW (s8.mem.arr64 IW) (r4.headD 0 + 7) = rdW (s4.mem.arr64 IW) (r4.headD 0 + 7) :=
    partsRdIW_grow hg48 (by rw [hc7]; omega)
  have hw8 : rdW (s8.mem.arr64 IW) (r4.headD 0 + 8) = rdW (s4.mem.arr64 IW) (r4.headD 0 + 8) :=
    partsRdIW_grow hg48 (by rw [hc8]; omega)
  refine ErrClaim.bind_right hrun8 ?_
  -- the record
  cases c9 : callE p F "check_block_pass_rec" [r1.headD 0, r1.tail.headD 0, r1.tail.tail.headD 0,
      r1.tail.tail.tail.headD 0, r3.headD 0, r3.tail.headD 0, r3.tail.tail.headD 0,
      r3.tail.tail.tail.headD 0, r6.headD 0, r6.tail.headD 0, r6.tail.tail.headD 0,
      r6.tail.tail.tail.headD 0, rdW (s8.mem.arr64 IW) (r4.headD 0 + 7),
      rdW (s8.mem.arr64 IW) (r4.headD 0 + 8), r5.headD 0, r5.tail.headD 0, r5.tail.tail.headD 0,
      rdW (s8.mem.arr64 IW) (r8.headD 0 + 4), rdW (s8.mem.arr64 IW) (r8.headD 0 + 5)] s8.mem with
  | error e9 =>
    rw [c9, icpE.k_check_block_pass_rec.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) c9
  | ok q9 =>
    rw [c9] at he
    cases he

end

end L.Ind
