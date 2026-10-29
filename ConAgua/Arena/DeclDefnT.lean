import ConAgua.Arena.DeclNatGateT
import ConAgua.Arena.DeclArmLoop
import ConAgua.Arena.DeclDivGateT

/-!
# The definition arm under `StageT` (lane `loopt3`, helper `loopt3-nat`)

`check_decl_defn`'s unified model and its refinement for both outcomes (`cdf_ref`), from `StageT`:
the constant check and the definition check (`ccv_ref`, `dv_ref`), then the two gates under
`StageC` at the pre-insertion view (con-ron's `CheckOK` restricted, the memory's half of `TwinOK`):
the structural-`Nat` gate (`dng_ref`, `DeclNatGateT.lean`) and the `Nat.div`-family pin gate
(`DivGateSpecC`/`DivGateSpecE`, `DeclDivGateT.lean`). The twin side is con-ron's
`checkDecl_bridge_defn`: `FoldOK` at the arm's entry carried across the constant check
(`checkConstantVal_bridge_of_fold`) and the definition check (`checkDefnVal_bridge`, which gives
the pushed index's `StepOK` at `env2`, what the gates read the stored value and guards through).
The variant records (`PinSetsR`, carried by the step's write set) and their twin denotations
(`PinsDenote`, carried by `Ext`) reach the pin gate.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


noncomputable section

namespace L.Arena

open L.Ind
open L.Rom (PinSetsR)
open L.Front (DECL DLP DeclsF)
open ConRon.Bridge (CheckOK StepOK FoldOK CoreSpec PinsDenote)

local notation "V" => ConLeche.CheckMode.verified

/-- `check_defn_val` is one of the loop's functions. -/
theorem checkDefnVal_loop : "check_defn_val" ∈ loopFns := loop_mem _ rfl

/-- The definition arm's program facts under `StageT`: its text, the structural gate's text (a
`NatSubProg'` with the two gate functions, its functions with a step's write set), and the pin
gate's `StageC` spec. -/
structure DefnProgT (p : Prog) (pins : List INatOpPinSet) : Prop where
  df : p.lookup "check_decl_defn" = some checkDeclDefn
  nat : NatSubProg' p
  natGate : p.lookup "defn_nat_gate" = some defnNatGate
  natCert : p.lookup "defn_nat_cert" = some defnNatCert
  natIn : StepIn p natGateFns
  div : DivGateSpecC p pins

set_option experimental.vcgen true in
/-- **The model of `check_decl_defn`, both outcomes**: its callees through their runs. -/
l_model checkDeclDefn_specE (p : Prog) (hf : p.lookup "check_decl_defn" = some checkDeclDefn)
  fns [hf ↦ checkDeclDefnE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 unified

/-- What the definition arm's error arms assume: `check_constant_val`'s (`VerdictCtxU`),
`install_value_guards`' claim (`check_defn_val`), the pin gate's claim. -/
structure CdfCtx (p : Prog) (pins : List INatOpPinSet) : Prop extends VerdictCtxU p where
  ivg : IvgE p
  div : DivGateSpecE p pins

/-- What the definition arm gives besides the twin's run: the stage at the twin's environment,
the core's memos, the growth, the variant records. -/
structure CdfPost (dn : NIdx → Option ConLeche.Name) (pins : List INatOpPinSet) (m : Mem)
    (w : Word × Mem) (y : IFEnv) (a' : AState) : Prop where
  stage : StageR dn w.1 y w.2 a'
  memos : CoreMemos w.2
  grow : IWGrow m w.2
  pins : PinSetsR w.2 pins

/-- **The definition arm refines `checkDecl`, both outcomes**, under `StageT` (con-ron's
`checkDecl_bridge_defn`'s decomposition): from `StageT`, the fold invariant `FoldOK`, the
declaration's constant and value denoting, the variant records in memory (`PinSetsR`) and in the
twin's store (`PinsDenote`): the constant check (`ccv_ref`), the definition check (`dv_ref`), the
structural gate (`dng_ref`), the pin gate (`DivGateSpecC`, `DivGateSpecE`). -/
theorem cdf_ref {p : Prog} (hA : ArmProg p) (hV : ValProg p) {pins : List INatOpPinSet}
    (hDP : DefnProgT p pins) (hq : KnotStageProg p) (hcl : LeafClosed p) (hlc : LoopClosed p)
    (hap : ApdF p) (hkp : CrKeep p) {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn)
    {vis : Word} {fe : IFEnv} {env : ConLeche.Env} {a : AState} (n : Nat) (hn : n ≤ 2 ^ 62)
    {m : Mem} {i : Word} {ds : Array IDeclaration} {cv : IConstantVal} {v : EIdx}
    {hh : ConLeche.ReducibilityHint} {c : ConLeche.ConstantVal} {x : ConLeche.Expr}
    (hS : StageT dn vis fe m a) (hPS : PinSetsR m pins)
    (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds) (hi : i.toNat < ds.size)
    (hd : ds[i.toNat] = .defnDecl cv v hh) (hfold : FoldOK V env fe a)
    (hcvd : Frontend.denoteCV a.store cv = some c) (hvd : denoteE a.store v = some x)
    (hPD : ∃ pinsP, PinsDenote a.store pins pinsP) (hCr : L.Stubs.CrOK m) :
    RefE (CdfCtx p pins) (checkDeclDefnE p n m i vis) (checkDecl V pins fe (.defnDecl cv v hh)) a
      (fun w y a' => CdfPost dn pins m w y a') := by
  have hfr : ∀ {k : Nat} {f : FnName} {args : List Word} {mx my : Mem} {rx : List Word},
      f ∈ armFns → callW p k f args mx = some (rx, my) → MemFrame stepA stepC mx my := by
    intro k f args mx my rx hf hc
    obtain ⟨s', hs', hfr', -⟩ := triple_of_callW (s₀ := ⟨mx, Locals.init []⟩)
      (hA.closed.memFrame k hf args ⟨mx, Locals.init []⟩) hc
    rw [← hs']; exact hfr'
  cases n with
  | zero => rw [checkDeclDefnE.eq_1]; exact RefE.of_cls0 rfl
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [checkDeclDefnE.arm1, checkDecl_defn_eq]
  -- `erec_ci`
  rcases h1 : callE p n "erec_ci" [i, 1] m with e1 | ⟨r1, m1⟩
  · rw [checkDeclDefnE.k_erec_ci.none]; exact fun hG => nvl hG.nv (by decide +kernel) h1
  rw [checkDeclDefnE.k_erec_ci.arm1]
  have h1w := callW_of_callE h1
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (erecCi_specW p hV.rcp n ⟨m, Locals.init []⟩ i 1) h1w
  rw [hs1] at hW1
  obtain ⟨hS1, hg1, hci1, hcv1, hval1, htop1⟩ :=
    erecCiW_okT (ci := .defnInfo cv v hh) hW1 hS hD hi (by rw [hd]; rfl)
  have hCr1 := hkp.call (im_mem _ rfl) h1w hCr
  have hPS1 := PinSetsR.step hPS hg1 (hfr (by decide) h1w)
  rw [hd] at hcv1 hval1
  simp only [stepCV, stepVal] at hcv1 hval1
  generalize hq0 : r1.headD 0 = q at hci1 hcv1 hval1 htop1 ⊢
  have hqb : q.toNat + 8 < 2 ^ 64 := by
    have := hS1.stage.iw.2.1; have := hS1.stage.iw.2.2.2.1; omega
  have hq1 : (q + 1).toNat = q.toNat + 1 := toNat_add_small q 1 (by omega)
  obtain ⟨wn, hwn, hwnl, hname0⟩ := decCI_name hci1
  have hname : cv.name = decI wn := hname0
  rw [rdW_of_get? hq1.symm (erecP_get hwn)]
  -- `check_constant_val`
  have h2R := ccv_ref hq hap hkp hn' hS1 (by rw [hq1]; exact hcv1) (by omega) (denoteCV_lps hcvd)
    hCr1
  rcases h2 : callE p n "check_constant_val" [vis, q + 1] m1 with e2 | ⟨r2, m2⟩
  · rw [checkDeclDefnE.k_check_constant_val.none]
    exact RefE.bind_left fun hG => RefE.run_err (s₀ := ⟨m1, Locals.init []⟩)
      (checkConstantVal_specE p hV n _ vis (q + 1)) hG.nv hG.toVerdictCtxU h2R h2
  rw [checkDeclDefnE.k_check_constant_val.arm1]
  have h2w := callW_of_callE h2
  obtain ⟨s2, hs2, -, _, a2, hrun2, hP2⟩ := RefE.run_ok (s₀ := ⟨m1, Locals.init []⟩)
    (checkConstantVal_specE p hV n _ vis (q + 1)) h2R h2
  subst hs2
  have hPS2 := PinSetsR.step hPS1 hP2.grow (hfr (by decide) h2w)
  obtain ⟨hstep1, F1, hpure1⟩ :=
    ConRon.Bridge.checkConstantVal_bridge_of_fold rfl (CoreSpec.of_core rfl) hfold hcvd hrun2
  have hok1 := hfold.ofCore hstep1
  have hcA := ConRon.Bridge.denoteCV_ext hcvd hstep1.ext
  have hv1 := ConRon.Bridge.denote_ext hvd hstep1.ext
  have hPD1 : ∃ pinsP, PinsDenote a2.store pins pinsP := by
    obtain ⟨pp, hp⟩ := hPD; exact ⟨pp, PinsDenote.mono hstep1.ext _ _ hp⟩
  refine RefE.bind_right hrun2 ?_
  -- `check_defn_val`
  have hx2 : ArrExt (erecP m1) (erecP s2.mem) := IWGrow.erecPExt hP2.grow
  have h3R := dv_ref hq hV hap hkp hn' "type mismatch in definition" hP2.stage
    (ArrExt.decCI hx2 hci1) (ArrExt.decCV hx2 hcv1) (ArrExt.hd? hx2 hval1) (denoteCV_lps hcA)
    hP2.crOK
  rcases h3 : callE p n "check_defn_val" [vis, q] s2.mem with e3 | ⟨r3, m3⟩
  · rw [checkDeclDefnE.k_check_defn_val.none]
    refine RefE.bind_left fun hG => ?_
    rw [checkDefnVal_dvT]
    exact RefE.run_err (s₀ := ⟨s2.mem, Locals.init []⟩) (checkDefnVal_specE p hV n _ vis q) trivial
      ⟨fun _ _ _ _ h => callE_nv hG.nv (declNv_mem _ (by decide +kernel)) _ _ _ h, hG.core, hG.ivg⟩
      h3R h3
  rw [checkDeclDefnE.k_check_defn_val.arm1]
  have h3w := callW_of_callE h3
  obtain ⟨s3, hs3, -, y3, a3, hrun3, hS3, hM3, hg3, rfl⟩ := RefE.run_ok (s₀ := ⟨s2.mem, Locals.init []⟩)
    (checkDefnVal_specE p hV n _ vis q) h3R h3
  subst hs3
  have hPS3 := PinSetsR.step hPS2 hg3 (hfr (by decide) h3w)
  rw [← checkDefnVal_dvT] at hrun3
  -- the twin's definition check: `CheckOK` at the old index, `StepOK` at the pushed one
  obtain ⟨hstep2, -, -, env2, F2, hstepOK2, hpure2⟩ := ConRon.Bridge.checkDefnVal_bridge rfl
    (CoreSpec.of_core rfl) hok1 hcA (ConRon.Bridge.checkConstantVal_typeWF hpure1) hv1 hrun3
  have hok3 := hok1.ofCore hstep2
  have hnm3 : denoteN a3.store.ns (decI wn) = some c.name := by
    rw [← hname]
    exact ConRon.Bridge.denoteN_ext (ConRon.Bridge.denoteCV_inv hcA).1 hstep2.ext
  have hPD3 : ∃ pinsP, PinsDenote a3.store pins pinsP := by
    obtain ⟨pp, hp⟩ := hPD1; exact ⟨pp, PinsDenote.mono hstep2.ext _ _ hp⟩
  have hvis : fe.visibleBelow = vis.toNat := hS.stage.check.env.vis
  have hpre := ConRon.Bridge.restrict_pushed_find (fe2 := fe.push (.defnInfo cv v hh)) rfl
    (hok3.check.ienv.find?_none
      (show denoteN a3.store.ns cv.name = some c.name by rw [hname]; exact hnm3)
      (ConRon.Bridge.checkConstantVal_fresh hpure1))
  have hck3 : CheckOK V env ((fe.push (.defnInfo cv v hh)).restrictTo vis.toNat) a3 := by
    rw [← hvis]; exact hok3.check.congr_find hpre rfl
  -- the memory's half after the push: the call's frame, the core memos
  have hf3 := (run_memFrame hlc checkDefnVal_loop (run_of_callW h3w)).1
  have hmem3 : TwinMem dn s3.mem a3 :=
    ⟨by rw [hf3.size]; exact hP2.stage.twin.erec, by rw [hf3.size]; exact hP2.stage.twin.spn,
      by rw [hf3.size]; exact hP2.stage.twin.bstk, hM3,
      fun k y e => hstep2.ext.lss.ls.ns k y (hP2.stage.twin.den.dnN k y e)⟩
  have hflag3 : pinW s3.mem 0 ≠ 0 := by
    simp only [pinW, hf3.1 PINS loopA_pins (by decide)]; exact hP2.stage.flag
  refine RefE.bind_right hrun3 ?_
  rw [hvis, hname]
  generalize hfe2 : fe.push (.defnInfo cv v hh) = fe2 at hS3 hrun3 hck3 hstepOK2 ⊢
  generalize hw : r3.headD 0 = w at hS3 ⊢
  have hC3 : StageC dn vis (fe2.restrictTo vis.toNat) env s3.mem a3 :=
    ⟨hS3.restrict vis, hck3, hmem3, hflag3⟩
  -- the structural gate
  have h4R := dng_ref hDP.nat hq hcl n hn' hwnl hS3 hC3 hok3.envWF hstepOK2 hnm3
  rcases h4 : callE p n "defn_nat_gate" [vis, w, wn] s3.mem with e4 | ⟨r4, m4⟩
  · rw [checkDeclDefnE.k_defn_nat_gate.none]
    exact RefE.bind_left fun hG => RefE.run_err (s₀ := ⟨s3.mem, Locals.init []⟩)
      (defnNatGate_specE p hDP.natGate hDP.natCert n _ vis w wn) hG.nv hG.core h4R h4
  rw [checkDeclDefnE.k_defn_nat_gate.arm1]
  have h4w := callW_of_callE h4
  obtain ⟨s4, hs4, -, _, a4, hrun4, hP4⟩ := RefE.run_ok (s₀ := ⟨s3.mem, Locals.init []⟩)
    (defnNatGate_specE p hDP.natGate hDP.natCert n _ vis w wn) h4R h4
  subst hs4
  have hPS4 := PinSetsR.step hPS3 hP4.grow (by
    obtain ⟨s', hs', hfr', -⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
      (hDP.natIn.memFrame n (f := "defn_nat_gate") (by decide) [vis, w, wn]
        ⟨s3.mem, Locals.init []⟩) h4w
    rw [← hs']; exact hfr')
  have hPD4 : ∃ pinsP, PinsDenote a4.store pins pinsP := by
    obtain ⟨pp, hp⟩ := hPD3; exact ⟨pp, PinsDenote.mono hP4.ext _ _ hp⟩
  have hCr4 := hkp.call (im_mem _ rfl) h4w (hkp.call (im_mem _ rfl) h3w hP2.crOK)
  refine RefE.bind_right hrun4 ?_
  -- the pin gate
  rcases h5 : callE p n "defn_div_gate" [vis, w, wn] s4.mem with e5 | ⟨r5, m5⟩
  · rw [checkDeclDefnE.k_defn_div_gate.none]
    exact RefE.bind_left fun hG => hG.div dn hdn vis w fe2 env env2 wn c.name n hn' s4.mem a4 hwnl
      hP4.stageW hP4.stage hok3.envWF (hstepOK2.mono hP4.ext) hPS4 hPD4
      (ConRon.Bridge.denoteN_ext hnm3 hP4.ext) hCr4 _ h5
  rw [checkDeclDefnE.k_defn_div_gate.arm1]
  obtain ⟨a5, hrun5, hS5, hC5, -, hg5, hPS5, -⟩ := hDP.div dn hdn vis w fe2 env env2 wn c.name n
    hn' s4.mem m5 a4 r5 hwnl (callW_of_callE h5) hP4.stageW hP4.stage hok3.envWF
    (hstepOK2.mono hP4.ext) hPS4 hPD4 (ConRon.Bridge.denoteN_ext hnm3 hP4.ext) hCr4
  exact RefE.bind_right hrun5 (RefE.ret rfl ⟨by simpa using hS5, hC5.mem.memos,
    hg1.trans (hP2.grow.trans (hg3.trans (hP4.grow.trans hg5))), hPS5⟩)

end L.Arena
