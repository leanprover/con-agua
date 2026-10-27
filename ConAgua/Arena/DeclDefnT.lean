import ConAgua.Arena.DeclNatGateT
import ConAgua.Arena.DeclDivGateT

/-!
# The definition arm under `StageT` (lane `loopt3`, helper `loopt3-nat`)

`check_decl_defn` (`DeclArmDefn.lean`, `cdfW_ok` at `StageR` through the gates' `StageR` specs)
from `StageT`, as the opaque arm (`cdoW_okT`, `DeclCrpT.lean`): the constant check and the
definition check under `StageT` (`checkConstantVal_refinesT`, `dvW_okT`), then the two gates under
`StageC` at the pre-insertion view (con-ron's `CheckOK` restricted, the memory's half of `TwinOK`):
the structural-`Nat` gate (`defnNatGate_okC`, `DeclNatGateT.lean`) and the `Nat.div`-family pin
gate (`DivGateSpecC`, helper `loopt3-div`'s `DeclDivGateT.lean`). The twin side is con-ron's
`checkDecl_bridge_defn`: `FoldOK` at the arm's entry carried across the constant check
(`checkConstantVal_bridge_of_fold`) and the definition check (`checkDefnVal_bridge`, which gives
the pushed index's `StepOK` at `env2`, what the gates read the stored value and guards through).
The variant records (`PinSetsR`, carried by the step's write set as in `cdfW_ok`) and their
twin denotations (`PinsDenote`, carried by `Ext`) reach the pin gate.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


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

/-- **The definition arm under `StageT`** (`cdfW_ok`'s, con-ron's `checkDecl_bridge_defn`'s
decomposition): from `StageT`, the fold invariant `FoldOK` (`TwinFold.fold`), the declaration's
constant and value denoting (`TwinFold.den`), the variant records in memory (`PinSetsR`) and in
the twin's store (`PinsDenote`, `TwinFold.pinsD`); the arm's run, the stage relation at the pushed
environment, the core's memos, and the variant records. -/
@[refines_part ConRon.Arena.checkDecl "the definition arm, under StageT"]
theorem cdfW_okT {p : Prog} (hA : ArmProg p) (hV : ValProg p) {pins : List INatOpPinSet}
    (hG : DefnProgT p pins) (hq : KnotStageProg p) (hcl : LeafClosed p) (hlc : LoopClosed p)
    (hap : ApdF p) (hkp : CrKeep p) {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn) {vis : Word} {fe : IFEnv}
    {env : ConLeche.Env} {a : AState} {n : Nat} (hn : n ≤ 2 ^ 62) {m m' : Mem} {i : Word}
    {r : List Word} {ds : Array IDeclaration} {cv : IConstantVal} {v : EIdx}
    {hh : ConLeche.ReducibilityHint} {c : ConLeche.ConstantVal} {x : ConLeche.Expr}
    (h : cdfW p n m i vis = some (r, m')) (hS : StageT dn vis fe m a) (hPS : PinSetsR m pins)
    (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds) (hi : i.toNat < ds.size)
    (hd : ds[i.toNat] = .defnDecl cv v hh) (hfold : FoldOK V env fe a)
    (hcvd : Frontend.denoteCV a.store cv = some c) (hvd : denoteE a.store v = some x)
    (hPD : ∃ pinsP, PinsDenote a.store pins pinsP) (hCr : L.Stubs.CrOK m) :
    ∃ fe' a', (checkDecl V pins fe (.defnDecl cv v hh)).run a = .ok (fe', a') ∧
      StageR dn (r.headD 0) fe' m' a' ∧ CoreMemos m' ∧ IWGrow m m' ∧ PinSetsR m' pins := by
  have hfr : ∀ {k : Nat} {f : FnName} {args : List Word} {mx my : Mem} {rx : List Word},
      f ∈ armFns → callW p k f args mx = some (rx, my) → MemFrame stepA stepC mx my := by
    intro k f args mx my rx hf hc
    obtain ⟨s', hs', hfr', -⟩ := triple_of_callW (s₀ := ⟨mx, Locals.init []⟩)
      (hA.closed.memFrame k hf args ⟨mx, Locals.init []⟩) hc
    rw [← hs']; exact hfr'
  cases n with
  | zero => simp [cdfW] at h
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [cdfW_step] at h
  -- `erec_ci`
  cases h1 : callW p n "erec_ci" [i, 1] m with
  | none => rw [h1] at h; cases h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, cdfK1_some] at h
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (erecCi_specW p hV.rcp n ⟨m, Locals.init []⟩ i 1) h1
  rw [hs1] at hW1
  obtain ⟨hS1, hg1, hci1, hcv1, hval1, htop1⟩ :=
    erecCiW_okT (ci := .defnInfo cv v hh) hW1 hS hD hi (by rw [hd]; rfl)
  have hPS1 := PinSetsR.step hPS hg1 (hfr (by decide) h1)
  rw [hd] at hcv1 hval1
  simp only [stepCV, stepVal] at hcv1 hval1
  generalize hq0 : r1.headD 0 = q at h hci1 hcv1 hval1 htop1
  have hqb : q.toNat + 8 < 2 ^ 64 := by
    have := hS1.stage.2.2.1; have := hS1.stage.2.2.2.2.1; omega
  have hq1 : (q + 1).toNat = q.toNat + 1 := toNat_add_small q 1 (by omega)
  obtain ⟨wn, hwn, hwnl, hname0⟩ := decCI_name hci1
  have hname : cv.name = decI wn := hname0
  rw [rdW_of_get? hq1.symm (erecP_get hwn)] at h
  -- `check_constant_val`
  cases h2 : callW p n "check_constant_val" [vis, q + 1] m1 with
  | none => rw [h2] at h; cases h
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2, cdfK2_some] at h
  obtain ⟨s2, hs2, -, hok2, hS2, hg2, -⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (checkConstantVal_refinesT p hV hq hap hkp n hn' ⟨m1, Locals.init []⟩ a dn fe vis (q + 1) cv hS1
      (by rw [hq1]; exact hcv1) (by omega) (denoteCV_lps hcvd) (hkp.call (im_mem _ rfl) h1 hCr)) h2
  subst hs2
  have hPS2 := PinSetsR.step hPS1 hg2 (hfr (by decide) h2)
  have hrun2 := AM.run_of_ok _ _ hok2
  obtain ⟨hstep1, F1, hpure1⟩ :=
    ConRon.Bridge.checkConstantVal_bridge_of_fold rfl (CoreSpec.of_core rfl) hfold hcvd hrun2
  have hok1 := hfold.ofCore hstep1
  have hcA := ConRon.Bridge.denoteCV_ext hcvd hstep1.ext
  have hv1 := ConRon.Bridge.denote_ext hvd hstep1.ext
  have hPD1 : ∃ pinsP, PinsDenote (AM.st (checkConstantVal V fe cv) a).store pins pinsP := by
    obtain ⟨pp, hp⟩ := hPD; exact ⟨pp, PinsDenote.mono hstep1.ext _ _ hp⟩
  generalize AM.st (checkConstantVal V fe cv) a = a2 at hrun2 hS2 hok1 hcA hv1 hPD1
  -- `check_defn_val`
  cases h3 : callW p n "check_defn_val" [vis, q] s2.mem with
  | none => rw [h3] at h; cases h
  | some rm3 =>
  obtain ⟨r3, m3⟩ := rm3
  rw [h3, cdfK3_some] at h
  have hx2 : ArrExt (erecP m1) (erecP s2.mem) := IWGrow.erecPExt hg2
  obtain ⟨s3, hs3, -, hW3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (dv_specW p hV (realCall p) (realCall_spec p) n ⟨s2.mem, Locals.init []⟩ vis q) h3
  subst hs3
  obtain ⟨a3, hrun3, hS3, hM3, hg3⟩ := dvW_okT hq hV.rcp hap hkp hn' "type mismatch in definition"
    hW3 hS2 (ArrExt.decCI hx2 hci1)
    (ArrExt.decCV hx2 hcv1) (ArrExt.hd? hx2 hval1) (denoteCV_lps hcA)
    (hkp.call (im_mem _ rfl) h2 (hkp.call (im_mem _ rfl) h1 hCr))
  have hPS3 := PinSetsR.step hPS2 hg3 (hfr (by decide) h3)
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
  have hvis : fe.visibleBelow = vis.toNat := hS.stage.1.env.vis
  have hpre := ConRon.Bridge.restrict_pushed_find (fe2 := fe.push (.defnInfo cv v hh)) rfl
    (hok3.check.ienv.find?_none (show denoteN a3.store.ns cv.name = some c.name by rw [hname]; exact hnm3)
      (ConRon.Bridge.checkConstantVal_fresh hpure1))
  have hck3 : CheckOK V env ((fe.push (.defnInfo cv v hh)).restrictTo vis.toNat) a3 := by
    rw [← hvis]; exact hok3.check.congr_find hpre rfl
  -- the memory's half after the push: the call's frame, the core memos
  have hf3 := (run_memFrame hlc checkDefnVal_loop (run_of_callW h3)).1
  have hmem3 : TwinMem dn s3.mem a3 :=
    ⟨by rw [hf3.2.2.1]; exact hS2.twin.erec, by rw [hf3.2.2.1]; exact hS2.twin.spn,
      by rw [hf3.2.2.1]; exact hS2.twin.bstk, hM3,
      fun k y e => hstep2.ext.lss.ls.ns k y (hS2.twin.den.dnN k y e)⟩
  have hflag3 : pinW s3.mem 0 ≠ 0 := by
    simp only [pinW, hf3.1 PINS loopA_pins (by decide)]; exact hS2.flag
  generalize hfe2 : fe.push (.defnInfo cv v hh) = fe2 at hS3 hrun3 hck3 hstepOK2
  generalize hw : r3.headD 0 = w at h hS3
  have hC3 : StageC dn vis (fe2.restrictTo vis.toNat) env s3.mem a3 :=
    ⟨hS3.restrict vis, hck3, hmem3, hflag3⟩
  -- the structural gate
  cases h4 : callW p n "defn_nat_gate" [vis, w, wn] s3.mem with
  | none => rw [h4] at h; cases h
  | some rm4 =>
  obtain ⟨r4, m4⟩ := rm4
  rw [h4, cdfK4_some] at h
  obtain ⟨a4, hrun4, hS4, hC4, hg4, hx4⟩ := defnNatGate_okC hG.nat hG.natGate hG.natCert hq hcl hn'
    hwnl h4 hS3 hC3 hok3.envWF hstepOK2 hnm3
  have hPS4 := PinSetsR.step hPS3 hg4 (by
    obtain ⟨s', hs', hfr', -⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
      (hG.natIn.memFrame n (f := "defn_nat_gate") (by decide) [vis, w, wn] ⟨s3.mem, Locals.init []⟩) h4
    rw [← hs']; exact hfr')
  have hPD4 : ∃ pinsP, PinsDenote a4.store pins pinsP := by
    obtain ⟨pp, hp⟩ := hPD3; exact ⟨pp, PinsDenote.mono hx4 _ _ hp⟩
  -- the pin gate
  cases h5 : callW p n "defn_div_gate" [vis, w, wn] m4 with
  | none => rw [h5] at h; cases h
  | some rm5 =>
  obtain ⟨r5, m5⟩ := rm5
  rw [h5, cdfK5_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨a5, hrun5, hS5, hC5, -, hg5, hPS5, -⟩ := hG.div dn hdn vis w fe2 env env2 wn c.name n hn'
    m4 m5 a4 r5 hwnl h5 hS4 hC4 hok3.envWF (hstepOK2.mono hx4) hPS4 hPD4
    (ConRon.Bridge.denoteN_ext hnm3 hx4)
    (hkp.call (im_mem _ rfl) h4 (hkp.call (im_mem _ rfl) h3 (hkp.call (im_mem _ rfl) h2
      (hkp.call (im_mem _ rfl) h1 hCr))))
  refine ⟨fe2, a5, ?_, by simpa using hS5, hC5.mem.memos,
    hg1.trans (hg2.trans (hg3.trans (hg4.trans hg5))), hPS5⟩
  rw [checkDecl_defn_eq, ← hfe2]
  simp only [StateT.run_bind, hrun2, exc_ok_bind', hrun3, hvis, hname]
  rw [hfe2]
  erw [hrun4, exc_ok_bind', hrun5]
  rfl

end L.Arena
