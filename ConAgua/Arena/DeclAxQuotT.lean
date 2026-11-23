module

import ConAgua.Arena.DeclArmT
public import ConAgua.Arena.DeclArmAxiom
import ConAgua.L.ModelGen
import ConAgua.Arena.RefWalk
import ConAgua.Arena.StageC
import ConAgua.Checker.NoVerdictTree
import ConRon.Bridge.Checker.Arms
import ConRon.Bridge.Checker.Base
import ConRon.Bridge.Checker.Basis
import ConRon.Bridge.Checker.DeclVal
public import ConAgua.Verdict.DeclValsE
import all ConAgua.Arena.DeclArms
public import ConAgua.Arena.DeclAxiomSpec4
public import ConAgua.Arena.DeclAxiomSpec
public import ConAgua.Arena.DeclAxiomSpec2
import ConAgua.Arena.DeclArmQuot
import ConAgua.Arena.InferFieldSort
import ConAgua.Arena.BasisBlockT

@[expose] public section

/-!
# The axiom arm, both outcomes, under `StageT` (lane `loopt3`, helper `loopt3-axq`)

`check_decl_axiom`'s unified model and refinement `cda_ref`, from `StageT` back to the stage
relation and the core's memos (option (a), replacing the interim contract
`stubArm_keepsCoreMemos`; the quotient arm `check_decl_quot` is `cdq_ref`, `DeclArmQuot.lean`,
and keeps the memos as a leaf).

Every call of the two arms but `check_constant_val` is a leaf of the declaration loop (`leafFns`:
`erec_ci`, the ROM block reader, `quot_pin_hit`, `check_basis_decl`, `ci_canon_eq`,
`std_axiom_ok`, `trust_compiler_ok`, `of_reduce_ax_ok`, `env_push`; `pin_at` is pure). So no
`TwinOK` or con-ron `CheckOK` has to be carried past a core call: the core's memos are kept by the
leaves' frame (`LeafClosed`) and by `erec_ci`'s (`erecCiW_frame`), and given by the one core call,
the constant check, under `StageT` (`ccv_ref`: `TwinOK` at its entry from the arm's `StageT`
across `erec_ci`'s frame). The twin's `StateOK` is needed only at the arm's entry (the ROM
reader, the canonical comparisons), where the loop has it.

The quotient readers' precondition `NamesDn dn a quotNames` (journal `loopt2`, landing 5) comes
from the loop-start fact `QuotDn dn` (`Quot`'s `sortZ` name `u` has a handle under the record
pool's name decoder) and `TwinOK`'s `den.dnN` (that handle reads back to `u` in the twin's name
store); the quotient record's `denoteCV` from the record's denotation (`TwinFold.den`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF)

local notation "V" => ConLeche.CheckMode.verified

/-- `erec_ci` keeps the core's memos. -/
theorem erecCiW_memos {n : Nat} {m m' : Mem} {i ck : Word} {r : List Word}
    (h : erecCiW n m i ck = some (r, m')) (hM : CoreMemos m) : CoreMemos m' :=
  hM.frame (erecCiW_frame h) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩

/-- A leaf call keeps the core's memos. -/
theorem leaf_memos {p : Prog} (hcl : LeafClosed p) {f : FnName} (hf : f ∈ leafFns) {k : Nat}
    {args : List Word} {x y : Mem} {rx : List Word} (hc : callW p k f args x = some (rx, y))
    (hM : CoreMemos x) : CoreMemos y :=
  hM.frame (callW_leafFrame hcl hf hc) leafA_memo leafC_memo leafA_walk leafC_walk leafA_lp leafC_lp leafA_hb leafC_hb

/-- **The model of `check_decl_quot(i, vis)`, both outcomes**: `erec_ci` through its run,
`check_quot_record` by its unified model. -/
l_model checkDeclQuot_specE (p : Prog) (hp : p.lookup "check_decl_quot" = some checkDeclQuot)
  (hRp : RecProg p) (hc : p.lookup "check_quot_record" = some checkQuotRecordL) (hB : BasisProg p)
  fns [hp ↦ checkDeclQuotE]
  specs [erecCi_specW p hRp n, checkQuotRecord_specE p hc hB n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- `StageT` across `erec_ci(i, 0)` on an axiom or a quotient record (`erecCiW_okA` with the
twin's invariants by `erec_ci`'s frame). -/
theorem erecCiW_okAT {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {i : Word} {r : List Word} {ds : Array IDeclaration}
    {cv : IConstantVal}
    (h : erecCiW n m i 0 = some (r, m')) (hS : StageT dn vis fe m a)
    (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds) (hi : i.toNat < ds.size)
    (hcv : L.Front.CVAt (m.arr64 DECL) (m.arr64 DLP) i.toNat cv) :
    StageT dn vis fe m' a ∧ IWGrow m m' ∧
      decCI (erecP m') (r.headD 0).toNat = some (.axiomInfo cv) ∧
      decCV (erecP m') ((r.headD 0).toNat + CI.cv.toNat) = some cv := by
  obtain ⟨hS', hg, h1, h2, -⟩ := erecCiW_okA h hS.stage hD hi hcv
  have hf := erecCiW_frame h
  exact ⟨⟨hS', hS.twin.frame hf ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
      ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
      ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩,
    by simp only [pinW, hf.arr PINS (by decide) (by decide)]; exact hS.flag⟩, hg, h1, h2⟩

/-- The lookups of the quotient arm. -/
structure QuotArmProg (p : Prog) : Prop where
  cdq : p.lookup "check_decl_quot" = some checkDeclQuot
  rcp : RecProg p
  cqr : QuotRecProg p
  leaf : LeafClosed p

/-- **`check_decl_quot(i, vis)` refines the quotient arm of `checkDeclKind`, both outcomes**, under
`StageT`: the record's constant into `EREC` (`erec_ci(i, 0)`), then `check_quot_record` at the
record's slot (`cqr_ref`). -/
theorem cdq_ref {p : Prog} (hQ : QuotArmProg p) {dn : NIdx → Option ConLeche.Name}
    (hQs : QuotSims p dn) {vis : Word} {fe : IFEnv} {a : AState} (n : Nat) {m : Mem} {i : Word}
    {ds : Array IDeclaration} {pins : List INatOpPinSet} {k : ConLeche.QuotKind}
    {cv : IConstantVal} (hS : StageT dn vis fe m a)
    (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds) (hi : i.toNat < ds.size)
    (hd : ds[i.toNat] = .quotDecl k cv) (hok : ConRon.Bridge.StateOK a)
    (hr : ConRon.Bridge.ReadOK a) {c : ConLeche.ConstantVal}
    (hden : Frontend.denoteCV a.store cv = some c) :
    RefE True (checkDeclQuotE p n m i vis) (checkDeclKind V pins fe (.quotDecl k cv)) a
      (fun v fe' a' => CqrPost m v.1 v.2 fe' a') := by
  have hdecl := hD.recs i.toNat hi
  rw [hd] at hdecl
  obtain ⟨-, hcvAt, hk⟩ := hdecl
  have h1r := hD.room
  have h2r := hD.dsize
  have hkw : rdW (m.arr64 DECL) (7 + 8 * i) = L.Front.dw (m.arr64 DECL) i.toNat 6 :=
    rdW_dw _ (by omega) (by decide) (by decide)
  cases n with
  | zero => rw [checkDeclQuotE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  rw [checkDeclQuotE.eq_2, hkw]
  have hsel : ∀ (kw : Word) (J : Word → Except Err (Word × Mem)),
      (if kw = 1 then J 0 else if kw = 2 then J 1 else if kw = 3 then J 2 else J 3) =
        J (slotOfW kw) := by
    intro kw J; unfold slotOfW
    by_cases h1 : kw = 1 <;> by_cases h2 : kw = 2 <;> by_cases h3 : kw = 3 <;> simp [h1, h2, h3]
  rw [hsel (L.Front.dw (m.arr64 DECL) i.toNat 6) (fun ks => checkDeclQuotE.j1 p n i vis ks m),
    slotOfW_eq, hk, checkDeclQuotE.j1.arm1]
  refine RefE.onlySim (fun _ => checkDeclQuotE.k_erec_ci.none ..) (fun _ _ h => h) fun r1 m1 h1 => ?_
  rw [checkDeclQuotE.k_erec_ci.arm1]
  obtain ⟨hS1, hg1, -, hcv1⟩ := erecCiW_okAT h1 hS hD hi hcvAt
  have hq1 : (r1.headD 0 + CI.cv).toNat = (r1.headD 0).toNat + CI.cv.toNat := by
    obtain ⟨w, hw, -⟩ := decCV_name hcv1
    exact off_add_toNat rfl (L.Arena.erecP_lt64 hw)
  exact L.Arena.RefE.mono (cqr_ref hQ.cqr hQ.leaf hQs n k hS1 hok hr (by rw [hq1]; exact hcv1) hden)
    fun v fe' a' h => ⟨h.stage, hg1.trans h.grow, h.memos⟩

/-- The lookups of the axiom arm. -/
structure AxArmProg (p : Prog) : Prop where
  cda : p.lookup "check_decl_axiom" = some checkDeclAxiom
  rcp : RecProg p
  cqr : QuotRecProg p
  ccv : CcvProg p
  std : StdProg2 p
  tco : TcoProg p
  ora : OraProg p

/-- **The model of `check_decl_axiom(i, vis)`, both outcomes**: `erec_ci` and the pin reads
through their runs, `check_quot_record` and `check_constant_val` by their unified models, the
leaves through `callE`. -/
l_model checkDeclAxiom_specE (p : Prog) (hX : AxArmProg p)
  fns [hX.cda ↦ checkDeclAxiomE]
  specs [erecCi_specW p hX.rcp n, pinAt_specW p hX.cqr.pa n,
    checkQuotRecord_specE p hX.cqr.cqr hX.cqr.basis n, checkConstantVal_specE p hX.ccv n,
    callW_spec p n "std_axiom_ok", callW_spec p n "env_push", callW_spec p n "trust_compiler_ok",
    callW_spec p n "of_reduce_ax_ok"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What the axiom arm gives besides the twin's environment `fe'` (from `m`): the stage relation
over the result word, the core's memos, the growth. -/
structure CdaPost (dn : NIdx → Option ConLeche.Name) (m : Mem) (r : Word) (m' : Mem) (fe' : IFEnv)
    (a' : AState) : Prop where
  stage : StageR r fe' m' a'
  memos : CoreMemos m'
  grow : IWGrow m m'

/-- **The axiom arm refines `checkDeclKind`'s `.axiomDecl` arm, both outcomes**, under `StageT`:
`Quot.sound` is the quotient package's record (`check_quot_record` at slot `4`, `cqr_ref`), else
the constant check (`ccv_ref`, `allow = 0`) and the five recognised axioms (the leaves
`std_axiom_ok`, `trust_compiler_ok`, `of_reduce_ax_ok`, then `env_push`); `propext`/`choice` of
another shape and every other axiom decline (the latter after the name's readback, from the fold
invariant), `sorryAx` is skipped. -/
theorem cda_ref {p : Prog} (hX : AxArmProg p) (hq : KnotStageProg p) (hcl : LeafClosed p)
    (hap : ApdF p) (hkp : CrKeep p) (hcrf : L.Ind.CrfF p) {dn : NIdx → Option ConLeche.Name}
    (hC : CcvSims p dn) (hQs : QuotSims p dn) (hdn : DnInj dn)
    {vis : Word} {fe : IFEnv} {a : AState} {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem}
    {i : Word} {ds : Array IDeclaration} {pins : List INatOpPinSet} {cv : IConstantVal}
    (hS : StageT dn vis fe m a) (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds)
    (hi : i.toNat < ds.size) (hd : ds[i.toNat] = .axiomDecl cv) (hok : ConRon.Bridge.StateOK a)
    {c : ConLeche.ConstantVal} (hcvd : Frontend.denoteCV a.store cv = some c)
    (hF : ∃ env, ConRon.Bridge.FoldOK env fe a) (hCr : L.Stubs.CrOK m) :
    RefE (VerdictCtxU p) (checkDeclAxiomE p n m i vis) (checkDeclKind V pins fe (.axiomDecl cv)) a
      (fun v fe' a' => CdaPost dn m v.1 v.2 fe' a') := by
  have hdecl := hD.recs i.toNat hi
  rw [hd] at hdecl
  obtain ⟨-, hcvAt⟩ := hdecl
  obtain ⟨env, hFo⟩ := hF
  cases n with
  | zero => rw [checkDeclAxiomE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [checkDeclAxiomE.eq_2]
  unfold checkDeclKind
  simp only []
  -- `erec_ci`
  refine RefE.onlySim (fun _ => checkDeclAxiomE.k_erec_ci.none ..) (fun _ _ h => h) fun r1 m1 h1 => ?_
  rw [checkDeclAxiomE.k_erec_ci.arm1]
  have hf1 := erecCiW_frame h1
  have hCr1 := CrOK.frame hCr hf1 (by decide) (by decide)
  obtain ⟨hT1, hg1, hci1, hcv1⟩ := erecCiW_okAT h1 hS hD hi hcvAt
  generalize hq0 : r1.headD 0 = q at hci1 hcv1 ⊢
  obtain ⟨wn, hwn, hwnl, hname0⟩ := decCV_name hcv1
  obtain ⟨wt, hwt, -, -⟩ := (decCV_words hcv1).2.2
  have hq1 : (q + CI.cv).toNat = q.toNat + CI.cv.toNat :=
    off_add_toNat rfl (by have := erecP_lt64 hwt; omega)
  have hname : cv.name = decI wn := hname0
  have hcv1' : decCV (erecP m1) (q + CI.cv).toNat = some cv := by rw [hq1]; exact hcv1
  have ex : rdW (m1.arr64 (L.tierA EREC ((q + (CI.cv + CV.name)) >>> 40)))
      (q + (CI.cv + CV.name) &&& 1099511627775) = wn :=
    (erRdOK m1).at _ CI.cv_name_toNat hwn
  rw [ex]
  -- `Quot.sound`
  refine RefE.bindLift (fun _ => checkDeclAxiomE.k_pin_at.none ..) fun r2 m2 h2 => ?_
  obtain ⟨hm2, hr2, hl2, hrun2⟩ := pinAtW_ok h2 hT1.stage.check.pins
  subst hm2
  have ep2 : r2.headD 0 = pinW m2 (1 + (4 : Word).toNat) := by rw [hr2]; rfl
  have hb2 := decI_beq (k := .name) wn _ hwnl hl2
  have hpq : pinQuotSound.run a = .ok (decI (pinW m2 (1 + (4 : Word).toNat)), a) := by
    simpa [pinQuotSound, show PIN_QUOT_SOUND = (4 : Word).toNat from rfl] using hrun2
  refine ⟨_, _, hpq, ?_⟩
  rw [hname, hb2]
  by_cases eq2 : wn = r2.headD 0
  · ----- `Quot.sound`
    rw [checkDeclAxiomE.k_pin_at.arm1 p _ _ _ _ _ _ eq2]
    rw [ep2] at eq2
    simp only [eq2, decide_true, ite_true]
    exact L.Ind.RefE.ofTrue (L.Arena.RefE.mono
      (cqr_ref hX.cqr hcl hQs n .sound hT1 hok hFo.check.readOK hcv1' hcvd)
      fun v fe' a' h => ⟨h.stage, h.memos, hg1.trans h.grow⟩)
  ----- the ordinary axioms
  rw [checkDeclAxiomE.k_pin_at.arm2 p _ _ _ _ _ _ eq2]
  rw [ep2] at eq2
  simp only [eq2, decide_false, Bool.false_eq_true, ite_false]
  -- the constant check
  have hcc := ccv_ref hX.ccv hq hap hkp hcrf hC hn' hT1 hcv1' hcvd hCr1 (allow := 0) (allowRd := 0)
    (allowSorry := 1)
  rw [show ((0 : Word) != 0) = false from rfl, show ((1 : Word) != 0) = true from rfl] at hcc
  refine RefE.bindE (fun _ => checkDeclAxiomE.k_check_constant_val.none ..) id hcc
    fun ⟨r3, m3⟩ _ a3 hrun3 hP3 => ?_
  rw [checkDeclAxiomE.k_check_constant_val.arm1]
  dsimp only at hP3
  have hS3 := hP3.stage
  have hg3 := hP3.grow
  obtain ⟨hstep1, -⟩ :=
    ConRon.Bridge.checkConstantVal_bridge_of_fold ConRon.Bridge.CoreSpec.of_core hFo hcvd hrun3
  have hok1 := hFo.ofCore hstep1
  have hcA := ConRon.Bridge.denoteCV_ext hcvd hstep1.ext
  have hnmA : denoteN a.store.ns (decI wn) = some c.name := by
    rw [← hname]; exact (ConRon.Bridge.denoteCV_inv hcvd).1
  have hext1 := hstep1.ext
  have hPx : ArrExt (erecP m2) (erecP m3) := L.Ind.IWGrow.ext hg3
  have hM3 : CoreMemos m3 := hS3.twin.memos
  have hlf : ∀ {f : FnName} {k : Nat} {args : List Word} {x y : Mem} {rx : List Word},
      f ∈ leafFns → callW p k f args x = some (rx, y) → CoreMemos x → CoreMemos y :=
    fun hf hc hx => leaf_memos hcl hf hc hx
  -- the standard axioms
  refine RefE.bindLift (fun _ => checkDeclAxiomE.k_std_axiom_ok.none ..) fun r4 m4 h4 => ?_
  obtain ⟨s4, hs4, -, hok4, hS4, hg4, hb4, -⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (stdAxiomOk_refines p hX.std dn hdn vis fe (q + CI.cv) cv n ⟨m3, Locals.init []⟩ a3
      ⟨hS3.stage, ArrExt.decCV hPx hcv1'⟩) h4
  subst hs4
  have hM4 := hlf (leaf_mem _ rfl) h4 hM3
  have hrun4 := AM.run_of_ok _ _ hok4
  refine ⟨_, _, hrun4, ?_⟩
  generalize s4.mem = m4 at *
  generalize AM.res (stdAxiomOk fe cv) a3 = b4 at hrun4 hb4
  generalize AM.st (stdAxiomOk fe cv) a3 = a4 at hrun4 hS4
  obtain ⟨-, hext4, hcache4, -, -⟩ := ConRon.Bridge.stdAxiomOk_run hok1 hcA hrun4
  have hP4 : ArrExt (erecP m2) (erecP m4) := L.Ind.IWGrow.ext (hg3.trans hg4)
  -- a push of the axiom, after a passed test
  have push : ∀ {mx : Mem} {ax : AState}, StageR vis fe mx ax → IWGrow m2 mx → CoreMemos mx →
      RefE (VerdictCtxU p) (checkDeclAxiomE.k_env_push p (liftE (callW p n "env_push" [vis, q] mx)))
        (pure (fe.push (.axiomInfo cv)) : AM IFEnv) ax
        (fun v fe' a' => CdaPost dn m v.1 v.2 fe' a') := by
    intro mx ax hSx hgx hMx
    refine RefE.onlySim (fun _ => checkDeclAxiomE.k_env_push.none ..) (fun _ _ h => h) fun ry my e => ?_
    rw [checkDeclAxiomE.k_env_push.arm1]
    obtain ⟨hSy, hgy⟩ := push_call hX.rcp e hSx (ArrExt.decCI (L.Ind.IWGrow.ext hgx) hci1)
    exact RefE.ret rfl ⟨by simpa using hSy, hlf (leaf_mem _ rfl) e hMx,
      hg1.trans (hgx.trans hgy)⟩
  rw [checkDeclAxiomE.k_std_axiom_ok.eq_2]
  refine RefE.split (fun z4 => by rw [← hb4]; simpa using z4) (fun z4 => by rw [← hb4] at z4; simpa using z4)
    (fun _ _ => push hS4 (hg3.trans hg4) hM4) fun _ _ => ?_
  -- `Lean.trustCompiler`
  refine RefE.bindLift (fun _ => checkDeclAxiomE.k_pin_at_2.none ..) fun r5 m5 h5 => ?_
  obtain ⟨hm5, hr5, hl5, hrun5⟩ := pinAtW_ok h5 hS4.check.pins
  subst hm5
  have ep5 : r5.headD 0 = pinW m5 (1 + (42 : Word).toNat) := by rw [hr5]; rfl
  have hb5 := decI_beq (k := .name) wn _ hwnl hl5
  have htn : trustCompilerName.run a4 = .ok (decI (pinW m5 (1 + (42 : Word).toNat)), a4) := by
    simpa [trustCompilerName, pinTrustCompiler, show PIN_TRUST_COMPILER = (42 : Word).toNat from rfl]
      using hrun5
  refine ⟨_, _, htn, ?_⟩
  rw [hb5, checkDeclAxiomE.k_pin_at_2.eq_2]
  refine RefE.split (fun eq5 => by rw [← ep5]; exact decide_eq_true eq5)
    (fun eq5 => by rw [ep5]; exact of_decide_eq_true eq5) (fun _ _ => ?_) fun _ _ => ?_
  · refine RefE.bindLift (fun _ => checkDeclAxiomE.k_trust_compiler_ok.none ..) fun r6 m6 h6 => ?_
    obtain ⟨s6, hs6, -, hok6, hS6, hg6, hb6, -⟩ := triple_of_callW (s₀ := ⟨m5, Locals.init []⟩)
      (trustCompilerOk_refines p hX.tco dn vis fe (q + CI.cv) cv n ⟨m5, Locals.init []⟩ a4
        ⟨hS4, ArrExt.decCV hP4 hcv1'⟩) h6
    subst hs6
    refine ⟨_, _, AM.run_of_ok _ _ hok6, ?_⟩
    rw [checkDeclAxiomE.k_trust_compiler_ok.eq_2]
    refine RefE.guardIf rfl (fun z6 => by rw [← hb6, z6]; rfl)
      (fun z6 => by rw [← hb6] at z6; simpa using z6) fun _ _ => ?_
    exact push hS6 (hg3.trans (hg4.trans hg6)) (hlf (leaf_mem _ rfl) h6 hM4)
  -- the `ofReduce*` pair
  refine RefE.onlySim (fun _ => checkDeclAxiomE.k_pin_at_3.none ..) (fun _ _ h => h) fun r7 m7 h7 => ?_
  rw [checkDeclAxiomE.k_pin_at_3.arm1]
  obtain ⟨hm7, hr7, hl7, hrun7⟩ := pinAtW_ok h7 hS4.check.pins
  subst hm7
  have ep7 : r7.headD 0 = pinW m7 (1 + (45 : Word).toNat) := by rw [hr7]; rfl
  refine RefE.onlySim (fun _ => checkDeclAxiomE.k_pin_at_4.none ..) (fun _ _ h => h) fun r8 m8 h8 => ?_
  obtain ⟨hm8, hr8, hl8, hrun8⟩ := pinAtW_ok h8 hS4.check.pins
  subst hm8
  have ep8 : r8.headD 0 = pinW m8 (1 + (46 : Word).toNat) := by rw [hr8]; rfl
  have hb7 := decI_beq (k := .name) wn _ hwnl hl7
  have hb8 := decI_beq (k := .name) wn _ hwnl hl8
  have hon : ofReduceNatName.run a4 = .ok (decI (pinW m8 (1 + (45 : Word).toNat)), a4) := by
    simpa [ofReduceNatName, pinOfReduceNat, show PIN_OF_REDUCE_NAT = (45 : Word).toNat from rfl]
      using hrun7
  have hob : ofReduceBoolName.run a4 = .ok (decI (pinW m8 (1 + (46 : Word).toNat)), a4) := by
    simpa [ofReduceBoolName, pinOfReduceBool, show PIN_OF_REDUCE_BOOL = (46 : Word).toNat from rfl]
      using hrun8
  refine RefE.bind_right hon (RefE.bind_right hob ?_)
  rw [checkDeclAxiomE.k_pin_at_4.eq_2, hb7, hb8, ← ep7, ← ep8]
  refine RefE.split (fun eq8 => by simpa using eq8) (fun eq8 => by simpa using eq8) (fun _ _ => ?_) fun _ _ => ?_
  · refine RefE.bindLift (fun _ => checkDeclAxiomE.k_of_reduce_ax_ok.none ..) fun r9 m9 h9 => ?_
    obtain ⟨s9, hs9, -, hok9, hS9, hg9, hb9, -⟩ := triple_of_callW (s₀ := ⟨m8, Locals.init []⟩)
      (ofReduceAxOk_refines p hX.ora dn hdn vis fe (q + CI.cv) cv n ⟨m8, Locals.init []⟩ a4
        ⟨hS4, ArrExt.decCV hP4 hcv1'⟩) h9
    subst hs9
    refine ⟨_, _, AM.run_of_ok _ _ hok9, ?_⟩
    rw [checkDeclAxiomE.k_of_reduce_ax_ok.eq_2]
    refine RefE.guardIf rfl (fun z9 => by rw [← hb9, z9]; rfl)
      (fun z9 => by rw [← hb9] at z9; simpa using z9) fun _ _ => ?_
    exact push hS9 (hg3.trans (hg4.trans hg9)) (hlf (leaf_mem _ rfl) h9 hM4)
  -- `propext` / `choice` of another shape
  refine RefE.onlySim (fun _ => checkDeclAxiomE.k_pin_at_5.none ..) (fun _ _ h => h) fun r10 m10 h10 => ?_
  rw [checkDeclAxiomE.k_pin_at_5.arm1]
  obtain ⟨hm10, hr10, hl10, hrun10⟩ := pinAtW_ok h10 hS4.check.pins
  subst hm10
  have ep10 : r10.headD 0 = pinW m10 (1 + (32 : Word).toNat) := by rw [hr10]; rfl
  refine RefE.onlySim (fun _ => checkDeclAxiomE.k_pin_at_6.none ..) (fun _ _ h => h) fun r11 m11 h11 => ?_
  obtain ⟨hm11, hr11, hl11, hrun11⟩ := pinAtW_ok h11 hS4.check.pins
  subst hm11
  have ep11 : r11.headD 0 = pinW m11 (1 + (33 : Word).toNat) := by rw [hr11]; rfl
  have hb10 := decI_beq (k := .name) wn _ hwnl hl10
  have hb11 := decI_beq (k := .name) wn _ hwnl hl11
  have hpn : propextName.run a4 = .ok (decI (pinW m11 (1 + (32 : Word).toNat)), a4) := by
    simpa [propextName, pinPropext, show PIN_PROPEXT = (32 : Word).toNat from rfl] using hrun10
  have hch : choiceName.run a4 = .ok (decI (pinW m11 (1 + (33 : Word).toNat)), a4) := by
    simpa [choiceName, pinChoice, show PIN_CHOICE = (33 : Word).toNat from rfl] using hrun11
  refine RefE.bind_right hpn (RefE.bind_right hch ?_)
  rw [checkDeclAxiomE.k_pin_at_6.eq_2, hb10, hb11, ← ep10, ← ep11]
  refine RefE.guardThen rfl (fun eq11 => by simpa using eq11) (fun eq11 => by simpa using eq11) fun _ _ => ?_
  -- `sorryAx` is skipped
  refine RefE.bindLift (fun _ => checkDeclAxiomE.k_pin_at_7.none ..) fun r12 m12 h12 => ?_
  obtain ⟨hm12, hr12, hl12, hrun12⟩ := pinAtW_ok h12 hS4.check.pins
  subst hm12
  have ep12 : r12.headD 0 = pinW m12 (1 + (13 : Word).toNat) := by rw [hr12]; rfl
  have hb12 := decI_beq (k := .name) wn _ hwnl hl12
  have hsa : pinSorryAx.run a4 = .ok (decI (pinW m12 (1 + (13 : Word).toNat)), a4) := by
    simpa [pinSorryAx, show PIN_SORRY_AX = (13 : Word).toNat from rfl] using hrun12
  refine ⟨_, _, hsa, ?_⟩
  rw [hb12, checkDeclAxiomE.k_pin_at_7.eq_2]
  refine RefE.split (fun eq12 => by rw [← ep12]; exact decide_eq_true eq12)
    (fun eq12 => by rw [ep12]; exact of_decide_eq_true eq12)
    (fun _ _ => RefE.ret rfl ⟨by simpa using hS4, hM4, hg1.trans (hg3.trans hg4)⟩) fun _ _ => ?_
  -- the readback of the name
  have hrn4 : ReadNCOK a4 := fun h x e =>
    ConRon.Bridge.denoteN_ext (hok1.check.caches.readN h x (by rw [← hcache4]; exact e)) hext4
  have hnm4 : denoteN a4.store.ns (decI wn) = some c.name :=
    ConRon.Bridge.denoteN_ext (ConRon.Bridge.denoteN_ext hnmA hext1) hext4
  obtain ⟨X, hrunN, -⟩ := readNameM_run' a4 (decI wn) c.name hnm4 hrn4
  exact RefE.bind_right hrunN fun _ => ErrClaim.fail _ _ rfl

/-! ## The theorem arm -/

/-- The lookups of the theorem arm. -/
structure ThmArmProg (p : Prog) : Prop where
  cdt : p.lookup "check_decl_thm" = some checkDeclThm
  ccv : CcvProg p

set_option experimental.vcgen true in
/-- **The model of `check_decl_thm`, both outcomes**: `erec_ci` through its run,
`check_constant_val` and `check_thm_val` by their unified models, `env_push` through `callE`. -/
l_model checkDeclThm_specE (p : Prog) (hX : ThmArmProg p)
  fns [hX.cdt ↦ checkDeclThmE]
  specs [erecCi_specW p hX.ccv.val.rcp n, checkConstantVal_specE p hX.ccv n,
    checkThmVal_specE p hX.ccv.val n, callW_spec p n "env_push"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **The theorem arm `check_decl_thm` refines `checkDeclKind` on a theorem under `StageT`, both
outcomes**: the record into `EREC` (`erec_ci(i, 2)`), the constant check (`ccv_ref`, `allow = 0`),
the theorem check (`checkThmVal_ref`, its prefix's premises from the fold invariant after the
constant check), the push. -/
theorem cdt_ref {p : Prog} (hX : ThmArmProg p) (hq : KnotStageProg p) (hcl : LeafClosed p)
    (hap : ApdF p) (hkp : CrKeep p) (hcrf : L.Ind.CrfF p) {dn : NIdx → Option ConLeche.Name}
    (hC : CcvSims p dn) {vis : Word} {fe : IFEnv} {a : AState} {n : Nat} (hn : n ≤ 2 ^ 62)
    {m : Mem} {i : Word} {ds : Array IDeclaration} {pins : List INatOpPinSet} {cv : IConstantVal}
    {v : EIdx} (hS : StageT dn vis fe m a) (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds)
    (hi : i.toNat < ds.size) (hd : ds[i.toNat] = .thmDecl cv v) {c : ConLeche.ConstantVal}
    (hcvd : Frontend.denoteCV a.store cv = some c)
    (hF : ∃ env, ConRon.Bridge.FoldOK env fe a) (hCr : L.Stubs.CrOK m) :
    RefE (VerdictCtxU p) (checkDeclThmE p n m i vis) (checkDeclKind V pins fe (.thmDecl cv v)) a
      (fun v fe' a' => CdaPost dn m v.1 v.2 fe' a') := by
  obtain ⟨env, hFo⟩ := hF
  cases n with
  | zero => rw [checkDeclThmE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [checkDeclThmE.eq_2]
  unfold checkDeclKind
  simp only []
  -- `erec_ci(i, 2)`
  refine RefE.onlySim (fun _ => checkDeclThmE.k_erec_ci.none ..) (fun _ _ h => h) fun r1 m1 h1 => ?_
  rw [checkDeclThmE.k_erec_ci.arm1]
  have hCr1 := CrOK.frame hCr (erecCiW_frame h1) (by decide) (by decide)
  obtain ⟨hT1, hg1, hci1, hcv1, hv1, -⟩ := erecCiW_okT (ci := .thmInfo cv) h1 hS hD hi (by rw [hd]; rfl)
  rw [hd] at hcv1 hv1
  simp only [stepCV, stepVal] at hcv1 hv1
  generalize r1.headD 0 = q at hci1 hcv1 hv1 ⊢
  obtain ⟨wt, hwt, -, -⟩ := (decCV_words hcv1).2.2
  have hq1 : (q + CI.cv).toNat = q.toNat + CI.cv.toNat :=
    off_add_toNat rfl (by have := erecP_lt64 hwt; omega)
  have hcv1' : decCV (erecP m1) (q + CI.cv).toNat = some cv := by rw [hq1]; exact hcv1
  -- the constant check
  have hcc := ccv_ref hX.ccv hq hap hkp hcrf hC hn' hT1 hcv1'
    hcvd hCr1 (allow := 0) (allowRd := 0) (allowSorry := 0)
  rw [show ((0 : Word) != 0) = false from rfl] at hcc
  refine RefE.bindE (fun _ => checkDeclThmE.k_check_constant_val.none ..) id hcc
    fun ⟨r3, m3⟩ _ a3 hrun3 hP3 => ?_
  rw [checkDeclThmE.k_check_constant_val.arm1]
  dsimp only at hP3
  obtain ⟨hstep1, F, hcF⟩ :=
    ConRon.Bridge.checkConstantVal_bridge_of_fold ConRon.Bridge.CoreSpec.of_core hFo hcvd hrun3
  have hok1 := hFo.ofCore hstep1
  have hg3 := hP3.grow
  obtain ⟨wv, hwv, hwvl, rfl⟩ := hd?_some hv1
  -- the theorem check
  refine RefE.bindE (fun _ => checkDeclThmE.k_check_thm_val.none ..) id
    (checkThmVal_ref hX.ccv hq hap hkp hcrf hn' hP3.stage (ArrExt.decCV (L.Ind.IWGrow.ext hg3) hcv1)
      (hg3.ext _ _ hwv) hwvl
      ⟨env, c, hFo.envWF, hok1.check, ConRon.Bridge.denoteCV_ext hcvd hstep1.ext,
        ConLeche.Expr.WScoped.of_not_hasFvar (ConRon.Bridge.checkConstantVal_typeWF hcF).fvar⟩
      hP3.crOK)
    fun ⟨r4, m4⟩ ci4 a4 hrun4 ⟨hS4, hg4, hCr4, hr4, hci4⟩ => ?_
  dsimp only at hr4 hS4 hg4 hCr4
  subst hr4 hci4
  rw [checkDeclThmE.k_check_thm_val.arm1]
  -- the push
  refine RefE.onlySim (fun _ => checkDeclThmE.k_env_push.none ..) (fun _ _ h => h) fun r5 m5 h5 => ?_
  rw [checkDeclThmE.k_env_push.arm1]
  obtain ⟨hS5, hg5⟩ := push_call hX.ccv.val.rcp h5 hS4.stage
    (ArrExt.decCI (L.Ind.IWGrow.ext (hg3.trans hg4)) hci1)
  exact RefE.ret rfl ⟨by simpa using hS5,
    leaf_memos hcl (leaf_mem _ rfl) h5 hS4.twin.memos, hg1.trans (hg3.trans (hg4.trans hg5))⟩

end L.Arena
