module

public import ConAgua.Arena.IndT.BlockRM
public import ConAgua.Verdict.DeclValsE
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
import ConAgua.Arena.IndT.Install1
import ConAgua.Arena.IndPartsSpec.IndPartsProg2
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved
import ConAgua.Arena.RecGenSpec.ClassFeR
import ConAgua.Arena.IndRealMemoCrT
import ConRon.Bridge.Checker.Base
import ConAgua.Arena.StageC
import ConLeche.Verify.BridgeWfImp
import ConRon.Bridge.Inductives.BlockTail
import all ConAgua.Arena.IndInstall
import ConAgua.L.WordOff

@[expose] public section

/-!
# `reduce_member`'s refinement (lane `ronsync2`, stage 3)

`reduce_member(vis, ms, nP)` (`IndInstall.lean`) refines `reduceMember .verified`, both outcomes
(`rm_ref`): `former_def_headed` (`fdhW_ok`), `declined_at_definition` (`dadW_ok`) and
`sl_contains`, `check_constant_val` (`ccv_ref`), `reduced_former` (`rf_ref`), `is_def_eq_core`
(`idc_ref`), the fresh member record (`rec5`); twin side as con-ron's `reduceMember_spec`.
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The lookups `reduce_member`'s model and refinement read. -/
structure RmProg (p : Prog) : Prop extends RfProg p where
  pir : p.lookup "pi_result" = some piResultL
  frs : p.lookup "former_res_sort" = some formerResSortL
  fdh : p.lookup "former_def_headed" = some formerDefHeadedL
  pin : p.lookup "pin_at" = some pinAtL
  dad : p.lookup "declined_at_definition" = some declinedAtDefinition
  slc : p.lookup "sl_contains" = some slContains
  r5 : p.lookup "rec5" = some rec5
  rm : p.lookup "reduce_member" = some reduceMember

set_option experimental.vcgen true in
/-- **`reduce_member`'s unified model**: `check_constant_val`, `reduced_former` and
`is_def_eq_core` through their calls, the rest (outside the verdict closure) lifted. -/
l_model rmE_spec (p : Prog) (hP : RmProg p)
  fns [hP.rm ↦ rmE]
  specs [callW_spec p n "former_def_headed", callW_spec p n "declined_at_definition",
    callW_spec p n "sl_contains", callW_spec p n "rec5"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `reduce_member` gives (from `m`, `a`): the stage after the twin's `CoreStep`, the pools
grown, the member's record below the tops. -/
structure RmPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (a : AState) (v : Word × Mem) (ms : MemberShape) (a' : AState) : Prop where
  stage : StageC dn vis fe env v.2 a'
  grow : IWGrow m v.2
  abs : AbsOK v.2
  core : ConRon.Bridge.CoreStep env fe a a'
  dec : DecB (fun m => decMSB m v.1.toNat) v.2 ms
  top : v.1.toNat + 5 ≤ iwTop v.2

/-- **A fresh member record** (`rec5`) whose words `1 ‥ 4` are those of the record of `msh` and
whose word `0` points at `cvR`'s constant record decodes as `{ msh with cvT := cvR }`. -/
theorem decMS_fresh {m m' : Mem} {ms qn cvpn : Nat} {msh : MemberShape} {cvR : IConstantVal}
    (hms : DecB (fun m => decMS m ms) m msh) (hg : IWGrow m m')
    (hcv : DecB (fun m => decCVp m cvpn) m' cvR) (h0 : iwN (truncM m') qn = some cvpn)
    (hk : ∀ k, 1 ≤ k → k ≤ 4 → iwN (truncM m') (qn + k) = iwN (truncM m) (ms + k)) :
    DecB (fun m => decMS m qn) m' { msh with cvT := cvR } := by
  obtain ⟨-, ⟨a4, ha4, hd4⟩, hni, hct⟩ := decMS_some (m := truncM m) hms
  have hd4' : DecB (fun m => decCVp m a4) m' msh.declared :=
    (show DecB (fun m => decCVp m a4) m msh.declared from hd4).grow (OMono.decCVp _) hg
  obtain ⟨o, l, ho, hl, hpl⟩ := decAt_some hct
  have hpl' : DecB (fun m => decPL m (decCN m) o l) m' msh.ctors :=
    (show DecB (fun m => decPL m (decCN m) o l) m msh.ctors from hpl).grow
      (OMono.decPL decCN_mono o l) hg
  show decMS (truncM m') qn = some _
  have e1 := hk 1 (by omega) (by omega)
  have e2 := hk 2 (by omega) (by omega)
  have e3 := hk 3 (by omega) (by omega)
  have e4 := hk 4 (by omega) (by omega)
  rw [hni] at e1
  rw [ho] at e2
  rw [show ms + 3 = ms + 2 + 1 by omega, hl] at e3
  rw [ha4] at e4
  have hcv' : decCVp (truncM m') cvpn = some cvR := hcv
  have hd4'' : decCVp (truncM m') a4 = some msh.declared := hd4'
  have hpl'' : decPL (truncM m') (decCN (truncM m')) o l = some msh.ctors := hpl'
  simp only [decMS, decAt, h0, hcv', e4, hd4'', e1, e2, show qn + 2 + 1 = qn + 3 by omega, e3, hpl'',
    bind, Option.bind, pure]

/-- `decMS_fresh` with the constructor slice's bound. -/
theorem decMSB_fresh {m m' : Mem} {ms qn cvpn : Nat} {msh : MemberShape} {cvR : IConstantVal}
    (hms : DecB (fun m => decMSB m ms) m msh) (hg : IWGrow m m')
    (hcv : DecB (fun m => decCVp m cvpn) m' cvR) (h0 : iwN (truncM m') qn = some cvpn)
    (hk : ∀ k, 1 ≤ k → k ≤ 4 → iwN (truncM m') (qn + k) = iwN (truncM m) (ms + k))
    (hT : iwTop m' ≤ (m'.arr64 IW).size) :
    DecB (fun m => decMSB m qn) m' { msh with cvT := cvR } := by
  have hd := decMSB_some (m := truncM m) hms
  have h1 := decMS_fresh (m := m) (ms := ms) hd.1 hg hcv h0 hk
  obtain ⟨o, l, ho, hl, hb, -⟩ := decCNSB_bound (m := m) (q := ms + 2) hd.2
  have e2 := hk 2 (by omega) (by omega)
  have e3 := hk 3 (by omega) (by omega)
  exact decMSB_of h1 (by rw [e2]; exact ho) (by rw [e3, show ms + 3 = ms + 2 + 1 by omega]; exact hl)
    (le_iwA_truncM_size (Nat.le_trans hb hg.iw) hT)

section rm
variable {p : Prog} (hV : CcvProg p) (hq : KnotStageProg p) (hap : ApdF p) (hkp : CrKeep p)
  (hcrf : CrfF p) (hP : RmProg p) (hWt : WhnfTopE p) {dn : NIdx → Option ConLeche.Name}
  (hCS : CcvSims p dn) {vis : Word} {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hV hq hap hkp hcrf hP hWt hCS henv in
theorem rm_ref (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState} {nP ms : Word} {msh : MemberShape}
    {msP : ConLeche.MemberShape} (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hmsB : DecB (fun m => decMSB m ms.toNat) m msh) (hmsb : ms.toNat + 5 ≤ iwTop m)
    (hmsP : ConRon.Bridge.Inductives.dMember a.store msh = some msP) :
    RefE (VerdictCtxU p) (rmE p n m vis ms nP) (ConRon.Arena.reduceMember V fe msh nP.toNat) a
      (fun v x a' => RmPost dn vis fe env m a v x a') := by
  rcases n with _ | n
  · rw [rmE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  have hS := hC.stage
  obtain ⟨hcvP, -, -⟩ := ConRon.Bridge.Inductives.dMember_inv hmsP
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hms : DecB (fun m => decMS m ms.toNat) m msh := decMSB_decMS hmsB
  obtain ⟨⟨c, hc, hcv⟩, -, hni, -⟩ := decMS_some (m := truncM m) hms
  obtain ⟨hw0, hcb, hmsl⟩ := partsIwRd hc rfl
  have hcvm : decCVp m (UInt64.ofNat c : Word).toNat = some msh.cvT := by
    rw [UInt64.toNat_ofNat_of_lt' hcb]; exact DecB.get (OMono.decCVp _) hcv
  have hcvB : DecB (fun m => decCVp m (UInt64.ofNat c : Word).toNat) m msh.cvT := by
    rw [UInt64.toNat_ofNat_of_lt' hcb]; exact hcv
  obtain ⟨hty32, htye⟩ := partsCVType hcvB (w := UInt64.ofNat c) rfl
  rw [rmE.arm1, hw0]
  unfold ConRon.Arena.reduceMember
  -- `former_def_headed`
  refine RefE.bindLift (fun _ => rfl) fun r1 m1 h1 => ?_
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (fdhW_spec p hP.fdh n _ _) h1
  simp only at hs1 hW1
  subst hs1
  obtain ⟨hm1, hrun1⟩ := fdhW_ok hP.pir hP.frs hS.check.arena.base hty32 hW1 (cv := msh.cvT) htye.symm
  rw [hm1]
  refine ⟨_, _, hrun1, ?_⟩
  dsimp only [rmE.k_former_def_headed]
  by_cases hz : r1.headD 0 = 0
  · rw [ite_eq_left hz]
    simp only [hz, bne_self_eq_false, Bool.false_eq_true, ite_false]
    exact RefE.ret rfl ⟨hC, IWGrow.refl m, hA, ConRon.Bridge.CoreStep.refl hC.check, hmsB, by omega⟩
  rw [ite_eq_right hz]
  simp only [bne_iff_ne, ne_eq, hz, not_false_eq_true, ite_true]
  -- `declined_at_definition`
  refine RefE.bindLift (fun _ => rfl) fun r2 m2 h2 => ?_
  obtain ⟨s2, hs2, -, hW2⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (dadW_spec p hP.dad n _) h2
  simp only at hs2 hW2
  subst hs2
  obtain ⟨ws, hrun2, hsl2, hws2, hg2, hf2, -, hroom2⟩ :=
    dadW_ok hP.pin hP.alloc hS.check.pins hS.iw.ctl hS.iw.iwSize hW2
  refine ⟨_, _, hrun2, ?_⟩
  have hS2 : StageR vis fe s2.mem a := stage_frame_iw hS hf2 hroom2
  have hA2 : AbsOK s2.mem := AFr.of_frame hf2 (by decide) (by decide) hA
  have hC2 : StageC dn vis fe env s2.mem a :=
    hC.of_pstep hS2 hA2 (ConRon.Bridge.Inductives.PStep.refl hC.check.state)
  have hcvm2 : decCVp s2.mem (UInt64.ofNat c : Word).toNat = some msh.cvT :=
    DecB.stab (OMono.decCVp _) hcvB _ hg2
  obtain ⟨wx, hwx, hwxl, hname⟩ := decCV_name (a := erecP s2.mem) hcvm2
  have ex : rdW (s2.mem.arr64 (tierA EREC ((UInt64.ofNat c : Word) >>> 40)))
      ((UInt64.ofNat c : Word) &&& 1099511627775) = wx := by
    rw [erRd_congr rfl rfl]; exact erRd_of _ _ hwx
  dsimp only [rmE.k_declined_at_definition]
  rw [ex]
  -- `sl_contains`
  refine RefE.onlySim (fun _ => rfl)
    (Q := fun r m₁ => m₁ = s2.mem ∧ r.headD 0 = if ws.contains wx then 1 else 0)
    (fun r m₁ hc' => by
      obtain ⟨s', hs', -, hm', hc''⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
        (slContains_spec p hP.slc n _ _ _ _) hc'
      simp only at hs' hm' hc''
      exact ⟨hs' ▸ hm', containsW_ok n _ _ _ _ _ ws hsl2 hc''⟩) fun r3 m3 ⟨hm3, hr3⟩ => ?_
  subst hm3
  dsimp only [rmE.k_sl_contains]
  have e1 : (ws.map decI).contains msh.cvT.name = ws.contains wx := by
    rw [hname]; exact contains_map_decI wx hwxl ws hws2
  rw [e1]
  refine RefE.guardThen (by decide) (fun h => ?_) (fun h => ?_) fun _ _ => ?_
  · rw [hr3] at h; revert h; cases ws.contains wx <;> simp
  · rw [hr3, h]; decide
  -- `check_constant_val`
  have hcvx : CVExt s2.mem (UInt64.ofNat c : Word).toNat := CVExt.of_dec hcvm2
  refine RefE.bindRun (s₀ := ⟨s2.mem, Locals.init []⟩) (fun _ => rfl)
    (checkConstantVal_specE p hV n _ vis _ 0 0 0) (fun hG => hG.nv) id
    (ccv_ref (allow := 0) (allowRd := 0) (allowSorry := 0) hV hq hap hkp hcrf hCS (by omega) hC2.stageT
      (rec2DecCV_erecP hcvm2 hcvx) hcvP hA2.cr.crOK)
    fun r4 s4 u4 a4 _ _ hr4 hP4 => ?_
  obtain ⟨c4, F₄, hF₄⟩ := ConRon.Bridge.checkConstantVal_bridge ConRon.Bridge.CoreSpec.of_core
    hC.check henv hcvP hr4
  have hC4 : StageC dn vis fe env s4.mem a4 := StageC.of_T hP4.stage c4.ok
  have hA4 : AbsOK s4.mem := hP4.abs hA2
  have hg04 : IWGrow m s4.mem := hg2.trans hP4.grow
  have hws : ConLeche.Expr.WScoped 0 msP.cvT.type :=
    ConLeche.Expr.WScoped.of_not_hasFvar (ConLeche.checkConstantVal_typeWF hF₄).1
  dsimp only [rmE.k_check_constant_val]
  have hms4 : DecB (fun m => decMS m ms.toNat) s4.mem msh := hms.grow (decMS_mono _) hg04
  obtain ⟨-, -, hni4, -⟩ := decMS_some (m := truncM s4.mem) hms4
  obtain ⟨hw1, hnb, -⟩ := partsIwRd hni4 (w := ms + 1) (by rw [UInt64.toNat_add]; simp; omega)
  rw [hw1]
  refine RefE.abort0 rfl fun hov => ?_
  have hk : (nP + UInt64.ofNat msh.nIdx).toNat = nP.toNat + msh.nIdx := by
    rw [L.toNat_add_of_not_lt hov, UInt64.toNat_ofNat_of_lt' hnb]
  -- `reduced_former`
  have hcvB4 : DecB (fun m => decCVp m (UInt64.ofNat c : Word).toNat) s4.mem msh.cvT :=
    hcvB.grow (OMono.decCVp _) hg04
  have hcvP4 := ConRon.Bridge.denoteCV_ext hcvP c4.ext
  have hRF := rf_ref hq hP.toRfProg henv n (by omega) (n := nP + UInt64.ofNat msh.nIdx) hC4 hA4 hcvB4
    hcvP4 hws
  rw [hk] at hRF
  refine RefE.bindRun (s₀ := ⟨s4.mem, Locals.init []⟩) (fun _ => rfl)
    (rfE_spec p hP.toRfProg n _ vis _ _) (fun hG => hG.nv) (fun hG => ⟨hG.nv, hWt⟩) hRF
    fun r5 s5 cvR a5 _ _ hr5 hR5 => ?_
  obtain ⟨c5, cvRP, hcvRP, hF5⟩ := ConRon.Bridge.Inductives.reducedFormer_specF
    ConRon.Bridge.CoreSpec.of_core henv msh.cvT msP.cvT _ hws a4 a5 cvR c4.ok hcvP4 hr5
  have hwR : ConLeche.Expr.WScoped 0 cvRP.type :=
    ConLeche.Expr.WScoped.of_not_hasFvar (ConLeche.Cached.Runs.reducedFormer_hasFvar henv
      (ConLeche.checkConstantVal_typeWF hF₄).1 hF5)
  have hg05 : IWGrow m s5.mem := hg04.trans hR5.grow
  have hcvB5 : DecB (fun m => decCVp m (UInt64.ofNat c : Word).toNat) s5.mem msh.cvT :=
    hcvB.grow (OMono.decCVp _) hg05
  obtain ⟨hx32, hxe⟩ := partsCVType hcvB5 (w := UInt64.ofNat c) rfl
  have hcvR5 := installCvDecB hR5.cv (CVExt.of_dec hR5.cv)
  obtain ⟨hy32, hye⟩ := partsCVType hcvR5 (w := r5.headD 0) rfl
  dsimp only [rmE.k_reduced_former]
  -- `is_def_eq_core`
  rw [← hye]
  refine RefE.bindE (fun _ => rfl) (fun hG => hG.core)
    (idc_ref hq henv (n := n) (by omega) (InsAt.refl hR5.stage hR5.abs) (dep := 0) (d := 0) rfl hxe hx32 hy32
      (ConRon.Bridge.denoteCV_type (ConRon.Bridge.denoteCV_ext hcvP4 hR5.core.ext))
      (by have := ConRon.Bridge.denoteCV_type hcvRP; rw [← hye] at this; exact this) hws hwR)
    fun ⟨r6, m6⟩ b6 a6 hr6 ⟨k6, hb6⟩ => ?_
  dsimp only [rmE.k_is_def_eq_core] at hb6 ⊢
  refine RefE.guard (by decide) hb6.1 hb6.2 fun _ _ => ?_
  -- `rec5` (no twin step)
  have hS6 := k6.stage.stage
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r7 m7 h7 => ?_
  obtain ⟨s7, hs7, -, hW7⟩ := triple_of_callW (s₀ := ⟨m6, Locals.init []⟩)
    (rec5_specW p hP.alloc n hP.r5 _ _ _ _ _ _) h7
  simp only at hs7 hW7
  subst hs7
  obtain ⟨hr7, hget7, hg7, hf7, htop7, hroom7⟩ := recW_post hW7 hS6.iw.ctl hS6.iw.iwSize rfl
  simp only [List.length_cons, List.length_nil] at htop7 hroom7
  have hS7 : StageR vis fe s7.mem a6 := stage_frame_iw hS6 hf7 (by simp only at htop7 hroom7 ⊢; omega)
  have hA7 : AbsOK s7.mem := AFr.of_frame hf7 (by decide) (by decide) k6.abs
  have hg06 : IWGrow m m6 := hg05.trans k6.grow
  have hq : (rdW (m6.arr64 CTL) 200).toNat = iwTop m6 := rfl
  -- the fresh record's words
  have hnew : ∀ j < 5, iwN (truncM s7.mem) ((rdW (m6.arr64 CTL) 200).toNat + j) =
      ([r5.headD 0, rdW (m6.arr64 IW) (ms + 1), rdW (m6.arr64 IW) (ms + 2), rdW (m6.arr64 IW) (ms + 3),
        rdW (m6.arr64 IW) (ms + 4)][j]?).map UInt64.toNat := by
    intro j hj
    rw [iwN_truncM (by omega)]
    simp only [iwN, nat?, iwA, aread_apply]
    rw [hget7 j (by simpa using hj)]
  have hold : ∀ k, 1 ≤ k → k ≤ 4 →
      iwN (truncM m) (ms.toNat + k) = some (rdW (m6.arr64 IW) (ms + UInt64.ofNat k)).toNat := by
    intro k hk1 hk4
    have hi : ms.toNat + k < iwTop m := by omega
    rw [iwN_truncM hi, ← iwN_grow hg06 hi]
    have hi6 : ms.toNat + k < (m6.arr64 IW).size := by have := hg06.iw; have := k6.stage.stage.iw.iw; omega
    have e : (ms + UInt64.ofNat k).toNat = ms.toNat + k := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]; omega
    simp only [iwN, nat?, iwA, aread_apply, rdW, e, Array.getElem?_eq_getElem hi6, Option.map_some,
      Option.getD_some]
  dsimp only [rmE.k_rec5]
  rw [hr7]
  refine RefE.ret rfl ⟨StageC.of_pstep k6.stage hS7 hA7 (ConRon.Bridge.Inductives.PStep.refl k6.stage.check.state),
    hg06.trans hg7, hA7, (c4.trans c5).trans k6.core, ?_, by simp only [List.headD_cons]; omega⟩
  simp only [List.headD_cons]
  refine decMSB_fresh hmsB (hg06.trans hg7) (cvpn := (r5.headD 0).toNat) ?_ (by simpa using hnew 0 (by omega))
    (fun k hk1 hk4 => ?_) hS7.iw.1
  · exact hcvR5.grow (OMono.decCVp _) (k6.grow.trans hg7)
  · rw [hold k hk1 hk4, hnew k (by omega)]
    rcases (show k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 by omega) with rfl | rfl | rfl | rfl <;> rfl

end rm

end L.Ind

end
