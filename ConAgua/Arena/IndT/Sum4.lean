import ConAgua.Arena.IndT.Sum3
import ConAgua.Arena.IndT.Install2
import ConRon.Bridge.Inductives.SumInstall

/-!
# `checkSumCtor` under `StageC` (lane `indstaget`)

`check_sum_ctor`'s model at `realCall p`, from `StageC` and con-ron's preconditions of
`checkSumCtor_spec` (the family's name and level parameters, the result sort, the two constant
values and both environments denote; the pre-block environment's `IFEnvOKS`), its twin side
transcribed from that spec's proof. The tail (`cscTailT`, `ctlW_okC`): the fields opened past the
parameters (`openPisAtFvarsF_run`), the family head (`paramLevels_spec`, `internConstE_run`), the
residual's spine (`getAppFn_run`, `getAppArgs_run`), the resolution tests (`fieldDomsResolve_spec`,
`idxArgsResolve_spec`), the field sorts (`fsortsW_okC`, con-ron's `checkStructFieldSortsI_spec` on
its run for the `CoreStep`).
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq henv in
/-- **`check_sum_ctor_tail` under `StageC`** (twin side: the tail of con-ron's
`checkSumCtor_spec`'s proof). -/
theorem ctlW_okC (n : Nat) (hn : n + 1 ≤ 2 ^ 62) (m : Mem)
    (a : AState) (vis0 T lo ll nP nIdx rs isP lg nF cqO cqL cqB : Word) (lps : List NIdx)
    (cq1 : List EIdx) (cvCa : IConstantVal) (hC : StageC dn vis fe env m a) (hT : H T)
    (hlps : decHL m lo.toNat ll.toNat = some lps) (hlb : lo.toNat + ll.toNat ≤ iwTop m)
    (hcq : decHL m cqO.toNat cqL.toNat = some cq1) (hcqb : cqO.toNat + cqL.toNat ≤ iwTop m)
    (hcqB : H cqB) (hrs : H rs) (hni : nP.toNat + nIdx.toNat < 2 ^ 64)
    (hnf : nP.toNat + nF.toNat < 2 ^ 64) (hA : AbsOK m)
    {env₀ : ConLeche.Env} {TP : ConLeche.Name} {lpsP : List ConLeche.Name} {rsP : ConLeche.Level}
    {crestP : ConLeche.Expr}
    (hTP : denoteN a.store.ns (decI T) = some TP)
    (hlpsP : Frontend.denoteNList a.store.ns lps = some lpsP)
    (hrsP : denoteL a.store.ls (decI rs) = some rsP)
    (hcqBP : denoteE a.store (decI cqB) = some crestP) (hwsc : ConLeche.Expr.WScoped nP.toNat crestP)
    (hok₀ : ConRon.Bridge.Inductives.IFEnvOKS env₀ (fe.restrictTo vis0.toNat) a.store)
    (hfe : ConRon.Bridge.denoteFEnv a.store fe = some env) :
    Sim (ctlW (realCall p) n m vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL cqB)
      (cscTailT (fe.restrictTo vis0.toNat) fe (decI T) lps nP.toNat nIdx.toNat (decI rs) (isP != 0)
        (lg != 0) cvCa nF.toNat (cq1, decI cqB)) a
      (fun r x m' a' => StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ x.1 = cvCa ∧
        decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some x.2 ∧
        (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ AbsOK m' ∧
        ConRon.Bridge.CoreStep V env fe a a') := by
  have hS := hC.stage
  have hv := hS.1.env.vis
  unfold ctlW cscTailT
  refine Sim.bindK (K := ctlK1 (realCall p) n vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL) rfl
    (fun _ _ => rfl)
    (Sim.withFr (F := AbsOK) (Sim.withRunC
      (sumSim_of_relAM (openPisAtFvarsF_spec dn vis fe nF cqB nP hcqB) hS))
      fun _ _ e => AbsOK.stub (by decide) hA e) fun rx ox m1 a1 hQ => ?_
  obtain ⟨⟨⟨hS1, hg1, hdec1⟩, hr1⟩, hA1⟩ := hQ
  obtain ⟨p1, ho1⟩ := ConRon.Bridge.Inductives.openPisAtFvarsF_run hC.check.state hcqBP hr1
  have hC1 : StageC dn vis fe env m1 a1 := hC.of_pstep hS1 hA1 p1
  by_cases h0 : rx.headD 0 = 0
  · rw [ctlK1_no (realCall p) n m1 vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL rx h0]; exact Sim.of_none
  rw [ctlK1_yes (realCall p) n m1 vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL rx h0]
  cases ox with
  | none => exact absurd hdec1 h0
  | some xq =>
  obtain ⟨xl1, xb⟩ := xq
  obtain ⟨xfvsP, xrestP, hxq, hxfvs, hxrest⟩ := ConRon.Bridge.Inductives.denoteOpen_some_inv ho1
  obtain ⟨-, ⟨hxl, hxlb⟩, hxb, hxbd⟩ := hdec1
  rw [sumGetD1, sumGetD2] at hxl hxlb
  rw [drop3_eq] at hxb hxbd
  refine Sim.bind_twin (x := (xl1, xb)) (a₁ := a1) rfl ?_
  generalize hxo : rx.tail.headD 0 = xo at hxl hxlb
  generalize hxlw : rx.tail.tail.headD 0 = xlw at hxl hxlb
  generalize hxbw : rx.tail.tail.tail.headD 0 = xbw at hxb hxbd
  -- `param_levels`
  refine Sim.bindK (K := ctlK2 (realCall p) n vis0 vis T nP nIdx rs isP lg nF cqO cqL xo xlw xbw) rfl
    (fun _ _ => rfl) (Sim.withFr (F := AbsOK) (Sim.withRunC (plSim (n + 1) m1 a1 lo ll lps hS1
      (by rw [decHL_grow hg1 hlb]; exact hlps) (by have := hg1.1; omega))) fun _ _ e => plW_afr e hA1)
    fun ru us m2 a2 hQ => ?_
  obtain ⟨⟨⟨hS2, hg2, hu, hus⟩, hr2⟩, hA2⟩ := hQ
  obtain ⟨p2, husP⟩ := ConRon.Bridge.Inductives.paramLevels_spec lps lpsP a1 a2 us hC1.check.state
    (ConRon.Bridge.denoteNListE_ext p1.ext _ _ hlpsP) hr2
  have hC2 : StageC dn vis fe env m2 a2 := hC1.of_pstep hS2 hA2 p2
  subst hus
  rw [ctlK2_some]
  -- `intern_const`
  refine Sim.bindK (K := ctlK3 (realCall p) n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xlw xbw) rfl
    (fun _ _ => rfl) (Sim.withFr (F := AbsOK) (Sim.withRunC (ceSim m2 a2 T (ru.headD 0) hS2 hT hu))
      fun _ _ e => ceinternW_afr e hA2) fun hd e m3 a3 hQ => ?_
  obtain ⟨⟨⟨he, hS3, hg3⟩, hr3⟩, hA3⟩ := hQ
  obtain ⟨p3, hhd⟩ := ConRon.Bridge.Inductives.internConstE_run hC2.check.state
    (ConRon.Bridge.denoteN_ext hTP (p1.ext.trans p2.ext)) husP hr3
  have hC3 : StageC dn vis fe env m3 a3 := hC2.of_pstep hS3 hA3 p3
  subst he
  by_cases hbig : 4294967296 ≤ hd
  · rw [ctlK3_big (realCall p) n m3 vis0 vis nP nIdx rs isP lg nF cqO cqL xo xlw xbw hd hbig]
    exact Sim.of_none
  rw [ctlK3_ok (realCall p) n m3 vis0 vis nP nIdx rs isP lg nF cqO cqL xo xlw xbw hd hbig]
  have hd32 : H hd := by have : ¬ (4294967296 : Nat) ≤ hd.toNat := hbig; show hd.toNat < 2 ^ 32; omega
  have hx13 := p2.ext.trans p3.ext
  have hxr3 : denoteE a3.store (decI xbw) = some xrestP := by
    rw [hxbd]; exact ConRon.Bridge.denote_ext hxrest hx13
  -- `get_app_fn_f`
  have h4 := gafF_ok dn vis fe CWF xbw hxb
  rw [CWF_eq, hxbd] at h4
  refine Sim.bindK (K := ctlK4 (realCall p) n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xlw xbw hd) rfl
    (fun _ _ => rfl) (Sim.withFr (F := AbsOK) (Sim.withRunC (sumSim_of_relW h4 hS3))
      fun _ _ e => (show AFr _ _ from AFr.of_frame (gafF_frame e)) hA3) fun rf xfn m4 a4 hQ => ?_
  obtain ⟨⟨⟨hS4, hg4, hf32, hfd⟩, hr4⟩, hA4⟩ := hQ
  rw [← hxbd] at hr4
  obtain ⟨ha4, -⟩ := ConRon.Bridge.Inductives.getAppFn_run hC3.check.state hxr3 hr4
  rw [ha4] at hS4 ⊢
  have hC4 : StageC dn vis fe env m4 a3 := hC3.of_pstep hS4 hA4 (PStep.refl hC3.check.state)
  rw [ctlK4_some]
  -- `get_app_args_f`
  have h5 := gaaF_ok dn vis fe CWF xbw hxb
  rw [CWF_eq, hxbd] at h5
  refine Sim.bindK (K := ctlK5 (realCall p) n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xlw hd (rf.headD 0))
    rfl (fun _ _ => rfl) (Sim.withFr (F := AbsOK) (Sim.withRunC (sumSim_of_relW h5 hS4))
      fun _ _ e => gaaF_afr e hA4) fun ra args m5 a5 hQ => ?_
  obtain ⟨⟨⟨hS5, hg5, hargs, hab⟩, hr5⟩, hA5⟩ := hQ
  rw [← hxbd] at hr5
  obtain ⟨ha5, hargsP⟩ := ConRon.Bridge.Inductives.getAppArgs_run hC4.check.state hxr3 hr5
  rw [ha5] at hS5 ⊢
  have hC5 : StageC dn vis fe env m5 a3 := hC4.of_pstep hS5 hA5 (PStep.refl hC4.check.state)
  rw [sumGetD0, sumGetD1] at hargs hab
  rw [ctlK5_some]
  subst hfd
  generalize hao : ra.headD 0 = ao at hargs hab
  generalize hal : ra.tail.headD 0 = al at hargs hab
  have hlen : args.length = al.toNat := decHL_length m5 hargs
  have hg15 := ((hg2.trans hg3).trans hg4).trans hg5
  have hg05 := hg1.trans hg15
  cases heo : (if nP ≤ al then eqW (n + 1) m5 ao nP cqO cqL else some 0) with
  | none => exact Sim.of_none
  | some e =>
  by_cases hfail : rf.headD 0 ≠ hd ∨ al ≠ nP + nIdx ∨ e = 0
  · rw [ctlK6_no (realCall p) n m5 vis0 vis nP nIdx rs isP lg nF xo xlw hd (rf.headD 0) ao al e hfail]
    exact Sim.of_none
  rw [ctlK6_yes (realCall p) n m5 vis0 vis nP nIdx rs isP lg nF xo xlw hd (rf.headD 0) ao al e hfail]
  have hfn : rf.headD 0 = hd := by
    by_cases h : rf.headD 0 = hd
    · exact h
    · exact absurd (Or.inl h) hfail
  have hln : al = nP + nIdx := by
    by_cases h : al = nP + nIdx
    · exact h
    · exact absurd (Or.inr (Or.inl h)) hfail
  have he0 : e ≠ 0 := fun h => hfail (Or.inr (Or.inr h))
  have hle : nP ≤ al := by
    by_cases h : nP ≤ al
    · exact h
    · rw [if_neg h] at heo; cases heo; exact absurd rfl he0
  rw [if_pos hle] at heo
  have hle' : nP.toNat ≤ al.toNat := UInt64.le_iff_toNat_le.mp hle
  have hcq5 : decHL m5 cqO.toNat cqL.toNat = some cq1 := by rw [decHL_grow hg05 hcqb]; exact hcq
  have htk := decHL_take hargs nP.toNat hle'
  obtain ⟨ws1, hs1, hm1, hb1⟩ := slR_of_decHL m5 _ _ _ htk (hS5.lt64 (by omega))
  obtain ⟨ws2, hs2, hm2, hb2⟩ := slR_of_decHL m5 _ _ _ hcq5 (hS5.lt64 (by have := hg05.1; omega))
  simp only [UInt64.ofNat_toNat] at hs1 hs2
  have heq := eqW_ok (n + 1) m5 _ _ _ _ e ws1 ws2 hs1 hs2 heo
  have hws : ws1 = ws2 := by
    by_cases h : ws1 = ws2
    · exact h
    · rw [heq, if_neg h] at he0; exact absurd rfl he0
  have htake : args.take nP.toNat = cq1 := by rw [hm1, hm2, hws]
  have hc : (decI (rf.headD 0) == (decI hd : EIdx) && args.take nP.toNat == cq1 &&
      args.length == nP.toNat + nIdx.toNat) = true := by
    rw [hfn, htake, hlen, hln, sum_toNat_add hni]; simp
  simp only [hc, ite_true]
  have hT5 : ao.toNat + al.toNat < 2 ^ 64 := hS5.lt64 hab
  have hxl5 : decHL m5 xo.toNat xlw.toNat = some xl1 := by rw [decHL_grow hg15 hxlb]; exact hxl
  have hxlb5 : xo.toNat + xlw.toNat ≤ iwTop m5 := by have := hg15.1; omega
  have hx03 := p1.ext.trans hx13
  have hread : ConRon.Bridge.Inductives.ReadOK env₀ (fe.restrictTo vis0.toNat) a3 :=
    ⟨hC5.check.state, hC5.check.pins, hok₀.mono hx03 a3 rfl⟩
  -- `field_doms_resolve`, at the pre-block view
  refine Sim.bindK (K := ctlK7 (realCall p) n vis0 vis isP lg rs nP nF xo xlw ao al) rfl (fun _ _ => rfl)
    (Sim.withRunC (fdrSim (n + 1) m5 a3 xo xlw xl1 (hS5.restrict vis0) hxl5 hxlb5 hA5))
    fun r1 b1 m6 a6 hQ => ?_
  obtain ⟨hQ, hr6⟩ := hQ
  obtain ⟨hS6, hg6, hb1⟩ := sumKeep_restrict hv hQ.1
  have hA6 := hQ.2
  obtain ⟨p6, -⟩ := ConRon.Bridge.Inductives.fieldDomsResolve_spec xl1 xfvsP hread
    (ConRon.Bridge.denoteEList_ext hx13 _ _ hxfvs) hr6
  have hC6 : StageC dn vis fe env m6 a6 := hC5.of_pstep hS6 hA6 p6
  by_cases h1 : r1.headD 0 = 0
  · rw [ctlK7_no (h := h1)]; exact Sim.of_none
  rw [ctlK7_yes (h := h1)]
  have hb1' : b1 = true := by rw [← hb1]; simpa using h1
  subst hb1'
  simp only [ite_true]
  -- `idx_args_resolve`
  have hao : (ao + nP).toNat = ao.toNat + nP.toNat := sum_toNat_add (by omega)
  have halp : (al - nP).toNat = al.toNat - nP.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ hle]
  have hdrop6 : decHL m6 (ao + nP).toNat (al - nP).toNat = some (args.drop nP.toNat) := by
    rw [hao, halp]
    exact decHL_drop nP.toNat (by rw [decHL_grow hg6 hab]; exact hargs) hle'
  have hdb6 : (ao + nP).toNat + (al - nP).toNat ≤ iwTop m6 := by
    rw [hao, halp]; have := hg6.1; omega
  refine Sim.bindK (K := ctlK8 (realCall p) n vis isP lg rs nP nF xo xlw ao al) rfl (fun _ _ => rfl)
    (Sim.withRunC (iarSim (n + 1) m6 a6 (ao + nP) (al - nP) (args.drop nP.toNat) (hS6.restrict vis0)
      hdrop6 hdb6 hA6))
    fun r2 b2 m7 a7 hQ => ?_
  obtain ⟨hQ, hr7⟩ := hQ
  obtain ⟨hS7, hg7, hb2⟩ := sumKeep_restrict hv hQ.1
  have hA7 := hQ.2
  have hargs6 := ConRon.Bridge.denoteEList_ext p6.ext _ _ hargsP
  obtain ⟨p7, -⟩ := ConRon.Bridge.Inductives.idxArgsResolve_spec (args.drop nP.toNat)
    (xrestP.getAppArgs.drop nP.toNat) (hread.mono p6.ok p6.ext p6.pins)
    (ConRon.Bridge.Inductives.denoteEList_drop hargs6 nP.toNat) hr7
  have hC7 : StageC dn vis fe env m7 a7 := hC6.of_pstep hS7 hA7 p7
  by_cases h2 : r2.headD 0 = 0
  · rw [ctlK8_no (h := h2)]; exact Sim.of_none
  rw [ctlK8_yes (h := h2)]
  have hb2' : b2 = true := by rw [← hb2]; simpa using h2
  subst hb2'
  simp only [ite_true]
  -- the field sorts
  have hg67 := hg6.trans hg7
  have hx37 := p6.ext.trans p7.ext
  have hx07 := hx03.trans hx37
  have hxfvs7 := ConRon.Bridge.denoteEList_ext (hx13.trans hx37) _ _ hxfvs
  have hidx7 := ConRon.Bridge.Inductives.denoteEList_drop
    (ConRon.Bridge.denoteEList_ext hx37 _ _ hargsP) nP.toNat
  have hxpos : ∀ i, i < nF.toNat → ∀ x, xfvsP[i]? = some x →
      ConLeche.Expr.WScoped (nP.toNat + i) x.fvarTypeD :=
    fun i _ x hx => ConRon.Bridge.Inductives.openers_typeD_WScoped hxq hwsc i x hx
  refine Sim.bindK (K := ctlK9) rfl (fun _ _ => rfl)
    (Sim.withRunC (fsortsW_okC hq henv n (by omega) m7 a7 isP lg rs nP xo xlw (ao + nP) (al - nP) nF xl1
      (args.drop nP.toNat) hC7 hA7 (by rw [decHL_grow hg67 hxlb5]; exact hxl5) (by have := hg67.1; omega)
      (by rw [decHL_grow hg7 hdb6]; exact hdrop6) (by have := hg7.1; omega) hrs hnf hxfvs7 hxpos))
    fun r9 sorts m8 a8 hQ => ?_
  obtain ⟨⟨hC8, hg8, hd8, hb8, hA8⟩, hr8⟩ := hQ
  obtain ⟨c8, -⟩ := ConRon.Bridge.Inductives.checkStructFieldSortsI_spec fe
    (ConRon.Bridge.CoreSpec.of_core rfl) henv (isP != 0) (lg != 0) (decI rs) rsP nP.toNat xl1
    (args.drop nP.toNat) xfvsP (xrestP.getAppArgs.drop nP.toNat) nF.toNat hxpos a7 a8 sorts hC7.check
    ⟨ConRon.Bridge.denoteL_ext hrsP hx07, hxfvs7, hidx7, ConRon.Bridge.denoteFEnv_mono hx07 hfe⟩ hr8
  have hp07 := (((p1.trans p2).trans p3).trans p6).trans p7
  exact Sim.ret ⟨hC8, (((hg1.trans hg15).trans hg67).trans hg8), rfl, by simpa using hd8,
    by simpa using hb8, hA8, (hp07.toCore hC.check).trans c8⟩

end sims

end L.Ind
