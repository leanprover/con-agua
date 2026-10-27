import ConAgua.Arena.DeclArmT
import ConAgua.Arena.IndT.Sum3
import ConAgua.Arena.RecGenSpec.Classes
import ConAgua.Arena.RecGenSpec.Rec3TmdWDecB
import ConAgua.Arena.IndInstallSpec.InstallSimCall
import ConAgua.Arena.RecGenSpec.ClassFeR

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
  (hV : ValProg p) (hOpf : OpfF p) (hLC : LvlCacheProg p)
  (hLT : p.lookup "lv_leq_top" = some lvLeqTop)
  (hApd : ApdF p) (hCrk : CrKeep p)

include hq henv hOpf hLC hLT in
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
    (opfSimRA (n := n + 1) hOpf hcqB hS hA) fun rx ox m1 a1 hQ => ?_
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
    · rw [ite_eq_right h] at heo; cases heo; exact absurd rfl he0
  rw [ite_eq_left hle] at heo
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
    · rw [heq, ite_eq_right h] at he0; exact absurd rfl he0
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
    (Sim.withRunC (fsortsW_okC hq henv hLC hLT n (by omega) m7 a7 isP lg rs nP xo xlw (ao + nP) (al - nP) nF xl1
      (args.drop nP.toNat) hC7 hA7 (by rw [decHL_grow hg67 hxlb5]; exact hxl5) (by have := hg67.1; omega)
      (by rw [decHL_grow hg7 hdb6]; exact hdrop6) (by have := hg7.1; omega) hrs (ConRon.Bridge.denoteL_ext hrsP hx07) hnf hxfvs7 hxpos))
    fun r9 sorts m8 a8 hQ => ?_
  obtain ⟨⟨hC8, hg8, hd8, hb8, hA8⟩, hr8⟩ := hQ
  obtain ⟨c8, -⟩ := ConRon.Bridge.Inductives.checkStructFieldSortsI_spec fe
    (ConRon.Bridge.CoreSpec.of_core rfl) henv (isP != 0) (lg != 0) (decI rs) rsP nP.toNat xl1
    (args.drop nP.toNat) xfvsP (xrestP.getAppArgs.drop nP.toNat) nF.toNat hxpos a7 a8 sorts hC7.check
    ⟨ConRon.Bridge.denoteL_ext hrsP hx07, hxfvs7, hidx7, ConRon.Bridge.denoteFEnv_mono hx07 hfe⟩ hr8
  have hp07 := (((p1.trans p2).trans p3).trans p6).trans p7
  exact Sim.ret ⟨hC8, (((hg1.trans hg15).trans hg67).trans hg8), rfl, by simpa using hd8,
    by simpa using hb8, hA8, (hp07.toCore hC.check).trans c8⟩

include hq henv in
/-- `check_struct_doms_at` under `StageC` as a `Sim` (an out-of-range count aborts in the model). -/
theorem sdSimC (k : Nat) (hk : k ≤ 2 ^ 62) (m : Mem) (a : AState) (off fo fl dO dl j : Word)
    (fvs doms : List EIdx) (fvsP domsP : List ConLeche.Expr) (hC : StageC dn vis fe env m a)
    (hA : AbsOK m)
    (hfvs : decHL m fo.toNat fl.toNat = some fvs) (hdoms : decHL m dO.toNat dl.toNat = some doms)
    (hfb : fo.toNat + fl.toNat ≤ iwTop m) (hdb : dO.toNat + dl.toNat ≤ iwTop m)
    (hoob : off.toNat + fl.toNat < 2 ^ 64)
    (hfP : Frontend.denoteEList a.store fvs = some fvsP)
    (hdP : Frontend.denoteEList a.store doms = some domsP)
    (hws : ∀ i, i < j.toNat → ∀ x y, fvsP[i]? = some x → domsP[i]? = some y →
      ConLeche.Expr.WScoped (off.toNat + i) x.fvarTypeD ∧ ConLeche.Expr.WScoped (off.toNat + i) y) :
    Sim (sdomsW (realCall p) k m vis off fo fl dO dl j) (checkStructDomsAt V fe off.toNat fvs doms j.toNat) a
      (fun _ _ m' a' => StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ AbsOK m') := by
  intro r m' e
  have e' := e
  rw [sdomsW_eq] at e'
  cases hd : domsW (realCall p) k m vis off fo fl dO dl j with
  | none => rw [hd] at e'; cases e'
  | some x =>
  obtain ⟨hjf, hjd⟩ := domsW_le hd
  have hS := hC.stage
  exact sdomsW_simC hq henv k hk m a off fo fl dO dl j fvs doms fvsP domsP hC hA hfvs hdoms
    (hS.lt64 hfb) (hS.lt64 hdb) hfb hdb hoob hjf hjd hfP hdP hws (r, m') e

include hq henv hV hOpf hLC hLT hApd hCrk in
/-- **`check_sum_ctor` under `StageC`** (twin side: con-ron's `checkSumCtor_spec`'s proof). -/
theorem ctorW_okC (n : Nat) (hn : n + 2 ≤ 2 ^ 62) (m : Mem)
    (a : AState) (vis0 T lo ll nP nIdx rs isP lg cvCw nF cvTaw : Word) (lps : List NIdx)
    (cvC cvTa : IConstantVal) (hC : StageC dn vis fe env m a) (hT : H T)
    (hlps : decHL m lo.toNat ll.toNat = some lps) (hlb : lo.toNat + ll.toNat ≤ iwTop m)
    (hcv : DecB (fun m => decCVp m cvCw.toNat) m cvC) (hta : DecB (fun m => decCVp m cvTaw.toNat) m cvTa)
    (hrs : H rs) (hni : nP.toNat + nIdx.toNat < 2 ^ 64) (hnf : nP.toNat + nF.toNat < 2 ^ 64)
    (hA : AbsOK m)
    {env₀ : ConLeche.Env} {TP : ConLeche.Name} {lpsP : List ConLeche.Name} {rsP : ConLeche.Level}
    {cvCP cvTaP : ConLeche.ConstantVal}
    (hTP : denoteN a.store.ns (decI T) = some TP)
    (hlpsP : Frontend.denoteNList a.store.ns lps = some lpsP)
    (hrsP : denoteL a.store.ls (decI rs) = some rsP)
    (hcvCP : Frontend.denoteCV a.store cvC = some cvCP)
    (hcvTaP : Frontend.denoteCV a.store cvTa = some cvTaP) (hws : ConLeche.Expr.WScoped 0 cvTaP.type)
    (hok₀ : ConRon.Bridge.Inductives.IFEnvOKS env₀ (fe.restrictTo vis0.toNat) a.store)
    (hfe : ConRon.Bridge.denoteFEnv a.store fe = some env) :
    Sim (ctorW (realCall p) n m vis0 vis T lo ll nP nIdx rs isP lg cvCw nF cvTaw)
      (checkSumCtor V (fe.restrictTo vis0.toNat) fe (decI T) lps nP.toNat nIdx.toNat (decI rs)
        (isP != 0) (lg != 0) cvC nF.toNat cvTa) a
      (fun r x m' a' => StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ r.headD 0 = cvCw ∧ x.1 = cvC ∧
        decHL m' (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat = some x.2 ∧
        (r.tail.headD 0).toNat + (r.tail.tail.headD 0).toNat ≤ iwTop m' ∧ AbsOK m' ∧
        ConRon.Bridge.CoreStep V env fe a a') := by
  have hS := hC.stage
  unfold ctorW
  rw [checkSumCtor_eq]
  -- `check_constant_val`
  obtain ⟨hcvx, -⟩ := rec3CVExt_of_trunc (show decCVp (truncM m) cvCw.toNat = some cvC from hcv)
  refine Sim.bindK (K := ctorK2 (realCall p) n vis0 vis T lo ll nP nIdx rs isP lg nF cvCw cvTaw) rfl
    (fun _ _ => rfl) (Sim.withFr (F := AbsOK) (Sim.withRunC
      (installSimCall (Q := fun _ _ m' a' => StageT dn vis fe m' a' ∧ IWGrow m m')
        (checkConstantVal_refinesT p hV hq hApd hCrk (n + 2) hn _ a dn fe vis cvCw cvC hC.stageT
          (rec2DecCV_erecP (DecB.get (OMono.decCVp _) hcv) hcvx) (rec3CVExt_lt hS hcvx)
          (denoteCV_lps hcvCP) hA.crMemo.crOK)
        fun _ _ h => ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩))
      fun _ _ e => checkConstantVal_absOK p hV hq hApd hCrk hn hC.stageT
        (rec2DecCV_erecP (DecB.get (OMono.decCVp _) hcv) hcvx) (rec3CVExt_lt hS hcvx)
        (denoteCV_lps hcvCP) hA.crMemo.crOK e hA) fun _ _ m1 a1 hQ => ?_
  obtain ⟨⟨⟨hT1, hg1⟩, hr1⟩, hA1⟩ := hQ
  have hS1 := hT1.stage
  obtain ⟨c1, F₁, hF₁⟩ := ConRon.Bridge.checkConstantVal_bridge rfl (ConRon.Bridge.CoreSpec.of_core rfl)
    hC.check henv hcvCP hr1
  have hC1 : StageC dn vis fe env m1 a1 := StageC.of_T hT1 c1.ok
  have hcA := ConRon.Bridge.denoteCV_ext hcvCP c1.ext
  have hwsA : ConLeche.Expr.WScoped 0 cvCP.type :=
    ConLeche.Expr.WScoped.of_not_hasFvar (ConLeche.checkConstantVal_typeWF hF₁).1
  rw [ctorK2_some]
  -- `strip_pis`
  obtain ⟨w1, hw1, hw1l, hw1d⟩ := sumTypeWord (hcv.stab (OMono.decCVp _) m1 hg1) hS1.2.2.2.2.1
  rw [hw1]
  have h2 := stripF_pis_ok dn vis fe (nP + nF) w1 hw1l
  rw [sum_toNat_add hnf, hw1d] at h2
  refine Sim.bindK (K := ctorK3 (realCall p) n vis0 vis T lo ll nP nIdx rs isP lg nF cvCw cvTaw) rfl
    (fun _ _ => rfl) (Sim.withFr (F := AbsOK) (Sim.withRunC (fun r m' e => h2 _ _ _ r e hS1))
      fun _ _ e => stripF_afr e hA1) fun r2 o2 m2 a2 hQ => ?_
  obtain ⟨⟨⟨hS2, hg2, hdec2⟩, hr2⟩, hA2⟩ := hQ
  obtain ⟨ha2, ho2⟩ := ConRon.Bridge.Inductives.stripPis_pstep hC1.check.state
    (ConRon.Bridge.denoteCV_type hcA) hr2
  rw [ha2] at hS2 ⊢
  have hC2 : StageC dn vis fe env m2 a1 := hC1.of_pstep hS2 hA2 (PStep.refl hC1.check.state)
  by_cases h20 : r2.headD 0 = 0
  · rw [ctorK3_no (h := h20)]; exact Sim.of_none
  rw [ctorK3_yes (h := h20)]
  cases o2 with
  | none => exact absurd hdec2 h20
  | some le =>
  obtain ⟨sl, cb⟩ := le
  obtain ⟨cxs, cbodyP, -, -, hcbP⟩ := ConRon.Bridge.Inductives.denoteBP_some ho2
  obtain ⟨-, -, hcb, hcbd⟩ := hdec2
  rw [drop3_eq] at hcb hcbd
  refine Sim.bind_twin (x := (sl, cb)) (a₁ := a1) rfl ?_
  subst hcbd
  have hg02 := hg1.trans hg2
  have hlps2 : decHL m2 lo.toNat ll.toNat = some lps := by rw [decHL_grow hg02 hlb]; exact hlps
  -- `struct_ctor_resid_ok`
  refine Sim.bindK (K := ctorK4 (realCall p) n vis0 vis T lo ll nP nIdx rs isP lg nF cvCw cvTaw) rfl
    (fun _ _ => rfl) (Sim.withFr (F := AbsOK) (Sim.withRunC (fun r m' e => by
      obtain ⟨x, a', h1, h2⟩ := srW_ok dn vis fe (n + 2) m2 m' a1 T lo ll nP nF nIdx _ r lps e hS2 hT hcb
        hlps2 (hS2.lt64 (by have := hg02.1; omega)) (by have := hg02.1; omega) (by omega) hni
      exact ⟨x, a', h1, h2⟩)) fun _ _ e => srW_afr _ _ _ _ _ _ _ _ _ _ _ e hA2) fun r3 b3 m3 a3 hQ => ?_
  obtain ⟨⟨⟨hS3, hg3, hb3, -⟩, hr3⟩, hA3⟩ := hQ
  have hx01 := c1.ext
  obtain ⟨p3, -⟩ := ConRon.Bridge.Inductives.structCtorResidOk_spec (decI T) TP lps lpsP nP.toNat
    nF.toNat nIdx.toNat _ cbodyP a1 a3 b3 hC2.check.state
    ⟨ConRon.Bridge.denoteN_ext hTP hx01, ConRon.Bridge.denoteNListE_ext hx01 _ _ hlpsP, hcbP⟩ hr3
  have hC3 : StageC dn vis fe env m3 a3 := hC2.of_pstep hS3 hA3 p3
  by_cases h30 : r3.headD 0 = 0
  · rw [ctorK4_no (h := h30)]; exact Sim.of_none
  rw [ctorK4_yes (h := h30)]
  have hb3' : b3 = true := by rw [← hb3]; simpa using h30
  subst hb3'
  simp only [ite_true]
  have hg03 := hg02.trans hg3
  -- the constructor's opened telescope
  obtain ⟨w3, hw3, hw3l, hw3d⟩ := sumTypeWord (hcv.stab (OMono.decCVp _) m3 hg03) hS3.2.2.2.2.1
  rw [hw3]
  have h4 := opfSimRA (n := n + 2) (k := nP) (i := 0) hOpf hw3l hS3 hA3
  rw [hw3d, show (0 : Word).toNat = 0 from rfl] at h4
  refine Sim.bindK (K := ctorK5 (realCall p) n vis0 vis T lo ll nP nIdx rs isP lg nF cvCw cvTaw) rfl
    (fun _ _ => rfl) h4 fun r4 o4 m4 a4 hQ => ?_
  obtain ⟨⟨⟨hS4, hg4, hdec4⟩, hr4⟩, hA4⟩ := hQ
  obtain ⟨p4, ho4⟩ := ConRon.Bridge.Inductives.openPisAtFvarsF_run hC3.check.state
    (ConRon.Bridge.denote_ext (ConRon.Bridge.denoteCV_type hcA) p3.ext) hr4
  have hC4 : StageC dn vis fe env m4 a4 := hC3.of_pstep hS4 hA4 p4
  by_cases h40 : r4.headD 0 = 0
  · rw [ctorK5_no (h := h40)]; exact Sim.of_none
  rw [ctorK5_yes (h := h40)]
  cases o4 with
  | none => exact absurd hdec4 h40
  | some le =>
  obtain ⟨cl, cb4⟩ := le
  obtain ⟨cfvsP, crestP, hcq, hcfvs, hcrest⟩ := ConRon.Bridge.Inductives.denoteOpen_some_inv ho4
  obtain ⟨-, ⟨hcl, hclb⟩, hcqB, hcqBd⟩ := hdec4
  rw [sumGetD1, sumGetD2] at hcl hclb
  rw [drop3_eq] at hcqB hcqBd
  refine Sim.bind_twin (x := (cl, cb4)) (a₁ := a4) rfl ?_
  subst hcqBd
  have hg04 := hg03.trans hg4
  -- the type former's opened telescope
  obtain ⟨w5, hw5, hw5l, hw5d⟩ := sumTypeWord (hta.stab (OMono.decCVp _) m4 hg04) hS4.2.2.2.2.1
  rw [hw5]
  have h5 := opfSimRA (n := n + 2) (k := nP) (i := 0) hOpf hw5l hS4 hA4
  rw [hw5d, show (0 : Word).toNat = 0 from rfl] at h5
  have hx04 := hx01.trans (p3.ext.trans p4.ext)
  refine Sim.bindK (K := ctorK6 (realCall p) n vis0 vis T lo ll nP nIdx rs isP lg nF cvCw _ _ _) rfl
    (fun _ _ => rfl) h5 fun r5 o5 m5 a5 hQ => ?_
  obtain ⟨⟨⟨hS5, hg5, hdec5⟩, hr5⟩, hA5⟩ := hQ
  obtain ⟨p5, ho5⟩ := ConRon.Bridge.Inductives.openPisAtFvarsF_run hC4.check.state
    (ConRon.Bridge.denote_ext (ConRon.Bridge.denoteCV_type hcvTaP) hx04) hr5
  have hC5 : StageC dn vis fe env m5 a5 := hC4.of_pstep hS5 hA5 p5
  by_cases h50 : r5.headD 0 = 0
  · rw [ctorK6_no (h := h50)]; exact Sim.of_none
  rw [ctorK6_yes (h := h50)]
  cases o5 with
  | none => exact absurd hdec5 h50
  | some le =>
  obtain ⟨tl, tb⟩ := le
  obtain ⟨tfvsP, trestP, htq, htfvs, -⟩ := ConRon.Bridge.Inductives.denoteOpen_some_inv ho5
  obtain ⟨-, ⟨htl, htlb⟩, -, -⟩ := hdec5
  rw [sumGetD1, sumGetD2] at htl htlb
  refine Sim.bind_twin (x := (tl, tb)) (a₁ := a5) rfl ?_
  -- `fvar_type_ds`
  refine Sim.bindK (K := ctorK7 (realCall p) n vis0 vis T lo ll nP nIdx rs isP lg nF cvCw _ _ _) rfl
    (fun _ _ => rfl) (Sim.withFr (F := AbsOK) (Sim.withRunC
      (sumSim_of_relW (ftdsF_ok dn vis fe _ _ tl) ⟨hS5, htl, fun _ => htlb⟩))
      fun _ _ e => ftdsF_afr e hA5)
    fun r6 tdoms m6 a6 hQ => ?_
  obtain ⟨⟨⟨hS6, hg6, htd, htdb⟩, hr6⟩, hA6⟩ := hQ
  obtain ⟨p6, hdoms⟩ := ConRon.Bridge.Inductives.fvarTypeDs_run tl tfvsP hC5.check.state htfvs hr6
  have hC6 : StageC dn vis fe env m6 a6 := hC5.of_pstep hS6 hA6 p6
  rw [sumGetD0, sumGetD1] at htd htdb
  rw [ctorK7_some]
  -- `check_struct_doms_at`
  have hg56 := hg5.trans hg6
  have hcl6 : decHL m6 (r4.tail.headD 0).toNat (r4.tail.tail.headD 0).toNat = some cl := by
    rw [decHL_grow hg56 hclb]; exact hcl
  have hclb6 : (r4.tail.headD 0).toNat + (r4.tail.tail.headD 0).toNat ≤ iwTop m6 := by
    have := hg56.1; omega
  have hx46 := p5.ext.trans p6.ext
  have hcfvs6 := ConRon.Bridge.denoteEList_ext hx46 _ _ hcfvs
  have hws7 : ∀ i, i < nP.toNat → ∀ x y, cfvsP[i]? = some x →
      (tfvsP.map ConLeche.Expr.fvarTypeD)[i]? = some y →
      ConLeche.Expr.WScoped ((0 : Word).toNat + i) x.fvarTypeD ∧
        ConLeche.Expr.WScoped ((0 : Word).toNat + i) y := by
    intro i _ x y hx hy
    refine ⟨ConRon.Bridge.Inductives.openers_typeD_WScoped hcq hwsA i x hx, ?_⟩
    rw [List.getElem?_map] at hy
    obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp hy
    exact ConRon.Bridge.Inductives.openers_typeD_WScoped htq hws i z hz
  refine Sim.bindK (K := ctorK8 (realCall p) n vis0 vis T lo ll nP nIdx rs isP lg nF cvCw _ _ _) rfl
    (fun _ _ => rfl) (Sim.withRunC (sdSimC hq henv (n + 2) hn m6 a6 0 _ _ _ _ nP cl tdoms cfvsP
      (tfvsP.map ConLeche.Expr.fvarTypeD) hC6 hA6 hcl6 htd hclb6 htdb
      (by simp only [UInt64.toNat_zero, Nat.zero_add]; have := hC6.stage.lt64 hclb6; omega)
      hcfvs6 hdoms hws7))
    fun _ _ m7 a7 hQ => ?_
  obtain ⟨⟨hC7, hg7, hA7⟩, hr7⟩ := hQ
  have hx06 := hx04.trans hx46
  obtain ⟨c7, -⟩ := ConRon.Bridge.Inductives.checkStructDomsAt_spec fe (ConRon.Bridge.CoreSpec.of_core rfl)
    henv 0 cl tdoms cfvsP (tfvsP.map ConLeche.Expr.fvarTypeD) nP.toNat
    (fun i hi x y hx hy => hws7 i hi x y hx hy) a6 a7 _ hC6.check
    ⟨hcfvs6, hdoms, ConRon.Bridge.denoteFEnv_mono hx06 hfe⟩ hr7
  rw [ctorK8_some]
  -- the tail
  have hg06 := (hg04.trans hg56)
  have hx07 := hx06.trans c7.ext
  have hwsc : ConLeche.Expr.WScoped nP.toNat crestP := by
    have := (ConLeche.openPisAtFvars_WScoped _ _ _ hcq hwsA).2
    simpa using this
  refine sumSim_map (K := ctorK9 cvCw) rfl (fun _ _ => rfl)
    (ctlW_okC hq henv hOpf hLC hLT n (by omega) m7 a7 vis0 T lo ll nP nIdx rs isP lg nF _ _ _ lps cl cvC hC7 hT
      (by rw [decHL_grow (hg06.trans hg7) hlb]; exact hlps) (by have := (hg06.trans hg7).1; omega)
      (by rw [decHL_grow hg7 hclb6]; exact hcl6) (by have := hg7.1; omega) hcqB hrs hni hnf hA7
      (ConRon.Bridge.denoteN_ext hTP hx07) (ConRon.Bridge.denoteNListE_ext hx07 _ _ hlpsP)
      (ConRon.Bridge.denoteL_ext hrsP hx07)
      (ConRon.Bridge.denote_ext hcrest (hx46.trans c7.ext)) hwsc
      (hok₀.mono hx07) (ConRon.Bridge.denoteFEnv_mono hx07 hfe))
    fun r8 x m8 a8 hQ => ?_
  obtain ⟨hC8, hg8, hx1, hd8, hb8, hA8, c8⟩ := hQ
  have hp16 := ((p3.trans p4).trans p5).trans p6
  exact ⟨hC8, ((hg06.trans hg7).trans hg8), rfl, hx1, by simpa using hd8, by simpa using hb8, hA8,
    ((c1.trans (hp16.toCore c1.ok)).trans c7).trans c8⟩

include hq henv hV hOpf hLC hLT hApd hCrk in
/-- **`check_sum_ctor` refines `checkSumCtor .verified`** under `StageC` (the knot's core calls;
the inputs' denotations as con-ron's `checkSumCtor_spec` asks), the pre-block environment the
restriction of `fe` to the view `vis0`. Returns `cvC` itself and the field sorts as a fresh `IW`
slice. -/
@[refines ConRon.Arena.checkSumCtor]
theorem checkSumCtor_refinesC (hP : SumProg p) (n : Nat) (hn : n + 2 ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (vis0 T lo ll nP nIdx rs isP lg cvCw nF cvTaw : Word) (lps : List NIdx)
    (cvC cvTa : IConstantVal) (hC : StageC dn vis fe env s₀.mem a₀) (hT : H T)
    (hlps : decHL s₀.mem lo.toNat ll.toNat = some lps) (hlb : lo.toNat + ll.toNat ≤ iwTop s₀.mem)
    (hcv : DecB (fun m => decCVp m cvCw.toNat) s₀.mem cvC)
    (hta : DecB (fun m => decCVp m cvTaw.toNat) s₀.mem cvTa)
    (hrs : H rs) (hni : nP.toNat + nIdx.toNat < 2 ^ 64) (hnf : nP.toNat + nF.toNat < 2 ^ 64)
    (hA : AbsOK s₀.mem)
    {env₀ : ConLeche.Env} {TP : ConLeche.Name} {lpsP : List ConLeche.Name} {rsP : ConLeche.Level}
    {cvCP cvTaP : ConLeche.ConstantVal}
    (hTP : denoteN a₀.store.ns (decI T) = some TP)
    (hlpsP : Frontend.denoteNList a₀.store.ns lps = some lpsP)
    (hrsP : denoteL a₀.store.ls (decI rs) = some rsP)
    (hcvCP : Frontend.denoteCV a₀.store cvC = some cvCP)
    (hcvTaP : Frontend.denoteCV a₀.store cvTa = some cvTaP) (hws : ConLeche.Expr.WScoped 0 cvTaP.type)
    (hok₀ : ConRon.Bridge.Inductives.IFEnvOKS env₀ (fe.restrictTo vis0.toNat) a₀.store)
    (hfe : ConRon.Bridge.denoteFEnv a₀.store fe = some env) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 3)) "check_sum_ctor"
      [vis0, vis, T, lo, ll, nP, nIdx, rs, isP, lg, cvCw, nF, cvTaw]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (checkSumCtor V (fe.restrictTo vis0.toNat) fe (decI T) lps nP.toNat nIdx.toNat (decI rs)
        (isP != 0) (lg != 0) cvC nF.toNat cvTa) a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (checkSumCtor V (fe.restrictTo vis0.toNat) fe (decI T) lps
        nP.toNat nIdx.toNat (decI rs) (isP != 0) (lg != 0) cvC nF.toNat cvTa) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ r.headD 0 = cvCw ∧
      (AM.res (checkSumCtor V (fe.restrictTo vis0.toNat) fe (decI T) lps nP.toNat nIdx.toNat (decI rs)
        (isP != 0) (lg != 0) cvC nF.toNat cvTa) a₀).1 = cvC ∧
      decHL s'.mem (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat =
        some (AM.res (checkSumCtor V (fe.restrictTo vis0.toNat) fe (decI T) lps nP.toNat nIdx.toNat
          (decI rs) (isP != 0) (lg != 0) cvC nF.toNat cvTa) a₀).2 ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (ctorW_spec p hP (realCall p) (realCall_spec p) n s₀ vis0 vis T lo ll nP nIdx rs
    isP lg cvCw nF cvTaw) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨hok, hC', hg', h0, h1, hd, -, hA', -⟩ := (ctorW_okC hq henv hV hOpf hLC hLT hApd hCrk n hn _ a₀ vis0 T lo ll nP nIdx rs
    isP lg cvCw nF cvTaw lps cvC cvTa hC hT hlps hlb hcv hta hrs hni hnf hA hTP hlpsP hrsP hcvCP hcvTaP
    hws hok₀ hfe).run hm
  exact ⟨hl, hok, hC', hg', h0, h1, hd, hA'⟩

end sims

end L.Ind
