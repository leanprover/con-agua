import ConAgua.Arena.IndT.Install1
import ConAgua.Arena.IndSumSpec.CheckSumCtor
import ConAgua.Arena.IndSumSpec.SumRules
import ConRon.Bridge.Inductives.SumInstall
import ConRon.Bridge.Inductives.StructParts

/-!
# The sum family's walk steps

The registered steps of `check_sum_ctor`'s callees outside the verdict closure, for the lockstep
walk of `RefWalk.lean` (docs/design/refgen.md): each is the callee's `Sim` under the package
`InsAt` (`Install1.lean`: `StageC`, `AbsOK`, the `IW` growth, the twin's core step), its result
decoded against the twin's and denoting con-leche's. They collect what each call site of a hand walk repeated: the
callee's triple (`triple_of_callW`), its relational lemma, its `AFr`, con-ron's bridge lemma for the
twin's run and `StageC.of_pstep`.
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section steps
variable {p : Prog} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
  {env : ConLeche.Env} {m₀ m : Mem} {a₀ a : AState} {n : Nat}

/-- **`open_pis_at_fvars_f`'s step**: the twin's `openPisAtFvarsF`, the package, the result decoded
(`none` exactly when the flag word is `0`) and denoting the opened telescope. -/
theorem opf_step (hOpf : OpfF p) (hk : InsAt dn vis fe env m₀ a₀ m a) {k e i : Word} (he : H e)
    {c : EIdx} (hc : decI e = c) {eP : ConLeche.Expr} (heP : denoteE a.store c = some eP) :
    Sim (callW p n "open_pis_at_fvars_f" [k, e, i] m) (openPisAtFvarsF k.toNat c i.toNat) a
      fun r o m' a' => InsAt dn vis fe env m a m' a' ∧ (r.headD 0 = 0 ↔ o = none) ∧
        ∀ l b, o = some (l, b) → decHL m' (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat = some l ∧
          (r.tail.headD 0).toNat + (r.tail.tail.headD 0).toNat ≤ iwTop m' ∧
          H (r.tail.tail.tail.headD 0) ∧ decI (r.tail.tail.tail.headD 0) = b ∧
          ∃ lP bP, ConLeche.openPisAtFvars k.toNat eP i.toNat = some (lP, bP) ∧
            Frontend.denoteEList a'.store l = some lP ∧ denoteE a'.store b = some bP :=
  fun r m' hc' => by
    subst hc
    obtain ⟨o, a', hr, ⟨⟨hS, hg, hdec⟩, -⟩, hA⟩ := opfSimRA (n := n) hOpf he hk.stage.stage hk.abs r m' hc'
    obtain ⟨p1, ho⟩ := ConRon.Bridge.Inductives.openPisAtFvarsF_run hk.stage.check.state heP hr
    refine ⟨o, a', hr, InsAt.pstep hk.stage hS hA hg p1, ?_, ?_⟩
    · cases o with
      | none => simpa [decOLE] using hdec
      | some q => exact ⟨fun h => absurd (hdec.1.symm.trans h) (by decide), fun h => by cases h⟩
    · rintro l b rfl
      obtain ⟨lP, bP, hq, hl, hb⟩ := ConRon.Bridge.Inductives.denoteOpen_some_inv ho
      obtain ⟨-, ⟨hl', hlb⟩, hb', hbd⟩ := hdec
      rw [sumGetD1, sumGetD2] at hl' hlb
      rw [drop3_eq] at hb' hbd
      exact ⟨hl', hlb, hb', hbd, lP, bP, hq, hl, hb⟩

/-- **`param_levels`' step**. -/
theorem pl_step (hP : SumProg p) (hk : InsAt dn vis fe env m₀ a₀ m a) {o l : Word} {lps : List NIdx}
    (hd : decHL m o.toNat l.toNat = some lps) (hb : o.toNat + l.toNat ≤ iwTop m)
    {lpsP : List ConLeche.Name} (hP' : Frontend.denoteNList a.store.ns lps = some lpsP) :
    Sim (callW p n "param_levels" [o, l] m) (paramLevels lps) a
      fun r us m' a' => InsAt dn vis fe env m a m' a' ∧ H (r.headD 0) ∧ decI (r.headD 0) = us ∧
        denoteLs a'.store.lss us = some (lpsP.map .param) :=
  fun r m' hc => by
    obtain ⟨s, hs, -, hm⟩ := triple_of_callW (plW_spec p hP.ha hP.hc hP.hsc hP.hg hP.hpf hP.hpp hP.hip
      hP.hplg hP.hpl hP.hil n ⟨m, Locals.init []⟩ o l) hc
    subst hs
    obtain ⟨us, a', hr, hS, hg, hu, hus⟩ := plSim n m a o l lps hk.stage.stage hd hb r s.mem hm
    obtain ⟨p2, husP⟩ := ConRon.Bridge.Inductives.paramLevels_spec lps lpsP a a' us hk.stage.check.state hP' hr
    exact ⟨us, a', hr, InsAt.pstep hk.stage hS (plW_afr hm hk.abs) hg p2, hu, hus, husP⟩

/-- **`intern_const`'s step**. -/
theorem ic_step (hP : SumProg p) (hk : InsAt dn vis fe env m₀ a₀ m a) {T u : Word} (hT : H T)
    (hu : H u) {TP : ConLeche.Name} {usP : List ConLeche.Level}
    (hTP : denoteN a.store.ns (decI T) = some TP) (husP : denoteLs a.store.lss (decI u) = some usP) :
    Sim (callW p n "intern_const" [T, u] m) (internE (.const (decI T) (decI u))) a
      fun r h m' a' => InsAt dn vis fe env m a m' a' ∧ h = decI (r.headD 0) ∧
        denoteE a'.store h = some (.const TP usP) :=
  fun r m' hc => by
    obtain ⟨s, hs, -, hm⟩ := triple_of_callW (internConst_spec p hP.hcf hP.hcp hP.hic n
      ⟨m, Locals.init []⟩ T u) hc
    subst hs
    obtain ⟨h, a', hr, he, hS, hg⟩ := ceSim m a T u hk.stage.stage hT hu (r.headD 0) s.mem hm
    obtain ⟨p3, hhd⟩ := ConRon.Bridge.Inductives.internConstE_run hk.stage.check.state hTP husP hr
    exact ⟨h, a', hr, InsAt.pstep hk.stage hS (ceinternW_afr hm hk.abs) hg p3, he, hhd⟩

/-- **`get_app_fn_f`'s step** (the twin state unchanged). -/
theorem gaf_step (hP : SumProg p) (hk : InsAt dn vis fe env m₀ a₀ m a) {e : Word} (he : H e)
    {eP : ConLeche.Expr} (heP : denoteE a.store (decI e) = some eP) :
    Sim (callW p n "get_app_fn_f" [CWF, e] m) (getAppFn coreWalkFuel (decI e)) a
      fun r x m' a' => InsAt dn vis fe env m a m' a' ∧ (r.headD 0).toNat < 2 ^ 32 ∧
        decI (r.headD 0) = x ∧ denoteE a'.store x = some eP.getAppFn :=
  fun r m' hc => by
    have h4 := gafF_ok dn vis fe CWF e he
    rw [CWF_eq] at h4
    obtain ⟨s, hs, -, hm⟩ := triple_of_callW (gafF_spec p hP.ad n ⟨m, Locals.init []⟩ [CWF, e]) hc
    subst hs
    obtain ⟨x, a', hr, hS, hg, hf32, hfd⟩ := (sumSim_of_relW h4 hk.stage.stage) r s.mem hm
    obtain ⟨ha, hx⟩ := ConRon.Bridge.Inductives.getAppFn_run hk.stage.check.state heP hr
    rw [ha] at hr hS
    exact ⟨x, a, hr, InsAt.pstep hk.stage hS ((show AFr _ _ from AFr.of_frame (gafF_frame hm)) hk.abs) hg
      (PStep.refl hk.stage.check.state), hf32, hfd, hx⟩

/-- **`get_app_args_f`'s step** (the twin state unchanged). -/
theorem gaa_step (hP : SumProg p) (hk : InsAt dn vis fe env m₀ a₀ m a) {e : Word} (he : H e)
    {eP : ConLeche.Expr} (heP : denoteE a.store (decI e) = some eP) :
    Sim (callW p n "get_app_args_f" [CWF, e] m) (getAppArgs coreWalkFuel (decI e)) a
      fun r xs m' a' => InsAt dn vis fe env m a m' a' ∧
        decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some xs ∧
        (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧
        Frontend.denoteEList a'.store xs = some eP.getAppArgs :=
  fun r m' hc => by
    have h5 := gaaF_ok dn vis fe CWF e he
    rw [CWF_eq] at h5
    obtain ⟨s, hs, -, hm⟩ := triple_of_callW (gaaF_spec p hP.ad n ⟨m, Locals.init []⟩ [CWF, e]) hc
    subst hs
    obtain ⟨xs, a', hr, hS, hg, hxs, hxb⟩ := (sumSim_of_relW h5 hk.stage.stage) r s.mem hm
    obtain ⟨ha, hx⟩ := ConRon.Bridge.Inductives.getAppArgs_run hk.stage.check.state heP hr
    rw [ha] at hr hS
    rw [sumGetD0, sumGetD1] at hxs hxb
    exact ⟨xs, a, hr, InsAt.pstep hk.stage hS (gaaF_afr hm hk.abs) hg (PStep.refl hk.stage.check.state),
      hxs, hxb, hx⟩

/-- **`sl_eq`** (an L helper, no twin step): the memory unchanged, `0` exactly when the two decoded
slices differ. -/
theorem slEq_step (hP : SumProg p) (hS : StageR dn vis fe m a) {o1 l1 o2 l2 : Word}
    {xs ys : List EIdx} (h1 : decHL m o1.toNat l1.toNat = some xs) (hb1 : o1.toNat + l1.toNat ≤ iwTop m)
    (h2 : decHL m o2.toNat l2.toNat = some ys) (hb2 : o2.toNat + l2.toNat ≤ iwTop m) :
    ∀ r m', callW p n "sl_eq" [o1, l1, o2, l2] m = some (r, m') →
      m' = m ∧ (r.headD 0 = 0 ↔ xs ≠ ys) := fun r m' hc => by
  obtain ⟨s, hs, -, hm, hq⟩ := triple_of_callW (slEq_spec p hP.heq n ⟨m, Locals.init []⟩ o1 l1 o2 l2) hc
  obtain ⟨ws1, hs1, hmm1, hw1⟩ := slR_of_decHL m _ _ _ h1 (hS.lt64 hb1)
  obtain ⟨ws2, hs2, hmm2, hw2⟩ := slR_of_decHL m _ _ _ h2 (hS.lt64 hb2)
  simp only [UInt64.ofNat_toNat] at hs1 hs2
  have heq := eqW_ok n m _ _ _ _ (r.headD 0) ws1 ws2 hs1 hs2 hq
  refine ⟨by rw [← hs, hm], ?_⟩
  rw [heq, hmm1, hmm2, Ne, map_decI_inj ws1 ws2 hw1 hw2]
  by_cases hw : ws1 = ws2 <;> simp [hw]

/-- **`field_doms_resolve`'s step**, under the view `vis0` (`fe₀`, the pre-block environment). -/
theorem fdr_step (hP : SumProg p) (hk : InsAt dn vis fe env m₀ a₀ m a) {vis0 o l : Word}
    {xs : List EIdx} (hd : decHL m o.toNat l.toNat = some xs) (hb : o.toNat + l.toNat ≤ iwTop m)
    {env₀ : ConLeche.Env} (hok : ConRon.Bridge.Inductives.IFEnvOKS env₀ (fe.restrictTo vis0.toNat) a.store)
    {xsP : List ConLeche.Expr} (hxs : Frontend.denoteEList a.store xs = some xsP) :
    Sim (callW p n "field_doms_resolve" [vis0, o, l] m) (fieldDomsResolve (fe.restrictTo vis0.toNat) xs) a
      fun r b m' a' => InsAt dn vis fe env m a m' a' ∧ (r.headD 0 = 0 ↔ b = false) :=
  fun r m' hc => by
    obtain ⟨s, hs, -, hm⟩ := triple_of_callW (fdrW_spec p hP.hfdr hP.ad.ftd hP.hcr n
      ⟨m, Locals.init []⟩ vis0 o l) hc
    subst hs
    obtain ⟨b, a', hr, hQ, hA⟩ := (fdrSim n m a o l xs (hk.stage.stage.restrict vis0) hd hb hk.abs) r s.mem hm
    obtain ⟨hS, hg, hb1⟩ := sumKeep_restrict hk.stage.stage.check.env.vis hQ
    obtain ⟨p6, -⟩ := ConRon.Bridge.Inductives.fieldDomsResolve_spec xs xsP
      ⟨hk.stage.check.state, hk.stage.check.pins, hok a rfl⟩ hxs hr
    refine ⟨b, a', hr, InsAt.pstep hk.stage hS hA hg p6, ?_⟩
    rw [← hb1]; cases b <;> simp

/-- **`idx_args_resolve`'s step**, under the view `vis0`. -/
theorem iar_step (hP : SumProg p) (hk : InsAt dn vis fe env m₀ a₀ m a) {vis0 o l : Word}
    {xs : List EIdx} (hd : decHL m o.toNat l.toNat = some xs) (hb : o.toNat + l.toNat ≤ iwTop m)
    {env₀ : ConLeche.Env} (hok : ConRon.Bridge.Inductives.IFEnvOKS env₀ (fe.restrictTo vis0.toNat) a.store)
    {xsP : List ConLeche.Expr} (hxs : Frontend.denoteEList a.store xs = some xsP) :
    Sim (callW p n "idx_args_resolve" [vis0, o, l] m) (idxArgsResolve (fe.restrictTo vis0.toNat) xs) a
      fun r b m' a' => InsAt dn vis fe env m a m' a' ∧ (r.headD 0 = 0 ↔ b = false) :=
  fun r m' hc => by
    obtain ⟨s, hs, -, hm⟩ := triple_of_callW (iarW_spec p hP.hiar hP.hcr n ⟨m, Locals.init []⟩ vis0 o l) hc
    subst hs
    obtain ⟨b, a', hr, hQ, hA⟩ := (iarSim n m a o l xs (hk.stage.stage.restrict vis0) hd hb hk.abs) r s.mem hm
    obtain ⟨hS, hg, hb1⟩ := sumKeep_restrict hk.stage.stage.check.env.vis hQ
    obtain ⟨p7, -⟩ := ConRon.Bridge.Inductives.idxArgsResolve_spec xs xsP
      ⟨hk.stage.check.state, hk.stage.check.pins, hok a rfl⟩ hxs hr
    refine ⟨b, a', hr, InsAt.pstep hk.stage hS hA hg p7, ?_⟩
    rw [← hb1]; cases b <;> simp

/-- **`strip_pis`' step** (the twin state unchanged). -/
theorem strip_step (hP : SumProg p) (hk : InsAt dn vis fe env m₀ a₀ m a) {k e : Word} (he : H e)
    {kN : Nat} (hkN : k.toNat = kN) {c : EIdx} (hc : decI e = c) {eP : ConLeche.Expr}
    (heP : denoteE a.store c = some eP) :
    Sim (callW p n "strip_pis" [k, e] m) (stripPis kN c) a
      fun r o m' a' => InsAt dn vis fe env m a m' a' ∧ (r.headD 0 = 0 ↔ o = none) ∧
        ∀ l b, o = some (l, b) → H (r.tail.tail.tail.headD 0) ∧ decI (r.tail.tail.tail.headD 0) = b ∧
          ∃ bP, denoteE a'.store b = some bP :=
  fun r m' hc' => by
    subst hkN hc
    obtain ⟨s, hs, -, hm⟩ := triple_of_callW (stripPis_specF p hP.strip n ⟨m, Locals.init []⟩ k e) hc'
    subst hs
    obtain ⟨o, a', hr, hS, hg, hdec⟩ := stripF_pis_ok dn vis fe k e he m s.mem a r hm hk.stage.stage
    obtain ⟨ha, ho⟩ := ConRon.Bridge.Inductives.stripPis_pstep hk.stage.check.state heP hr
    rw [ha] at hr hS
    refine ⟨o, a, hr, InsAt.pstep hk.stage hS (stripF_afr hm hk.abs) hg (PStep.refl hk.stage.check.state),
      ?_, ?_⟩
    · cases o with
      | none => simpa [decOLE] using hdec
      | some q => exact ⟨fun h => absurd (hdec.1.symm.trans h) (by decide), fun h => by cases h⟩
    · rintro l b rfl
      obtain ⟨-, bP, -, -, hb⟩ := ConRon.Bridge.Inductives.denoteBP_some ho
      obtain ⟨-, -, hb', hbd⟩ := hdec
      rw [drop3_eq] at hb' hbd
      exact ⟨hb', hbd, bP, hb⟩

/-- **`struct_ctor_resid_ok`'s step**. -/
theorem sr_step (hP : SumProg p) (hk : InsAt dn vis fe env m₀ a₀ m a) {T lo ll nP o nIdx cb : Word}
    {lps : List NIdx} (hT : H T) (hcb : H cb) (hd : decHL m lo.toNat ll.toNat = some lps)
    (hb : lo.toNat + ll.toNat ≤ iwTop m) (ho : o.toNat + nP.toNat < 2 ^ 64)
    (hni : nP.toNat + nIdx.toNat < 2 ^ 64) {TP : ConLeche.Name} {lpsP : List ConLeche.Name}
    {cbP : ConLeche.Expr} (hTP : denoteN a.store.ns (decI T) = some TP)
    (hlP : Frontend.denoteNList a.store.ns lps = some lpsP) (hcbP : denoteE a.store (decI cb) = some cbP) :
    Sim (callW p n "struct_ctor_resid_ok" [T, lo, ll, nP, o, nIdx, cb] m)
      (structCtorResidOk (decI T) lps nP.toNat o.toNat nIdx.toNat (decI cb)) a
      fun r b m' a' => InsAt dn vis fe env m a m' a' ∧ (r.headD 0 = 0 ↔ b = false) :=
  fun r m' hc => by
    obtain ⟨s, hs, -, hm⟩ := triple_of_callW (srW_spec p hP.ha hP.hc hP.hsc hP.hg hP.hpf hP.hpp hP.hip
      hP.hplg hP.hpl hP.hil hP.hcf hP.hcp hP.hic hP.hbf hP.hbp hP.hib hP.hpg hP.hps hP.heq hP.hsr hP.ad n
      ⟨m, Locals.init []⟩ T lo ll nP o nIdx cb) hc
    subst hs
    obtain ⟨b, a', hr, hS, hg, hb3, -⟩ := srW_ok dn vis fe n m s.mem a T lo ll nP o nIdx cb r lps hm
      hk.stage.stage hT hcb hd (hk.stage.stage.lt64 hb) hb ho hni
    obtain ⟨p3, -⟩ := ConRon.Bridge.Inductives.structCtorResidOk_spec (decI T) TP lps lpsP nP.toNat
      o.toNat nIdx.toNat _ cbP a a' b hk.stage.check.state ⟨hTP, hlP, hcbP⟩ hr
    refine ⟨b, a', hr, InsAt.pstep hk.stage hS (srW_afr _ _ _ _ _ _ _ _ _ _ _ hm hk.abs) hg p3, ?_⟩
    rw [← hb3]; cases b <;> simp

/-- **`fvar_type_ds`' step**. -/
theorem ftds_step (hP : SumProg p) (hk : InsAt dn vis fe env m₀ a₀ m a) {o l : Word} {xs : List EIdx}
    (hd : decHL m o.toNat l.toNat = some xs) (hb : o.toNat + l.toNat ≤ iwTop m)
    {xsP : List ConLeche.Expr} (hxs : Frontend.denoteEList a.store xs = some xsP) :
    Sim (callW p n "fvar_type_ds" [o, l] m) (fvarTypeDs xs) a
      fun r ds m' a' => InsAt dn vis fe env m a m' a' ∧
        decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some ds ∧
        (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧
        Frontend.denoteEList a'.store ds = some (xsP.map ConLeche.Expr.fvarTypeD) :=
  fun r m' hc => by
    obtain ⟨s, hs, -, hm⟩ := triple_of_callW (ftdsF_spec p hP.ad n ⟨m, Locals.init []⟩ [o, l]) hc
    subst hs
    obtain ⟨ds, a', hr, hS, hg, hds, hdb⟩ :=
      (sumSim_of_relW (ftdsF_ok dn vis fe o l xs) ⟨hk.stage.stage, hd, fun _ => hb⟩) r s.mem hm
    obtain ⟨p6, hdP⟩ := ConRon.Bridge.Inductives.fvarTypeDs_run xs xsP hk.stage.check.state hxs hr
    rw [sumGetD0, sumGetD1] at hds hdb
    exact ⟨ds, a', hr, InsAt.pstep hk.stage hS (ftdsF_afr hm hk.abs) hg p6, hds, hdb, hdP⟩

end steps

end L.Ind

end
