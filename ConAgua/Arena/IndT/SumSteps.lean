module

public import ConAgua.Arena.IndT.Install1
import ConAgua.Arena.IndSumSpec.CheckSumCtor
import ConAgua.Arena.IndSumSpec.SumRules
import ConRon.Bridge.Inductives.SumInstall
import ConRon.Bridge.Inductives.StructParts
import ConAgua.Arena.IndPosSpec.NestBlockOfKey
import ConAgua.Arena.IndSim
import ConAgua.Arena.IndSumSpec.Row
import ConAgua.Arena.IndSumSpec.StructCtorResidOk
import ConAgua.Arena.RecGenSpec.CruleProg
public import ConAgua.Arena.IndSumSpec.SumProg
public import ConRon.Bridge.Inductives.Rel

@[expose] public section

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
            Frontend.denoteEList a'.store l = some lP ∧ denoteE a'.store b = some bP := by
  sorry

/-- **`param_levels`' step**. -/
theorem pl_step (hP : SumProg p) (hk : InsAt dn vis fe env m₀ a₀ m a) {o l : Word} {lps : List NIdx}
    (hd : decHL m o.toNat l.toNat = some lps) (hb : o.toNat + l.toNat ≤ iwTop m)
    {lpsP : List ConLeche.Name} (hP' : Frontend.denoteNList a.store.ns lps = some lpsP) :
    Sim (callW p n "param_levels" [o, l] m) (paramLevels lps) a
      fun r us m' a' => InsAt dn vis fe env m a m' a' ∧ H (r.headD 0) ∧ decI (r.headD 0) = us ∧
        denoteLs a'.store.lss us = some (lpsP.map .param) := by
  sorry

/-- **`intern_const`'s step**. -/
theorem ic_step (hP : SumProg p) (hk : InsAt dn vis fe env m₀ a₀ m a) {T u : Word} (hT : H T)
    (hu : H u) {TP : ConLeche.Name} {usP : List ConLeche.Level}
    (hTP : denoteN a.store.ns (decI T) = some TP) (husP : denoteLs a.store.lss (decI u) = some usP) :
    Sim (callW p n "intern_const" [T, u] m) (internE (.const (decI T) (decI u))) a
      fun r h m' a' => InsAt dn vis fe env m a m' a' ∧ h = decI (r.headD 0) ∧
        denoteE a'.store h = some (.const TP usP) := by
  sorry

/-- **`get_app_fn_f`'s step** (the twin state unchanged). -/
theorem gaf_step (hP : SumProg p) (hk : InsAt dn vis fe env m₀ a₀ m a) {e : Word} (he : H e)
    {eP : ConLeche.Expr} (heP : denoteE a.store (decI e) = some eP) :
    Sim (callW p n "get_app_fn_f" [CWF, e] m) (getAppFn coreWalkFuel (decI e)) a
      fun r x m' a' => InsAt dn vis fe env m a m' a' ∧ (r.headD 0).toNat < 2 ^ 32 ∧
        decI (r.headD 0) = x ∧ denoteE a'.store x = some eP.getAppFn := by
  sorry

/-- **`get_app_args_f`'s step** (the twin state unchanged). -/
theorem gaa_step (hP : SumProg p) (hk : InsAt dn vis fe env m₀ a₀ m a) {e : Word} (he : H e)
    {eP : ConLeche.Expr} (heP : denoteE a.store (decI e) = some eP) :
    Sim (callW p n "get_app_args_f" [CWF, e] m) (getAppArgs coreWalkFuel (decI e)) a
      fun r xs m' a' => InsAt dn vis fe env m a m' a' ∧
        decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some xs ∧
        (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧
        Frontend.denoteEList a'.store xs = some eP.getAppArgs := by
  sorry

/-- **`sl_eq`** (an L helper, no twin step): the memory unchanged, `0` exactly when the two decoded
slices differ. -/
theorem slEq_step (hP : SumProg p) (hS : StageR vis fe m a) {o1 l1 o2 l2 : Word}
    {xs ys : List EIdx} (h1 : decHL m o1.toNat l1.toNat = some xs) (hb1 : o1.toNat + l1.toNat ≤ iwTop m)
    (h2 : decHL m o2.toNat l2.toNat = some ys) (hb2 : o2.toNat + l2.toNat ≤ iwTop m) :
    ∀ r m', callW p n "sl_eq" [o1, l1, o2, l2] m = some (r, m') →
      m' = m ∧ (r.headD 0 = 0 ↔ xs ≠ ys) := by
  sorry

/- ronsync2 stage 2: commented out (statement at the old twin/L)
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
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
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
-/

/-- **`strip_pis`' step** (the twin state unchanged). -/
theorem strip_step (hP : SumProg p) (hk : InsAt dn vis fe env m₀ a₀ m a) {k e : Word} (he : H e)
    {kN : Nat} (hkN : k.toNat = kN) {c : EIdx} (hc : decI e = c) {eP : ConLeche.Expr}
    (heP : denoteE a.store c = some eP) :
    Sim (callW p n "strip_pis" [k, e] m) (stripPis kN c) a
      fun r o m' a' => InsAt dn vis fe env m a m' a' ∧ (r.headD 0 = 0 ↔ o = none) ∧
        ∀ l b, o = some (l, b) → H (r.tail.tail.tail.headD 0) ∧ decI (r.tail.tail.tail.headD 0) = b ∧
          ∃ bP, denoteE a'.store b = some bP := by
  sorry

/-- **`struct_ctor_resid_ok`'s step**. -/
theorem sr_step (hP : SumProg p) (hk : InsAt dn vis fe env m₀ a₀ m a) {T lo ll nP o nIdx cb : Word}
    {lps : List NIdx} (hT : H T) (hcb : H cb) (hd : decHL m lo.toNat ll.toNat = some lps)
    (hb : lo.toNat + ll.toNat ≤ iwTop m) (ho : o.toNat + nP.toNat < 2 ^ 64)
    (hni : nP.toNat + nIdx.toNat < 2 ^ 64) {TP : ConLeche.Name} {lpsP : List ConLeche.Name}
    {cbP : ConLeche.Expr} (hTP : denoteN a.store.ns (decI T) = some TP)
    (hlP : Frontend.denoteNList a.store.ns lps = some lpsP) (hcbP : denoteE a.store (decI cb) = some cbP) :
    Sim (callW p n "struct_ctor_resid_ok" [T, lo, ll, nP, o, nIdx, cb] m)
      (structCtorResidOk (decI T) lps nP.toNat o.toNat nIdx.toNat (decI cb)) a
      fun r b m' a' => InsAt dn vis fe env m a m' a' ∧ (r.headD 0 = 0 ↔ b = false) := by
  sorry

/-- **`fvar_type_ds`' step**. -/
theorem ftds_step (hP : SumProg p) (hk : InsAt dn vis fe env m₀ a₀ m a) {o l : Word} {xs : List EIdx}
    (hd : decHL m o.toNat l.toNat = some xs) (hb : o.toNat + l.toNat ≤ iwTop m)
    {xsP : List ConLeche.Expr} (hxs : Frontend.denoteEList a.store xs = some xsP) :
    Sim (callW p n "fvar_type_ds" [o, l] m) (fvarTypeDs xs) a
      fun r ds m' a' => InsAt dn vis fe env m a m' a' ∧
        decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some ds ∧
        (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧
        Frontend.denoteEList a'.store ds = some (xsP.map ConLeche.Expr.fvarTypeD) := by
  sorry

end steps

end L.Ind

end
