module

public import ConAgua.Arena.RecCheckSpec.RcLook
public import ConAgua.Arena.IndPosSpec.Rx
public import ConAgua.Arena.RecSim
import ConAgua.Arena.IndPosSpec.NestCrest
import ConAgua.Arena.IndPosSpec.SgGoW
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndPosSpec.DecNHFields
import ConAgua.Arena.IndPosSpec.MapOKStep
import ConAgua.Arena.IndPosSpec.PosmemoRxMfr
public import ConAgua.Arena.IndPosSpec.CrLook
public import ConAgua.Arena.IndPosSpec.NestGroupCtors
import all ConAgua.Arena.RecCheck

@[expose] public section

/-!
# EraseFVarTys: `ConRon.Arena.eraseFVarTys`, `ConRon.Arena.targetCanonParams`, `ConRon.Arena.targetCtorsOf`

The refinement theorems `eraseFVarTys_refines`, `targetCanonParams_refines`, `targetCtorsOf_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem RcMR.fr {m m' : Mem} (h : RcMR m) (hf : MFr [] [] m m') : RcMR m' :=
  ⟨h.pos.fr hf, let ⟨mp, hm⟩ := h.ta; ⟨mp, taMR_mfr hf (by simp) (by simp) hm⟩⟩

theorem RcMR.setRf {m m' : Mem} (h : RcMR m) (hf : RxFr m m') (hn : ∃ M G g, RfInv m' M G g) : RcMR m' :=
  ⟨h.pos.setRf hf hn, let ⟨mp, hm⟩ := h.ta; ⟨mp, taMR_mfr hf (by decide) (by decide) hm⟩⟩

theorem RcMR.setNo {m m' : Mem} (h : RcMR m) (hf : MFr [NOM] [204, 205] m m') (hn : ∃ mp, noMR m' mp) :
    RcMR m' :=
  ⟨h.pos.setNo hf hn, let ⟨mp, hm⟩ := h.ta; ⟨mp, taMR_mfr hf (by decide) (by decide) hm⟩⟩

/-- **`erase_fvar_tys` is its model `eftF`** (generated). -/
l_model eftF_spec (p : Prog) (L : RcLook p)
  fns [L.eft ↦ eftF list]
  specs [iwAlloc_specW p L.rx.ha n, (rxSpec_all p L.rx n).2.2.2.2.2.2.2]
  grind [arena_grind]

/-- **`target_canon_params` is its model `tcpF`** (generated). -/
l_model tcp_specF (p : Prog) (L : RcLook p)
  fns [L.tcp ↦ tcpF list]
  specs [rec3_specW p L.rx.ha n L.r3, (rxSpec_all p L.rx n).2.2.2.2.2.2.2]
  grind [arena_grind]

/-- A fresh `FvMap` record of words `ws` (`recW`): what `replace_fvars` needs of it, and the frames. -/
theorem rcFresh {vis : Word} {fe : IFEnv} {m m1 : Mem} {a : AState}
    {k : Word} {ws r : List Word} (h : recW m k ws = some (r, m1)) (hS : StageR vis fe m a)
    (hk : k.toNat = ws.length) :
    r = [rdW (m.arr64 CTL) 200] ∧ (rdW (m.arr64 CTL) 200).toNat = iwTop m ∧
    (∀ j < ws.length, (m1.arr64 IW)[iwTop m + j]? = ws[j]?) ∧
    StageR vis fe m1 a ∧ IWGrow m m1 ∧ MemFrame [IW] [200] m m1 ∧ iwTop m1 = iwTop m + ws.length := by
  obtain ⟨hr, hget, hg, hf, ht, -⟩ := recW_post h hS.iw.ctl hS.iw.iwSize hk
  refine ⟨hr, rfl, hget, ?_, hg, hf, ht⟩
  simp only [recW] at h
  rcases hal : allocW m k with _ | ⟨q, m0⟩ <;> rw [hal] at h
  · cases h
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact StageR.wrIW (allocW_stage hal hS).1 q ws

/-- `erase_fvar_tys` simulates `eraseFVarTys`. -/
theorem eftF_ok (fe : IFEnv) (vis : Word) (n : Nat) {m m' : Mem}
    {a : AState} {e : Word} {r : List Word} (h : eftF n m e = some (r, m')) (hS : StageR vis fe m a)
    (he : H e) (hP : RcMR m) :
    ∃ a', (ConRon.Arena.eraseFVarTys (decE e)).run a = .ok (decE (r.headD 0), a') ∧ H (r.headD 0) ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ RcMR m' := by
  rcases n with _ | n
  · cases h
  rw [eftF.arm1] at h
  rcases ha : allocW m 1 with _ | ⟨f, m1⟩ <;> simp only [ha, eftF.k_iw_alloc, reduceCtorEq] at h
  rcases hr : rxW n (m1.set64 IW f 2) f e with _ | ⟨z, m2⟩ <;> simp only [hr, eftF.k_replace_fvars, reduceCtorEq] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hrec : recW m 1 [2] = some ([f], m1.set64 IW f 2) := by simp [recW, ha, wrIW]
  obtain ⟨hr0, hq, hget, hS1, hg1, hf1, ht1⟩ := rcFresh hrec hS rfl
  simp only [List.cons.injEq, and_true] at hr0
  subst hr0
  have hfm : FMOk (m1.set64 IW (rdW (m.arr64 CTL) 200) 2) (rdW (m.arr64 CTL) 200).toNat .erase := by
    refine ⟨?_, ?_⟩
    · have := hget 0 (by simp); rw [Nat.add_zero, ← hq] at this; exact iwN_of_get this
    · simp only [List.length_singleton] at ht1; omega
  obtain ⟨M, G, g, hR⟩ := hP.pos.rf
  obtain ⟨a', hrun, hH, M', G', hS', hg', hR', -, -⟩ := (rxOK_all fe vis n).2.2.2.2.2.2 _ _ a _ e .erase z M G g hr
    hS1 hfm he (hR.frame (RfFr.of_iw hf1))
  exact ⟨a', hrun, hH, hS', hg1.trans hg', (hP.fr (MFr.of_iw hf1)).setRf (rxW_mfr hr) ⟨M', G', g, hR'⟩⟩

/-- `tcpF`'s two arms as one: the recorded offset `0` for an empty slice. -/
theorem tcpF_succ (n : Nat) (m : Mem) (pfo pfl e : Word) :
    tcpF (n + 1) m pfo pfl e = tcpF.j1 n pfl e (if pfl = 0 then 0 else pfo) m := by
  by_cases h0 : pfl = 0
  · rw [tcpF.arm1 n m pfo pfl e h0, ite_eq_left h0]
  · rw [tcpF.arm2 n m pfo pfl e h0, ite_eq_right h0]

/-- `target_canon_params` simulates `targetCanonParams`, from the openers decoded below the top. -/
theorem tcpF_ok (fe : IFEnv) (vis : Word) (n : Nat) {m m' : Mem}
    {a : AState} {pfo pfl e : Word} {pfvs : List EIdx} {r : List Word}
    (h : tcpF n m pfo pfl e = some (r, m')) (hS : StageR vis fe m a) (hpf : HSl0 m pfo pfl pfvs)
    (he : H e) (hP : RcMR m) :
    ∃ a', (ConRon.Arena.targetCanonParams pfvs (decE e)).run a = .ok (decE (r.headD 0), a') ∧
      H (r.headD 0) ∧ StageR vis fe m' a' ∧ IWGrow m m' ∧ RcMR m' := by
  rcases n with _ | n
  · cases h
  rw [tcpF_succ, tcpF.j1] at h
  -- the openers' offset as recorded: `0` for an empty slice
  obtain ⟨po, hpo, hpd, hpb⟩ : ∃ po : Word, po = (if pfl = 0 then 0 else pfo) ∧
      decHL m po.toNat pfl.toNat = some pfvs ∧ po.toNat + pfl.toNat ≤ iwTop m := by
    by_cases h0 : pfl = 0
    · subst h0
      have hx : pfvs = [] := by have := hpf.len; simpa using this
      subst hx
      exact ⟨0, by simp, by simp [decHL, hslice?], by simp⟩
    · rcases hpf.2 with h1 | h1
      · exact absurd h1 h0
      · exact ⟨pfo, by simp [h0], hpf.1, h1⟩
  rw [← hpo] at h
  rcases hrec : recW m 3 [3, po, pfl] with _ | ⟨r1, m1⟩ <;> simp only [hrec, tcpF.k_rec3, reduceCtorEq] at h
  obtain ⟨hr0, hq, hget, hS1, hg1, hf1, ht1⟩ := rcFresh hrec hS rfl
  subst hr0
  simp only [List.headD_cons] at h
  rcases hr : rxW n m1 (rdW (m.arr64 CTL) 200) e with _ | ⟨z, m2⟩ <;> simp only [hr, tcpF.k_replace_fvars, reduceCtorEq] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  simp only [List.length_cons, List.length_nil] at ht1
  have g0 := hget 0 (by simp)
  have g1 := hget 1 (by simp)
  have g2 := hget 2 (by simp)
  simp only [Nat.add_zero, List.getElem?_cons_zero, List.getElem?_cons_succ] at g0 g1 g2
  have hfm : FMOk m1 (rdW (m.arr64 CTL) 200).toNat (.canon pfvs) := by
    rw [hq]
    refine ⟨iwN_of_get g0, by omega, po.toNat, pfl.toNat, iwN_of_get g1, iwN_of_get g2, ?_, by omega⟩
    rw [decHL_grow hg1 hpb]; exact hpd
  obtain ⟨M, G, g, hR⟩ := hP.pos.rf
  obtain ⟨a', hrun, hH, M', G', hS', hg', hR', -, -⟩ := (rxOK_all fe vis n).2.2.2.2.2.2 _ _ a _ e _ z M G g hr
    hS1 hfm he (hR.frame (RfFr.of_iw hf1))
  exact ⟨a', hrun, hH, hS', hg1.trans hg', (hP.fr (MFr.of_iw hf1)).setRf (rxW_mfr hr) ⟨M', G', g, hR'⟩⟩

section census
variable (p : Prog) (L : RcLook p)
include L

/-- **`erase_fvar_tys` refines `eraseFVarTys`** (through `replace_fvars`' `mk_app_n` stub): the walk
memos well formed before and after. -/
@[refines ConRon.Arena.eraseFVarTys]
theorem eraseFVarTys_refines (n : Nat) (s₀ : St) (a₀ : AState) (_dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis e : Word) (he : H e) (hS : StageR vis fe s₀.mem a₀) (hP : RcMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "erase_fvar_tys" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.eraseFVarTys (decE e)) a₀ ∧
      decE (r.headD 0) = AM.res (ConRon.Arena.eraseFVarTys (decE e)) a₀ ∧ H (r.headD 0) ∧
      StageR vis fe s'.mem (AM.st (ConRon.Arena.eraseFVarTys (decE e)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ RcMR s'.mem; ⊤⦄ := by
  refine triple_post (eftF_spec p L (n + 1) s₀ e) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨a', hrun, hH, hS', hg, hP'⟩ := eftF_ok fe vis (n + 1) hm hS he hP
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, hres.symm, hH, by rw [hst]; exact hS', hg, hP'⟩

/-- **`target_canon_params` refines `targetCanonParams`** (through `replace_fvars`' stub). -/
@[refines ConRon.Arena.targetCanonParams]
theorem targetCanonParams_refines (n : Nat) (s₀ : St) (a₀ : AState) (_dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis pfo pfl e : Word) (pfvs : List EIdx) (he : H e) (hS : StageR vis fe s₀.mem a₀)
    (hpf : HSl0 s₀.mem pfo pfl pfvs) (hP : RcMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "target_canon_params" [pfo, pfl, e]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.targetCanonParams pfvs (decE e)) a₀ ∧
      decE (r.headD 0) = AM.res (ConRon.Arena.targetCanonParams pfvs (decE e)) a₀ ∧ H (r.headD 0) ∧
      StageR vis fe s'.mem (AM.st (ConRon.Arena.targetCanonParams pfvs (decE e)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ RcMR s'.mem; ⊤⦄ := by
  refine triple_post (tcp_specF p L (n + 1) s₀ pfo pfl e) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨a', hrun, hH, hS', hg, hP'⟩ := tcpF_ok fe vis (n + 1) hm hS hpf he hP
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, hres.symm, hH, by rw [hst]; exact hS', hg, hP'⟩

end census

/-! ## `target_ctors_of` -/

l_model targetCtorsOf_spec (p : Prog) (hL : RcLook p)
  fns [hL.tco ↦ tcoW]
  specs [nt_spec' p hL.nt n]
  grind [arena_grind]

theorem NcOut.tco {m : Mem} {r : List Word} {x : Option (Nat × List (IConstantVal × Nat))} (h : NcOut m r x) :
    NcOut m [r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0] x := by
  cases x with
  | none => exact h
  | some y => exact h

/-- `target_ctors_of` simulates `targetCtorsOf`. -/
theorem tcoW_ok (_dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis I : Word) (hI : H I) (n : Nat) {m m' : Mem} {a : AState} {r : List Word} (h : tcoW (n + 2) m vis I = some (r, m'))
    (hS : StageR vis fe m a) :
    ∃ x a', (ConRon.Arena.targetCtorsOf fe (decI I)).run a = .ok (x, a') ∧ StageR vis fe m' a' ∧
      IWGrow m m' ∧ NcOut m' r x ∧ MFr [] [] m m' := by
  rw [tcoW.arm1] at h
  rcases hn : ntWf (n + 1) m vis I with _ | ⟨r1, m1⟩ <;> simp only [hn, tcoW.k_nest_container, reduceCtorEq] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨x, a', hrun, hS', hg, hout⟩ := ntW_ok fe vis I hI n m _ a r1 hn hS
  exact ⟨x, a', hrun, hS', hg, hout.tco, ntWf_mfr hn⟩

/-- **`target_ctors_of` refines `targetCtorsOf`** (through `nest_container`'s stubs). -/
@[refines ConRon.Arena.targetCtorsOf]
theorem targetCtorsOf_refines (p : Prog) (L : RcLook p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis I : Word) (hI : H I) (hS : StageR vis fe s₀.mem a₀) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 2)) "target_ctors_of" [vis, I]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.targetCtorsOf fe (decI I)) a₀ ∧
      StageR vis fe s'.mem (AM.st (ConRon.Arena.targetCtorsOf fe (decI I)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ NcOut s'.mem r (AM.res (ConRon.Arena.targetCtorsOf fe (decI I)) a₀); ⊤⦄ := by
  refine triple_post (targetCtorsOf_spec p L (n + 2) s₀ vis I) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hg, hout, -⟩ := tcoW_ok dn fe vis I hI n hm hS
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hout⟩

end L.Ind

end
