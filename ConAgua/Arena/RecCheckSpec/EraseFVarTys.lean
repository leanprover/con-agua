module

public import ConAgua.Arena.RecCheckSpec.RcLook
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
import ConAgua.Arena.IndPosSpec.Rx
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

def eftK1 (n : Nat) (e : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (f, m1) => eftK2 (rxW n (m1.set64 IW f 2) f e)

/-- **The model of `erase_fvar_tys`** (body fuel `n`). -/
def eftW (n : Nat) (m : Mem) (e : Word) : Option (List Word × Mem) := eftK1 n e (allocW m 1)

section arms
variable (n : Nat) (m1 m2 : Mem) (e f r : Word)
theorem eftK1_some : eftK1 n e (some (f, m1)) = eftK2 (rxW n (m1.set64 IW f 2) f e) := rfl
theorem eftK2_some : eftK2 (some (r, m2)) = some ([r], m2) := rfl
end arms
attribute [ind_grind] eftK1_some eftK2_some

theorem eraseFVarTys_spec (p : Prog) (L : RxLook p) (hp : p.lookup "erase_fvar_tys" = some eraseFVarTys)
    (n : Nat) (s₀ : St) (e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "erase_fvar_tys" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ eftW n s₀.mem e = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, eraseFVarTys]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      iwAlloc_specW p L.ha n, (rxSpec_all p L n).2.2.2.2.2.2.2] <;>
    finish (gen := 20) [eftW]

/-- A fresh `FvMap` record of words `ws` (`recW`): what `replace_fvars` needs of it, and the frames. -/
theorem rcFresh {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m1 : Mem} {a : AState}
    {k : Word} {ws r : List Word} (h : recW m k ws = some (r, m1)) (hS : StageR vis fe m a)
    (hk : k.toNat = ws.length) :
    r = [rdW (m.arr64 CTL) 200] ∧ (rdW (m.arr64 CTL) 200).toNat = iwTop m ∧
    (∀ j < ws.length, (m1.arr64 IW)[iwTop m + j]? = ws[j]?) ∧
    StageR vis fe m1 a ∧ IWGrow m m1 ∧ MemFrame [IW] [200] m m1 ∧ iwTop m1 = iwTop m + ws.length := by
  sorry

/-- `erase_fvar_tys` simulates `eraseFVarTys`. -/
theorem eftW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (n : Nat) {m m' : Mem}
    {a : AState} {e : Word} {r : List Word} (h : eftW n m e = some (r, m')) (hS : StageR vis fe m a)
    (he : H e) (hP : RcMR m) :
    ∃ a', (ConRon.Arena.eraseFVarTys (decE e)).run a = .ok (decE (r.headD 0), a') ∧ H (r.headD 0) ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ RcMR m' := by
  sorry

theorem tcpK1_some (n : Nat) (e : Word) (r1 : List Word) (m1 : Mem) :
    tcpK1 n e (some (r1, m1)) = eftK2 (rxW n m1 (r1.headD 0) e) := rfl
attribute [ind_grind] tcpK1_some

theorem targetCanonParams_spec (p : Prog) (L : RxLook p) (h3 : p.lookup "rec3" = some rec3)
    (hp : p.lookup "target_canon_params" = some targetCanonParams) (n : Nat) (s₀ : St) (pfo pfl e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "target_canon_params" [pfo, pfl, e]
    ⦃fun r s' => LocEq s' s₀ ∧ tcpW n s₀.mem pfo pfl e = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, targetCanonParams]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      rec3_specW p L.ha n h3, (rxSpec_all p L n).2.2.2.2.2.2.2] <;>
    finish (gen := 20) [tcpW]

/-- `target_canon_params` simulates `targetCanonParams`, from the openers decoded below the top. -/
theorem tcpW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (n : Nat) {m m' : Mem}
    {a : AState} {pfo pfl e : Word} {pfvs : List EIdx} {r : List Word}
    (h : tcpW n m pfo pfl e = some (r, m')) (hS : StageR vis fe m a) (hpf : HSl0 m pfo pfl pfvs)
    (he : H e) (hP : RcMR m) :
    ∃ a', (ConRon.Arena.targetCanonParams pfvs (decE e)).run a = .ok (decE (r.headD 0), a') ∧
      H (r.headD 0) ∧ StageR vis fe m' a' ∧ IWGrow m m' ∧ RcMR m' := by
  sorry

section census
variable (p : Prog) (L : RcLook p)
include L

/-- **`erase_fvar_tys` refines `eraseFVarTys`** (through `replace_fvars`' `mk_app_n` stub): the walk
memos well formed before and after. -/
@[refines ConRon.Arena.eraseFVarTys]
theorem eraseFVarTys_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis e : Word) (he : H e) (hS : StageR vis fe s₀.mem a₀) (hP : RcMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "erase_fvar_tys" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.eraseFVarTys (decE e)) a₀ ∧
      decE (r.headD 0) = AM.res (ConRon.Arena.eraseFVarTys (decE e)) a₀ ∧ H (r.headD 0) ∧
      StageR vis fe s'.mem (AM.st (ConRon.Arena.eraseFVarTys (decE e)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ RcMR s'.mem; ⊤⦄ := by
  refine triple_post (eraseFVarTys_spec p L.rx L.eft n s₀ e) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨a', hrun, hH, hS', hg, hP'⟩ := eftW_ok dn fe vis n hm hS he hP
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, hres.symm, hH, by rw [hst]; exact hS', hg, hP'⟩

/-- **`target_canon_params` refines `targetCanonParams`** (through `replace_fvars`' stub). -/
@[refines ConRon.Arena.targetCanonParams]
theorem targetCanonParams_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis pfo pfl e : Word) (pfvs : List EIdx) (he : H e) (hS : StageR vis fe s₀.mem a₀)
    (hpf : HSl0 s₀.mem pfo pfl pfvs) (hP : RcMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "target_canon_params" [pfo, pfl, e]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.targetCanonParams pfvs (decE e)) a₀ ∧
      decE (r.headD 0) = AM.res (ConRon.Arena.targetCanonParams pfvs (decE e)) a₀ ∧ H (r.headD 0) ∧
      StageR vis fe s'.mem (AM.st (ConRon.Arena.targetCanonParams pfvs (decE e)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ RcMR s'.mem; ⊤⦄ := by
  refine triple_post (targetCanonParams_spec p L.rx L.r3 L.tcp n s₀ pfo pfl e) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨a', hrun, hH, hS', hg, hP'⟩ := tcpW_ok dn fe vis n hm hS hpf he hP
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, hres.symm, hH, by rw [hst]; exact hS', hg, hP'⟩

end census

/-! ## `target_ctors_of` -/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
l_model targetCtorsOf_spec (p : Prog) (hL : RcLook p)
  fns [hL.tco ↦ tcoW]
  specs [nt_spec' p hL.nt n]
  grind [arena_grind]
-/

theorem NcOut.tco {m : Mem} {r : List Word} {x : Option (Nat × List (IConstantVal × Nat))} (h : NcOut m r x) :
    NcOut m [r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0] x := by
  cases x with
  | none => exact h
  | some y => exact h

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- `target_ctors_of` simulates `targetCtorsOf`. -/
theorem tcoW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis I : Word) (hI : H I) (n : Nat) {m m' : Mem} {a : AState} {r : List Word} (h : tcoW (n + 2) m vis I = some (r, m'))
    (hS : StageR vis fe m a) :
    ∃ x a', (ConRon.Arena.targetCtorsOf fe (decI I)).run a = .ok (x, a') ∧ StageR vis fe m' a' ∧
      IWGrow m m' ∧ NcOut m' r x ∧ MFr [] [] m m' := by
  rw [tcoW.arm1] at h
  rcases hn : ntWf (n + 1) m vis I with _ | ⟨r1, m1⟩ <;> simp only [hn, tcoW.k_nest_container, reduceCtorEq] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨x, a', hrun, hS', hg, hout⟩ := ntW_ok dn fe vis I hI n m _ a r1 hn hS
  exact ⟨x, a', hrun, hS', hg, hout.tco, ntWf_mfr hn⟩
-/

/-- **`target_ctors_of` refines `targetCtorsOf`** (through `nest_container`'s stubs). -/
@[refines ConRon.Arena.targetCtorsOf]
theorem targetCtorsOf_refines (p : Prog) (L : RcLook p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis I : Word) (hI : H I) (hS : StageR vis fe s₀.mem a₀) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 2)) "target_ctors_of" [vis, I]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.targetCtorsOf fe (decI I)) a₀ ∧
      StageR vis fe s'.mem (AM.st (ConRon.Arena.targetCtorsOf fe (decI I)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ NcOut s'.mem r (AM.res (ConRon.Arena.targetCtorsOf fe (decI I)) a₀); ⊤⦄ := by
  sorry

end L.Ind

end
