module

public import ConAgua.Arena.DeclArmT
public import ConAgua.Arena.DeclReducePin
public import ConAgua.Arena.DeclAxQuotT
import ConAgua.Arena.IndInstallSpec.PapW
import ConAgua.Arena.DeclNatPushPop
import ConAgua.Arena.IndSumSpec.ConsSumCtors
import ConAgua.Arena.IndRealMemoCrT
import ConAgua.Arena.IndRealWalkT
import ConAgua.Arena.RefWalk
import ConAgua.Arena.QuotAtT
import ConAgua.Arena.IndPosSpec.CloseTelescope
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
import ConRon.Bridge.Checker.Arms
import ConRon.Bridge.Checker.Base
public import ConRon.Bridge.Checker.DeclVal
public import ConRon.Bridge.Core.Knot
import all ConAgua.Arena.DeclArms

@[expose] public section

/-!
# The reduce-pin gate and the opaque arm under `StageT`

`check_reduce_pin` (models in `DeclReducePin.lean`) interns between its two core calls, so it runs
under `StageT` with con-ron's `CheckOK` beside it, as con-ron's `checkReducePin_bridge` does:

* the leaves (`reduce_elem_ok`, `reduce_decl_pin`, `reduce_cert_var`, `mk_app`, and
  `reduce_stored_ok` at the pushed view) by their `StageR` refinements, the leaves' write set
  (`LeafClosed`), and con-ron's run lemmas (`IStepS`, so `TwinOK` after by `TwinOK.of_istep`, and
  `CheckOK` after by `CheckOK.mono`);
* `reduce_pin_guard` (`rpg_ref`): its leaf `reduce_decl_pin` as above, the walks' `StageT`
  contracts, `CheckOK` after by con-ron's `reducePinGuard_run`;
* the two `is_def_eq_core` calls by the knot's `StageT` sim, `CheckOK` after by con-ron's
  `KnotSpec.defeq`;
* the push, the one read at the pushed view and the pop (`env_pop_temp`, `EnvR.popTemp`): the
  popped index is the old one's view (`IFEnv.SameView`), so `TwinOK` and `CheckOK` move to it.

The opaque arm (`cdo_ref`) carries con-ron's fold invariant across the constant check and the
value check (`checkConstantVal_bridge_of_fold`, `checkOpaqueVal_bridge`), as con-ron's
`checkDecl_bridge_opaque` does.
-/

open ConRon.Arena
open ConLeche (IndWF CtorWF)
open Std.WP
open scoped Lean.Order

noncomputable section

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF)
open ConRon.Bridge (CheckOK StepOK FoldOK CoreSpec)

local notation "V" => ConLeche.CheckMode.verified

/-! ## The popped index is the old one's view -/

/-- `StoreDen` reads the environment through `find?` and `findTable?` only. -/
theorem StoreDen.sameView {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState}
    {fe fe' : IFEnv} (h : StoreDen dn m a fe) (hv : ConRon.Bridge.IFEnv.SameView fe' fe) :
    StoreDen dn m a fe' := by
  have hT : ∀ c, fe'.findTable? c = fe.findTable? c := fun c => by
    simp only [IFEnv.findTable?, IFEnv.rawTable?, hv.find, hv.tbls, hv.base]
  exact { h with
    constLps := fun c ci hc => h.constLps c ci (by rw [← hv.find]; exact hc)
    proj := fun c t hc => h.proj c t (by rw [← hT]; exact hc)
    recRules := fun c cv mI rP isK rules hc => h.recRules c cv mI rP isK rules (by rw [← hv.find]; exact hc)
    recLevels := fun c cv mI rP isK rules hc =>
      h.recLevels c cv mI rP isK rules (by rw [← hv.find]; exact hc) }

/-- `TwinOK` at another view of the same index. -/
theorem TwinOK.sameView {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState}
    {fe fe' : IFEnv} (h : TwinOK dn m a fe) (hv : ConRon.Bridge.IFEnv.SameView fe' fe) :
    TwinOK dn m a fe' :=
  ⟨h.readL, h.readLs, h.nwf, h.erec, h.spn, h.memos, h.bstk, h.den.sameView hv⟩

/-! ## The gate's leaves under `StageT` and `CheckOK` -/

section leaves
variable {p : Prog} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
  {env : ConLeche.Env}

/-- **`reduce_elem_ok` under `StageT`**, `CheckOK` kept, the answer con-leche's. -/
theorem reo_simT (hC : CrpProg p) (hcl : LeafClosed p) (n : Nat) {m : Mem} {a : AState}
    {c : Word} {nm : ConLeche.Name} (hS : StageT dn vis fe m a) (hck : CheckOK false env fe a)
    (hnm : denoteN a.store.ns (decI c) = some nm) (hc : c.toNat < 2 ^ 32) :
    Sim (callW p n "reduce_elem_ok" [vis, c] m) (reduceElemOk fe (decI c)) a
      (fun r x m' a' => StageT dn vis fe m' a' ∧ IWGrow m m' ∧ decW0B m' r x ∧
        CheckOK false env fe a' ∧ Ext a.store a'.store ∧ x = ConLeche.reduceElemOk env nm) := by
  intro r m' h
  obtain ⟨s', hs', -, hok, hS', hg, hd⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (reduceElemOk_refines p hC.red vis fe c hc n ⟨m, Locals.init []⟩ a hS.stage) h
  subst hs'
  have hrun := AM.run_of_ok _ _ hok
  obtain ⟨hst, hx⟩ := ConRon.Bridge.reduceElemOk_run hck.state hck.pins hck.ienv hnm _ _ hrun
  exact ⟨_, _, hrun, StageT.of_leafI hS hS' hst (callW_leafFrame hcl (leaf_mem _ rfl) h), hg, hd,
    hck.mono hst.ok hst.ext hst.caches hst.pins, hst.ext, hx⟩

/-- **`reduce_decl_pin` under `StageT`**, `CheckOK` kept, the pin denoting con-leche's. -/
theorem rdp_simT (hC : CrpProg p) (hcl : LeafClosed p) (n : Nat) {m : Mem} {a : AState}
    {c : Word} {nm : ConLeche.Name} (hS : StageT dn vis fe m a) (hck : CheckOK false env fe a)
    (hnm : denoteN a.store.ns (decI c) = some nm) (hc : c.toNat < 2 ^ 32) :
    Sim (callW p n "reduce_decl_pin" [c] m) (reduceDeclPin (decI c)) a
      (fun r x m' a' => StageT dn vis fe m' a' ∧ IWGrow m m' ∧ decW0E m' r x ∧
        CheckOK false env fe a' ∧ Ext a.store a'.store ∧
        denoteE a'.store x = some (ConLeche.reduceDeclPin nm)) := by
  intro r m' h
  obtain ⟨s', hs', -, hok, hS', hg, hd⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (reduceDeclPin_refines (p := p) (hpa := hC.red.pa) (n := n) (s₀ := ⟨m, Locals.init []⟩)
      (a₀ := a) (hS := hS.stage) (hc := hc) (hR := hC.red.rom) (hp := hC.rdp)) h
  subst hs'
  have hrun := AM.run_of_ok _ _ hok
  obtain ⟨hst, hden⟩ := ConRon.Bridge.reduceDeclPin_run hck.state hck.pins hnm hrun
  exact ⟨_, _, hrun, StageT.of_leafI hS hS' hst (callW_leafFrame hcl (leaf_mem _ rfl) h), hg, hd,
    hck.mono hst.ok hst.ext hst.caches hst.pins, hst.ext, hden⟩

/-- **`reduce_cert_var` under `StageT`**, `CheckOK` kept, the variable denoting con-leche's. -/
theorem rcv_simT (hC : CrpProg p) (hcl : LeafClosed p) (n : Nat) {m : Mem} {a : AState}
    {c : Word} {nm : ConLeche.Name} (hS : StageT dn vis fe m a) (hck : CheckOK false env fe a)
    (hnm : denoteN a.store.ns (decI c) = some nm) (hc : c.toNat < 2 ^ 32) :
    Sim (callW p n "reduce_cert_var" [c] m) (reduceCertVar (decI c)) a
      (fun r x m' a' => StageT dn vis fe m' a' ∧ IWGrow m m' ∧ x = decE (r.headD 0) ∧
        CheckOK false env fe a' ∧ Ext a.store a'.store ∧
        denoteE a'.store x = some (ConLeche.reduceCertVar nm)) := by
  intro r m' h
  obtain ⟨s', hs', -, hok, hS', hg, hd⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (reduceCertVar_refines (p := p) (hp := hC.rcv) (n := n) (s₀ := ⟨m, Locals.init []⟩) (a₀ := a)
      (fe := fe) (vis := vis) (c := c) (hS := hS.stage) (hc := hc)) h
  subst hs'
  have hrun := AM.run_of_ok _ _ hok
  obtain ⟨hst, hden⟩ := ConRon.Bridge.reduceCertVar_run hck.state hck.pins hnm hrun
  exact ⟨_, _, hrun, StageT.of_leafI hS hS' hst (callW_leafFrame hcl (leaf_mem _ rfl) h), hg, hd,
    hck.mono hst.ok hst.ext hst.caches hst.pins, hst.ext, hden⟩

/-- **`mk_app` under `StageT`**, `CheckOK` kept, the application denoting. -/
theorem mkApp_simT (hC : CrpProg p) (hcl : LeafClosed p) (n : Nat) {m : Mem} {a : AState}
    {f x : Word} {ef ex : ConLeche.Expr} (hS : StageT dn vis fe m a) (hck : CheckOK false env fe a)
    (hf : denoteE a.store (decI f) = some ef) (hx : denoteE a.store (decI x) = some ex) :
    Sim (callW p n "mk_app" [f, x] m) (internE (.app (decI f) (decI x))) a
      (fun r y m' a' => StageT dn vis fe m' a' ∧ IWGrow m m' ∧ y = decE (r.headD 0) ∧
        CheckOK false env fe a' ∧ Ext a.store a'.store ∧
        denoteE a'.store y = some (.app ef ex)) := by
  intro r m' h
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (mkApp_spec p hC.db hC.af hC.ap hC.ia hC.ma n ⟨m, Locals.init []⟩ f x) h
  subst hs'
  obtain ⟨a', hrun, hS', hg⟩ := mkApp_stage hS.stage f x hW
  obtain ⟨hst, hden⟩ := ConRon.Bridge.Frontend.internE_sstep hck.state
    (ConRon.Bridge.viewOK_app (by rw [decE_eq, hf]; rfl) (by rw [decE_eq, hx]; rfl)) hrun
  refine ⟨_, _, hrun, StageT.of_leafI hS hS' hst (callW_leafFrame hcl (leaf_mem _ rfl) h), hg, rfl,
    hck.mono hst.ok hst.ext hst.caches hst.pins, hst.ext, ?_⟩
  rw [hden]
  simp only [denoteEView, decE_eq, ConRon.Bridge.denote_ext hf hst.ext,
    ConRon.Bridge.denote_ext hx hst.ext]
  rfl

/-- `mk_app`'s result is a handle. -/
theorem mkApp_hw (hC : CrpProg p) {n : Nat} {m m' : Mem} {a : AState} {f x : Word}
    {r : List Word} (hS : StageR vis fe m a) (h : callW p n "mk_app" [f, x] m = some (r, m')) :
    (r.headD 0).toNat < 2 ^ 32 := by
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (mkApp_spec p hC.db hC.af hC.ap hC.ia hC.ma n ⟨m, Locals.init []⟩ f x) h
  exact mkAppW_hw m a hS.check.arena f x _ _ hW

end leaves

/-! ## `reduce_pin_guard(vis, c)` -/

section rpg
variable {p : Prog} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
  {env : ConLeche.Env}

/-- **`reduce_pin_guard(vis, c)` refines `reducePinGuard`, both outcomes**, under `StageT` and
`CheckOK` (for the pin's interning): the pin (`rdp_simT`), the walks `loose_bvars_bounded_fast`
and `has_fvar_fast`, the declared universe parameters (none: `apdF_okT`), the constants
resolving (`crfF_okT`). -/
theorem rpg_ref (hC : CrpProg p) (hcl : LeafClosed p) (hap : ApdF p) (hcrf : L.Ind.CrfF p)
    (hkp : CrKeep p) (n : Nat) {m : Mem} {a : AState} {c : Word} {nm : ConLeche.Name}
    (hS : StageT dn vis fe m a) (hck : CheckOK false env fe a)
    (hnm : denoteN a.store.ns (decI c) = some nm) (hc : c.toNat < 2 ^ 32) (hCr : L.Stubs.CrOK m) :
    RefE (VerdictCtxU p) (reducePinGuardE p n m vis c) (reducePinGuard fe (decI c)) a
      (fun w x a' => StageT dn vis fe w.2 a' ∧ IWGrow m w.2 ∧ L.Stubs.CrOK w.2 ∧
        (w.1 != 0) = x) := by
  cases n with
  | zero => rw [reducePinGuardE.eq_1]; exact RefE.of_cls0 rfl
  | succ n =>
  rw [reducePinGuardE.arm1]
  simp only [reducePinGuard]
  -- the pin
  refine RefE.bindSim (fun _ => rfl) (rdp_simT hC hcl n hS hck hnm hc)
    fun r1 x1 m1 a1 h1 _ ⟨hS1, hg1, ⟨hl1, hx1⟩, _, _, _⟩ => ?_
  subst hx1
  rw [reducePinGuardE.k_reduce_decl_pin.arm1]
  have hCr1 := hkp.call (im_mem _ rfl) h1 hCr
  -- `loose_bvars_bounded_fast(4000000000, 0, p)`
  refine RefE.bindSim (fun _ => rfl)
    (fun r m' h => lbbF_okT dn vis fe 4000000000 0 (r1.headD 0) hl1 m1 m' a1 r h hS1)
    fun r2 x2 m2 a2 h2 _ ⟨hS2, hg2, hx2, _⟩ => ?_
  have hCr2 := CrOK.frame hCr1 (lbbF_frame h2) (by decide) (by decide)
  by_cases h20 : r2.headD 0 = 0
  · rw [reducePinGuardE.k_loose_bvars_bounded_fast.arm1 p n vis _ r2 m2 h20]
    have : x2 = false := by rw [← hx2, h20]; rfl
    subst this
    exact RefE.ret rfl ⟨hS2, hg1.trans hg2, hCr2, rfl⟩
  rw [reducePinGuardE.k_loose_bvars_bounded_fast.arm2 p n vis _ r2 m2 h20]
  have : x2 = true := by rw [← hx2]; simpa using h20
  subst this
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  -- `has_fvar_fast(4000000000, p)`
  refine RefE.bindSim (fun _ => rfl)
    (fun r m' h => hffF_okT dn vis fe 4000000000 (r1.headD 0) hl1 m2 m' a2 r h hS2)
    fun r3 x3 m3 a3 h3 _ ⟨hS3, hg3, hx3, _⟩ => ?_
  have hCr3 := CrOK.frame hCr2 (hffF_frame h3) (by decide) (by decide)
  by_cases h30 : r3.headD 0 = 0
  rotate_left
  · rw [reducePinGuardE.k_has_fvar_fast.arm1 p n vis _ r3 m3 h30]
    have : x3 = true := by rw [← hx3]; simpa using h30
    subst this
    exact RefE.ret rfl ⟨hS3, hg1.trans (hg2.trans hg3), hCr3, rfl⟩
  rw [reducePinGuardE.k_has_fvar_fast.arm2 p n vis _ r3 m3 h30]
  have : x3 = false := by rw [← hx3, h30]; rfl
  subst this
  simp only [Bool.false_eq_true, ite_false]
  -- `all_level_params_defined(0, 0, p)`
  refine RefE.bindCall (fun _ => rfl) (fun hG _ h4 => nvl hG.nv (by decide +kernel) h4)
    (fun b h4 => apdF_okT dn vis fe 0 0 (r1.headD 0) hl1 [] m3 b.2 a3 b.1 (apdF_of_callW hap h4)
      ⟨hS3, decHL_zero_zero m3, [], rfl⟩)
    fun r4 m4 x4 a4 h4 _ ⟨hS4, hg4, hx4, _⟩ => ?_
  have h4' := apdF_of_callW hap (callW_of_callE h4)
  have hCr4 := CrOK.frame hCr3 (apdF_frame h4') (by decide) (by decide)
  by_cases h40 : r4.headD 0 = 0
  · rw [reducePinGuardE.k_all_level_params_defined.arm1 p n vis _ r4 m4 h40]
    have : x4 = false := by rw [← hx4, h40]; rfl
    subst this
    exact RefE.ret rfl ⟨hS4, hg1.trans (hg2.trans (hg3.trans hg4)), hCr4, rfl⟩
  rw [reducePinGuardE.k_all_level_params_defined.arm2 p n vis _ r4 m4 h40]
  have : x4 = true := by rw [← hx4]; simpa using h40
  subst this
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  -- `consts_resolve_ffast(vis, p)`
  rw [← bind_pure (constsResolveFFast fe _)]
  refine RefE.bindCall (fun _ => rfl) (fun hG _ h5 => nvl hG.nv (by decide +kernel) h5)
    (fun b h5 => crfF_okT dn vis fe (r1.headD 0) hl1 m4 b.2 a4 b.1 (crfF_of_callW hcrf h5)
      ⟨hS4, hCr4.crMemo⟩)
    fun r5 m5 x5 a5 h5 _ ⟨⟨hS5, hg5, hx5, _⟩, hCr5⟩ => ?_
  rw [reducePinGuardE.k_consts_resolve_ffast.arm1]
  exact RefE.ret rfl ⟨hS5, hg1.trans (hg2.trans (hg3.trans (hg4.trans hg5))), hCr5.crOK, hx5⟩

end rpg

/-! ## `check_reduce_pin_pre(vis, c, v)` -/

section crpp
variable {p : Prog} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
  {env : ConLeche.Env}

/-- **`check_reduce_pin_pre(vis, c, v)` refines `checkReducePinPre`, both outcomes**, under
`StageT` and `CheckOK` (con-ron's `checkReducePinPre_bridge`'s decomposition): the element guard,
the pin's guards (`rpg_ref`), the value against the pin, the identity certificate; the three
guards and the spelling test decline, the certificate failing (con-ron's `internal`) and a
non-handle are plain aborts. -/
theorem crpp_ref (hC : CrpProg p) (hq : KnotStageProg p) (hcl : LeafClosed p) (hap : ApdF p)
    (hkp : CrKeep p) (hcrf : L.Ind.CrfF p) {a : AState} {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem}
    {c v : Word} {nm : ConLeche.Name} {x : ConLeche.Expr}
    (hS : StageT dn vis fe m a) (hck : CheckOK false env fe a) (henv : ConLeche.EnvWF env)
    (hnm : denoteN a.store.ns (decI c) = some nm) (hvx : denoteE a.store (decI v) = some x)
    (hws : ConLeche.Expr.WScoped 0 x) (hc : c.toNat < 2 ^ 32) (hv : v.toNat < 2 ^ 32)
    (hCr : L.Stubs.CrOK m) :
    RefE (VerdictCtxU p) (checkReducePinPreE p n m vis c v)
      (checkReducePinPre V fe (decI c) (decI v)) a
      (fun w _ a' => StageT dn vis fe w.2 a' ∧ IWGrow m w.2 ∧ L.Stubs.CrOK w.2 ∧
        CheckOK false env fe a' ∧ Ext a.store a'.store) := by
  have hknot := (CoreSpec.of_core).knot env fe henv
  cases n with
  | zero => rw [checkReducePinPreE.eq_1]; exact RefE.of_cls0 rfl
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [checkReducePinPreE.arm1]
  simp only [checkReducePinPre]
  -- the element inductive
  refine RefE.bindSim (fun _ => rfl) (reo_simT hC hcl n hS hck hnm hc)
    fun r1 x1 m1 a1 h1 _ ⟨hS1, hg1, ⟨hx1, _⟩, hck1, hext1, _⟩ => ?_
  have hCr1 := hkp.call (im_mem _ rfl) h1 hCr
  by_cases h10 : r1.headD 0 = 0
  · rw [checkReducePinPreE.k_reduce_elem_ok.abort1 p n vis c v r1 m1 h10]
    have : x1 = false := by rw [← hx1, h10]; rfl
    subst this
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact fun _ => ErrClaim.fail _ _ rfl
  rw [checkReducePinPreE.k_reduce_elem_ok.arm1 p n vis c v r1 m1 h10]
  have : x1 = true := by rw [← hx1]; simpa using h10
  subst this
  simp only [↓reduceIte]
  have hnm1 := ConRon.Bridge.denoteN_ext hnm hext1
  -- the pin's guards
  refine RefE.bindE (fun _ => checkReducePinPreE.k_reduce_pin_guard.none ..) id
    (rpg_ref hC hcl hap hcrf hkp n hS1 hck1 hnm1 hc hCr1)
    fun ⟨e2, m2⟩ x2 a2 hrun2 ⟨hS2, hg2, hCr2, hx2⟩ => ?_
  dsimp only at hS2 hg2 hCr2 hx2
  obtain ⟨hck2, hext2, -, hpg⟩ := ConRon.Bridge.reducePinGuard_run hck1 hnm1 hrun2
  by_cases h20 : e2 = 0
  · rw [checkReducePinPreE.k_reduce_pin_guard.abort1 p n vis c v e2 m2 h20]
    have : x2 = false := by rw [← hx2, h20]; rfl
    subst this
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact fun _ => ErrClaim.fail _ _ rfl
  rw [checkReducePinPreE.k_reduce_pin_guard.arm1 p n vis c v e2 m2 h20]
  have : x2 = true := by rw [← hx2]; simpa using h20
  subst this
  simp only [↓reduceIte]
  have hwsP : ConLeche.Expr.WScoped 0 (ConLeche.reduceDeclPin nm) := by
    refine ConLeche.Expr.WScoped.of_not_hasFvar ?_
    have hc2 := hpg.symm
    simp only [ConLeche.reducePinGuard, Bool.and_eq_true, Bool.not_eq_true'] at hc2
    exact hc2.1.1.2
  have hnm2 := ConRon.Bridge.denoteN_ext hnm1 hext2
  -- the pin
  refine RefE.bindSim (fun _ => rfl) (rdp_simT hC hcl n hS2 hck2 hnm2 hc)
    fun r3 x3 m3 a3 h3 _ ⟨hS3, hg3, ⟨hl3, hx3⟩, hck3, hext3, hden3⟩ => ?_
  subst hx3
  rw [checkReducePinPreE.k_reduce_decl_pin.arm1]
  have hCr3 := hkp.call (im_mem _ rfl) h3 hCr2
  have hext03 := (hext1.trans hext2).trans hext3
  have hv3 := ConRon.Bridge.denote_ext hvx hext03
  -- the value against the pin
  refine RefE.bindCall (fun _ => rfl)
    (fun hG _ h4 => hG.core.isDefEqCore n hn' hS3 0 v (r3.headD 0) hv hl3 _ h4)
    (fun b h4 => hq.isDefEqCore_sim n hn' hS3 0 v (r3.headD 0) hv hl3 b.1 b.2 h4)
    fun r4 m4 x4 a4 h4 hrun4 ⟨hS4, hg4, hx4⟩ => ?_
  have hCr4 := hkp.call (im_mem _ rfl) (callW_of_callE h4) hCr3
  obtain ⟨hck4, hext4, -, -⟩ := ConRon.Bridge.AM.of_run (P := fun t => t = a3) rfl hrun4
    (hknot.defeq a3 0 (decI v) (decI (r3.headD 0)) x _ hck3 hv3 hden3 hws hwsP)
  by_cases h40 : r4.headD 0 = 0
  · rw [checkReducePinPreE.k_is_def_eq_core.abort1 p n vis c v r4 m4 h40]
    have : x4 = false := by rw [← hx4]; simp only [decBool, h40]; rfl
    subst this
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact fun _ => ErrClaim.fail _ _ rfl
  rw [checkReducePinPreE.k_is_def_eq_core.arm1 p n vis c v r4 m4 h40]
  have : x4 = true := by rw [← hx4]; simpa [decBool] using h40
  subst this
  simp only [↓reduceIte]
  have hnm4 := ConRon.Bridge.denoteN_ext hnm2 (hext3.trans hext4)
  -- the certificate's variable
  refine RefE.bindSim (fun _ => rfl) (rcv_simT hC hcl n hS4 hck4 hnm4 hc)
    fun r5 x5 m5 a5 h5 _ ⟨hS5, hg5, hx5, hck5, hext5, hden5⟩ => ?_
  subst hx5
  have hCr5 := hkp.call (im_mem _ rfl) h5 hCr4
  by_cases h50 : 4294967296 ≤ r5.headD 0
  · rw [checkReducePinPreE.k_reduce_cert_var.abort1 p n vis v r5 m5 h50]
    exact RefE.of_cls0 rfl
  rw [checkReducePinPreE.k_reduce_cert_var.arm1 p n vis v r5 m5 h50]
  have hl5 : (r5.headD 0).toNat < 2 ^ 32 := by
    have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp h50); simpa using this
  have hv5 := ConRon.Bridge.denote_ext hv3 ((hext4.trans hext5))
  -- the application
  refine RefE.bindSim (fun _ => rfl) (mkApp_simT hC hcl n hS5 hck5 hv5 hden5)
    fun r6 x6 m6 a6 h6 _ ⟨hS6, hg6, hx6, hck6, hext6, hden6⟩ => ?_
  have hl6 := mkApp_hw hC hS5.stage h6
  subst hx6
  rw [checkReducePinPreE.k_mk_app.arm1]
  have hCr6 := hkp.call (im_mem _ rfl) h6 hCr5
  have hwsC : ConLeche.Expr.WScoped 1 (ConLeche.reduceCertVar nm) := by
    unfold ConLeche.reduceCertVar ConLeche.reduceElemTy
    split <;> simp [ConLeche.Expr.WScoped]
  have hwsA : ConLeche.Expr.WScoped 1 (.app x (ConLeche.reduceCertVar nm)) := by
    unfold ConLeche.Expr.WScoped
    exact ⟨ConLeche.Expr.WScoped.mono (by omega) hws, hwsC⟩
  -- the identity certificate
  refine RefE.bindCall (fun _ => rfl)
    (fun hG _ h7 => hG.core.isDefEqCore n hn' hS6 1 (r6.headD 0) (r5.headD 0) hl6 hl5 _ h7)
    (fun b h7 => hq.isDefEqCore_sim n hn' hS6 1 (r6.headD 0) (r5.headD 0) hl6 hl5 b.1 b.2 h7)
    fun r7 m7 x7 a7 h7 hrun7 ⟨hS7, hg7, hx7⟩ => ?_
  have hCr7 := hkp.call (im_mem _ rfl) (callW_of_callE h7) hCr6
  obtain ⟨hck7, hext7, -, -⟩ := ConRon.Bridge.AM.of_run (P := fun t => t = a6) rfl hrun7
    (hknot.defeq a6 1 (decI (r6.headD 0)) (decI (r5.headD 0)) _ _ hck6 hden6
      (ConRon.Bridge.denote_ext hden5 hext6) hwsA hwsC)
  by_cases h70 : r7.headD 0 = 0
  · rw [checkReducePinPreE.k_is_def_eq_core_2.abort1 p r7 m7 h70]
    exact RefE.of_cls0 rfl
  rw [checkReducePinPreE.k_is_def_eq_core_2.arm1 p r7 m7 h70]
  have : x7 = true := by rw [← hx7]; simpa [decBool] using h70
  subst this
  simp only [↓reduceIte]
  exact RefE.ret rfl ⟨hS7, hg1.trans (hg2.trans (hg3.trans (hg4.trans (hg5.trans (hg6.trans hg7))))),
    hCr7, hck7, (((hext03.trans hext4).trans hext5).trans hext6).trans hext7⟩

end crpp

/-! ## `check_reduce_pin(vis, q, c, v)` -/

/-- The own layer's row arrays of a name tag and tier. -/
theorem tierA_oix_cases (g : Nat) (t : UInt64) :
    tierA (oixArr g) t = OIXA ∨ tierA (oixArr g) t = OIXS ∨ tierA (oixArr g) t = OIXN ∨
      tierA (oixArr g) t = tier1 OIXA ∨ tierA (oixArr g) t = tier1 OIXS ∨
      tierA (oixArr g) t = tier1 OIXN := by
  unfold tierA oixArr; generalize (t &&& 1 != 0) = b
  cases b <;> split <;> (try split) <;> decide

/-- `reduce_op_cv_a`'s arrays are not the own rows. -/
theorem rcvaA_oix : ∀ b ∈ rcvaA, ∀ g t, b ≠ tierA (oixArr g) t := by
  intro b hb g t he
  have hb' := (List.mem_filter.mp hb).2
  simp only [decide_eq_true_eq] at hb'
  rcases tierA_oix_cases g t with h | h | h | h | h | h <;> rw [he, h] at hb' <;> simp at hb'

theorem rcvaC_stamp : (133 : Word) ∉ rcvaC := by
  intro h
  have := (List.mem_filter.mp h).2
  simp at this

/-- `TwinOK` across a leaf whose twin run is an interning step. -/
theorem TwinOK.leafI {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState} {fe : IFEnv}
    (h : TwinOK dn m a fe) (hs : ConRon.Bridge.Frontend.IStepS a a')
    (hf : MemFrame leafA leafC m m') : TwinOK dn m' a' fe :=
  h.of_istep hs (by rw [hf.size]; exact h.erec) (by rw [hf.size]; exact h.spn)
    (by rw [hf.size]; exact h.bstk)
    (h.memos.frame hf leafA_memo leafC_memo leafA_walk leafC_walk leafA_lp leafC_lp leafA_hb leafC_hb)

/-- `TwinOK` across a leaf that leaves the twin alone. -/
theorem TwinOK.leafSame {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {fe : IFEnv}
    (h : TwinOK dn m a fe) (hf : MemFrame leafA leafC m m') : TwinOK dn m' a fe :=
  h.frame hf leafA_memo leafC_memo leafA_walk leafC_walk leafA_lp leafC_lp leafA_hb leafC_hb

theorem pinW_leaf {m m' : Mem} (hf : MemFrame leafA leafC m m') : pinW m' 0 = pinW m 0 := by
  have hP : m'.arr64 PINS = m.arr64 PINS := hf.arr PINS leafA_pins (by decide)
  simp only [pinW, hP]

section crp
variable {p : Prog} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
  {env : ConLeche.Env}

/-- **`check_reduce_pin(vis, q, c, v)` refines `checkReducePin`, both outcomes** (con-ron's
`checkReducePin_bridge`'s decomposition), under `StageT` and `CheckOK`: the record `q` (the
opaque `ci`, named `c`) pushed, the stored constant read at the pushed view (`StepOK` there), the
displaced row put back (`env_pop_temp`: the push the newest, its displaced row older and no
other name's, `EnvR.popTemp`), then `crpp_ref` at the popped index, which is `fe`'s view. -/
theorem crp_ref (hC : CrpProg p) (hq : KnotStageProg p) (hcl : LeafClosed p) (hap : ApdF p)
    (hkp : CrKeep p) (hcrf : L.Ind.CrfF p) {env2 : ConLeche.Env} {a : AState} {n : Nat}
    (hn : n ≤ 2 ^ 62) {m : Mem} {q c v : Word} {ci : IConstantInfo} {nm : ConLeche.Name}
    {x : ConLeche.Expr} (hS : StageT dn vis fe m a) (hck : CheckOK false env fe a)
    (henv : ConLeche.EnvWF env) (hok2 : StepOK env2 (fe.push ci) a)
    (hci : decCI (erecP m) q.toNat = some ci) (hcn : ci.name = decI c)
    (hnm : denoteN a.store.ns (decI c) = some nm) (hvx : denoteE a.store (decI v) = some x)
    (hws : ConLeche.Expr.WScoped 0 x) (hc : c.toNat < 2 ^ 32) (hv : v.toNat < 2 ^ 32)
    (hCr : L.Stubs.CrOK m) :
    RefE (VerdictCtxU p) (checkReducePinE p n m vis q c v)
      (checkReducePin V fe ci (decI c) (decI v)) a
      (fun w fe' a' => StageT dn w.1 fe' w.2 a' ∧ IWGrow m w.2 ∧ L.Stubs.CrOK w.2 ∧
        CheckOK false env fe' a' ∧ Ext a.store a'.store ∧ ConRon.Bridge.IFEnv.SameView fe' fe) := by
  have hE := hS.stage.check.env
  have hcw : (decI c : NIdx).word.toUInt64 = c := decI_word_self c hc
  cases n with
  | zero => rw [checkReducePinE.eq_1]; exact RefE.of_cls0 rfl
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [checkReducePinE.arm1]
  simp only [checkReducePin]
  -- the displaced row
  refine RefE.onlySim (fun _ => checkReducePinE.k_env_row_get.none ..) (fun _ _ h => h)
    fun r1 m1 h1 => ?_
  obtain ⟨s1, rfl, hm1, -, hr1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envRowGet_spec p hC.red.erg n _ c) h1
  rw [checkReducePinE.k_env_row_get.arm1, hm1, hr1]
  simp only [List.headD_cons, List.tail_cons]
  generalize hrc : (ownRaw m c).1 = rc
  generalize hrq : (ownRaw m c).2 = rq
  -- the push
  refine RefE.onlySim (fun _ => checkReducePinE.k_env_push.none ..) (fun _ _ h => h)
    fun r2 m2 h2 => ?_
  rw [checkReducePinE.k_env_push.arm1]
  obtain ⟨hS2, hg2⟩ := envPush_stage hC.ef h2 hS.stage hci
  obtain ⟨hO2, hr2, hvlt⟩ := envPush_ownC hC.ef h2 hE hci (by have := hS.stage.iw.ctl; omega)
  rw [hr2] at hS2 ⊢
  simp only [List.headD_cons] at hS2 ⊢
  have hf2 := callW_leafFrame hcl (leaf_mem _ rfl) h2
  have hCr2 := hkp.call (im_mem _ rfl) h2 hCr
  have hv1 : (vis + 1).toNat = vis.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  -- the stored constant at the pushed view
  have hsim3 : Sim (callW p n "reduce_stored_ok" [vis + 1, c] m2)
      (reduceStoredOk (fe.push ci) (decI c)) a
      (fun r b m' a' => StageR (vis + 1) (fe.push ci) m' a' ∧ IWGrow m2 m' ∧ decW0B m' r b ∧
        ConRon.Bridge.Frontend.IStepS a a') := by
    intro r m' h
    obtain ⟨s', hs', -, hok, hS', hg, hd⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
      (reduceStoredOk_refines p hC.red (vis + 1) (fe.push ci) c hc n ⟨m2, Locals.init []⟩ a hS2) h
    subst hs'
    have hrun := AM.run_of_ok _ _ hok
    obtain ⟨hst, -⟩ := ConRon.Bridge.reduceStoredOk_run hck.state hck.pins hok2.ienv hnm _ _ hrun
    exact ⟨_, _, hrun, hS', hg, hd, hst⟩
  refine RefE.bindSim (fun _ => rfl) hsim3 fun r3 x3 m3 a3 h3 _ ⟨hS3, hg3, ⟨hx3, _⟩, hst3⟩ => ?_
  rw [checkReducePinE.k_reduce_stored_ok.arm1]
  have hCr3 := hkp.call (im_mem _ rfl) h3 hCr2
  have hf3 := callW_leafFrame hcl (leaf_mem _ rfl) h3
  obtain ⟨s3', hs3', -, hW3⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
    (rso_specW p hC.red.rso n _ (vis + 1) c) h3
  have hfr3 : MemFrame rcvaA rcvaC m2 m3 := by
    have := rsoW_frame hC.red hC.rcva hW3; rwa [hs3'] at this
  have hO3 : ownC m3 = ownC m2 := ownC_frame hfr3 rcvaA_oix rcvaC_stamp
  -- the pop's preconditions
  have hOc : ∀ k : NIdx, ownC m3 k = if k = decI c then vis + 1 else ownC m k := by
    intro k; rw [hO3, hO2, hcn]; rfl
  have htop : (ownRaw m3 c).1 = vis + 1 := by
    have := hOc (decI c); simp only [ownC, hcw, ite_true] at this; exact this
  have hrcm : ownC m (decI c) = rc := by simp only [ownC, hcw, hrc]
  have hg03 : IWGrow m m3 := hg2.trans hg3
  have hcv : rc ≠ 0 → rc.toNat - 1 < (vis + 1).toNat - 1 := by
    intro h0
    have := hE.fresh (decI c) (by rw [hcw, hrc]; exact h0)
    rw [hcw, hrc] at this; rw [hv1]; omega
  have hcd : rc ≠ 0 → ∃ ci', decCI (erecP m3) rq.toNat = some ci' := by
    intro h0
    obtain ⟨ci', hci'⟩ := hE.own_dec (decI c) (by rw [hcw, hrc]; exact h0)
    rw [hcw, hrq] at hci'
    exact ⟨ci', ArrExt.decCI (L.Ind.IWGrow.ext hg03) hci'⟩
  have hfree : rc ≠ 0 → ∀ k : NIdx, k.word.toUInt64 ≠ c → (ownRaw m3 k.word.toUInt64).1 ≠ rc := by
    intro h0 k hk e
    have hkc : k ≠ decI c := fun h => hk (by rw [h, hcw])
    have h1 := hOc k
    simp only [ownC, hkc, ite_false] at h1
    rw [h1] at e
    exact hkc (hE.uniq k (decI c) (by rw [e]; exact h0) (by rw [e, hcw, hrc]))
  have hrc32 : rc.toNat < 2 ^ 32 := by rw [← hrc]; exact ownRaw_fst_lt m c
  -- the pop
  refine RefE.onlySim (fun _ => checkReducePinE.k_env_pop_temp.none ..) (fun _ _ h => h)
    fun r4 m4 h4 => ?_
  obtain ⟨s4, rfl, -, hr4, hE4, hm4⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (envPopTemp_refines p hC.rs hC.pop n _ (vis + 1) c rc rq hS3.check.env hc
      (by intro h0; have := congrArg UInt64.toNat h0; rw [hv1] at this; simp at this)
      htop hrc32 hcv hcd hfree) h4
  simp only at hE4 hm4
  have hprev : (if rc = 0 then none else decCI (erecP m3) rq.toNat) = fe.idx[(decI c : NIdx)]? := by
    obtain ⟨he, hd⟩ := prevD_eq (rec3PrevD hE hc)
    rw [← he, hrc, hrq]
    split
    · rfl
    · rename_i h0
      obtain ⟨ci', hci'⟩ := hd (by rw [hrc]; exact h0)
      rw [hrq] at hci'
      rw [hci', ArrExt.decCI (L.Ind.IWGrow.ext hg03) hci']
  rw [hprev, ← hcn] at hE4
  have hsv := ConRon.Bridge.IFEnv.sameView_popTemp fe ci
  generalize hfe' : (fe.push ci).popTemp ci.name fe.idx[ci.name]? = fe' at hE4 hsv
  rw [hm4] at hE4
  obtain ⟨hS4R, hg4⟩ := StageR.of_own hS3 hE4
  rw [← hm4] at hS4R hg4
  have hf4 := callW_leafFrame hcl (leaf_mem _ rfl) h4
  have hCr4 := hkp.call (im_mem _ rfl) h4 hCr3
  have hvv : vis + 1 - 1 = vis := by simp
  rw [hvv] at hS4R
  -- the flags set back
  rw [checkReducePinE.k_env_pop_temp.arm1]
  refine RefE.onlySim (fun _ => checkReducePinE.k_env_set_flags.none ..) (fun _ _ h => h)
    fun r45 m45 h45 => ?_
  obtain ⟨hS45R, hg45, -⟩ := L.Ind.setFlags_stage hC.ef hS4R hE.natLit hE.strLit h45
  have hf45 := callW_leafFrame hcl (leaf_mem _ rfl) h45
  have hCr45 := hkp.call (im_mem _ rfl) h45 hCr4
  have hT4 : TwinOK dn m45 a3 (fe'.setFlags fe.natLit fe.strLit) :=
    ((((hS.twin.leafSame hf2).leafI hst3 hf3).leafSame hf4).leafSame hf45).sameView hsv
  have hflag : pinW m45 0 ≠ 0 := by
    rw [pinW_leaf hf45, pinW_leaf hf4, pinW_leaf hf3, pinW_leaf hf2]; exact hS.flag
  have hS4 : StageT dn vis (fe'.setFlags fe.natLit fe.strLit) m45 a3 := ⟨hS45R, hT4, hflag⟩
  have hck4 : CheckOK false env (fe'.setFlags fe.natLit fe.strLit) a3 :=
    (hck.mono hst3.ok hst3.ext hst3.caches hst3.pins).congr_find hsv.find hsv.tbls hsv.base
      (hsv.flags hck.ienv.flags)
  -- the stored test
  by_cases h30 : r3.headD 0 = 0
  · rw [checkReducePinE.k_env_set_flags.abort1 p n c v _ _ r45 m45 h30]
    have : x3 = false := by rw [← hx3, h30]; rfl
    subst this
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact fun _ => ErrClaim.fail _ _ rfl
  rw [checkReducePinE.k_env_set_flags.arm1 p n c v _ _ r45 m45 h30, hr4, List.headD_cons, hvv]
  have : x3 = true := by rw [← hx3]; simpa using h30
  subst this
  simp only [↓reduceIte]
  rw [show (fe.push ci).popTemp (decI c) fe.idx[(decI c : NIdx)]? = fe' by rw [← hcn]; exact hfe']
  -- the body at the popped index
  refine RefE.bindE (fun _ => checkReducePinE.k_check_reduce_pin_pre.none ..) id
    (crpp_ref hC hq hcl hap hkp hcrf hn' hS4 hck4 henv
      (ConRon.Bridge.denoteN_ext hnm hst3.ext) (ConRon.Bridge.denote_ext hvx hst3.ext) hws hc hv
      hCr45)
    fun ⟨z, m5⟩ _ a5 _ ⟨hS5, hg5, hCr5, hck5, hext5⟩ => ?_
  rw [checkReducePinE.k_check_reduce_pin_pre.arm1]
  exact RefE.ret rfl ⟨hS5, hg2.trans (hg3.trans (hg4.trans (hg45.trans hg5))), hCr5, hck5,
    hst3.ext.trans hext5, hsv⟩

end crp

/-! ## The opaque arm -/

/-- The lookups of the opaque arm. -/
structure OpqArmProg (p : Prog) : Prop where
  cdo : p.lookup "check_decl_opaque" = some checkDeclOpaque
  ccv : CcvProg p
  crp : CrpProg p

set_option experimental.vcgen true in
/-- **The model of `check_decl_opaque(i, vis)`, both outcomes**: `erec_ci` and the pin reads
through their runs, `check_constant_val`, `check_opaque_val` and `check_reduce_pin` by their
unified models, `env_push` through `callE`. -/
l_model checkDeclOpaque_specE (p : Prog) (hX : OpqArmProg p)
  fns [hX.cdo ↦ checkDeclOpaqueE]
  specs [erecCi_specW p hX.ccv.val.rcp n, checkConstantVal_specE p hX.ccv n,
    checkOpaqueVal_specE p hX.ccv.val n, pinAt_specW p hX.crp.red.pa n,
    checkReducePin_specE p hX.crp n, callW_spec p n "env_push"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **The opaque arm `check_decl_opaque` refines `checkDeclKind` on an opaque under `StageT`, both
outcomes** (con-ron's `checkDecl_bridge_opaque`): the record into `EREC` (`erec_ci(i, 0)`), the
constant check (`ccv_ref`, `allow = 0`), the opaque check (`checkOpaqueVal_ref`), for
`Lean.reduceNat`/`Lean.reduceBool` the reduce-pin gate (`crp_ref`, con-ron's invariants after the
two checks from the fold invariant), the push. -/
theorem cdo_ref {p : Prog} (hX : OpqArmProg p) (hq : KnotStageProg p) (hcl : LeafClosed p)
    (hap : ApdF p) (hkp : CrKeep p) (hcrf : L.Ind.CrfF p) {dn : NIdx → Option ConLeche.Name}
    (hC : CcvSims p dn) {vis : Word} {fe : IFEnv} {a : AState} {n : Nat} (hn : n ≤ 2 ^ 62)
    {m : Mem} {i : Word} {ds : Array IDeclaration} {pins : List INatOpPinSet} {cv : IConstantVal}
    {v : EIdx} (hS : StageT dn vis fe m a) (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds)
    (hi : i.toNat < ds.size) (hd : ds[i.toNat] = .opaqueDecl cv v) {c : ConLeche.ConstantVal}
    {x : ConLeche.Expr} (hcvd : Frontend.denoteCV a.store cv = some c)
    (hvd : denoteE a.store v = some x)
    (hF : ∃ env, ConRon.Bridge.FoldOK env fe a) (hCr : L.Stubs.CrOK m) :
    RefE (VerdictCtxU p) (checkDeclOpaqueE p n m i vis) (checkDeclKind V pins fe (.opaqueDecl cv v)) a
      (fun w fe' a' => CdaPost dn m w.1 w.2 fe' a') := by
  obtain ⟨env, hFo⟩ := hF
  cases n with
  | zero => rw [checkDeclOpaqueE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [checkDeclOpaqueE.eq_2]
  unfold checkDeclKind
  simp only []
  -- `erec_ci(i, 0)`
  refine RefE.onlySim (fun _ => checkDeclOpaqueE.k_erec_ci.none ..) (fun _ _ h => h)
    fun r1 m1 h1 => ?_
  rw [checkDeclOpaqueE.k_erec_ci.arm1]
  have hCr1 := CrOK.frame hCr (erecCiW_frame h1) (by decide) (by decide)
  obtain ⟨hT1, hg1, hci1, hcv1, hv1, -⟩ :=
    erecCiW_okT (ci := .axiomInfo cv) h1 hS hD hi (by rw [hd]; rfl)
  rw [hd] at hcv1 hv1
  simp only [stepCV, stepVal] at hcv1 hv1
  generalize r1.headD 0 = q at hci1 hcv1 hv1 ⊢
  obtain ⟨wn, hwn, hwnl, hname0⟩ := decCV_name hcv1
  obtain ⟨wt, hwt, -, -⟩ := (decCV_words hcv1).2.2
  have hq1 : (q + CI.cv).toNat = q.toNat + CI.cv.toNat :=
    off_add_toNat rfl (by have := erecP_lt64 hwt; omega)
  have hcv1' : decCV (erecP m1) (q + CI.cv).toNat = some cv := by rw [hq1]; exact hcv1
  obtain ⟨wv, hwv, hwvl, rfl⟩ := hd?_some hv1
  have exn : rdW (m1.arr64 (L.tierA EREC ((q + (CI.cv + CV.name)) >>> 40)))
      (q + (CI.cv + CV.name) &&& 1099511627775) = wn :=
    (erRdOK m1).at _ CI.cv_name_toNat hwn
  have exv : rdW (m1.arr64 (L.tierA EREC ((q + CI.defnValue) >>> 40))) (q + CI.defnValue &&& 1099511627775) =
      wv := (erRdOK m1).at _ rfl hwv
  rw [exn, exv]
  -- the constant check
  have hcc := ccv_ref hX.ccv hq hap hkp hcrf hC hn' hT1 hcv1' hcvd hCr1 (allow := 0)
  rw [show ((0 : Word) != 0) = false from rfl] at hcc
  refine RefE.bindE (fun _ => checkDeclOpaqueE.k_check_constant_val.none ..) id hcc
    fun ⟨r3, m3⟩ _ a3 hrun3 hP3 => ?_
  rw [checkDeclOpaqueE.k_check_constant_val.arm1]
  dsimp only at hP3
  obtain ⟨hstep1, F1, hpure1⟩ :=
    ConRon.Bridge.checkConstantVal_bridge_of_fold ConRon.Bridge.CoreSpec.of_core hFo hcvd hrun3
  have hcA := ConRon.Bridge.denoteCV_ext hcvd hstep1.ext
  have hok1 := hFo.ofCore hstep1
  have hv1x := ConRon.Bridge.denote_ext hvd hstep1.ext
  have hg3 := hP3.grow
  -- the opaque check
  refine RefE.bindE (fun _ => checkDeclOpaqueE.k_check_opaque_val.none ..) id
    (checkOpaqueVal_ref hX.ccv hq hap hkp hcrf hn' hP3.stage
      (ArrExt.decCV (L.Ind.IWGrow.ext hg3) hcv1) (hg3.ext _ _ hwv) hwvl ⟨_, hcA⟩ hP3.crOK)
    fun ⟨r4, m4⟩ ci4 a4 hrun4 ⟨hP4, hr4, hci4⟩ => ?_
  dsimp only at hP4 hr4 hci4
  subst r4 ci4
  rw [checkDeclOpaqueE.k_check_opaque_val.arm1]
  obtain ⟨hstep2, -, hci2, hcw2, hsh2, F2, hpure2⟩ :=
    ConRon.Bridge.checkOpaqueVal_bridge ConRon.Bridge.CoreSpec.of_core hok1 hcA
      (ConRon.Bridge.checkConstantVal_typeWF hpure1) hv1x hrun4
  have hok2 := hok1.ofCore hstep2
  have hname : cv.name = decI wn := hname0
  have hnm2 : denoteN a4.store.ns (decI wn) = some c.name := by
    rw [← hname]
    exact ConRon.Bridge.denoteN_ext (ConRon.Bridge.denoteCV_inv hcA).1 hstep2.ext
  have hv2 := ConRon.Bridge.denote_ext hv1x hstep2.ext
  have hg4 := hP4.grow
  have hS4 := hP4.stage
  have hP14 : ArrExt (erecP m1) (erecP m4) := L.Ind.IWGrow.ext (hg3.trans hg4)
  -- a push of the opaque at the view `u`
  have push : ∀ {u : Word} {fe' : IFEnv} {mx : Mem} {ax : AState}, StageR u fe' mx ax →
      IWGrow m4 mx → CoreMemos mx →
      RefE (VerdictCtxU p) (checkDeclOpaqueE.j1 p n q u mx)
        (pure (fe'.push (.axiomInfo cv)) : AM IFEnv) ax
        (fun w fe'' a' => CdaPost dn m w.1 w.2 fe'' a') := by
    intro u fe' mx ax hSx hgx hMx
    rw [checkDeclOpaqueE.j1.arm1]
    refine RefE.onlySim (fun _ => checkDeclOpaqueE.k_env_push.none ..) (fun _ _ h => h)
      fun ry my e => ?_
    rw [checkDeclOpaqueE.k_env_push.arm1]
    obtain ⟨hSy, hgy⟩ := push_call hX.ccv.val.rcp e hSx
      (ArrExt.decCI (L.Ind.IWGrow.ext hgx) (ArrExt.decCI hP14 hci1))
    exact RefE.ret rfl ⟨by simpa using hSy, leaf_memos hcl (leaf_mem _ rfl) e hMx,
      hg1.trans (hg3.trans (hg4.trans (hgx.trans hgy)))⟩
  -- the reduce operations' pins
  refine RefE.onlySim (fun _ => checkDeclOpaqueE.k_pin_at.none ..) (fun _ _ h => h)
    fun r5 m5 h5 => ?_
  rw [checkDeclOpaqueE.k_pin_at.arm1]
  obtain ⟨hm5, hr5, hl5, hrun5⟩ := pinAtW_ok h5 hS4.stage.check.pins
  subst m5 r5
  refine RefE.onlySim (fun _ => checkDeclOpaqueE.k_pin_at_2.none ..) (fun _ _ h => h)
    fun r6 m6 h6 => ?_
  obtain ⟨hm6, hr6, hl6, hrun6⟩ := pinAtW_ok h6 hS4.stage.check.pins
  subst m6 r6
  simp only [List.headD_cons]
  have hnames : (reduceOpNames).run a4 =
      .ok ([decI (pinW m4 (1 + (43 : Word).toNat)), decI (pinW m4 (1 + (44 : Word).toNat))], a4) := by
    simp only [reduceOpNames, reduceNatName, reduceBoolName, pinReduceNat, pinReduceBool,
      StateT.run_bind, show PIN_REDUCE_NAT = (43 : Word).toNat from rfl,
      show PIN_REDUCE_BOOL = (44 : Word).toNat from rfl, hrun5, L.Arena.except_ok_bind, hrun6]
    rfl
  refine RefE.bind_right hnames ?_
  have hb43 := decI_beq (k := .name) wn (pinW m4 (1 + (43 : Word).toNat)) hwnl hl5
  have hb44 := decI_beq (k := .name) wn (pinW m4 (1 + (44 : Word).toNat)) hwnl hl6
  rw [hname]
  by_cases hop : wn = pinW m4 (1 + (43 : Word).toNat) ∨ wn = pinW m4 (1 + (44 : Word).toNat)
  · rw [checkDeclOpaqueE.k_pin_at_2.arm1 p n q wn wv vis _ _ m4 hop]
    have hcont : ([decI (pinW m4 (1 + (43 : Word).toNat)), decI (pinW m4 (1 + (44 : Word).toNat))] :
        List NIdx).contains (decI wn) = true := by
      simp only [List.contains_cons, List.contains_nil, Bool.or_false, hb43, hb44]
      simpa using hop
    rw [ite_eq_left hcont]
    -- the reduce-pin gate
    have hok2' := hok2.toStepOK.push hok2.check.state hci2 hsh2 hcw2
      (hr := ConLeche.RuleWF.of_not_rec (fun _ _ _ _ _ heq => nomatch heq))
    refine RefE.bindE (fun _ => checkDeclOpaqueE.k_check_reduce_pin.none ..) id
      (crp_ref hX.crp hq hcl hap hkp hcrf hn' hS4 hok2.check hok2.envWF hok2'
        (ArrExt.decCI hP14 hci1) hname hnm2 hv2
        (ConLeche.Expr.WScoped.of_not_hasFvar (ConRon.Bridge.checkOpaqueVal_noFvar hpure2))
        hwnl hwvl hP4.crOK)
      fun ⟨u, m7⟩ fe7 a7 _ ⟨hS7, hg7, _, _, _, _⟩ => ?_
    rw [checkDeclOpaqueE.k_check_reduce_pin.arm1]
    exact push hS7.stage hg7 hS7.twin.memos
  · rw [checkDeclOpaqueE.k_pin_at_2.arm2 p n q wn wv vis _ _ m4 hop]
    have hcont : ([decI (pinW m4 (1 + (43 : Word).toNat)), decI (pinW m4 (1 + (44 : Word).toNat))] :
        List NIdx).contains (decI wn) = false := by
      simp only [List.contains_cons, List.contains_nil, Bool.or_false, hb43, hb44]
      simpa using hop
    rw [ite_eq_right (by rw [hcont]; decide)]
    exact RefE.bind_right rfl (push hS4.stage (IWGrow.refl _) hS4.twin.memos)

end L.Arena
