import ConAgua.Arena.DeclArmT
import ConAgua.Arena.RecGenSpec.CruleProg
import ConAgua.Arena.DeclReducePin

/-!
# The reduce-pin gate and the opaque arm under `StageC` (lane `loopt2`)

`check_reduce_pin` (`DeclReducePin.lean`) runs after the opaque's push, interning between its two
core calls: `TwinOK` cannot be tracked on the L side there (landing 6). It runs here under `StageC`
(`TwinStep.lean`): the stage relation, con-ron's `CheckOK`, the memory's half of `TwinOK`, the pin
flag. Mirrors con-ron's `checkReducePin_bridge`:

* the leaves (`reduce_stored_ok`, `reduce_elem_ok`, `reduce_decl_pin`, `reduce_cert_var`, `mk_app`)
  by `StageC.of_leaf`: their `StageR` refinements, the leaves' write set (`LeafClosed`), con-ron's
  `IStepS` (`reduceStoredOk_run`, `reduceElemOk_run`, `reduceDeclPin_run`, `reduceCertVar_run`,
  `Frontend.internE_sstep`);
* `reduce_pin_guard` (`rpgW_okC`): its leaf `reduce_decl_pin` as above, then the walks' `StageT`
  contracts (`IndStubsT.lean`), and `CheckOK` after from con-ron's `reducePinGuard_run`;
* the two `is_def_eq_core` calls by the knot's `StageT` sim and `CheckOK` after from con-ron's
  `KnotSpec.defeq` (`StageC.of_T`).

The opaque arm (`cdo_ref`) carries con-ron's fold invariant `FoldOK` from its entry across the
constant check (`checkConstantVal_bridge_of_fold`) and the value check (`checkOpaqueVal_bridge`),
as con-ron's `checkDecl_bridge_opaque` does; the gate's `CheckOK` at the restricted pushed index
is `CheckOK.congr_find` of it (`restrict_pushed_find`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


noncomputable section

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF)
open ConRon.Bridge (CheckOK StepOK FoldOK CoreSpec)

local notation "V" => ConLeche.CheckMode.verified

theorem leafA_app : ∀ b ∈ ([AREC, ASLOT, ADER, tier1 AREC, tier1 ASLOT, tier1 ADER] : List TieredArray),
    b ∈ leafA := by
  decide +kernel
theorem leafC_app₀ : (4 : Word) ∈ leafC ∧ (5 : Word) ∈ leafC := by decide +kernel
/-- By cases: `decide +kernel` on the bounded form over `Word` takes >16 GB. -/
theorem leafC_app : ∀ x ∈ ([4, 5] : List Word), x ∈ leafC := by
  intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl
  · exact leafC_app₀.1
  · exact leafC_app₀.2

/-- `mk_app`'s frame is a leaf's. -/
theorem mkAppW_leafFrame {m m' : Mem} {f x r : Word} (h : mkAppW m f x = some (r, m')) :
    MemFrame leafA leafC m m' :=
  (mkAppW_frame m m' f x r h).mono leafA_app leafC_app

/-- `check_opaque_val` is one of the loop's functions. -/
theorem checkOpaqueVal_loop : "check_opaque_val" ∈ loopFns := loop_mem _ rfl

/-- `StageC` after a twin run, from `StageT` after it and con-ron's `CheckOK` from the start. -/
theorem rpg_fin {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
    {m : Mem} {a a' : AState} {c : Word} {cn : ConLeche.Name} {x : Bool}
    (hck : CheckOK V env fe a) (hd : denoteN a.store.ns (decI c) = some cn)
    (hrun : (reducePinGuard fe (decI c)).run a = .ok (x, a')) (hT : StageT dn vis fe m a') :
    StageC dn vis fe env m a' ∧ Ext a.store a'.store ∧
      x = ConLeche.reducePinGuard env cn := by
  obtain ⟨hck', hx, -, hr⟩ := ConRon.Bridge.reducePinGuard_run hck hd hrun
  exact ⟨StageC.of_T hT hck', hx, hr⟩

/-- **`reduce_pin_guard` under `StageC`** (`reducePinGuard_refines`'s): the pin by
`StageC.of_leaf`, the walks by their `StageT` contracts, `CheckOK` after by con-ron's
`reducePinGuard_run`. -/
theorem rpgW_okC {p : Prog} (hpa : p.lookup "pin_at" = some pinAtL)
    (hpd : p.lookup "reduce_decl_pin" = some reduceDeclPinL) (hR : L.Rom.RomRefs p)
    (hcl : LeafClosed p) (hap : ApdF p) (hck : CrKeep p) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv}
    {env : ConLeche.Env} {a : AState} {n : Nat} {m m' : Mem} {c : Word} {r : List Word}
    {cn : ConLeche.Name}
    (h : rpgW p (realCall p) n m vis c = some (r, m')) (hS : StageC dn vis fe env m a) (hc : c.toNat < 2 ^ 32)
    (hd : denoteN a.store.ns (decI c) = some cn) (hCr : L.Stubs.CrOK m) :
    ∃ x a', (reducePinGuard fe (decI c)).run a = .ok (x, a') ∧ StageC dn vis fe env m' a' ∧
      Ext a.store a'.store ∧ x = ConLeche.reducePinGuard env cn ∧
      IWGrow m m' ∧ decW0B m' r x := by
  cases n with
  | zero => simp [rpgW] at h
  | succ n =>
  rw [rpgW_step] at h
  cases h1 : callW p n "reduce_decl_pin" [c] m with
  | none => rw [h1] at h; cases h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, rpgK1_some] at h
  have hCr1 := hck.call (im_mem _ rfl) h1 hCr
  obtain ⟨s1, hs1, -, hok1, hS1, hg1, he1l, he1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (reduceDeclPin_refines p hpa n ⟨m, Locals.init []⟩ a dn fe vis c hS.stage hc hR hpd) h1
  subst hs1
  have hrun1 := AM.run_of_ok _ _ hok1
  obtain ⟨hi1, -⟩ := ConRon.Bridge.reduceDeclPin_run hS.check.state hS.check.pins hd hrun1
  have hC1 := StageC.of_leaf hS hS1 (callW_leafFrame hcl (leaf_mem _ (by decide)) h1) hi1
  have hT1 := hC1.stageT
  generalize AM.st (reduceDeclPin (decI c)) a = a1 at hrun1 hT1
  rw [← he1] at hrun1
  generalize r1.headD 0 = e at h hrun1 he1l
  have h00 : (0 : Word).toNat = 0 := rfl
  have hF : (4000000000 : Word).toNat = coreWalkFuel := rfl
  -- `loose_bvars_bounded_fast`
  cases h2 : lbbF s1.mem [4000000000, 0, e] with
  | none => rw [h2] at h; simp [rpgK2] at h
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2, rpgK2_some] at h
  have hCr2 := CrOK.frame hCr1 (lbbF_frame h2) (by decide) (by decide)
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2, -⟩ :=
    lbbF_okT dn vis fe 4000000000 0 e he1l s1.mem m2 a1 r2 h2 hT1
  rw [hF, h00] at hrun2
  by_cases hb2 : r2.headD 0 = 0
  · rw [ite_eq_left hb2] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ex2 : x2 = false := by rw [← hx2]; simpa using hb2
    have hrun : (reducePinGuard fe (decI c)).run a = .ok (false, a2) := by
      simp only [reducePinGuard, StateT.run_bind, hrun1, exc_ok_bind', hrun2, ex2, Bool.not_false,
        ite_true, StateT.run_pure]
      rfl
    obtain ⟨hC, hx, hr⟩ := rpg_fin hS.check hd hrun hS2
    exact ⟨false, a2, hrun, hC, hx, hr, hg1.trans hg2, by simp [decW0B]⟩
  rw [ite_eq_right hb2] at h
  have ex2 : x2 = true := by rw [← hx2]; simpa using hb2
  -- `has_fvar_fast`
  cases h3 : hffF m2 [4000000000, e] with
  | none => rw [h3] at h; simp [rpgK3] at h
  | some rm3 =>
  obtain ⟨r3, m3⟩ := rm3
  rw [h3, rpgK3_some] at h
  have hCr3 := CrOK.frame hCr2 (hffF_frame h3) (by decide) (by decide)
  obtain ⟨x3, a3, hrun3, hS3, hg3, hx3, -⟩ :=
    hffF_okT dn vis fe 4000000000 e he1l m2 m3 a2 r3 h3 hS2
  rw [hF] at hrun3
  by_cases hb3 : r3.headD 0 ≠ 0
  · rw [ite_eq_left hb3] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ex3 : x3 = true := by rw [← hx3]; simpa using hb3
    have hrun : (reducePinGuard fe (decI c)).run a = .ok (false, a3) := by
      simp only [reducePinGuard, StateT.run_bind, hrun1, exc_ok_bind', hrun2, ex2, Bool.not_true,
        Bool.false_eq_true, ite_false, hrun3, ex3, ite_true, StateT.run_pure]
      rfl
    obtain ⟨hC, hx, hr⟩ := rpg_fin hS.check hd hrun hS3
    exact ⟨false, a3, hrun, hC, hx, hr, hg1.trans (hg2.trans hg3), by simp [decW0B]⟩
  rw [ite_eq_right hb3] at h
  have ex3 : x3 = false := by rw [← hx3]; simpa using hb3
  -- `all_level_params_defined`
  cases h4 : realCall p n "all_level_params_defined" [0, 0, e] m3 with
  | none => rw [h4] at h; simp [rpgK4] at h
  | some rm4 =>
  obtain ⟨r4, m4⟩ := rm4
  rw [h4, rpgK4_some] at h
  have hCr4 := CrOK.frame hCr3 (apdF_frame (apdF_of_callW hap h4)) (by decide) (by decide)
  obtain ⟨x4, a4, hrun4, hS4, hg4, hx4, -⟩ :=
    apdF_okT dn vis fe 0 0 e he1l [] m3 m4 a3 r4 (apdF_of_callW hap h4)
      ⟨hS3, by simp [decHL, hslice?], [], rfl⟩
  by_cases hb4 : r4.headD 0 = 0
  · rw [ite_eq_left hb4] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ex4 : x4 = false := by rw [← hx4]; simpa using hb4
    have hrun : (reducePinGuard fe (decI c)).run a = .ok (false, a4) := by
      simp only [reducePinGuard, StateT.run_bind, hrun1, exc_ok_bind', hrun2, ex2, Bool.not_true,
        Bool.false_eq_true, ite_false, hrun3, ex3, hrun4, ex4, Bool.not_false, ite_true,
        StateT.run_pure]
      rfl
    obtain ⟨hC, hx, hr⟩ := rpg_fin hS.check hd hrun hS4
    exact ⟨false, a4, hrun, hC, hx, hr, hg1.trans (hg2.trans (hg3.trans hg4)), by simp [decW0B]⟩
  rw [ite_eq_right hb4] at h
  have ex4 : x4 = true := by rw [← hx4]; simpa using hb4
  -- `consts_resolve_ffast`
  cases h5 : realCall p n "consts_resolve_ffast" [vis, e] m4 with
  | none => rw [h5] at h; simp [rpgK5] at h
  | some rm5 =>
  obtain ⟨r5, m5⟩ := rm5
  rw [h5, rpgK5_some] at h
  obtain ⟨x5, a5, hrun5, ⟨hS5, hg5, hx5⟩, -⟩ :=
    crfF_okT dn vis fe e he1l m4 m5 a4 r5 (crfF_of_callW hck.crf h5) ⟨hS4, hCr4.crMemo⟩
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hrun : (reducePinGuard fe (decI c)).run a = .ok (x5, a5) := by
    simp only [reducePinGuard, StateT.run_bind, hrun1, exc_ok_bind', hrun2, ex2, Bool.not_true,
      Bool.false_eq_true, ite_false, hrun3, ex3, hrun4, ex4]
    exact hrun5
  obtain ⟨hC, hx, hr⟩ := rpg_fin hS.check hd hrun hS5
  exact ⟨x5, a5, hrun, hC, hx, hr, hg1.trans (hg2.trans (hg3.trans (hg4.trans hg5))), hx5⟩

/-- **`is_def_eq_core`'s twin side**: con-ron's `KnotSpec.defeq` at `checkFuel` (`CoreSpec.of_core`)
gives `CheckOK` and `Ext` after a run from `CheckOK` and the two sides' denotations. -/
theorem defeq_check {env : ConLeche.Env} {fe : IFEnv} {a a' : AState} {d : Nat} {i j : EIdx}
    {x y : ConLeche.Expr} {b : Bool} (henv : ConLeche.EnvWF env) (hck : CheckOK V env fe a)
    (hi : denoteE a.store i = some x) (hj : denoteE a.store j = some y)
    (hwx : ConLeche.Expr.WScoped d x) (hwy : ConLeche.Expr.WScoped d y)
    (hrun : (isDefEqCore V fe checkFuel d i j).run a = .ok (b, a')) :
    CheckOK V env fe a' ∧ Ext a.store a'.store ∧ a'.pins = a.pins ∧
      ConRon.Bridge.Core.SimV (ConLeche.isDefEqCore V env) d x y b :=
  ConRon.Bridge.AM.of_run (P := fun t => t = a) rfl hrun
    (((CoreSpec.of_core rfl).knot env fe henv).defeq a d i j x y hck hi hj hwx hwy)

/-- What `check_reduce_pin` gives besides the twin's run (from `m`): the stage relation at the
pushed view `vis2`, `StageC` at the pre-insertion view `vis`, the growth. -/
structure CrpPost (dn : NIdx → Option ConLeche.Name) (vis vis2 : Word) (fe2 : IFEnv)
    (env : ConLeche.Env) (m m' : Mem) (a' : AState) : Prop where
  stage2 : StageR dn vis2 fe2 m' a'
  stageC : StageC dn vis (fe2.restrictTo vis.toNat) env m' a'
  grow : IWGrow m m'

/-- **`check_reduce_pin` refines `checkReducePin`, both outcomes** (con-ron's
`checkReducePin_bridge`'s decomposition): from the stage relation at the pushed view `vis2`,
con-ron's `CheckOK` at the pre-insertion view `vis` of the index (at `env`, the environment before
the push), the pushed index's `StepOK` (at `env2`), the memory's half of `TwinOK`, the pin flag, the
name's and the value's denotations. The three guards and the spelling test decline; the identity
certificate failing is the twin's `internal` (class `0`); `is_def_eq_core`'s errors are the core
stub's claims. -/
@[refines ConRon.Arena.checkReducePin]
theorem crp_ref {p : Prog} (hC : CrpProg p) (hq : KnotStageProg p) (hcl : LeafClosed p)
    (hkp : CrKeep p) {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn) {vis vis2 : Word}
    {fe2 : IFEnv} {env env2 : ConLeche.Env} {a : AState} {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem}
    {c v : Word} {nm : ConLeche.Name} {x : ConLeche.Expr}
    (hS : StageR dn vis2 fe2 m a)
    (hck : CheckOK V env (fe2.restrictTo vis.toNat) a) (henv : ConLeche.EnvWF env)
    (hok2 : StepOK env2 fe2 a) (hmem : TwinMem dn m a) (hflag : pinW m 0 ≠ 0)
    (hnm : denoteN a.store.ns (decI c) = some nm) (hvx : denoteE a.store (decI v) = some x)
    (hws : ConLeche.Expr.WScoped 0 x) (hc : c.toNat < 2 ^ 32) (hv : v.toNat < 2 ^ 32)
    (hCr : L.Stubs.CrOK m) :
    RefE (CoreStubsE p) (checkReducePinE p n m vis vis2 c v)
      (checkReducePin V (fe2.restrictTo vis.toNat) fe2 (decI c) (decI v)) a
      (fun w _ a' => CrpPost dn vis vis2 fe2 env m w.2 a') := by
  cases n with
  | zero => rw [checkReducePinE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [checkReducePinE.eq_2]
  simp only [checkReducePin]
  have hvb : fe2.visibleBelow = vis2.toNat := hS.check.env.vis
  have hC0 : StageC dn vis (fe2.restrictTo vis.toNat) env m a := ⟨hS.restrict vis, hck, hmem, hflag⟩
  generalize hfe : fe2.restrictTo vis.toNat = fe at hC0 hck ⊢
  -- the stored constant, at `vis2`
  refine RefE.bindLift (fun _ => rfl) fun r1 m1 h1 => ?_
  have hCr1 := hkp.call (im_mem _ rfl) h1 hCr
  obtain ⟨s1, hs1, -, hok1, hS1, hg1, hb1, -⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (reduceStoredOk_refines p hC.red dn vis2 fe2 c hc n ⟨m, Locals.init []⟩ a hS) h1
  subst hs1
  have hrun1 := AM.run_of_ok _ _ hok1
  refine ⟨_, _, hrun1, ?_⟩
  dsimp only [checkReducePinE.k_reduce_stored_ok]
  refine RefE.guardIf rfl (fun e1 => by rw [← hb1]; simpa using e1)
    (fun e1 => by rw [← hb1] at e1; simpa using e1) fun _ _ => ?_
  obtain ⟨hi1, -⟩ := ConRon.Bridge.reduceStoredOk_run hck.state hck.pins hok2.ienv hnm _ _ hrun1
  generalize AM.st (reduceStoredOk fe2 (decI c)) a = a1 at hrun1 hS1 hi1
  have hC1 : StageC dn vis fe env s1.mem a1 :=
    StageC.of_leaf hC0 (by rw [← hfe]; exact hS1.restrict vis)
      (callW_leafFrame hcl (leaf_mem _ (by decide)) h1) hi1
  have hnm1 := ConRon.Bridge.denoteN_ext hnm hi1.ext
  have hv1 := ConRon.Bridge.denote_ext hvx hi1.ext
  -- the element inductive
  refine RefE.bindLift (fun _ => rfl) fun r2 m2 h2 => ?_
  have hCr2 := hkp.call (im_mem _ rfl) h2 hCr1
  obtain ⟨s2, hs2, -, hok2', hS2, hg2, hb2, -⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (reduceElemOk_refines p hC.red dn hdn vis fe c hc n ⟨s1.mem, Locals.init []⟩ a1 hC1.stage) h2
  subst hs2
  have hrun2 := AM.run_of_ok _ _ hok2'
  refine ⟨_, _, hrun2, ?_⟩
  dsimp only [checkReducePinE.k_reduce_elem_ok]
  refine RefE.guardIf rfl (fun e2 => by rw [← hb2]; simpa using e2)
    (fun e2 => by rw [← hb2] at e2; simpa using e2) fun _ _ => ?_
  obtain ⟨hi2, -⟩ := ConRon.Bridge.reduceElemOk_run hC1.check.state hC1.check.pins
    hC1.check.ienv hnm1 _ _ hrun2
  generalize AM.st (reduceElemOk fe (decI c)) a1 = a2 at hrun2 hS2 hi2
  have hC2 := StageC.of_leaf hC1 hS2 (callW_leafFrame hcl (leaf_mem _ (by decide)) h2) hi2
  have hnm2 := ConRon.Bridge.denoteN_ext hnm1 hi2.ext
  have hv2 := ConRon.Bridge.denote_ext hv1 hi2.ext
  -- the pin's guards
  refine RefE.bindLift (fun _ => rfl) fun r3 m3 h3 => ?_
  obtain ⟨s3, hs3, -, hW3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (rpg_specW p hC.bvb hC.hf hC.rpg (realCall p) (realCall_spec p) n ⟨s2.mem, Locals.init []⟩ vis c)
    h3
  subst hs3
  obtain ⟨x3, a3, hrun3, hC3, hx3, hr3, hg3, hb3⟩ :=
    rpgW_okC hC.red.pa hC.rdp hC.red.rom hcl hC.apd hkp hW3 hC2 hc hnm2 hCr2
  refine ⟨_, _, hrun3, ?_⟩
  dsimp only [checkReducePinE.k_reduce_pin_guard]
  refine RefE.guardIf rfl (fun e3 => by rw [← hb3.1]; simpa using e3)
    (fun e3 => by rw [← hb3.1] at e3; simpa using e3) fun _ e3 => ?_
  have t3 : x3 = true := e3
  have hc2 : ConLeche.reducePinGuard env nm = true := by rw [← hr3, t3]
  have hwsP : ConLeche.Expr.WScoped 0 (ConLeche.reduceDeclPin nm) := by
    refine ConLeche.Expr.WScoped.of_not_hasFvar ?_
    simp only [ConLeche.reducePinGuard, Bool.and_eq_true, Bool.not_eq_true'] at hc2
    exact hc2.1.1.2
  have hnm3 := ConRon.Bridge.denoteN_ext hnm2 hx3
  have hv3 := ConRon.Bridge.denote_ext hv2 hx3
  -- the pin
  refine RefE.bindLift (fun _ => rfl) fun r4 m4 h4 => ?_
  obtain ⟨s4, hs4, -, hok4, hS4, hg4, hpl, hpe⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (reduceDeclPin_refines p hC.red.pa n ⟨s3.mem, Locals.init []⟩ a3 dn fe vis c hC3.stage hc
      hC.red.rom hC.rdp) h4
  subst hs4
  have hrun4 := AM.run_of_ok _ _ hok4
  rw [← hpe] at hrun4
  obtain ⟨hi4, hpd⟩ := ConRon.Bridge.reduceDeclPin_run hC3.check.state hC3.check.pins hnm3 hrun4
  refine ⟨_, _, hrun4, ?_⟩
  dsimp only [checkReducePinE.k_reduce_decl_pin]
  generalize AM.st (reduceDeclPin (decI c)) a3 = a4 at hrun4 hS4 hi4 hpd
  have hC4 := StageC.of_leaf hC3 hS4 (callW_leafFrame hcl (leaf_mem _ (by decide)) h4) hi4
  have hnm4 := ConRon.Bridge.denoteN_ext hnm3 hi4.ext
  have hv4 := ConRon.Bridge.denote_ext hv3 hi4.ext
  -- the value against the pin
  refine RefE.bindCall (fun _ => rfl)
    (fun hcE _ h5 => hcE.isDefEqCore n hn' hC4.stageT 0 v (r4.headD 0) hv hpl _ h5)
    (fun b h5 => hq.isDefEqCore_sim n hn' hC4.stageT 0 v (r4.headD 0) hv hpl b.1 b.2 h5)
    fun r5 m5 x5 a5 _ hrun5 ⟨hT5, hg5, hx5⟩ => ?_
  obtain ⟨hck5, hx5', -, -⟩ := defeq_check henv hC4.check hv4 hpd hws hwsP hrun5
  have hC5 := StageC.of_T hT5 hck5
  dsimp only [checkReducePinE.k_is_def_eq_core]
  refine RefE.guardIf rfl (fun e5 => by rw [← hx5, decBool, e5]; rfl)
    (fun e5 => by rw [← hx5] at e5; simpa [decBool] using e5) fun _ _ => ?_
  have hnm5 := ConRon.Bridge.denoteN_ext hnm4 hx5'
  have hv5 := ConRon.Bridge.denote_ext hv4 hx5'
  -- the certificate's variable
  refine RefE.bindLift (fun _ => rfl) fun r6 m6 h6 => ?_
  obtain ⟨s6, hs6, -, hok6, hS6, hg6, hx6⟩ := triple_of_callW (s₀ := ⟨m5, Locals.init []⟩)
    (reduceCertVar_refines p hC.rcv n ⟨m5, Locals.init []⟩ a5 dn fe vis c hC5.stage hc) h6
  subst hs6
  have hrun6 := AM.run_of_ok _ _ hok6
  rw [hx6] at hrun6
  obtain ⟨hi6, hxv⟩ := ConRon.Bridge.reduceCertVar_run hck5.state hck5.pins hnm5 hrun6
  refine ⟨_, _, hrun6, ?_⟩
  generalize AM.st (reduceCertVar (decI c)) a5 = a6 at hrun6 hS6 hi6 hxv
  have hC6 := StageC.of_leaf hC5 hS6 (callW_leafFrame hcl (leaf_mem _ (by decide)) h6) hi6
  have hv6 : denoteE a6.store (decE v) = some x := ConRon.Bridge.denote_ext hv5 hi6.ext
  dsimp only [checkReducePinE.k_reduce_cert_var]
  refine RefE.abort0 rfl fun e6 => ?_
  have hxl : (r6.headD 0).toNat < 2 ^ 32 := by
    have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp e6); simpa using this
  -- the application
  refine RefE.bindLift (fun _ => rfl) fun ax m7 h7 => ?_
  obtain ⟨a7, hrun7, hS7, hg7⟩ := mkApp_stage hC6.stage v (r6.headD 0) h7
  have haxl := mkAppW_hw s6.mem a6 hC6.stage.check.arena v (r6.headD 0) ax m7 h7
  obtain ⟨hi7, hax⟩ := ConRon.Bridge.Frontend.internE_sstep hC6.check.state
    (ConRon.Bridge.viewOK_app (by rw [hv6]; rfl) (by rw [hxv]; rfl)) hrun7
  have hax' : denoteE a7.store (decE ax) = some (.app x (ConLeche.reduceCertVar nm)) := by
    rw [hax]
    simp only [denoteEView, ConRon.Bridge.denote_ext hv6 hi7.ext,
      ConRon.Bridge.denote_ext hxv hi7.ext, opt2]
  have hC7 := StageC.of_leaf hC6 hS7 (mkAppW_leafFrame h7) hi7
  have hwsC : ConLeche.Expr.WScoped 1 (ConLeche.reduceCertVar nm) := by
    unfold ConLeche.reduceCertVar ConLeche.reduceElemTy
    split <;> simp [ConLeche.Expr.WScoped]
  have hwsA : ConLeche.Expr.WScoped 1 (.app x (ConLeche.reduceCertVar nm)) := by
    unfold ConLeche.Expr.WScoped
    exact ⟨ConLeche.Expr.WScoped.mono (by omega) hws, hwsC⟩
  refine ⟨_, _, (hrun7 : (internE (.app (decI v) (decE (r6.headD 0)))).run a6 = .ok (decE ax, a7)), ?_⟩
  dsimp only [checkReducePinE.k_mk_app]
  -- the identity certificate
  refine RefE.bindCall (fun _ => rfl)
    (fun hcE _ h8 => hcE.isDefEqCore n hn' hC7.stageT 1 ax (r6.headD 0) haxl hxl _ h8)
    (fun b h8 => hq.isDefEqCore_sim n hn' hC7.stageT 1 ax (r6.headD 0) haxl hxl b.1 b.2 h8)
    fun r8 m8 x8 a8 _ hrun8 ⟨hT8, hg8, hx8⟩ => ?_
  obtain ⟨hck8, -, -, -⟩ := defeq_check henv hC7.check hax'
    (ConRon.Bridge.denote_ext hxv hi7.ext) hwsA hwsC hrun8
  have hC8 := StageC.of_T hT8 hck8
  dsimp only [checkReducePinE.k_is_def_eq_core_2]
  refine RefE.abort0 rfl fun e8 => ?_
  have t8 : x8 = true := by rw [← hx8]; simpa [decBool] using e8
  rw [t8]
  refine RefE.ite_pos rfl (RefE.ret rfl ⟨?_, by rw [← hfe] at hC8; exact hC8, hg1.trans (hg2.trans (hg3.trans (hg4.trans
    (hg5.trans (hg6.trans (hg7.trans hg8))))))⟩)
  have := StageR.restrict hC8.stage vis2
  rw [← hfe, IFEnv.restrictTo_restrictTo, ← hvb, IFEnv.restrictTo_self] at this
  exact this

set_option experimental.vcgen true in
/-- **The model of `check_decl_opaque`, both outcomes**: its callees through their runs. -/
l_model checkDeclOpaque_specE (p : Prog)
  (hf : p.lookup "check_decl_opaque" = some checkDeclOpaque)
  fns [hf ↦ checkDeclOpaqueE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified

/-- **The opaque arm refines `checkDecl`, both outcomes**, under `StageT` (con-ron's
`checkDecl_bridge_opaque`): the constant check and the value check (`ccv_ref`, `ov_ref`), then for
`Lean.reduceNat`/`Lean.reduceBool` the reduce-pin gate under `StageC` (`crp_ref`) at the
pre-insertion view (con-ron's `CheckOK`, restricted, and the memory's half: the call's frame by
`LoopClosed`, the core memos by `ov_ref`). From the fold invariant `FoldOK` at the arm's entry and
the declaration's constant and value denoting. -/
theorem cdo_ref {p : Prog} (hV : ValProg p) (hC : CrpProg p) (hq : KnotStageProg p)
    (hcl : LeafClosed p) (hlc : LoopClosed p) (hap : ApdF p) (hkp : CrKeep p)
    {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn)
    {vis : Word} {fe : IFEnv} {env : ConLeche.Env} {a : AState} (n : Nat) (hn : n ≤ 2 ^ 62)
    {m : Mem} {i : Word} {ds : Array IDeclaration} {pins : List INatOpPinSet}
    {cv : IConstantVal} {v : EIdx} {c : ConLeche.ConstantVal} {x : ConLeche.Expr}
    (hS : StageT dn vis fe m a)
    (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds) (hi : i.toNat < ds.size)
    (hd : ds[i.toNat] = .opaqueDecl cv v) (hfold : FoldOK V env fe a)
    (hcvd : Frontend.denoteCV a.store cv = some c) (hvd : denoteE a.store v = some x)
    (hCr : L.Stubs.CrOK m) :
    RefE (CdtCtx p) (checkDeclOpaqueE p n m i vis) (checkDecl V pins fe (.opaqueDecl cv v)) a
      (fun w y a' => ArmPost dn m w.1 w.2 y a') := by
  show RefE _ _ (do checkConstantVal V fe cv
                    let fe2 ← checkOpaqueVal V fe cv v
                    if (← reduceOpNames).contains cv.name then
                      checkReducePin V (fe2.restrictTo fe.visibleBelow) fe2 cv.name v
                    pure fe2) a _
  cases n with
  | zero => rw [checkDeclOpaqueE.eq_1]; exact RefE.of_cls0 rfl
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [checkDeclOpaqueE.arm1]
  -- `erec_ci`
  rcases h1 : callE p n "erec_ci" [i, 0] m with e1 | ⟨r1, m1⟩
  · rw [checkDeclOpaqueE.k_erec_ci.none]; exact fun hG => nvl hG.nv (by decide +kernel) h1
  rw [checkDeclOpaqueE.k_erec_ci.arm1]
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callE (erecCi_specW p hV.rcp n ⟨m, Locals.init []⟩ i 0) h1
  subst hs1
  have hCr1 := CrOK.frame hCr (erecCiW_frame hW1) (by decide) (by decide)
  obtain ⟨hS1, hg1, hci1, hcv1, hval1, htop1⟩ :=
    erecCiW_okT (ci := .axiomInfo cv) hW1 hS hD hi (by rw [hd]; rfl)
  rw [hd] at hcv1 hval1
  simp only [stepCV, stepVal] at hcv1 hval1
  generalize hq0 : r1.headD 0 = q at hci1 hcv1 hval1 htop1 ⊢
  have hqb : q.toNat + 8 < 2 ^ 64 := by
    have := hS1.stage.iw.er; have := hS1.stage.iw.erSize; omega
  have hq1 : (q + 1).toNat = q.toNat + 1 := toNat_add_small q 1 (by omega)
  have hq5 : (q + 5).toNat = q.toNat + 5 := toNat_add_small q 5 (by omega)
  -- the name and value words
  obtain ⟨wn, hwn, hwnl, hname0⟩ := decCI_name hci1
  have hname : cv.name = decI wn := hname0
  obtain ⟨wv, hwv, hwvl, rfl⟩ := hd?_some hval1
  rw [rdW_of_get? hq1.symm (erecP_get hwn), rdW_of_get? hq5.symm (erecP_get hwv)]
  -- `check_constant_val`
  refine RefE.bindRun (s₀ := ⟨s1.mem, Locals.init []⟩) (fun _ => rfl)
    (checkConstantVal_specE p hV n _ vis (q + 1)) (fun hG => hG.nv) (fun hG => hG.toVerdictCtxU)
    (ccv_ref hq hap hkp hn' hS1 (by rw [hq1]; exact hcv1) (by omega) (denoteCV_lps hcvd) hCr1)
    fun r2 s2 _ a2 _ _ hrun2 hP2 => ?_
  dsimp only [checkDeclOpaqueE.k_check_constant_val]
  obtain ⟨hstep1, F1, hpure1⟩ :=
    ConRon.Bridge.checkConstantVal_bridge_of_fold rfl (CoreSpec.of_core rfl) hfold hcvd hrun2
  have hok1 := hfold.ofCore hstep1
  have hcA := ConRon.Bridge.denoteCV_ext hcvd hstep1.ext
  have hv1 := ConRon.Bridge.denote_ext hvd hstep1.ext
  -- `check_opaque_val`
  have hx2 : ArrExt (erecP s1.mem) (erecP s2.mem) := IWGrow.erecPExt hP2.grow
  rw [checkOpaqueVal_dvT]
  refine RefE.bindRun (s₀ := ⟨s2.mem, Locals.init []⟩) (fun _ => rfl) (checkOpaqueVal_specE p hV n _ vis q)
    (fun _ => trivial)
    (fun hG => ⟨fun _ _ _ _ h => callE_nv hG.nv (declNv_mem _ (by decide +kernel)) _ _ _ h, hG.core, hG.ivg⟩)
    (ov_ref hq hV hap hkp hn' "type mismatch in opaque" hP2.stage (ArrExt.decCI hx2 hci1)
      (ArrExt.decCV hx2 (decCI_cvTA hci1 (.inr rfl))) (ArrExt.hd? hx2 hval1) (denoteCV_lps hcA) hP2.crOK)
    fun r3 s3 y3 a3 h3 _ hrun3 ⟨hS3, hM3, hg3, hy3⟩ => ?_
  subst hy3
  dsimp only [checkDeclOpaqueE.k_check_opaque_val]
  have h3w := callW_of_callE h3
  have hCr3 := hkp.call (im_mem _ rfl) h3w hP2.crOK
  rw [← checkOpaqueVal_dvT] at hrun3
  -- the twin's value check: `CheckOK` at the old index, `StepOK` at the pushed one
  obtain ⟨hstep2, -, -, env2, F2, hstepOK2, hpure2⟩ := ConRon.Bridge.checkOpaqueVal_bridge rfl
    (CoreSpec.of_core rfl) hok1 hcA (ConRon.Bridge.checkConstantVal_typeWF hpure1) hv1 hrun3
  have hok3 := hok1.ofCore hstep2
  have hnm3 : denoteN a3.store.ns (decI wn) = some c.name := by
    rw [← hname]
    exact ConRon.Bridge.denoteN_ext (ConRon.Bridge.denoteCV_inv hcA).1 hstep2.ext
  have hv3 := ConRon.Bridge.denote_ext hv1 hstep2.ext
  have hvis : fe.visibleBelow = vis.toNat := hS.stage.check.env.vis
  have hpre := ConRon.Bridge.restrict_pushed_find (fe2 := fe.push (.axiomInfo cv)) rfl
    (hok3.check.ienv.find?_none
      (show denoteN a3.store.ns cv.name = some c.name by rw [hname]; exact hnm3)
      (ConRon.Bridge.checkConstantVal_fresh hpure1))
  have hck3 : CheckOK V env ((fe.push (.axiomInfo cv)).restrictTo vis.toNat) a3 := by
    rw [← hvis]; exact hok3.check.congr_find hpre rfl
  have hws : ConLeche.Expr.WScoped 0 x :=
    ConLeche.Expr.WScoped.of_not_hasFvar (ConRon.Bridge.checkOpaqueVal_noFvar hpure2)
  -- the memory's half after the push: the call's frame, the core memos
  have hf3 := (run_memFrame hlc checkOpaqueVal_loop (run_of_callW h3w)).1
  have hmem3 : TwinMem dn s3.mem a3 :=
    ⟨by rw [hf3.size]; exact hP2.stage.twin.erec, by rw [hf3.size]; exact hP2.stage.twin.spn,
      by rw [hf3.size]; exact hP2.stage.twin.bstk, hM3,
      fun k y e => hstep2.ext.lss.ls.ns k y (hP2.stage.twin.den.dnN k y e)⟩
  have hflag3 : pinW s3.mem 0 ≠ 0 := by
    simp only [pinW, hf3.1 PINS loopA_pins (by decide)]; exact hP2.stage.flag
  generalize hfe2 : fe.push (.axiomInfo cv) = fe2 at hS3 hrun3 hck3 hstepOK2 ⊢
  -- the two pins
  rcases h4 : callE p n "pin_at" [43] s3.mem with e4 | ⟨r4, m4⟩
  · rw [checkDeclOpaqueE.k_pin_at.none]; exact fun hG => nvl hG.nv (by decide +kernel) h4
  rw [checkDeclOpaqueE.k_pin_at.arm1]
  obtain ⟨s4, hs4, -, hW4⟩ := triple_of_callE
    (pinAt_specW p hC.red.pa n ⟨s3.mem, Locals.init []⟩ 43) h4
  obtain ⟨hm4, hr4, -, -⟩ := pinAtW_ok hW4 hS3.check.pins
  have hm4' : m4 = s3.mem := hs4.symm.trans hm4
  subst hm4'
  rcases h5 : callE p n "pin_at" [44] s3.mem with e5 | ⟨r5, m5⟩
  · rw [checkDeclOpaqueE.k_pin_at_2.none]; exact fun hG => nvl hG.nv (by decide +kernel) h5
  obtain ⟨s5, hs5, -, hW5⟩ := triple_of_callE
    (pinAt_specW p hC.red.pa n ⟨s3.mem, Locals.init []⟩ 44) h5
  obtain ⟨hm5, hr5, -, -⟩ := pinAtW_ok hW5 hS3.check.pins
  have hm5' : m5 = s3.mem := hs5.symm.trans hm5
  subst hm5'
  have e4 : r4.headD 0 = pinW s3.mem (1 + (43 : Word).toNat) := by rw [hr4]; rfl
  have e5 : r5.headD 0 = pinW s3.mem (1 + (44 : Word).toNat) := by rw [hr5]; rfl
  have hF := hS3.check.pins.full hflag3
  have hcont : (reduceOpNames.run a3) =
      .ok ((List.range' 44 2).map (fun j => decI (pinW s3.mem j)), a3) := reduceOpNames_run hF
  have hiff := contains_pins hF hwnl 44 2 (by omega) (by omega)
  refine RefE.bind_right hcont ?_
  rw [hname]
  by_cases hin : wn = r4.headD 0 ∨ wn = r5.headD 0
  · rw [checkDeclOpaqueE.k_pin_at_2.arm1 p _ _ _ _ _ _ _ _ hin]
    rw [e4, e5] at hin
    have hc : ((List.range' 44 2).map fun j => (decI (pinW s3.mem j) : NIdx)).contains (decI wn) =
        true := by
      rw [hiff]
      rcases hin with e | e
      · exact ⟨44, by omega, by omega, e.symm⟩
      · exact ⟨45, by omega, by omega, e.symm⟩
    refine RefE.ite_pos hc ?_
    rw [hvis]
    refine RefE.bindRun (s₀ := ⟨s3.mem, Locals.init []⟩) (fun _ => rfl)
      (checkReducePin_specE p hC n _ vis (r3.headD 0) wn wv) (fun hG => hG.nv) (fun hG => hG.core)
      (crp_ref hC hq hcl hkp hdn hn' hS3 hck3 hok3.envWF hstepOK2 hmem3 hflag3 hnm3 hv3 hws hwnl hwvl
        hCr3) fun r6 s6 _ a6 _ _ _ hR6 => ?_
    rw [checkDeclOpaqueE.k_check_reduce_pin.arm1, checkDeclOpaqueE.j1.arm1]
    exact RefE.ret rfl ⟨by simpa using hR6.stage2, hR6.stageC.mem.memos,
      hg1.trans (hP2.grow.trans (hg3.trans hR6.grow))⟩
  · rw [checkDeclOpaqueE.k_pin_at_2.arm2 p _ _ _ _ _ _ _ _ hin, checkDeclOpaqueE.j1.arm1]
    rw [e4, e5] at hin
    have hc : ((List.range' 44 2).map fun j => (decI (pinW s3.mem j) : NIdx)).contains (decI wn) =
        false := by
      cases hcb : ((List.range' 44 2).map fun j => (decI (pinW s3.mem j) : NIdx)).contains (decI wn)
      · rfl
      exfalso
      rw [hiff] at hcb
      obtain ⟨j, hj1, hj2, e⟩ := hcb
      apply hin
      have : j = 44 ∨ j = 45 := by omega
      rcases this with rfl | rfl
      · exact .inl e.symm
      · exact .inr e.symm
    refine RefE.ite_neg (by rw [hc]; decide) ?_
    exact RefE.ret rfl ⟨by simpa using hS3, hM3, hg1.trans (hP2.grow.trans hg3)⟩

end L.Arena
