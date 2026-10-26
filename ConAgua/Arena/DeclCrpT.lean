import ConAgua.Arena.DeclArmT
import ConAgua.Arena.DeclArmOpaque
import ConAgua.Arena.StageC
import ConAgua.Arena.LoopFns
import ConRon.Bridge.Checker.Arms

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

The opaque arm (`cdoW_okT`) carries con-ron's fold invariant `FoldOK` from its entry across the
constant check (`checkConstantVal_bridge_of_fold`) and the value check (`checkOpaqueVal_bridge`),
as con-ron's `checkDecl_bridge_opaque` does; the gate's `CheckOK` at the restricted pushed index
is `CheckOK.congr_find` of it (`restrict_pushed_find`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF)
open ConRon.Bridge (CheckOK StepOK FoldOK CoreSpec)

local notation "V" => ConLeche.CheckMode.verified

theorem leafA_app : ∀ b ∈ [AREC, ASLOT, ADER, AREC + 256, ASLOT + 256, ADER + 256], b ∈ leafA := by
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
  · rw [if_pos hb2] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ex2 : x2 = false := by rw [← hx2]; simpa using hb2
    have hrun : (reducePinGuard fe (decI c)).run a = .ok (false, a2) := by
      simp only [reducePinGuard, StateT.run_bind, hrun1, exc_ok_bind', hrun2, ex2, Bool.not_false,
        if_true, StateT.run_pure]
      rfl
    obtain ⟨hC, hx, hr⟩ := rpg_fin hS.check hd hrun hS2
    exact ⟨false, a2, hrun, hC, hx, hr, hg1.trans hg2, by simp [decW0B]⟩
  rw [if_neg hb2] at h
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
  · rw [if_pos hb3] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ex3 : x3 = true := by rw [← hx3]; simpa using hb3
    have hrun : (reducePinGuard fe (decI c)).run a = .ok (false, a3) := by
      simp only [reducePinGuard, StateT.run_bind, hrun1, exc_ok_bind', hrun2, ex2, Bool.not_true,
        Bool.false_eq_true, if_false, hrun3, ex3, if_true, StateT.run_pure]
      rfl
    obtain ⟨hC, hx, hr⟩ := rpg_fin hS.check hd hrun hS3
    exact ⟨false, a3, hrun, hC, hx, hr, hg1.trans (hg2.trans hg3), by simp [decW0B]⟩
  rw [if_neg hb3] at h
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
  · rw [if_pos hb4] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ex4 : x4 = false := by rw [← hx4]; simpa using hb4
    have hrun : (reducePinGuard fe (decI c)).run a = .ok (false, a4) := by
      simp only [reducePinGuard, StateT.run_bind, hrun1, exc_ok_bind', hrun2, ex2, Bool.not_true,
        Bool.false_eq_true, if_false, hrun3, ex3, hrun4, ex4, Bool.not_false, if_true,
        StateT.run_pure]
      rfl
    obtain ⟨hC, hx, hr⟩ := rpg_fin hS.check hd hrun hS4
    exact ⟨false, a4, hrun, hC, hx, hr, hg1.trans (hg2.trans (hg3.trans hg4)), by simp [decW0B]⟩
  rw [if_neg hb4] at h
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
      Bool.false_eq_true, if_false, hrun3, ex3, hrun4, ex4]
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

/-- **`check_reduce_pin` under `StageC`** (`crpW_ok`'s, con-ron's `checkReducePin_bridge`'s
decomposition): from the stage relation at the pushed view `vis2`, con-ron's `CheckOK` at the
pre-insertion view `vis` of the index (at `env`, the environment before the push), the pushed
index's `StepOK` (at `env2`), the memory's half of `TwinOK`, the pin flag, the name's and the
value's denotations; the gate at `vis`, the stage relation at `vis2` and `StageC` at `vis` after. -/
@[refines ConRon.Arena.checkReducePin]
theorem crpW_okT {p : Prog} (hC : CrpProg p) (hq : KnotStageProg p) (hcl : LeafClosed p)
    (hkp : CrKeep p) {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn) {vis vis2 : Word} {fe2 : IFEnv}
    {env env2 : ConLeche.Env} {a : AState} {n : Nat} (hn : n ≤ 2 ^ 62) {m m' : Mem} {c v : Word}
    {r : List Word} {nm : ConLeche.Name} {x : ConLeche.Expr}
    (hW : crpW p (realCall p) n m vis vis2 c v = some (r, m')) (hS : StageR dn vis2 fe2 m a)
    (hck : CheckOK V env (fe2.restrictTo vis.toNat) a) (henv : ConLeche.EnvWF env)
    (hok2 : StepOK env2 fe2 a) (hmem : TwinMem dn m a) (hflag : pinW m 0 ≠ 0)
    (hnm : denoteN a.store.ns (decI c) = some nm) (hvx : denoteE a.store (decI v) = some x)
    (hws : ConLeche.Expr.WScoped 0 x) (hc : c.toNat < 2 ^ 32) (hv : v.toNat < 2 ^ 32)
    (hCr : L.Stubs.CrOK m) :
    ∃ a', (checkReducePin V (fe2.restrictTo vis.toNat) fe2 (decI c) (decI v)).run a = .ok ((), a') ∧
      StageR dn vis2 fe2 m' a' ∧ StageC dn vis (fe2.restrictTo vis.toNat) env m' a' ∧
      IWGrow m m' := by
  cases n with
  | zero => simp [crpW] at hW
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [crpW_step] at hW
  have hvb : fe2.visibleBelow = vis2.toNat := hS.1.env.vis
  have hC0 : StageC dn vis (fe2.restrictTo vis.toNat) env m a := ⟨hS.restrict vis, hck, hmem, hflag⟩
  generalize hfe : fe2.restrictTo vis.toNat = fe at hC0 hck ⊢
  -- the stored constant, at `vis2`
  cases h1 : callW p n "reduce_stored_ok" [vis2, c] m with
  | none => rw [h1] at hW; cases hW
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, crpK1_some] at hW
  have hCr1 := hkp.call (im_mem _ rfl) h1 hCr
  obtain ⟨s1, hs1, -, hok1, hS1, hg1, hb1, -⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (reduceStoredOk_refines p hC.red dn vis2 fe2 c hc n ⟨m, Locals.init []⟩ a hS) h1
  subst hs1
  have hrun1 := AM.run_of_ok _ _ hok1
  by_cases e1 : r1.headD 0 = 0
  · rw [if_pos e1] at hW; cases hW
  rw [if_neg e1] at hW
  have t1 : AM.res (reduceStoredOk fe2 (decI c)) a = true := by rw [← hb1]; simpa using e1
  rw [t1] at hrun1
  obtain ⟨hi1, -⟩ := ConRon.Bridge.reduceStoredOk_run hck.state hck.pins hok2.ienv hnm _ _ hrun1
  generalize AM.st (reduceStoredOk fe2 (decI c)) a = a1 at hrun1 hS1 hi1
  have hC1 : StageC dn vis fe env s1.mem a1 :=
    StageC.of_leaf hC0 (by rw [← hfe]; exact hS1.restrict vis)
      (callW_leafFrame hcl (leaf_mem _ (by decide)) h1) hi1
  have hnm1 := ConRon.Bridge.denoteN_ext hnm hi1.ext
  have hv1 := ConRon.Bridge.denote_ext hvx hi1.ext
  -- the element inductive
  cases h2 : callW p n "reduce_elem_ok" [vis, c] s1.mem with
  | none => rw [h2] at hW; cases hW
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2, crpK2_some] at hW
  have hCr2 := hkp.call (im_mem _ rfl) h2 hCr1
  obtain ⟨s2, hs2, -, hok2', hS2, hg2, hb2, -⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (reduceElemOk_refines p hC.red dn hdn vis fe c hc n ⟨s1.mem, Locals.init []⟩ a1 hC1.stage) h2
  subst hs2
  have hrun2 := AM.run_of_ok _ _ hok2'
  by_cases e2 : r2.headD 0 = 0
  · rw [if_pos e2] at hW; cases hW
  rw [if_neg e2] at hW
  have t2 : AM.res (reduceElemOk fe (decI c)) a1 = true := by rw [← hb2]; simpa using e2
  rw [t2] at hrun2
  obtain ⟨hi2, -⟩ := ConRon.Bridge.reduceElemOk_run hC1.check.state hC1.check.pins
    hC1.check.ienv hnm1 _ _ hrun2
  generalize AM.st (reduceElemOk fe (decI c)) a1 = a2 at hrun2 hS2 hi2
  have hC2 := StageC.of_leaf hC1 hS2 (callW_leafFrame hcl (leaf_mem _ (by decide)) h2) hi2
  have hnm2 := ConRon.Bridge.denoteN_ext hnm1 hi2.ext
  have hv2 := ConRon.Bridge.denote_ext hv1 hi2.ext
  -- the pin's guards
  cases h3 : callW p n "reduce_pin_guard" [vis, c] s2.mem with
  | none => rw [h3] at hW; cases hW
  | some rm3 =>
  obtain ⟨r3, m3⟩ := rm3
  rw [h3, crpK3_some] at hW
  obtain ⟨s3, hs3, -, hW3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (rpg_specW p hC.bvb hC.hf hC.rpg (realCall p) (realCall_spec p) n ⟨s2.mem, Locals.init []⟩ vis c)
    h3
  subst hs3
  obtain ⟨x3, a3, hrun3, hC3, hx3, hr3, hg3, hb3⟩ :=
    rpgW_okC hC.red.pa hC.rdp hC.red.rom hcl hC.apd hkp hW3 hC2 hc hnm2 hCr2
  by_cases e3 : r3.headD 0 = 0
  · rw [if_pos e3] at hW; cases hW
  rw [if_neg e3] at hW
  have t3 : x3 = true := by rw [← hb3.1]; simpa using e3
  rw [t3] at hrun3
  have hc2 : ConLeche.reducePinGuard env nm = true := by rw [← hr3, t3]
  have hwsP : ConLeche.Expr.WScoped 0 (ConLeche.reduceDeclPin nm) := by
    refine ConLeche.Expr.WScoped.of_not_hasFvar ?_
    simp only [ConLeche.reducePinGuard, Bool.and_eq_true, Bool.not_eq_true'] at hc2
    exact hc2.1.1.2
  have hnm3 := ConRon.Bridge.denoteN_ext hnm2 hx3
  have hv3 := ConRon.Bridge.denote_ext hv2 hx3
  -- the pin
  cases h4 : callW p n "reduce_decl_pin" [c] s3.mem with
  | none => rw [h4] at hW; cases hW
  | some rm4 =>
  obtain ⟨r4, m4⟩ := rm4
  rw [h4, crpK4_some] at hW
  obtain ⟨s4, hs4, -, hok4, hS4, hg4, hpl, hpe⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (reduceDeclPin_refines p hC.red.pa n ⟨s3.mem, Locals.init []⟩ a3 dn fe vis c hC3.stage hc
      hC.red.rom hC.rdp) h4
  subst hs4
  have hrun4 := AM.run_of_ok _ _ hok4
  rw [← hpe] at hrun4
  obtain ⟨hi4, hpd⟩ := ConRon.Bridge.reduceDeclPin_run hC3.check.state hC3.check.pins hnm3 hrun4
  generalize AM.st (reduceDeclPin (decI c)) a3 = a4 at hrun4 hS4 hi4 hpd
  have hC4 := StageC.of_leaf hC3 hS4 (callW_leafFrame hcl (leaf_mem _ (by decide)) h4) hi4
  have hnm4 := ConRon.Bridge.denoteN_ext hnm3 hi4.ext
  have hv4 := ConRon.Bridge.denote_ext hv3 hi4.ext
  -- the value against the pin
  cases h5 : realCall p n "is_def_eq_core" [vis, 0, v, r4.headD 0] s4.mem with
  | none => rw [h5] at hW; simp [crpK5] at hW
  | some rm5 =>
  obtain ⟨r5, m5⟩ := rm5
  rw [h5, crpK5_some] at hW
  obtain ⟨x5, a5, hrun5, hT5, hg5, hx5⟩ :=
    hq.isDefEqCore_sim n hn' hC4.stageT 0 v (r4.headD 0) hv hpl r5 m5 h5
  have h00 : (0 : Word).toNat = 0 := rfl
  have h01 : (1 : Word).toNat = 1 := rfl
  rw [h00] at hrun5
  obtain ⟨hck5, hx5', -, -⟩ := defeq_check henv hC4.check hv4 hpd hws hwsP hrun5
  have hC5 := StageC.of_T hT5 hck5
  by_cases e5 : r5.headD 0 = 0
  · rw [if_pos e5] at hW; cases hW
  rw [if_neg e5] at hW
  have t5 : x5 = true := by rw [← hx5]; simpa [decBool] using e5
  have hnm5 := ConRon.Bridge.denoteN_ext hnm4 hx5'
  have hv5 := ConRon.Bridge.denote_ext hv4 hx5'
  -- the certificate's variable
  cases h6 : callW p n "reduce_cert_var" [c] m5 with
  | none => rw [h6] at hW; simp [crpK6] at hW
  | some rm6 =>
  obtain ⟨r6, m6⟩ := rm6
  rw [h6, crpK6_some] at hW
  obtain ⟨s6, hs6, -, hok6, hS6, hg6, hx6⟩ := triple_of_callW (s₀ := ⟨m5, Locals.init []⟩)
    (reduceCertVar_refines p hC.rcv n ⟨m5, Locals.init []⟩ a5 dn fe vis c hC5.stage hc) h6
  subst hs6
  have hrun6 := AM.run_of_ok _ _ hok6
  rw [hx6] at hrun6
  obtain ⟨hi6, hxv⟩ := ConRon.Bridge.reduceCertVar_run hck5.state hck5.pins hnm5 hrun6
  generalize AM.st (reduceCertVar (decI c)) a5 = a6 at hrun6 hS6 hi6 hxv
  have hC6 := StageC.of_leaf hC5 hS6 (callW_leafFrame hcl (leaf_mem _ (by decide)) h6) hi6
  have hv6 : denoteE a6.store (decE v) = some x := ConRon.Bridge.denote_ext hv5 hi6.ext
  by_cases e6 : 4294967296 ≤ r6.headD 0
  · rw [if_pos e6] at hW; cases hW
  rw [if_neg e6] at hW
  have hxl : (r6.headD 0).toNat < 2 ^ 32 := by
    have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp e6); simpa using this
  -- the application
  cases h7 : mkAppW s6.mem v (r6.headD 0) with
  | none => rw [h7] at hW; cases hW
  | some rm7 =>
  obtain ⟨ax, m7⟩ := rm7
  rw [h7, crpK7_some] at hW
  obtain ⟨a7, hrun7, hS7, hg7⟩ := mkApp_stage hC6.stage v (r6.headD 0) h7
  have haxl := mkAppW_hw s6.mem a6 hC6.stage.1.arena v (r6.headD 0) ax m7 h7
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
  -- the identity certificate
  cases h8 : realCall p n "is_def_eq_core" [vis, 1, ax, r6.headD 0] m7 with
  | none => rw [h8] at hW; simp [crpK8] at hW
  | some rm8 =>
  obtain ⟨r8, m8⟩ := rm8
  rw [h8, crpK8_some] at hW
  obtain ⟨x8, a8, hrun8, hT8, hg8, hx8⟩ :=
    hq.isDefEqCore_sim n hn' hC7.stageT 1 ax (r6.headD 0) haxl hxl r8 m8 h8
  rw [h01] at hrun8
  obtain ⟨hck8, -, -, -⟩ := defeq_check henv hC7.check hax'
    (ConRon.Bridge.denote_ext hxv hi7.ext) hwsA hwsC hrun8
  have hC8 := StageC.of_T hT8 hck8
  by_cases e8 : r8.headD 0 = 0
  · rw [if_pos e8] at hW; cases hW
  rw [if_neg e8] at hW
  have t8 : x8 = true := by rw [← hx8]; simpa [decBool] using e8
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨rfl, rfl⟩ := hW
  refine ⟨a8, ?_, ?_, hC8, hg1.trans (hg2.trans (hg3.trans (hg4.trans (hg5.trans (hg6.trans
    (hg7.trans hg8))))))⟩
  · simp only [checkReducePin, StateT.run_bind, hrun1, exc_ok_bind', if_true]
    simp only [hrun2, exc_ok_bind', if_true, StateT.run_bind, hrun3, hrun4, hrun5, t5, hrun6]
    have e7 : (internE (.app (decI v) (decE (r6.headD 0)))).run a6 = .ok (decE ax, a7) := hrun7
    simp only [e7, exc_ok_bind']
    have e8 : (isDefEqCore V fe checkFuel 1 (decE ax) (decE (r6.headD 0))).run a7 =
        .ok (x8, a8) := hrun8
    simp only [e8, t8]
    rfl
  · have := StageR.restrict hC8.stage vis2
    rw [← hfe, IFEnv.restrictTo_restrictTo, ← hvb, IFEnv.restrictTo_self] at this
    exact this

/-- **The opaque arm under `StageT`** (`cdoW_ok`'s): the constant check and the value check under
`StageT` (`checkConstantVal_refinesT`, `dvW_okT`), then for `Lean.reduceNat`/`Lean.reduceBool` the
reduce-pin gate under `StageC` (`crpW_okT`). The twin side is con-ron's `checkDecl_bridge_opaque`:
the fold invariant `FoldOK` at the arm's entry (`TwinFold.fold`), the declaration's constant and
value denoting (`TwinFold.den`). After the value check's push `TwinOK` is not re-derived: the gate
runs from `StageC` at the pre-insertion view (con-ron's `CheckOK`, restricted, and the memory's
half: the call's frame by `LoopClosed`, the core memos by `dvW_okT`). Post: the stage relation at
the pushed environment and the core's memos. -/
theorem cdoW_okT {p : Prog} (hV : ValProg p) (hC : CrpProg p) (hq : KnotStageProg p)
    (hcl : LeafClosed p) (hlc : LoopClosed p) (hap : ApdF p) (hkp : CrKeep p) {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn)
    {vis : Word} {fe : IFEnv} {env : ConLeche.Env} {a : AState} {n : Nat} (hn : n ≤ 2 ^ 62)
    {m m' : Mem} {i : Word} {r : List Word} {ds : Array IDeclaration} {pins : List INatOpPinSet}
    {cv : IConstantVal} {v : EIdx} {c : ConLeche.ConstantVal} {x : ConLeche.Expr}
    (h : cdoW p n m i vis = some (r, m')) (hS : StageT dn vis fe m a)
    (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds) (hi : i.toNat < ds.size)
    (hd : ds[i.toNat] = .opaqueDecl cv v) (hfold : FoldOK V env fe a)
    (hcvd : Frontend.denoteCV a.store cv = some c) (hvd : denoteE a.store v = some x)
    (hCr : L.Stubs.CrOK m) :
    ∃ fe' a', (checkDecl V pins fe (.opaqueDecl cv v)).run a = .ok (fe', a') ∧
      StageR dn (r.headD 0) fe' m' a' ∧ CoreMemos m' ∧ IWGrow m m' := by
  cases n with
  | zero => simp [cdoW] at h
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [cdoW_step] at h
  cases h1 : erecCiW n m i 0 with
  | none => rw [h1] at h; cases h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, cdoK1_some] at h
  have hCr1 := CrOK.frame hCr (erecCiW_frame h1) (by decide) (by decide)
  obtain ⟨hS1, hg1, hci1, hcv1, hval1, htop1⟩ :=
    erecCiW_okT (ci := .axiomInfo cv) h1 hS hD hi (by rw [hd]; rfl)
  rw [hd] at hcv1 hval1
  simp only [stepCV, stepVal] at hcv1 hval1
  generalize hq0 : r1.headD 0 = q at h hci1 hcv1 hval1 htop1
  have hqb : q.toNat + 8 < 2 ^ 64 := by
    have := hS1.stage.2.2.1; have := hS1.stage.2.2.2.2.1; omega
  have hq1 : (q + 1).toNat = q.toNat + 1 := toNat_add_small q 1 (by omega)
  have hq5 : (q + 5).toNat = q.toNat + 5 := toNat_add_small q 5 (by omega)
  -- the name and value words
  obtain ⟨wn, hwn, hwnl, hname0⟩ := decCI_name hci1
  have hname : cv.name = decI wn := hname0
  obtain ⟨wv, hwv, hwvl, rfl⟩ := hd?_some hval1
  rw [rdW_of_get? hq1.symm (erecP_get hwn), rdW_of_get? hq5.symm (erecP_get hwv)] at h
  -- `check_constant_val`
  cases h2 : callW p n "check_constant_val" [vis, q + 1] m1 with
  | none => rw [h2] at h; cases h
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2, cdoK2_some] at h
  have hCr2 := hkp.call (im_mem _ rfl) h2 hCr1
  obtain ⟨s2, hs2, -, hok2, hS2, hg2, -⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (checkConstantVal_refinesT p hV hq hap hkp n hn' ⟨m1, Locals.init []⟩ a dn fe vis (q + 1) cv hS1
      (by rw [hq1]; exact hcv1) (by omega) (denoteCV_lps hcvd) hCr1) h2
  subst hs2
  have hrun2 := AM.run_of_ok _ _ hok2
  obtain ⟨hstep1, F1, hpure1⟩ :=
    ConRon.Bridge.checkConstantVal_bridge_of_fold rfl (CoreSpec.of_core rfl) hfold hcvd hrun2
  have hok1 := hfold.ofCore hstep1
  have hcA := ConRon.Bridge.denoteCV_ext hcvd hstep1.ext
  have hv1 := ConRon.Bridge.denote_ext hvd hstep1.ext
  generalize AM.st (checkConstantVal V fe cv) a = a2 at hrun2 hS2 hok1 hcA hv1
  -- `check_opaque_val`
  cases h3 : callW p n "check_opaque_val" [vis, q] s2.mem with
  | none => rw [h3] at h; cases h
  | some rm3 =>
  obtain ⟨r3, m3⟩ := rm3
  rw [h3, cdoK3_some] at h
  have hCr3 := hkp.call (im_mem _ rfl) h3 hCr2
  have hx2 : ArrExt (erecP m1) (erecP s2.mem) := IWGrow.erecPExt hg2
  obtain ⟨s3, hs3, -, hW3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (ov_specW p hV (realCall p) (realCall_spec p) n ⟨s2.mem, Locals.init []⟩ vis q) h3
  subst hs3
  obtain ⟨a3, hrun3, hS3, hM3, hg3⟩ := dvW_okT hq hV.rcp hC.apd hkp hn' "type mismatch in opaque"
    hW3 hS2 (ArrExt.decCI hx2 hci1)
    (by have := ArrExt.decCV hx2 (decCI_cvTA hci1 (.inr rfl)); exact this) (ArrExt.hd? hx2 hval1)
    (denoteCV_lps hcA) hCr2
  rw [← checkOpaqueVal_dvT] at hrun3
  -- the twin's value check: `CheckOK` at the old index, `StepOK` at the pushed one
  obtain ⟨hstep2, -, -, env2, F2, hstepOK2, hpure2⟩ := ConRon.Bridge.checkOpaqueVal_bridge rfl
    (CoreSpec.of_core rfl) hok1 hcA (ConRon.Bridge.checkConstantVal_typeWF hpure1) hv1 hrun3
  have hok3 := hok1.ofCore hstep2
  have hnm3 : denoteN a3.store.ns (decI wn) = some c.name := by
    rw [← hname]
    exact ConRon.Bridge.denoteN_ext (ConRon.Bridge.denoteCV_inv hcA).1 hstep2.ext
  have hv3 := ConRon.Bridge.denote_ext hv1 hstep2.ext
  have hvis : fe.visibleBelow = vis.toNat := hS.stage.1.env.vis
  have hpre := ConRon.Bridge.restrict_pushed_find (fe2 := fe.push (.axiomInfo cv)) rfl
    (hok3.check.ienv.find?_none (show denoteN a3.store.ns cv.name = some c.name by rw [hname]; exact hnm3)
      (ConRon.Bridge.checkConstantVal_fresh hpure1))
  have hck3 : CheckOK V env ((fe.push (.axiomInfo cv)).restrictTo vis.toNat) a3 := by
    rw [← hvis]; exact hok3.check.congr_find hpre rfl
  have hws : ConLeche.Expr.WScoped 0 x :=
    ConLeche.Expr.WScoped.of_not_hasFvar (ConRon.Bridge.checkOpaqueVal_noFvar hpure2)
  -- the memory's half after the push: the call's frame, the core memos
  have hf3 := (run_memFrame hlc checkOpaqueVal_loop (run_of_callW h3)).1
  have hmem3 : TwinMem dn s3.mem a3 :=
    ⟨by rw [hf3.2.2.1]; exact hS2.twin.erec, by rw [hf3.2.2.1]; exact hS2.twin.spn,
      by rw [hf3.2.2.1]; exact hS2.twin.bstk, hM3,
      fun k y e => hstep2.ext.lss.ls.ns k y (hS2.twin.den.dnN k y e)⟩
  have hflag3 : pinW s3.mem 0 ≠ 0 := by
    simp only [pinW, hf3.1 PINS loopA_pins (by decide)]; exact hS2.flag
  generalize hfe2 : fe.push (.axiomInfo cv) = fe2 at hS3 hrun3 hck3 hstepOK2
  -- the two pins
  cases h4 : pinAtW s3.mem 43 with
  | none => rw [h4] at h; cases h
  | some rm4 =>
  obtain ⟨r4, m4⟩ := rm4
  rw [h4, cdoK4_some] at h
  obtain ⟨hm4, hr4, -, -⟩ := pinAtW_ok h4 hS3.1.pins
  rw [hm4] at h
  cases h5 : pinAtW s3.mem 44 with
  | none => rw [h5] at h; cases h
  | some rm5 =>
  obtain ⟨r5, m5⟩ := rm5
  rw [h5, cdoK5_some] at h
  obtain ⟨hm5, hr5, -, -⟩ := pinAtW_ok h5 hS3.1.pins
  subst hm5
  have e4 : r4.headD 0 = pinW s3.mem (1 + (43 : Word).toNat) := by rw [hr4]; rfl
  have e5 : r5.headD 0 = pinW s3.mem (1 + (44 : Word).toNat) := by rw [hr5]; rfl
  have hF := hS3.1.pins.full hflag3
  have hcont : (reduceOpNames.run a3) =
      .ok ((List.range' 44 2).map (fun j => decI (pinW s3.mem j)), a3) := reduceOpNames_run hF
  have hiff := contains_pins hF hwnl 44 2 (by omega) (by omega)
  by_cases hin : wn = r4.headD 0 ∨ wn = r5.headD 0
  · rw [if_pos hin] at h
    rw [e4, e5] at hin
    have hc : ((List.range' 44 2).map fun j => (decI (pinW s3.mem j) : NIdx)).contains (decI wn) =
        true := by
      rw [hiff]
      rcases hin with e | e
      · exact ⟨44, by omega, by omega, e.symm⟩
      · exact ⟨45, by omega, by omega, e.symm⟩
    cases h6 : callW p n "check_reduce_pin" [vis, r3.headD 0, wn, wv] s3.mem with
    | none => rw [h6] at h; cases h
    | some rm6 =>
    obtain ⟨r6, m6⟩ := rm6
    rw [h6, cdoK6_some] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨s6, hs6, -, hW6⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
      (crp_specW p hC (realCall p) (realCall_spec p) n ⟨s3.mem, Locals.init []⟩ vis (r3.headD 0)
        wn wv) h6
    subst hs6
    obtain ⟨a6, hrun6, hS6, hC6, hg6⟩ := crpW_okT hC hq hcl hkp hdn hn' hW6 hS3 hck3 hok3.envWF
      hstepOK2 hmem3 hflag3 hnm3 hv3 hws hwnl hwvl hCr3
    refine ⟨fe2, a6, ?_, by simpa using hS6, hC6.mem.memos,
      hg1.trans (hg2.trans (hg3.trans hg6))⟩
    show (do checkConstantVal V fe cv
             let fe2 ← checkOpaqueVal V fe cv (decI wv)
             if (← reduceOpNames).contains cv.name then
               checkReducePin V (fe2.restrictTo fe.visibleBelow) fe2 cv.name (decI wv)
             pure fe2).run a = _
    simp only [StateT.run_bind, hrun2, exc_ok_bind', hrun3, hcont, hname, hc, if_true, hvis]
    simp only [hrun6, exc_ok_bind', StateT.run_pure]
    rfl
  · rw [if_neg hin] at h
    rw [e4, e5] at hin
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
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
    refine ⟨fe2, _, ?_, by simpa using hS3, hM3, hg1.trans (hg2.trans hg3)⟩
    show (do checkConstantVal V fe cv
             let fe2 ← checkOpaqueVal V fe cv (decI wv)
             if (← reduceOpNames).contains cv.name then
               checkReducePin V (fe2.restrictTo fe.visibleBelow) fe2 cv.name (decI wv)
             pure fe2).run a = _
    simp only [StateT.run_bind, hrun2, exc_ok_bind', hrun3, hcont, hname, hc, Bool.false_eq_true,
      if_false, StateT.run_pure]
    rfl

end L.Arena
