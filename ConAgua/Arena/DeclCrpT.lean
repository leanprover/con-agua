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

set_option linter.deprecated false

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsR)
open ConRon.Bridge (CheckOK StepOK FoldOK CoreSpec)

local notation "V" => ConLeche.CheckMode.verified

theorem leafA_app : AREC ∈ leafA ∧ ASLOT ∈ leafA ∧ ADER ∈ leafA := by decide +kernel
theorem leafC_app : (4 : Word) ∈ leafC ∧ (5 : Word) ∈ leafC := by decide +kernel

/-- `mk_app`'s frame is a leaf's. -/
theorem mkAppW_leafFrame {m m' : Mem} {f x r : Word} (h : mkAppW m f x = some (r, m')) :
    MemFrame leafA leafC m m' :=
  (mkAppW_frame m m' f x r h).mono
    (by intro b hb; simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl
        · exact leafA_app.1
        · exact leafA_app.2.1
        · exact leafA_app.2.2)
    (by intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl
        · exact leafC_app.1
        · exact leafC_app.2)

/-- `check_opaque_val` is one of the loop's functions. -/
theorem checkOpaqueVal_loop : "check_opaque_val" ∈ loopFns := List.mem_of_getElem? (i := 208) rfl

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
    (hcl : LeafClosed p) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {env : ConLeche.Env} {a : AState} {n : Nat} {m m' : Mem} {c : Word} {r : List Word}
    {cn : ConLeche.Name}
    (h : rpgW p n m vis c = some (r, m')) (hS : StageC dn vis fe env m a) (hc : c.toNat < 2 ^ 32)
    (hd : denoteN a.store.ns (decI c) = some cn) :
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
  cases h2 : stubM "loose_bvars_bounded_fast" s1.mem [4000000000, 0, e] with
  | none => rw [h2] at h; simp [rpgK2] at h
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2, rpgK2_some] at h
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2, -⟩ :=
    looseBVarsBoundedFastT_spec dn vis fe 4000000000 0 e he1l s1.mem m2 a1 r2 h2 hT1
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
  cases h3 : stubM "has_fvar_fast" m2 [4000000000, e] with
  | none => rw [h3] at h; simp [rpgK3] at h
  | some rm3 =>
  obtain ⟨r3, m3⟩ := rm3
  rw [h3, rpgK3_some] at h
  obtain ⟨x3, a3, hrun3, hS3, hg3, hx3, -⟩ :=
    hasFvarFastT_spec dn vis fe 4000000000 e he1l m2 m3 a2 r3 h3 hS2
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
  cases h4 : stubM "all_level_params_defined" m3 [0, 0, e] with
  | none => rw [h4] at h; simp [rpgK4] at h
  | some rm4 =>
  obtain ⟨r4, m4⟩ := rm4
  rw [h4, rpgK4_some] at h
  obtain ⟨x4, a4, hrun4, hS4, hg4, hx4, -⟩ :=
    allLevelParamsDefinedT_spec dn vis fe 0 0 e he1l [] m3 m4 a3 r4 h4
      ⟨hS3, by simp [decHL, hslice?]⟩
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
  cases h5 : stubM "consts_resolve_ffast" m4 [vis, e] with
  | none => rw [h5] at h; simp [rpgK5] at h
  | some rm5 =>
  obtain ⟨r5, m5⟩ := rm5
  rw [h5, rpgK5_some] at h
  obtain ⟨x5, a5, hrun5, hS5, hg5, hx5⟩ :=
    constsResolveFFastT_spec dn vis fe e he1l m4 m5 a4 r5 h5 hS4
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hrun : (reducePinGuard fe (decI c)).run a = .ok (x5, a5) := by
    simp only [reducePinGuard, StateT.run_bind, hrun1, exc_ok_bind', hrun2, ex2, Bool.not_true,
      Bool.false_eq_true, if_false, hrun3, ex3, hrun4, ex4]
    exact hrun5
  obtain ⟨hC, hx, hr⟩ := rpg_fin hS.check hd hrun hS5
  exact ⟨x5, a5, hrun, hC, hx, hr, hg1.trans (hg2.trans (hg3.trans (hg4.trans hg5))), hx5⟩

end L.Arena
