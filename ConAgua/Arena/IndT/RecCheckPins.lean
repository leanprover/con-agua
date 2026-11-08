module

import ConAgua.Arena.RecClassSpec.IhW
import ConAgua.Arena.RecGenSpec.DecCIIndCv
import ConAgua.Arena.RecGenSpec.CkcW
import ConAgua.Arena.RecClassSpec.ReadProg
public import ConAgua.Verdict.IndBPins
import ConAgua.Arena.IndPosSpec.NestCrest
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.RefWalk

@[expose] public section

/-!
# `target_major_pins`: one refinement for both outcomes

`tmp_ref` refines `targetMajorPins` with `tmpE` (`Verdict/IndBPins`) for both outcomes, from
`StageC`, `AbsOK` and the inputs' denotations con-ron's `targetMajorPins_spec` asks (the
parameters' denotations and their scoping at the rule prefix), the twin side transcribed from that
spec's proof: `targetPinTys` (`tpt_ref`), the head's intern (`internConstE_run`), `mkAppN`
(`mkAppN_run`), `inferTypeCore` (`inferC_rsim`, the core stubs' claim). Its post carries the
frame (`MFr`) for `class_majors`' `PosMR`; `tptE_mfr` is `target_pin_tys`' frame.
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dMajor)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section mfr
variable {p : Prog} (hq : KnotStageProg p)

include hq in
theorem coreC_mfr {n : Nat} {args r : List Word} {m m' : Mem}
    (h : realCall p n "infer_type_core" args m = some (r, m')) : MFr [] [] m m' :=
  MFr.of_frame (run_memFrame hq.closed (by decide) (run_of_callW h)).1 coreStageA_stage coreStageC_stage

include hq in
theorem tptE_mfr : ∀ (n : Nat) (m m' : Mem) (vis d xo xl v : Word),
    tptE p n m vis d xo xl = .ok (v, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, _, h => by rw [tptE.eq_def] at h; cases h
  | n + 1, m, m', vis, d, xo, xl, v, h => by
    by_cases hl : xl = 0
    · rw [tptE.arm1 p n m vis d xo xl hl] at h
      cases h; exact MFr.refl _ _ _
    rw [tptE.arm2 p n m vis d xo xl hl] at h
    rcases h1 : callE p n "infer_type_core" [vis, d, rdW (m.arr64 IW) xo] m with e1 | ⟨r1, m1⟩ <;>
      rw [h1] at h
    · rw [tptE.k_infer_type_core.none] at h; cases h
    rw [tptE.k_infer_type_core.arm1] at h
    refine (coreC_mfr hq (callW_of_callE h1)).trans ?_
    rcases h2 : tptE p n m1 vis d (xo + 1) (xl - 1) with e2 | ⟨v2, m2⟩ <;> rw [h2] at h
    · rw [tptE.k_target_pin_tys.none] at h; cases h
    rw [tptE.k_target_pin_tys.arm1] at h
    cases h
    exact tptE_mfr n _ _ _ _ _ _ _ h2

end mfr

/-- What `target_major_pins` gives besides the twin's run (from `m`): the stage invariant, the
growth, the abstraction memos, the frame. -/
structure TmpPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m m' : Mem) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  abs : AbsOK m'
  mfr : MFr [] [] m m'

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq henv in
/-- **`target_major_pins` refines `targetMajorPins .verified`, both outcomes** (twin side: con-ron's
`targetMajorPins_spec`'s proof): `tpt_ref`, the head's intern (`internConstE_run`), `mkAppN`
(`mkAppN_run`), `inferC_rsim` (the core stubs' claim). -/
theorem tmp_ref (N : Nat) (hN : N ≤ 2 ^ 62) {m : Mem} {a : AState} {rP Mp : Word}
    {M : TargetMajor} (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hM : DecB (fun m => decTM m Mp.toNat) m M)
    {MP : ConLeche.TargetMajor} (hMP : dMajor a.store M = some MP)
    (hds : MP.member = none → ∀ x ∈ MP.ds, ConLeche.Expr.WScoped rP.toNat x) :
    RefE (VerdictCtx p) (tmpE p N m vis rP Mp) (ConRon.Arena.targetMajorPins V fe rP.toNat M) a
      (fun v _ a' => TmpPost dn vis fe env m v.2 a') := by
  sorry

include hq henv in
/-- **`target_major_pins` refines `targetMajorPins`** under `StageC` (`tmp_ref`'s ok half; the
knot's `infer_type_core`; the major's denotation and its parameters' scoping as con-ron's
`targetMajorPins_spec` asks). -/
@[refines ConRon.Arena.targetMajorPins]
theorem targetMajorPins_refinesC (hp : TmpProg p) (N : Nat) (hN : N ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (rP Mp : Word) (M : TargetMajor) (hC : StageC dn vis fe env s₀.mem a₀)
    (hA : AbsOK s₀.mem) (hM : DecB (fun m => decTM m Mp.toNat) s₀.mem M)
    {MP : ConLeche.TargetMajor} (hMP : dMajor a₀.store M = some MP)
    (hds : MP.member = none → ∀ x ∈ MP.ds, ConLeche.Expr.WScoped rP.toNat x) :
    ⦃fun s => s = s₀⦄ invoke p (exec p N) "target_major_pins" [vis, rP, Mp]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.targetMajorPins V fe rP.toNat M) a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (ConRon.Arena.targetMajorPins V fe rP.toNat M) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (tmpE_spec p hp N s₀ vis rP Mp)
    (tmp_ref hq henv N hN hC hA hM hMP hds)) ?_
  rintro r s' ⟨hl, _, a', run, hR⟩
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, by rw [hst]; exact hR.stage, hR.grow, hR.abs⟩

end sims

end L.Ind
