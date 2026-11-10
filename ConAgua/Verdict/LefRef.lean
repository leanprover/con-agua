module

import ConAgua.Arena.IndRealLvlC
public import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndRealLvlT
import ConAgua.Arena.RefWalk
public import ConAgua.Arena.TwinStep
public import ConRon.Bridge.Inductives.Run
import all ConAgua.Arena.IndIface

@[expose] public section

/-!
# `lvl_eq_fueled`: one model and one refinement for both outcomes

`lvl_eq_fueled(u, v)` is the twin's `liftFueled "level comparison" (← lvlEq? u v)` (`lefT`): its
unified model `lefE` calls `lvl_eq_c` (outside the verdict closure) through its run; `lef_ref`
refines it against `lefT` under `NVAt p "lvl_eq_c"` (its one error of class `1`/`2` is its own
decline, the twin's `liftFueled` on `none`). The post `LefPost` carries `lvlEq?`'s run (callers
splice it into their twins, `lefT_bind`), the `StageT` package, and the `StageC` package as a
conditional field. The callers' hand models read the function through its run
(`cl n "lvl_eq_fueled" [u, v] m`); their ok refinements take `RefE.run_okW`, their error claims
`RefE.run_err`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

noncomputable section

set_option experimental.vcgen true

namespace L.Arena

open L.Ind

/-- A callee outside the verdict closure: its errors are of class `0` (`callE_nv`). -/
def NVAt (p : Prog) (f : FnName) : Prop :=
  ∀ n args m e, callE p n f args m = .error e → e.cls = 0

l_model lefE_spec (p : Prog) (hf : p.lookup "lvl_eq_fueled" = some lvlEqFueled)
  fns [hf ↦ lefE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  finish [tierW, idxW] unified

/-- **The twin of `lvl_eq_fueled`**: the level comparison, `none` (out of fuel) a failure. -/
def lefT (u v : LIdx) : AM Bool := lvlEq? u v >>= liftFueled "level comparison"

/-- A caller's `liftFueled "level comparison" (← lvlEq? u v)`, then the rest. -/
theorem lefT_bind {β : Type} (u v : LIdx) (k : Bool → AM β) :
    (lvlEq? u v >>= fun x => liftFueled "level comparison" x >>= k) = lefT u v >>= k := by
  simp only [lefT, bind_assoc]

/-- What `lvl_eq_fueled` gives besides the twin's answer `b` (from `m`, `a`): `lvlEq?`'s run,
the word, the stage relation, the growth, the frame (only the core's memos); under `StageC` and `AbsOK` before, both after and the
twin's step a `PStep`. -/
structure LefPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (u v : Word)
    (m : Mem) (a : AState) (w : Word) (m' : Mem) (b : Bool) (a' : AState) : Prop where
  run : (lvlEq? (decI u) (decI v)).run a = .ok (some b, a')
  res : w = if b then 1 else 0
  stage : StageT dn vis fe m' a'
  grow : IWGrow m m'
  mfr : MFr [] [] m m'
  stageC : ∀ env, StageC dn vis fe env m a → AbsOK m →
    StageC dn vis fe env m' a' ∧ AbsOK m' ∧ ConRon.Bridge.Inductives.PStep a a'

/-- **`lvl_eq_fueled` refines `lefT`, both outcomes**: `lvl_eq_c` (outside the verdict closure)
by `lvlEqC_simTE` (`lvlEqC_simC` under `StageC`); its word `0` is `lvlEq?`'s `none`, the
twin's `liftFueled` failure. -/
theorem lef_ref {p : Prog} (hcl : CoreStageClosed p) (hL : LvlCacheProg p) (n : Nat)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}
    {u v : Word} (hS : StageT dn vis fe m a) (hu : H u) (hv : H v) {lu lv : ConLeche.Level}
    (hdu : denoteL a.store.ls (decI u) = some lu) (hdv : denoteL a.store.ls (decI v) = some lv) :
    RefE (NVAt p "lvl_eq_c") (lefE p n m u v) (lefT (decI u) (decI v)) a
      (fun w b a' => LefPost dn vis fe u v m a w.1 w.2 b a') := by
  cases n with
  | zero => rw [lefE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  rw [lefE.arm1]; unfold lefT
  refine RefE.bindCall (Q := fun b a1 x => StageT dn vis fe b.2 a1 ∧ IWGrow m b.2 ∧ decLvlEq b.2 b.1 x)
    (fun _ => lefE.k_lvl_eq_c.none ..) (fun hnv _ h1 => ErrClaim.of_cls0 (hnv _ _ _ _ h1))
    (fun b h => lvlEqC_simTE p hcl hL n hS u v hu hv lu lv hdu hdv b.1 b.2 h)
    fun r1 m1 x a1 h1 hrun ⟨hSt, hg, hdec⟩ => ?_
  have h1' := callW_of_callE h1
  unfold decLvlEq at hdec
  rw [← bind_pure (liftFueled _ x)]
  dsimp only [lefE.k_lvl_eq_c]
  refine RefE.guardOpt rfl (fun h0 => by rcases x with _ | _ | _ <;> grind)
    (fun hx => by subst hx; exact hdec) fun b hb h0 => ?_
  subst hb
  refine RefE.ret rfl ⟨hrun, ?_, hSt, hg,
    MFr.of_frame (run_memFrame hcl.lvl (by decide) (run_of_callW h1')).1 coreStageA_stage coreStageC_stage,
    fun env hC hA => ?_⟩
  · cases b <;> simp at hdec ⊢ <;> simp [hdec]
  obtain ⟨x', a1', hrun', hC1, -, -, hA1, hP⟩ :=
    lvlEqC_simC p hcl hL n hC hA u v hu hv lu lv hdu hdv r1 m1 h1'
  rw [hrun] at hrun'
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj hrun')
  exact ⟨hC1, hA1, hP⟩

end L.Arena

end
