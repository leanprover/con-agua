module

import ConAgua.Arena.RecCheckSpec.TargetRecPins
import ConAgua.Arena.IndSumSpec.SoaW
public import ConAgua.Verdict.VCtx
public import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndInstallSpec.NhW
import ConAgua.Arena.IndInstallSpec.PartsAt
import ConAgua.Arena.IndPartsSpec.BlockRecLpsOk
import ConAgua.Arena.IndPartsSpec.BlockRecNameSetOk
import ConAgua.Arena.IndPartsSpec.BlockSplitRecs
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.RecCheckSpec.TpsW
import all ConAgua.Arena.RecCheck

@[expose] public section

/-!
# `target_rec_pins`: one model and one refinement for both outcomes

`trpE` (`l_model … unified`): every callee through its run (`callE`; they are outside the verdict
closure). `trp_ref` refines `targetRecPins` for both outcomes; its ok half is
`targetRecPins_refines`, its error half read by `gen_rec_check_prep`'s refinement (`grpB_ref`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

l_model trpE_spec (p : Prog) (hf : p.lookup "target_rec_pins" = some targetRecPins)
  fns [hf ↦ trpE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified

/-! ## The twin's name pins, from `namesTwin`'s run -/

/-- **`namesTwin`'s run, step by step**: the twin's `n₀`, the wanted auxiliary names, its answer
(the set test, then no two recursors sharing a name). -/
theorem namesTwin_run {bs : BlockShape} {a a' : AState} {b : Bool} (h : (namesTwin bs).run a = .ok (b, a')) :
    ∃ n0 a1 want, (rpN0 bs).run a = .ok (n0, a1) ∧
      ((List.range (rpAux bs).length).mapM fun i => internNNode (.str n0 s!"rec_{i + 1}")).run a1 =
        .ok (want, a') ∧
      b = (rpSetOk ((rpAux bs).map (·.cvR.name)) want && nameNodup (bs.recs.map (·.cvR.name))) := by
  unfold namesTwin at h
  simp only [StateT.run_bind] at h
  cases hn : (rpN0 bs).run a with
  | error e => rw [hn] at h; cases h
  | ok x =>
  obtain ⟨n0, a1⟩ := x
  rw [hn] at h
  simp only [except_ok_bind] at h
  cases hw : ((List.range (rpAux bs).length).mapM fun i => internNNode (.str n0 s!"rec_{i + 1}")).run a1 with
  | error e => rw [hw] at h; cases h
  | ok y =>
  obtain ⟨want, a2⟩ := y
  rw [hw] at h
  simp only [except_ok_bind] at h
  refine ⟨n0, a1, want, rfl, ?_⟩
  split at h <;> cases h <;> exact ⟨hw, by simp [*]⟩

/-- What `target_rec_pins` gives besides the twin's run (from `m`): the stage relation, the growth. -/
structure TrpPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem)
    (a' : AState) : Prop where
  stage : StageR vis fe m' a'
  grow : IWGrow m m'

section sims
variable {p : Prog} (L : RpLook p) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

include L in
/-- **`target_rec_pins` refines `targetRecPins`, both outcomes**: the callees run through their
runs (`callE`; outside the verdict closure, so their errors claim nothing), against the twin's
steps; `target_rec_pins_names` is the twin's name pins from `n₀` on (`namesTwin_run`), checked in
one answer where the twin has two `fail`s. -/
theorem trp_ref (N : Nat) {m : Mem} {a : AState} {pp bo bl : Word} {bs : BlockShape}
    {blk : List IConstantInfo}
    (hS : StageR vis fe m a) (hq : DecB (fun m => decBS m pp.toNat) m bs)
    (hblk : DecB (fun m => decEBlk dn m bo.toNat bl.toNat) m blk) :
    RefE (VerdictCtx p) (trpE p N m pp bo bl) (ConRon.Arena.targetRecPins bs blk) a
      (fun v _ a' => TrpPost dn vis fe m v.2 a') := by
  sorry

include L in
/-- **`target_rec_pins` refines `targetRecPins`** (`trp_ref`'s ok half; through the stubs
`name_rec`, `name_rec_i`, `intern_nanon`, the reserved-name tests): the shape and the block decoded
below the tops, nothing else. -/
@[refines ConRon.Arena.targetRecPins]
theorem targetRecPins_refines (n : Nat) (s₀ : St) (a₀ : AState) (pp bo bl : Word) (bs : BlockShape)
    (blk : List IConstantInfo) (hS : StageR vis fe s₀.mem a₀)
    (hq : DecB (fun m => decBS m pp.toNat) s₀.mem bs)
    (hblk : DecB (fun m => decEBlk dn m bo.toNat bl.toNat) s₀.mem blk) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 3)) "target_rec_pins" [pp, bo, bl]
    ⦃fun _r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.targetRecPins bs blk) a₀ ∧
      StageR vis fe s'.mem (AM.st (ConRon.Arena.targetRecPins bs blk) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (trpE_spec p L.pins (n + 3) s₀ pp bo bl) (trp_ref L (n + 3) hS hq hblk)) ?_
  rintro _r s' ⟨hl, _, a', run, hR⟩
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, by rw [hst]; exact hR.stage, hR.grow⟩

end sims


end L.Ind
