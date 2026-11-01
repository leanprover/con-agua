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
  stage : StageR dn vis fe m' a'
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
    (hS : StageR dn vis fe m a) (hq : DecB (fun m => decBS m pp.toNat) m bs)
    (hblk : DecB (fun m => decEBlk dn m bo.toNat bl.toNat) m blk) :
    RefE (VerdictCtx p) (trpE p N m pp bo bl) (ConRon.Arena.targetRecPins bs blk) a
      (fun v _ a' => TrpPost dn vis fe m v.2 a') := by
  obtain _ | N := N
  · simp only [trpE]
    exact RefE.of_cls0 Err.cls_outOfFuel
  have hT : ∀ m : Mem, iwTop m < 2 ^ 64 := fun m => (rdW (m.arr64 CTL) 200).toNat_lt
  have hq9 := rpShape9 hq
  obtain ⟨hmem, hrecs, -⟩ := decBS_some (show decBS (truncM m) pp.toNat = some bs from hq)
  obtain ⟨mo, ml, hmo, hml, hmsB, hmb⟩ := partsAt (fun q => decMS_mono q) hmem
  obtain ⟨ro, rl, hro, hrl, hrsB, hrb⟩ := partsAt (fun q => decRS_mono q) hrecs
  have hms : PSlR0 decMS bs.members mo ml m := ⟨hmsB, hmb⟩
  have hrs : PSlR0 decRS bs.recs ro rl m := ⟨hrsB, hrb⟩
  have hk : ml.toNat = bs.k := (decPL_length _ hmsB).symm
  have hrlen : rl.toNat = bs.recs.length := (decPL_length _ hrsB).symm
  have hi : ∀ i, i < 9 → (pp + UInt64.ofNat i).toNat = pp.toNat + i := fun i hi => by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (show i < UInt64.size by rw [UInt64_size_eq]; omega)]
    exact Nat.mod_eq_of_lt (by have := hT m; omega)
  have rd0 : ∀ m', IWGrow m m' → rdW (m'.arr64 IW) pp = mo := fun m' hg => by
    have := (trpRd hg (i := 0) (by simpa using hmo) (by simp)).1
    simpa using this
  have rd1 : ∀ m', IWGrow m m' → rdW (m'.arr64 IW) (pp + 1) = ml := fun m' hg => by
    have := (trpRd hg (i := 1) hml (hi 1 (by omega))).1
    simpa using this
  have rd2 : rdW (m.arr64 IW) (pp + 2) = ro := by
    have := (trpRd (IWGrow.refl m) (i := 2) hro (hi 2 (by omega))).1
    simpa using this
  have rd3 : rdW (m.arr64 IW) (pp + 3) = rl := by
    have := (trpRd (IWGrow.refl m) (i := 3) (by simpa [Nat.add_assoc] using hrl) (hi 3 (by omega))).1
    simpa using this
  rw [trpE.arm1, rd2, rd3]
  unfold ConRon.Arena.targetRecPins
  -- `block_rec_lps_ok`
  refine RefE.onlyCall (fun _ => rfl) (fun hV => hV.nv) (_root_.L.Checker.nv_mem (by decide +kernel))
    fun r1 m1 h1 => ?_
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (blockRecLpsOk_spec p L.alloc L.erCopy L.erToIw L.slEq L.copy L.cons
    L.lpsOne L.lpsGo L.lps L.lpsOk N ⟨m, Locals.init []⟩ pp) (callW_of_callE h1)
  subst hs1
  obtain ⟨hr1, hS1, hg1⟩ := lokW_stage hW1 hS hq
  rw [trpE.k_block_rec_lps_ok.eq_2]
  refine RefE.guard rfl (fun hz => by rw [hr1] at hz; simpa using hz) (fun hc => by rw [hr1, hc]; rfl)
    fun _ _ => ?_
  -- `block_rec_names_unreserved`
  refine RefE.onlyCall (fun _ => rfl) (fun hV => hV.nv) (_root_.L.Checker.nv_mem (by decide +kernel))
    fun r2 m2 h2 => ?_
  obtain ⟨s2, hs2, -, hok2, hr2, hS2, hg2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (blockRecNamesUnreserved_refines p L.unres L.rrn N _ a dn fe vis ro rl bs.recs hS1
      ((hrsB.grow (OMono.decPL (fun q => decRS_mono q) _ _) hg1).stab (OMono.decPL (fun q => decRS_mono q) _ _))
      (by
        rcases hrb with h0 | h0
        · rw [h0]; simpa using ro.toNat_lt
        · have := hT m; omega)) (callW_of_callE h2)
  subst hs2
  dsimp only at hok2 hr2 hS2 hg2
  refine RefE.bind_right (partsRunOfOk hok2) ?_
  rw [trpE.k_block_rec_names_unreserved.eq_2, rd1 _ (hg1.trans hg2)]
  refine RefE.guard rfl (fun hz => by rw [hr2] at hz; simpa using hz) (fun hc => by rw [hr2, hc]; rfl)
    fun _ _ => ?_
  -- `block_rec_split_own_aux`
  refine RefE.onlyCall (fun _ => rfl) (fun hV => hV.nv) (_root_.L.Checker.nv_mem (by decide +kernel))
    fun r3 m3 h3 => ?_
  obtain ⟨s3, hs3, -, hW3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (soa_spec p L.toIndPartsProg L.soa N _ ro rl ml) (callW_of_callE h3)
  subst hs3
  dsimp only at hW3
  have hg12 := hg1.trans hg2
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := by
    cases N with
    | zero => simp [soaW] at hW3
    | succ n => exact ⟨n, rfl⟩
  obtain ⟨hS3, hg3, hown, haux⟩ := soaW_ok0 N' hW3 hS2 (hrs.grow (fun q => decRS_mono q) hg12)
  rw [hk] at hown haux
  rw [trpE.k_block_rec_split_own_aux.arm1, rd0 _ (hg12.trans hg3)]
  -- `block_rec_name_set_ok`
  refine RefE.onlyCall (fun _ => rfl) (fun hV => hV.nv) (_root_.L.Checker.nv_mem (by decide +kernel))
    fun r4 m4 h4 => ?_
  have hms3 := hms.grow (fun q => decMS_mono q) (hg12.trans hg3)
  obtain ⟨s4, hs4, -, hok4, hr4, hS4, hg4⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (blockRecNameSetOk_refines p L.toIndPartsProg3 N' _ _ dn vis fe mo ml (r3.headD 0) (r3.tail.headD 0)
      bs.members _ hS3 hms3 hown) (callW_mono (callW_of_callE h4) (by omega))
  subst hs4
  dsimp only at hok4 hr4 hS4 hg4
  refine RefE.bind_right (partsRunOfOk hok4) ?_
  rw [trpE.k_block_rec_name_set_ok.eq_2]
  refine RefE.guard rfl (fun hz => by rw [hr4] at hz; simpa using hz) (fun hc => by rw [hr4, hc]; rfl)
    fun _ _ => ?_
  -- `target_rec_pins_names`: the twin's name pins, from its `n₀` on
  refine RefE.onlyCall (fun _ => rfl) (fun hV => hV.nv) (_root_.L.Checker.nv_mem (by decide +kernel))
    fun r5 m5 h5 => ?_
  obtain ⟨s5, hs5, -, hW5⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (tpn_spec p L.names (N' + 1) ⟨s4.mem, Locals.init []⟩ mo ml ro rl (r3.tail.tail.headD 0)
      (r3.tail.tail.tail.headD 0)) (callW_mono (callW_of_callE h5) (by omega))
  subst hs5
  dsimp only at hW5
  have hg14 := (hg12.trans hg3).trans hg4
  obtain ⟨b5, a5, hrun3, hr5, hS5, hg5⟩ := tpnW_sim p L N' s4.mem _ mo ml ro rl _ _ bs hS4
    (hms.grow (fun q => decMS_mono q) hg14) (hrs.grow (fun q => decRS_mono q) hg14)
    (haux.grow (fun q => decRS_mono q) hg4) r5 s5.mem hW5
  obtain ⟨n0, a2, want, hn0, hwant, rfl⟩ := namesTwin_run hrun3
  rw [trpE.k_target_rec_pins_names.eq_2]
  rcases hm : bs.members with _ | ⟨ms0, rest⟩ <;> simp only [rpN0, hm] at hn0 <;>
    refine RefE.bind_right hn0 ?_
  all_goals
    refine RefE.bind_right hwant ?_
    by_cases hs : rpSetOk ((rpAux bs).map (·.cvR.name)) want = false
    · rw [ite_eq_left (by rw [hr5, hs]; rfl)]; exact RefE.twinFail rfl hs
    refine RefE.twinPass (b := rpSetOk ((rpAux bs).map (·.cvR.name)) want) (by simpa using hs) ?_
    refine RefE.guard rfl (fun hz => by rw [hr5] at hz; simpa [hs] using hz)
      (fun hnd => by rw [hr5, hnd, Bool.and_false]; rfl) fun _ _ => ?_
    -- `target_rec_pins_split`: the twin's constructor grouping
    refine RefE.onlyCall (fun _ => rfl) (fun hV => hV.nv) (_root_.L.Checker.nv_mem (by decide +kernel))
      fun r6 m6 h6 => ?_
    obtain ⟨s6, hs6, -, hW6⟩ := triple_of_callW (s₀ := ⟨s5.mem, Locals.init []⟩)
      (tps_spec p L.psplit (N' + 1) _ pp ml rl bo bl) (callW_mono (callW_of_callE h6) (by omega))
    subst hs6
    dsimp only at hW6
    have hg15 := hg14.trans hg5
    obtain ⟨b6, a6, hrun4, hr6, rfl, hS6, hg6⟩ := tpsW_sim p L N' s5.mem _ pp ml rl bo bl bs blk hS5
      (hq.grow (decBS_mono _) hg15) (hblk.grow (decEBlk_mono dn _ _) hg15) hk hrlen r6 s6.mem hW6
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj hrun4)
    rw [trpE.k_target_rec_pins_split.eq_2]
    rcases hb : ConRon.Arena.blockSplit blk with _ | ⟨cvTs, cs, rs⟩ <;> simp only [splitOk, hb] at hr6
    · exact RefE.abortAt (by simpa using hr6) fun _ => ErrClaim.fail _ _ rfl
    · exact RefE.guardIf rfl (fun hz => by rw [hr6] at hz; simpa using hz) (fun hc => by rw [hr6, hc]; rfl)
        fun _ _ => RefE.ret rfl ⟨hS6, hg15.trans hg6⟩

include L in
/-- **`target_rec_pins` refines `targetRecPins`** (`trp_ref`'s ok half; through the stubs
`name_rec`, `name_rec_i`, `intern_nanon`, the reserved-name tests): the shape and the block decoded
below the tops, nothing else. -/
@[refines ConRon.Arena.targetRecPins]
theorem targetRecPins_refines (n : Nat) (s₀ : St) (a₀ : AState) (pp bo bl : Word) (bs : BlockShape)
    (blk : List IConstantInfo) (hS : StageR dn vis fe s₀.mem a₀)
    (hq : DecB (fun m => decBS m pp.toNat) s₀.mem bs)
    (hblk : DecB (fun m => decEBlk dn m bo.toNat bl.toNat) s₀.mem blk) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 3)) "target_rec_pins" [pp, bo, bl]
    ⦃fun _r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.targetRecPins bs blk) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.targetRecPins bs blk) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (trpE_spec p L.pins (n + 3) s₀ pp bo bl) (trp_ref L (n + 3) hS hq hblk)) ?_
  rintro _r s' ⟨hl, _, a', run, hR⟩
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, by rw [hst]; exact hR.stage, hR.grow⟩

end sims


end L.Ind
