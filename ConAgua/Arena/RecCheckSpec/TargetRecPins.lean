import ConAgua.Arena.IndSumSpec.SoaW
import ConAgua.Arena.RecCheckSpec.TpsW
import ConAgua.Arena.IndInstallSpec.NhW
import ConAgua.Arena.IndPartsSpec.BlockRecLpsOk
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# TargetRecPins: `ConRon.Arena.targetRecPins`

The twin's `targetRecPins` when its tests pass (`trp_twin`), the stage relation across
`block_rec_lps_ok` (`lokW_stage`), the record reads (`trpRd`); `target_rec_pins`' refinement is
`trp_ref` (`Verdict/IndBRecPins.lean`).
-/

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **`block_rec_lps_ok` under the stage relation**: no hypothesis beyond the shape decoded below
the tops. -/
theorem lokW_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m m' : Mem} {q : Word} {r : List Word} {bs : BlockShape} (h : lokW n m q = some (r, m'))
    (hS : StageR dn vis fe m a) (hq : DecB (fun m => decBS m q.toNat) m bs) :
    r = [if ConRon.Arena.blockRecLpsOk bs then 1 else 0] ∧ StageR dn vis fe m' a ∧ IWGrow m m' := by
  obtain ⟨hI1, -, hsz, hEs, hc⟩ := hS.2
  obtain ⟨hr, hg, hf, hw⟩ := lokW_ok n m m' q r bs h (hq.get (decBS_mono _)) (hq.stab (decBS_mono _))
    (rpShape9 hq) hsz hc hEs
  exact ⟨hr, stage_frame_iw hS hf (by rw [← hf.size IW]; exact hw hI1), hg⟩

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section arms
variable (p : Prog) (n : Nat) (m : Mem) (reco recl auxo auxl : Word) (r rw : List Word)
theorem tpnK4_some : tpnK4 p n (some (r, m)) = tpnK5 (callW p n "sl_nodup" [r.headD 0, r.tail.headD 0] m) := rfl
theorem tpnK2_some : tpnK2 p n reco recl rw (some (r, m)) = tpnK3 p n reco recl
    (callW p n "sl_set_eq" [rw.headD 0, rw.tail.headD 0, r.headD 0, r.tail.headD 0] m) := rfl
theorem tpnK1_some : tpnK1 p n reco recl auxo auxl (some (r, m)) =
    tpnK2 p n reco recl r (callW p n "ptr_list_names" [auxo, auxl] m) := rfl
theorem tpnK0_some : tpnK0 p n reco recl auxo auxl (some (r, m)) = tpnB p n reco recl auxo auxl (r.headD 0) m := rfl
end arms
attribute [ind_grind] tpnK4_some tpnK2_some tpnK1_some tpnK0_some

set_option maxHeartbeats 1600000 in
theorem tpn_spec (p : Prog) (hp : p.lookup "target_rec_pins_names" = some targetRecPinsNames) (n : Nat)
    (s₀ : St) (mo k reco recl auxo auxl : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "target_rec_pins_names" [mo, k, reco, recl, auxo, auxl]
    ⦃fun r s' => LocEq s' s₀ ∧ tpnW p n s₀.mem mo k reco recl auxo auxl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, targetRecPinsNames]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "intern_nanon", callW_spec p n "block_rec_want_aux_names",
      callW_spec p n "ptr_list_names", callW_spec p n "sl_set_eq", callW_spec p n "sl_nodup"] <;>
    finish (gen := 40) (instances := 20000) [tpnW, tpnB, rdW_eq]

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section arms
variable (p : Prog) (n : Nat) (m : Mem) (pp k recl cso csl : Word) (r ra : List Word)
theorem tpsK3_some : tpsK3 p n ra (some (r, m)) =
    tpsK4 (callW p n "sl_eq" [ra.headD 0, ra.tail.headD 0, r.headD 0, r.tail.headD 0] m) := rfl
theorem tpsK2_some : tpsK2 p n cso csl (some (r, m)) = tpsK3 p n r (callW p n "ptr_list_names" [cso, csl] m) := rfl
theorem tpsK1_some : tpsK1 p n cso csl (some (r, m)) =
    tpsK2 p n cso csl (callW p n "ptr_list_names" [r.headD 0, r.tail.headD 0] m) := rfl
end arms
attribute [ind_grind] tpsK3_some tpsK2_some tpsK1_some

set_option maxHeartbeats 1600000 in
theorem tps_spec (p : Prog) (hp : p.lookup "target_rec_pins_split" = some targetRecPinsSplit) (n : Nat)
    (s₀ : St) (pp k recl bo bl : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "target_rec_pins_split" [pp, k, recl, bo, bl]
    ⦃fun r s' => LocEq s' s₀ ∧ tpsW p n s₀.mem pp k recl bo bl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, targetRecPinsSplit]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "block_split", callW_spec p n "block_shape_all_ctors",
      callW_spec p n "ptr_list_names", callW_spec p n "sl_eq"] <;>
    finish (gen := 40) (instances := 20000) [tpsW, rdW_eq]

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The twin, when every test passes -/

/-- **The twin's `targetRecPins` passes** when its tests do. -/
theorem trp_twin (bs : BlockShape) (blk : List IConstantInfo) (a a1 a2 a3 : AState)
    (h0 : ConRon.Arena.blockRecLpsOk bs = true)
    (h1 : (ConRon.Arena.blockRecNamesUnreserved bs.recs).run a = .ok (true, a1))
    (h2 : (ConRon.Arena.blockRecNameSetOk bs.members (bs.recs.filter fun rc => rc.tgt < bs.k)).run a1 =
      .ok (true, a2))
    (h3 : (namesTwin bs).run a2 = .ok (true, a3)) (h4 : splitOk bs blk = true) :
    (ConRon.Arena.targetRecPins bs blk).run a = .ok ((), a3) := by
  unfold namesTwin at h3
  simp only [StateT.run_bind] at h3
  cases hn : (rpN0 bs).run a2 with
  | error e => rw [hn] at h3; cases h3
  | ok x =>
  obtain ⟨n0, a2'⟩ := x
  rw [hn] at h3
  simp only [except_ok_bind] at h3
  cases hw : ((List.range (rpAux bs).length).mapM fun i => internNNode (.str n0 s!"rec_{i + 1}")).run a2' with
  | error e => rw [hw] at h3; cases h3
  | ok y =>
  obtain ⟨want, a2''⟩ := y
  rw [hw] at h3
  simp only [except_ok_bind] at h3
  have hc : rpSetOk ((rpAux bs).map (·.cvR.name)) want = true := by
    refine Classical.byContradiction fun hc => ?_; rw [ite_eq_right hc] at h3; cases h3
  rw [ite_eq_left hc] at h3
  have hnd : nameNodup (bs.recs.map (·.cvR.name)) = true ∧ a2'' = a3 := by
    change Except.ok (nameNodup (bs.recs.map (·.cvR.name)), a2'') = Except.ok (true, a3) at h3
    simp only [Except.ok.injEq, Prod.mk.injEq] at h3
    exact ⟨h3.1, h3.2⟩
  obtain ⟨hnd, rfl⟩ := hnd
  unfold rpSetOk at hc
  unfold rpAux at hw hc
  unfold splitOk at h4
  unfold ConRon.Arena.targetRecPins
  rcases hm : bs.members with _ | ⟨ms0, rest⟩
  · simp only [rpN0, hm] at hn
    rcases hb : ConRon.Arena.blockSplit blk with _ | ⟨cvTs, cs, rs⟩ <;> rw [hb] at h4
    · cases h4
    rw [hm] at h2
    have hw' : ((List.range (List.filter (fun rc => !decide (rc.tgt < bs.k)) bs.recs).length).mapM
        fun i => internNNode (.str n0 (toString "rec_" ++ (i + 1).repr))).run a2' = .ok (want, a2'') := hw
    simp [StateT.run_bind, hw', h0, h1, h2, hn, hnd, h4, except_ok_bind]
    rw [ite_eq_left hc]; simp; rfl
  · simp only [rpN0, hm] at hn
    change Except.ok (ms0.cvT.name, a2) = Except.ok (n0, a2') at hn
    simp only [Except.ok.injEq, Prod.mk.injEq] at hn
    obtain ⟨rfl, rfl⟩ := hn
    rcases hb : ConRon.Arena.blockSplit blk with _ | ⟨cvTs, cs, rs⟩ <;> rw [hb] at h4
    · cases h4
    rw [hm] at h2
    have hw' : ((List.range (List.filter (fun rc => !decide (rc.tgt < bs.k)) bs.recs).length).mapM
        fun i => internNNode (.str ms0.cvT.name (toString "rec_" ++ (i + 1).repr))).run a2 = .ok (want, a2'') := hw
    simp [StateT.run_bind, hw', h0, h1, h2, hnd, h4, except_ok_bind]
    rw [ite_eq_left hc]; simp; rfl

/-- A word of a decoded record below the top, in any memory grown into. -/
theorem trpRd {m m' : Mem} (hg : IWGrow m m') {pp : Word} {i v : Nat} (h : iwN (truncM m) (pp.toNat + i) = some v)
    (hi : (pp + UInt64.ofNat i).toNat = pp.toNat + i) :
    rdW (m'.arr64 IW) (pp + UInt64.ofNat i) = UInt64.ofNat v ∧ v < 2 ^ 64 := by
  obtain ⟨hw, hvb, hlt⟩ := partsIwRd h hi
  exact ⟨by rw [partsRdIW_grow hg (by rw [hi]; exact hlt), hw], hvb⟩

end L.Ind

end

end
