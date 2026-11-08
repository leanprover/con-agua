module

public import ConAgua.Arena.RecCheckSpec.TpsW
import ConAgua.Arena.RecCheckSpec.TpnB
import ConAgua.Arena.IndPartsSpec.BlockRecLpsOk
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.IndPartsSpec.EqW
import all ConAgua.Arena.RecCheck

@[expose] public section

/-!
# TargetRecPins: `ConRon.Arena.targetRecPins`

The stage relation across `block_rec_lps_ok` (`lokW_stage`), the record reads (`trpRd`);
`target_rec_pins`' refinement is `trp_ref` (`Verdict/IndBRecPins.lean`).
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
theorem lokW_stage {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m m' : Mem} {q : Word} {r : List Word} {bs : BlockShape} (h : lokW n m q = some (r, m'))
    (hS : StageR vis fe m a) (hq : DecB (fun m => decBS m q.toNat) m bs) :
    r = [if ConRon.Arena.blockRecLpsOk bs then 1 else 0] ∧ StageR vis fe m' a ∧ IWGrow m m' := by
  obtain ⟨hI1, -, hsz, hEs, hc⟩ := hS.iw
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
  sorry

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

/-- A word of a decoded record below the top, in any memory grown into. -/
theorem trpRd {m m' : Mem} (hg : IWGrow m m') {pp : Word} {i v : Nat} (h : iwN (truncM m) (pp.toNat + i) = some v)
    (hi : (pp + UInt64.ofNat i).toNat = pp.toNat + i) :
    rdW (m'.arr64 IW) (pp + UInt64.ofNat i) = UInt64.ofNat v ∧ v < 2 ^ 64 := by
  obtain ⟨hw, hvb, hlt⟩ := partsIwRd h hi
  exact ⟨by rw [partsRdIW_grow hg (by rw [hi]; exact hlt), hw], hvb⟩

end L.Ind

end

end
