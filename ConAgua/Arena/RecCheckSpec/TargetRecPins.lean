module

import ConAgua.Arena.RecCheckSpec.TpnB
public import ConAgua.Arena.IndPartsSpec.BlockRecLpsOk
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.IndDecStab
import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved
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
  have hI1 := hS.iw.iw
  have hsz := hS.iw.iwSize
  have hEs := hS.iw.erSize
  have hc := hS.iw.ctl
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
  exact ⟨by rw [rdW_iw_grow hg (by rw [hi]; exact hlt), hw], hvb⟩

end L.Ind

end

end
