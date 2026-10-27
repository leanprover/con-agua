import ConAgua.Arena.CoreWalks
import ConAgua.Arena.WalkLeavesRefine
import ConAgua.Census.Attr
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The scope walk and the leaf guard as the core's callees (lane `whnf3`)

`wscoped_bfast` and `leaf_guard` refine their twins under `ArenaD` and their memo relations
(`WalkScopeRefine.lean`, `WalkLeavesRefine.lean`); here they are lifted to `CoreS`, discharging
`IotaCallees`' `WscopedBFastOK` and `LeafGuardOK`. The twin state does not move (the walks only
read the store), the walks write arrays 151‥154 and `CTL` 152‥157 alone (`CoreS.frameM`), and their
memos' well-formedness, carried in `CoreMemos` (`WalkMemos`), comes back from their own posts.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

section bridges
variable {p : Prog}

/-- **`wscoped_bfast(d, e)` refines `wscopedBFast coreWalkFuel` under `CoreS`** (`WscopedBFastOK`). -/
@[refines ConRon.Arena.wscopedBFast]
theorem wscoped_core (hp : WsProg p) : WscopedBFastOK p := by
  intro n s₀ a₀ dn vis fe M eb d e hS hE
  cases n with
  | zero => exact CoreSpec.zeroW hp.wsfast _ _ _ _ _ _ _ _ _ _ _
  | succ n =>
  unfold CoreSpec
  apply L.M.triple_of_run
  intro s r s' hs hr
  obtain ⟨hloc, hI⟩ := L.M.of_run (P := fun s => s = s₀) hs hr
    (wscopedBFast_spec p hp.derb hp.wsf hp.wsp hp.wsgo hp.wsnode hp.wsc hp.wsfast n s₀ d e)
  subst hs
  obtain ⟨hrun, hM', hle, hf⟩ := wsFastW_ok n _ _ a₀ hS.arena hS.memos.2.2.1 d e _ hE hI
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  have hmem : CoreMemos s'.mem :=
    ⟨coreIl_frame hf (by decide) (by decide) hS.memos, coreAb_frame hf (by decide) (by decide) hS.memos,
      hM',
      let ⟨mp, hm⟩ := hS.memos.2.2.2.1
      ⟨mp, memoRG_frame coreFlSch coreFlSch_wf bmKey _ _ _ (by decide) (by decide) _ _ hf mp hm⟩,
      let ⟨mp, hm⟩ := hS.memos.2.2.2.2.1
      ⟨mp, memoRG_frame coreLsbSch coreLsbSch_wf bmKey _ _ _ (by decide) (by decide) _ _ hf mp hm⟩,
      hS.memos.2.2.2.2.2.frame hf (by decide) (by decide)⟩
  obtain ⟨hS', hSt⟩ := hS.frameM hf (by decide) (by simp) hmem
  refine ⟨hloc, hok, ⟨M, by rw [hst]; exact hS', KeptAll.refl _ _, hSt⟩, ?_, ?_⟩
  · rw [hres, decBool]
  · unfold ResH HW; have := UInt64.le_iff_toNat_le.mp hle
    have h1 : (1 : Word).toNat = 1 := rfl
    omega

/-- **`leaf_guard(fab, major)` refines `leafGuard coreWalkFuel` under `CoreS`** (`LeafGuardOK`). -/
@[refines ConRon.Arena.leafGuard]
theorem leafGuard_core (hp : LgProg p) : LeafGuardOK p := by
  intro n s₀ a₀ dn vis fe M eb fab major hS hF hJ
  cases n with
  | zero => exact CoreSpec.zeroW hp.lg _ _ _ _ _ _ _ _ _ _ _
  | succ n =>
  unfold CoreSpec
  apply L.M.triple_of_run
  intro s r s' hs hr
  obtain ⟨hloc, hI⟩ := L.M.of_run (P := fun s => s = s₀) hs hr (leafGuard_spec p hp n s₀ fab major)
  subst hs
  obtain ⟨hrun, hM', hle, hf⟩ :=
    lgW_ok n _ _ a₀ hS.arena ⟨hS.memos.2.2.2.1, hS.memos.2.2.2.2.1⟩ fab major _ hF hJ hI
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  have hmem : CoreMemos s'.mem :=
    ⟨coreIl_frame hf (by decide) (by decide) hS.memos, coreAb_frame hf (by decide) (by decide) hS.memos,
      let ⟨mp, hm⟩ := hS.memos.2.2.1
      ⟨mp, memoRG_frame coreWsSch coreWsSch_wf lfKey _ _ _ (by decide) (by decide) _ _ hf mp hm⟩,
      hM'.1, hM'.2, hS.memos.2.2.2.2.2.frame hf (by decide) (by decide)⟩
  obtain ⟨hS', hSt⟩ := hS.frameM hf (by decide) (by simp) hmem
  refine ⟨hloc, hok, ⟨M, by rw [hst]; exact hS', KeptAll.refl _ _, hSt⟩, ?_, ?_⟩
  · rw [hres, decBool]
  · unfold ResH HW; have := UInt64.le_iff_toNat_le.mp hle
    have h1 : (1 : Word).toNat = 1 := rfl
    omega

end bridges

end L.Arena
