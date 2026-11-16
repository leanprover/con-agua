module

public import ConAgua.Arena.WhnfCoreAppLoop
public import ConAgua.Arena.RecLayout.CIDec
import ConAgua.Arena.RefWalk
import ConAgua.Arena.WhnfCoreRefine
import ConAgua.Arena.WhnfCoreProj
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
public import Std.WP.Tactic
import all ConAgua.Arena.WhnfCore

@[expose] public section

/-!
# The stuck spine (con-ron's #556 P-A): `iota_target` and `whnf_stuck`

`iota_target(vis, h)` refines `iotaTarget` (its answer `(1, mI)` is the twin's `some (mI + 1)`),
`whnf_stuck(mode, vis, d, h, e)` refines `whnfStuck`: the spine's arguments pushed at the top
(`get_app_args`), `iota_rec_at` at the prefix `mI + 1` (the twin's `iotaRecAt … args k` reads only
`takeEidx args k`, `iotaRecAt_prefix`), the reduct re-applied (`mk_app_n_from`), the top put back.
Each over its unified model; `whnf_stuck`'s errors are `iota_rec_at`'s (`AppG`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

l_model whnfStuckE_spec (p : Prog) (hf : p.lookup "whnf_stuck" = some whnfStuckL)
  fns [hf ↦ whnfStuckE list]
  specs [callW_spec p n "env_find", callW_spec p n "ls_node", callW_spec p n "get_app_args",
    callW_spec p n "mk_app_n_from"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-! ## Tags off the handle word -/

/-- A tag word is one of 16. -/
theorem tagW_fin (x : Word) (hx : HW x) : ∃ k : Fin 16, tagW x = (k.val : Nat).toUInt64 :=
  ⟨⟨(tagW x).toNat, tagW_lt x hx⟩, by simp⟩

/-- `isStuckHead` off the tag mask `334` (`fvar`, `sort`, `const`, `forallE`, `lit`). -/
theorem isStuckHead_w (h : Word) (hh : HW h) :
    isStuckHead (decE h) = ((334 : Word) >>> tagW h &&& 1 != 0) := by
  simp only [isStuckHead, decE_tag h hh]
  obtain ⟨k, hk⟩ := tagW_fin h hh
  rw [hk]; clear hk; revert k; decide

/-- `whnfCoreStuckTag` off the tag mask `657` (`bvar`, `app`, `letE`, `proj`). -/
theorem stuckTag_w (e : Word) (he : HW e) :
    whnfCoreStuckTag (decE e) = ((657 : Word) >>> tagW e &&& 1 == 0) := by
  simp only [whnfCoreStuckTag, decE_tag e he]
  obtain ⟨k, hk⟩ := tagW_fin e he
  rw [hk]; clear hk; revert k; decide

/-- `whnfCoreKey` as the loop's `key` word. -/
theorem key_w (h e : Word) (hh : HW h) (he : HW e) :
    whnfCoreKey (decE h) (decE e) =
      (((640 : Word) >>> tagW e &&& 1 ||| (if tagW e = 4 then (1 : Word) else 0) &&& (1 - ((334 : Word) >>> tagW h &&& 1))) != 0) := by
  simp only [whnfCoreKey, isStuckHead, decE_tag e he, decE_tag h hh]
  obtain ⟨k, hk⟩ := tagW_fin e he
  obtain ⟨j, hj⟩ := tagW_fin h hh
  rw [hk, hj]; clear hk hj; revert k j; decide

/-- `whnfCoreCheapSafe` as the loop's `safe` word. -/
theorem safe_w (h e : Word) (hh : HW h) (he : HW e) :
    whnfCoreCheapSafe (decE h) (decE e) =
      (((128 : Word) >>> tagW e &&& 1 ||| (if tagW e = 4 then (1 : Word) else 0) &&&
        (((334 : Word) >>> tagW h &&& 1) ||| (if tagW h = 5 then (1 : Word) else 0))) != 0) := by
  simp only [whnfCoreCheapSafe, isStuckHead, decE_tag e he, decE_tag h hh]
  obtain ⟨k, hk⟩ := tagW_fin e he
  obtain ⟨j, hj⟩ := tagW_fin h hh
  rw [hk, hj]; clear hk hj; revert k j; decide


/-- The `key` word is a bit. -/
theorem key01 (h e : Word) (hh : HW h) (he : HW e) :
    ((640 : Word) >>> tagW e &&& 1 ||| (if tagW e = 4 then (1 : Word) else 0) &&& (1 - ((334 : Word) >>> tagW h &&& 1))) = 0 ∨
    ((640 : Word) >>> tagW e &&& 1 ||| (if tagW e = 4 then (1 : Word) else 0) &&& (1 - ((334 : Word) >>> tagW h &&& 1))) = 1 := by
  obtain ⟨k, hk⟩ := tagW_fin e he
  obtain ⟨j, hj⟩ := tagW_fin h hh
  rw [hk, hj]; clear hk hj; revert k j; decide

/-! ## The refinements -/

/-- The `viewConst` projection of a `const` handle past its view checks. -/
theorem viewConst_w (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (hv : viewOK m h CONST) :
    a.store.viewConst (decE h) = some (decI (tfld m CONST (tierW h) (idxW h) 0),
      decI (tfld m CONST (tierW h) (idxW h) 1)) := by
  obtain ⟨k, hk, hn, hu⟩ := node_of m a h constCS CeRecRel (·.consts) _ hR.const hv.2
  simp only [EStore.viewConst, EStore.persGetConst]
  rw [proj_tier m a hR h hh (fun t i => t.getConst i) hv.1]
  simp only [ETables.getConst, Tbl.node?, decE_idx h (narrow_of_cnt m h hR.const rfl hv.2)]
  rw [hk]
  simp [hn, hu, decI_word]

/-- `eidxCopyUpto` up to `k` reads only the first `k` entries. -/
theorem eidxCopyUpto_prefix (xs : Array EIdx) (k : Nat) (hk : k ≤ xs.size) :
    ∀ (K i : Nat) (out : Array EIdx), k - i = K →
      eidxCopyUpto xs k i out = eidxCopyUpto (xs.extract 0 k) k i out := by
  intro K
  induction K with
  | zero =>
    intro i out hK
    rw [eidxCopyUpto, eidxCopyUpto]
    have : ¬ (i < k ∧ i < xs.size) := by omega
    have h2 : ¬ (i < k ∧ i < (xs.extract 0 k).size) := by simp; omega
    simp only [this, h2, dite_false]
  | succ K ih =>
    intro i out hK
    rw [eidxCopyUpto, eidxCopyUpto]
    have h1 : i < k ∧ i < xs.size := by omega
    have h2 : i < k ∧ i < (xs.extract 0 k).size := by simp; omega
    simp only [h1, h2, and_self, dite_true]
    rw [ih (i + 1) _ (by omega)]
    congr 2
    simp [Array.getElem_extract]

/-- A leading part of a stack slice. -/
theorem SpineR.prefix {m : Mem} {off cnt : Word} {xs : Array EIdx} (h : SpineR m off cnt xs)
    (c : Word) (hc : c.toNat ≤ cnt.toNat) : SpineR m off c (xs.extract 0 c.toNat) := by
  have hb := h.bound
  have hsz := h.size
  refine ⟨by simp; omega, by omega, fun i hi => h.lt i (by omega), fun i hi => ?_⟩
  have hi' : i < xs.size := by simp only [Array.size_extract] at hi; omega
  rw [Array.getElem_extract]
  simpa using h.get i hi'

section stuck
variable (p : Prog) (hp : WhnfCoreProg p) (hcc : CoreCallees p)

include hp hcc in
/-- **`whnf_stuck` refines `whnfStuck`, both outcomes**: its errors are `iota_rec_at`'s (`AppG`). -/
@[refines ConRon.Arena.whnfStuck]
theorem stuck_ref (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d h e : Word) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (hh : HW h) (he : HW e) :
    RefE (AppG p n) (whnfStuckE p (n + 1) s₀.mem mode vis d h e)
      (whnfStuck (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE h) (decE e))
      a₀ (CorePost decStep dn s₀.mem vis fe MM eb ResW) := by
  sorry

end stuck

end L.Arena
