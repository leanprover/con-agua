module

public import ConAgua.Arena.IndPosSpec.RxMapW
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import ConAgua.L.ModelGen
public import ConAgua.Arena.IndPosSpec.MatesW
import all ConAgua.Arena.IndPos

@[expose] public section

/-!
# Rx

`hiAt_specW`, `keyMap_specW`, the generated models and specs of `nest_hole_img_root` (`rxRoot_spec`) and
of the `replaceFVars` block (`rxSpec_all`).
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem hiAt_specW (p : Prog) (hp : p.lookup "nest_ctx_hi_at" = some nestCtxHiAt) (n : Nat) (s₀ : St)
    (ctx nf : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctx_hi_at" [ctx, nf]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ r.headD 0 = hiW s₀.mem ctx nf; ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, nestCtxHiAt]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;> finish [hiW, rdW_eq]

theorem keyMap_specW (p : Prog) (hp : p.lookup "nest_key_map" = some nestKeyMap) (n : Nat) (s₀ : St)
    (dO dL hO hL i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_key_map" [dO, dL, hO, hL, i]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ r.headD 0 = (kmW s₀.mem dO dL hO hL i).1 ∧
      r.tail.headD 0 = (kmW s₀.mem dO dL hO hL i).2; ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, nestKeyMap]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;> finish [kmW, rdW_eq]

end L.Ind

namespace L.Ind

open L.Arena

l_model rxRoot_spec (p : Prog) (L : RxLook p)
  fns [L.rt ↦ rxRootW tuple]
  specs [hiAt_specW p L.hi n, slGetD_specW p L.gd n, internConst_spec p L.cf L.cp L.ci n, mknF_spec p L.ad n]
  grind [arena_grind] fold [tierW, idxW] finish [tierW, idxW]

/-- The `replaceFVars` block: `fv_map_at`, `nest_hole_img`, `nest_hole_img_frame`,
`nest_hole_img_ds`, `nest_hole_img_ds_go`, `replace_fvars_go`, `replace_fvars_node`,
`replace_fvars`. -/
l_model rxSpec_all (p : Prog) (L : RxLook p)
  fns [L.fma ↦ rxMapW tuple, L.img ↦ rxImgW tuple, L.fr ↦ rxFrameW tuple, L.ds ↦ rxDsW tuple,
    L.dsg ↦ rxDsGoW void, L.go ↦ rxGoW, L.nd ↦ rxNodeW, L.rf ↦ rxW]
  specs [keyMap_specW p L.km n, pinWord_specV p L.hl.hpw n, internSort_spec p L.hl.hsf L.hl.hsp L.hl.his n,
    internFVar_spec p L.hl.hff L.hl.hfp L.hl.hif n, rxRoot_spec p L n, hiAt_specW p L.hi n,
    posRec2_specW p L.ha L.h2 n, posRec4_specW p L.ha L.h4 n, posRec5_specW p L.ha L.h5 n,
    internConst_spec p L.cf L.cp L.ci n, mknF_spec p L.ad n, iwAlloc_specW p L.ha n,
    eView_spec p L.hl.hv n, memoFindG_spec rfSch p _ L.rff n, memoPutG_spec rfSch p _ L.rfp n,
    mkApp_spec p L.hk.hd L.hk.appF L.hk.appP L.hk.appI L.hk.appM n,
    mkLam_spec p L.hk.hd L.hk.lamF L.hk.lamP L.hk.lamI L.hk.lamM n,
    mkForall_spec p L.hk.hd L.hk.forF L.hk.forP L.hk.forI L.hk.forM n,
    mkLet_spec p L.hk.hd L.hk.ltF L.hk.ltP L.hk.ltI L.hk.ltM n,
    mkProj_spec p L.hk.hd L.hk.prjF L.hk.prjP L.hk.prjI L.hk.prjM n,
    bankEnterG_spec 218 p _ L.rfe n, bankLeaveG_spec 218 p _ L.rfl' n, memoClearG_spec rfSch p _ L.rfc n]
  grind [arena_grind] fold [tierW, idxW] finish [tierW, idxW]

/-! ## Bridges over the generated models -/

/-- `fv_map_at` returns `nest_hole_img`'s results as they are. -/
theorem rxMapW_kImg (x : Option (Word × Word × Mem)) : rxMapW.k_nest_hole_img x = x := by
  rcases x with _ | ⟨_, _, _⟩ <;> rfl

/-- `nest_hole_img_ds_go` returns its recursive call's memory as it is. -/
theorem rxDsGoW_kGo (x : Option Mem) : rxDsGoW.k_nest_hole_img_ds_go x = x := by
  cases x <;> rfl

/-- The `rf_find` and `rf_put` after the node step are one `msetG`. -/
theorem rxGoW_kNode (h r : Word) (m1 : Mem) : rxGoW.k_replace_fvars_node h (some (r, m1)) =
    rxGoW.k_rf_put r (msetG rfSch m1 h (rdW (m1.arr64 CTL) 219 <<< 32) r) := by
  by_cases hf : mfindG rfSch m1 h (rdW (m1.arr64 CTL) 219 <<< 32) = []
  · rw [rxGoW.k_replace_fvars_node.abort1 _ _ _ hf, msetG, ite_eq_left hf]; rfl
  · rw [rxGoW.k_replace_fvars_node.arm1 _ _ _ hf, msetG_eq _ _ _ _ _ hf]

/-- `fv_map_at`'s result, or the handle itself where the map misses. -/
theorem rxGoW_kMap (h ok r : Word) (m1 : Mem) :
    rxGoW.k_fv_map_at h (some (ok, r, m1)) = some ((if ok ≠ 0 then r else h), m1) := by
  by_cases hok : ok ≠ 0
  · rw [rxGoW.k_fv_map_at.arm1 _ _ _ _ hok, ite_eq_left hok]
  · rw [rxGoW.k_fv_map_at.arm2 _ _ _ _ (Classical.not_not.mp hok), ite_eq_right hok]

section
variable {n : Nat} {m : Mem} {f fu h : Word}

/-- The four leaf kinds (`bvar`, `sort`, `lit`, `const`) return the handle. -/
theorem rxGoW_leaf (hf : fu ≠ 0) (hv : eViewW m h ≠ [])
    (hg : (eViewW m h).headD 0 = 0 ∨ (eViewW m h).headD 0 = 2 ∨ (eViewW m h).headD 0 = 8 ∨
      (eViewW m h).headD 0 = 3) : rxGoW (n + 1) m f fu h = some (h, m) := by
  rcases hg with hg | hg | hg | hg
  · exact rxGoW.arm1 _ _ _ _ _ hf hv hg
  · exact rxGoW.arm2 _ _ _ _ _ hf hv (by rw [hg]; decide) hg
  · exact rxGoW.arm3 _ _ _ _ _ hf hv (by rw [hg]; decide) (by rw [hg]; decide) hg
  · exact rxGoW.arm4 _ _ _ _ _ hf hv (by rw [hg]; decide) (by rw [hg]; decide) (by rw [hg]; decide) hg

/-- An `fvar` goes through `fv_map_at`. -/
theorem rxGoW_fvar (hf : fu ≠ 0) (hv : eViewW m h ≠ []) (hg : (eViewW m h).headD 0 = 1) :
    rxGoW (n + 1) m f fu h = rxGoW.k_fv_map_at h (rxMapW n m f ((eViewW m h).tail.headD 0)) :=
  rxGoW.arm5 _ _ _ _ _ hf hv (by rw [hg]; decide) (by rw [hg]; decide) (by rw [hg]; decide)
    (by rw [hg]; decide) hg

end

end L.Ind

/-! ## The relational side: the banked memo's invariant -/

namespace L.Ind

open L.Arena

theorem RfFr.of_iw {m m' : Mem} (h : MemFrame [IW] [200] m m') : RfFr m m' :=
  ⟨_, _, h, by simp [RFM, IW], by simp, by simp, by simp⟩

theorem posRecW_fr {m m' : Mem} {ws : List Word} {q : Word} (h : posRecW m ws = some (q, m')) : RfFr m m' := by
  simp only [posRecW] at h
  rcases hal : allocW m (UInt64.ofNat ws.length) with _ | ⟨q1, m1⟩ <;> rw [hal] at h; · simp at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  simp only [allocW] at hal
  split at hal; · simp at hal
  split at hal; · simp at hal
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hal)
  exact RfFr.of_iw ((allocMem_frame m _).trans (wrIW_frame _ _ _))

theorem allocW_fr {m m' : Mem} {k q : Word} (h : allocW m k = some (q, m')) : RfFr m m' := by
  simp only [allocW] at h
  split at h; · simp at h
  split at h; · simp at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact RfFr.of_iw (allocMem_frame m k)

end L.Ind

end
