import ConAgua.Arena.IndPosSpec.RpGoStep
import ConAgua.Arena.IndPosSpec.RxMapW

/-!
# Rx

`hiAt_specW`, `keyMap_specW`, `rxRoot_spec`, `RxSpec`, `rxSpec_zero`, `rxMap_step` and the lemmas only they use.
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

section spec
variable (p : Prog) (L : RxLook p)

include L in
theorem rxRoot_spec (n : Nat) (s₀ : St) (ctx i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_hole_img_root" [ctx, i]
    ⦃fun r s' => LocEq s' s₀ ∧ rxRootW s₀.mem ctx i = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ L.rt, callFn, nestHoleImgRoot]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        hiAt_specW p L.hi n, slGetD_specW p L.gd n, internConst_spec p L.cf L.cp L.ci n,
        mknF_spec p L.ad n] <;>
      finish (gen := 20) [rdW_eq]

/-- The specs of the block at exec fuel `n`. -/
def RxSpec (n : Nat) : Prop :=
  (∀ (s₀ : St) (f i : Word), ⦃fun s => s = s₀⦄ invoke p (exec p n) "fv_map_at" [f, i]
    ⦃fun r s' => LocEq s' s₀ ∧ rxMapW n s₀.mem f i = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (ctx po pl nn i : Word), ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_hole_img" [ctx, po, pl, nn, i]
    ⦃fun r s' => LocEq s' s₀ ∧ rxImgW n s₀.mem ctx po pl nn i = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (ctx po pl n1 i : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nest_hole_img_frame" [ctx, po, pl, n1, i]
    ⦃fun r s' => LocEq s' s₀ ∧ rxFrameW n s₀.mem ctx po pl n1 i = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (f o l : Word), ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_hole_img_ds" [f, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ rxDsW n s₀.mem f o l = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (f o l q j : Word), ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_hole_img_ds_go" [f, o, l, q, j]
    ⦃fun _ s' => LocEq s' s₀ ∧ rxDsGoW n s₀.mem f o l q j = some s'.mem; ⊤⦄) ∧
  (∀ (s₀ : St) (f fu h : Word), ⦃fun s => s = s₀⦄ invoke p (exec p n) "replace_fvars_go" [f, fu, h]
    ⦃fun r s' => LocEq s' s₀ ∧ rxGoW n s₀.mem f fu h = some (r.headD 0, s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (f f1 g x y z : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "replace_fvars_node" [f, f1, g, x, y, z]
    ⦃fun r s' => LocEq s' s₀ ∧ rxNodeW n s₀.mem f f1 g x y z = some (r.headD 0, s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (f e : Word), ⦃fun s => s = s₀⦄ invoke p (exec p n) "replace_fvars" [f, e]
    ⦃fun r s' => LocEq s' s₀ ∧ rxW n s₀.mem f e = some (r.headD 0, s'.mem); ⊤⦄)

include L in
theorem rxSpec_zero : RxSpec p 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros
  · rw [invoke_eq _ L.fma]; simp only [callFn, fvMapAt]; vcgen [exec] <;> grind
  · rw [invoke_eq _ L.img]; simp only [callFn, nestHoleImg]; vcgen [exec] <;> grind
  · rw [invoke_eq _ L.fr]; simp only [callFn, nestHoleImgFrame]; vcgen [exec] <;> grind
  · rw [invoke_eq _ L.ds]; simp only [callFn, nestHoleImgDs]; vcgen [exec] <;> grind
  · rw [invoke_eq _ L.dsg]; simp only [callFn, nestHoleImgDsGo]; vcgen [exec] <;> grind
  · rw [invoke_eq _ L.go]; simp only [callFn, replaceFVarsGo]; vcgen [exec] <;> grind
  · rw [invoke_eq _ L.nd]; simp only [callFn, replaceFVarsNode]; vcgen [exec] <;> grind
  · rw [invoke_eq _ L.rf]; simp only [callFn, replaceFVars]; vcgen [exec] <;> grind

end spec

section step
variable (p : Prog) (L : RxLook p) (n : Nat) (ih : RxSpec p n)
include L ih

theorem rxMap_step (s₀ : St) (f i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "fv_map_at" [f, i]
    ⦃fun r s' => LocEq s' s₀ ∧ rxMapW (n + 1) s₀.mem f i = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  obtain ⟨-, hImg, -, -, -, -, -, -⟩ := ih
  simp only [invoke_eq _ L.fma, callFn, fvMapAt]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, hImg,
      keyMap_specW p L.km n, pinWord_specV p L.hl.hpw n, internSort_spec p L.hl.hsf L.hl.hsp L.hl.his n,
      internFVar_spec p L.hl.hff L.hl.hfp L.hl.hif n] <;>
    finish (gen := 20) [rdW_eq]

theorem rxImg_step (s₀ : St) (ctx po pl nn i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_hole_img" [ctx, po, pl, nn, i]
    ⦃fun r s' => LocEq s' s₀ ∧ rxImgW (n + 1) s₀.mem ctx po pl nn i = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  obtain ⟨-, hImg, hFr, -, -, -, -, -⟩ := ih
  simp only [invoke_eq _ L.img, callFn, nestHoleImg]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, hImg, hFr,
      rxRoot_spec p L n, hiAt_specW p L.hi n] <;>
    finish (gen := 20) [rdW_eq]

theorem rxFrame_step (s₀ : St) (ctx po pl n1 i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_hole_img_frame" [ctx, po, pl, n1, i]
    ⦃fun r s' => LocEq s' s₀ ∧ rxFrameW (n + 1) s₀.mem ctx po pl n1 i = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  obtain ⟨-, -, -, hDs, -, -, -, -⟩ := ih
  simp only [invoke_eq _ L.fr, callFn, nestHoleImgFrame]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, hDs,
      posRec2_specW p L.ha L.h2 n, posRec4_specW p L.ha L.h4 n, posRec5_specW p L.ha L.h5 n,
      internConst_spec p L.cf L.cp L.ci n, mknF_spec p L.ad n] <;>
    finish (gen := 20) [rdW_eq]

theorem rxDs_step (s₀ : St) (f o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_hole_img_ds" [f, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ rxDsW (n + 1) s₀.mem f o l = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  obtain ⟨-, -, -, -, hDg, -, -, -⟩ := ih
  simp only [invoke_eq _ L.ds, callFn, nestHoleImgDs]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, hDg, iwAlloc_specW p L.ha n] <;>
    finish (gen := 20)

theorem rxDsGo_step (s₀ : St) (f o l q j : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_hole_img_ds_go" [f, o, l, q, j]
    ⦃fun _ s' => LocEq s' s₀ ∧ rxDsGoW (n + 1) s₀.mem f o l q j = some s'.mem; ⊤⦄ := by
  obtain ⟨-, -, -, -, hDg, -, -, hRf⟩ := ih
  simp only [invoke_eq _ L.dsg, callFn, nestHoleImgDsGo]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, hDg, hRf] <;>
    finish (gen := 20) [rdW_eq]

theorem rxGo_step (s₀ : St) (f fu h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "replace_fvars_go" [f, fu, h]
    ⦃fun r s' => LocEq s' s₀ ∧ rxGoW (n + 1) s₀.mem f fu h = some (r.headD 0, s'.mem); ⊤⦄ := by
  obtain ⟨hMap, -, -, -, -, -, hNd, -⟩ := ih
  simp only [invoke_eq _ L.go, callFn, replaceFVarsGo]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      eView_spec p L.hl.hv n, hMap, memoFindG_spec rfSch p _ L.rff n,
      memoPutG_spec rfSch p _ L.rfp n, hNd] <;> finish (gen := 20) [St.setLocs_mem', rdW_eq]

theorem rxNode_step (s₀ : St) (f f1 g x y z : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "replace_fvars_node" [f, f1, g, x, y, z]
    ⦃fun r s' => LocEq s' s₀ ∧ rxNodeW (n + 1) s₀.mem f f1 g x y z = some (r.headD 0, s'.mem); ⊤⦄ := by
  obtain ⟨-, -, -, -, -, hGo, -, -⟩ := ih
  have hk := L.hk
  simp only [invoke_eq _ L.nd, callFn, replaceFVarsNode]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, hGo,
      mkApp_spec p hk.hd hk.appF hk.appP hk.appI hk.appM n,
      mkLam_spec p hk.hd hk.lamF hk.lamP hk.lamI hk.lamM n,
      mkForall_spec p hk.hd hk.forF hk.forP hk.forI hk.forM n,
      mkLet_spec p hk.hd hk.ltF hk.ltP hk.ltI hk.ltM n,
      mkProj_spec p hk.hd hk.prjF hk.prjP hk.prjI hk.prjM n] <;> finish (gen := 20) [St.setLocs_mem']

theorem rxRf_step (s₀ : St) (f e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "replace_fvars" [f, e]
    ⦃fun r s' => LocEq s' s₀ ∧ rxW (n + 1) s₀.mem f e = some (r.headD 0, s'.mem); ⊤⦄ := by
  obtain ⟨-, -, -, -, -, hGo, -, -⟩ := ih
  simp only [invoke_eq _ L.rf, callFn, replaceFVars]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, hGo,
      bankEnterG_spec 218 p _ L.rfe n, bankLeaveG_spec 218 p _ L.rfl' n] <;> finish (gen := 20)

end step

theorem rxSpec_all (p : Prog) (L : RxLook p) (n : Nat) : RxSpec p n := by
  induction n with
  | zero => exact rxSpec_zero p L
  | succ n ih =>
    exact ⟨rxMap_step p L n ih, rxImg_step p L n ih, rxFrame_step p L n ih, rxDs_step p L n ih,
      rxDsGo_step p L n ih, rxGo_step p L n ih, rxNode_step p L n ih, rxRf_step p L n ih⟩

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
