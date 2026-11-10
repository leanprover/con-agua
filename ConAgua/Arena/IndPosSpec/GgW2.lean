module

public import ConAgua.Arena.IndPosSpec.CfW
import ConAgua.Arena.IndPosSpec.NcnW2
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
public import ConAgua.Arena.IndPosSpec.NbPosW
public import ConAgua.Arena.IndPosSpec.NbKeyK2
public import ConAgua.Arena.IndPosSpec.NbLook
import ConAgua.Arena.IndPosSpec.EntryW
import ConAgua.Arena.IndPosSpec.UnW
import ConAgua.Arena.IndPartsSpec.BlockCounts
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.IndPos
import all ConAgua.Arena.IndPos2
import all ConAgua.Arena.IndSum

@[expose] public section

/-!
# GgW2

`posRecW_iwFr`, `snocW_iwFr`, `nestFrameMates_specW`, `slNew1_specW` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- `posRecW` writes the record pool only. -/
theorem posRecW_iwFr {m m' : Mem} {ws : List Word} {q : Word} (h : posRecW m ws = some (q, m')) :
    MemFrame [IW] [200] m m' := by
  simp only [posRecW] at h
  rcases hal : allocW m (UInt64.ofNat ws.length) with _ | ⟨q1, m1⟩ <;> rw [hal] at h; · simp at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact (allocW_iwFrame hal).trans (wrIW_frame _ _ _)

/-- `snocW` writes the record pool only. -/
theorem snocW_iwFr {n : Nat} {m m' : Mem} {o l x : Word} {r : List Word} (h : snocW n m o l x = some (r, m')) :
    MemFrame [IW] [200] m m' := by
  unfold snocW at h
  split at h; · simp at h
  split at h; · simp at h
  rename_i q m1 hal
  split at h; · simp at h
  rename_i m2 hc
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact ((allocW_iwFrame hal).trans (posmemo_copyW_iw _ _ _ _ _ _ hc)).trans (set64IW_frame _ _ _)

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

theorem nestFrameMates_specW (p : Prog) (L : FmLook p) (n : Nat) (s₀ : St) (vis c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_frame_mates" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ nfmW p n s₀.mem vis c = some (r, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ L.hp, callFn, nestFrameMatesL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        nestBlockOf_specW p L.hg L.hf L.hbo n,
        nestFrameMatesGo_spec p L.hc L.ha L.hcp L.hsn L.hgo n] <;>
      finish (gen := 20) [nfmW]

theorem slNew1_specW (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hp : p.lookup "sl_new1" = some slNew1) (n : Nat) (s₀ : St) (x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "sl_new1" [x]
    ⦃fun r s' => LocEq s' s₀ ∧ new1W s₀.mem x = some (r, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, slNew1]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, iwAlloc_specW p ha n] <;>
      finish [new1W, allocMem, allocW]

end L.Ind

namespace L.Ind

open L.Arena

theorem nestFrameGrp_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc2 : p.lookup "iw_copy" = some iwCopy) (h3 : p.lookup "rec3" = some rec3)
    (h4 : p.lookup "rec4" = some rec4) (hsn : p.lookup "sl_snoc" = some slSnoc)
    (hv : p.lookup "e_view" = some eView) (hs : p.lookup "sl_cons" = some slCons)
    (hpb : p.lookup "pi_binders" = some piBinders)
    (hp : p.lookup "nest_frame_grp" = some nestFrameGrpL) (n : Nat) :
    ∀ (s₀ : St) (hi us dO dL gO gL pO pL nO nL : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_frame_grp" [hi, us, dO, dL, gO, gL, pO, pL, nO, nL]
    ⦃fun r s' => LocEq s' s₀ ∧ fgW n s₀.mem hi us dO dL gO gL pO pL nO nL =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0], s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ hi us dO dL gO gL pO pL nO nL
    rw [invoke_eq _ hp]; simp only [callFn, nestFrameGrpL]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ hi us dO dL gO gL pO pL nO nL
    simp only [invoke_eq _ hp, callFn, nestFrameGrpL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        posRec4_specW p ha h4 n, posRec3_specW p ha h3 n, piBinders_spec p ha hc2 hv hs hpb n,
        slSnoc_specW p ha hc2 hsn n, ih] <;>
      finish (gen := 20) (instances := 5000) [rdW_eq, Locals.init_cons_zero, CWF, List.getD_cons_zero,
        List.getD_cons_succ]

end L.Ind

namespace L.Ind

open L.Arena

theorem nestFrameHoles_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc2 : p.lookup "iw_copy" = some iwCopy) (hsn : p.lookup "sl_snoc" = some slSnoc)
    (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
    (hif : p.lookup "intern_fvar" = some internFVar)
    (hp : p.lookup "nest_frame_holes" = some nestFrameHolesL) (n : Nat) :
    ∀ (s₀ : St) (hi gO gL aO aL : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_frame_holes" [hi, gO, gL, aO, aL]
    ⦃fun r s' => LocEq s' s₀ ∧ fhW n s₀.mem hi gO gL aO aL = some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ hi gO gL aO aL
    rw [invoke_eq _ hp]; simp only [callFn, nestFrameHolesL]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ hi gO gL aO aL
    simp only [invoke_eq _ hp, callFn, nestFrameHolesL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        internFVar_spec p hff hfp hif n, slSnoc_specW p ha hc2 hsn n, ih] <;>
      finish (gen := 20) (instances := 5000) [rdW_eq, Locals.init_cons_zero]

end L.Ind

namespace L.Ind

open L.Arena

theorem nestContNewActive_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc2 : p.lookup "iw_copy" = some iwCopy) (h4 : p.lookup "rec4" = some rec4)
    (hsn : p.lookup "sl_snoc" = some slSnoc)
    (hp : p.lookup "nest_cont_new_active" = some nestContNewActiveL) (n : Nat) :
    ∀ (s₀ : St) (us dO dL gO gL aO aL : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_cont_new_active" [us, dO, dL, gO, gL, aO, aL]
    ⦃fun r s' => LocEq s' s₀ ∧ caW n s₀.mem us dO dL gO gL aO aL = some ([r.headD 0, r.tail.headD 0], s'.mem);
      ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ us dO dL gO gL aO aL
    rw [invoke_eq _ hp]; simp only [callFn, nestContNewActiveL]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ us dO dL gO gL aO aL
    simp only [invoke_eq _ hp, callFn, nestContNewActiveL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        posRec4_specW p ha h4 n, slSnoc_specW p ha hc2 hsn n, ih] <;>
      finish (gen := 20) (instances := 5000) [rdW_eq, Locals.init_cons_zero]

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

namespace L.Ind

open L.Arena

theorem nestPosHoleKind_spec (p : Prog) (hh : p.lookup "nest_ctx_hi_at" = some nestCtxHiAt)
    (hp : p.lookup "nest_pos_hole_kind" = some nestPosHoleKindL) (n : Nat) (s₀ : St) (ctx kb i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_pos_hole_kind" [ctx, kb, i]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ hkWf n s₀.mem ctx kb i = some (r.headD 0); ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, nestPosHoleKindL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, nestCtxHiAt_specE p hh n] <;>
      finish (gen := 20) [hkWf, hkW, rdW_eq, LocEq]

end L.Ind

namespace L.Ind

open L.Arena

theorem nestHoleAt_spec' (p : Prog) (L : PfLook p) (k : Nat) (s₀ : St) (ctx po pl i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_hole_at" [ctx, po, pl, i]
    ⦃fun r s' => LocEq s' s₀ ∧ haWf k s₀.mem ctx po pl i = some (r, s'.mem); ⊤⦄ :=
  nestHoleAt_spec p L.ha L.h3 L.hsg L.h4 L.hrg L.hr L.hc L.hap L.hha k s₀ ctx po pl i


end L.Ind

namespace L.Ind

open L.Arena

theorem structUsedLater_spec' (p : Prog) (L : UslLook p) (n : Nat) (s₀ : St) (cty nP j : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_used_later" [cty, nP, j]
    ⦃fun r s' => LocEq s' s₀ ∧ ustWf n s₀.mem cty nP j = some (r.headD 0, s'.mem); ⊤⦄ := by
  match n with
  | 0 => rw [invoke_eq _ L.hp]; simp only [callFn, structUsedLaterL]; vcgen [exec] <;> grind
  | 1 =>
    rw [invoke_eq _ L.hp]; simp only [callFn, structUsedLaterL]
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, invoke_exec0 p] <;> grind
  | n + 2 => exact structUsedLater_spec p L.hv L.hf L.hput L.hins L.hgo L.hbp L.hst L.hcl L.hfast L.hp n s₀ cty nP j

theorem nestCtorsU4_spec (p : Prog) (L : UslLook p) (hp : p.lookup "nest_ctors_u4" = some nestCtorsU4L)
    (n : Nat) : ∀ (s₀ : St) (ko nF cl i : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctors_u4" [ko, nF, cl, i]
    ⦃fun r s' => LocEq s' s₀ ∧ u4W n s₀.mem ko nF cl i = some ([r.headD 0], s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ ko nF cl i
    rw [invoke_eq _ hp]; simp only [callFn, nestCtorsU4L]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ ko nF cl i
    simp only [invoke_eq _ hp, callFn, nestCtorsU4L]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, structUsedLater_spec' p L n, ih] <;>
      finish (gen := 20) [rdW_eq]

end L.Ind

namespace L.Ind

open L.Arena

theorem nestCtorsResOk_spec (p : Prog) (hl : NoLook p) (hoa : p.lookup "nest_occ_any" = some nestOccAnyL)
    (hrh : p.lookup "nest_res_head" = some nestResHeadL) (had : AdF p)
    (hp : p.lookup "nest_ctors_res_ok" = some nestCtorsResOkL) (n : Nat) (s₀ : St) (ctx hi cur : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctors_res_ok" [ctx, hi, cur]
    ⦃fun r s' => LocEq s' s₀ ∧ roW n s₀.mem ctx hi cur = some ([r.headD 0], s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, nestCtorsResOkL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        nestResHead_spec p hrh had n, gaaF_spec p had n, nestOccAny_spec p hl hoa n] <;>
      finish (gen := 20) [roW, roK0_eq, rdW_eq]

end L.Ind

end

end


section


/-! # `IndPos2`, the `nestPos` block (lane `indproofs2`, helper `pos2`): the L side — every
function of the block refines its word model, by one induction on the exec fuel. -/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

-- `posRec3_eq`, `posRec3_specW`: `CtxFields.lean`.

theorem pos2_getElem_getD (a : Array Word) (i : Nat) (h : i < a.size) : a[i] = a[i]?.getD 0 := by
  simp [h]

theorem nestCtorNf_spec' (p : Prog) (L : NbLook p) (k : Nat) (s₀ : St) (ctx po pl us dO dL cv closed : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_ctor_nf" [ctx, po, pl, us, dO, dL, cv, closed]
    ⦃fun r s' => LocEq s' s₀ ∧ ncnWf k s₀.mem ctx po pl us dO dL cv closed = some ([r.headD 0], s'.mem); ⊤⦄ := by
  match k with
  | 0 => exact triple_post (invoke_exec0 p _ _ s₀) (fun _ _ h => h.elim)
  | k + 1 =>
    refine triple_post (nestCtorNf_spec p L.ct.cr.rx L.hnf k s₀ ctx po pl us dO dL cv closed) ?_
    rintro r s' ⟨h1, h2⟩
    exact ⟨h1, by simp [ncnWf, h2]⟩

theorem nestWalkStack_spec' (p : Prog) (L : NbLook p) (n : Nat) (s₀ : St) (ctx off l po pl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_walk_stack" [ctx, off, l, po, pl]
    ⦃fun r s' => LocEq s' s₀ ∧ nwsWf n s₀.mem ctx off l po pl = some (r, s'.mem); ⊤⦄ := by
  match n with
  | 0 => exact triple_post (invoke_exec0 p _ _ s₀) (fun _ _ h => h.elim)
  | n + 1 => exact nestWalkStack_spec p L.dc L.hws n s₀ ctx off l po pl

end L.Ind

end

end
