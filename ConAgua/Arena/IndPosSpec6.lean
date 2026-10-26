import ConAgua.Arena.IndPosSpec5
import ConAgua.Arena.IndDecStab

/-! # `nestCtorNf` (lane `indproofs2`, helper `pos`): a frame constructor's record, read back through
`FvMap.holeImg ctx prog prog.length` (`nest_hole_img_ds` for the parameters). -/


noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

def ncnK3 (us cv q l : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (ty, m3) => posRecW m3 [rdW (m3.arr64 EREC) cv, us, q, l, ty]
def ncnK2 (k : Nat) (f us cv closed : Word) : Option (Word × Word × Mem) → Option (Word × Mem)
  | none => none
  | some (q, l, m2) => ncnK3 us cv q l (rxW k m2 f closed)
def ncnK1 (k : Nat) (us dO dL cv closed : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (f, m1) => ncnK2 k f us cv closed (rxDsW k m1 f dO dL)
/-- The model of `nest_ctor_nf` at exec fuel `k + 1`. -/
def ncnW (k : Nat) (m : Mem) (ctx po pl us dO dL cv closed : Word) : Option (Word × Mem) :=
  ncnK1 k us dO dL cv closed (posRecW m [0, ctx, po, pl, pl])

section arms
variable (k : Nat) (m1 m2 m3 : Mem) (f us cv closed dO dL q l ty : Word)
theorem ncnK3_some : ncnK3 us cv q l (some (ty, m3)) = posRecW m3 [rdW (m3.arr64 EREC) cv, us, q, l, ty] := rfl
theorem ncnK2_some : ncnK2 k f us cv closed (some (q, l, m2)) = ncnK3 us cv q l (rxW k m2 f closed) := rfl
theorem ncnK1_some : ncnK1 k us dO dL cv closed (some (f, m1)) = ncnK2 k f us cv closed (rxDsW k m1 f dO dL) := rfl
end arms
attribute [ind_grind] ncnK3_some ncnK2_some ncnK1_some

theorem nestCtorNf_spec (p : Prog) (L : RxLook p) (hp : p.lookup "nest_ctor_nf" = some nestCtorNfL) (k : Nat)
    (s₀ : St) (ctx po pl us dO dL cv closed : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "nest_ctor_nf" [ctx, po, pl, us, dO, dL, cv, closed]
    ⦃fun r s' => LocEq s' s₀ ∧ ncnW k s₀.mem ctx po pl us dO dL cv closed = some (r.headD 0, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, nestCtorNfL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      posRec5_specW p L.ha L.h5 k, (rxSpec_all p L k).2.2.2.1, (rxSpec_all p L k).2.2.2.2.2.2.2] <;>
    finish (gen := 20) [ncnW, rdW_eq]

section rel
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

theorem ncnW_ok (k : Nat) (m m' : Mem) (a : AState) (ctx po pl us dO dL cv closed nf : Word) (c : NestCtx)
    (prog : List NestHole) (ds : List EIdx) (cvv : IConstantVal) (M : Std.HashMap (EIdx × Word) EIdx) (G g : Word)
    (h : ncnW k m ctx po pl us dO dL cv closed = some (nf, m')) (hS : StageR dn vis fe m a)
    (hc : decCtx m ctx.toNat = some c) (hin : CtxIn m ctx.toNat (· < iwTop m)) (hs : HSl m po.toNat pl.toNat prog)
    (hb : c.nP + c.names.length + pl.toNat < 2 ^ 64) (hus : H us)
    (hds : decHL m dO.toNat dL.toNat = some ds) (hdsb : ∀ j < dL.toNat, dO.toNat + j < iwTop m)
    (hcl : H closed) (hcv : decCV (erecP m) cv.toNat = some cvv) (hR : RfInv m M G g) :
    ∃ x a', (ConRon.Arena.nestCtorNf c prog (decI us) ds cvv (decE closed)).run a = .ok (x, a') ∧
      DecB (fun m => decNCN m nf.toNat) m' x ∧ nf.toNat + 5 ≤ iwTop m' ∧ RxPost dn fe vis m m' a' M G g := by
  unfold ncnW at h
  have hpl : prog.length = pl.toNat := hs.1
  rcases hr1 : posRecW m [0, ctx, po, pl, pl] with _ | ⟨f, m1⟩ <;> rw [hr1] at h; · simp [ncnK1] at h
  rw [ncnK1_some] at h
  obtain ⟨hS1, hg1, hf1, ht1, hget1⟩ := posRecW_stage hr1 hS (by simp)
  simp only [List.length_cons, List.length_nil] at ht1
  have g0 := iwN_of_get (by simpa using hget1 0 (by simp))
  have g1 := iwN_of_get (by simpa using hget1 1 (by simp))
  have g2 := iwN_of_get (by simpa using hget1 2 (by simp))
  have g3 := iwN_of_get (by simpa using hget1 3 (by simp))
  have g4 := iwN_of_get (by simpa using hget1 4 (by simp))
  obtain ⟨ec, hci1⟩ := hin.grow hg1
  have hfm : FMOk m1 f.toNat (.holeImg c prog pl.toNat) :=
    ⟨by simpa using g0, by omega, ⟨ctx.toNat, g1, by rw [ec]; exact hc, hci1⟩,
      ⟨po.toNat, pl.toNat, g2, g3, hs.grow hg1⟩, g4, hb⟩
  have hR1 := hR.frame (posRecW_fr hr1)
  rcases hd : rxDsW k m1 f dO dL with _ | ⟨q, l, m2⟩ <;> rw [hd] at h; · simp [ncnK2] at h
  rw [ncnK2_some] at h
  obtain ⟨ys, a2, hrun2, hdec2, hq2, M2, G2, hS2, hg2, hR2, hk2, hG2⟩ := (rxOK_all dn fe vis k).2.2.2.1 m1 m2 a f dO dL
    q l _ ds M G g hd hS1 hfm (by rw [decHL_agree (RdS.of_grow hg1) hdsb]; exact hds)
    (fun j hj => Nat.lt_of_lt_of_le (hdsb j hj) hg1.1) hR1
  rcases hrx : rxW k m2 f closed with _ | ⟨ty, m3⟩ <;> rw [hrx] at h; · simp [ncnK3] at h
  rw [ncnK3_some] at h
  obtain ⟨a3, hrun3, hty, M3, G3, hS3, hg3, hR3, hk3, hG3⟩ := (rxOK_all dn fe vis k).2.2.2.2.2.2 m2 m3 a2 f closed _
    ty M2 G2 g hrx hS2 (hfm.grow hg2) hcl hR2
  obtain ⟨hS4, hg4, hf4, ht4, hget4⟩ := posRecW_stage h hS3 (by simp)
  simp only [List.length_cons, List.length_nil] at ht4
  have hg13 := (hg1.trans hg2).trans hg3
  -- the constructor's name, from `EREC`
  obtain ⟨wn, hwn, hwnH, hwnd⟩ := decCV_name hcv
  have hcvb : cv.toNat < erTop m := by have := (Array.getElem?_eq_some_iff.mp hwn).1; have := erecP_size_le m; omega
  have hrdn : rdW (m3.arr64 EREC) cv = wn := by
    have e1 : (m3.arr64 EREC)[cv.toNat]? = (m.arr64 EREC)[cv.toNat]? := hg13.2.2.2 _ hcvb
    simp [rdW, e1, erecP_get hwn]
  rw [hrdn] at hget4
  refine ⟨⟨cvv.name, decI us, ys, decE ty⟩, a3, ?_, ?_, by omega,
    ⟨M3, G3, hS4, (hg1.trans hg2).trans (hg3.trans hg4), hR3.frame (posRecW_fr h), hk2.trans hk3 hG2,
      UInt64.le_trans hG2 hG3⟩⟩
  · simp only [ConRon.Arena.nestCtorNf, hpl, StateT.run_bind]
    simp only [hrun2, except_ok_bind, hrun3]
    rfl
  · have hn0 := hget4 0 (by simp)
    have hn1 := hget4 1 (by simp)
    have hn2 := hget4 2 (by simp)
    have hn3 := hget4 3 (by simp)
    have hn4 := hget4 4 (by simp)
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.add_zero] at hn0 hn1 hn2 hn3 hn4
    have hql : decHL m' q.toNat l.toNat = some ys := by rw [decHL_grow (hg3.trans hg4) hq2]; exact hdec2
    have hqlT : decHL (truncM m') q.toNat l.toNat = some ys := by
      rw [decHL_truncM (by have := hg3.1; have := hg4.1; omega)]; exact hql
    have t : ∀ i < 5, (iwA (truncM m'))[nf.toNat + i]? = (m'.arr64 IW)[nf.toNat + i]? := fun i hi => by
      rw [truncM_iw_eq (by omega)]; rfl
    have hn0' := t 0 (by omega); have hn1' := t 1 (by omega); have hn2' := t 2 (by omega)
    have hn3' := t 3 (by omega); have hn4' := t 4 (by omega)
    simp only [Nat.add_zero] at hn0'
    rw [hn0] at hn0'; rw [hn1] at hn1'; rw [hn2] at hn2'; rw [hn3] at hn3'; rw [hn4] at hn4'
    show decNCN (truncM m') nf.toNat = _
    simp only [decNCN, decAt, iwH, iwN, hd?, nat?, hn0', hn1', hwnH, hus, Option.bind_eq_bind,
      Option.bind_some, ite_true, ite_true]
    rw [show nf.toNat + 2 + 1 = nf.toNat + 3 by omega, hn2', hn3', hn4']
    simp [hqlT, hwnd, hty, decE_eq]

end rel

section census
variable (p : Prog) (L : RxLook p) (hp : p.lookup "nest_ctor_nf" = some nestCtorNfL)
include L hp

/-- **`nest_ctor_nf` refines `nestCtorNf`** (through `mk_app_n`'s stub in the hole images). -/
@[refines ConRon.Arena.nestCtorNf]
theorem nestCtorNf_refines (k : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
    (vis ctx po pl us dO dL cv closed : Word) (c : NestCtx) (prog : List NestHole) (ds : List EIdx)
    (cvv : IConstantVal) (M : Std.HashMap (EIdx × Word) EIdx) (G g : Word) (hS : StageR dn vis fe s₀.mem a₀)
    (hc : decCtx s₀.mem ctx.toNat = some c) (hin : CtxIn s₀.mem ctx.toNat (· < iwTop s₀.mem))
    (hs : HSl s₀.mem po.toNat pl.toNat prog) (hb : c.nP + c.names.length + pl.toNat < 2 ^ 64) (hus : H us)
    (hds : decHL s₀.mem dO.toNat dL.toNat = some ds) (hdsb : ∀ j < dL.toNat, dO.toNat + j < iwTop s₀.mem)
    (hcl : H closed) (hcv : decCV (erecP s₀.mem) cv.toNat = some cvv) (hR : RfInv s₀.mem M G g) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "nest_ctor_nf" [ctx, po, pl, us, dO, dL, cv, closed]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.nestCtorNf c prog (decI us) ds cvv (decE closed)) a₀ ∧
      decNCN s'.mem (r.headD 0).toNat =
        some (AM.res (ConRon.Arena.nestCtorNf c prog (decI us) ds cvv (decE closed)) a₀) ∧
      (r.headD 0).toNat + 5 ≤ iwTop s'.mem ∧
      RxPost dn fe vis s₀.mem s'.mem (AM.st (ConRon.Arena.nestCtorNf c prog (decI us) ds cvv (decE closed)) a₀)
        M G g; ⊤⦄ := by
  refine triple_post (nestCtorNf_spec p L hp k s₀ ctx po pl us dO dL cv closed) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hdec, hb5, hpost⟩ := ncnW_ok dn fe vis k _ _ a₀ ctx po pl us dO dL cv closed _ c prog ds cvv
    M G g hm hS hc hin hs hb hus hds hdsb hcl hcv hR
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hres]; exact hdec.get (decNCN_mono _), hb5, by rw [hst]; exact hpost⟩

end census

end L.Ind
