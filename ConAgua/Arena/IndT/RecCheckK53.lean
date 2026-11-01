module

public import ConRon.Bridge.Inductives.PosWalks
public import ConAgua.Arena.RecCheckSpec.EqWDec
public import ConAgua.Arena.IndRealAbsPos
public import ConAgua.Arena.RecCheckSpec.EeW
public import ConRon.Bridge.Inductives.RecCheck

@[expose] public section

/-!
# `targetK53`'s steps under `StageC`: frames and erasures (lane `indstaget`, helper `pds`)

The frames of the callees' models of `target_k53` (`eeW_afr`, `noF_afr`, `tteW_afr`) and the
twin's erasures (`eraseAll_spec`, `tkTele_cstep`: `mapM_RE_P` of `eraseFVarTys_spec`), for the
refinements `tka_ref`, `tkh_ref`, `tk_ref` (`Verdict/IndBTka`, `Verdict/IndBK53`).
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep TAArgs dShape dCtors dCtorNf dMajor PSpecP REL)
open ConRon.Bridge (CoreStep denote_ext denoteEList_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Frames -/

theorem eftF_afr {n : Nat} {m m' : Mem} {e : Word} {r : List Word} (h : eftF n m e = some (r, m')) :
    AFr m m' := by
  obtain _ | n := n
  · simp [eftF] at h
  simp only [eftF, eftW] at h
  rcases ha : allocW m 1 with _ | ⟨f, m1⟩ <;> simp only [ha, eftK1, reduceCtorEq] at h
  rcases hr : rxW n (m1.set64 IW f 2) f e with _ | ⟨z, m2⟩ <;> simp only [hr, eftK2, reduceCtorEq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
  exact ((allocW_afr ha).trans (set64IW_afr _ _ _)).trans (rxW_afr hr)

theorem eeW_afr : ∀ (n : Nat) {m m' : Mem} {o l : Word} {r : List Word}, eeW n m o l = some (r, m') →
    AFr m m'
  | 0, _, _, _, _, _, h => by simp [eeW] at h
  | n + 1, m, m', o, l, r, h => by
    by_cases hl : l = 0
    · rw [eeW_nil (h := hl)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
      exact AFr.refl _
    rw [eeW_cons (h := hl)] at h
    rcases h1 : eftF n m (rdW (m.arr64 IW) o) with _ | ⟨rv, m1⟩ <;> simp only [h1, eeK0, reduceCtorEq] at h
    rcases h2 : eeW n m1 (o + 1) (l - 1) with _ | ⟨rr, m2⟩ <;> simp only [h2, eeK1, reduceCtorEq] at h
    rcases h3 : consW n m2 (rv.headD 0) (rr.headD 0) (rr.tail.headD 0) with _ | ⟨rc, m3⟩ <;> simp only [h3, eeK2, reduceCtorEq] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
    exact ((eftF_afr h1).trans (eeW_afr n h2)).trans (consW_afr h3)

theorem noF_afr {n : Nat} {m m' : Mem} {no nl lo hi e r : Word}
    (h : noF n m no nl lo hi e = some (r, m')) : AFr m m' := by
  cases n with
  | zero => simp [noF] at h
  | succ n => exact noConstWf_afr (n := n + 1) h

/-- The annotations of a denoted handle list erased: con-ron's `mapM_RE_P` of `eraseFVarTys_spec`. -/
theorem eraseAll_spec (xs : List EIdx) (xsP : List ConLeche.Expr) :
    PSpecP (fun st => True ∧ Frontend.denoteEList st xs = some xsP)
      (xs.mapM ConRon.Arena.eraseFVarTys) (REL (xsP.map ConLeche.Expr.eraseFVarTys)) :=
  ConRon.Bridge.Inductives.mapM_RE_P (fun _ => True) (fun _ h => h)
    (fun e eP => fun s₀ s' r hok hp hpre hrun =>
      ConRon.Bridge.Inductives.eraseFVarTys_spec e eP s₀ s' r hok hp hpre.2 hrun) xs xsP

theorem tteW_afr {n : Nat} {m m' : Mem} {bso bsl teo tel : Word} {r : List Word}
    (h : tteW n m bso bsl teo tel = some (r, m')) : AFr m m' := by
  obtain _ | n := n
  · simp [tteW] at h
  rw [tteW_succ] at h
  rcases h1 : eeW n m bso bsl with _ | ⟨r1, m1⟩ <;> simp only [h1, tteK1, reduceCtorEq] at h
  rcases h2 : eeW n m1 teo tel with _ | ⟨r2, m2⟩ <;> simp only [h2, tteK2, reduceCtorEq] at h
  rcases h3 : eqW n m2 (r1.headD 0) (r1.tail.headD 0) (r2.headD 0) (r2.tail.headD 0) with _ | e <;> simp only [h3, tteK3, reduceCtorEq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
  exact (eeW_afr n h1).trans (eeW_afr n h2)

/-- The telescope check is a twin step con-ron calls a `CoreStep` (two `eraseAll_spec` runs). -/
theorem tkTele_cstep {fe : IFEnv} {env : ConLeche.Env} {teleW tele : List EIdx}
    {twP tP : List ConLeche.Expr} {s₀ s' : AState}
    {c : Bool} (hok : ConRon.Bridge.CheckOK V env fe s₀)
    (hw : Frontend.denoteEList s₀.store teleW = some twP)
    (ht : Frontend.denoteEList s₀.store tele = some tP)
    (hrun : (tkTele teleW tele).run s₀ = .ok (c, s')) : CoreStep V env fe s₀ s' := by
  have hrun' : (tkTele teleW tele) s₀ = .ok (c, s') := hrun
  simp only [tkTele] at hrun'
  obtain ⟨ew, s1, k1, z1⟩ := ConRon.Bridge.AM.bind_ok hrun'
  obtain ⟨q1, -⟩ := ConRon.Bridge.Inductives.RC.pspecP_core (eraseAll_spec teleW twP) hok
    ⟨trivial, hw⟩ k1
  obtain ⟨et, s2, k2, z2⟩ := ConRon.Bridge.AM.bind_ok z1
  obtain ⟨q2, -⟩ := ConRon.Bridge.Inductives.RC.pspecP_core (eraseAll_spec tele tP) q1.ok
    ⟨trivial, denoteEList_ext q1.ext _ _ ht⟩ k2
  obtain ⟨-, rfl⟩ := ConRon.Bridge.AM.pure_ok z2
  exact q1.trans q2


end L.Ind
