import ConAgua.Arena.IndT.RecCheckTmn
import ConAgua.Arena.RecCheckSpec16

/-!
# `targetK53` under `StageC` (lane `indstaget`, helper `pds`)

`target_k53`'s model at `realCall p`, from `StageC` and the inputs' denotations con-ron's
`targetK53_spec` asks; its twin side transcribed from that spec's proof: `stripPis`
(`stripPis_pstep`, read-only), the telescopes' annotations erased (`mapM_RE_P` of
`eraseFVarTys_spec`), the heads and arguments (`getAppFn_run`, `viewConst_run`, `getAppArgs_run`,
read-only), the arguments' check (`internConstE_run`, `mkAppN_run`; `nestOcc` read-only), then
`tcmF_okC`.
-/

set_option linter.deprecated false

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
  cases n with
  | zero => simp [eftF] at h
  | succ n =>
  simp only [eftF, eftW] at h
  cases ha : allocW m 1 with
  | none => rw [ha] at h; simp [eftK1] at h
  | some x =>
  obtain ⟨f, m1⟩ := x
  rw [ha, eftK1_some] at h
  cases hr : rxW n (m1.set64 IW f 2) f e with
  | none => rw [hr] at h; simp [eftK2] at h
  | some y =>
  obtain ⟨z, m2⟩ := y
  rw [hr, eftK2_some] at h
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
    cases h1 : eftF n m (rdW (m.arr64 IW) o) with
    | none => rw [h1] at h; simp [eeK0] at h
    | some x =>
    obtain ⟨rv, m1⟩ := x
    rw [h1, eeK0_some] at h
    cases h2 : eeW n m1 (o + 1) (l - 1) with
    | none => rw [h2] at h; simp [eeK1] at h
    | some y =>
    obtain ⟨rr, m2⟩ := y
    rw [h2, eeK1_some] at h
    cases h3 : consW n m2 (rv.headD 0) (rr.headD 0) (rr.tail.headD 0) with
    | none => rw [h3] at h; simp [eeK2] at h
    | some z =>
    obtain ⟨rc, m3⟩ := z
    rw [h3, eeK2_some] at h
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

end L.Ind
