module

public import ConAgua.Arena.RecCheckSpec.BvbWStageC
public import ConAgua.Arena.RecCheckSpec.EraseFVarTys
public import ConAgua.Arena.IndGrindAttr
import ConAgua.Arena.IndPosSpec.FgW
public import ConAgua.Arena.RecCheckSpec.RcLook

@[expose] public section

/-!
# TaGoWMfr

`taCW_same`, `taGoW_mfr`, `taAW_mfr`, `RcMR.setTa` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `target_abs`' write set -/

theorem taCW_same {n : Nat} {m m' : Mem} {no nl lvls ho hl hh nn vus r : Word}
    (h : taCW n m no nl lvls ho hl hh nn vus = some (r, m')) : m' = m := by
  cases n with
  | zero => simp [taCW] at h
  | succ n =>
    simp only [taCW, taCW.k_sl_find.eq_def] at h
    repeat' split at h
    all_goals (simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h; try exact h.2.symm)

theorem taGoW_mfr (n : Nat) :
    (∀ (m m' : Mem) (no nl lvls ho hl f h r : Word), taGoW n m no nl lvls ho hl f h = some (r, m') →
      MFr [TAM] [212, 213] m m') ∧
    (∀ (m m' : Mem) (no nl lvls ho hl f1 g x y z r : Word),
      taNodeW n m no nl lvls ho hl f1 g x y z = some (r, m') → MFr [TAM] [212, 213] m m') := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  cases n with
  | zero => exact ⟨fun _ _ _ _ _ _ _ _ _ _ h => by simp [taGoW.eq_1] at h,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => by simp [taNodeW.eq_1] at h⟩
  | succ j =>
  have ihG : ∀ (m m' : Mem) (no nl lvls ho hl f h r : Word), taGoW j m no nl lvls ho hl f h = some (r, m') →
      MFr [TAM] [212, 213] m m' := (ih j (by omega)).1
  refine ⟨?_, ?_⟩
  · intro m m' no nl lvls ho hl f h r hg
    rcases taGoW_some hg with rfl | hc | ⟨rn, m1, hn, hs⟩
    · exact MFr.refl _ _ _
    · rw [taCW_same hc]; exact MFr.refl _ _ _
    cases j with
    | zero => rw [taNodeW.eq_1] at hn; cases hn
    | succ i =>
      exact ((ih (i + 1) (by omega)).2 _ _ _ _ _ _ _ _ _ _ _ _ _ hn).trans
        ⟨_, _, msetG_frame taSch taSch_wf m1 m' h 0 rn hs, by simp [taSch, TAM], by simp [taSch]⟩
  · intro m m' no nl lvls ho hl f1 g x y z r hn
    rw [taNodeW.eq_def] at hn
    simp only at hn
    split at hn
    · obtain ⟨⟨a2, m1⟩, h1, hn⟩ := of_K hn (taNodeW.k_target_abs_go.none ..)
      rw [taNodeW.k_target_abs_go.arm1] at hn
      obtain ⟨⟨x2, m2⟩, h2, hn⟩ := of_K hn (taNodeW.k_target_abs_go_2.none _)
      rw [taNodeW.k_target_abs_go_2.arm1] at hn
      exact ((ihG _ _ _ _ _ _ _ _ _ _ h1).trans (ihG _ _ _ _ _ _ _ _ _ _ h2)).trans (MFr.of_low (mkAppW_low hn)).up
    split at hn
    · obtain ⟨⟨a2, m1⟩, h1, hn⟩ := of_K hn (taNodeW.k_target_abs_go_3.none ..)
      rw [taNodeW.k_target_abs_go_3.arm1] at hn
      obtain ⟨⟨x2, m2⟩, h2, hn⟩ := of_K hn (taNodeW.k_target_abs_go_4.none _)
      rw [taNodeW.k_target_abs_go_4.arm1] at hn
      exact ((ihG _ _ _ _ _ _ _ _ _ _ h1).trans (ihG _ _ _ _ _ _ _ _ _ _ h2)).trans (MFr.of_low (mkLamW_low hn)).up
    split at hn
    · obtain ⟨⟨a2, m1⟩, h1, hn⟩ := of_K hn (taNodeW.k_target_abs_go_5.none ..)
      rw [taNodeW.k_target_abs_go_5.arm1] at hn
      obtain ⟨⟨x2, m2⟩, h2, hn⟩ := of_K hn (taNodeW.k_target_abs_go_6.none _)
      rw [taNodeW.k_target_abs_go_6.arm1] at hn
      exact ((ihG _ _ _ _ _ _ _ _ _ _ h1).trans (ihG _ _ _ _ _ _ _ _ _ _ h2)).trans (MFr.of_low (mkForallW_low hn)).up
    split at hn
    · obtain ⟨⟨a2, m1⟩, h1, hn⟩ := of_K hn (taNodeW.k_target_abs_go_7.none ..)
      rw [taNodeW.k_target_abs_go_7.arm1] at hn
      obtain ⟨⟨x2, m2⟩, h2, hn⟩ := of_K hn (taNodeW.k_target_abs_go_8.none ..)
      rw [taNodeW.k_target_abs_go_8.arm1] at hn
      obtain ⟨⟨c2, m3⟩, h3, hn⟩ := of_K hn (taNodeW.k_target_abs_go_9.none ..)
      rw [taNodeW.k_target_abs_go_9.arm1] at hn
      exact (((ihG _ _ _ _ _ _ _ _ _ _ h1).trans (ihG _ _ _ _ _ _ _ _ _ _ h2)).trans
        (ihG _ _ _ _ _ _ _ _ _ _ h3)).trans (MFr.of_low (mkLetW_low hn)).up
    · obtain ⟨⟨a2, m1⟩, h1, hn⟩ := of_K hn (taNodeW.k_target_abs_go_10.none ..)
      rw [taNodeW.k_target_abs_go_10.arm1] at hn
      exact (ihG _ _ _ _ _ _ _ _ _ _ h1).trans (MFr.of_low (mkProjW_low hn)).up

/-- **`target_abs` writes only its memo** (array `TAM`, `CTL[212]`, `CTL[213]`) besides the stores'
interns. -/
theorem taAW_mfr {n : Nat} {m m' : Mem} {no nl lvls ho hl e r : Word}
    (h : taAW n m no nl lvls ho hl e = some (r, m')) : MFr [TAM] [212, 213] m m' := by
  by_cases h0 : rdW (m.arr64 CTL) taSch.cs + 2 = 0
  · simp [taAW, h0] at h
  rw [taAW.arm1 n m no nl lvls ho hl e h0] at h
  exact MFr.trans ⟨_, _, mclearG_frame taSch m, by simp, by simp [taSch]⟩ ((taGoW_mfr n).1 _ _ _ _ _ _ _ _ _ _ h)

theorem RcMR.setTa {m m' : Mem} (h : RcMR m) (hf : MFr [TAM] [212, 213] m m') (hn : ∃ mp, taMR m' mp) :
    RcMR m' := ⟨h.pos.mfr hf (by simp [PosAv, NOM, DPM, RAM, HBM, RFM, TAM]), hn⟩

/-! ## Callees at any exec fuel -/

section rel
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

theorem taF_ok (n : Nat) {m m' : Mem} {a : AState} {no nl lvls ho hl e r : Word} {names : List NIdx}
    {holes : List EIdx} (h : taF n m no nl lvls ho hl e = some (r, m')) (hS : StageR vis fe m a)
    (he : H e) (hlv : H lvls)
    (hdec : decHL m no.toNat nl.toNat = some names) (hit : no.toNat + nl.toNat ≤ iwTop m)
    (hho : decHL m ho.toNat hl.toNat = some holes) (hht : ho.toNat + hl.toNat ≤ iwTop m) (hP : RcMR m) :
    ∃ a', (ConRon.Arena.targetAbs names (decI lvls) holes (decE e)).run a = .ok (decE r, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ RcMR m' := by
  cases n with
  | zero => cases h
  | succ n =>
    obtain ⟨mp, hM⟩ := hP.ta
    obtain ⟨a', mp1, hrun, hM1, hS', hg⟩ :=
      taAW_ok n (fun _ => none) fe vis m m' a no nl lvls ho hl e r names holes mp h hS he hlv hdec hit hho hht hM
    exact ⟨a', hrun, hS', hg, hP.setTa (taAW_mfr h) ⟨mp1, hM1⟩⟩

end rel

/-- The lookups of `target_params_def_eq`. -/
structure TpLook (p : Prog) : Prop where
  rc : RcLook p
  ta : TaLook p
  bvb : BvbProg p
  hf : HfF p
  step : p.lookup "target_params_def_eq_step" = some targetParamsDefEqStep
  tpd : p.lookup "target_params_def_eq" = some targetParamsDefEq

end L.Ind

end
