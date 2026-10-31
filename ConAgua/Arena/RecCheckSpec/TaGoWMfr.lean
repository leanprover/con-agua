module

public import ConAgua.Arena.RecCheckSpec.BvbWStageC
public import ConAgua.Arena.RecCheckSpec.EraseFVarTys
public import ConAgua.Arena.IndGrindAttr

@[expose] public section

/-!
# TaGoWMfr

`taCW_same`, `taGoW_mfr`, `taAW_mfr`, `RcMR.setTa`, `tcpF`, `tcpF_ok` and the lemmas only they use.
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
    simp only [taCW] at h
    by_cases hv : vus ≠ lvls
    · rw [ite_eq_left hv] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
    rw [ite_eq_right hv] at h
    rcases hf : findW n m no nl nn with _ | fr <;> rw [hf] at h <;>
      try (simp only [taCK, reduceCtorEq] at h; done)
    simp only [taCK] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
    split at h <;> (simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm)

theorem taGoW_mfr (n : Nat) :
    (∀ (m m' : Mem) (no nl lvls ho hl f h r : Word), taGoW n m no nl lvls ho hl f h = some (r, m') →
      MFr [TAM] [212, 213] m m') ∧
    (∀ (m m' : Mem) (no nl lvls ho hl f1 g x y z r : Word),
      taNodeW n m no nl lvls ho hl f1 g x y z = some (r, m') → MFr [TAM] [212, 213] m m') := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  cases n with
  | zero => exact ⟨fun _ _ _ _ _ _ _ _ _ _ h => by simp [taGoW] at h,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => by simp [taNodeW] at h⟩
  | succ j =>
  have ihG : ∀ (m m' : Mem) (no nl lvls ho hl f h r : Word), taGoW j m no nl lvls ho hl f h = some (r, m') →
      MFr [TAM] [212, 213] m m' := (ih j (by omega)).1
  refine ⟨?_, ?_⟩
  · intro m m' no nl lvls ho hl f h r hg
    by_cases hf : f = 0
    · rw [taGoW_abort (hf := hf)] at hg; simp at hg
    rw [taGoW_view (hf := hf)] at hg
    unfold taG1 at hg
    split at hg; · simp at hg
    split at hg
    · simp only [Option.some.injEq, Prod.mk.injEq] at hg; rw [← hg.2]; exact MFr.refl _ _ _
    split at hg
    · rw [taCW_same hg]; exact MFr.refl _ _ _
    unfold taG3 at hg
    split at hg; · simp at hg
    split at hg
    · simp only [Option.some.injEq, Prod.mk.injEq] at hg; rw [← hg.2]; exact MFr.refl _ _ _
    cases hn : taNodeW j m no nl lvls ho hl (f - 1) _ _ _ _ with
    | none => rw [hn] at hg; simp [taG4] at hg
    | some pr =>
      obtain ⟨rn, m1⟩ := pr
      rw [hn, taG4_some] at hg
      rcases hs : msetG taSch m1 h 0 rn with _ | m2 <;> simp only [hs, taG5, reduceCtorEq] at hg
      simp only [Option.some.injEq, Prod.mk.injEq] at hg
      rw [← hg.2]
      cases j with
      | zero => simp [taNodeW] at hn
      | succ i =>
        exact ((ih (i + 1) (by omega)).2 _ _ _ _ _ _ _ _ _ _ _ _ _ hn).trans
          ⟨_, _, msetG_frame taSch taSch_wf m1 m2 h 0 rn hs, by simp [taSch, TAM], by simp [taSch]⟩
  · intro m m' no nl lvls ho hl f1 g x y z r hn
    unfold taNodeW at hn
    split at hn
    · rcases h1 : taGoW j m no nl lvls ho hl f1 x with _ | ⟨a2, m1⟩ <;> simp only [h1, taB1, reduceCtorEq] at hn
      rcases h2 : taGoW j m1 no nl lvls ho hl f1 y with _ | ⟨x2, m2⟩ <;> simp only [h2, taB2, reduceCtorEq] at hn
      exact ((ihG _ _ _ _ _ _ _ _ _ _ h1).trans (ihG _ _ _ _ _ _ _ _ _ _ h2)).trans (rpMkW_mfr hn).up
    split at hn
    · rcases h1 : taGoW j m no nl lvls ho hl f1 x with _ | ⟨a2, m1⟩ <;> simp only [h1, taL1, reduceCtorEq] at hn
      rcases h2 : taGoW j m1 no nl lvls ho hl f1 y with _ | ⟨x2, m2⟩ <;> simp only [h2, taL2, reduceCtorEq] at hn
      rcases h3 : taGoW j m2 no nl lvls ho hl f1 z with _ | ⟨c2, m3⟩ <;> simp only [h3, taL3, reduceCtorEq] at hn
      exact (((ihG _ _ _ _ _ _ _ _ _ _ h1).trans (ihG _ _ _ _ _ _ _ _ _ _ h2)).trans
        (ihG _ _ _ _ _ _ _ _ _ _ h3)).trans (rpMkW_mfr hn).up
    · rcases h1 : taGoW j m no nl lvls ho hl f1 z with _ | ⟨a2, m1⟩ <;> simp only [h1, taP1, reduceCtorEq] at hn
      exact (ihG _ _ _ _ _ _ _ _ _ _ h1).trans (rpMkW_mfr hn).up

/-- **`target_abs` writes only its memo** (array `TAM`, `CTL[212]`, `CTL[213]`) besides the stores'
interns. -/
theorem taAW_mfr {n : Nat} {m m' : Mem} {no nl lvls ho hl e r : Word}
    (h : taAW n m no nl lvls ho hl e = some (r, m')) : MFr [TAM] [212, 213] m m' := by
  by_cases h0 : rdW (m.arr64 CTL) taSch.cs + 2 = 0
  · simp [taAW, h0] at h
  rw [taAW_eq n m no nl lvls ho hl e h0] at h
  exact MFr.trans ⟨_, _, mclearG_frame taSch m, by simp, by simp [taSch]⟩ ((taGoW_mfr n).1 _ _ _ _ _ _ _ _ _ _ h)

theorem RcMR.setTa {m m' : Mem} (h : RcMR m) (hf : MFr [TAM] [212, 213] m m') (hn : ∃ mp, taMR m' mp) :
    RcMR m' := ⟨h.pos.mfr hf (by simp [PosAv, NOM, DPM, RAM, HBM, RFM, TAM]), hn⟩

/-! ## Callees at any exec fuel -/

def tcpF : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, pfo, pfl, e => tcpW n m pfo pfl e

section rel
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

theorem tcpF_ok (n : Nat) {m m' : Mem} {a : AState} {pfo pfl e : Word} {pfvs : List EIdx} {r : List Word}
    (h : tcpF n m pfo pfl e = some (r, m')) (hS : StageR dn vis fe m a) (hpf : HSl0 m pfo pfl pfvs)
    (he : H e) (hP : RcMR m) :
    ∃ a', (ConRon.Arena.targetCanonParams pfvs (decE e)).run a = .ok (decE (r.headD 0), a') ∧
      H (r.headD 0) ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧ RcMR m' := by
  cases n with
  | zero => cases h
  | succ n => exact tcpW_ok dn fe vis n h hS hpf he hP

theorem taF_ok (n : Nat) {m m' : Mem} {a : AState} {no nl lvls ho hl e r : Word} {names : List NIdx}
    {holes : List EIdx} (h : taF n m no nl lvls ho hl e = some (r, m')) (hS : StageR dn vis fe m a)
    (he : H e) (hlv : H lvls)
    (hdec : decHL m no.toNat nl.toNat = some names) (hit : no.toNat + nl.toNat ≤ iwTop m)
    (hho : decHL m ho.toNat hl.toNat = some holes) (hht : ho.toNat + hl.toNat ≤ iwTop m) (hP : RcMR m) :
    ∃ a', (ConRon.Arena.targetAbs names (decI lvls) holes (decE e)).run a = .ok (decE r, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ RcMR m' := by
  cases n with
  | zero => cases h
  | succ n =>
    obtain ⟨mp, hM⟩ := hP.ta
    obtain ⟨a', mp1, hrun, hM1, hS', hg⟩ :=
      taAW_ok n dn fe vis m m' a no nl lvls ho hl e r names holes mp h hS he hlv hdec hit hho hht hM
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
