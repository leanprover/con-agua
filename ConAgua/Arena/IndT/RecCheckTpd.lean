module

public import ConAgua.Arena.RecCheckSpec.EraseFVarTys
import ConRon.Bridge.Inductives.RecCheck
public import ConAgua.Arena.RecCheckSpec.PdsC
public import ConAgua.Arena.RecCheckSpec.TaGoWMfr
import ConAgua.Arena.IndRealAbsPos
import ConAgua.Arena.IndRealAbsSim
public import ConAgua.Arena.IndTwin
public import ConRon.Bridge.Inductives.Run

@[expose] public section

/-!
# `targetParamsDefEq` under `StageC`: frames and the closedness reads

The facts `target_params_def_eq`'s refinement (`pds_ref`, `pde_ref`) uses besides the twin's specs:
the frames across the core calls, `target_canon_params` and `target_abs`, and the closedness reads
(`RC.closed4_bind_run`).
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep TAArgs)
open ConRon.Bridge (CoreStep denote_ext denoteEList_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Frames -/

/-- Across a core call: the stage memos stand but the `hb` memo (`CoreFr.mfr`). -/
theorem MFr.ofCore {p : Prog} (hcl : CoreStageClosed p) {f : FnName} (hf : f ∈ stageCoreFns)
    {n : Nat} {vs : List Word} {m m' : Mem} {r : List Word} (h : callW p n f vs m = some (r, m')) :
    MFr [HBM] [214, 215] m m' :=
  (callW_coreFrame hcl hf h).mfr

theorem tcpF_afr {n : Nat} {m m' : Mem} {pfo pfl e : Word} {r : List Word}
    (h : tcpF n m pfo pfl e = some (r, m')) : AFr m m' := by
  obtain _ | n := n
  · simp [tcpF] at h
  simp only [tcpF_succ, tcpF.j1, tcpF.k_rec3.eq_def, tcpF.k_replace_fvars.eq_def] at h
  afr_auto h [recW_afr, rxW_afr]

theorem taGoW_afr (n : Nat) :
    (∀ (m m' : Mem) (no nl lvls ho hl f h r : Word), taGoW n m no nl lvls ho hl f h = some (r, m') →
      AFr m m') ∧
    (∀ (m m' : Mem) (no nl lvls ho hl f1 g x y z r : Word),
      taNodeW n m no nl lvls ho hl f1 g x y z = some (r, m') → AFr m m') := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  cases n with
  | zero => exact ⟨fun _ _ _ _ _ _ _ _ _ _ h => by simp [taGoW.eq_1] at h,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => by simp [taNodeW.eq_1] at h⟩
  | succ j =>
  have ihG : ∀ (m m' : Mem) (no nl lvls ho hl f h r : Word), taGoW j m no nl lvls ho hl f h = some (r, m') →
      AFr m m' := (ih j (by omega)).1
  refine ⟨?_, ?_⟩
  · intro m m' no nl lvls ho hl f h r hg
    rcases taGoW_some hg with rfl | hc | ⟨rn, m1, hn, hs⟩
    · exact AFr.refl _
    · rw [taCW_same hc]; exact AFr.refl _
    cases j with
    | zero => rw [taNodeW.eq_1] at hn; cases hn
    | succ i =>
      exact ((ih (i + 1) (by omega)).2 _ _ _ _ _ _ _ _ _ _ _ _ _ hn).trans
        (AFr.of_frame (msetG_frame taSch taSch_wf m1 m' h 0 rn hs))
  · intro m m' no nl lvls ho hl f1 g x y z r hn
    rw [taNodeW.eq_def] at hn
    simp only at hn
    split at hn
    · obtain ⟨⟨a2, m1⟩, h1, hn⟩ := of_K hn (taNodeW.k_target_abs_go.none ..)
      rw [taNodeW.k_target_abs_go.arm1] at hn
      obtain ⟨⟨x2, m2⟩, h2, hn⟩ := of_K hn (taNodeW.k_target_abs_go_2.none _)
      rw [taNodeW.k_target_abs_go_2.arm1] at hn
      exact ((ihG _ _ _ _ _ _ _ _ _ _ h1).trans (ihG _ _ _ _ _ _ _ _ _ _ h2)).trans (mkAppW_afr hn)
    split at hn
    · obtain ⟨⟨a2, m1⟩, h1, hn⟩ := of_K hn (taNodeW.k_target_abs_go_3.none ..)
      rw [taNodeW.k_target_abs_go_3.arm1] at hn
      obtain ⟨⟨x2, m2⟩, h2, hn⟩ := of_K hn (taNodeW.k_target_abs_go_4.none _)
      rw [taNodeW.k_target_abs_go_4.arm1] at hn
      exact ((ihG _ _ _ _ _ _ _ _ _ _ h1).trans (ihG _ _ _ _ _ _ _ _ _ _ h2)).trans (mkLamW_afr hn)
    split at hn
    · obtain ⟨⟨a2, m1⟩, h1, hn⟩ := of_K hn (taNodeW.k_target_abs_go_5.none ..)
      rw [taNodeW.k_target_abs_go_5.arm1] at hn
      obtain ⟨⟨x2, m2⟩, h2, hn⟩ := of_K hn (taNodeW.k_target_abs_go_6.none _)
      rw [taNodeW.k_target_abs_go_6.arm1] at hn
      exact ((ihG _ _ _ _ _ _ _ _ _ _ h1).trans (ihG _ _ _ _ _ _ _ _ _ _ h2)).trans (mkForallW_afr hn)
    split at hn
    · obtain ⟨⟨a2, m1⟩, h1, hn⟩ := of_K hn (taNodeW.k_target_abs_go_7.none ..)
      rw [taNodeW.k_target_abs_go_7.arm1] at hn
      obtain ⟨⟨x2, m2⟩, h2, hn⟩ := of_K hn (taNodeW.k_target_abs_go_8.none ..)
      rw [taNodeW.k_target_abs_go_8.arm1] at hn
      obtain ⟨⟨c2, m3⟩, h3, hn⟩ := of_K hn (taNodeW.k_target_abs_go_9.none ..)
      rw [taNodeW.k_target_abs_go_9.arm1] at hn
      exact (((ihG _ _ _ _ _ _ _ _ _ _ h1).trans (ihG _ _ _ _ _ _ _ _ _ _ h2)).trans
        (ihG _ _ _ _ _ _ _ _ _ _ h3)).trans (mkLetW_afr hn)
    · obtain ⟨⟨a2, m1⟩, h1, hn⟩ := of_K hn (taNodeW.k_target_abs_go_10.none ..)
      rw [taNodeW.k_target_abs_go_10.arm1] at hn
      exact (ihG _ _ _ _ _ _ _ _ _ _ h1).trans (mkProjW_afr hn)

theorem taF_afr {n : Nat} {m m' : Mem} {no nl lvls ho hl e r : Word}
    (h : taF n m no nl lvls ho hl e = some (r, m')) : AFr m m' := by
  obtain _ | n := n
  · simp [taF] at h
  simp only [taF] at h
  by_cases h0 : rdW (m.arr64 CTL) taSch.cs + 2 = 0
  · simp [taAW, h0] at h
  rw [taAW.arm1 n m no nl lvls ho hl e h0] at h
  exact (AFr.of_frame (mclearG_frame taSch m)).trans ((taGoW_afr n).1 _ _ _ _ _ _ _ _ _ _ h)

/-! ## The closedness reads -/

/-- con-ron's `RC.closed4_bind_run` at `tpClosed`. -/
theorem tpClosed_pstep {pfvs : List EIdx} {a b : EIdx} {aP bP : ConLeche.Expr} {s₀ s' : AState}
    {c : Bool} (hok : ConRon.Bridge.StateOK s₀) (ha : denoteE s₀.store a = some aP)
    (hb : denoteE s₀.store b = some bP)
    (hrun : (tpClosed pfvs a b).run s₀ = .ok (c, s')) :
    PStep s₀ s' ∧ c = (aP.bvarB == 0 && bP.bvarB == 0 && decide (aP.fvarB ≤ pfvs.length) &&
      decide (bP.fvarB ≤ pfvs.length)) := by
  have hrun' : (tpClosed pfvs a b) s₀ = .ok (c, s') := hrun
  obtain ⟨s1, p1, z1⟩ := ConRon.Bridge.Inductives.RC.closed4_bind_run (k := pure) (n := pfvs.length)
    hok ha hb (by simpa only [tpClosed, pure_bind, bind_pure] using hrun')
  obtain ⟨rfl, rfl⟩ := ConRon.Bridge.AM.pure_ok z1
  exact ⟨p1, rfl⟩

end L.Ind
