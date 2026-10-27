import ConAgua.Arena.IndPosSpec.BvbWMfr
import ConAgua.Arena.RecCheckSpec.TaCW

/-!
# BvbWStageC

`taF`, `bvbW_stageC`, `pdsK11`, `pdsK10`, `pdsK9`, `pdsK8`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

def taF : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, no, nl, lvls, ho, hl, e => taAW n m no nl lvls ho hl e

section rel
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

/-- **`bvar_b` under the stage relation at the twin's `coreWalkFuel`**, at any exec fuel (the L
fuel word `CWF` is `coreWalkFuel`: `bvbW_okF`'s first alternative). -/
theorem bvbW_stageC {m m' : Mem} {a : AState} (hS : StageR dn vis fe m a) (n : Nat)
    (h x : Word) (hh : H h) (hb : bvbW n m h CWF = some (x, m')) :
    ∃ a', (bvarB coreWalkFuel (decE h)).run a = .ok (x.toNat, a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      MFr [] [] m m' := by
  obtain ⟨a', hrun, hD⟩ := bvbW_okF n coreWalkFuel m m' a hS.1.arena h CWF x hh (.inl (Nat.le_of_eq CWF_eq)) hb
  have hfr : BbFrame m m' := by
    match n, hb with
    | n + 1, hb =>
      by_cases hs : derBW m h = 32767
      · rw [bvbW_sat (n := n) (m := m) (h := h) (f := CWF) hs] at hb
        match n, hb with
        | k + 1, hb => rw [bbN_succ] at hb; exact bbMemoW_frame k m m' h CWF x hb
      · rw [bvbW_pk (n := n) (m := m) (h := h) (f := CWF) hs] at hb
        obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
        exact MemFrame.refl _ _ _
  have hk : sp a' = sp a := by
    rw [bvarB_run] at hrun
    split at hrun
    · exact (keeps_bvarBoundMemo coreWalkFuel (decE h)).run hrun
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hrun; rw [hrun.2]
  have hcp : cp a' = cp a := by simp only [sp, Prod.mk.injEq] at hk; simp [cp, hk.2.1, hk.2.2]
  obtain ⟨hS', hg⟩ := StageR.of_walk hS hD hfr (by simp [BMEMO]) (by
    intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> decide) hcp
  exact ⟨a', hrun, hS', hg, bvbW_mfr hb⟩

end rel

/-! ## `target_params_def_eq_step`: the word model -/

def pdsK11 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

def pdsK10 (cR : CallM) (n : Nat) (vis d av bv : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => pdsK11 (cR n "is_def_eq_core" [vis, d, av, bv] m)

def pdsK9 (cR : CallM) (n : Nat) (vis d av bv : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => pdsK10 cR n vis d av bv (cR n "infer_type_core" [vis, d, bv] m)

def pdsK8 (cR : CallM) (n : Nat) (vis d av : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (bv, m) =>
    if 4294967296 ≤ bv then none
    else if av = bv then some ([1], m)
    else pdsK9 cR n vis d av bv (cR n "infer_type_core" [vis, d, av] m)

end L.Ind

end
