module

import ConAgua.Arena.IndPosSpec.BvbWMfr
public import ConAgua.Arena.RecCheckSpec.TaCW
import ConAgua.Arena.BvarBRefine

@[expose] public section

/-!
# BvbWStageC

`taF`, `bvbW_stageC`.
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
theorem bvbW_stageC {m m' : Mem} {a : AState} (hS : StageR vis fe m a) (n : Nat)
    (h x : Word) (hh : H h) (hb : bvbW n m CWF h = some (x, m')) :
    ∃ a', (bvarB coreWalkFuel (decE h)).run a = .ok (x.toNat, a') ∧ StageR vis fe m' a' ∧ IWGrow m m' ∧
      MFr [] [] m m' := by
  obtain ⟨a', hrun, hD⟩ := bvbW_okF n coreWalkFuel m m' a hS.check.arena h CWF x hh (.inl (Nat.le_of_eq CWF_eq)) hb
  have hfr : BbFrame m m' := by
    match n, hb with
    | n + 1, hb =>
      by_cases hs : derBW m h = 32767
      · rw [bvbW.arm1 n m CWF h hs] at hb
        match n, hb with
        | k + 1, hb => rw [bbN_succ] at hb; exact bbMemoW_frame k m m' h CWF x hb
      · rw [bvbW.arm2 n m CWF h hs] at hb
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

end L.Ind

end
