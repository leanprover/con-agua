import ConAgua.Arena.IndPartsSpec.BmgW
import ConAgua.Census.Attr

/-!
# BlockMemberCounts: `ConRon.Arena.blockMemberCounts`

The refinement theorems `blockMemberCounts_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **`block_member_counts` refines `blockMemberCounts?`** from member `0` (through
`rec_target_of`'s and `block_counts`' stubs; the counts and the recursor records' words past
`2^32` a capacity abort): the formers a slice of constants, the recursors the split's records,
both decoded below the tops; the result a number slice decoded below the tops (`NsR`). -/
@[refines ConRon.Arena.blockMemberCounts?]
theorem blockMemberCounts_refines (p : Prog) (hP : IndPartsProg4 p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (nPd k nC no nl ro rl cto ctl : Word)
    (names : List NIdx) (cvTs : List IConstantVal) (rs : List (IConstantVal × Nat × Nat × List IRecRule))
    (hS : StageR dn vis fe s₀.mem a₀) (hts : PSlR decCVp cvTs cto ctl s₀.mem)
    (hrs : PSlR decSR rs ro rl s₀.mem) (hnm : DecB (fun m => decHL m no.toNat nl.toNat) s₀.mem names)
    (hnb : no.toNat + nl.toNat ≤ iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "block_member_counts" [nPd, k, nC, no, nl, ro, rl, cto, ctl]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.blockMemberCounts? nPd.toNat k.toNat nC.toNat names rs 0 cvTs) a₀ ∧
      NsR (AM.res (ConRon.Arena.blockMemberCounts? nPd.toNat k.toNat nC.toNat names rs 0 cvTs) a₀) r s'.mem ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.blockMemberCounts? nPd.toNat k.toNat nC.toNat names rs 0 cvTs) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (bmc_spec p hP n s₀ nPd k nC no nl ro rl cto ctl) ?_
  rintro r s' ⟨hl, hm⟩
  unfold bmcW at hm
  split at hm
  · cases hm
  rename_i hg
  have b : ∀ w : Word, ¬ 4294967296 ≤ w → w.toNat < 2 ^ 32 := fun w h => by
    rw [UInt64.le_iff_toNat_le] at h; simpa using h
  have hsim := bmgW_sim (b nPd (fun h => hg (Or.inl h))) (b k (fun h => hg (Or.inr (Or.inl h))))
    (b nC (fun h => hg (Or.inr (Or.inr (Or.inl h))))) (b rl (fun h => hg (Or.inr (Or.inr (Or.inr h))))) n
    s₀.mem a₀ cto ctl 0 cvTs hS hts hrs hnm hnb (by simp; have := hts.2; omega)
  rcases hb : bmgW n s₀.mem nPd k nC no nl ro rl cto ctl 0 with _ | ⟨r1, m1⟩ <;> rw [hb] at hm
  · cases hm
  rw [bmfK2_some] at hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm)
  obtain ⟨hok, hR, hS', hg'⟩ := Sim.run hsim hb
  exact ⟨hl, hok, NsR_three hR, hS', hg'⟩

end L.Ind

end
