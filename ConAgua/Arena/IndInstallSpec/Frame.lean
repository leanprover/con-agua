import ConAgua.Arena.IndInstallSpec.OfClosed
import ConAgua.Arena.IndRealBph2

/-!
# Frame

`cidK2`, `cidFreeA`, `cidFreeC`, `CidMemos`, `CidMemos.frame`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## The model -/

section model
variable (p : Prog)

/-- After `check_basis_decl` or `check_block`: the view. -/
def cidK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

end model

/-! ## The write set of `basis_pin_hit` and `block_parts` -/

/-- The arrays they may write: all below 320 (both tiers) but the stage memos' (`201..208`) and `abstract1`'s
memo (`49`), and since lane `indstaget` the pins and the core's walk memos. -/
def cidFreeA : List ArrId := (List.range 388).filter (fun b => (b < 201 ∨ 208 < b) ∧ b ≠ 49 ∧ b ≠ 50 ∧ b ≠ 51 ∧ b ≠ 155 ∧
  b ≠ PINS ∧ b ≠ 151 ∧ b ≠ 152 ∧ b ≠ 153 ∧ b ≠ 52 ∧ b ≠ 53 ∧ b ≠ 54)

/-- The `CTL` words they may write: all below 256 but the stage memos' (`202..219`) and
the walk memos' epoch words (`48`, `50`, `52`, `158`). -/
def cidFreeC : List Word :=
  ((List.range 256).filter (fun c => (c < 202 ∨ 219 < c) ∧ c ≠ 48 ∧ c ≠ 50 ∧ c ≠ 52 ∧ c ≠ 158 ∧
    c ≠ 152 ∧ c ≠ 154 ∧ c ≠ 156 ∧ c ≠ 54 ∧ c ≠ 56 ∧ c ≠ 58)).map Nat.toUInt64

/-- The memos the arm carries to `check_block`. -/
def CidMemos (m : Mem) : Prop :=
  PosMR m ∧ (∃ mp, maMR m mp) ∧ AbsOK m ∧ ∃ mp, taMR m mp

theorem CidMemos.frame {m m' : Mem} (h : CidMemos m) (hf : MemFrame cidFreeA cidFreeC m m') :
    CidMemos m' := by
  have hM : MFr [] [] m m' := MFr.of_frame hf
    (fun b hb => by
      simp only [cidFreeA, List.mem_filter, List.mem_range, decide_eq_true_eq] at hb
      exact hb.2.1)
    (fun x hx => by
      simp only [cidFreeC, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hx
      obtain ⟨c, ⟨hc, h1, -⟩, rfl⟩ := hx
      have : (Nat.toUInt64 c).toNat = c := UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)
      rw [this]; exact h1)
  obtain ⟨hP, ⟨mp, hma⟩, hA, ⟨tp, hta⟩⟩ := h
  refine ⟨hP.fr hM, ⟨mp, maMR_mfr hM hma⟩, ?_, ⟨tp, taMR_mfr hM (by simp) (by simp) hta⟩⟩
  exact AFr.of_frame hf (by decide +kernel) (by decide +kernel) hA

end L.Ind
