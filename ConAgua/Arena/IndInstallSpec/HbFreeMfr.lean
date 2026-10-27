import ConAgua.Arena.IndInstallSpec.TabsProg
import ConAgua.Arena.IndPartsSpec.IndPartsProg2

/-!
# HbFreeMfr

`hbFreeA`, `hbFreeC`, `hbFree_mfr`, `HbMemo.ofClosed`, `posFreeA`, `posFreeC` and the lemmas only they use.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Write sets from the program text -/

/-- Every word array below 320 (both tiers) but the `has_loose_bvar_b` memo's. -/
def hbFreeA : List ArrId := (List.range 388).filter (· ≠ HBM)
/-- Every `CTL` word below 256 but the `hb` memo's stamp word. -/
def hbFreeC : List Word := ((List.range 256).filter (· ≠ 214)).map Nat.toUInt64

theorem hbFree_mfr {m m' : Mem} (h : MemFrame hbFreeA hbFreeC m m') :
    MFr [MAM, NOM, DPM, RFM, RAM, TAM, MCM]
      [202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 215, 216, 217, 218, 219] m m' := by
  refine ⟨hbFreeA, hbFreeC, h, fun b hb => ?_, fun x hx => ?_⟩
  · simp only [hbFreeA, List.mem_filter, List.mem_range, decide_eq_true_eq] at hb
    obtain ⟨c, hc⟩ : ∃ c : Nat, c = b := ⟨b, rfl⟩
    have h1 : c < 388 := hc ▸ hb.1
    have h2 : c ≠ 207 := hc ▸ hb.2
    subst hc
    by_cases a1 : c < 201; · exact .inl a1
    by_cases a2 : 208 < c; · exact .inr (.inl a2)
    right; right
    rcases (show c = 201 ∨ c = 202 ∨ c = 203 ∨ c = 204 ∨ c = 205 ∨ c = 206 ∨ c = 208 by omega) with
      h | h | h | h | h | h | h <;> subst h <;> decide
  · simp only [hbFreeC, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hx
    obtain ⟨c, ⟨hc, hne⟩, rfl⟩ := hx
    have hc' : (Nat.toUInt64 c).toNat = c := by simp; omega
    rw [hc']
    by_cases h1 : c < 202; · exact .inl h1
    by_cases h2 : 219 < c; · exact .inr (.inl h2)
    right; right
    rcases (show c = 202 ∨ c = 203 ∨ c = 204 ∨ c = 205 ∨ c = 206 ∨ c = 207 ∨ c = 208 ∨ c = 209 ∨
      c = 210 ∨ c = 211 ∨ c = 212 ∨ c = 213 ∨ c = 215 ∨ c = 216 ∨ c = 217 ∨ c = 218 ∨ c = 219 by omega) with
      h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide

/-- **A call of a function of a set closed outside the `hb` memo keeps it well formed.** -/
theorem HbMemo.ofClosed {p : Prog} {fs : List FnName} (hcl : closedA p hbFreeA hbFreeC fs = true)
    {f : FnName} (hf : f ∈ fs) {n : Nat} {vs : List Word} {m : Mem} {r : List Word} {m' : Mem}
    (h : callW p n f vs m = some (r, m')) (hM : HbMemo m) : HbMemo m' := by
  obtain ⟨mp, hmp⟩ := hM
  exact ⟨mp, hbMR_mfr (hbFree_mfr (run_memFrame hcl hf (run_of_callW h)).1) (by decide) (by decide) hmp⟩

/-- Every word array below 320 (both tiers) but the five walk memos'. -/
def posFreeA : List ArrId := (List.range 388).filter (fun b => b ∉ [NOM, DPM, RAM, HBM, RFM])
/-- Every `CTL` word below 256 but the five memos' stamp words (and the banked memo's two). -/
def posFreeC : List Word :=
  ((List.range 256).filter (fun c => c ∉ [204, 206, 208, 210, 214, 218, 219])).map Nat.toUInt64

/-! ## The record's slices -/

/-- **The `BlockPass` record and its eight slices lie below the pool's top.** -/
def BPassB (m : Mem) (q : Nat) : Prop :=
  q + 19 ≤ iwTop m ∧ ∀ i ∈ [1, 4, 6, 8, 10, 12, 15, 17], ∀ o l, iwN m (q + i) = some o →
    iwN m (q + i + 1) = some l → o + l ≤ iwTop m

/-- A word of the pool below the top, read where L reads it. -/
theorem bpWord {m : Mem} {i v : Nat} (h : iwN (truncM m) i = some v) {w : Word} (hw : w.toNat = i) :
    rdW (m.arr64 IW) w = UInt64.ofNat v ∧ v < 2 ^ 64 := by
  obtain ⟨h1, h2, -⟩ := partsIwRd h hw; exact ⟨h1, h2⟩

end L.Ind
