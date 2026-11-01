module

import ConAgua.Arena.DeclDivModSpec.DivModTypePins
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.Arena.DeclNatGate
public import ConAgua.Rom.PinSets

@[expose] public section

/-!
# DecCIDefnValue

`PinsIW`, `PinsIW.grow`, `decCI_defn_value`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open L.Rom (PinSetR)

namespace L.Ind

open L.Arena

/-- **The variant slice**: `IW[o ‥ o + l]` holds pointers to the 40-word records of the variants
`ips`, in order. -/
def PinsIW (m : Mem) (o l : Nat) (ips : List INatOpPinSet) : Prop :=
  o + l ≤ iwTop m ∧ l = ips.length ∧ ∀ (j : Nat) (hj : j < ips.length), ∃ ps : Word,
    (iwA m)[o + j]? = some ps ∧ PinSetR m ps ips[j]

theorem PinsIW.grow {m m' : Mem} {o l : Nat} {ips : List INatOpPinSet} (h : PinsIW m o l ips)
    (hg : IWGrow m m') : PinsIW m' o l ips := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Nat.le_trans h1 hg.iw, h2, fun j hj => ?_⟩
  obtain ⟨ps, hp, hP⟩ := h3 j hj
  refine ⟨ps, ?_, PinSetR.grow hP hg⟩
  simp only [iwA] at hp ⊢; rw [hg.iwGet _ (by omega)]; exact hp

theorem decCI_defn_value {a : Array Word} {dn : NIdx → Option ConLeche.Name} {p : Nat}
    {cv : IConstantVal} {v : EIdx} {hint : ConLeche.ReducibilityHint}
    (h : decCI a dn p = some (.defnInfo cv v hint)) :
    a[p]? = some 1 ∧ ∃ w, a[p + 5]? = some w ∧ w.toNat < 2 ^ 32 ∧ v = decI w := by
  obtain ⟨hk, -⟩ : a[p]? = some 1 ∧ True := by
    rcases decCI_defn_cases h with ⟨cv', v', hint', he, hk, hcv⟩ | ⟨w, hw, hne, hnd⟩
    · exact ⟨hk, trivial⟩
    · exact absurd rfl (hnd cv v hint)
  refine ⟨hk, ?_⟩
  unfold decCI at h
  have hn : nat? a p = some 1 := by simp [nat?, hk]
  rw [hn] at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨a1, ha1, h⟩ := h
  cases ha1
  simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨cv2, -, v2, hv2, h3, -, he2⟩ := h
  have hv : v2 = v := by cases he2; rfl
  subst hv
  cases hq : a[p + 5]? with
  | none => simp [hd?, hq] at hv2
  | some w =>
    by_cases hlt : w.toNat < 2 ^ 32
    · have e : (hd? a (p + 5) : Option EIdx) = some (decI w) := by simp [hd?, hq, hlt]
      rw [e] at hv2
      exact ⟨w, rfl, hlt, (Option.some.inj hv2).symm⟩
    · simp [hd?, hq, hlt] at hv2

end L.Ind
