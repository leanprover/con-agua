import ConAgua.Arena.PromoteCIInfra

/-!
# StPNat

`stP_nat`, `FireWords`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

theorem stP_nat (d : Word) (ps : List (Word × Word)) {m m' : Mem}
    (hlt : ∀ q ∈ ps, d.toNat + q.1.toNat < 2 ^ 64) (hnd : (ps.map (fun q => q.1.toNat)).Nodup)
    (h : stP d m ps = some m') :
    (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ MemFrame [EREC] [] m m' ∧
    (∀ i, (∀ q ∈ ps, d.toNat + q.1.toNat ≠ i) → (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
    (∀ q ∈ ps, d.toNat + q.1.toNat < (m.arr64 EREC).size) ∧
    (∀ q ∈ ps, (m'.arr64 EREC)[d.toNat + q.1.toNat]? = some q.2) := by
  have e : ∀ q ∈ ps, (d + q.1).toNat = d.toNat + q.1.toNat := by
    intro q hq; rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (hlt q hq)
  have hpw : ps.Pairwise (fun a b => (d + a.1).toNat ≠ (d + b.1).toNat) := by
    have := List.pairwise_map.mp hnd
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) this
    rw [e a ha, e b hb]; omega
  obtain ⟨h1, h2, h3, h4, h5⟩ := stP_facts d ps m m' hpw h
  refine ⟨h1, h2, fun i hi => h3 i (fun q hq => by rw [e q hq]; exact hi q hq), fun q hq => ?_,
    fun q hq => ?_⟩
  · have := h4 q hq; rwa [e q hq] at this
  · have := h5 q hq; rwa [e q hq] at this

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

/-- **A promoted firing mode's five words** denote `fire` in the pool `A`. -/
def FireWords (A : Array Word) (k q b r y : Word) (fire : IRecRuleFire) : Prop :=
  (k = 0 ∧ fire = IRecRuleFire.plain) ∨
  (k = 1 ∧ ∃ lv ps, fire = IRecRuleFire.nested lv ps ∧ hslice? A q.toNat b.toNat = some lv ∧
    hslice? A r.toNat y.toNat = some ps)

end rel

end L.Arena
