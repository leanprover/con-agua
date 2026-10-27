import ConAgua.Arena.PromoteRecRef

/-!
# Alloc

`alloc_rel`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

/-- **`erec_alloc(k)`**: the old top is returned, the top raised; the rest is untouched. -/
theorem alloc_rel {n : Nat} {k : Word} {m m' : Mem} {r : List Word}
    (hc : callW p (n + 1) "erec_alloc" [k] m = some (r, m')) :
    (r.headD 0).toNat = erecTop m ∧ erecTop m' = erecTop m + k.toNat ∧
    erecTop m + k.toNat ≤ (m.arr64 EREC).size ∧ MemFrame [] [129] m m' ∧
    m'.arr64 EREC = m.arr64 EREC := by
  obtain ⟨s₁, hs₁, -, hW₁⟩ := callW_triple (erecAlloc_spec p (hp.get "erec_alloc") n ⟨m, Locals.init []⟩ k) hc
  rw [hs₁] at hW₁
  obtain ⟨hdq, rfl, hd6, hroom, hctl⟩ := erAlloc_facts hW₁
  have hdv : (r.headD 0).toNat = erecTop m := by rw [hdq]; rfl
  refine ⟨hdv, ?_, by have h := hroom; simp only at h; omega, MemFrame.setCtl m 129 _, Mem.arr64_set64_ne _ _ _ _ _ (by decide)⟩
  simp only [erecTop]
  rw [rdW_set64, ite_eq_left ⟨rfl, rfl, by simpa using hctl⟩, hd6, hdv]; rfl

end rel

end L.Arena
