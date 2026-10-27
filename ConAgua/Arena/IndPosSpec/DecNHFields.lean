import ConAgua.Arena.IndIface

/-!
# DecNHFields

`decNH_fields`, `iwN_of_get`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem decNH_fields {m : Mem} {w : Nat} {hl : NestHole} (h : decNH m w = some hl) :
    ∃ k, iwN m w = some k ∧ decNK m k = some hl.key := by
  simp only [decNH, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk, key, hkey, b, hb, h'⟩ := h
  obtain rfl := Option.some.inj h'
  exact ⟨k, hk, hkey⟩

theorem iwN_of_get {m : Mem} {i : Nat} {w : Word} (h : (m.arr64 IW)[i]? = some w) : iwN m i = some w.toNat := by
  simp [iwN, nat?, iwA, h]

end L.Ind

end
