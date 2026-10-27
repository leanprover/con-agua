import ConAgua.Arena.IndPosSpec.CtxFields
import ConAgua.Arena.IndPosSpec.PiBWStage

/-!
# NkFields

`NKSl`, `nk_fields`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `nest_inst_type_ty`: the relational side -/

/-- A `NestKey` record's `ds` slice ends below the pool's top. -/
def NKSl (m : Mem) (key : Word) : Prop :=
  (rdW (m.arr64 IW) (key + 2)).toNat + (rdW (m.arr64 IW) (key + 3)).toNat ≤ iwTop m

/-- A decoded `NestKey`'s fields, as the words L reads. -/
theorem nk_fields {m : Mem} {key : Word} {kk : NestKey} (hk : decNK m key.toNat = some kk)
    (hin : NKIn m key.toNat (· < iwTop m)) (htop : iwTop m < 2 ^ 64) :
    H (rdW (m.arr64 IW) key) ∧ decI (rdW (m.arr64 IW) key) = kk.cname ∧
    H (rdW (m.arr64 IW) (key + 1)) ∧ decI (rdW (m.arr64 IW) (key + 1)) = kk.lvls ∧
    decHL m (rdW (m.arr64 IW) (key + 2)).toNat (rdW (m.arr64 IW) (key + 3)).toNat = some kk.ds ∧
    (∀ j < (rdW (m.arr64 IW) (key + 3)).toNat, (rdW (m.arr64 IW) (key + 2)).toNat + j < iwTop m) ∧
    key.toNat + 4 ≤ iwTop m := by
  simp only [decNK, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at hk
  obtain ⟨c, hc, u, hu, ds, hds, heq⟩ := hk
  cases Option.some.inj heq
  have h3 := hin.1 3 (by omega)
  obtain ⟨o, l, ho, hl, hd⟩ := decAt_some hds
  have r2 : (rdW (m.arr64 IW) (key + 2)).toNat = o := rd_iwN (by simpa using ho) (by simp; omega)
  have r3 : (rdW (m.arr64 IW) (key + 3)).toNat = l := rd_iwN (by simpa using hl) (by simp; omega)
  obtain ⟨h0a, h0b⟩ := rd_iwH0E (m := m) (o := key) hc
  obtain ⟨h1a, h1b⟩ := rd_iwH (p := key) (i := 1) (by simpa using hu) (by simp; omega)
  refine ⟨h0a, h0b, h1a, h1b, by rw [r2, r3]; exact hd, by rw [r2, r3]; exact hin.2 o l ho (by simpa using hl), by omega⟩

end L.Ind

end
