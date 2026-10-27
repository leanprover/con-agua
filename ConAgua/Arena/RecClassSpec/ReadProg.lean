import ConAgua.Arena.IndDecStab
import ConAgua.Arena.RecClassSpec.SlotsProg
import ConAgua.Arena.RecStab

/-!
# ReadProg

`ReadProg`, `FA2.get`, `decRead`, `RecsDec`, `iwN_truncM_get`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Models -/

/-- The lookups `class_read` needs. -/
structure ReadProg (p : Prog) : Prop extends SlotsProg p where
  mp : p.lookup "class_read_mot_pos" = some classReadMotPos
  rcl : p.lookup "class_read_rec_cls" = some classReadRecCls
  rfin : p.lookup "class_read_finish" = some classReadFinish
  ns : p.lookup "class_read_n_slots" = some classReadNSlots
  rd : p.lookup "class_read" = some classRead

end L.Ind

namespace L.Ind

open L.Arena

theorem FA2.get {α β : Type} {R : α → β → Prop} : ∀ {as : List α} {bs : List β}, FA2 R as bs →
    ∀ j (h1 : j < as.length) (h2 : j < bs.length), R (as[j]'h1) (bs[j]'h2)
  | _, _, .nil, j, h1, _ => by simp at h1
  | _, _, .cons h hs, 0, _, _ => h
  | _, _, .cons _ hs, j + 1, h1, h2 => FA2.get hs j (by simpa using h1) (by simpa using h2)

/-- `class_read`'s result: `none`, or a stably decoding `ClassRead` record. -/
def decRead (m' : Mem) (r : List Word) : Option ClassRead → Prop
  | none => r.headD 0 = 0
  | some cr => r.headD 0 = 1 ∧ StabD (fun m => decCR m (r.tail.headD 0).toNat) m' cr ∧
      ∃ so sl, iwN m' (r.tail.headD 0).toNat = some so ∧ iwN m' ((r.tail.headD 0).toNat + 1) = some sl ∧
        SPL decCS m' so sl cr.slots

/-- The recursors decoded below the tops, their slice word-addressable (a major index past
`2^64 - 2` is `class_read_rec_cls`' capacity abort, lane `indproofs4`). -/
def RecsDec (m : Mem) (ro rl : Word) (recs : List RecShape) : Prop :=
  DecB (fun m => decPL m (decRS m) ro.toNat rl.toNat) m recs ∧ ro.toNat + rl.toNat < 2 ^ 64

theorem iwN_truncM_get {m : Mem} {i v : Nat} (h : iwN (truncM m) i = some v) :
    i < iwTop m ∧ iwN m i = some v := by
  simp only [iwN, nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h
  obtain ⟨hi, hw'⟩ := truncM_iw_get hw
  exact ⟨hi, by simp [iwN, nat?, hw']⟩

end L.Ind

end
