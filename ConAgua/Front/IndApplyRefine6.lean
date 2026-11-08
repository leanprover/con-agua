module

import ConRon.Bridge.Frontend.Rel
import ConAgua.Front.IndApplyRefine
import ConAgua.Arena.LevelArena
public import Std.Tactic.BVDecide.Normalize.Prop
public import ConAgua.Arena.LevelLeqRel
public import ConAgua.Front.IndApplySpec
public import ConRon.Arena.Frontend.ExportC
public import ConRon.Bridge.StateOK

@[expose] public section

/-!
# The apply step of an `inductive` line against the twin, VI: `kExpected?`

`kExpW_twin`: `vi_k_expected` against the twin's `kExpected?` match: a block that is not one type
with one constructor is `some false` (`1`); else the sort at the end of the type's telescope is read
back (`readLevel`) and compared with `zero` by `Level.isEquiv` — in L by `lv_equiv` against a heap
`zero` node, which agrees with the twin because the name store is well formed (`StateOK`: `nameN`
is a `NameRel`, `equivW_ok`).
-/

open L.Arena
open ConRon.Arena
open ConRon.Arena.Frontend
open L.Ind (eViewW eViewW_ok ViewR)


namespace L.Front.Ind

/-- A sort's level, under the store's well-formedness, reads back. -/
theorem denoteL_of_sort {a : AState} (hok : ConRon.Bridge.StateOK a) {r : EIdx} {s : LIdx}
    (h : a.store.view r = some (.sort s)) : ∃ L, denoteL a.store.ls s = some L := by
  sorry

theorem readLevel_run' {a : AState} {s : LIdx} {L : ConLeche.Level} (h : denoteL a.store.ls s = some L) :
    (readLevel s).run a = .ok (L, a) := by
  rw [show (readLevel s).run a = (match denoteL a.store.ls s with
    | some l => (pure l : AM ConLeche.Level)
    | none => fail (.internal "arena: dangling level handle")).run a from rfl, h]
  rfl

theorem encO_two (o : Option Bool) : encO o = 2 ↔ o = some true := by
  cases o with
  | none => simp [encO]
  | some x => cases x <;> simp [encO]

end L.Front.Ind
