module

public import ConAgua.Front.FrontRun
public import ConAgua.Front.DeclsPre

@[expose] public section

/-!
# The frontend after the prelude: records already in `DECL` (lane `pipeline`)

The checker parses the stream with the prelude's records still in `DECL[0‥P)`
(`Checker/Prelude.lean`): `front_run` starts from a memory related to the blank parse state
prefixed by them (`StateD.blank.pre D`, `Front/DeclsPre.lean`). The twin's parse only pushes to
`decls` (`applyLine_pre`), so the frontend's own refinement carries over: the memory is related to
the twin's parse state prefixed by `D` (`FrontInvP`, the driver's invariant, `FrontRunRef.lean`).
-/

open Std.WP
open scoped Lean.Order
open L.Arena
open ConLeche.Frontend hiding StateD RecordVerdict applyLine parseBytes ParseResultD parseChunks
open ConRon.Arena ConRon.Arena.Frontend

namespace L.Front

section pre
variable (D : Array IDeclaration)

theorem applyLine_pre_ok {st : StateD} {r : LineRec} {a : AState} :
    AM.ok (applyLine (st.pre D) r) a ↔ AM.ok (applyRecord st r) a := by
  simp only [AM.ok, applyLine_pre_run]
  cases (applyRecord st r).run a <;> rfl

theorem applyLine_pre_st {st : StateD} {r : LineRec} {a : AState} :
    AM.st (applyLine (st.pre D) r) a = AM.st (applyRecord st r) a := by
  simp only [AM.st, applyLine_pre_run]
  cases (applyRecord st r).run a <;> rfl

theorem applyLine_pre_res {st : StateD} {r : LineRec} {a : AState} (h : AM.ok (applyRecord st r) a) :
    AM.res (applyLine (st.pre D) r) a = preL D (AM.res (applyRecord st r) a) := by
  simp only [AM.res, AM.ok, applyLine_pre_run] at h ⊢
  revert h
  cases (applyRecord st r).run a with
  | error e => simp
  | ok v => intro _; rfl

/-- The driver's invariant after the prelude: the input is `b`, the memory related to the twin's
parse state prefixed by `D`, con-ron's bridge invariant of the twin's own. -/
def FrontInvP (b : ByteArray) (m : Mem) (a : AState) (st : StateD) : Prop :=
  m.arr8 IN = b.data ∧ ArenaD m a ∧ StateDR m (st.pre D) ∧ TwinOK a st ∧ ModeOK m

section init
variable (m m' : Mem) (a : AState) (hR : ArenaD m a) (hD : StateDR m (StateD.blank.pre D))

include hR hD in
theorem frontInitW_refines_pre (h : frontInitW m = some m') :
    AM.ok ConRon.Arena.Frontend.StateD.init a ∧ ArenaD m' (AM.st ConRon.Arena.Frontend.StateD.init a) ∧
      StateDR m' ((AM.res ConRon.Arena.Frontend.StateD.init a).pre D) := by
  simp only [frontInitW] at h
  cases h1 : putK NID 0 (nainternW m) with
  | none => rw [h1] at h; simp [initK] at h
  | some m₂ =>
    rw [h1, initK_some] at h
    obtain ⟨w₁, m₁, hI1, hw1, hp1⟩ := putK_eq h1
    obtain ⟨w₂, m₃, hI2, hw2, hp2⟩ := putK_eq h
    obtain ⟨ok1, R1, res1, hf1⟩ := nanon_A m a hR w₁ m₁ hI1
    have R2 := ArenaD.putT _ _ _ R1 NID (.inl rfl) 0 w₁ hp1
    obtain ⟨ok2, R3, res2, hf2⟩ := zero_A _ _ R2 w₂ m₃ hI2
    have hX : ConRon.Arena.Frontend.StateD.init = (internNNode .anonymous >>= fun n0 => internLNode .zero >>= fun l0 =>
        pure ({ names := IdTable.singleton n0, levels := IdTable.singleton l0 } : StateD)) := rfl
    let n0 := AM.res (internNNode .anonymous) a
    obtain ⟨okI, stI, resI⟩ := AM.bind_pure (internLNode .zero)
      (fun l0 => ({ names := IdTable.singleton n0, levels := IdTable.singleton l0 } : StateD))
      (AM.st (internNNode .anonymous) a) ok2
    have okX : AM.ok ConRon.Arena.Frontend.StateD.init a := by rw [hX, AM.ok_bind]; exact ⟨ok1, okI⟩
    have D1 : StateDR m₂
        { names := IdTable.singleton (decI w₁), levels := {}, decls := D } :=
      hD.putName hf1 (by tapart) (by tapart) 0 w₁ hp1 hw1 _
        (fun j => by simp [IdTable.get?_singleton, StateD.blank, StateD.pre, IdTable.get?_empty])
        rfl (by simp [StateD.blank, StateD.pre])
    refine ⟨okX, ?_, ?_⟩
    · rw [hX] at okX ⊢
      rw [AM.st_bind _ _ _ okX, stI]
      exact ArenaD.putT _ _ _ R3 LID (.inr (.inl rfl)) _ _ hp2
    · rw [hX, AM.res_bind _ _ _ ok1, resI, res2]
      simp only [n0, res1]
      exact D1.putLevel hf2 (by tapart) (by tapart) 0 w₂ hp2 hw2 _
        (fun j => by simp [IdTable.get?_singleton, IdTable.get?_empty]) rfl
        (by simp [StateD.pre])

end init

end pre

end L.Front
