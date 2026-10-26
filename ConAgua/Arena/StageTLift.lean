import ConAgua.Arena.TwinStep

/-!
# Lifting stage facts from `StageR` to `StageT` (lane `indproofs3`)

`StageT` (`IndTwin.lean`) is `StageR` with the twin's invariants `TwinOK` and the pin flag. A stage
theorem proved under `StageR` lifts to `StageT` when its callee's twin op changes at most the
per-call memos (readers, checks, walks over `a.memos`) and its L run leaves the core memos and
the pins alone: `StageT.lift_keep`. `KeepPostT` is `KeepPost` with `StageT` after.
-/


open ConRon.Arena

namespace L.Ind

open L.Arena

/-- The post of a callee that keeps `StageT` (`KeepPost` with `StageT`). -/
def KeepPostT {α : Type} (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (dec : Mem → List Word → α → Prop) (m m' : Mem) (a : AState) (r : List Word) (x : α) : Prop :=
  StageT dn vis fe m' a ∧ IWGrow m m' ∧ dec m' r x

/-! ## Lifting a `StageR` fact to `StageT` (callees that leave the twin's store, caches and pins) -/

section lift
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- `TwinOK` reads the twin state's store, caches and pins only: a change of the per-call memos
keeps it. -/
theorem _root_.L.Arena.TwinOK.withMemos {m : Mem} {a : AState} (h : TwinOK dn m a fe) (X : Memos) :
    TwinOK dn m { a with memos := X } fe :=
  ⟨h.readL, h.readLs, h.nwf, h.erec, h.spn, h.memos, h.bstk, h.den.caches rfl rfl rfl⟩

/-- **A `StageR` `Sim` is a `StageT` `Sim`** for a callee whose twin op changes at most the per-call
memos (readers, checks, the walks over `a.memos`) and whose L run leaves the core memos and the
pins alone (`hfr`; lane `loopt`'s `TwinOK.frame`). One line per existing stage theorem. -/
theorem StageT.lift_keep {β α : Type} {mo : Option (β × Mem)} {op : AM α} {m : Mem} {a : AState}
    {Q : β → α → Mem → AState → Prop} {A : List ArrId} {C : List Word}
    (hT : StageT dn vis fe m a)
    (h : Sim mo op a (fun r x m' a' => StageR dn vis fe m' a' ∧ Q r x m' a'))
    (hkeep : ∀ x a', op.run a = .ok (x, a') → ∃ X, a' = { a with memos := X })
    (hfr : ∀ r m', mo = some (r, m') → MemFrame A C m m')
    (hP : PINS ∉ A) (hA : (50 : ArrId) ∉ A ∧ (49 : ArrId) ∉ A) (hC : (50 : Word) ∉ C ∧ (48 : Word) ∉ C)
    (hWA : (151 : ArrId) ∉ A ∧ (152 : ArrId) ∉ A ∧ (153 : ArrId) ∉ A)
    (hWC : (152 : Word) ∉ C ∧ (154 : Word) ∉ C ∧ (156 : Word) ∉ C)
    (hLA : (52 : ArrId) ∉ A ∧ (53 : ArrId) ∉ A ∧ (54 : ArrId) ∉ A)
    (hLC : (54 : Word) ∉ C ∧ (56 : Word) ∉ C ∧ (58 : Word) ∉ C) :
    Sim mo op a (fun r x m' a' => StageT dn vis fe m' a' ∧ Q r x m' a') := by
  intro r m' e
  obtain ⟨x, a', hrun, hS', hq⟩ := h r m' e
  obtain ⟨X, rfl⟩ := hkeep x a' hrun
  have hf := hfr r m' e
  have hPe : m'.arr64 PINS = m.arr64 PINS := hf.1 PINS hP (by decide)
  exact ⟨x, _, hrun, ⟨hS', (hT.twin.frame hf hA hC hWA hWC hLA hLC).withMemos X,
    by simp only [pinW, hPe]; exact hT.flag⟩, hq⟩

end lift

end L.Ind
