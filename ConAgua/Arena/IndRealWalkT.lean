import ConAgua.Arena.IndRealWalk
import ConAgua.Arena.StageTLift

/-!
# `has_fvar_fast`, `loose_bvars_bounded_fast` under `StageT` (lane `indproofs4`)

`IndRealWalk.lean`'s `hffF_ok`, `lbbF_ok` lifted by `StageT.lift_keep`: the twin side changes the
per-call memos only (`Keeps sp`), and the L side writes the walks' memos only (`frA`/`frC`,
`walkA`/`walkC`), away from the pins and the core memos. Replaces `IndStubsT`'s
`hasFvarFastT_spec`, `looseBVarsBoundedFastT_spec`.
-/


open ConRon.Arena

namespace L.Ind

open L.Arena

theorem keeps_fvarB_sp (F : Nat) (e : EIdx) : Keeps sp (fvarB F e) := by
  unfold fvarB
  refine Keeps.bind (keeps_derivedE _) fun x => ?_
  by_cases hc : ((ConLeche.fvarOfData x).toNat == ConLeche.satRange) = true
  · simp only [hc, ↓reduceIte]; exact keeps_fvarRangeMemo F e
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]; exact Keeps.pure _

theorem keeps_bvarB_sp (F : Nat) (e : EIdx) : Keeps sp (bvarB F e) := by
  unfold bvarB
  refine Keeps.bind (keeps_derivedE _) fun x => ?_
  by_cases hc : ((ConLeche.bvarOfData x).toNat == ConLeche.satRange) = true
  · simp only [hc, ↓reduceIte]; exact keeps_bvarBoundMemo F e
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]; exact Keeps.pure _

/-- A run keeping `sp` changes the memos only. -/
theorem memos_only_of_sp {α : Type} {op : AM α} (h : Keeps sp op) {a : AState} :
    ∀ x a', op.run a = .ok (x, a') → ∃ X, a' = { a with memos := X } := by
  intro x a' hr
  have e := h.run hr
  obtain ⟨s, mo, c, p⟩ := a
  obtain ⟨s', mo', c', p'⟩ := a'
  simp only [sp, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl, rfl⟩ := e
  exact ⟨mo', rfl⟩

/-- **`has_fvar_fast` under `StageT`** (replaces `IndStubsT.hasFvarFastT_spec`). -/
theorem hffF_okT (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (f e : Word)
    (he : H e) :
    RelW hffF [f, e] (StageT dn vis fe) (hasFvarFast f.toNat (decI e)) (KeepPostT dn vis fe decW0B) :=
  fun m _ a r h hT =>
    StageT.lift_keep (A := frA) (C := frC) hT
      (fun r m' e' => hffF_ok dn vis fe f e he m m' a r e' hT.stage)
      (memos_only_of_sp (Keeps.bind (keeps_fvarB_sp _ _) fun _ => Keeps.pure _))
      (fun _ _ e' => hffF_frame e') (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) r _ h

/-- **`loose_bvars_bounded_fast` under `StageT`** (replaces
`IndStubsT.looseBVarsBoundedFastT_spec`). -/
theorem lbbF_okT (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (f k e : Word)
    (he : H e) :
    RelW lbbF [f, k, e] (StageT dn vis fe) (looseBVarsBoundedFast f.toNat k.toNat (decI e))
      (KeepPostT dn vis fe decW0B) :=
  fun m _ a r h hT =>
    StageT.lift_keep (A := walkA) (C := walkC) hT
      (fun r m' e' => lbbF_ok dn vis fe f k e he m m' a r e' hT.stage)
      (memos_only_of_sp (Keeps.bind (keeps_bvarB_sp _ _) fun _ => Keeps.pure _))
      (fun _ _ e' => lbbF_frame e') (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) r _ h

end L.Ind
