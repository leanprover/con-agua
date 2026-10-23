import ConAgua.Arena.IndRealOpf3
import ConAgua.Arena.IndT.Lift

/-!
# `open_pis_at_fvars_f` under `StageC` (lane `indproofs4`, helper `opf`)

`IndRealOpf3.lean`'s `opfF_ok` lifted to `StageC` by con-ron's `openPisAtFvarsF_run` (the twin's
run from `StateOK` and the input's denotation is a `PStep` whose result denotes con-leche's
`openPisAtFvars`): `StageC.of_pstep` with the `AbsOK` after.
-/

open ConRon.Arena

namespace L.Ind

open L.Arena

/-- **`open_pis_at_fvars_f` refines `openPisAtFvarsF` under `StageC`**, the result denoting
con-leche's `openPisAtFvars`. -/
theorem opfF_okC (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (k e i : Word) (he : H e) (hP : ConLeche.Expr) :
    RelW opfF [k, e, i]
      (fun m a => StageC dn vis fe env m a ∧ AbsOK m ∧ denoteE a.store (decI e) = some hP)
      (openPisAtFvarsF k.toNat (decI e) i.toNat)
      (fun m m' a r x => StageC dn vis fe env m' a ∧ IWGrow m m' ∧ decOLE m' r x ∧ AbsOK m' ∧
        ConRon.Bridge.Inductives.denoteOpen a.store x = some (ConLeche.openPisAtFvars k.toNat hP i.toNat)) := by
  intro m m' a r h ⟨hC, hA, hd⟩
  obtain ⟨x, a', hrun, ⟨hS', hg, hdec⟩, hA'⟩ := opfF_ok dn vis fe k e i he m m' a r h ⟨hC.stage, hA⟩
  obtain ⟨q, ho⟩ := ConRon.Bridge.Inductives.openPisAtFvarsF_run hC.check.state hd hrun
  exact ⟨x, a', hrun, hC.of_pstep hS' hA' q, hg, hdec, hA', ho⟩

end L.Ind
