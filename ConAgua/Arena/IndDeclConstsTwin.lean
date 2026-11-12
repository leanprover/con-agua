module

public import ConRon.Bridge.Checker.Install
import ConRon.Bridge.Checker.Names

@[expose] public section

/-!
# The twin's `declConstants`/`declTables` keep `CheckOK` (lane `ronsync2`, stage 3)

Con-ron's `constsSpec`/`tablesSpec` (`ConRon/Bridge/Checker/Install.lean`) at the driver's
environment (`DriverOK`), restated at any `CheckOK false env fe` (the stream index's builder runs
them at the stage's own environment): the invariant after the run and the store's growth. The
proofs are theirs, the denotations dropped.
-/

open ConLeche ConRon.Arena ConRon.Bridge ConRon.Bridge.Inductives

namespace L.Ind

theorem checkOK_of_pstep {eager : Bool} {env : Env} {fe : IFEnv} {s s' : AState}
    (h : CheckOK eager env fe s) (hp : PStep s s') : CheckOK eager env fe s' :=
  ⟨hp.ok, h.caches.monoF hp.ext hp.cframe, h.pins.mono hp.ext hp.pins, h.ienv.mono hp.ext⟩

/-- **The twin's `declConstants` keeps `CheckOK`** and grows the store. -/
theorem declConstants_chk {env : Env} {fe : IFEnv} {s s' : AState} {pd : IDeclaration}
    {L : List IConstantInfo} (hok : CheckOK false env fe s)
    (hd : ∃ d, Frontend.denoteDecl s.store pd = some d)
    (hrun : ConRon.Arena.declConstants pd s = .ok (L, s')) :
    CheckOK false env fe s' ∧ Ext s.store s'.store := by
  sorry

/-- **The twin's `declTables` keeps `CheckOK`** and grows the store. -/
theorem declTables_chk {env : Env} {fe : IFEnv} {s s' : AState} {pd : IDeclaration}
    {Q : List IProjTable} (hok : CheckOK false env fe s)
    (hd : ∃ d, Frontend.denoteDecl s.store pd = some d)
    (hrun : ConRon.Arena.declTables pd s = .ok (Q, s')) :
    CheckOK false env fe s' ∧ Ext s.store s'.store := by
  sorry

end L.Ind
