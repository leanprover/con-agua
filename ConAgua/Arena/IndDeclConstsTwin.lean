module

public import ConRon.Bridge.Checker.Install
import ConRon.Bridge.Checker.Names
import ConRon.Bridge.Checker.Basis
import ConRon.Bridge.Inductives.Install

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
  obtain ⟨d, hd⟩ := hd
  cases pd with
  | indDecl block nP =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨b, hb, rfl⟩ := hd
    simp only [ConRon.Arena.declTables] at hrun
    obtain ⟨q, s2, g2, k2⟩ := AM.bind_ok hrun
    obtain ⟨hp2, -, hq⟩ := readBlock_installS hok hb g2
    have hok2 := checkOK_of_pstep hok hp2
    cases q with
    | error e =>
      obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
      exact ⟨hok2, hp2.ext⟩
    | ok p =>
      simp only [ROp, Except.toOption] at hq
      obtain ⟨pP, -, hdp⟩ := hq
      obtain ⟨hms, -⟩ := dShape_inv hdp
      obtain ⟨o, s3, k3, k4⟩ := AM.bind_ok k2
      obtain ⟨hp3, -, -⟩ := blockTables_run p.members pP.members hok2.state hdp hms k3
      cases o with
      | none =>
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k4
        exact ⟨checkOK_of_pstep hok2 hp3, hp2.ext.trans hp3.ext⟩
      | some q =>
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k4
        exact ⟨checkOK_of_pstep hok2 hp3, hp2.ext.trans hp3.ext⟩
  | _ =>
    simp only [ConRon.Arena.declTables] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun; exact ⟨hok, Ext.refl _⟩

end L.Ind
