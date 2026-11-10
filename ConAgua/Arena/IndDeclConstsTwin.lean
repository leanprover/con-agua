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
  obtain ⟨d, hd⟩ := hd
  cases pd with
  | defnDecl v e hint =>
    simp only [ConRon.Arena.declConstants] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun; exact ⟨hok, Ext.refl _⟩
  | thmDecl v e =>
    simp only [ConRon.Arena.declConstants] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun; exact ⟨hok, Ext.refl _⟩
  | opaqueDecl v e =>
    simp only [ConRon.Arena.declConstants] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun; exact ⟨hok, Ext.refl _⟩
  | axiomDecl v =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨cv, hcv, rfl⟩ := hd
    simp only [ConRon.Arena.declConstants, declConstantsAxiom] at hrun
    obtain ⟨qs, s1, g1, r1⟩ := AM.bind_ok hrun
    obtain ⟨rfl, -⟩ := pinAt_run (x := ConLeche.quotSoundName) hok.pins rfl g1
    rcases AM.ite_ok r1 with ⟨-, k⟩ | ⟨-, k⟩
    · obtain ⟨ci, s2, g2, k2⟩ := AM.bind_ok k
      obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
      obtain ⟨hr, -⟩ := quotAt_run hok.state hok.readOK hcv g2
      exact ⟨hr.checkOK hok, hr.ext⟩
    · obtain ⟨sa, s2, g2, r2⟩ := AM.bind_ok k
      obtain ⟨rfl, -⟩ := pinAt_run (x := ConLeche.sorryAxName) hok.pins rfl g2
      rcases AM.ite_ok r2 with ⟨-, k3⟩ | ⟨-, k3⟩
      · obtain ⟨rfl, rfl⟩ := AM.pure_ok k3; exact ⟨hok, Ext.refl _⟩
      · obtain ⟨rfl, rfl⟩ := AM.pure_ok k3; exact ⟨hok, Ext.refl _⟩
  | quotDecl k v =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨cv, hcv, rfl⟩ := hd
    simp only [ConRon.Arena.declConstants] at hrun
    obtain ⟨ci, s2, g2, k2⟩ := AM.bind_ok hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
    obtain ⟨hr, -⟩ := quotAt_run hok.state hok.readOK hcv g2
    exact ⟨hr.checkOK hok, hr.ext⟩
  | indDecl block nP =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨b, hb, rfl⟩ := hd
    simp only [ConRon.Arena.declConstants] at hrun
    obtain ⟨r, s1, g1, k1⟩ := AM.bind_ok hrun
    obtain ⟨hst1, hx1, hp1, hc1, -, -, rfl⟩ := basisNameHit_run hok.state hb g1
    have hok1 := hok.mono hst1 hx1 hc1 hp1
    have hb1 := denoteCIList_mono hx1 _ _ hb
    cases hk : ConLeche.basisNameHit b with
    | some kind =>
      rw [hk] at k1
      obtain ⟨hr, -⟩ := BasisKind.atBlock_run hok1.state hok1.readOK hb1 k1
      exact ⟨hr.checkOK hok1, hx1.trans hr.ext⟩
    | none =>
      rw [hk] at k1
      obtain ⟨q, s2, g2, k2⟩ := AM.bind_ok k1
      obtain ⟨hp2, -, hq⟩ := blockShape?_installS hok1 hb1 g2
      have hok2 := checkOK_of_pstep hok1 hp2
      cases q with
      | none =>
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨hok2, hx1.trans hp2.ext⟩
      | some p =>
        simp only [ROp] at hq
        obtain ⟨pP, -, hdp⟩ := hq
        obtain ⟨hp3, -, -⟩ := blockConstants_run hok2.state hok2.pins hdp k2
        exact ⟨checkOK_of_pstep hok2 hp3, (hx1.trans hp2.ext).trans hp3.ext⟩

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
    obtain ⟨r, s1, g1, k1⟩ := AM.bind_ok hrun
    obtain ⟨hst1, hx1, hp1, hc1, -, -, rfl⟩ := basisNameHit_run hok.state hb g1
    have hok1 := hok.mono hst1 hx1 hc1 hp1
    have hb1 := denoteCIList_mono hx1 _ _ hb
    cases hk : ConLeche.basisNameHit b with
    | some kind =>
      rw [hk] at k1
      obtain ⟨rfl, rfl⟩ := AM.pure_ok k1
      exact ⟨hok1, hx1⟩
    | none =>
      rw [hk] at k1
      obtain ⟨q, s2, g2, k2⟩ := AM.bind_ok k1
      obtain ⟨hp2, -, hq⟩ := blockShape?_installS hok1 hb1 g2
      have hok2 := checkOK_of_pstep hok1 hp2
      cases q with
      | none =>
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨hok2, hx1.trans hp2.ext⟩
      | some p =>
        simp only [ROp] at hq
        obtain ⟨pP, -, hdp⟩ := hq
        obtain ⟨hms, -⟩ := dShape_inv hdp
        obtain ⟨hp3, -, -, -⟩ := blockTables_run p.members pP.members hok2.state hdp hms k2
        exact ⟨checkOK_of_pstep hok2 hp3, (hx1.trans hp2.ext).trans hp3.ext⟩
  | _ =>
    simp only [ConRon.Arena.declTables] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun; exact ⟨hok, Ext.refl _⟩

end L.Ind
