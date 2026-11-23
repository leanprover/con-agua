module

public import ConAgua.Arena.Jobs

@[expose] public section

/-!
# The jobs' `check_record_sol` facts from its refinement

`CrsSpec` (`Arena/Jobs.lean`: what `record_job` takes of `check_record_sol` at a solution) from
`crs_ref` (`Arena/JustifyRef7.lean`, the model's refinement) through the model's spec
(`checkRecordSol_specE`), with the write set `closedA p cdA cdC` (decided at the checker's
program: `Checker/JobsClosed.lean`'s `checkerProg_crsW`).
-/

open ConRon.Arena

namespace L.Arena

open L.Ind

/-- **`CrsSpec` from `crs_ref`** and the program facts it takes. -/
theorem crsSpec_of {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}
    {ds : Array IDeclaration} {p : Prog} (P : CrsProg p) (hP : CdProg pins dn ds p)
    (hq : KnotStageProg p) (hap : ApdF p) (hkp : CrKeep p) (hcrf : L.Ind.CrfF p)
    (hC : CcvSims p dn) (hW : ∃ F, "check_record_sol" ∈ F ∧ closedA p cdA cdC F = true) :
    CrsSpec pins dn ds p where
  ref hFD hLD {N} hN {m} {a} {vis} {fe} {i} {J} {envS} {matesU} hi hok hR hS hF hden hPD hIM hJ hWM
      hsol hm hcm hnx := by
    have hM := crs_ref P hP hFD hLD hq hap hkp hcrf hC hN hi hok hR hS hF hden hPD hIM hJ hsol hm hcm
      hWM hnx
    have hs := checkRecordSol_specE p P.crs P.cj N ⟨m, Locals.init []⟩ i vis
    rcases c : callE p N "check_record_sol" [i, vis] m with e | ⟨r, m'⟩
    · exact fun hG => RefE.run_err hs hG.1.nv ⟨hG.1.cd, hG.2⟩ hM c
    · obtain ⟨s', rfl, -, y, a', hr, hR'⟩ := RefE.run_ok hs hM c
      exact ⟨y, a', hr, hR'⟩
  wr := hW

end L.Arena
