import ConAgua.Verdict.IndA1
/-!
# `check_block`'s error claim

`checkBlockE_claim`: `CheckBlockE p` (the claim `check_ind_decl` takes as a hypothesis), the error
half of `check_block`'s refinement (`block_ref`, `Block`), from the claims of the pass's checks and
of the tail's callees (`BlockG`).
-/

open ConRon.Arena

namespace L.Ind

open L.Arena

theorem checkBlockE_claim {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true) (hG : BlockG p) :
    CheckBlockE p := by
  intro env hkp henv hV hOpf hLC hLT hApd hCrk hIlpf hLz hP fs fs2 hcl hfs hfr hcl2 hfs2 fsR fsT hclR hfR
    hclT hfT F hF m a dn vis fe bO bL p0 bs block hC hq hsrc hcx hblk hPm hma hA hkP hkt hkr hta hrb hcoh
    hden shP hshP blockP hbP fsH fsM hfRc hclH hfH hclM hfM hlpsDn e he
  exact RefE.run_err (icbE_spec p hP F ⟨m, Locals.init []⟩ vis bO bL p0) hnv hG
    (block_ref hkp henv hV hOpf hLC hLT hApd hCrk hIlpf hLz hP hcl hfs hfr hcl2 hfs2 hclR hfR hclT hfT F
      (by omega) hC hq hsrc hcx hblk hPm hma hA hkP hkt hkr hta hrb hcoh hden hshP hbP hfRc hclH hfH hclM hfM
      hlpsDn) he

end L.Ind
