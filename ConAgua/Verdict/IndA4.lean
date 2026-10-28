import ConAgua.Verdict.IndA2
/-!
# `check_block_tail`'s error claim

`checkBlockTailE_claim`: the error half of `check_block_tail`'s refinement (`tail_ref`, `Tail`), in
the shape `check_block`'s claim reads (`CheckBlockTailE`), from the claims of the tail's callees
(`TailG`).
-/

open ConRon.Arena

namespace L.Ind

open L.Arena

theorem checkBlockTailE_claim {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true) (hG : TailG p) :
    CheckBlockTailE p := by
  intro hkp env₁ henv₁ hV hOpf hLC hLT hApd hCrk hIlpf hP L fs hfs hcl fsR hclR hfR s₀ a dn vis fe bO bL q bp block
    hC hq hblk hM hA hkeep hR hrb hlp hcoh hden qP hqP blockP hbP hTw henv₂ hMs hfRc fsH hclH hfH F hF er he
  exact RefE.run_err (ictlE_spec p hP F ⟨s₀.mem, Locals.init []⟩ bO bL q) hnv hG
    (tail_ref hkp henv₁ hV hOpf hLC hLT hApd hCrk hIlpf hP L hfs hcl F hclR hfR (by omega) hC hq hblk hM hA
      hkeep hR hrb hlp hcoh hden hqP hbP hTw henv₂ hMs hfRc hclH hfH) he

end L.Ind
