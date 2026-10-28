import ConAgua.Verdict.DefEqQuickE

/-!
# `defeq_lams`' error claim

`defeqLams_ref`'s error half (`DefEqMidLams.lean`), in the shape `quick_lam` reads.
-/

open ConRon.Arena

namespace L.Arena

/-- **`defeq_lams`' error claim** (`DefeqLamsE`, `defeqLams_ref`'s error half). -/
theorem defeqLams_refinesE (p : Prog) (hp : LamsProg p) (hi : Inst1OK p)
    (hnv : closedNV p L.Checker.nvFns = true) : DefeqLamsE p :=
  fun n hk hkE F hF hn s₀ a₀ dn vis fe M eb mode d ty₁ body₁ ty₂ body₂ hs h1 hb1 h2 hb2 hd =>
    RefE.coreSpecE (defeqLams_specE p hp.lams (n + 1) s₀ mode vis d ty₁ body₁ ty₂ body₂) trivial
      ⟨hkE, hnv⟩
      (defeqLams_ref p hp hi n hk F hF hn s₀ a₀ dn vis fe M eb mode d ty₁ body₁ ty₂ body₂ hs h1 hb1
        h2 hb2 hd)

end L.Arena
