import ConAgua.Verdict.DefEqQuickE

/-!
# `defeq_binders`' error claim

`db_ref`'s error half (`DefEqMidPeel.lean`), in the shape `quick_forall` reads.
-/

open ConRon.Arena

namespace L.Arena

/-- **`defeq_binders`' error claim** (`DefeqBindersE`, `db_ref`'s error half). -/
theorem defeqBinders_refinesE (p : Prog) (hp : PeelProg p) (hil : InstListOK p)
    (hnv : closedNV p L.Checker.nvFns = true) : DefeqBindersE p :=
  fun n hk hkE F hF hn s₀ a₀ dn vis fe M eb mode d ty1 body1 ty2 body2 hs h1 hb1 h2 hb2 hd =>
    RefE.coreSpecE (dbE_spec p hp.binders (n + 1) s₀ mode vis d ty1 body1 ty2 body2) hnv ⟨hkE, hnv⟩
      (db_ref p hp hil n hk F hF hn s₀ a₀ dn vis fe M eb mode d ty1 body1 ty2 body2 hs h1 hb1 h2 hb2 hd)

end L.Arena
