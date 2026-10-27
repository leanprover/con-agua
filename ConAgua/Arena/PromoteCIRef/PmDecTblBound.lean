import ConAgua.Arena.PromoteCIRef.HlistUnfold
import ConAgua.Arena.PromoteCIRef.PmDecRuleWords

/-!
# PmDecTblBound

`pmDecTbl_bound`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

theorem pmDecTbl_bound {a : Array Word} {q : Nat} {tbl : IProjTable} (h : decTbl a q = some tbl) :
    q + 12 < a.size := by
  unfold decTbl at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨e2, h2, e3, h3, e4, h4, e5, h5, e6, h6, e7, h7, e8, h8, e9, h9, -⟩ := h
  obtain ⟨o, c, -, hc1, -⟩ := hlist?_unfold h9
  obtain ⟨w, hw, -⟩ := nat?_get hc1
  exact (Array.getElem?_eq_some_iff.mp hw).1

end L.Arena
