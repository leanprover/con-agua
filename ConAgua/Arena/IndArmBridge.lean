import ConAgua.Arena.IndInstallSpec36
import ConRon.Bridge.Promote.Exact

/-!
# From the fold's invariants to `check_ind_decl`'s inputs (lane `indproofs4`)

The loop gives the inductive arm `FoldOK` (`IndArmSpec`), whose `IFEnvCoh` makes the environment's
index the list's own (`mkIFEnvGo`). Here: what `cidW_ok` takes of the environment, from it.
-/

open ConRon.Arena

namespace L.Ind

/-- Every entry of `mkIFEnvGo cs`'s index is below the list's length. -/
theorem mkIFEnvGo_lt : ∀ (cs : List IConstantInfo) (n : NIdx) (e : Nat × IConstantInfo),
    (mkIFEnvGo cs).2[n]? = some e → e.1 < cs.length
  | [], n, e, h => by simp [mkIFEnvGo] at h
  | ci :: cs, n, e, h => by
    simp only [mkIFEnvGo, Std.HashMap.getElem?_insert] at h
    split at h
    · cases h
      simp only [ConRon.Bridge.mkIFEnvGo_fst', List.length_cons]; omega
    · have := mkIFEnvGo_lt cs n e h
      simp only [List.length_cons]; omega

/-- **A coherent environment's entries are all visible** (`AllVis`). -/
theorem AllVis.of_coh {fe : IFEnv} (h : ConRon.Bridge.IFEnvCoh fe) : AllVis fe := by
  intro n e he
  rw [h.2 n] at he
  rw [h.1]
  exact mkIFEnvGo_lt _ _ _ he

end L.Ind
