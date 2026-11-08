module

public import ConAgua.Arena.DeclCvg
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.Arena.DeclCvg
import ConAgua.Arena.DerRel
import ConAgua.Arena.IndPartsSpec.MemberNames
import ConAgua.Arena.ScratchRefine

@[expose] public section

/-!
# FlushStage

`flush_stage`, `cvLpsA_stage` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- `flush_caches()` under the stage relation. -/
theorem flush_stage {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (h : StageR vis fe m a) (hok : FlushOK m) :
    StageR vis fe (flushMem m) { a with caches := Caches.empty } ∧ IWGrow m (flushMem m) := by
  sorry

/-- `cv_lps(q)` under the stage relation: the level parameters, a slice below the top. -/
theorem cvLpsA_stage {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {q : Word} {r : List Word} {cv : IConstantVal}
    (h : L.Arena.cvLpsW n m q = some (r, m')) (hS : StageR vis fe m a)
    (hq : decCV (erA m) q.toNat = some cv) (hqb : q.toNat + 3 < 2 ^ 64) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some cv.levelParams ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  sorry

end L.Ind

end
