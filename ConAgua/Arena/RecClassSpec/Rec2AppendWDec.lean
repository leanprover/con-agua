module

import ConAgua.Arena.RecClassSpec.ClassGenMajorCi
import ConAgua.Arena.IndPosSpec.RootHoles
public import ConAgua.Arena.IndCopy2
public import ConAgua.Arena.IndDecStab

@[expose] public section

/-!
# Rec2AppendWDec

`rec2AppendW_norm`, `rec2AppendW_dec`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem rec2AppendW_norm (n : Nat) (m : Mem) (o1 o2 l2 : Word) :
    appendW n m o1 0 o2 l2 = appendW n m 0 0 o2 l2 := by
  have hc : ∀ k m1 q (s : Word), copyW k m1 q s 0 = copyW k m1 q 0 0 := by
    intro k; cases k <;> simp [copyW]
  simp only [appendW, hc]

/-- `sl_append` of a slice decoded below the tops (possibly empty, at any offset) and a slice
below the top. -/
theorem rec2AppendW_dec {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {o1 l1 o2 l2 : Word} {r : List Word} {xs ys : List EIdx}
    (h : appendW n m o1 l1 o2 l2 = some (r, m')) (hS : StageR vis fe m a)
    (h1 : DecB (fun m => (decHL m o1.toNat l1.toNat : Option (List EIdx))) m xs)
    (h2 : decHL m o2.toNat l2.toNat = some ys) (hb2 : o2.toNat + l2.toNat ≤ iwTop m) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some (xs ++ ys) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  sorry

end L.Ind

end
