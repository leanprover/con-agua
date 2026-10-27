import ConAgua.Arena.IndPosSpec.NestSeedOf
import ConAgua.Arena.IndPosSpec.NestSeeds

/-!
# DecNLAt

`decNL_at`, `SdRes`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The seeds' slice -/

theorem decNL_at {m : Mem} {o l : Nat} {xs : List Nat} (h : decNL m o l = some xs) (j : Nat) (hj : j < l) :
    iwN m (o + j) = some (xs[j]'(by rw [decNL_length m h]; exact hj)) := by
  have := mapM_opt_get (fun j => iwN m (o + j)) (List.range l) xs h j (by simpa using hj)
  simpa using this

/-- What `class_seeds` returns: `nestSeeds`' input slice. -/
def SdRes (m : Mem) (o l : Word) (seeds : List (NestKey × Nat)) : Prop :=
  o.toNat + l.toNat ≤ iwTop m ∧ l.toNat = seeds.length ∧
    (∃ ps, decNL m o.toNat l.toNat = some ps) ∧ SeedsAt m o.toNat seeds

end L.Ind
