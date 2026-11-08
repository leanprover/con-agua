module

import ConAgua.Arena.IndPosSpec.FgW
public import ConAgua.Arena.RecCheckSpec.TpnB
import ConAgua.Arena.IndPartsSpec.PartsPSlCons
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import ConAgua.Arena.RecClassSpec.Classes
import Std.Tactic.BVDecide.Normalize.Bool

@[expose] public section

/-!
# SoaW

`sumDecNL_of_decB`, `sumDecB_cons`, `consW_pslr`, `soaW_ok`, `soaW_ok0`.
-/

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- A decoded pointer slice's numbers decode in the memory itself. -/
theorem sumDecNL_of_decB {α : Type} {f : Mem → Nat → Option α} {m : Mem} {o l : Nat} {ys : List α}
    (h : DecB (fun m => decPL m (f m) o l) m ys) :
    ∃ ps, decNL (truncM m) o l = some ps ∧ decNL m o l = some ps ∧ ps.mapM (f (truncM m)) = some ys := by
  have h' : decPL (truncM m) (f (truncM m)) o l = some ys := h
  rw [decPL_eq_bind] at h'
  cases hps : decNL (truncM m) o l with
  | none => rw [hps] at h'; cases h'
  | some ps =>
    rw [hps] at h'
    exact ⟨ps, rfl, (OMono.decNL o l).mono _ _ _ (IWGrow.truncExt (IWGrow.refl m)) hps, by simpa using h'⟩

/-- **Consing onto a decoded pointer slice** (`sl_cons`'s result, above the old top). -/
theorem sumDecB_cons {α : Type} {f : Mem → Nat → Option α} (hf : ∀ q, OMono (fun m => f m q))
    {m m' : Mem} {o' l' : Nat} {x : Nat} {ps : List Nat} {y : α} {ys : List α}
    (hps : ps.mapM (f (truncM m)) = some ys) (hd' : decNL m' o' l' = some (x :: ps))
    (hb' : o' + l' ≤ iwTop m') (hg : IWGrow m m') (hy : DecB (fun m => f m x) m' y) :
    DecB (fun m => decPL m (f m) o' l') m' (y :: ys) := by
  have e2 : DecB (fun m => ps.mapM (f m)) m' ys := DecB.grow (OMono.mapM hf ps) hg hps
  show decPL (truncM m') (f (truncM m')) o' l' = some (y :: ys)
  rw [decPL_eq_bind, show decNL (truncM m') o' l' = some (x :: ps) from decNL_decB hd' hb']
  simp only [Option.bind_some, List.mapM_cons]
  rw [show f (truncM m') x = some y from hy, show ps.mapM (f (truncM m')) = some ys from e2]
  rfl

end L.Ind

end

end

section

noncomputable section

/-!
# `RecCheck`: `targetMajorNfs` (lane `indproofs3`, helper `rec`)

The walk's recorded constructor normal forms of a class. L (D18): the loop became the twin's list
recursion (the tail first, so the class-match calls fire from the last entry to the first), each
kept entry `sl_cons`ed onto the kept tail (a copy, so the result is a pointer slice decoded below
the tops). Callees: `ctors_have_name` (helper `recb`'s `chnW`), `target_class_match`
(`RecCheckSpec/TcmLook`), `sl_cons`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- A pointer consed onto a pointer slice decoded below the tops (`sl_cons`). -/
theorem consW_pslr {α : Type} {f : Mem → Nat → Option α} (hf : ∀ q, OMono (fun m => f m q))
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {x o l : Word} {r : List Word} {xs : List α} {y : α}
    (h : consW n m x o l = some (r, m')) (hS : StageR vis fe m a) (hxs : PSlR f xs o l m)
    (hy : DecB (fun m => f m x.toNat) m y) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ PSlR f (y :: xs) (r.headD 0) (r.tail.headD 0) m' ∧
      MFr [] [] m m' := by
  sorry

end L.Ind

end
end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **`block_rec_split_own_aux`'s model is the twin's two `filter`s** (as slices of `RecShape`
pointers decoded below the tops). -/
theorem soaW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (reco recl k : Word) (recs : List RecShape) (r : List Word),
    soaW n m reco recl k = some (r, m') → StageR vis fe m a → PSlR decRS recs reco recl m →
    StageR vis fe m' a ∧ IWGrow m m' ∧
      PSlR decRS (recs.filter fun rc => decide (rc.tgt < k.toNat)) (r.headD 0) (r.tail.headD 0) m' ∧
      PSlR decRS (recs.filter fun rc => !decide (rc.tgt < k.toNat)) (r.tail.tail.headD 0)
        (r.tail.tail.tail.headD 0) m' := by
  sorry

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The relational lemma -/

/-- `block_rec_split_own_aux` at a slice below the top unless empty. -/
theorem soaW_ok0 {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat)
    {m m' : Mem} {a : AState} {reco recl k : Word} {recs : List RecShape} {r : List Word}
    (h : soaW (n + 1) m reco recl k = some (r, m')) (hS : StageR vis fe m a)
    (hrs : PSlR0 decRS recs reco recl m) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      PSlR decRS (recs.filter fun rc => decide (rc.tgt < k.toNat)) (r.headD 0) (r.tail.headD 0) m' ∧
      PSlR decRS (recs.filter fun rc => !decide (rc.tgt < k.toNat)) (r.tail.tail.headD 0)
        (r.tail.tail.tail.headD 0) m' := by
  sorry

end L.Ind

end

end
