import ConAgua.Arena.IndPosSpec.FgW
import ConAgua.Arena.RecCheckSpec.TpnB

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
    (h : consW n m x o l = some (r, m')) (hS : StageR dn vis fe m a) (hxs : PSlR f xs o l m)
    (hy : DecB (fun m => f m x.toNat) m y) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ PSlR f (y :: xs) (r.headD 0) (r.tail.headD 0) m' ∧
      MFr [] [] m m' := by
  obtain ⟨ps, -, hps, hmap⟩ := sumDecNL_of_decB hxs.1
  obtain ⟨hS', hg, hd', ht'⟩ := consW_stageN h hS hxs.2 hps
  exact ⟨hS', hg, ⟨sumDecB_cons hf hmap hd' (Nat.le_of_eq ht') hg (hy.grow (hf _) hg), Nat.le_of_eq ht'⟩,
    consW_mfr h⟩

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
    soaW n m reco recl k = some (r, m') → StageR dn vis fe m a → PSlR decRS recs reco recl m →
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      PSlR decRS (recs.filter fun rc => decide (rc.tgt < k.toNat)) (r.headD 0) (r.tail.headD 0) m' ∧
      PSlR decRS (recs.filter fun rc => !decide (rc.tgt < k.toNat)) (r.tail.tail.headD 0)
        (r.tail.tail.tail.headD 0) m' := by
  induction n with
  | zero => intro m m' a reco recl k recs r h; simp [soaW] at h
  | succ n ih =>
    intro m m' a reco recl k recs r h hS hrs
    by_cases hl : recl = 0
    · rw [soaW.arm1 n m reco recl k hl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hl; rw [partsPSl_nil hrs]
      exact ⟨hS, IWGrow.refl _, PSlR.nil _ _, PSlR.nil _ _⟩
    rw [soaW.arm2 n m reco recl k hl] at h
    obtain ⟨pc, rs0, rs', rfl, hw, hpb, hrs0, hrs'⟩ := partsPSl_cons hrs hl
    rcases h1 : soaW n m (reco + 1) (recl - 1) k with _ | ⟨r1, m1⟩ <;> rw [h1] at h <;>
      try (simp only [soaW.k_block_rec_split_own_aux, reduceCtorEq] at h; done)
    obtain ⟨hS1, hg1, hown, haux⟩ := ih m m1 a (reco + 1) (recl - 1) k rs' r1 h1 hS hrs'
    -- the recursor's pointer and its target, as the model reads them in `m1`
    have hrlt : reco.toNat < iwTop m := by
      have := hrs.2
      have : recl.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e))
      omega
    have hw1 : rdW (m1.arr64 IW) reco = UInt64.ofNat pc := by rw [partsRdIW_grow hg1 hrlt, hw]
    obtain ⟨-, -, -, htg, -⟩ := decRS_some (show decRS (truncM m) pc = some rs0 from hrs0)
    obtain ⟨htw, htb, htlt⟩ := partsIwRd htg
      (show (UInt64.ofNat pc + 3).toNat = pc + 3 by
        rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' hpb]; simp
        have := partsIwLt htg; have := (rdW (m.arr64 CTL) 200).toNat_lt; simp only [iwTop] at *; omega)
    have hw3 : rdW (m1.arr64 IW) (rdW (m1.arr64 IW) reco + 3) = UInt64.ofNat rs0.tgt := by
      rw [hw1, partsRdIW_grow hg1 (by
        rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' hpb]; simp
        have := (rdW (m.arr64 CTL) 200).toNat_lt; simp only [iwTop] at *; omega), htw]
    have hlt : (UInt64.ofNat rs0.tgt < k) = (rs0.tgt < k.toNat) := by
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' htb]
    have hy : DecB (fun m => decRS m (UInt64.ofNat pc : Word).toNat) m1 rs0 := by
      rw [UInt64.toNat_ofNat_of_lt' hpb]; exact hrs0.grow (decRS_mono _) hg1
    by_cases hc : rs0.tgt < k.toNat
    · rw [soaW.k_block_rec_split_own_aux.arm1 n reco k r1 m1 (by rw [hw3, hlt]; exact hc), hw1] at h
      rcases h2 : consW n m1 (UInt64.ofNat pc) (r1.headD 0) (r1.tail.headD 0) with _ | ⟨r2, m2⟩ <;> simp only [h2, soaW.k_sl_cons, reduceCtorEq] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨hS2, hg2, hd2, -⟩ := consW_pslr (fun q => decRS_mono q) h2 hS1 hown hy
      refine ⟨hS2, hg1.trans hg2, ?_, ?_⟩
      · simp only [List.filter_cons, decide_eq_true hc, ite_true, List.headD_cons, List.tail_cons]
        exact hd2
      · simp only [List.filter_cons, decide_eq_true hc, Bool.not_true, Bool.false_eq_true, ite_false,
          List.headD_cons, List.tail_cons]
        exact haux.grow (fun q => decRS_mono q) hg2
    · rw [soaW.k_block_rec_split_own_aux.arm2 n reco k r1 m1 (by rw [hw3, hlt]; exact hc), hw1] at h
      rcases h2 : consW n m1 (UInt64.ofNat pc) (r1.tail.tail.headD 0) (r1.tail.tail.tail.headD 0) with _ | ⟨r2, m2⟩ <;> simp only [h2, soaW.k_sl_cons_2, reduceCtorEq] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨hS2, hg2, hd2, -⟩ := consW_pslr (fun q => decRS_mono q) h2 hS1 haux hy
      refine ⟨hS2, hg1.trans hg2, ?_, ?_⟩
      · simp only [List.filter_cons, decide_eq_false hc, Bool.false_eq_true, ite_false, List.headD_cons,
          List.tail_cons]
        exact hown.grow (fun q => decRS_mono q) hg2
      · simp only [List.filter_cons, decide_eq_false hc, Bool.not_false, ite_true, List.headD_cons,
          List.tail_cons]
        exact hd2

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
    (h : soaW (n + 1) m reco recl k = some (r, m')) (hS : StageR dn vis fe m a)
    (hrs : PSlR0 decRS recs reco recl m) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      PSlR decRS (recs.filter fun rc => decide (rc.tgt < k.toNat)) (r.headD 0) (r.tail.headD 0) m' ∧
      PSlR decRS (recs.filter fun rc => !decide (rc.tgt < k.toNat)) (r.tail.tail.headD 0)
        (r.tail.tail.tail.headD 0) m' := by
  by_cases hl : recl = 0
  · rw [soaW.arm1 n m reco recl k hl] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rw [hrs.nil hl]
    exact ⟨hS, IWGrow.refl _, PSlR.nil _ _, PSlR.nil _ _⟩
  · exact soaW_ok (n + 1) m m' a reco recl k recs r h hS (hrs.pslr hl)

end L.Ind

end

end
