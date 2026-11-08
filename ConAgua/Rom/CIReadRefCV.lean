module

import ConAgua.Rom.CIReadRefNames
import ConAgua.Rom.CIReadRefW
public import ConAgua.Rom.CIReadRefBase
public import ConAgua.Rom.CIReadSpec

@[expose] public section

/-!
# The ROM constant readers: constant values (helper `decls4-rom`)

`rci_cv(q, p)` refines `Frontend.internCV` (name, level parameters, type at the current memo),
the 4-word record at `p` decoding to the twin's value (`decCV`).
-/


open ConRon.Arena ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order

namespace L.Rom

open L.Arena L.Ind

/-! ## One `EREC` word written -/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem er_set_ne (m : Mem) (j w : Word) (i : Nat) (hi : i ≠ j.toNat) :
    (erA (m.set64 EREC j w))[i]? = erA m i := by
  simp only [erA]
  rw [Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  simp [Ne.symm hi]
-/

/-- Everything a reader carries, across one `EREC` word written above the entry's top. -/
theorem setER_facts {m₀ m : Mem} {a₀ a : AState} {T : Nat} {seen : List ConLeche.Expr} {memo : EMemo}
    (hI : RInv m₀ a₀ T m a) (hM : MemoR m seen memo) (j w : Word) (hj : erTop m₀ ≤ j.toNat) :
    RInv m₀ a₀ T (m.set64 EREC j w) a ∧ MemoR (m.set64 EREC j w) seen memo ∧
      stkTop (m.set64 EREC j w) = stkTop m ∧ erTop (m.set64 EREC j w) = erTop m ∧
      (m.set64 EREC j w).arr64 IW = m.arr64 IW := by
  have hf := MemFrame.set64 m EREC (by decide) j w
  have hC : (m.set64 EREC j w).arr64 CTL = m.arr64 CTL := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  exact ⟨hI.setER j w hj, hM.frameG hf (by decide) (by simp), by simp only [stkTop, hC],
    by simp only [erTop, hC], Mem.arr64_set64_ne _ _ _ _ _ (by decide)⟩

/-- A decoding survives a word written outside its words. -/
theorem Holds.setER {α : Type} {SE SI : Nat → Prop} {f : Mem → Option α} {x : α} {m : Mem}
    (h : Holds SE SI f m x) (j w : Word) (hj : ∀ i, SE i → i ≠ j.toNat) :
    Holds SE SI f (m.set64 EREC j w) x :=
  h.keep (fun i hi => er_set_ne m j w i (hj i hi))
    (fun i _ => by simp only [iwA]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)])

/-- `decCV` from its three parts. -/
theorem holds_decCV {m : Mem} {q : Nat} {SL SI : Nat → Prop} {n t : Word} {l : List NIdx}
    (hn : erA m q = some n) (hnl : n.toNat < 2 ^ 32)
    (hl : Holds SL SI (fun m => (hlist? (erA m) (q + 1) : Option (List NIdx))) m l)
    (ht : erA m (q + 3) = some t) (htl : t.toNat < 2 ^ 32) :
    Holds (fun i => i = q ∨ SL i ∨ i = q + 3) SI (fun m => decCV (erA m) q) m ⟨decI n, l, decI t⟩ := by
  intro m' h1 h2
  have e1 := (h1 q (.inl rfl)).trans hn
  have e3 := (h1 (q + 3) (.inr (.inr rfl))).trans ht
  have e2 := hl m' (fun i hi => h1 i (.inr (.inl hi))) h2
  simp [decCV, hd?, e1, e3, e2, hnl, htl]

/-- A constant value fits its encoding. -/
def cvFits (cv : ConLeche.ConstantVal) : Bool :=
  nameFits cv.name && cv.levelParams.all nameFits && exprFits cv.type

section cv
variable {rom : List UInt8} {p : Prog} (hL : RomCIProg rom p) (hr : RomOK rom)
include hL hr

/-- **`rci_cv` refines `Frontend.internCV`** at the memo `memo` (`seen`), into the 4-word record
at `pp` (allocated above the entry's top). -/
@[refines_part ConRon.Arena.Frontend.internCV "values whose type fits the ROM encoding"]
theorem cv_rel {m₀ : Mem} {a₀ : AState} {T : Nat} (seen : List ConLeche.Expr) (memo : EMemo)
    (cv : ConLeche.ConstantVal) (hfit : cvFits cv = true) (k : Nat) (m : Mem) (a : AState)
    (q pp : Word) (rest : List UInt8) (r : List Word) (m' : Mem) (hI : RInv m₀ a₀ T m a)
    (hM : MemoR m seen memo) (hst : stkTop m = 0) (hd : rom.drop q.toNat = (encCV seen cv).1 ++ rest)
    (hp0 : erTop m₀ ≤ pp.toNat) (hp4 : pp.toNat + 4 ≤ erTop m)
    (hc : callW p (k + 1) "rci_cv" [q, pp] m = some (r, m')) :
    ∃ (memo' : EMemo) (icv : IConstantVal) (a' : AState),
      (Frontend.internCV memo cv).run a = .ok ((memo', icv), a') ∧
      RInv m₀ a₀ T m' a' ∧ MemoR m' (encCV seen cv).2 memo' ∧ stkTop m' = 0 ∧
      (r.headD 0).toNat = q.toNat + (encCV seen cv).1.length ∧
      EKeep (fun i => pp.toNat ≤ i ∧ i < pp.toNat + 4) m m' ∧ erTop m ≤ erTop m' ∧
      m'.arr64 IW = m.arr64 IW ∧
      Holds (fun i => (pp.toNat ≤ i ∧ i < pp.toNat + 4) ∨ (erTop m ≤ i ∧ i < erTop m'))
        (fun _ => False) (fun m => decCV (erA m) pp.toNat) m' icv := by
  sorry

end cv

end L.Rom
