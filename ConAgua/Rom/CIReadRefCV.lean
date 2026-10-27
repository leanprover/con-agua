import ConAgua.Rom.CIReadRefNames
import ConAgua.Census.Attr

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

theorem er_set_ne (m : Mem) (j w : Word) (i : Nat) (hi : i ≠ j.toNat) :
    (erA (m.set64 EREC j w))[i]? = (erA m)[i]? := by
  simp only [erA]
  rw [Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  simp [Ne.symm hi]

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
    (hn : (erA m)[q]? = some n) (hnl : n.toNat < 2 ^ 32)
    (hl : Holds SL SI (fun m => (hlist? (erA m) (q + 1) : Option (List NIdx))) m l)
    (ht : (erA m)[q + 3]? = some t) (htl : t.toNat < 2 ^ 32) :
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
  simp only [cvFits, Bool.and_eq_true] at hfit
  obtain ⟨⟨hfn, hfl⟩, hfe⟩ := hfit
  have hw := callW_model (M := fun mq => cvW p k mq q pp) (cv_specW rom p hL k · q pp) hc
  unfold cvW at hw
  -- the name
  obtain ⟨r1, m1, h1, hw⟩ := ntBW_inv hw
  have hd0 : rom.drop q.toNat = encName cv.name ++
      (encNameL cv.levelParams ++ ((encExprM seen cv.type).1 ++ rest)) := by
    rw [hd]; simp [encCV, List.append_assoc]
  obtain ⟨a1, hrun1, hA1, hk1, hlt1, hq1, hf1, hmo1⟩ := nameCall hL hr cv.name hfn hI.arena hI.mode hd0 h1
  obtain ⟨hI1, hE1, hIW1, ht1, -⟩ := hI.expr hA1 hmo1 (hf1.mono (fun b hb => by simp [ExprA, RomA, hb])
    (fun x hx => by simp [ExprC, RomC, hx])) hk1
  have hM1 := hM.frameG hf1 (by decide) (by decide)
  have hs1 : stkTop m1 = stkTop m := hf1.2.1 131 (by decide)
  have hlt := hI.er_lt
  have hgo := hI.grow.2.1
  -- the name word
  obtain ⟨hI2, hM2, hs2, ht2, hIW2⟩ := setER_facts hI1 hM1 pp (r1.headD 0) hp0
  have hsz1 : erTop m1 ≤ (m1.arr64 EREC).size := hI1.ok.2.1
  -- the level parameters
  cases k with
  | zero => rw [callW_zero] at hw; simp at hw
  | succ k =>
  obtain ⟨r2, m3, h2, hw⟩ := ntBW_inv hw
  have hp1 : (pp + 1).toNat = pp.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hp3 : (pp + 3).toNat = pp.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  have hdl : rom.drop (r1.tail.headD 0).toNat =
      encNameL cv.levelParams ++ ((encExprM seen cv.type).1 ++ rest) :=
    drop_shift rom hr q (encName cv.name) _ _ (by rw [hd0, List.append_assoc]) _ hq1
  obtain ⟨ws, a3, hrun3, hwlt, hI3, hM3, hs3, hq3, hek3, ht3, hiw3, hH3⟩ :=
    nameSl_rel hL hr seen memo cv.levelParams hfl k _ a1 _ (pp + 1) _ _ m3 hI2 hM2 hdl
      (by omega) (by rw [ht2, ht1]; omega) h2
  -- the type
  obtain ⟨r4, m4, h4, hw⟩ := ntBW_inv hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  have hdt : rom.drop (r2.headD 0).toNat = (encExprM seen cv.type).1 ++ rest :=
    drop_shift rom hr _ (encNameL cv.levelParams) _ _ (by rw [hdl, List.append_assoc]) _ (by rw [hq3, hq1])
  obtain ⟨memo', a4, hrun4, hA4, hk4, hM4, hlt4, hq4, hf4, hs4, hmo4⟩ :=
    exprCall hL hr cv.type hfe hI3.arena hI3.mode hM3 hdt (by rw [hs3, hs2, hs1, hst]; decide)
      (by have := hI3.ok.2.2.2.2; omega) h4
  obtain ⟨hI4, hE4, hIW4, ht4, -⟩ := hI3.expr hA4 hmo4 hf4 hk4
  obtain ⟨hI5, hM5, hs5, ht5, hIW5⟩ := setER_facts hI4 hM4 (pp + 3) (r4.headD 0) (by omega)
  refine ⟨memo', ⟨decI (r1.headD 0), ws.map decI, decI (r4.headD 0)⟩, a4, ?_, hI5, hM5,
    by rw [hs5, hs4, hs3, hs2, hs1, hst], ?_, ?_, by omega, by rw [hIW5, hIW4, hiw3, hIW2, hIW1], ?_⟩
  · simp only [Frontend.internCV]
    rw [run_bind_of _ _ _ _ _ hrun1, run_bind_of _ _ _ _ _ hrun3, run_bind_of _ _ _ _ _ hrun4]
    rfl
  · simp only [List.headD_cons]; rw [hq4, hq3, hq1]; simp [encCV, encNameL]; omega
  · refine ⟨by omega, fun i hi hR => ?_⟩
    rw [er_set_ne _ _ _ _ (by omega)]
    simp only [erA, hE4]
    rw [show (m3.arr64 EREC)[i]? = (erA m3)[i]? from rfl, hek3.2 i (by omega) (by omega),
      er_set_ne _ _ _ _ (by omega)]
    simp only [erA, hE1]
  · -- the record
    have hw0 : (erA (m1.set64 EREC pp (r1.headD 0)))[pp.toNat]? = some (r1.headD 0) :=
      er_set_get m1 pp _ (by omega)
    have hw0' : (erA ((m4.set64 EREC (pp + 3) (r4.headD 0))))[pp.toNat]? = some (r1.headD 0) := by
      rw [er_set_ne _ _ _ _ (by omega)]
      simp only [erA, hE4]
      rw [show (m3.arr64 EREC)[pp.toNat]? = (erA m3)[pp.toNat]? from rfl,
        hek3.2 pp.toNat (by omega) (by omega)]
      exact hw0
    have hw3 : (erA (m4.set64 EREC (pp + 3) (r4.headD 0)))[pp.toNat + 3]? = some (r4.headD 0) := by
      rw [← hp3]; exact er_set_get m4 _ _ (by have := hI4.ok.2.1; omega)
    have hL3 : Holds (fun i => (pp.toNat + 1 ≤ i ∧ i < pp.toNat + 1 + 2) ∨
        (erTop (m1.set64 EREC pp (r1.headD 0)) ≤ i ∧ i < erTop m3)) (fun _ => False)
        (fun m => (hlist? (erA m) (pp.toNat + 1) : Option (List NIdx)))
        (m4.set64 EREC (pp + 3) (r4.headD 0)) (ws.map decI) := by
      rw [← hp1]
      refine (hH3.keep (fun i _ => by simp only [erA, hE4]) (fun _ h => h.elim)).setER _ _ ?_
      intro i hi; rw [hp1] at hi; omega
    refine (holds_decCV hw0' hlt1 hL3 hw3 hlt4).mono (fun i hi => ?_) (fun _ h => h)
    rcases hi with rfl | hi | rfl
    · left; omega
    · rcases hi with hi | hi
      · left; omega
      · right; omega
    · left; omega

end cv

end L.Rom
