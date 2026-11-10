module

import ConAgua.Rom.CIReadRefNames
import ConAgua.Rom.CIReadRefW
public import ConAgua.Rom.CIReadRefBase
public import ConAgua.Rom.CIReadSpec
import ConAgua.Rom.ReadScr

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

/-- A decoding survives a word written outside its words. -/
theorem Holds.putER {α : Type} {SE SI : Nat → Prop} {f : Mem → Option α} {x : α} {m : Mem}
    (h : Holds SE SI f m x) (j w : Word) (hj : ∀ i, SE i → i ≠ j.toNat ∧ i < 2 ^ 41)
    (hj1 : j.toNat < 2 ^ 41) : Holds SE SI f (erecPutMem m j w) x :=
  h.keep (fun i hi => er_put_ne m j w i (hj i hi).1 (hj i hi).2 hj1)
    (fun i _ => by simp only [iwA, (erecPutMem_frame m j w).arr IW (by decide) (by decide)])

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
at `pp` (allocated in the flag's tier above the entry's top). -/
@[refines_part ConRon.Arena.Frontend.internCV "values whose type fits the ROM encoding"]
theorem cv_rel {m₀ : Mem} {a₀ : AState} {T : Nat} (seen : List ConLeche.Expr) (memo : EMemo)
    (cv : ConLeche.ConstantVal) (hfit : cvFits cv = true) (k : Nat) (m : Mem) (a : AState)
    (q pp : Word) (rest : List UInt8) (r : List Word) (m' : Mem) (hI : RInv m₀ a₀ T m a)
    (hM : MemoR m seen memo) (hst : stkTop m = 0) (hd : rom.drop q.toNat = (encCV seen cv).1 ++ rest)
    (hp0 : erT m₀ ≤ pp.toNat) (hp4 : pp.toNat + 4 ≤ erT m)
    (hc : callW p (k + 1) "rci_cv" [q, pp] m = some (r, m')) :
    ∃ (memo' : EMemo) (icv : IConstantVal) (a' : AState),
      (Frontend.internCV memo cv).run a = .ok ((memo', icv), a') ∧
      RInv m₀ a₀ T m' a' ∧ MemoR m' (encCV seen cv).2 memo' ∧ stkTop m' = 0 ∧
      (r.headD 0).toNat = q.toNat + (encCV seen cv).1.length ∧
      EKeep (fun i => pp.toNat ≤ i ∧ i < pp.toNat + 4) m m' ∧ erT m ≤ erT m' ∧
      m'.arr64 IW = m.arr64 IW ∧
      Holds (fun i => (pp.toNat ≤ i ∧ i < pp.toNat + 4) ∨ (erT m ≤ i ∧ i < erT m'))
        (fun _ => False) (fun m => decCV (erA m) pp.toNat) m' icv := by
  simp only [cvFits, Bool.and_eq_true] at hfit
  obtain ⟨⟨hfn, hfl⟩, hfe⟩ := hfit
  have hw := callW_model (M := fun mq => cvW p k mq q pp) (cv_specW rom p hL k · q pp) hc
  unfold cvW at hw
  simp only [putE] at hw
  have hlt := hI.er_lt
  -- the name
  obtain ⟨r1, m1, h1, hw⟩ := ntBW_inv hw
  have hd0 : rom.drop q.toNat = encName cv.name ++
      (encNameL cv.levelParams ++ ((encExprM seen cv.type).1 ++ rest)) := by
    rw [hd]; simp [encCV, List.append_assoc]
  obtain ⟨a1, hrun1, hA1, hk1, hlt1, hq1, hf1, hmo1⟩ := nameCall hL hr cv.name hfn hI.arena hI.mode hd0 h1
  obtain ⟨hI1, -, -, hIW1, ht1, -, hE1⟩ := hI.expr hA1 hmo1 (hf1.mono (fun b hb => by simp [ExprA, RomA, hb])
    (fun x hx => by simp [ExprC, RomC, hx])) hk1 (L.Arena.internName_ks _ _ _ _ hrun1)
  have hM1 := hM.frameG hf1 (by decide) (by decide)
  have hs1 : stkTop m1 = stkTop m := hf1.ctl 131 (by decide)
  -- the name word
  obtain ⟨ra, ma, ha, hw⟩ := ntBW_inv hw
  rw [putCall hL ha] at hw
  obtain ⟨hI2, hM2, hs2, ht2, hIW2, hg2, hn2⟩ := putER_facts hI1 hM1 pp (r1.headD 0) hp0 (by omega)
  -- the level parameters
  cases k with
  | zero => rw [callW_zero] at hw; simp at hw
  | succ k =>
  obtain ⟨r2, m3, h2, hw⟩ := ntBW_inv hw
  have hp1 : (pp + 1).toNat = pp.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hp3 : (pp + 3).toNat = pp.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  have hdl : rom.drop (r1.tail.headD 0).toNat =
      encNameL cv.levelParams ++ ((encExprM seen cv.type).1 ++ rest) :=
    drop_shift rom q (encName cv.name) _ _ (by rw [hd0, List.append_assoc]) _ hq1
  obtain ⟨ws, a3, hrun3, hwlt, hI3, hM3, hs3, hq3, hek3, ht3, hiw3, hH3⟩ :=
    nameSl_rel hL hr seen memo cv.levelParams hfl k _ a1 _ (pp + 1) _ _ m3 hI2 hM2 hdl
      (by omega) (by rw [ht2, ht1]; omega) h2
  -- the type
  obtain ⟨r4, m4, h4, hw⟩ := ntBW_inv hw
  have hdt : rom.drop (r2.headD 0).toNat = (encExprM seen cv.type).1 ++ rest :=
    drop_shift rom _ (encNameL cv.levelParams) _ _ (by rw [hdl, List.append_assoc]) _ (by rw [hq3, hq1])
  obtain ⟨memo', a4, hrun4, hA4, hk4, hM4, hlt4, hq4, hf4, hs4, hmo4⟩ :=
    exprCall hL hr cv.type hfe hI3.arena hI3.mode hM3 hdt (by rw [hs3, hs2, hs1, hst]; decide)
      (by have := hI3.ok.ctl; omega) h4
  obtain ⟨hI4, -, -, hIW4, ht4, -, hE4⟩ := hI3.expr hA4 hmo4 hf4 hk4
    (L.Arena.internExprGo_ks _ _ _ _ _ hrun4)
  obtain ⟨rb, m5, hb, hw⟩ := ntBW_inv hw
  rw [putCall hL hb] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  obtain ⟨hI5, hM5, hs5, ht5, hIW5, hg5, hn5⟩ :=
    putER_facts hI4 hM4 (pp + 3) (r4.headD 0) (by omega) (by omega)
  refine ⟨memo', ⟨decI (r1.headD 0), ws.map decI, decI (r4.headD 0)⟩, a4, ?_, hI5, hM5,
    by rw [hs5, hs4, hs3, hs2, hs1, hst], ?_, ?_, by omega, by rw [hIW5, hIW4, hiw3, hIW2, hIW1], ?_⟩
  · simp only [Frontend.internCV]
    rw [run_bind_of _ _ _ _ _ hrun1, run_bind_of _ _ _ _ _ hrun3, run_bind_of _ _ _ _ _ hrun4]
    rfl
  · simp only [List.headD_cons]; rw [hq4, hq3, hq1]; simp [encCV, encNameL]; omega
  · refine ⟨by omega, fun i hi hR => ?_⟩
    rw [hn5 i (by omega) (by omega), hE4, hek3.2 i (by omega) (by omega), hn2 i (by omega) (by omega), hE1]
  · -- the record
    have hw0' : erA (erecPutMem m4 (pp + 3) (r4.headD 0)) pp.toNat = some (r1.headD 0) := by
      rw [hn5 _ (by omega) (by omega), hE4, hek3.2 pp.toNat (by omega) (by omega)]
      exact hg2
    have hw3 : erA (erecPutMem m4 (pp + 3) (r4.headD 0)) (pp.toNat + 3) = some (r4.headD 0) := by
      rw [← hp3]; exact hg5
    have hL3 : Holds (fun i => (pp.toNat + 1 ≤ i ∧ i < pp.toNat + 1 + 2) ∨
        (erT (erecPutMem m1 pp (r1.headD 0)) ≤ i ∧ i < erT m3)) (fun _ => False)
        (fun m => (hlist? (erA m) (pp.toNat + 1) : Option (List NIdx)))
        (erecPutMem m4 (pp + 3) (r4.headD 0)) (ws.map decI) := by
      rw [← hp1]
      refine (hH3.keep (fun i _ => by rw [hE4]) (fun _ h => h.elim)).putER _ _ ?_ (by omega)
      intro i hi; rw [hp1] at hi; have := hI3.er_lt; rw [hp3]; omega
    refine (holds_decCV hw0' hlt1 hL3 hw3 hlt4).mono (fun i hi => ?_) (fun _ h => h)
    rcases hi with rfl | hi | rfl
    · left; omega
    · rcases hi with hi | hi
      · left; omega
      · right; omega
    · left; omega

end cv

end L.Rom
