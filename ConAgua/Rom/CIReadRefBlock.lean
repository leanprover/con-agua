import ConAgua.Rom.CIReadRefCI
import ConAgua.Census.Attr

/-!
# The ROM constant readers: blocks (helper `decls4-rom`)

`rci_block_to(q, o, k)` refines `Frontend.internCIList` at one memo, the record pointers to
`IW[o ‥]` (`basisDec`).
-/


open ConRon.Arena ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order

namespace L.Rom

open L.Arena L.Ind

/-- `IW` below `m`'s top unchanged outside `R`, the top unchanged. -/
def IKeep (R : Nat → Prop) (m m' : Mem) : Prop :=
  iwTop m' = iwTop m ∧ ∀ i, i < iwTop m → ¬ R i → (iwA m')[i]? = (iwA m)[i]?

theorem iw_set_ne (m : Mem) (j w : Word) (i : Nat) (hi : i ≠ j.toNat) :
    (iwA (m.set64 IW j w))[i]? = (iwA m)[i]? := by
  simp only [iwA]
  rw [Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  simp [Ne.symm hi]

/-- The block's pointer and record at index `j`. -/
def BlkAt (dn : NIdx → Option ConLeche.Name) (SE : Nat → Prop) (m : Mem) (i : Nat)
    (ci : IConstantInfo) : Prop :=
  ∃ w : Word, (iwA m)[i]? = some w ∧
    Holds SE (fun _ => False) (fun m => decCI (erA m) dn w.toNat) m ci

/-- The `sortZ` names of a block's constants. -/
def blkZ : List ConLeche.ConstantInfo → List ConLeche.Name
  | [] => []
  | c :: cs => ciZ c ++ blkZ cs

section block
variable {rom : List UInt8} {p : Prog} (hL : RomCIProg rom p) (hr : RomOK rom)
include hL hr

/-- **`rci_block_to` refines `Frontend.internCIList`** at one memo. -/
@[refines_part ConRon.Arena.Frontend.internCIList "the pinned constants' kinds"]
theorem blockTo_rel {m₀ : Mem} {a₀ : AState} {T : Nat} (dn : NIdx → Option ConLeche.Name) :
    ∀ (cs : List ConLeche.ConstantInfo), cs.all ciFits = true → ∀ (seen : List ConLeche.Expr)
      (memo : EMemo) (k : Nat) (m : Mem) (a : AState) (q o kw : Word) (rest : List UInt8)
      (r : List Word) (m' : Mem),
      ZOKM dn (blkZ cs) a memo → RInv m₀ a₀ T m a → MemoR m seen memo → stkTop m = 0 →
      rom.drop q.toNat = (encCIsM seen cs).1 ++ rest → kw.toNat = cs.length →
      iwTop m₀ ≤ o.toNat → o.toNat + cs.length ≤ iwTop m →
      callW p k "rci_block_to" [q, o, kw] m = some (r, m') →
      ∃ (memo' : EMemo) (ics : List IConstantInfo) (a' : AState),
        (Frontend.internCIList memo cs).run a = .ok ((memo', ics), a') ∧ ics.length = cs.length ∧
        RInv m₀ a₀ T m' a' ∧ MemoR m' (encCIsM seen cs).2 memo' ∧ stkTop m' = 0 ∧
        (r.headD 0).toNat = q.toNat + (encCIsM seen cs).1.length ∧
        EKeep (fun _ => False) m m' ∧ erTop m ≤ erTop m' ∧
        IKeep (fun i => o.toNat ≤ i ∧ i < o.toNat + cs.length) m m' ∧
        ∀ j (hj : j < ics.length),
          BlkAt dn (fun i => erTop m ≤ i ∧ i < erTop m') m' (o.toNat + j) ics[j] := by
  intro cs
  induction cs with
  | nil =>
    intro _ seen memo k m a q o kw rest r m' _ hI hM hst hd hk ho hot hc
    cases k with
    | zero => rw [callW_zero] at hc; cases hc
    | succ k =>
    have hw := callW_model (M := fun mq => blockToW p k mq q o kw) (blockTo_specW rom p hL k · q o kw) hc
    have hk0 : kw = 0 := by apply UInt64.toNat_inj.mp; simpa using hk
    simp only [blockToW, hk0, ite_true, Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact ⟨memo, [], a, rfl, rfl, hI, hM, hst, by simp [encCIsM], EKeep.refl _ _, Nat.le_refl _,
      ⟨rfl, fun _ _ _ => rfl⟩, fun j hj => by simp at hj⟩
  | cons c cs ih =>
    intro hfit seen memo k m a q o kw rest r m' hz hI hM hst hd hk ho hot hc
    simp only [List.all_cons, Bool.and_eq_true] at hfit
    simp only [List.length_cons] at hk hot
    cases k with
    | zero => rw [callW_zero] at hc; cases hc
    | succ k =>
    have hw := callW_model (M := fun mq => blockToW p k mq q o kw) (blockTo_specW rom p hL k · q o kw) hc
    have hk0 : kw ≠ 0 := fun h => by subst h; simp at hk
    simp only [blockToW, hk0, ite_false] at hw
    cases k with
    | zero => rw [callW_zero] at hw; simp at hw
    | succ k =>
    obtain ⟨r1, m1, h1, hw⟩ := ntBW_inv hw
    have hd0 : rom.drop q.toNat = (encCI seen c).1 ++ ((encCIsM (encCI seen c).2 cs).1 ++ rest) := by
      rw [hd]; simp [encCIsM, List.append_assoc]
    obtain ⟨memo1, ici, a1, hrun1, hI1, hM1, hs1, hq1, hek1, hp1, hIW1, hH1⟩ :=
      ci_rel hL hr dn seen memo c hfit.1 k m a (by
        rcases hz with h | ⟨hok, hmo, hn⟩
        · exact .inl (List.append_eq_nil_iff.mp h).1
        · exact .inr ⟨hok, hmo, hn.mono (fun x hx => List.mem_append_left _ hx)⟩) q _ r1 m1 hI hM hst
        hd0 h1
    have hlt := hI.iw_lt
    have hiw1 : iwTop m1 = iwTop m := hI1.top.trans hI.top.symm
    have hszI : iwTop m ≤ (m.arr64 IW).size := hI.ok.1
    have hI2 := hI1.setIW o (r1.headD 0) ho
    have hf2 := MemFrame.set64 m1 IW (by decide) o (r1.headD 0)
    have hM2 := hM1.frameG hf2 (by decide) (by simp)
    have hC2 : (m1.set64 IW o (r1.headD 0)).arr64 CTL = m1.arr64 CTL :=
      Mem.arr64_set64_ne _ _ _ _ _ (by decide)
    have hE2 : (m1.set64 IW o (r1.headD 0)).arr64 EREC = m1.arr64 EREC :=
      Mem.arr64_set64_ne _ _ _ _ _ (by decide)
    have hs2 : stkTop (m1.set64 IW o (r1.headD 0)) = stkTop m1 := by simp only [stkTop, hC2]
    have ht2 : erTop (m1.set64 IW o (r1.headD 0)) = erTop m1 := by simp only [erTop, hC2]
    have hi2 : iwTop (m1.set64 IW o (r1.headD 0)) = iwTop m1 := by simp only [iwTop, hC2]
    have ho1 : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hk1' : (kw - 1).toNat = cs.length := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
    obtain ⟨r2, m3, h2, hw⟩ := ntBW_inv hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hd1 : rom.drop (r1.tail.headD 0).toNat = (encCIsM (encCI seen c).2 cs).1 ++ rest :=
      drop_shift rom hr q _ _ _ (by rw [hd0, List.append_assoc]) _ hq1
    obtain ⟨memo2, ics, a2, hrun2, hlen2, hI3, hM3, hs3, hq3, hek3, ht3, hik3, hB3⟩ :=
      ih hfit.2 _ memo1 (k + 1) _ a1 _ (o + 1) (kw - 1) rest r2 m3 (by
        rcases hz with h | ⟨hok, hmo, hn⟩
        · exact .inl (List.append_eq_nil_iff.mp h).2
        · obtain ⟨st, -, hmo1⟩ := ConRon.Bridge.Frontend.internCI_sstep hok hmo hrun1
          exact .inr ⟨st.ok, hmo1, (hn.ext st.ext).mono (fun x hx => List.mem_append_right _ hx)⟩)
        hI2 hM2 (by rw [hs2]; exact hs1)
        hd1 hk1' (by omega) (by omega) h2
    have hE2' : ∀ i : Nat, (erA (m1.set64 IW o (r1.headD 0)))[i]? = (erA m1)[i]? := fun i => by
      unfold erA; rw [hE2]
    have hIW1' : ∀ i : Nat, (iwA m1)[i]? = (iwA m)[i]? := fun i => by unfold iwA; rw [hIW1]
    have hle1 := hek1.1
    have hle3 := hek3.1
    have hti3 := hik3.1
    refine ⟨memo2, ici :: ics, a2, ?_, by simp [hlen2], hI3, by simpa [encCIsM] using hM3, hs3, ?_, ?_,
      by omega, ⟨by rw [hik3.1, hi2, hiw1], fun i hi hR => ?_⟩, fun j hj => ?_⟩
    · simp only [Frontend.internCIList]
      rw [run_bind_of _ _ _ _ _ hrun1, run_bind_of _ _ _ _ _ hrun2]
      rfl
    · simp only [List.headD_cons]; rw [hq3, hq1]; simp [encCIsM]; omega
    · refine ⟨by omega, fun i hi _ => ?_⟩
      rw [hek3.2 i (by omega) id, hE2', hek1.2 i hi id]
    · simp only [List.length_cons] at hR
      rw [hik3.2 i (by omega) (by rw [ho1]; omega), iw_set_ne _ _ _ _ (by omega), hIW1']
    · cases j with
      | zero =>
        refine ⟨r1.headD 0, ?_, ?_⟩
        · simp only [Nat.add_zero]
          rw [hik3.2 _ (by omega) (by rw [ho1]; omega)]
          exact iw_set_get _ _ _ (by rw [hIW1]; omega)
        · simp only [List.getElem_cons_zero]
          refine (hH1.keep (fun i hi => ?_) (fun _ h => h.elim)).mono
            (fun i hi => ⟨hi.1, by omega⟩) (fun _ h => h)
          rw [hek3.2 i (by omega) id, hE2']
      | succ j =>
        simp only [List.getElem_cons_succ]
        obtain ⟨w, hw1, hw2⟩ := hB3 j (by simp at hj; omega)
        refine ⟨w, by rw [ho1] at hw1; rw [← hw1]; congr 1; omega,
          hw2.mono (fun i hi => ⟨by omega, hi.2⟩) (fun _ h => h)⟩

end block

end L.Rom
