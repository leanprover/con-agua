import ConAgua.Rom.CIReadRefRule

/-!
# The ROM constant readers: constants (helper `decls4-rom`)

`rci_ci(q)` refines `Frontend.internCI` into a fresh `EREC` record (`decCI`), for the kinds the
pinned constants have (axioms, theorems, inductives without `sortZ` names, constructors,
recursors with plain rules: `ciFits`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open ConRon.Arena ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order

namespace L.Rom

open L.Arena L.Ind

/-- The constants the readers handle, fitting their encodings. -/
def ciFits : ConLeche.ConstantInfo → Bool
  | .axiomInfo v => cvFits v
  | .thmInfo v => cvFits v
  | .indInfo v c => cvFits v && capsFits c
  | .ctorInfo v nP nF => cvFits v && decide (nP < 2 ^ 64) && decide (nF < 2 ^ 64)
  | .recInfo v mI rP rs => cvFits v && decide (mI < 2 ^ 64) && decide (rP < 2 ^ 64) &&
      decide (rs.length < 2 ^ 59) && rs.all ruleFits
  | _ => false

section ci
variable {rom : List UInt8} {p : Prog} (hL : RomCIProg rom p) (hr : RomOK rom)
include hL hr

set_option maxHeartbeats 4000000 in
/-- **`rci_ci`'s common part**: the kind word, the record allocated, its constant value. -/
theorem ciPre {m₀ : Mem} {a₀ : AState} (seen : List ConLeche.Expr) (memo : EMemo)
    (v : ConLeche.ConstantVal) (hv : cvFits v = true) (kn : Nat) (sz : Word)
    (hsz : ciSize (UInt64.ofNat kn) = some sz) (h5 : 5 ≤ sz.toNat) (hkn : kn < 2 ^ 64)
    (tail : List UInt8) (k : Nat) (m : Mem) (a : AState) (q : Word) (rest : List UInt8)
    (r : List Word) (m' : Mem) (hI : RInv m₀ a₀ m a) (hM : MemoR m seen memo) (hst : stkTop m = 0)
    (hd : rom.drop q.toNat = u64B kn ++ ((encCV seen v).1 ++ (tail ++ rest)))
    (hc : callW p (k + 1) "rci_ci" [q] m = some (r, m')) :
    ∃ (pp : Word) (memo1 : EMemo) (icv : IConstantVal) (a1 : AState) (m2 : Mem) (q2 : Word) (k' : Nat),
      k = k' + 1 ∧ pp.toNat = erTop m ∧ erTop m + sz.toNat ≤ erTop m2 ∧
      (Frontend.internCV memo v).run a = .ok ((memo1, icv), a1) ∧
      RInv m₀ a₀ m2 a1 ∧ MemoR m2 (encCV seen v).2 memo1 ∧ stkTop m2 = 0 ∧
      rom.drop q2.toNat = tail ++ rest ∧ q2.toNat = q.toNat + 8 + (encCV seen v).1.length ∧
      EKeep (fun _ => False) m m2 ∧ m2.arr64 IW = m.arr64 IW ∧
      (erA m2)[pp.toNat]? = some (UInt64.ofNat kn) ∧
      Holds (fun i => (pp.toNat + 1 ≤ i ∧ i < pp.toNat + 5) ∨ (erTop m + sz.toNat ≤ i ∧ i < erTop m2))
        (fun _ => False) (fun m => decCV (erA m) (pp.toNat + 1)) m2 icv ∧
      ntBW (ciTailW p k m2 (UInt64.ofNat kn) pp q2) (fun r3 m3 => some ([pp, r3.headD 0], m3)) =
        some (r, m') := by
  have hw := callW_model (M := fun mq => ciW p k mq q) (ci_specW rom p hL k · q) hc
  unfold ciW at hw
  replace hw := rdU_some hL hw
  have e0 := u64_at hr q 0 [] kn _ (by rw [hd]; rfl) (by simp) hkn
  simp only [UInt64.add_zero] at e0
  rw [e0, hsz] at hw
  simp only at hw
  have hlt := hI.er_lt
  have hgo := hI.grow.2.1
  have hrom := hr; simp only [RomOK] at hrom
  cases h1 : callW p k "erec_alloc" [sz] m with
  | none => rw [h1] at hw; simp at hw
  | some t1 =>
  obtain ⟨r1, m1⟩ := t1
  rw [h1, bW_some] at hw
  obtain ⟨hI1, ho1, ht1, hE1, hIW1, -⟩ := hI.erAlloc (erAllocCall hL h1)
  have hf1 : MemFrame [] [129] m m1 := by
    have := erAllocCall hL h1; simp only [erAllocW] at this
    split at this; · cases this
    split at this; · cases this
    simp only [Option.some.injEq, Prod.mk.injEq] at this; rw [← this.2]; exact MemFrame.setCtl _ _ _
  have hM1 := hM.frameG hf1 (by simp) (by decide)
  have hs1 : stkTop m1 = stkTop m := hf1.2.1 131 (by decide)
  have hlt1 := hI1.er_lt
  obtain ⟨hI2, hM2, hs2, ht2, hIW2⟩ := setER_facts hI1 hM1 (r1.headD 0) (UInt64.ofNat kn) (by omega)
  cases k with
  | zero => rw [callW_zero] at hw; simp at hw
  | succ k =>
  cases h2 : callW p (k + 1) "rci_cv" [q + 8, r1.headD 0 + 1] (m1.set64 EREC (r1.headD 0) (UInt64.ofNat kn)) with
  | none => rw [h2] at hw; simp at hw
  | some t2 =>
  obtain ⟨r2, m2⟩ := t2
  rw [h2, bW_some] at hw
  have hlen := drop_len rom _ (u64B kn) _ hd (by simp [u64B])
  simp only [u64B, List.length_cons, List.length_nil] at hlen
  have hq8 : (q + 8).toNat = q.toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
  have hp1 : (r1.headD 0 + 1).toNat = (r1.headD 0).toNat + 1 := by
    rw [UInt64.toNat_add, show (1 : Word).toNat = 1 from rfl]; exact Nat.mod_eq_of_lt (by omega)
  have hd8 : rom.drop (q + 8).toNat = (encCV seen v).1 ++ (tail ++ rest) := by
    rw [hq8, ← List.drop_drop, hd]; simp [u64B]
  obtain ⟨memo1, icv, a2, hrun2, hI3, hM3, hs3, hq3, hek3, ht3, hIW3, hH3⟩ :=
    cv_rel hL hr seen memo v hv k _ a _ (r1.headD 0 + 1) _ _ m2 hI2 hM2 (by rw [hs2, hs1, hst]) hd8
      (by omega) (by omega) h2
  have hE1' : ∀ i : Nat, (erA m1)[i]? = (erA m)[i]? := fun i => by unfold erA; rw [hE1]
  refine ⟨r1.headD 0, memo1, icv, a2, m2, r2.headD 0, k, rfl, ho1, by omega, hrun2, hI3, hM3, hs3,
    ?_, ?_, ⟨by omega, fun i hi _ => ?_⟩, by rw [hIW3, hIW2, hIW1], ?_, ?_, hw⟩
  · exact drop_shift rom hr _ _ _ _ (by rw [hd8, List.append_assoc]) _ hq3
  · rw [hq3, hq8]
  · rw [hek3.2 i (by omega) (by omega), er_set_ne _ _ _ _ (by omega), hE1']
  · rw [hek3.2 _ (by omega) (by omega)]
    exact er_set_get m1 _ _ (by have := hI1.ok.2.1; omega)
  · rw [hp1] at hH3
    exact hH3.mono (fun i hi => by omega) (fun _ h => h)

end ci

end L.Rom
