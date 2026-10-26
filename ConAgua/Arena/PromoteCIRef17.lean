import ConAgua.Arena.PromoteCIRef16

/-!
# The constant arms: `pci_ctor`, `pci_defn`
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

theorem toNat_add5 (x : Word) (h : x.toNat + 5 < 2 ^ 64) : (x + 5).toNat = x.toNat + 5 := by
  rw [UInt64.toNat_add, show (5 : Word).toNat = 5 from rfl]; exact Nat.mod_eq_of_lt h

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem ctor_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f q : Word) (D : Nat)
    (cv : IConstantVal) (kw w5 w6 : Word) (r : List Word) (m' : Mem) (hD : ArenaD m a)
    (hP : PMemoR m pm) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hts : erecTop m ≤ (m.arr64 EREC).size)
    (hcv : decCV (preE m D) (q.toNat + 1) = some cv) (hkw : (m.arr64 EREC)[q.toNat]? = some kw)
    (h5 : (m.arr64 EREC)[q.toNat + 5]? = some w5) (h6 : (m.arr64 EREC)[q.toNat + 6]? = some w6)
    (hqD : q.toNat + 7 ≤ D) (hDt : D ≤ erecTop m)
    (hc : callW p n "pci_ctor" [f, q] m = some (r, m')) :
    ArmOk m a r m' 7 kw
      (fun (cv' : IConstantVal) a' pm' => (promoteCV pm f.toNat cv).run a = .ok ((pm', cv'), a'))
      (fun cv' M d => decCV (erecP M) (d + 1) = some cv' ∧ (erecP M)[d + 5]? = some w5 ∧
        (erecP M)[d + 6]? = some w6) := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (pciCtor_spec p hp n ⟨m, Locals.init []⟩ f q) hc
  simp only at hW
  rw [hs'] at hW
  simp only [ctorW, pciMkC] at hW
  cases n with
  | zero => simp only [callW_zero', Option.bind_none] at hW; cases hW
  | succ n =>
  have e1 : (q + 1).toNat = q.toNat + 1 := toNat_add1 _ (by omega)
  have e5 : (q + 5).toNat = q.toNat + 5 := toNat_add5 _ (by omega)
  obtain ⟨⟨ra, m0⟩, hrd, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hm0, hr0, -⟩ := rd2_call p hp hrd
  obtain rfl := hm0.symm
  rw [rd2W_of hsz (by rw [e5]; simpa using h5) (by rw [e5]; simpa using h6)] at hr0
  subst hr0
  simp only [g0, g1, List.headD_cons, List.tail_cons] at hW
  obtain ⟨⟨c, m₁⟩, hca, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨a1, pm1, cv', hrun1, hD1, hP1, hCV, hg1, hts1, hcp1, hfr1, htk1⟩ :=
    cv_rel p hp (n + 1) m a pm f (q + 1) cv c m₁ hD hP
      (by rw [e1]; exact (preE_mono m hDt).decCV hcv) hsz hca
  have hsz1 : (m₁.arr64 EREC).size < 2 ^ 64 := by rw [hg1.2.2]; exact hsz
  cases hmk : callW p (n + 1) "pci_mk" [q, 7, g0 c, g1 c, g2 c, g3 c] m₁ with
  | none => rw [hmk] at hW; cases hW
  | some x =>
  obtain ⟨dl, m₂⟩ := x
  rw [hmk] at hW
  simp only [Option.bind_some] at hW
  have hkw1 : (m₁.arr64 EREC)[q.toNat]? = some kw := by
    rw [hg1.2.1 _ (by omega)]; exact hkw
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := mk_decode p hp (n := n) hCV (ArrExt.refl _) (Nat.le_refl _)
    hts1 hsz1 hkw1 (by simp only [show ((7 : Word)).toNat = 7 from rfl]; omega) hmk
  simp only [show ((7 : Word)).toNat = 7 from rfl] at b2
  have hsz2 : (m₂.arr64 EREC).size < 2 ^ 64 := by rw [b3.2.2]; exact hsz1
  have e5d : (dl.headD 0 + 5).toNat = erecTop m₁ + 5 := by
    rw [toNat_add5 _ (by omega)]; omega
  obtain ⟨⟨z, m₃⟩, hwr, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨t1, t2, t3, t4, t5⟩ := wr2_rel p hp (d := dl.headD 0 + 5)
    (by rw [e5d]; omega) hsz2 hwr
  rw [e5d] at t3 t4 t5
  obtain ⟨hr, hm3⟩ := Prod.mk.inj (Option.some.inj hW)
  subst hm3
  obtain ⟨hDf, hPf⟩ := arenaD_erec129 hD1 hP1 b4
  obtain ⟨hDg, hPg⟩ := arenaD_erecFrame hDf hPf t2
  have hT3 : erecTop m₃ = erecTop m₂ := by simp only [erecTop]; rw [t2.2.1 129 (by simp)]
  have hsz3 : (m₃.arr64 EREC).size = (m₂.arr64 EREC).size := t1
  have hgs : SlotGrow m₂ m₃ (erecTop m₁ + 5) (erecTop m₁ + 7) :=
    ⟨by rw [hT3]; exact Nat.le_refl _, fun i hi hout => t3 i (by omega), hsz3⟩
  have hts3 : erecTop m₃ ≤ (m₃.arr64 EREC).size := by rw [hT3, hsz3]; exact b5
  have hg23 : ErecGrow m₁ m₃ :=
    ((SlotGrow.of_grow b3 (erecTop m₁ + 5) (erecTop m₁ + 7)).trans hgs (Nat.le_refl _)
      (Nat.le_refl _)).toGrow (by omega)
  refine ⟨a1, pm1, cv', hrun1, hDg, hPg, hcp1, ?_,
    htk1.trans ((TierKeep.of_frame b4 (by simp)).trans (TierKeep.of_frame t2 (by simp))), hg1.trans hg23, hts3, erecTop m₁, ?_, hg1.1, ?_, ?_, ?_⟩
  · exact (hfr1.trans (b4.mono (by simp) (by simp))).trans (t2.mono (by simp) (by simp))
  · rw [← hr]; exact b1
  · rw [hT3, b2]; omega
  · rw [t3 _ (Or.inl (by omega))]; exact b6
  · refine ⟨b7.2 m₃ (erecTop m₁ + 7) hgs b5 hts3, ?_, ?_⟩
    · exact preE_of_get (m := m₃) (T := erecTop m₃) (by rw [hT3, b2]; omega) (by simpa using t4)
    · exact preE_of_get (m := m₃) (T := erecTop m₃) (by rw [hT3, b2]; omega) (by simpa using t5)

end rel

end L.Arena
