import ConAgua.Arena.PromoteCIRef17

/-!
# The constant arms: `pci_defn`, `pci_ind`
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

theorem ErecGrow.of_eq {m m' : Mem} (hE : m'.arr64 EREC = m.arr64 EREC)
    (hT : erecTop m' = erecTop m) : ErecGrow m m' :=
  ⟨by omega, fun i _ => by rw [hE], by rw [hE]⟩

theorem rd3W_ne {m : Mem} {s : Word} (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hne : rd3W m s ≠ []) :
    ∃ a b c : Word, rd3W m s = [a, b, c] ∧ (m.arr64 EREC)[s.toNat]? = some a ∧
      (m.arr64 EREC)[s.toNat + 1]? = some b ∧ (m.arr64 EREC)[s.toNat + 2]? = some c := by
  unfold rd3W at hne ⊢
  by_cases hc : (m.arr64 EREC).size ≤ s.toNat ∨ (m.arr64 EREC).size ≤ (s + 1).toNat ∨
      (m.arr64 EREC).size ≤ (s + 2).toNat
  · rw [if_pos hc] at hne; exact absurd rfl hne
  rw [if_neg hc]
  simp only [not_or, Nat.not_le] at hc
  obtain ⟨h0, h1, h2⟩ := hc
  have e1 : (s + 1).toNat = s.toNat + 1 := toNat_add1 _ (by omega)
  have e2 : (s + 2).toNat = s.toNat + 2 := by
    rw [UInt64.toNat_add, show (2 : Word).toNat = 2 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  rw [e1] at h1; rw [e2] at h2
  refine ⟨_, _, _, rfl, ?_, ?_, ?_⟩
  · simp [rdW, Array.getElem?_eq_getElem h0]
  · rw [rdW, e1]; simp [Array.getElem?_eq_getElem h1]
  · rw [rdW, e2]; simp [Array.getElem?_eq_getElem h2]

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem defn_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f q : Word) (D : Nat)
    (cv : IConstantVal) (kw wv : Word) (r : List Word) (m' : Mem) (hD : ArenaD m a)
    (hP : PMemoR m pm) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hts : erecTop m ≤ (m.arr64 EREC).size)
    (hcv : decCV (preE m D) (q.toNat + 1) = some cv) (hkw : (m.arr64 EREC)[q.toNat]? = some kw)
    (h5 : (m.arr64 EREC)[q.toNat + 5]? = some wv) (hwv : wv.toNat < 2 ^ 32)
    (hqD : q.toNat + 7 ≤ D) (hDt : D ≤ erecTop m)
    (hc : callW p n "pci_defn" [f, q] m = some (r, m')) :
    ArmOk m a r m' 8 kw
      (fun (x : IConstantVal × EIdx) a' pm' => ∃ (a1 : AState) (pm1 : PMemo),
        (promoteCV pm f.toNat cv).run a = .ok ((pm1, x.1), a1) ∧
        (promoteE pm1 f.toNat (decE wv)).run a1 = .ok ((pm', x.2), a'))
      (fun x M d => decCV (erecP M) (d + 1) = some x.1 ∧
        (hd? (erecP M) (d + 5) : Option EIdx) = some x.2 ∧ ∃ w6 w7 : Word,
          (erecP M)[d + 6]? = some w6 ∧ (erecP M)[d + 7]? = some w7 ∧
          (m.arr64 EREC)[q.toNat + 6]? = some w6 ∧ (m.arr64 EREC)[q.toNat + 7]? = some w7) := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (pciDefn_spec p hp n ⟨m, Locals.init []⟩ f q) hc
  simp only at hW
  rw [hs'] at hW
  simp only [defnW, pciMkC] at hW
  cases n with
  | zero => simp only [callW_zero', Option.bind_none] at hW; cases hW
  | succ n =>
  have e1 : (q + 1).toNat = q.toNat + 1 := toNat_add1 _ (by omega)
  have e5 : (q + 5).toNat = q.toNat + 5 := toNat_add5 _ (by omega)
  obtain ⟨⟨ra, m0⟩, hrd, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hm0, hr0, hne⟩ := rd3_call p hp hrd
  obtain rfl := hm0.symm
  rw [hr0] at hne
  obtain ⟨wa, w6, w7, hr3, hwa, hw6, hw7⟩ := rd3W_ne hsz hne
  rw [e5] at hwa hw6 hw7
  have hwav : wv = wa := (Option.some.inj (hwa.symm.trans (by simpa using h5))).symm
  subst hwav
  rw [hr3] at hr0
  subst hr0
  simp only [g0, g1, g2, List.headD_cons, List.tail_cons] at hW
  obtain ⟨⟨c, m₁⟩, hca, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨a1, pm1, cv', hrun1, hD1, hP1, hCV, hg1, hts1, hcp1, hfr1, htk1⟩ :=
    cv_rel p hp (n + 1) m a pm f (q + 1) cv c m₁ hD hP
      (by rw [e1]; exact (preE_mono m hDt).decCV hcv) hsz hca
  have hsz1 : (m₁.arr64 EREC).size < 2 ^ 64 := by rw [hg1.2.2]; exact hsz
  obtain ⟨⟨rx, m₂⟩, hcb, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨a2, pm2, hrun2, hD2, hP2, hpw2, hcp2, hfr2, htk2⟩ :=
    (pe_rel p hp (n + 1)).1 m₁ a1 pm1 f wv rx m₂ hD1 hP1 hwv hcb
  obtain ⟨hE2, hT2⟩ := eFrame_erec hfr2
  have hg12 : ErecGrow m₁ m₂ := ErecGrow.of_eq hE2 hT2
  have hP2e : erecP m₂ = erecP m₁ := by
    rw [erecP_eq_preE, erecP_eq_preE, hT2]; exact preE_congr hE2 _
  have hsz2 : (m₂.arr64 EREC).size < 2 ^ 64 := by rw [hE2]; exact hsz1
  have hts2 : erecTop m₂ ≤ (m₂.arr64 EREC).size := by rw [hE2, hT2]; exact hts1
  cases hmk : callW p (n + 1) "pci_mk" [q, 8, g0 c, g1 c, g2 c, g3 c] m₂ with
  | none => rw [hmk] at hW; cases hW
  | some x =>
  obtain ⟨dl, m₃⟩ := x
  rw [hmk] at hW
  simp only [Option.bind_some] at hW
  have hkw2 : (m₂.arr64 EREC)[q.toNat]? = some kw := by
    rw [hE2, hg1.2.1 _ (by omega)]; exact hkw
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := mk_decode p hp (n := n) hCV (by rw [hP2e]; exact ArrExt.refl _)
    (by rw [hT2]; exact Nat.le_refl _) hts2 hsz2 hkw2 (by simp only [show ((8 : Word)).toNat = 8 from rfl]; omega) hmk
  simp only [show ((8 : Word)).toNat = 8 from rfl] at b2
  have hsz3 : (m₃.arr64 EREC).size < 2 ^ 64 := by rw [b3.2.2]; exact hsz2
  have e5d : (dl.headD 0 + 5).toNat = erecTop m₂ + 5 := by
    rw [toNat_add5 _ (by omega)]; omega
  obtain ⟨⟨z, m₄⟩, hwr, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ := wr3_rel p hp (d := dl.headD 0 + 5)
    (by rw [e5d]; omega) hsz3 hwr
  rw [e5d] at t3 t4 t5 t6
  obtain ⟨hr, hm4⟩ := Prod.mk.inj (Option.some.inj hW)
  subst hm4
  obtain ⟨hDf, hPf⟩ := arenaD_erec129 hD2 hP2 b4
  obtain ⟨hDg, hPg⟩ := arenaD_erecFrame hDf hPf t2
  have hT4 : erecTop m₄ = erecTop m₃ := by simp only [erecTop]; rw [t2.2.1 129 (by simp)]
  have hsz4 : (m₄.arr64 EREC).size = (m₃.arr64 EREC).size := t1
  have hgs : SlotGrow m₃ m₄ (erecTop m₂ + 5) (erecTop m₂ + 8) :=
    ⟨by rw [hT4]; exact Nat.le_refl _, fun i hi hout => t3 i (by omega), hsz4⟩
  have hts4 : erecTop m₄ ≤ (m₄.arr64 EREC).size := by rw [hT4, hsz4]; exact b5
  have hg34 : ErecGrow m₂ m₄ :=
    ((SlotGrow.of_grow b3 (erecTop m₂ + 5) (erecTop m₂ + 8)).trans hgs (Nat.le_refl _)
      (Nat.le_refl _)).toGrow (by omega)
  refine ⟨a2, pm2, (cv', decE (rx.headD 0)), ⟨a1, pm1, hrun1, hrun2⟩, hDg, hPg,
    hcp2.trans hcp1, ?_,
    htk1.trans (htk2.trans ((TierKeep.of_frame b4 (by simp)).trans (TierKeep.of_frame t2 (by simp)))),
    hg1.trans (hg12.trans hg34), hts4, erecTop m₂, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((hfr1.trans (eFrame_cons hfr2)).trans (b4.mono (by simp) (by simp))).trans
      (t2.mono (by simp) (by simp))
  · rw [← hr]; exact b1
  · rw [hT2]; exact hg1.1
  · rw [hT4, b2]; omega
  · rw [t3 _ (Or.inl (by omega))]; exact b6
  · refine ⟨b7.2 m₄ (erecTop m₂ + 8) hgs b5 hts4, ?_, w6, w7, ?_, ?_, hw6, hw7⟩
    · exact hd?_of_pre (m := m₄) (T := erecTop m₄) (by rw [hT4, b2]; omega) (by simpa using t4) hpw2.1
    · exact preE_of_get (m := m₄) (T := erecTop m₄) (by rw [hT4, b2]; omega) (by simpa using t5)
    · exact preE_of_get (m := m₄) (T := erecTop m₄) (by rw [hT4, b2]; omega) (by simpa using t6)

end rel

end L.Arena
