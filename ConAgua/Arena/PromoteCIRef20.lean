import ConAgua.Arena.PromoteCIRef19

/-!
# `pci_rec`
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

theorem SlotGrow.widen {m m' : Mem} {lo hi lo' hi' : Nat} (h : SlotGrow m m' lo hi)
    (hlo : lo' ≤ lo) (hhi : hi ≤ hi') : SlotGrow m m' lo' hi' :=
  ⟨h.1, fun i hi1 hout => h.2.1 i hi1 (by omega), h.2.2⟩

theorem rules_zero_gen {n : Nat} {f s l d : Word} {m m' : Mem} {r : List Word} (p : Prog)
    (hp : PromoteProg p) (hl : l = 0)
    (hc : callW p n "promote_rules" [f, s, l, d] m = some (r, m')) : m' = m := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (promoteRules_spec p hp n ⟨m, Locals.init []⟩ f s l d) hc
  simp only at hW
  rw [hs'] at hW
  simp only [rulesW, hl, ↓reduceIte, Option.some.injEq] at hW
  exact hW.symm

theorem preE_size_le (m : Mem) (D : Nat) : (preE m D).size ≤ D := by
  simp [preE, Nat.min_le_left]

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

/-- **`rec_block`**: a fresh block of `11 l` words, the four record words written at `d5`. -/
theorem recBlock_rel {n : Nat} {d5 w5 w6 l : Word} {m m' : Mem} {r : List Word}
    (hsz : (m.arr64 EREC).size < 2 ^ 64) (hbd : d5.toNat + 4 ≤ erecTop m)
    (hts : erecTop m ≤ (m.arr64 EREC).size)
    (hc : callW p n "rec_block" [d5, w5, w6, l] m = some (r, m')) :
    l.toNat < 1152921504606846976 ∧ (r.headD 0).toNat = erecTop m ∧
    erecTop m' = erecTop m + 11 * l.toNat ∧ SlotGrow m m' d5.toNat (d5.toNat + 4) ∧
    MemFrame [EREC] [129] m m' ∧ erecTop m' ≤ (m'.arr64 EREC).size ∧
    (m'.arr64 EREC)[d5.toNat]? = some w5 ∧ (m'.arr64 EREC)[d5.toNat + 1]? = some w6 ∧
    (m'.arr64 EREC)[d5.toNat + 2]? = some (r.headD 0) ∧ (m'.arr64 EREC)[d5.toNat + 3]? = some l := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (recBlock_spec p hp n ⟨m, Locals.init []⟩ d5 w5 w6 l) hc
  simp only at hW
  rw [hs'] at hW
  simp only [recBlockW] at hW
  cases n with
  | zero => simp only [callW_zero'] at hW; split at hW <;> simp at hW
  | succ n =>
  by_cases hbig : 1152921504606846976 ≤ l
  · rw [ite_eq_left hbig] at hW; cases hW
  rw [ite_eq_right hbig] at hW
  have h60 : l.toNat < 1152921504606846976 := by
    have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hbig)
    simpa using this
  have h11 : (11 * l).toNat = 11 * l.toNat := toNat_mul11 l (by omega)
  obtain ⟨⟨r5, ma⟩, hal, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hd5, hTa, hroom, hfa, hEa⟩ := alloc_rel p hp hal
  rw [h11] at hTa hroom
  obtain ⟨⟨z, mb⟩, hwr, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
  subst hm
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ := wr4_rel p hp (d := d5) (by rw [hEa]; omega)
    (by rw [hEa]; exact hsz) hwr
  have hT : erecTop mb = erecTop m + 11 * l.toNat := by
    simp only [erecTop]; rw [t2.2.1 129 (by simp)]; exact hTa
  have hsz' : (mb.arr64 EREC).size = (m.arr64 EREC).size := by rw [t1, hEa]
  refine ⟨h60, by rw [← hr]; exact hd5, hT, ⟨by omega, fun i hi hout => ?_, hsz'⟩,
    (hfa.mono (by simp) (by simp)).trans (t2.mono (by simp) (by simp)), by rw [hT, hsz']; omega,
    by simpa using t4, by simpa using t5, by rw [← hr]; simpa using t6, by simpa using t7⟩
  · rw [t3 i (by omega), hEa]

theorem rec_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f q : Word) (D : Nat)
    (cv : IConstantVal) (rls : List IRecRule) (kw w5 w6 w7 w8 : Word) (r : List Word) (m' : Mem)
    (hD : ArenaD m a) (hP : PMemoR m pm) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hts : erecTop m ≤ (m.arr64 EREC).size)
    (hcv : decCV (preE m D) (q.toNat + 1) = some cv) (hkw : (m.arr64 EREC)[q.toNat]? = some kw)
    (h5 : (m.arr64 EREC)[q.toNat + 5]? = some w5) (h6 : (m.arr64 EREC)[q.toNat + 6]? = some w6)
    (h7 : (m.arr64 EREC)[q.toNat + 7]? = some w7) (h8 : (m.arr64 EREC)[q.toNat + 8]? = some w8)
    (hrls : decRules (preE m D) w7.toNat w8.toNat = some rls)
    (hqD : q.toNat + 9 ≤ D) (hDt : D ≤ erecTop m)
    (hc : callW p n "pci_rec" [f, q] m = some (r, m')) :
    ArmOk m a r m' 9 kw
      (fun (x : IConstantVal × List IRecRule) a' pm' => ∃ (a1 : AState) (pm1 : PMemo),
        (promoteCV pm f.toNat cv).run a = .ok ((pm1, x.1), a1) ∧
        (promoteRules pm1 f.toNat rls).run a1 = .ok ((pm', x.2), a'))
      (fun x M d => decCV (erecP M) (d + 1) = some x.1 ∧ nat? (erecP M) (d + 5) = some w5.toNat ∧
        nat? (erecP M) (d + 6) = some w6.toNat ∧ nat? (erecP M) (d + 8) = some w8.toNat ∧
        ∃ pw : Nat, nat? (erecP M) (d + 7) = some pw ∧ decRules (erecP M) pw w8.toNat = some x.2) := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (pciRec_spec p hp n ⟨m, Locals.init []⟩ f q) hc
  simp only at hW
  rw [hs'] at hW
  simp only [recW, pciMkC] at hW
  cases n with
  | zero => simp only [callW_zero', Option.bind_none] at hW; cases hW
  | succ n =>
  have e1 : (q + 1).toNat = q.toNat + 1 := toNat_add1 _ (by omega)
  have e5 : (q + 5).toNat = q.toNat + 5 := toNat_add5 _ (by omega)
  obtain ⟨⟨ra, m0⟩, hrd, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hm0, hr0, -⟩ := rd4_call p hp hrd
  obtain rfl := hm0.symm
  rw [rd4W_of hsz (by rw [e5]; simpa using h5) (by rw [e5]; simpa using h6)
    (by rw [e5]; simpa using h7) (by rw [e5]; simpa using h8)] at hr0
  subst hr0
  simp only [g0, g1, g2, g3, List.headD_cons, List.tail_cons] at hW
  obtain ⟨⟨c, m₁⟩, hca, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨a1, pm1, cv', hrun1, hD1, hP1, hCV, hg1, hts1, hcp1, hfr1, htk1⟩ :=
    cv_rel p hp (n + 1) m a pm f (q + 1) cv c m₁ hD hP
      (by rw [e1]; exact (preE_mono m hDt).decCV hcv) hsz hca
  have hsz1 : (m₁.arr64 EREC).size < 2 ^ 64 := by rw [hg1.2.2]; exact hsz
  cases hmk : callW p (n + 1) "pci_mk" [q, 9, g0 c, g1 c, g2 c, g3 c] m₁ with
  | none => rw [hmk] at hW; cases hW
  | some x =>
  obtain ⟨dl, m₂⟩ := x
  rw [hmk] at hW
  simp only [Option.bind_some] at hW
  have hkw1 : (m₁.arr64 EREC)[q.toNat]? = some kw := by
    rw [hg1.2.1 _ (by omega)]; exact hkw
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := mk_decode p hp (n := n) hCV (ArrExt.refl _) (Nat.le_refl _)
    hts1 hsz1 hkw1 (by simp only [show ((9 : Word)).toNat = 9 from rfl]; omega) hmk
  simp only [show ((9 : Word)).toNat = 9 from rfl] at b2
  have hsz2 : (m₂.arr64 EREC).size < 2 ^ 64 := by rw [b3.2.2]; exact hsz1
  have e5d : (dl.headD 0 + 5).toNat = erecTop m₁ + 5 := by
    rw [toNat_add5 _ (by omega)]; omega
  obtain ⟨⟨bl, m₃⟩, hbl, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨c60, u1, u2, u3, u4, u5, u6, u7, u8, u9⟩ := recBlock_rel p hp (d5 := dl.headD 0 + 5)
    hsz2 (by rw [e5d, b2]; omega) b5 hbl
  rw [e5d] at u3 u6 u7 u8 u9
  have hsz3 : (m₃.arr64 EREC).size < 2 ^ 64 := by rw [u3.2.2]; exact hsz2
  obtain ⟨⟨z, m₄⟩, hpr, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hr, hm4⟩ := Prod.mk.inj (Option.some.inj hW)
  subst hm4
  obtain ⟨hDf, hPf⟩ := arenaD_erec129 hD1 hP1 b4
  obtain ⟨hDg, hPg⟩ := arenaD_erec129 hDf hPf u4
  have hg02 : ErecGrow m m₂ := hg1.trans b3
  have h01 : erecTop m ≤ erecTop m₁ := hg1.1
  have hlow : ArrExt (preE m D) (preE m₃ D) := preE_ext (fun i hi => by
    rw [u3.2.1 i (by omega) (by omega)]; exact hg02.2.1 i (by omega))
  have hgb : SlotGrow m₂ m₃ (erecTop m₁ + 5) (erecTop m₁ + 5 + 4) := u3
  by_cases hl0 : w8 = 0
  · have hm : m₃ = m₄ := (rules_zero_gen p hp hl0 hpr).symm
    subst hm
    have hl0' : w8.toNat = 0 := by rw [hl0]; rfl
    rw [hl0'] at hrls
    simp only [decRules, List.range_zero, List.mapM_nil, Option.pure_def, Option.some.injEq] at hrls
    subst hrls
    have hg3 : ErecGrow m₁ m₃ :=
      ((SlotGrow.of_grow b3 (erecTop m₁ + 5) (erecTop m₁ + 5 + 4)).trans hgb (Nat.le_refl _)
        (Nat.le_refl _)).toGrow (by omega)
    refine ⟨a1, pm1, (cv', []), ⟨a1, pm1, hrun1, ?_⟩, hDg, hPg, hcp1, ?_,
      htk1.trans ((TierKeep.of_frame b4 (by simp)).trans (TierKeep.of_frame u4 (by simp))), hg1.trans hg3, u5,
      erecTop m₁, ?_, hg1.1, ?_, ?_, ?_⟩
    · rw [promoteRules_nil]; rfl
    · exact (hfr1.trans (b4.mono (by simp) (by simp))).trans (u4.mono (by simp) (by simp))
    · rw [← hr]; exact b1
    · rw [u2, b2]; omega
    · have h1 : (m₃.arr64 EREC)[erecTop m₁]? = (m₂.arr64 EREC)[erecTop m₁]? :=
        hgb.2.1 _ (by omega) (Or.inl (by omega))
      rw [h1]; exact b6
    · have hts3 : erecTop m₃ ≤ (m₃.arr64 EREC).size := u5
      have N : ∀ {i : Nat} {w : Word}, i < erecTop m₃ → (m₃.arr64 EREC)[i]? = some w →
          nat? (erecP m₃) i = some w.toNat := fun hi h => nat?_of_pre hi h
      refine ⟨b7.2 m₃ _ hgb b5 hts3, N (by omega) (by simpa using u6), N (by omega) (by simpa using u7),
        N (by omega) (by simpa using u9), (bl.headD 0).toNat, N (by omega) (by simpa using u8), ?_⟩
      rw [hl0']; simp [decRules]
  · have hbnd := decRules_bound _ _ _ _ hrls
    have hsD : w7.toNat + 11 * w8.toNat ≤ D := by
      rcases hbnd with h0 | h0
      · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hl0
      · have := preE_size_le m D; omega
    obtain ⟨a3, pm3, rls', hrun3, hD3, hP3, hcp3, hfr3, htk3, hgs3, hts3, hdr3⟩ :=
      rules_rel p hp (n + 1) m₃ a1 pm1 f w7 w8 (bl.headD 0) D rls z m₄ hDg hPg hsz3 u5
        (hlow.decRules hrls) hsD (by omega) (by omega) (by omega) hpr
    have hjoin : SlotGrow m₂ m₄ (erecTop m₁ + 5) ((bl.headD 0).toNat + 11 * w8.toNat) :=
      (hgb.widen (Nat.le_refl _) (show erecTop m₁ + 5 + 4 ≤ (bl.headD 0).toNat by omega)).join hgs3
        (by omega) (by omega)
    have hg4 : ErecGrow m m₄ :=
      ((SlotGrow.of_grow hg02 (erecTop m₁ + 5) ((bl.headD 0).toNat + 11 * w8.toNat)).trans hjoin
        (Nat.le_refl _) (Nat.le_refl _)).toGrow (by omega)
    have hts2' : erecTop m₂ ≤ (m₂.arr64 EREC).size := b5
    have N : ∀ {i : Nat} {w : Word}, i < erecTop m₄ → (m₄.arr64 EREC)[i]? = some w →
        nat? (erecP m₄) i = some w.toNat := fun hi h => nat?_of_pre hi h
    have key : ∀ j, j < 4 → (m₄.arr64 EREC)[erecTop m₁ + 5 + j]? = (m₃.arr64 EREC)[erecTop m₁ + 5 + j]? :=
      fun j hj => hgs3.2.1 _ (by omega) (Or.inl (by omega))
    have hT3 : erecTop m₃ = erecTop m₂ + 11 * w8.toNat := by rw [u2]
    refine ⟨a3, pm3, (cv', rls'), ⟨a1, pm1, hrun1, hrun3⟩, hD3, hP3, hcp3.trans hcp1, ?_,
      htk1.trans ((TierKeep.of_frame b4 (by simp)).trans ((TierKeep.of_frame u4 (by simp)).trans htk3)), hg4, hts3,
      erecTop m₁, ?_, hg1.1, ?_, ?_, ?_⟩
    · exact ((hfr1.trans (b4.mono (by simp) (by simp))).trans (u4.mono (by simp) (by simp))).trans hfr3
    · rw [← hr]; exact b1
    · have := hgs3.1; omega
    · rw [hjoin.2.1 _ (by omega) (Or.inl (by omega))]; exact b6
    · refine ⟨b7.2 m₄ _ hjoin b5 hts3, N (by have := hgs3.1; omega) ?_, N (by have := hgs3.1; omega) ?_,
        N (by have := hgs3.1; omega) ?_, (bl.headD 0).toNat, N (by have := hgs3.1; omega) ?_, ?_⟩
      · have := key 0 (by omega); simp only [Nat.add_zero] at this; rw [this]; simpa using u6
      · have := key 1 (by omega); rw [show erecTop m₁ + 5 + 1 = erecTop m₁ + 6 from rfl] at this
        rw [show erecTop m₁ + 6 = erecTop m₁ + 5 + 1 from rfl, this]; simpa using u7
      · have := key 3 (by omega); rw [show erecTop m₁ + 5 + 3 = erecTop m₁ + 8 from rfl] at this
        rw [this]; simpa using u9
      · have := key 2 (by omega); rw [show erecTop m₁ + 5 + 2 = erecTop m₁ + 7 from rfl] at this
        rw [this]; simpa using u8
      · exact hdr3

end rel

end L.Arena
