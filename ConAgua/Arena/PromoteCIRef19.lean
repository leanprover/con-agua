import ConAgua.Arena.PromoteCIRef18

/-!
# The constant arms: `pci_ind`, and the rules block of `pci_rec`
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

theorem decRules_bound : ∀ (c : Nat) (a : Array Word) (off : Nat) (rls : List IRecRule),
    decRules a off c = some rls → c = 0 ∨ off + 11 * c ≤ a.size := by
  intro c
  induction c with
  | zero => intro a off rls _; exact .inl rfl
  | succ c ih =>
    intro a off rls h
    right
    rw [decRules_succ] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨r0, hr0, rs, hrs, -⟩ := h
    obtain ⟨w0, w1, w2, w8, w9, w10, -, -, -, -, -, -, -, -, -, -, -, -, e10, -⟩ := pmDecRule_words hr0
    have := (Array.getElem?_eq_some_iff.mp e10).1
    rcases ih a (off + 11) rs hrs with h0 | h0
    · subst h0; omega
    · omega

theorem toNat_mul11 (l : Word) (h : l.toNat < 2 ^ 60) : (11 * l).toNat = 11 * l.toNat := by
  rw [UInt64.toNat_mul, show (11 : Word).toNat = 11 from rfl]
  exact Nat.mod_eq_of_lt (by omega)

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem ind_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f q : Word) (D : Nat)
    (dn : NIdx → Option ConLeche.Name) (cv : IConstantVal) (caps : IIndCaps) (kw : Word)
    (r : List Word) (m' : Mem) (hD : ArenaD m a) (hP : PMemoR m pm)
    (hsz : (m.arr64 EREC).size < 2 ^ 64) (hts : erecTop m ≤ (m.arr64 EREC).size)
    (hcv : decCV (preE m D) (q.toNat + 1) = some cv)
    (hcaps : decCaps (preE m D) dn (q.toNat + 5) = some caps)
    (hkw : (m.arr64 EREC)[q.toNat]? = some kw) (hqD : q.toNat + 20 ≤ D) (hDt : D ≤ erecTop m)
    (hc : callW p n "pci_ind" [f, q] m = some (r, m')) :
    ArmOk m a r m' 20 kw
      (fun (x : IConstantVal × IIndCaps) a' pm' => ∃ (a1 : AState) (pm1 : PMemo),
        (promoteCV pm f.toNat cv).run a = .ok ((pm1, x.1), a1) ∧
        (promoteCaps pm1 f.toNat caps).run a1 = .ok ((pm', x.2), a'))
      (fun x M d => decCV (erecP M) (d + 1) = some x.1 ∧ decCaps (erecP M) dn (d + 5) = some x.2) := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (pciInd_spec p hp n ⟨m, Locals.init []⟩ f q) hc
  simp only at hW
  rw [hs'] at hW
  simp only [indW, pciMkC] at hW
  cases n with
  | zero => simp only [callW_zero', Option.bind_none] at hW; cases hW
  | succ n =>
  have e1 : (q + 1).toNat = q.toNat + 1 := toNat_add1 _ (by omega)
  have e5 : (q + 5).toNat = q.toNat + 5 := toNat_add5 _ (by omega)
  obtain ⟨⟨c, m₁⟩, hca, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨a1, pm1, cv', hrun1, hD1, hP1, hCV, hg1, hts1, hcp1, hfr1, htk1⟩ :=
    cv_rel p hp (n + 1) m a pm f (q + 1) cv c m₁ hD hP
      (by rw [e1]; exact (preE_mono m hDt).decCV hcv) hsz hca
  have hsz1 : (m₁.arr64 EREC).size < 2 ^ 64 := by rw [hg1.2.2]; exact hsz
  cases hmk : callW p (n + 1) "pci_mk" [q, 20, g0 c, g1 c, g2 c, g3 c] m₁ with
  | none => rw [hmk] at hW; cases hW
  | some x =>
  obtain ⟨dl, m₂⟩ := x
  rw [hmk] at hW
  simp only [Option.bind_some] at hW
  have hkw1 : (m₁.arr64 EREC)[q.toNat]? = some kw := by
    rw [hg1.2.1 _ (by omega)]; exact hkw
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := mk_decode p hp (n := n) hCV (ArrExt.refl _) (Nat.le_refl _)
    hts1 hsz1 hkw1 (by simp only [show ((20 : Word)).toNat = 20 from rfl]; omega) hmk
  simp only [show ((20 : Word)).toNat = 20 from rfl] at b2
  have hsz2 : (m₂.arr64 EREC).size < 2 ^ 64 := by rw [b3.2.2]; exact hsz1
  have e5d : (dl.headD 0 + 5).toNat = erecTop m₁ + 5 := by
    rw [toNat_add5 _ (by omega)]; omega
  obtain ⟨⟨z, m₃⟩, hcc, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hDf, hPf⟩ := arenaD_erec129 hD1 hP1 b4
  have hg02 : ErecGrow m m₂ := hg1.trans b3
  have hlow : ArrExt (preE m D) (preE m₂ D) := preE_ext (fun i hi => hg02.2.1 i (by omega))
  obtain ⟨a3, pm3, caps', hrun3, hD3, hP3, hcp3, hfr3, htk3, hgs, hts3, hdc⟩ :=
    caps_rel p hp (n + 1) m₂ a1 pm1 f (q + 5) (dl.headD 0 + 5) D dn caps z m₃ hDf hPf hsz2 b5
      (by rw [e5]; exact hlow.decCaps hcaps) (by rw [e5]; omega) (by have := hg02.1; omega)
      (by rw [e5d]; have := hg1.1; omega) (by rw [e5d, b2]; omega) hcc
  rw [e5d] at hgs hdc
  obtain ⟨hr, hm3⟩ := Prod.mk.inj (Option.some.inj hW)
  subst hm3
  have hg3 : ErecGrow m₁ m₃ :=
    ((SlotGrow.of_grow b3 (erecTop m₁ + 5) (erecTop m₁ + 5 + 15)).trans hgs (Nat.le_refl _)
      (Nat.le_refl _)).toGrow (by omega)
  refine ⟨a3, pm3, (cv', caps'), ⟨a1, pm1, hrun1, hrun3⟩, hD3, hP3, hcp3.trans hcp1, ?_,
    htk1.trans ((TierKeep.of_frame b4 (by simp)).trans htk3), hg1.trans hg3, hts3, erecTop m₁, ?_, hg1.1, ?_, ?_, ?_⟩
  · exact (hfr1.trans (b4.mono (by simp) (by simp))).trans hfr3
  · rw [← hr]; exact b1
  · have := hgs.1; omega
  · have h1 : (m₃.arr64 EREC)[erecTop m₁]? = (m₂.arr64 EREC)[erecTop m₁]? := hgs.2.1 _ (by omega) (Or.inl (by omega))
    rw [h1]; exact b6
  · exact ⟨b7.2 m₃ _ hgs b5 hts3, hdc⟩

end rel

end L.Arena
