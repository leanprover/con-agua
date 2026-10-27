import ConAgua.Arena.PromoteCIRef.DecRuleMk
import ConAgua.Arena.PromoteCIRef.StPNat

/-!
# Fire

`nat?_pre`, `hlist?_pre`, `getElem?_some_of_lt`, `fire_rel`.
-/

section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## Decoding stored words -/

theorem nat?_pre {m : Mem} {D i k : Nat} (h : nat? (preE m D) i = some k) :
    ∃ w, (m.arr64 EREC)[i]? = some w ∧ w.toNat = k ∧ i < D := by
  simp only [nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h
  obtain ⟨hi, hw'⟩ := preE_get_lt hw
  exact ⟨w, hw', rfl, hi⟩

theorem hlist?_pre {m : Mem} {D i : Nat} {k : IdxKind} {xs : List (Idx k)}
    (h : hlist? (preE m D) i = some xs) :
    ∃ wo wl : Word, (m.arr64 EREC)[i]? = some wo ∧ (m.arr64 EREC)[i + 1]? = some wl ∧
      hslice? (preE m D) wo.toNat wl.toNat = some xs := by
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨o, ho, l, hl, hs⟩ := h
  obtain ⟨wo, h1, rfl, -⟩ := nat?_pre ho
  obtain ⟨wl, h2, rfl, -⟩ := nat?_pre hl
  exact ⟨wo, wl, h1, h2, hs⟩

theorem getElem?_some_of_lt (a : Array Word) {i : Nat} (h : i < a.size) : ∃ w, a[i]? = some w :=
  ⟨a[i], Array.getElem?_eq_getElem h⟩

end L.Arena

end

section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

/-- **`promote_fire` refines `promoteFire`**: a rule record at `s` (decoded below `D`), its firing
mode promoted into five words. -/
theorem fire_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f s : Word) (D : Nat)
    (fire : IRecRuleFire) (r : List Word) (m' : Mem) (hD : ArenaD m a) (hP : PMemoR m pm)
    (hsz : (m.arr64 EREC).size < 2 ^ 64) (hts : erecTop m ≤ (m.arr64 EREC).size)
    (hsrc : decFire (preE m D) s.toNat = some fire) (hsD : s.toNat + 11 ≤ D) (hDt : D ≤ erecTop m)
    (hc : callW p n "promote_fire" [f, s] m = some (r, m')) :
    ∃ a' pm' fire', (promoteFire pm f.toNat fire).run a = .ok ((pm', fire'), a') ∧
      ArenaD m' a' ∧ PMemoR m' pm' ∧ cp a' = cp a ∧
      MemFrame (EREC :: eArrs) (129 :: eCtl) m m' ∧ TierKeep m m' ∧ ErecGrow m m' ∧
      erecTop m' ≤ (m'.arr64 EREC).size ∧
      FireWords (erecP m') (g0 r) (g1 r) (g2 r) (g3 r) (g4 r) fire' ∧
      (g0 r = 1 → erecTop m ≤ (g1 r).toNat ∧ erecTop m ≤ (g3 r).toNat) := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (promoteFire_spec p hp n ⟨m, Locals.init []⟩ f s) hc
  simp only at hW
  rw [hs'] at hW
  simp only [fireW] at hW
  have hbd : s.toNat + 7 < (m.arr64 EREC).size := by omega
  obtain ⟨w3, h3⟩ := getElem?_some_of_lt (m.arr64 EREC) (i := s.toNat + 3) (by omega)
  obtain ⟨w4, h4⟩ := getElem?_some_of_lt (m.arr64 EREC) (i := s.toNat + 4) (by omega)
  obtain ⟨w5, h5⟩ := getElem?_some_of_lt (m.arr64 EREC) (i := s.toNat + 5) (by omega)
  obtain ⟨w6, h6⟩ := getElem?_some_of_lt (m.arr64 EREC) (i := s.toNat + 6) (by omega)
  obtain ⟨w7, h7⟩ := getElem?_some_of_lt (m.arr64 EREC) (i := s.toNat + 7) (by omega)
  have e3 : (s + 3).toNat = s.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  have hrd : rd5W m (s + 3) = [w3, w4, w5, w6, w7] :=
    rd5W_of hsz (by rw [e3]; exact h3) (by rw [e3]; exact h4) (by rw [e3]; exact h5)
      (by rw [e3]; exact h6) (by rw [e3]; exact h7)
  obtain ⟨⟨r₀, m₁⟩, hca, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hm1, hr0, -⟩ := rd5_call p hp hca
  obtain rfl := hm1.symm
  rw [hrd] at hr0
  subst hr0
  unfold decFire at hsrc
  cases hk : nat? (preE m D) (s.toNat + 3) with
  | none => rw [hk] at hsrc; simp at hsrc
  | some k =>
  obtain ⟨w3', h3', hk3, -⟩ := nat?_pre hk
  have hw3 : w3' = w3 := Option.some.inj (h3'.symm.trans h3)
  subst hw3
  simp only [hk, Option.bind_eq_bind, Option.bind_some] at hsrc
  match k, hsrc, hk3 with
  | 0, hsrc, hk3 =>
    simp only [Option.some.injEq] at hsrc
    subst hsrc
    have hw : w3' = 0 := UInt64.toNat_inj.mp (by simpa using hk3)
    subst hw
    rw [ite_eq_left (by simp [g0])] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    subst hm
    refine ⟨a, pm, .plain, rfl, hD, hP, rfl, MemFrame.refl _ _ _, TierKeep.refl _, ErecGrow.refl _, hts, ?_, ?_⟩
    · rw [← hr]
      exact Or.inl ⟨rfl, rfl⟩
    · rw [← hr]
      intro h
      simp [g0] at h
  | 1, hsrc, hk3 =>
    have hw : w3' = 1 := UInt64.toNat_inj.mp (by simpa using hk3)
    subst hw
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at hsrc
    obtain ⟨lv, hlv, ps, hps, rfl⟩ := hsrc
    obtain ⟨wo, wl, hwo, hwl, hsl1⟩ := hlist?_pre hlv
    obtain ⟨wo', wl', hwo', hwl', hsl2⟩ := hlist?_pre hps
    have e4 : wo = w4 := Option.some.inj (hwo.symm.trans h4)
    have e5 : wl = w5 := Option.some.inj (hwl.symm.trans h5)
    have e6 : wo' = w6 := Option.some.inj (hwo'.symm.trans h6)
    have e7 : wl' = w7 := Option.some.inj (hwl'.symm.trans h7)
    subst e4 e5 e6 e7
    rw [ite_eq_right (by simp [g0])] at hW
    simp only [g0, g1, g2, g3, g4, List.headD_cons, List.tail_cons] at hW
    obtain ⟨⟨r₁, m₁⟩, hcb, hW⟩ := Option.bind_eq_some_iff.mp hW
    dsimp only at hW
    have hslr : hslice? (m.arr64 EREC) wo.toNat wl.toNat = some lv :=
      (erecP_ext m).hslice? ((preE_mono m hDt).hslice? hsl1)
    have hot : wo.toNat + wl.toNat ≤ erecTop m ∨ wl = 0 := by
      rcases hslice?_pre_le hsl1 with h0 | h0
      · right; exact UInt64.toNat_inj.mp (by simpa using h0)
      · left; omega
    obtain ⟨hq, ht, hts1, a1, pm1, us1, hrun1, hD1, hP1, hsl1', hag1, hsz1', hcp1, hfr1, htk1⟩ :=
      sliceL_rel p hp n m a pm f wo wl lv r₁ m₁ hD hP hslr hot hsz hcb
    have hg1 : ErecGrow m m₁ := ⟨by omega, fun i hi => hag1 i hi, hsz1'⟩
    have hpr : hslice? (m₁.arr64 EREC) wo'.toNat wl'.toNat = some ps :=
      (erecP_ext m₁).hslice? (hg1.ext.hslice? ((preE_mono m hDt).hslice? hsl2))
    have hot2 : wo'.toNat + wl'.toNat ≤ erecTop m₁ ∨ wl' = 0 := by
      rcases hslice?_pre_le hsl2 with h0 | h0
      · right; exact UInt64.toNat_inj.mp (by simpa using h0)
      · left; omega
    have hsz1 : (m₁.arr64 EREC).size < 2 ^ 64 := by rw [hsz1']; exact hsz
    obtain ⟨⟨r₂, m₂⟩, hcc, hW⟩ := Option.bind_eq_some_iff.mp hW
    dsimp only at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    subst hm
    obtain ⟨hq2, ht2, hts2, a2, pm2, us2, hrun2, hD2, hP2, hsl2', hag2, hsz2', hcp2, hfr2, htk2⟩ :=
      sliceE_rel p hp n m₁ a1 pm1 f wo' wl' ps r₂ m₂ hD1 hP1 hpr hot2 hsz1 hcc
    have hg2 : ErecGrow m₁ m₂ := ⟨by omega, fun i hi => hag2 i hi, hsz2'⟩
    have hq1v : (r₁.headD 0).toNat = erecTop m := by rw [hq]; rfl
    have hq2v : (r₂.headD 0).toNat = erecTop m₁ := by rw [hq2]; rfl
    refine ⟨a2, pm2, .nested us1 us2, ?_, hD2, hP2, hcp2.trans hcp1,
      hfr1.trans hfr2, htk1.trans htk2, hg1.trans hg2, hts2, ?_, ?_⟩
    · rw [promoteFire, run_bind_ok hrun1]
      simp only
      rw [run_bind_ok hrun2]; rfl
    · rw [← hr]
      simp only [g0, g1, g2, g3, g4, List.headD_cons, List.tail_cons]
      refine Or.inr ⟨rfl, us1, us2, rfl, ?_, ?_⟩
      · rw [hq1v]
        have h1 : hslice? (erecP m₁) (erecTop m) wl.toNat = some us1 := by
          rw [hslice?_erecP hts1 (by omega)]; exact hsl1'
        exact hg2.ext.hslice? h1
      · rw [hq2v, hslice?_erecP hts2 (by omega)]; exact hsl2'
    · intro _
      rw [← hr]
      simp only [g1, g3, List.headD_cons, List.tail_cons]
      exact ⟨by rw [hq1v]; exact Nat.le_refl _, by rw [hq2v]; omega⟩
  | k + 2, hsrc, _ => cases hsrc

end rel

end L.Arena

end
