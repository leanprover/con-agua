import ConAgua.Arena.PromoteCIRef2

/-!
# `promote_fire` refines `promoteFire`; the stores as relations
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

theorem stP_nat (d : Word) (ps : List (Word × Word)) {m m' : Mem}
    (hlt : ∀ q ∈ ps, d.toNat + q.1.toNat < 2 ^ 64) (hnd : (ps.map (fun q => q.1.toNat)).Nodup)
    (h : stP d m ps = some m') :
    (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ MemFrame [EREC] [] m m' ∧
    (∀ i, (∀ q ∈ ps, d.toNat + q.1.toNat ≠ i) → (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
    (∀ q ∈ ps, d.toNat + q.1.toNat < (m.arr64 EREC).size) ∧
    (∀ q ∈ ps, (m'.arr64 EREC)[d.toNat + q.1.toNat]? = some q.2) := by
  have e : ∀ q ∈ ps, (d + q.1).toNat = d.toNat + q.1.toNat := by
    intro q hq; rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (hlt q hq)
  have hpw : ps.Pairwise (fun a b => (d + a.1).toNat ≠ (d + b.1).toNat) := by
    have := List.pairwise_map.mp hnd
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) this
    rw [e a ha, e b hb]; omega
  obtain ⟨h1, h2, h3, h4, h5⟩ := stP_facts d ps m m' hpw h
  refine ⟨h1, h2, fun i hi => h3 i (fun q hq => by rw [e q hq]; exact hi q hq), fun q hq => ?_,
    fun q hq => ?_⟩
  · have := h4 q hq; rwa [e q hq] at this
  · have := h5 q hq; rwa [e q hq] at this

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem wr1_call {n : Nat} {d a : Word} {m m' : Mem} {r : List Word}
    (hc : callW p n "erec_wr1" [d, a] m = some (r, m')) :
    stP d m [((0 : Word), a)] = some m' := by
  obtain ⟨s', rfl, -, hW⟩ := callW_triple (erecWr1_spec p hp n ⟨m, Locals.init []⟩ d a) hc; exact hW

theorem wr2_call {n : Nat} {d a b : Word} {m m' : Mem} {r : List Word}
    (hc : callW p n "erec_wr2" [d, a, b] m = some (r, m')) :
    stP d m [((0 : Word), a), ((1 : Word), b)] = some m' := by
  obtain ⟨s', rfl, -, hW⟩ := callW_triple (erecWr2_spec p hp n ⟨m, Locals.init []⟩ d a b) hc; exact hW

theorem wr3_call {n : Nat} {d a b c : Word} {m m' : Mem} {r : List Word}
    (hc : callW p n "erec_wr3" [d, a, b, c] m = some (r, m')) :
    stP d m [((0 : Word), a), ((1 : Word), b), ((2 : Word), c)] = some m' := by
  obtain ⟨s', rfl, -, hW⟩ := callW_triple (erecWr3_spec p hp n ⟨m, Locals.init []⟩ d a b c) hc; exact hW

theorem wr4_call {n : Nat} {d a b c e : Word} {m m' : Mem} {r : List Word}
    (hc : callW p n "erec_wr4" [d, a, b, c, e] m = some (r, m')) :
    stP d m [((0 : Word), a), ((1 : Word), b), ((2 : Word), c), ((3 : Word), e)] = some m' := by
  obtain ⟨s', rfl, -, hW⟩ := callW_triple (erecWr4_spec p hp n ⟨m, Locals.init []⟩ d a b c e) hc; exact hW

theorem wr5_call {n : Nat} {d a b c e g : Word} {m m' : Mem} {r : List Word}
    (hc : callW p n "erec_wr5" [d, a, b, c, e, g] m = some (r, m')) :
    stP d m [((0 : Word), a), ((1 : Word), b), ((2 : Word), c), ((3 : Word), e), ((4 : Word), g)] = some m' := by
  obtain ⟨s', rfl, -, hW⟩ := callW_triple (erecWr5_spec p hp n ⟨m, Locals.init []⟩ d a b c e g) hc; exact hW

theorem capsWr_call {n : Nat} {d c a k : Word} {m m' : Mem} {r : List Word}
    (hc : callW p n "caps_wr" [d, c, a, k] m = some (r, m')) :
    stP d m [((1 : Word), c), ((10 : Word), a), ((13 : Word), k)] = some m' := by
  obtain ⟨s', rfl, -, hW⟩ := callW_triple (capsWr_spec p hp n ⟨m, Locals.init []⟩ d c a k) hc; exact hW

theorem projWr_call {n : Nat} {d sn lp c ss bs gs : Word} {m m' : Mem} {r : List Word}
    (hc : callW p n "proj_wr" [d, sn, lp, c, ss, bs, gs] m = some (r, m')) :
    stP d m [((2 : Word), sn), ((3 : Word), lp), ((6 : Word), c),
      ((8 : Word), ss), ((9 : Word), bs), ((11 : Word), gs)] = some m' := by
  obtain ⟨s', rfl, -, hW⟩ := callW_triple (projWr_spec p hp n ⟨m, Locals.init []⟩ d sn lp c ss bs gs) hc; exact hW

/-- **A promoted firing mode's five words** denote `fire` in the pool `A`. -/
def FireWords (A : Array Word) (k q b r y : Word) (fire : IRecRuleFire) : Prop :=
  (k = 0 ∧ fire = IRecRuleFire.plain) ∨
  (k = 1 ∧ ∃ lv ps, fire = IRecRuleFire.nested lv ps ∧ hslice? A q.toNat b.toNat = some lv ∧
    hslice? A r.toNat y.toNat = some ps)

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
    rw [if_pos (by simp [g0])] at hW
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
    rw [if_neg (by simp [g0])] at hW
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
