import ConAgua.Arena.PromoteCIRef9

/-!
# `promote_caps` refines `promoteCaps`
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

theorem decCaps_words {a : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Nat}
    {caps : IIndCaps} (h : decCaps a dn q = some caps) :
    hd? a (q + 1) = some caps.etaCtor ∧ hlist? a (q + 10) = some caps.all ∧
      hlist? a (q + 13) = some caps.ctors ∧ decPW a dn (q + 7) = some caps.sortZ := by
  unfold decCaps at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨e1, h1, e2, h2, e3, h3, e4, h4, e5, h5, e6, h6, e7, h7, e8, h8, e9, h9, e10, h10,
    e11, h11, rfl⟩ := h
  exact ⟨h2, h9, h11, h8⟩

theorem promoteCaps_eq (pm : PMemo) (fuel : Nat) (c : IIndCaps) :
    promoteCaps pm fuel c = (do
      let (m, ct) ← promoteN pm fuel c.etaCtor
      let (m, al) ← promoteNList m fuel c.all
      let (m, cs) ← promoteNList m fuel c.ctors
      pure (m, { c with etaCtor := ct, all := al, ctors := cs })) := rfl

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem capsWr_rel' {n : Nat} {d c a k : Word} {m m' : Mem} {r : List Word}
    (hbd : d.toNat + 14 ≤ (m.arr64 EREC).size) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hc : callW p n "caps_wr" [d, c, a, k] m = some (r, m')) :
    (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ MemFrame [EREC] [] m m' ∧
    (∀ i, i ≠ d.toNat + 1 → i ≠ d.toNat + 10 → i ≠ d.toNat + 13 →
      (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
    (m'.arr64 EREC)[d.toNat + 1]? = some c ∧ (m'.arr64 EREC)[d.toNat + 10]? = some a ∧
    (m'.arr64 EREC)[d.toNat + 13]? = some k := by
  have h := capsWr_call p hp hc
  obtain ⟨h1, h2, h3, h4, h5⟩ := stP_nat d _ (by simp; omega) (by simp) h
  refine ⟨h1, h2, fun i hi1 hi2 hi3 => h3 i ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      show (((1 : Word)).toNat = 1) from rfl, show (((10 : Word)).toNat = 10) from rfl,
      show (((13 : Word)).toNat = 13) from rfl]
    omega
  · simpa using h5

theorem projWr_rel' {n : Nat} {d sn lp c ss bs gs : Word} {m m' : Mem} {r : List Word}
    (hbd : d.toNat + 12 ≤ (m.arr64 EREC).size) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hc : callW p n "proj_wr" [d, sn, lp, c, ss, bs, gs] m = some (r, m')) :
    (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ MemFrame [EREC] [] m m' ∧
    (∀ i, i ≠ d.toNat + 2 → i ≠ d.toNat + 3 → i ≠ d.toNat + 6 →
      i ≠ d.toNat + 8 → i ≠ d.toNat + 9 → i ≠ d.toNat + 11 →
      (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
    (m'.arr64 EREC)[d.toNat + 2]? = some sn ∧
    (m'.arr64 EREC)[d.toNat + 3]? = some lp ∧ (m'.arr64 EREC)[d.toNat + 6]? = some c ∧
    (m'.arr64 EREC)[d.toNat + 8]? = some ss ∧ (m'.arr64 EREC)[d.toNat + 9]? = some bs ∧
    (m'.arr64 EREC)[d.toNat + 11]? = some gs := by
  have h := projWr_call p hp hc
  obtain ⟨h1, h2, h3, h4, h5⟩ := stP_nat d _ (by simp; omega) (by simp) h
  refine ⟨h1, h2, fun i hi2 hi3 hi4 hi5 hi6 hi7 => h3 i ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      show (((2 : Word)).toNat = 2) from rfl,
      show (((3 : Word)).toNat = 3) from rfl, show (((6 : Word)).toNat = 6) from rfl,
      show (((8 : Word)).toNat = 8) from rfl, show (((9 : Word)).toNat = 9) from rfl,
      show (((11 : Word)).toNat = 11) from rfl]
    omega
  · simpa using h5

theorem caps_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f s d : Word) (D : Nat)
    (dn : NIdx → Option ConLeche.Name) (caps : IIndCaps) (r : List Word) (m' : Mem)
    (hD : ArenaD m a) (hP : PMemoR m pm)
    (hsz : (m.arr64 EREC).size < 2 ^ 64) (hts : erecTop m ≤ (m.arr64 EREC).size)
    (hcaps : decCaps (preE m D) dn s.toNat = some caps) (hsD : s.toNat + 15 ≤ D)
    (hDt : D ≤ erecTop m) (hdD : D ≤ d.toNat) (hdT : d.toNat + 15 ≤ erecTop m)
    (hc : callW p n "promote_caps" [f, s, d] m = some (r, m')) :
    ∃ a' pm' caps', (promoteCaps pm f.toNat caps).run a = .ok ((pm', caps'), a') ∧
      ArenaD m' a' ∧ PMemoR m' pm' ∧ cp a' = cp a ∧
      MemFrame (EREC :: eArrs) (129 :: eCtl) m m' ∧ TierKeep m m' ∧ SlotGrow m m' d.toNat (d.toNat + 15) ∧
      erecTop m' ≤ (m'.arr64 EREC).size ∧ decCaps (erecP m') dn d.toNat = some caps' := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (promoteCaps_spec p hp n ⟨m, Locals.init []⟩ f s d) hc
  simp only at hW
  rw [hs'] at hW
  simp only [capsW] at hW
  cases n with
  | zero => simp only [callW_zero', Option.bind_none] at hW; cases hW
  | succ n =>
  obtain ⟨hec, hall, hcts, hsortz⟩ := decCaps_words hcaps
  -- the parts
  obtain ⟨⟨cr, m₃⟩, hca, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨s1, hs1, -, hW1⟩ := callW_triple (capsParts_spec p hp n ⟨m, Locals.init []⟩ f s) hca
  rw [hs1] at hW1
  simp only [capsPW] at hW1
  have e1 : (s + 1).toNat = s.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have e10 : (s + 10).toNat = s.toNat + 10 := by rw [UInt64.toNat_add]; simp; omega
  have e13 : (s + 13).toNat = s.toNat + 13 := by rw [UInt64.toNat_add]; simp; omega
  -- name
  have hd1 : hd? (erecP m) (s + 1).toNat = some caps.etaCtor := by
    rw [e1]; exact (preE_mono m hDt).hd? hec
  obtain ⟨⟨c, m₁⟩, hcb, hW1⟩ := Option.bind_eq_some_iff.mp hW1
  dsimp only at hW1
  obtain ⟨a1, pm1, hrun1, hD1, hP1, hpw1, hcp1, hfr1, htk1⟩ :=
    pnAt_rel p hp n m a pm f (s + 1) caps.etaCtor c m₁ hD hP hsz hd1 hcb
  obtain ⟨hE1, hT1⟩ := eFrame_erec hfr1
  have hsz1 : (m₁.arr64 EREC).size < 2 ^ 64 := by rw [hE1]; exact hsz
  have hP1' : erecP m₁ = erecP m := by rw [erecP_eq_preE, erecP_eq_preE, hT1]; exact preE_congr hE1 _
  -- all
  have hl10 : hlist? (erecP m₁) (s + 10).toNat = some caps.all := by
    rw [hP1', e10]; exact (preE_mono m hDt).hlist? hall
  obtain ⟨⟨x1, m₂⟩, hcc, hW1⟩ := Option.bind_eq_some_iff.mp hW1
  dsimp only at hW1
  obtain ⟨wo1, wl1, hn1, hn1', hsl1, a2, pm2, al', hrun2, hD2, hP2, hcp2, hfr2, hq2, hg2, hT2, hts2,
    hsl2, htk2⟩ := psAt0_rel p hp n m₁ a1 pm1 f (s + 10) caps.all x1 m₂ hD1 hP1 hsz1 hl10 hcc
  have hsz2 : (m₂.arr64 EREC).size < 2 ^ 64 := by rw [hg2.2.2]; exact hsz1
  -- ctors
  have hl13 : hlist? (erecP m₂) (s + 13).toNat = some caps.ctors := by
    rw [e13]
    exact hg2.ext.hlist? (by rw [hP1']; exact (preE_mono m hDt).hlist? hcts)
  cases hcd : callW p n "ps_at" [0, f, s + 13] m₂ with
  | none => rw [hcd] at hW1; cases hW1
  | some x =>
  obtain ⟨x2, m₃'⟩ := x
  rw [hcd] at hW1
  simp only [Option.bind_some] at hW1
  obtain ⟨wo2, wl2, hn2, hn2', hsl2', a3, pm3, cs', hrun3, hD3, hP3, hcp3, hfr3, hq3, hg3, hT3, hts3,
    hsl3, htk3⟩ := psAt0_rel p hp n m₂ a2 pm2 f (s + 13) caps.ctors x2 m₃' hD2 hP2 hsz2 hl13 hcd
  obtain ⟨hlist, hm3⟩ := Prod.mk.inj (Option.some.inj hW1)
  subst hm3
  obtain ⟨hc0, hrest⟩ := List.cons.inj hlist
  obtain ⟨hx0, hrest2⟩ := List.cons.inj hrest
  obtain ⟨hy0, -⟩ := List.cons.inj hrest2
  rw [← hc0, ← hx0, ← hy0] at hW
  have hE3m : ∀ i < erecTop m, (m₃'.arr64 EREC)[i]? = (m.arr64 EREC)[i]? := fun i hi => by
    rw [hg3.2.1 i (by rw [hT2, hT1]; omega), hg2.2.1 i (by rw [hT1]; exact hi), hE1]
  have hsz3 : (m₃'.arr64 EREC).size = (m.arr64 EREC).size := by rw [hg3.2.2, hg2.2.2, hE1]
  have hg03 : ErecGrow m m₃' :=
    ⟨by rw [← hT1]; exact Nat.le_trans hg2.1 hg3.1, hE3m, hsz3⟩
  have hts3' : erecTop m₃' ≤ (m₃'.arr64 EREC).size := hts3
  -- the copy
  obtain ⟨⟨z, m₄⟩, hce, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨k1, k2, k3, k4⟩ := cp_rel p hp (n + 1) m₃' d s 15 z m₄ (by simp only [show ((15 : Word)).toNat = 15 from rfl]; omega)
    (by simp only [show ((15 : Word)).toNat = 15 from rfl]; omega) (by rw [hsz3]; exact hsz) hce
  simp only [show ((15 : Word)).toNat = 15 from rfl] at k3 k4
  cases hcf : callW p (n + 1) "caps_wr" [d, c.headD 0, x1.headD 0, x2.headD 0] m₄ with
  | none => rw [hcf] at hW; cases hW
  | some x =>
  obtain ⟨z2, m₅⟩ := x
  rw [hcf, memK_some] at hW
  have hm : m₅ = m' := Option.some.inj hW
  subst hm
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := capsWr_rel' p hp (d := d) (by rw [k1, hsz3]; omega)
    (by rw [k1, hsz3]; exact hsz) hcf
  have hT4 : erecTop m₄ = erecTop m₃' := by simp only [erecTop]; rw [k2.2.1 129 (by simp)]
  have hT5 : erecTop m₅ = erecTop m₃' := by
    simp only [erecTop]; rw [w2.2.1 129 (by simp), k2.2.1 129 (by simp)]
  have hsz5 : (m₅.arr64 EREC).size = (m₃'.arr64 EREC).size := by rw [w1, k1]
  have hun : ∀ i, (i < d.toNat ∨ d.toNat + 15 ≤ i) → (m₅.arr64 EREC)[i]? = (m₃'.arr64 EREC)[i]? :=
    fun i hi => by rw [w3 i (by omega) (by omega) (by omega), k3 i (by omega)]
  have hgr : SlotGrow m₃' m₅ d.toNat (d.toNat + 15) :=
    ⟨by rw [hT5]; exact Nat.le_refl _, fun i _ hout => hun i hout, hsz5⟩
  have hgrm : SlotGrow m m₅ d.toNat (d.toNat + 15) :=
    (SlotGrow.of_grow hg03 _ _).trans hgr (Nat.le_refl _) (Nat.le_refl _)
  have hts5 : erecTop m₅ ≤ (m₅.arr64 EREC).size := by rw [hT5, hsz5]; exact hts3'
  have hT3m : erecTop m ≤ erecTop m₃' := hg03.1
  obtain ⟨hDf, hPf⟩ := arenaD_erecFrame hD3 hP3 (k2.trans w2)
  have hwd : ∀ i, i < 15 → i ≠ 1 → i ≠ 10 → i ≠ 13 →
      (erecP m₅)[d.toNat + i]? = (preE m D)[s.toNat + i]? := by
    intro i hi h1 h10 h13
    have a1 : (erecP m₅)[d.toNat + i]? = (m₅.arr64 EREC)[d.toNat + i]? :=
      erecP_getElem m₅ _ (by omega) hts5
    have a2 : (preE m D)[s.toNat + i]? = (m.arr64 EREC)[s.toNat + i]? := by
      rw [preE_get, if_pos (by omega)]
    rw [a1, a2, w3 _ (by omega) (by omega) (by omega), k4 i hi, hE3m _ (by omega)]
  have hstab : ∀ (x y : Nat) (xs : List NIdx), hslice? (preE m D) x y = some xs →
      hslice? (erecP m₅) x y = some xs := by
    intro x y xs h
    have hb := hslice?_pre_le h
    have h1 := (preE_mono m hDt).hslice? h
    have h2 := hg03.ext.hslice? h1
    exact hgr.hslice? hts3' hts5 h2 (by omega)
  have hpw : decPW (erecP m₅) dn (d.toNat + 7) = some caps.sortZ :=
    decPW_move (a := preE m D) (q := s.toNat + 7) (d := d.toNat + 7)
      (fun i hi => by
        have := hwd (7 + i) (by omega) (by omega) (by omega) (by omega)
        simpa [Nat.add_assoc] using this)
      (fun x y _ _ xs h => hstab x y xs h) hsortz
  have h1' : (hd? (erecP m₅) (d.toNat + 1) : Option NIdx) = some (decI (c.headD 0)) := by
    rw [erecP_eq_preE]; exact hd?_of_pre (by omega) w4 hpw1.1
  -- the word `s + 11` and `s + 14`
  have hw11 : (m.arr64 EREC)[s.toNat + 11]? = some wl1 := by
    rw [e10] at hn1'
    obtain ⟨w, hw, hwl⟩ := nat?_get hn1'
    have := erecP_get hw
    rw [hE1] at this
    have hwe : w = wl1 := UInt64.toNat_inj.mp hwl
    subst hwe; exact this
  have hw14 : (m.arr64 EREC)[s.toNat + 14]? = some wl2 := by
    rw [e13] at hn2'
    obtain ⟨w, hw, hwl⟩ := nat?_get hn2'
    have := erecP_get hw
    rw [hg2.2.1 _ (by rw [hT1]; omega), hE1] at this
    have hwe : w = wl2 := UInt64.toNat_inj.mp hwl
    subst hwe; exact this
  have h10' : (hlist? (erecP m₅) (d.toNat + 10) : Option (List NIdx)) = some al' := by
    simp only [L.Arena.hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff]
    refine ⟨(x1.headD 0).toNat, ?_, wl1.toNat, ?_, ?_⟩
    · rw [erecP_eq_preE]; exact nat?_of_pre (by omega) w5
    · rw [erecP_eq_preE]
      refine nat?_of_pre (m := m₅) (T := erecTop m₅) (w := wl1) (by omega) ?_
      rw [show d.toNat + 10 + 1 = d.toNat + 11 from rfl, w3 _ (by omega) (by omega) (by omega),
        k4 11 (by omega), hE3m _ (by omega)]
      exact hw11
    · have h2' := hg3.ext.hslice? hsl2
      have h3' := hgr.hslice? hts3' hts5 h2' (Or.inr (Or.inl (by omega)))
      rw [hq2]; exact h3'
  have h13' : (hlist? (erecP m₅) (d.toNat + 13) : Option (List NIdx)) = some cs' := by
    simp only [L.Arena.hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff]
    refine ⟨(x2.headD 0).toNat, ?_, wl2.toNat, ?_, ?_⟩
    · rw [erecP_eq_preE]; exact nat?_of_pre (by omega) w6
    · rw [erecP_eq_preE]
      refine nat?_of_pre (m := m₅) (T := erecTop m₅) (w := wl2) (by omega) ?_
      rw [show d.toNat + 13 + 1 = d.toNat + 14 from rfl, w3 _ (by omega) (by omega) (by omega),
        k4 14 (by omega), hE3m _ (by omega)]
      exact hw14
    · have h3' := hgr.hslice? hts3' hts5 hsl3 (Or.inr (Or.inl (by omega)))
      rw [hq3]; exact h3'
  refine ⟨a3, pm3, { caps with etaCtor := decI (c.headD 0), all := al', ctors := cs' }, ?_, hDf, hPf,
    hcp3.trans (hcp2.trans hcp1), ?_,
    htk1.trans (htk2.trans (htk3.trans (TierKeep.of_frame (k2.trans w2) (by simp)))), hgrm, hts5, ?_⟩
  · rw [promoteCaps_eq, run_bind_ok hrun1]
    simp only
    rw [run_bind_ok hrun2]
    simp only
    rw [run_bind_ok hrun3]; rfl
  · exact ((eFrame_cons hfr1).trans (hfr2.trans hfr3)).trans
      ((k2.trans w2).mono (by simp) (by simp))
  · exact decCaps_move (a := preE m D) (q := s.toNat) hcaps
      (fun i hi h1 h10 h13 => hwd i hi h1 h10 h13) hpw h1' h10' h13'

end rel

end L.Arena
