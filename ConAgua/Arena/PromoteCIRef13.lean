import ConAgua.Arena.PromoteCIRef12

/-!
# `proj_b`, `promote_proj_table`
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

theorem hlist?_unfold {a : Array Word} {i : Nat} {k : IdxKind} {xs : List (Idx k)}
    (h : hlist? a i = some xs) :
    ∃ o c : Nat, nat? a i = some o ∧ nat? a (i + 1) = some c ∧ hslice? a o c = some xs := by
  simp only [L.Arena.hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨o, ho, c, hc, hs⟩ := h
  exact ⟨o, c, ho, hc, hs⟩

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem projB_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f q : Word) (ct : NIdx)
    (ss : LIdx) (bodies : List EIdx) (guards : List LIdx) (r : List Word) (m' : Mem)
    (hD : ArenaD m a) (hP : PMemoR m pm)
    (hsz : (m.arr64 EREC).size < 2 ^ 64) (hqb : q.toNat + 13 ≤ (m.arr64 EREC).size)
    (hct : hd? (erecP m) (q.toNat + 6) = some ct) (hss : hd? (erecP m) (q.toNat + 8) = some ss)
    (hbs : hlist? (erecP m) (q.toNat + 9) = some bodies)
    (hgs : hlist? (erecP m) (q.toNat + 11) = some guards)
    (hc : callW p n "proj_b" [f, q] m = some (r, m')) :
    ∃ (a1 : AState) (pm1 : PMemo) (a2 : AState) (pm2 : PMemo) (a3 : AState) (pm3 : PMemo)
      (a4 : AState) (pm4 : PMemo) (c' : NIdx) (ss' : LIdx) (bs' : List EIdx) (gs' : List LIdx)
      (wlb wlg : Word),
      (promoteN pm f.toNat ct).run a = .ok ((pm1, c'), a1) ∧
      (promoteL pm1 f.toNat ss).run a1 = .ok ((pm2, ss'), a2) ∧
      (promoteEList pm2 f.toNat bodies).run a2 = .ok ((pm3, bs'), a3) ∧
      (promoteLList pm3 f.toNat guards).run a3 = .ok ((pm4, gs'), a4) ∧
      ArenaD m' a4 ∧ PMemoR m' pm4 ∧ cp a4 = cp a ∧
      MemFrame (EREC :: eArrs) (129 :: eCtl) m m' ∧ TierKeep m m' ∧ ErecGrow m m' ∧
      erecTop m' ≤ (m'.arr64 EREC).size ∧
      PW (g0 r) ∧ decI (g0 r) = c' ∧ PW (g1 r) ∧ decI (g1 r) = ss' ∧
      nat? (erecP m) (q.toNat + 9 + 1) = some wlb.toNat ∧
      nat? (erecP m) (q.toNat + 11 + 1) = some wlg.toNat ∧
      (g2 r).toNat = erecTop m ∧ (g3 r).toNat = erecTop m + wlb.toNat ∧
      erecTop m' = erecTop m + wlb.toNat + wlg.toNat ∧
      hslice? (erecP m') (erecTop m) wlb.toNat = some bs' ∧
      hslice? (erecP m') (erecTop m + wlb.toNat) wlg.toNat = some gs' := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (projB_spec p hp n ⟨m, Locals.init []⟩ f q) hc
  simp only at hW
  rw [hs'] at hW
  simp only [projBW] at hW
  have e6 : (q + 6).toNat = q.toNat + 6 := by rw [UInt64.toNat_add]; simp; omega
  have e8 : (q + 8).toNat = q.toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
  have e9 : (q + 9).toNat = q.toNat + 9 := by rw [UInt64.toNat_add]; simp; omega
  have e11 : (q + 11).toNat = q.toNat + 11 := by rw [UInt64.toNat_add]; simp; omega
  obtain ⟨⟨c9, m₁⟩, hca, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨a1, pm1, hrun1, hD1, hP1, hpw1, hcp1, hfr1, htk1⟩ :=
    pnAt_rel p hp n m a pm f (q + 6) ct c9 m₁ hD hP hsz (by rw [e6]; exact hct) hca
  obtain ⟨hE1, hT1⟩ := eFrame_erec hfr1
  have hsz1 : (m₁.arr64 EREC).size < 2 ^ 64 := by rw [hE1]; exact hsz
  have hP1' : erecP m₁ = erecP m := by
    rw [erecP_eq_preE, erecP_eq_preE, hT1]; exact preE_congr hE1 _
  obtain ⟨⟨c10, m₂⟩, hcb, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨a2, pm2, hrun2, hD2, hP2, hpw2, hcp2, hfr2, htk2⟩ :=
    plAt_rel p hp n m₁ a1 pm1 f (q + 8) ss c10 m₂ hD1 hP1 hsz1 (by rw [hP1', e8]; exact hss) hcb
  obtain ⟨hE2, hT2⟩ := eFrame_erec hfr2
  have hsz2 : (m₂.arr64 EREC).size < 2 ^ 64 := by rw [hE2]; exact hsz1
  have hP2' : erecP m₂ = erecP m₁ := by
    rw [erecP_eq_preE, erecP_eq_preE, hT2]; exact preE_congr hE2 _
  obtain ⟨⟨c11, m₃⟩, hcc, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨wo3, wl3, hn3, hn3', hsl3, a3, pm3, bs', hrun3, hD3, hP3, hcp3, hfr3, hq3, hg3, hT3, hts3,
    hsl3', htk3⟩ := psAt2_rel p hp n m₂ a2 pm2 f (q + 9) bodies c11 m₃ hD2 hP2 hsz2
      (by rw [hP2', hP1', e9]; exact hbs) hcc
  have hsz3 : (m₃.arr64 EREC).size < 2 ^ 64 := by rw [hg3.2.2]; exact hsz2
  obtain ⟨⟨c12, m₄⟩, hcd, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨wo4, wl4, hn4, hn4', hsl4, a4, pm4, gs', hrun4, hD4, hP4, hcp4, hfr4, hq4, hg4, hT4, hts4,
    hsl4', htk4⟩ := psAt1_rel p hp n m₃ a3 pm3 f (q + 11) guards c12 m₄ hD3 hP3 hsz3
      (by rw [e11]; exact hg3.ext.hlist? (by rw [hP2', hP1']; exact hgs)) hcd
  obtain ⟨hlist, hm4⟩ := Prod.mk.inj (Option.some.inj hW)
  subst hm4
  -- the length word of the guards, read in the original pool
  obtain ⟨og, cg, hog, hcg, -⟩ := hlist?_unfold hgs
  have hcg3 : nat? (erecP m₃) (q.toNat + 11 + 1) = some cg := hg3.ext.nat? (by rw [hP2', hP1']; exact hcg)
  rw [e11] at hn4'
  have hcgw : cg = wl4.toNat := Option.some.inj (hcg3.symm.trans hn4')
  have hg04 : ErecGrow m m₄ :=
    ⟨by rw [← hT1, ← hT2]; exact Nat.le_trans hg3.1 hg4.1, fun i hi => by
      rw [hg4.2.1 i (by rw [hT3, hT2, hT1]; omega), hg3.2.1 i (by rw [hT2, hT1]; exact hi), hE2, hE1],
      by rw [hg4.2.2, hg3.2.2, hE2, hE1]⟩
  refine ⟨a1, pm1, a2, pm2, a3, pm3, a4, pm4, decI (c9.headD 0), decI (c10.headD 0), bs', gs',
    wl3, wl4, hrun1, hrun2, hrun3, hrun4, hD4, hP4, hcp4.trans (hcp3.trans (hcp2.trans hcp1)),
    (((eFrame_cons hfr1).trans (eFrame_cons hfr2)).trans hfr3).trans hfr4,
    htk1.trans (htk2.trans (htk3.trans htk4)),
    hg04, hts4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hlist]; exact hpw1
  · rw [← hlist] <;> rfl
  · rw [← hlist]; exact hpw2
  · rw [← hlist] <;> rfl
  · rw [e9, hP2', hP1'] at hn3'; exact hn3'
  · rw [← hcgw]; exact hcg
  · rw [← hlist]; simp only [g2, List.headD_cons, List.tail_cons]; rw [hq3, hT2, hT1]
  · rw [← hlist]; simp only [g3, List.headD_cons, List.tail_cons]; rw [hq4, hT3, hT2, hT1]
  · rw [hT4, hT3, hT2, hT1]
  · rw [hT2, hT1] at hsl3'; exact hg4.ext.hslice? hsl3'
  · rw [hT3, hT2, hT1] at hsl4'; exact hsl4'

end rel

end L.Arena
