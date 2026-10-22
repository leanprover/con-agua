import ConAgua.Arena.PromoteCIRef11

/-!
# `proj_a` and `proj_b` as relations
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

theorem toNat_addn (q : Word) (k : Nat) (hk : k < 2 ^ 64) (h : q.toNat + k < 2 ^ 64) :
    (q + UInt64.ofNat k).toNat = q.toNat + k := toNat_addk q k hk h

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem projA_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f q : Word) (sn tn : NIdx)
    (lps : List NIdx) (r : List Word) (m' : Mem) (hD : ArenaD m a) (hP : PMemoR m pm)
    (hsz : (m.arr64 EREC).size < 2 ^ 64) (hqb : q.toNat + 14 ≤ (m.arr64 EREC).size)
    (hsn : hd? (erecP m) (q.toNat + 2) = some sn) (htn : hd? (erecP m) (q.toNat + 1) = some tn)
    (hlp : hlist? (erecP m) (q.toNat + 3) = some lps)
    (hc : callW p n "proj_a" [f, q] m = some (r, m')) :
    ∃ (a1 : AState) (pm1 : PMemo) (a2 : AState) (pm2 : PMemo) (a3 : AState) (pm3 : PMemo)
      (sn' tn' : NIdx) (lps' : List NIdx) (wl : Word),
      (promoteN pm f.toNat sn).run a = .ok ((pm1, sn'), a1) ∧
      (promoteN pm1 f.toNat tn).run a1 = .ok ((pm2, tn'), a2) ∧
      (promoteNList pm2 f.toNat lps).run a2 = .ok ((pm3, lps'), a3) ∧
      ArenaD m' a3 ∧ PMemoR m' pm3 ∧ cp a3 = cp a ∧
      MemFrame (EREC :: eArrs) (129 :: eCtl) m m' ∧ ErecGrow m m' ∧
      erecTop m' ≤ (m'.arr64 EREC).size ∧
      PW (g0 r) ∧ decI (g0 r) = tn' ∧ PW (g1 r) ∧ decI (g1 r) = sn' ∧
      nat? (erecP m) (q.toNat + 3 + 1) = some wl.toNat ∧ (g2 r).toNat = erecTop m ∧
      erecTop m' = erecTop m + wl.toNat ∧ hslice? (erecP m') (erecTop m) wl.toNat = some lps' := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (projA_spec p hp n ⟨m, Locals.init []⟩ f q) hc
  simp only at hW
  rw [hs'] at hW
  simp only [projAW] at hW
  have e2 : (q + 2).toNat = q.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have e1 : (q + 1).toNat = q.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have e3 : (q + 3).toNat = q.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  cases hca : callW p n "pn_at" [f, q + 2] m with
  | none => rw [hca] at hW; cases hW
  | some x =>
  obtain ⟨c6, m₁⟩ := x
  rw [hca] at hW
  simp only [Option.bind_some] at hW
  obtain ⟨a1, pm1, hrun1, hD1, hP1, hpw1, hcp1, hfr1⟩ :=
    pnAt_rel p hp n m a pm f (q + 2) sn c6 m₁ hD hP hsz (by rw [e2]; exact hsn) hca
  obtain ⟨hE1, hT1⟩ := eFrame_erec hfr1
  have hsz1 : (m₁.arr64 EREC).size < 2 ^ 64 := by rw [hE1]; exact hsz
  have hP1' : erecP m₁ = erecP m := by
    rw [erecP_eq_preE, erecP_eq_preE, hT1]; exact preE_congr hE1 _
  cases hcb : callW p n "pn_at" [f, q + 1] m₁ with
  | none => rw [hcb] at hW; cases hW
  | some x =>
  obtain ⟨c7, m₂⟩ := x
  rw [hcb] at hW
  simp only [Option.bind_some] at hW
  obtain ⟨a2, pm2, hrun2, hD2, hP2, hpw2, hcp2, hfr2⟩ :=
    pnAt_rel p hp n m₁ a1 pm1 f (q + 1) tn c7 m₂ hD1 hP1 hsz1 (by rw [hP1', e1]; exact htn) hcb
  obtain ⟨hE2, hT2⟩ := eFrame_erec hfr2
  have hsz2 : (m₂.arr64 EREC).size < 2 ^ 64 := by rw [hE2]; exact hsz1
  have hP2' : erecP m₂ = erecP m₁ := by
    rw [erecP_eq_preE, erecP_eq_preE, hT2]; exact preE_congr hE2 _
  cases hcc : callW p n "ps_at" [0, f, q + 3] m₂ with
  | none => rw [hcc] at hW; cases hW
  | some x =>
  obtain ⟨c8, m₃⟩ := x
  rw [hcc] at hW
  simp only [Option.bind_some] at hW
  obtain ⟨wo, wl, hn1, hn1', hsl1, a3, pm3, lps', hrun3, hD3, hP3, hcp3, hfr3, hq3, hg3, hT3, hts3,
    hsl3⟩ := psAt0_rel p hp n m₂ a2 pm2 f (q + 3) lps c8 m₃ hD2 hP2 hsz2
      (by rw [hP2', hP1', e3]; exact hlp) hcc
  obtain ⟨hlist, hm3⟩ := Prod.mk.inj (Option.some.inj hW)
  subst hm3
  obtain ⟨h0, hrest⟩ := List.cons.inj hlist
  obtain ⟨h1, hrest2⟩ := List.cons.inj hrest
  obtain ⟨h2, -⟩ := List.cons.inj hrest2
  have hg03 : ErecGrow m m₃ :=
    ⟨by rw [← hT1, ← hT2]; exact hg3.1, fun i hi => by
      rw [hg3.2.1 i (by rw [hT2, hT1]; exact hi), hE2, hE1], by rw [hg3.2.2, hE2, hE1]⟩
  refine ⟨a1, pm1, a2, pm2, a3, pm3, decI (c6.headD 0), decI (c7.headD 0), lps', wl, hrun1, hrun2,
    hrun3, hD3, hP3, hcp3.trans (hcp2.trans hcp1),
    ((hfr1.mono (by simp) (by simp)).trans (hfr2.mono (by simp) (by simp))).trans hfr3, hg03, hts3,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← h0]; exact hpw2
  · rw [← h0]
  · rw [← h1]; exact hpw1
  · rw [← h1]
  · rw [← e3, hP2', hP1'] at *; exact hn1'
  · rw [← h2, hq3, hT2, hT1]
  · rw [hT3, hT2, hT1]
  · rw [hT2, hT1] at hsl3; exact hsl3

end rel

end L.Arena
