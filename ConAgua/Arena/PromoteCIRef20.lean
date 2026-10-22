import ConAgua.Arena.PromoteCIRef19

/-!
# `rec_rules`: the rules block of `pci_rec`
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

theorem preE_size_le (m : Mem) (D : Nat) : (preE m D).size ≤ D := by
  simp [preE, Nat.min_le_left]

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem rules_zero {n : Nat} {f s l d : Word} {m m' : Mem} {r : List Word} (hl : l = 0)
    (hc : callW p n "promote_rules" [f, s, l, d] m = some (r, m')) : m' = m := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (promoteRules_spec p hp n ⟨m, Locals.init []⟩ f s l d) hc
  simp only at hW
  rw [hs'] at hW
  simp only [rulesW, hl, ↓reduceIte, Option.some.injEq] at hW
  exact hW.symm

theorem recRules_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f s l : Word) (D : Nat)
    (rls : List IRecRule) (r : List Word) (m' : Mem) (hD : ArenaD m a) (hP : PMemoR m pm)
    (hsz : (m.arr64 EREC).size < 2 ^ 64) (hts : erecTop m ≤ (m.arr64 EREC).size)
    (hrls : decRules (preE m D) s.toNat l.toNat = some rls) (hDt : D ≤ erecTop m)
    (hc : callW p n "rec_rules" [f, s, l] m = some (r, m')) :
    ∃ a' pm' rls', (promoteRules pm f.toNat rls).run a = .ok ((pm', rls'), a') ∧
      ArenaD m' a' ∧ PMemoR m' pm' ∧ cp a' = cp a ∧
      MemFrame (EREC :: eArrs) (129 :: eCtl) m m' ∧ ErecGrow m m' ∧
      erecTop m' ≤ (m'.arr64 EREC).size ∧ (r.headD 0).toNat = erecTop m ∧
      erecTop m + 11 * l.toNat ≤ erecTop m' ∧
      decRules (erecP m') (r.headD 0).toNat l.toNat = some rls' := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (recRules_spec p hp n ⟨m, Locals.init []⟩ f s l) hc
  simp only at hW
  rw [hs'] at hW
  simp only [recRulesW] at hW
  cases n with
  | zero => simp only [callW_zero'] at hW; split at hW <;> simp at hW
  | succ n =>
  by_cases hbig : 1152921504606846976 ≤ l
  · rw [if_pos hbig] at hW; cases hW
  rw [if_neg hbig] at hW
  have h60 : l.toNat < 1152921504606846976 := by
    have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hbig)
    simpa using this
  have h11 : (11 * l).toNat = 11 * l.toNat := toNat_mul11 l (by omega)
  cases hal : callW p (n + 1) "erec_alloc" [11 * l] m with
  | none => rw [hal] at hW; cases hW
  | some x =>
  obtain ⟨r5, ma⟩ := x
  rw [hal] at hW
  simp only [Option.bind_some] at hW
  obtain ⟨hd5, hTa, hroom, hfa, hEa⟩ := alloc_rel p hp hal
  rw [h11] at hTa hroom
  have hga : ErecGrow m ma := ErecGrow.of_alloc hEa hTa
  obtain ⟨hDa, hPa⟩ := arenaD_ctl129 hD hP hfa
  have hsza : (ma.arr64 EREC).size < 2 ^ 64 := by rw [hEa]; exact hsz
  have htsa : erecTop ma ≤ (ma.arr64 EREC).size := by rw [hEa, hTa]; exact hroom
  cases hpr : callW p (n + 1) "promote_rules" [f, s, l, r5.headD 0] ma with
  | none => rw [hpr] at hW; cases hW
  | some x =>
  obtain ⟨z, m₂⟩ := x
  rw [hpr] at hW
  simp only [Option.bind_some] at hW
  obtain ⟨hr, hm2⟩ := Prod.mk.inj (Option.some.inj hW)
  subst hm2
  by_cases hl0 : l = 0
  · have hm := rules_zero p hp hl0 hpr
    subst hm
    have hl0' : l.toNat = 0 := by rw [hl0]; rfl
    rw [hl0'] at hrls
    simp only [decRules, List.range_zero, List.mapM_nil, Option.pure_def, Option.some.injEq] at hrls
    subst hrls
    refine ⟨a, pm, [], ?_, hDa, hPa, rfl, hfa.mono (by simp) (by simp) |>.mono (by simp) (by simp),
      hga, htsa, ?_, by omega, ?_⟩
    · rw [promoteRules_nil]; rfl
    · rw [← hr]; exact hd5
    · rw [hl0']; rfl
  · have hbnd := decRules_bound _ _ _ _ hrls
    have hsD : s.toNat + 11 * l.toNat ≤ D := by
      rcases hbnd with h0 | h0
      · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hl0
      · have := (preE_size_le m D); omega
    have hlow : ArrExt (preE m D) (preE ma D) := preE_ext (fun i hi => hga.2.1 i (by omega))
    obtain ⟨a2, pm2, rls', hrun, hD2, hP2, hcp2, hfr2, hgs, hts2, hdr⟩ :=
      rules_rel p hp (n + 1) ma a pm f s l (r5.headD 0) D rls z m₂ hDa hPa hsza htsa
        (hlow.decRules hrls) hsD (by have := hga.1; omega) (by omega) (by omega) hpr
    have hg2 : ErecGrow ma m₂ :=
      ((SlotGrow.of_grow (ErecGrow.refl ma) (r5.headD 0).toNat ((r5.headD 0).toNat + 11 * l.toNat)).trans hgs
        (Nat.le_refl _) (Nat.le_refl _)).toGrow (by omega)
    refine ⟨a2, pm2, rls', hrun, hD2, hP2, hcp2, (hfa.mono (by simp) (by simp)).trans hfr2,
      hga.trans hg2, hts2, ?_, ?_, ?_⟩
    · rw [← hr]; exact hd5
    · have := hgs.1; omega
    · rw [← hr]; exact hdr

end rel

end L.Arena
