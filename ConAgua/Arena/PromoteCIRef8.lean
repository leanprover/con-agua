import ConAgua.Arena.PromoteCIRef7
import ConAgua.Arena.PromoteCIExt

/-!
# `promote_rules` refines `promoteRules`
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

theorem promoteRules_nil (pm : PMemo) (fuel : Nat) : promoteRules pm fuel [] = pure (pm, []) := by
  rw [promoteRules]
theorem promoteRules_cons (pm : PMemo) (fuel : Nat) (r : IRecRule) (rs : List IRecRule) :
    promoteRules pm fuel (r :: rs) = (do
      let (m, r) ← promoteRule pm fuel r
      let (m, rs) ← promoteRules m fuel rs
      pure (m, r :: rs)) := by
  rw [promoteRules]

theorem decRules_succ (a : Array Word) (off c : Nat) :
    decRules a off (c + 1) = (decRule a off).bind fun r =>
      (decRules a (off + 11) c).bind fun rs => some (r :: rs) := by
  unfold decRules
  have hf : ((fun j => decRule a (off + 11 * j)) ∘ Nat.succ) =
      fun j => decRule a (off + 11 + 11 * j) :=
    funext fun j => by simp only [Function.comp]; congr 1; omega
  rw [List.range_succ_eq_map, List.mapM_cons, List.mapM_map, hf]
  simp

theorem SlotGrow.join {m₁ m₂ m₃ : Mem} {lo mid hi : Nat} (h₁ : SlotGrow m₁ m₂ lo mid)
    (h₂ : SlotGrow m₂ m₃ mid hi) (hl : lo ≤ mid) (hm : mid ≤ hi) : SlotGrow m₁ m₃ lo hi := by
  refine ⟨Nat.le_trans h₁.1 h₂.1, fun i hi1 hout => ?_, h₂.2.2.trans h₁.2.2⟩
  rw [h₂.2.1 i (by have := h₁.1; omega) (by omega), h₁.2.1 i hi1 (by omega)]

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem rules_rel : ∀ (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f s l d : Word) (D : Nat)
    (rls : List IRecRule) (r : List Word) (m' : Mem),
    ArenaD m a → PMemoR m pm → (m.arr64 EREC).size < 2 ^ 64 → erecTop m ≤ (m.arr64 EREC).size →
    decRules (preE m D) s.toNat l.toNat = some rls → s.toNat + 11 * l.toNat ≤ D →
    D ≤ erecTop m → D ≤ d.toNat → d.toNat + 11 * l.toNat ≤ erecTop m →
    callW p n "promote_rules" [f, s, l, d] m = some (r, m') →
    ∃ a' pm' rls', (promoteRules pm f.toNat rls).run a = .ok ((pm', rls'), a') ∧ ArenaD m' a' ∧
      PMemoR m' pm' ∧ cp a' = cp a ∧ MemFrame (EREC :: eArrs) (129 :: eCtl) m m' ∧ TierKeep m m' ∧
      SlotGrow m m' d.toNat (d.toNat + 11 * l.toNat) ∧ erecTop m' ≤ (m'.arr64 EREC).size ∧
      decRules (erecP m') d.toNat l.toNat = some rls' := by
  intro n
  induction n with
  | zero => intro m a pm f s l d D rls r m' _ _ _ _ _ _ _ _ _ hc; rw [callW_zero'] at hc; cases hc
  | succ n ih =>
  intro m a pm f s l d D rls r m' hD hP hsz hts hdec hsD hDt hdD hdT hc
  obtain ⟨s', hs', -, hW⟩ := callW_triple (promoteRules_spec p hp n ⟨m, Locals.init []⟩ f s l d) hc
  simp only at hW
  rw [hs'] at hW
  simp only [rulesW] at hW
  by_cases hl : l = 0
  · rw [if_pos hl] at hW
    have hm : m = m' := Option.some.inj hW
    subst hm
    have hl0 : l.toNat = 0 := by rw [hl]; rfl
    rw [hl0] at hdec
    simp only [decRules, List.range_zero, List.mapM_nil, Option.pure_def, Option.some.injEq] at hdec
    subst hdec
    refine ⟨a, pm, [], ?_, hD, hP, rfl, MemFrame.refl _ _ _, TierKeep.refl _, SlotGrow.refl _ _ _, hts, ?_⟩
    · rw [promoteRules_nil]; rfl
    · rw [hl0]; rfl
  rw [if_neg hl] at hW
  have hl1 : l.toNat = (l - 1).toNat + 1 := by
    rw [toNat_sub1 l hl]; have := toNat_pred l hl; omega
  rw [hl1, decRules_succ] at hdec
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hdec
  obtain ⟨r0, hr0, rs0, hrs0, rfl⟩ := hdec
  obtain ⟨⟨z, m₁⟩, hca, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨a1, pm1, rl', hrun1, hD1, hP1, hcp1, hfr1, htk1, hg1, hts1, hdr, hfh⟩ :=
    rule_rel p hp n m a pm f s d D r0 z m₁ hD hP hsz hts hr0 (by omega) hDt hdD (by omega) hca
  have hsz1 : (m₁.arr64 EREC).size < 2 ^ 64 := by rw [hg1.2.2]; exact hsz
  cases hcb : callW p n "promote_rules" [f, s + 11, l - 1, d + 11] m₁ with
  | none => rw [hcb] at hW; cases hW
  | some x =>
  obtain ⟨z2, m₂⟩ := x
  rw [hcb, memK_some] at hW
  have hm : m₂ = m' := Option.some.inj hW
  subst hm
  have e11s : (s + 11).toNat = s.toNat + 11 := by rw [UInt64.toNat_add]; simp; omega
  have e11d : (d + 11).toNat = d.toNat + 11 := by rw [UInt64.toNat_add]; simp; omega
  have hlow : ArrExt (preE m D) (preE m₁ D) := preE_ext (fun i hi => by
    exact hg1.2.1 i (by omega) (Or.inl (by omega)))
  obtain ⟨a2, pm2, rs', hrun2, hD2, hP2, hcp2, hfr2, htk2, hg2, hts2, hdr2⟩ :=
    ih m₁ a1 pm1 f (s + 11) (l - 1) (d + 11) D rs0 z2 m₂ hD1 hP1 hsz1 hts1
      (by rw [e11s]; exact hlow.decRules hrs0)
      (by rw [e11s, toNat_sub1 l hl]; omega) (by have := hg1.1; omega) (by rw [e11d]; omega)
      (by rw [e11d, toNat_sub1 l hl]; have := hg1.1; omega) hcb
  have hlpos : 1 ≤ l.toNat := by have := toNat_pred l hl; omega
  have hg2' : SlotGrow m₁ m₂ (d.toNat + 11) (d.toNat + 11 * l.toNat) := by
    have := hg2
    rw [e11d, toNat_sub1 l hl] at this
    have e : d.toNat + 11 + 11 * (l.toNat - 1) = d.toNat + 11 * l.toNat := by omega
    rwa [e] at this
  refine ⟨a2, pm2, rl' :: rs', ?_, hD2, hP2, hcp2.trans hcp1,
    (hfr1.trans hfr2), htk1.trans htk2, ?_, hts2, ?_⟩
  · rw [promoteRules_cons, run_bind_ok hrun1]
    simp only
    rw [run_bind_ok hrun2]; rfl
  · exact hg1.join hg2' (by omega) (by omega)
  · have hext : ExtP (RuleP d.toNat (erecTop m)) (erecP m₁) (erecP m₂) := by
      intro i v hP hv
      obtain ⟨hi1, hv1⟩ := preE_get_lt (m := m₁) (T := erecTop m₁) hv
      unfold RuleP at hP
      have := hg2'.2.1 i hi1 (by omega)
      exact preE_of_get (m := m₂) (T := erecTop m₂) (by have := hg2'.1; omega)
        (by rw [this]; exact hv1)
    rw [e11d] at hdr2
    rw [hl1, decRules_succ, decRule_ext hext hdr hfh, Option.bind_some, hdr2]
    rfl

end rel

end L.Arena
