import ConAgua.Arena.PromoteCIRef4

/-!
# `promote_rule` and `promote_rules` refine `promoteRule` and `promoteRules`
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

theorem preE_congr {m m' : Mem} (h : m'.arr64 EREC = m.arr64 EREC) (T : Nat) :
    preE m' T = preE m T := by simp [preE, h]

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

/-- **`rule_wr`**: the constructor and right-hand side written, three words copied twice. -/
theorem ruleWr_rel {n : Nat} {d s c r w1 w2 w9 w10 : Word} {m m' : Mem} {rr : List Word}
    (hsz : (m.arr64 EREC).size < 2 ^ 64) (hsd : s.toNat + 11 ≤ d.toNat)
    (hdb : d.toNat + 11 ≤ (m.arr64 EREC).size)
    (h1 : (m.arr64 EREC)[s.toNat + 1]? = some w1) (h2 : (m.arr64 EREC)[s.toNat + 2]? = some w2)
    (h9 : (m.arr64 EREC)[s.toNat + 9]? = some w9) (h10 : (m.arr64 EREC)[s.toNat + 10]? = some w10)
    (hc : callW p n "rule_wr" [d, s, c, r] m = some (rr, m')) :
    (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ MemFrame [EREC] [] m m' ∧
    (∀ i, (i < d.toNat ∨ d.toNat + 11 ≤ i ∨ (d.toNat + 3 ≤ i ∧ i < d.toNat + 8)) →
      (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
    (m'.arr64 EREC)[d.toNat]? = some c ∧ (m'.arr64 EREC)[d.toNat + 1]? = some w1 ∧
    (m'.arr64 EREC)[d.toNat + 2]? = some w2 ∧ (m'.arr64 EREC)[d.toNat + 8]? = some r ∧
    (m'.arr64 EREC)[d.toNat + 9]? = some w9 ∧ (m'.arr64 EREC)[d.toNat + 10]? = some w10 := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (ruleWr_spec p hp n ⟨m, Locals.init []⟩ d s c r) hc
  simp only at hW
  rw [hs'] at hW
  simp only [ruleWrW] at hW
  have e1 : (s + 1).toNat = s.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have e9 : (s + 9).toNat = s.toNat + 9 := by rw [UInt64.toNat_add]; simp; omega
  have e8 : (d + 8).toNat = d.toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
  obtain ⟨⟨ra, ma⟩, hca, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hm1, hr1, -⟩ := rd2_call p hp hca
  obtain rfl := hm1.symm
  rw [rd2W_of hsz (by rw [e1]; simpa using h1) (by rw [e1]; simpa using h2)] at hr1
  subst hr1
  obtain ⟨⟨rb, mb⟩, hcb, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hm2, hr2, -⟩ := rd2_call p hp hcb
  obtain rfl := hm2.symm
  rw [rd2W_of hsz (by rw [e9]; simpa using h9) (by rw [e9]; simpa using h10)] at hr2
  subst hr2
  simp only [g0, g1, List.headD_cons, List.tail_cons] at hW
  obtain ⟨⟨rc, mc⟩, hcc, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := wr3_rel p hp (by omega) hsz hcc
  cases hcd : callW p n "erec_wr3" [d + 8, r, w9, w10] mc with
  | none => rw [hcd] at hW; cases hW
  | some x =>
  obtain ⟨rd, md⟩ := x
  rw [hcd, memK_some] at hW
  have hm : md = m' := Option.some.inj hW
  subst hm
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := wr3_rel p hp (d := d + 8) (by rw [e8, a1]; omega) (by rw [a1]; exact hsz) hcd
  rw [e8] at b3 b4 b5 b6
  refine ⟨by rw [b1, a1], a2.trans b2, fun i hi => ?_, ?_, ?_, ?_, b4, b5, b6⟩
  · rw [b3 i (by omega), a3 i (by omega)]
  · rw [b3 d.toNat (by omega)]; simpa using a4
  · rw [b3 (d.toNat + 1) (by omega)]; exact a5
  · rw [b3 (d.toNat + 2) (by omega)]; exact a6

end rel

end L.Arena
