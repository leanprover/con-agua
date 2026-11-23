module

public import ConAgua.Arena.NeedsRef
import ConAgua.Arena.RecLayout.RuleDec
import ConAgua.Arena.RecLayout.CIDec
import all ConAgua.Arena.Needs

@[expose] public section

/-!
# What a record reads, in L: the refinements, part 2 (lane compare, helper H1)

The recursor rules (`needs_rule`, `needs_rules`) against the twin's `NeedsSt.rule`,
`NeedsSt.rules`, at a rule record decoded from the record pool (`decRule`, `decRules`).
-/

open ConRon.Arena
open Std.WP

namespace L.Arena

open L.Ind L.Stubs

/-- The record pool's word read across the walk's writes. -/
theorem erRd_nd {m m' : Mem} (hf : MemFrame ndA ndC m m') : erRd m' = erRd m := by
  funext x
  simp only [erRd]
  rw [hf.tier _ (by decide) (by decide) (by decide)]

section steps
variable {p : Prog} (P : NeedsProg p) {vis : Word} {fe : IFEnv} {a : AState}
include P

/-- **`needs_rule(q)` refines `NeedsSt.rule`** at the rule record `q` decodes to. -/
@[refines ConRon.Arena.NeedsSt.rule]
theorem needsRule_ref {n : Nat} {m m' : Mem} {q : Word} {r : List Word} {x : NeedsSt}
    {rl : IRecRule} (hc : callW p n "needs_rule" [q] m = some (r, m')) (hS : StageR vis fe m a)
    (hx : NdR m x) (hq : decRule (erecP m) q.toNat = some rl) :
    ∃ y, (x.rule rl).run a = .ok (y, a) ∧ NdR m' y ∧ StageR vis fe m' a ∧
      MemFrame ndA ndC m m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (needsRule_specW p P.rule n _ q) hc
  have hR := erRdOK m
  obtain ⟨hct, -, hrh⟩ := decRule_fields hq
  obtain ⟨erh, wrh⟩ := hd?_rd (f := Rule.rhs) hR hrh
  obtain ⟨ect, wct⟩ := hd?_rd (f := Rule.ctor) hR hct
  rcases n with _ | n
  · rw [needsRuleW.eq_1] at hW; cases hW
  rw [needsRuleW.arm1] at hW
  replace hW := opt_some hW (needsRuleW.k_needs_expr.eq_1 _ _ _)
  obtain ⟨⟨r1, m1⟩, c1, hW⟩ := hW
  rw [needsRuleW.k_needs_expr.arm1] at hW
  obtain ⟨y1, e1, hy1, hS1, f1⟩ := needsExpr_ref P c1 hS hx wrh
  rw [erRd_nd f1] at hW
  replace hW := opt_some hW (needsRuleW.k_needs_name.eq_1 _ _ _)
  obtain ⟨⟨r2, m2⟩, c2, hW⟩ := hW
  obtain ⟨hy2, f2⟩ := needsName_step P c2 hy1 wct
  have hS2 := (hS1.ndFrame f2).1
  have hrd2 : erRd m2 = erRd m := by rw [erRd_nd f2, erRd_nd f1]
  have e1' : (x.expr rl.rhs).run a = .ok (y1, a) := by rw [erh]; exact e1
  have hfire := decRule_fire hq
  obtain ⟨wf, hwf, ewf⟩ := hfire.kind
  have hrf : erRd m2 (q + Rule.fire) = wf := by rw [hrd2]; exact hR.at Rule.fire rfl hwf
  generalize hk : rl.fire = fr at hfire ewf
  cases fr with
  | nested lv ps =>
    have h1 : erRd m2 (q + Rule.fire) = 1 := by
      rw [hrf]; exact UInt64.toNat_inj.mp (by simpa using ewf)
    rw [needsRuleW.k_needs_name.arm1 _ _ _ _ _ h1] at hW
    replace hW := opt_some hW (needsRuleW.k_needs_exprs.eq_1 _)
    obtain ⟨⟨r3, m3⟩, c3, hW⟩ := hW
    rw [needsRuleW.k_needs_exprs.arm1, needsRuleW.j1.arm1] at hW
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hps := hlist?_rd (g := Rule.pinsOff + 1) hR (by decide) hfire.2.2
    rw [← hrd2, ← erecP_nd (f1.trans f2), ← UInt64.add_assoc] at hps
    obtain ⟨y3, e3, hy3, hS3, f3⟩ := needsExprs_ref P c3 hS2 hy2 hps
    refine ⟨y3, ?_, hy3, hS3, f1.trans (f2.trans f3)⟩
    simp only [NeedsSt.rule, StateT.run_bind, e1', except_ok_bind, hk]
    rw [ect]; exact e3
  | plain =>
    have h1 : erRd m2 (q + Rule.fire) ≠ 1 := by
      rw [hrf]; intro e; rw [e] at ewf; simp at ewf
    rw [needsRuleW.k_needs_name.arm2 _ _ _ _ _ h1, needsRuleW.j1.arm1] at hW
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    refine ⟨_, ?_, hy2, hS2, f1.trans f2⟩
    simp only [NeedsSt.rule, StateT.run_bind, e1', except_ok_bind, hk]
    rw [ect]; rfl
  | levels lv =>
    have h1 : erRd m2 (q + Rule.fire) ≠ 1 := by
      rw [hrf]; intro e; rw [e] at ewf; simp at ewf
    rw [needsRuleW.k_needs_name.arm2 _ _ _ _ _ h1, needsRuleW.j1.arm1] at hW
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    refine ⟨_, ?_, hy2, hS2, f1.trans f2⟩
    simp only [NeedsSt.rule, StateT.run_bind, e1', except_ok_bind, hk]
    rw [ect]; rfl

/-- **`needs_rules`' loop**: from cursor `i`, the rules of `Rule.size` words, in order. -/
theorem needsRulesLoop : ∀ (n : Nat) (m m' : Mem) (o l i : Word) (x : NeedsSt) (rs : List IRecRule),
    needsRulesW.loop1 p n m o l i = some m' → StageR vis fe m a → NdR m x → i ≤ l →
    decRules (erecP m) (o.toNat + Rule.size.toNat * i.toNat) (l.toNat - i.toNat) = some rs →
    ∃ y, (x.rules rs).run a = .ok (y, a) ∧ NdR m' y ∧ MemFrame ndA ndC m m'
  | 0, _, _, _, _, _, _, _, hW, _, _, _, _ => by rw [needsRulesW.loop1.eq_1] at hW; cases hW
  | n + 1, m, m', o, l, i, x, rs, hW, hS, hx, hil, hrs => by
    by_cases hlt : i < l
    · rw [needsRulesW.loop1.arm1 _ _ _ _ _ _ hlt] at hW
      have hi1 : (i + 1).toNat = i.toNat + 1 := by
        have := UInt64.lt_iff_toNat_lt.mp hlt; have := l.toNat_lt
        rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]; omega
      have hk : l.toNat - i.toNat = (l.toNat - (i + 1).toNat) + 1 := by
        have := UInt64.lt_iff_toNat_lt.mp hlt; omega
      rw [hk, decRules_succ] at hrs
      cases e1 : decRule (erecP m) (o.toNat + Rule.size.toNat * i.toNat) with
      | none => rw [e1] at hrs; cases hrs
      | some rl =>
      cases e2 : decRules (erecP m) (o.toNat + Rule.size.toNat * i.toNat + Rule.size.toNat)
          (l.toNat - (i + 1).toNat) with
      | none => rw [e1, e2] at hrs; cases hrs
      | some rs' =>
      rw [e1, e2] at hrs
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at hrs
      subst hrs
      have hq : (o + Rule.size * i).toNat = o.toNat + Rule.size.toNat * i.toNat := by
        obtain ⟨w, hw, -⟩ := hd?_some (decRule_fields e1).1
        have := (erRdOK m).lt _ _ hw
        have : Rule.size.toNat = 8 := rfl
        rw [UInt64.toNat_add, UInt64.toNat_mul]; omega
      replace hW := opt_some hW (needsRulesW.k_needs_rule.eq_1 _ _ _ _ _)
      obtain ⟨⟨r1, m1⟩, c1, hW⟩ := hW
      rw [needsRulesW.k_needs_rule.arm1] at hW
      obtain ⟨y1, ey1, hy1, hS1, hf1⟩ := needsRule_ref P c1 hS hx (by rw [hq]; exact e1)
      have hs1 : decRules (erecP m1) (o.toNat + Rule.size.toNat * (i + 1).toNat)
          (l.toNat - (i + 1).toNat) = some rs' := by
        rw [erecP_nd hf1, hi1, Nat.mul_succ, ← Nat.add_assoc, ← hi1]; exact e2
      obtain ⟨y2, ey2, hy2, hf2⟩ := needsRulesLoop n m1 m' o l (i + 1) y1 rs' hW hS1 hy1
        (by rw [UInt64.le_iff_toNat_le, hi1]; have := UInt64.lt_iff_toNat_lt.mp hlt; omega) hs1
      refine ⟨y2, ?_, hy2, hf1.trans hf2⟩
      simp only [NeedsSt.rules, StateT.run_bind, ey1, except_ok_bind]
      exact ey2
    · rw [needsRulesW.loop1.arm2 _ _ _ _ _ _ hlt] at hW
      cases hW
      have hle : l.toNat - i.toNat = 0 := by
        have := UInt64.le_iff_toNat_le.mp hil; have := UInt64.not_lt.mp hlt
        have := UInt64.le_iff_toNat_le.mp this; omega
      rw [hle] at hrs
      simp only [decRules, List.range_zero, List.mapM_nil, Option.pure_def, Option.some.injEq] at hrs
      subst hrs
      exact ⟨x, rfl, hx, MemFrame.refl _ _ _⟩

/-- **`needs_rules(o, l)` refines `NeedsSt.rules`** over the `l` rule records from `o`. -/
@[refines ConRon.Arena.NeedsSt.rules]
theorem needsRules_ref {n : Nat} {m m' : Mem} {o l : Word} {r : List Word} {x : NeedsSt}
    {rs : List IRecRule} (hc : callW p n "needs_rules" [o, l] m = some (r, m'))
    (hS : StageR vis fe m a) (hx : NdR m x) (hrs : decRules (erecP m) o.toNat l.toNat = some rs) :
    ∃ y, (x.rules rs).run a = .ok (y, a) ∧ NdR m' y ∧ StageR vis fe m' a ∧
      MemFrame ndA ndC m m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (needsRules_specW p P.rules n _ o l) hc
  rcases n with _ | n
  · rw [needsRulesW.eq_1] at hW; cases hW
  rw [needsRulesW.arm1] at hW
  rcases e : needsRulesW.loop1 p (n + 1) m o l 0 with _ | m1
  · rw [e, needsRulesW.k_loop1.eq_1] at hW; cases hW
  rw [e, needsRulesW.k_loop1.arm1] at hW
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨y, ey, hy, hf⟩ := needsRulesLoop P (n + 1) m _ o l 0 x rs e hS hx
    (by rw [UInt64.le_iff_toNat_le]; simp) (by simpa using hrs)
  exact ⟨y, ey, hy, (hS.ndFrame hf).1, hf⟩

end steps

end L.Arena
