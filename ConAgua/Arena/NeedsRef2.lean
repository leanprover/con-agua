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

end steps

end L.Arena
