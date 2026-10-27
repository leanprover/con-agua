import ConAgua.Arena.RecGenSpec4
import ConAgua.Arena.RecClassSpecN

/-!
# `RecGen`: `classRulesOk` (lane `indproofs2`, helper `rec3`)
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## The model -/

def crsK6 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r6, m6) => some ([r6.headD 0, r6.tail.headD 0], m6)

def crsK5 (n : Nat) (y : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => crsK6 (consW n m5 y (r5.headD 0) (r5.tail.headD 0))

def cr1K : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m') => some ([r.headD 0], m')

/-- **The model of `class_rules_ok_one`.** -/
noncomputable def cr1W (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, visT, visR, g, cvR, x, gen =>
    if (rdW (m.arr64 IW) g + rdW (m.arr64 IW) (g + 8)) + rdW (m.arr64 IW) (x + 1) < (rdW (m.arr64 IW) g + rdW (m.arr64 IW) (g + 8)) then none
    else cr1K (cruleW cR n m visT visR cvR ((rdW (m.arr64 IW) g + rdW (m.arr64 IW) (g + 8)) + rdW (m.arr64 IW) (x + 1)) gen)

mutual
/-- **The model of `class_rules_ok`.** -/
noncomputable def crsW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, visT, visR, g, rco, rcl, cgo, cgl, cvR, c, xo, xl =>
    if xl = 0 then some ([0, 0], m)
    else crsK1 cR n visT visR g rco rcl cgo cgl cvR c xo xl (rdW (m.arr64 IW) xo) (L.Arena.cvLpsW n m cvR)
noncomputable def crsK1 (cR : CallM) (n : Nat) (visT visR g rco rcl cgo cgl cvR c xo xl x : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => crsK2 cR n visT visR g rco rcl cgo cgl cvR c xo xl x (plW n m1 (r1.headD 0) (r1.tail.headD 0))
noncomputable def crsK2 (cR : CallM) (n : Nat) (visT visR g rco rcl cgo cgl cvR c xo xl x : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => crsK3 cR n visT visR g rco rcl cgo cgl cvR c xo xl x (ruW n m2 g rco rcl cgo cgl (r2.headD 0) c x)
noncomputable def crsK3 (cR : CallM) (n : Nat) (visT visR g rco rcl cgo cgl cvR c xo xl x : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) =>
    if r3.headD 0 = 0 then none
    else crsK4 cR n visT visR g rco rcl cgo cgl cvR c xo xl (cr1W cR n m3 visT visR g cvR x (r3.tail.headD 0))
noncomputable def crsK4 (cR : CallM) (n : Nat) (visT visR g rco rcl cgo cgl cvR c xo xl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) =>
    crsK5 n (r4.headD 0) (crsW cR n m4 visT visR g rco rcl cgo cgl cvR c (xo + 1) (xl - 1))
end

section arms
variable (cR : CallM) (n : Nat) (m m1 m2 m3 m4 m5 m6 : Mem) (visT visR g rco rcl cgo cgl cvR c xo xl x y : Word)
  (r1 r2 r3 r4 r5 r6 : List Word)
theorem crsW_nil (h : xl = 0) : crsW cR (n + 1) m visT visR g rco rcl cgo cgl cvR c xo xl = some ([0, 0], m) := by
  simp [crsW, h]
theorem crsW_cons (h : ¬ xl = 0) : crsW cR (n + 1) m visT visR g rco rcl cgo cgl cvR c xo xl =
    crsK1 cR n visT visR g rco rcl cgo cgl cvR c xo xl (rdW (m.arr64 IW) xo) (L.Arena.cvLpsW n m cvR) := by
  simp only [crsW]; rw [ite_eq_right h]
theorem crsK1_some : crsK1 cR n visT visR g rco rcl cgo cgl cvR c xo xl x (some (r1, m1)) =
    crsK2 cR n visT visR g rco rcl cgo cgl cvR c xo xl x (plW n m1 (r1.headD 0) (r1.tail.headD 0)) := by
  rw [crsK1]
theorem crsK2_some : crsK2 cR n visT visR g rco rcl cgo cgl cvR c xo xl x (some (r2, m2)) =
    crsK3 cR n visT visR g rco rcl cgo cgl cvR c xo xl x (ruW n m2 g rco rcl cgo cgl (r2.headD 0) c x) := by
  rw [crsK2]
theorem crsK3_fail (h : r3.headD 0 = 0) : crsK3 cR n visT visR g rco rcl cgo cgl cvR c xo xl x (some (r3, m3)) = none := by
  rw [crsK3, ite_eq_left h]
theorem crsK3_ok (h : ¬ r3.headD 0 = 0) : crsK3 cR n visT visR g rco rcl cgo cgl cvR c xo xl x (some (r3, m3)) =
    crsK4 cR n visT visR g rco rcl cgo cgl cvR c xo xl (cr1W cR n m3 visT visR g cvR x (r3.tail.headD 0)) := by
  rw [crsK3, ite_eq_right h]
theorem cr1W_big (h : (rdW (m.arr64 IW) g + rdW (m.arr64 IW) (g + 8)) + rdW (m.arr64 IW) (x + 1) < (rdW (m.arr64 IW) g + rdW (m.arr64 IW) (g + 8))) : cr1W cR (n + 1) m visT visR g cvR x y = none := by
  rw [cr1W, ite_eq_left h]
theorem cr1W_ok (h : ¬ (rdW (m.arr64 IW) g + rdW (m.arr64 IW) (g + 8)) + rdW (m.arr64 IW) (x + 1) < (rdW (m.arr64 IW) g + rdW (m.arr64 IW) (g + 8))) : cr1W cR (n + 1) m visT visR g cvR x y =
    cr1K (cruleW cR n m visT visR cvR ((rdW (m.arr64 IW) g + rdW (m.arr64 IW) (g + 8)) + rdW (m.arr64 IW) (x + 1)) y) := by
  rw [cr1W, ite_eq_right h]
theorem cr1K_some : cr1K (some (r1, m1)) = some ([r1.headD 0], m1) := rfl
theorem crsK4_some : crsK4 cR n visT visR g rco rcl cgo cgl cvR c xo xl (some (r4, m4)) =
    crsK5 n (r4.headD 0) (crsW cR n m4 visT visR g rco rcl cgo cgl cvR c (xo + 1) (xl - 1)) := by
  rw [crsK4]
theorem crsK5_some : crsK5 n y (some (r5, m5)) = crsK6 (consW n m5 y (r5.headD 0) (r5.tail.headD 0)) := rfl
theorem crsK6_some : crsK6 (some (r6, m6)) = some ([r6.headD 0, r6.tail.headD 0], m6) := rfl
end arms

grind_pattern [ind_grind] crsW_nil => crsW cR (n + 1) m visT visR g rco rcl cgo cgl cvR c xo xl
grind_pattern [ind_grind] crsW_cons => crsW cR (n + 1) m visT visR g rco rcl cgo cgl cvR c xo xl
grind_pattern [ind_grind] crsK1_some => crsK1 cR n visT visR g rco rcl cgo cgl cvR c xo xl x (some (r1, m1))
grind_pattern [ind_grind] crsK2_some => crsK2 cR n visT visR g rco rcl cgo cgl cvR c xo xl x (some (r2, m2))
grind_pattern [ind_grind] crsK3_fail => crsK3 cR n visT visR g rco rcl cgo cgl cvR c xo xl x (some (r3, m3))
grind_pattern [ind_grind] crsK3_ok => crsK3 cR n visT visR g rco rcl cgo cgl cvR c xo xl x (some (r3, m3))
grind_pattern [ind_grind] crsK4_some => crsK4 cR n visT visR g rco rcl cgo cgl cvR c xo xl (some (r4, m4))
grind_pattern [ind_grind] crsK5_some => crsK5 n y (some (r5, m5))
grind_pattern [ind_grind] crsK6_some => crsK6 (some (r6, m6))
grind_pattern [ind_grind] cr1W_big => cr1W cR (n + 1) m visT visR g cvR x y
grind_pattern [ind_grind] cr1W_ok => cr1W cR (n + 1) m visT visR g cvR x y
grind_pattern [ind_grind] cr1K_some => cr1K (some (r1, m1))

/-- The lookups `class_rules_ok` needs. -/
structure CrsProg (p : Prog) : Prop where
  ru : RuProg p
  cr : CruleProg p
  alloc : p.lookup "iw_alloc" = some iwAlloc
  copy : p.lookup "iw_copy" = some iwCopy
  cons : p.lookup "sl_cons" = some slCons
  slGet : p.lookup "sl_get" = some slGet
  paramFind : p.lookup "param_find" = some paramFind
  paramPush : p.lookup "param_push" = some paramPush
  internParam : p.lookup "intern_param" = some internParam
  plGo : p.lookup "param_levels_go" = some paramLevelsGoL
  pl : p.lookup "param_levels" = some paramLevelsL
  il : IlF p
  crs : p.lookup "class_rules_ok" = some classRulesOkL
  one : p.lookup "class_rules_ok_one" = some classRulesOkOne

theorem classRulesOkOne_spec (p : Prog) (h : CrsProg p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) (s₀ : St) (visT visR g cvR x gen : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_rules_ok_one" [visT, visR, g, cvR, x, gen]
    ⦃fun r s' => LocEq s' s₀ ∧ cr1W cR n s₀.mem visT visR g cvR x gen = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.one]
  simp only [callFn, classRulesOkOne]
  rcases n with _ | n
  · vcgen [exec] <;> grind
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, classRuleOk_spec p h.cr cR hcR n] <;>
    finish (gen := 20) [rdW_eq, loc_init4, loc_init5]

theorem classRulesOk_spec (p : Prog) (h : CrsProg p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) :
    ∀ (s₀ : St) (visT visR g rco rcl cgo cgl cvR c xo xl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_rules_ok" [visT, visR, g, rco, rcl, cgo, cgl, cvR, c, xo, xl]
    ⦃fun r s' => LocEq s' s₀ ∧ crsW cR n s₀.mem visT visR g rco rcl cgo cgl cvR c xo xl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ visT visR g rco rcl cgo cgl cvR c xo xl
    rw [invoke_eq _ h.crs]; simp only [callFn, classRulesOkL]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ visT visR g rco rcl cgo cgl cvR c xo xl
    rw [invoke_eq _ h.crs]
    simp only [callFn, classRulesOkL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        L.Arena.cvLps_specW p h.cr.alloc h.cr.copy h.cr.eti h.cr.lps n,
        plW_spec p h.alloc h.copy h.cons h.slGet h.paramFind h.paramPush h.internParam h.plGo h.pl h.il n,
        classGenRule_spec p h.ru n, classRulesOkOne_spec p h cR hcR n,
        slCons_specW p h.alloc h.copy h.cons n, ih] <;>
      finish (gen := 20) (instances := 5000) [rdW_eq, loc_init4, loc_init5, loc_init6, loc_init7, loc_init8, loc_init9,
        loc_init10]

/-! ## Shared pieces -/

/-- A `Sim` (lane `indproofs2`'s combinators) as a `RSim`. -/
theorem rec3Sim_rsim {β α : Type} {mo : Option (β × Mem)} {op : AM α} {a : AState}
    {Q : β → α → Mem → AState → Prop} (h : Sim mo op a Q) :
    RSim mo op a (fun b a' x => Q b.1 x b.2 a') := fun b hb => h b.1 b.2 hb

/-- A word sum that does not wrap. -/
theorem rec3Add_toNat {a b : Word} (h : ¬ a + b < a) : (a + b).toNat = a.toNat + b.toNat := by
  have h' : ¬ (a + b).toNat < a.toNat := fun x => h (UInt64.lt_iff_toNat_lt.mpr x)
  rw [UInt64.toNat_add] at h' ⊢
  have := a.toNat_lt; have := b.toNat_lt
  by_cases hc : a.toNat + b.toNat < 2 ^ 64
  · exact Nat.mod_eq_of_lt hc
  · exfalso; apply h'; rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

/-- The slots' count and the constructors of a class generator decoded below the tops. -/
theorem rec3CG_parts {m : Mem} {g : Nat} {G : ClassGen} (h : DecB (fun m => decCG m g) m G) :
    iwN m (g + 8) = some G.slots.length ∧
    ∃ o l, iwN m (g + 9) = some o ∧ iwN m (g + 10) = some l ∧
      DecB (fun m => decPL m (decLH m (decPL m (decCC m))) o l) m G.ctors := by
  have h' : decCG (truncM m) g = some G := h
  simp only [decCG, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h'
  obtain ⟨nP, hnP, ps, hps, cls, hcls, ft, hft, sl, hsl, cts, hcts, el, hel, pre, hpre, rfl⟩ := h'
  obtain ⟨o7, l7, h7, h8, hs⟩ := decAt_some hsl
  obtain ⟨o9, l9, h9, h10, hc⟩ := decAt_some hcts
  rw [show g + 7 + 1 = g + 8 by omega] at h8
  rw [show g + 9 + 1 = g + 10 by omega] at h10
  refine ⟨by rw [(rec2IwN_trunc h8).2, decPL_length _ hs], o9, l9, (rec2IwN_trunc h9).2,
    (rec2IwN_trunc h10).2, hc⟩

/-- `CVExt` bounds the record's address. -/
theorem rec3CVExt_lt {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}
    {q : Nat} (hS : StageR dn vis fe m a) (h : CVExt m q) : q + 3 < 2 ^ 64 := by
  obtain ⟨-, hE1, -, hEs, -⟩ := hS.2
  have := h.1
  omega

/-! ## `class_rules_ok_one` -/

/-! ## `class_rules_ok` -/

/-- The result: a handle slice below the top. -/
abbrev decEL : Mem → List Word → List EIdx → Prop := decRL (fun m => decHL m) 0

/-! ## The `abstract1` memo across a rule's check -/

end L.Ind
