import ConAgua.Arena.RecGenSpec8
import ConAgua.Arena.RecGenSpec4
import ConAgua.Arena.RecClassSpecO
import ConAgua.Arena.IndPartsSpec15

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
noncomputable def cr1W : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, visT, visR, g, cvR, x, gen =>
    if (rdW (m.arr64 IW) g + rdW (m.arr64 IW) (g + 8)) + rdW (m.arr64 IW) (x + 1) < (rdW (m.arr64 IW) g + rdW (m.arr64 IW) (g + 8)) then none
    else cr1K (cruleW n m visT visR cvR ((rdW (m.arr64 IW) g + rdW (m.arr64 IW) (g + 8)) + rdW (m.arr64 IW) (x + 1)) gen)

mutual
/-- **The model of `class_rules_ok`.** -/
noncomputable def crsW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, visT, visR, g, rco, rcl, cgo, cgl, cvR, c, xo, xl =>
    if xl = 0 then some ([0, 0], m)
    else crsK1 n visT visR g rco rcl cgo cgl cvR c xo xl (rdW (m.arr64 IW) xo) (L.Arena.cvLpsW n m cvR)
noncomputable def crsK1 (n : Nat) (visT visR g rco rcl cgo cgl cvR c xo xl x : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => crsK2 n visT visR g rco rcl cgo cgl cvR c xo xl x (plW n m1 (r1.headD 0) (r1.tail.headD 0))
noncomputable def crsK2 (n : Nat) (visT visR g rco rcl cgo cgl cvR c xo xl x : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => crsK3 n visT visR g rco rcl cgo cgl cvR c xo xl x (ruW n m2 g rco rcl cgo cgl (r2.headD 0) c x)
noncomputable def crsK3 (n : Nat) (visT visR g rco rcl cgo cgl cvR c xo xl x : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) =>
    if r3.headD 0 = 0 then none
    else crsK4 n visT visR g rco rcl cgo cgl cvR c xo xl (cr1W n m3 visT visR g cvR x (r3.tail.headD 0))
noncomputable def crsK4 (n : Nat) (visT visR g rco rcl cgo cgl cvR c xo xl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) =>
    crsK5 n (r4.headD 0) (crsW n m4 visT visR g rco rcl cgo cgl cvR c (xo + 1) (xl - 1))
end

section arms
variable (n : Nat) (m m1 m2 m3 m4 m5 m6 : Mem) (visT visR g rco rcl cgo cgl cvR c xo xl x y : Word)
  (r1 r2 r3 r4 r5 r6 : List Word)
theorem crsW_nil (h : xl = 0) : crsW (n + 1) m visT visR g rco rcl cgo cgl cvR c xo xl = some ([0, 0], m) := by
  simp [crsW, h]
theorem crsW_cons (h : ¬ xl = 0) : crsW (n + 1) m visT visR g rco rcl cgo cgl cvR c xo xl =
    crsK1 n visT visR g rco rcl cgo cgl cvR c xo xl (rdW (m.arr64 IW) xo) (L.Arena.cvLpsW n m cvR) := by
  simp only [crsW]; rw [if_neg h]
theorem crsK1_some : crsK1 n visT visR g rco rcl cgo cgl cvR c xo xl x (some (r1, m1)) =
    crsK2 n visT visR g rco rcl cgo cgl cvR c xo xl x (plW n m1 (r1.headD 0) (r1.tail.headD 0)) := by
  rw [crsK1]
theorem crsK2_some : crsK2 n visT visR g rco rcl cgo cgl cvR c xo xl x (some (r2, m2)) =
    crsK3 n visT visR g rco rcl cgo cgl cvR c xo xl x (ruW n m2 g rco rcl cgo cgl (r2.headD 0) c x) := by
  rw [crsK2]
theorem crsK3_fail (h : r3.headD 0 = 0) : crsK3 n visT visR g rco rcl cgo cgl cvR c xo xl x (some (r3, m3)) = none := by
  rw [crsK3, if_pos h]
theorem crsK3_ok (h : ¬ r3.headD 0 = 0) : crsK3 n visT visR g rco rcl cgo cgl cvR c xo xl x (some (r3, m3)) =
    crsK4 n visT visR g rco rcl cgo cgl cvR c xo xl (cr1W n m3 visT visR g cvR x (r3.tail.headD 0)) := by
  rw [crsK3, if_neg h]
theorem cr1W_big (h : (rdW (m.arr64 IW) g + rdW (m.arr64 IW) (g + 8)) + rdW (m.arr64 IW) (x + 1) < (rdW (m.arr64 IW) g + rdW (m.arr64 IW) (g + 8))) : cr1W (n + 1) m visT visR g cvR x y = none := by
  rw [cr1W, if_pos h]
theorem cr1W_ok (h : ¬ (rdW (m.arr64 IW) g + rdW (m.arr64 IW) (g + 8)) + rdW (m.arr64 IW) (x + 1) < (rdW (m.arr64 IW) g + rdW (m.arr64 IW) (g + 8))) : cr1W (n + 1) m visT visR g cvR x y =
    cr1K (cruleW n m visT visR cvR ((rdW (m.arr64 IW) g + rdW (m.arr64 IW) (g + 8)) + rdW (m.arr64 IW) (x + 1)) y) := by
  rw [cr1W, if_neg h]
theorem cr1K_some : cr1K (some (r1, m1)) = some ([r1.headD 0], m1) := rfl
theorem crsK4_some : crsK4 n visT visR g rco rcl cgo cgl cvR c xo xl (some (r4, m4)) =
    crsK5 n (r4.headD 0) (crsW n m4 visT visR g rco rcl cgo cgl cvR c (xo + 1) (xl - 1)) := by
  rw [crsK4]
theorem crsK5_some : crsK5 n y (some (r5, m5)) = crsK6 (consW n m5 y (r5.headD 0) (r5.tail.headD 0)) := rfl
theorem crsK6_some : crsK6 (some (r6, m6)) = some ([r6.headD 0, r6.tail.headD 0], m6) := rfl
end arms

grind_pattern [ind_grind] crsW_nil => crsW (n + 1) m visT visR g rco rcl cgo cgl cvR c xo xl
grind_pattern [ind_grind] crsW_cons => crsW (n + 1) m visT visR g rco rcl cgo cgl cvR c xo xl
grind_pattern [ind_grind] crsK1_some => crsK1 n visT visR g rco rcl cgo cgl cvR c xo xl x (some (r1, m1))
grind_pattern [ind_grind] crsK2_some => crsK2 n visT visR g rco rcl cgo cgl cvR c xo xl x (some (r2, m2))
grind_pattern [ind_grind] crsK3_fail => crsK3 n visT visR g rco rcl cgo cgl cvR c xo xl x (some (r3, m3))
grind_pattern [ind_grind] crsK3_ok => crsK3 n visT visR g rco rcl cgo cgl cvR c xo xl x (some (r3, m3))
grind_pattern [ind_grind] crsK4_some => crsK4 n visT visR g rco rcl cgo cgl cvR c xo xl (some (r4, m4))
grind_pattern [ind_grind] crsK5_some => crsK5 n y (some (r5, m5))
grind_pattern [ind_grind] crsK6_some => crsK6 (some (r6, m6))
grind_pattern [ind_grind] cr1W_big => cr1W (n + 1) m visT visR g cvR x y
grind_pattern [ind_grind] cr1W_ok => cr1W (n + 1) m visT visR g cvR x y
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

theorem classRulesOkOne_spec (p : Prog) (h : CrsProg p) (n : Nat) (s₀ : St) (visT visR g cvR x gen : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_rules_ok_one" [visT, visR, g, cvR, x, gen]
    ⦃fun r s' => LocEq s' s₀ ∧ cr1W n s₀.mem visT visR g cvR x gen = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.one]
  simp only [callFn, classRulesOkOne]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, classRuleOk_spec p h.cr n] <;>
      finish (gen := 20) [rdW_eq, loc_init4, loc_init5]

theorem classRulesOk_spec (p : Prog) (h : CrsProg p) (n : Nat) :
    ∀ (s₀ : St) (visT visR g rco rcl cgo cgl cvR c xo xl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_rules_ok" [visT, visR, g, rco, rcl, cgo, cgl, cvR, c, xo, xl]
    ⦃fun r s' => LocEq s' s₀ ∧ crsW n s₀.mem visT visR g rco rcl cgo cgl cvR c xo xl = some (r, s'.mem); ⊤⦄ := by
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
        classGenRule_spec p h.ru n, classRulesOkOne_spec p h n,
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

theorem cr1W_rel {dn : NIdx → Option ConLeche.Name} {visT visR : Word} {feR : IFEnv} {a : AState}
    {N : Nat} {m m' : Mem} {g cvR x gen : Word} {r : List Word} {cv : IConstantVal} {G : ClassGen}
    {X : ClassCtor} (h : cr1W N m visT visR g cvR x gen = some (r, m')) (hS : StageR dn visR feR m a)
    (hgen : H gen) (hcv : decCVp m cvR.toNat = some cv) (hext : CVExt m cvR.toNat)
    (hG : DecB (fun m => decCG m g.toNat) m G) (hns : G.nP + G.slots.length < 2 ^ 64)
    (hX : DecB (fun m => decCC m x.toNat) m X) :
    ∃ a', (ConRon.Arena.classRuleOk V visT.toNat feR cv (G.nP + G.slots.length + X.nF) (decI gen)).run a =
      .ok (decI gen, a') ∧ StageR dn visR feR m' a' ∧ IWGrow m m' ∧ r = [gen] := by
  cases N with
  | zero => simp [cr1W] at h
  | succ N =>
  have hsz := hS.2.2.2.1
  obtain ⟨hnP, -⟩ := rec2CG_parts hG
  obtain ⟨hsl, -⟩ := rec3CG_parts hG
  obtain ⟨hnF, -, -⟩ := rec2CC_parts (hX.get (decCC_mono _))
  obtain ⟨e0, t0⟩ := rec2RdN (w := g) (k := 0) (by simpa using hnP) hsz
  obtain ⟨e8, t8⟩ := rec2RdN (w := g) (k := 8) hsl hsz
  obtain ⟨e1, t1⟩ := rec2RdN (w := x) (k := 1) hnF hsz
  simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero,
    show UInt64.ofNat 8 = (8 : Word) from rfl, show UInt64.ofNat 1 = (1 : Word) from rfl] at e0 e8 e1
  by_cases hb : rdW (m.arr64 IW) g + rdW (m.arr64 IW) (g + 8) + rdW (m.arr64 IW) (x + 1) <
      rdW (m.arr64 IW) g + rdW (m.arr64 IW) (g + 8)
  · rw [cr1W_big (h := hb)] at h; cases h
  rw [cr1W_ok (h := hb)] at h
  cases h1 : cruleW N m visT visR cvR (rdW (m.arr64 IW) g + rdW (m.arr64 IW) (g + 8) + rdW (m.arr64 IW) (x + 1)) gen with
  | none => rw [h1] at h; cases h
  | some rm =>
  obtain ⟨r1, m1⟩ := rm
  rw [h1, cr1K_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨a', hrun, hS', hg, rfl⟩ := cruleW_ok h1 hS hgen (rec2DecCV_erecP hcv hext) (rec3CVExt_lt hS hext)
  have hn : (rdW (m.arr64 IW) g + rdW (m.arr64 IW) (g + 8) + rdW (m.arr64 IW) (x + 1)).toNat =
      G.nP + G.slots.length + X.nF := by
    rw [rec3Add_toNat hb, e0, e8, e1, t1]
    rw [UInt64.toNat_add, t0, t8]; exact congrArg (· + X.nF) (Nat.mod_eq_of_lt hns)
  rw [hn] at hrun
  exact ⟨a', hrun, hS', hg, rfl⟩

/-! ## `class_rules_ok` -/

/-- The result: a handle slice below the top. -/
abbrev decEL : Mem → List Word → List EIdx → Prop := decRL (fun m => decHL m) 0

/-! ## The `abstract1` memo across a rule's check -/

theorem pinternW_afr {m m' : Mem} {u r : Word} (h : pinternW m u = some (r, m')) : AFr m m' := by
  rw [pinternW_eq] at h
  exact AFr.of_frame (internM_frame _ paramSch_wf _ _ _ _ _ _ _ _ h) (by simp [paramSch, PREC, PSLOT])
    (by simp [paramSch])

theorem plgW_afr : ∀ (k : Nat) (m m' : Mem) (o l : Word) (r : List Word), plgW k m o l = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, h => by simp [plgW] at h
  | k + 1, m, m', o, l, r, h => by
    simp only [plgW, plK0.eq_def, plK1.eq_def, plK2.eq_def, plK3.eq_def] at h
    afr_auto h [allocW_afr, pinternW_afr, plgW_afr k _ _ _ _ _, consW_afr]

theorem ilF_afr {m m' : Mem} {args r : List Word} (h : ilF m args = some (r, m')) : AFr m m' :=
  AFr.of_frame (ilF_frame h)

theorem plW_afr {k : Nat} {m m' : Mem} {o l : Word} {r : List Word} (h : plW k m o l = some (r, m')) :
    AFr m m' := by
  cases k with
  | zero => simp [plW] at h
  | succ k =>
  simp only [plW, plW.plK4.eq_def, plW.plK5.eq_def] at h
  afr_auto h [plgW_afr _ _ _ _ _ _, ilF_afr]

theorem iarW_afr : ∀ (n : Nat) (m m' : Mem) (v o l : Word) (r : List Word), iarW n m v o l = some (r, m') →
    AFr m m'
  | 0, _, _, _, _, _, _, h => by simp [iarW] at h
  | n + 1, m, m', v, o, l, r, h => by
    simp only [iarW, iarK.eq_def, resK'.eq_def] at h
    afr_auto h [stub_afr, iarW_afr n _ _ _ _ _ _]

theorem crgW_afr {N : Nat} {m m' : Mem} {visR cvR gen : Word} {r : List Word}
    (h : crgW N m visR cvR gen = some (r, m')) : AFr m m' := by
  cases N with
  | zero => simp [crgW] at h
  | succ N =>
  simp only [crgW, crgK0.eq_def, crgK1.eq_def, crgK2.eq_def, crgK3.eq_def, crgK4.eq_def] at h
  afr_auto h [lbbF_afr, hffF_afr, cvLpsA_afr, stub_afr]

theorem cruleW_afr {N : Nat} {m m' : Mem} {visT visR cvR n gen : Word} {r : List Word}
    (h : cruleW N m visT visR cvR n gen = some (r, m')) : AFr m m' := by
  cases N with
  | zero => simp [cruleW] at h
  | succ N =>
  simp only [cruleW, cruK1.eq_def, cruK2.eq_def, cruK3.eq_def, cruK4.eq_def] at h
  afr_auto h [crgW_afr, stub_afr, (fun h => (AFr.of_frame (flushMem_frame _)).trans (stripF_afr h)),
    iarW_afr _ _ _ _ _ _ _]

theorem cr1W_afr {n : Nat} {m m' : Mem} {visT visR g cvR x gen : Word} {r : List Word}
    (h : cr1W n m visT visR g cvR x gen = some (r, m')) : AFr m m' := by
  cases n with
  | zero => simp [cr1W] at h
  | succ n =>
  simp only [cr1W, cr1K.eq_def] at h
  afr_auto h [cruleW_afr]

theorem crsW_sim (dn : NIdx → Option ConLeche.Name) (visT visR : Word) (feR : IFEnv) (g rco rcl cgo cgl cvR c : Word)
    (G : ClassGen) (recCls : List Nat) (cvGs : List IConstantVal) (cv : IConstantVal)
    (hns : G.nP + G.slots.length < 2 ^ 64) (hrcb : rco.toNat + rcl.toNat < 2 ^ 64)
    (hcgb : cgo.toNat + cgl.toNat < 2 ^ 64) (n : Nat) :
    ∀ (m : Mem) (a : AState) (xo xl : Word) (Xs : List ClassCtor), StageR dn visR feR m a →
    DecB (fun m => decCG m g.toNat) m G → DecB (fun m => decNL m rco.toNat rcl.toNat) m recCls →
    DecB (fun m => decPL m (decCVp m) cgo.toNat cgl.toNat) m cvGs →
    decCVp m cvR.toNat = some cv → CVExt m cvR.toNat →
    DecB (fun m => decPL m (decCC m) xo.toNat xl.toNat) m Xs → AbsOK m →
    RSim (crsW n m visT visR g rco rcl cgo cgl cvR c xo xl)
      (ConRon.Arena.classRulesOk V visT.toNat feR G recCls cvGs cv c.toNat Xs) a
      (fun b a' x => KP dn visR feR m decEL b a' x ∧ AbsOK b.2) := by
  induction n with
  | zero => intros; intro b hb; simp [crsW] at hb
  | succ n ih =>
  intro m a xo xl Xs hS hG hrc hcg hcv hext hXs hA
  have hsz := hS.2.2.2.1
  by_cases hxl : xl = 0
  · rw [crsW_nil (h := hxl)]
    have : Xs = [] := by
      have := decPL_length _ (hXs.get (OMono.decPL (fun q => decCC_mono q) _ _))
      rw [hxl] at this; exact List.eq_nil_of_length_eq_zero (by simpa using this)
    subst this
    unfold ConRon.Arena.classRulesOk
    exact RSim.pure_some ⟨⟨hS, IWGrow.refl m, by simp [decHL, hslice?], by simp⟩, hA⟩
  rw [crsW_cons (h := hxl)]
  obtain ⟨jx, hjx⟩ : ∃ j, xl.toNat = j + 1 :=
    ⟨xl.toNat - 1, by have : xl.toNat ≠ 0 := fun e => hxl (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  have hXs' : decPL (truncM m) (decCC (truncM m)) xo.toNat (jx + 1) = some Xs := by rw [← hjx]; exact hXs
  obtain ⟨px, X, Xs', rfl, hpx, hX, hXsT⟩ := decPL_cons hXs'
  obtain ⟨hxot, hpxm⟩ := rec2IwN_trunc hpx
  have hxot' : iwTop m ≤ (m.arr64 IW).size := hS.2.1
  obtain ⟨ex, tx⟩ := rec2RdN (w := xo) (k := 0) (by simpa using hpxm) hsz
  simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero] at ex
  rw [ex]
  have hX' : DecB (fun m => decCC m (UInt64.ofNat px : Word).toNat) m X := by rw [tx]; exact hX
  unfold ConRon.Arena.classRulesOk
  -- `cv_lps`: L only
  refine RSim.lstep (K := crsK1 n visT visR g rco rcl cgo cgl cvR c xo xl (UInt64.ofNat px)) (by rw [crsK1])
    fun ⟨r1, m1⟩ h1 => ?_
  obtain ⟨hS1, hg1, hd1, ht1⟩ := cvLpsA_stage h1 hS hcv (rec3CVExt_lt hS hext)
  have hA1 := cvLpsA_afr h1 hA
  rw [crsK1_some]
  -- `param_levels`
  refine RSim.bind (K := crsK2 n visT visR g rco rcl cgo cgl cvR c xo xl (UInt64.ofNat px)) (by rw [crsK2])
    (RSim.withF (rec3Sim_rsim (plW_sim (k := n) hS1 hd1 ht1)) (fun _ hb => plW_afr hb)) ?_
  rintro ⟨r2, m2⟩ rl a2 - ⟨⟨hrlH, hrl, hS2, hg2⟩, hf2⟩
  dsimp only at hrlH hrl hS2 hg2
  subst hrl
  rw [crsK2_some]
  have hg02 := hg1.trans hg2
  -- `class_gen_rule`
  refine RSim.bind (K := crsK3 n visT visR g rco rcl cgo cgl cvR c xo xl (UInt64.ofNat px)) (by rw [crsK3])
    (ruW_sim dn visR feR n m2 a2 g rco rcl cgo cgl (r2.headD 0) c (UInt64.ofNat px) G X recCls cvGs hS2
      (hG.grow (decCG_mono _) hg02) hns (hX'.grow (decCC_mono _) hg02) hrlH
      (hrc.grow (OMono.decNL _ _) hg02) hrcb (hcg.grow (OMono.decPL (fun q => OMono.decCVp q) _ _) hg02)
      hcgb (hf2 hA1)) ?_
  rintro ⟨r3, m3⟩ o3 a3 - ⟨⟨hS3, hg3, ho3⟩, hA3⟩
  dsimp only at hS3 hg3 ho3
  cases o3 with
  | none => rw [crsK3_fail (h := ho3)]; exact RSim.none
  | some gen =>
  obtain ⟨h31, hgH, hgd⟩ := ho3
  rw [crsK3_ok (h := by rw [h31]; decide)]
  subst hgd
  have hg03 := hg02.trans hg3
  -- `class_rules_ok_one`
  refine RSim.bind (K := crsK4 n visT visR g rco rcl cgo cgl cvR c xo xl) (by rw [crsK4])
    (Q1 := fun b a' y => StageR dn visR feR b.2 a' ∧ IWGrow m3 b.2 ∧ b.1 = [r3.tail.headD 0] ∧
      y = decI (r3.tail.headD 0) ∧ AbsOK b.2)
    (fun ⟨r4, m4⟩ h4 => by
      obtain ⟨a', hrun, hS', hg, hr⟩ := cr1W_rel h4 hS3 hgH
        (by rw [decCVp_grow_r hg03 hext]; exact hcv) (CVExt_grow hg03 hext)
        (hG.grow (decCG_mono _) hg03) hns (hX'.grow (decCC_mono _) hg03)
      exact ⟨_, a', hrun, hS', hg, hr, rfl, cr1W_afr h4 hA3⟩) ?_
  rintro ⟨r4, m4⟩ y a4 - ⟨hS4, hg4, hr4, rfl, hA4⟩
  dsimp only at hS4 hg4 hr4
  subst hr4
  rw [crsK4_some]
  have hg04 := hg03.trans hg4
  -- the rest
  have hxo1 := rec2ToNat_succ (o := xo) (i := xo.toNat) (Nat.le_refl _) (by omega)
  have hxl1 := rec2ToNat_pred hxl
  refine RSim.bind (K := crsK5 n (r3.tail.headD 0)) rfl
    (ih m4 a4 (xo + 1) (xl - 1) Xs' hS4 (hG.grow (decCG_mono _) hg04) (hrc.grow (OMono.decNL _ _) hg04)
      (hcg.grow (OMono.decPL (fun q => OMono.decCVp q) _ _) hg04)
      (by rw [decCVp_grow_r hg04 hext]; exact hcv) (CVExt_grow hg04 hext)
      (by rw [hxo1, hxl1, hjx]; exact (show DecB (fun m => decPL m (decCC m) (xo.toNat + 1) jx) m Xs' from
        hXsT).grow (OMono.decPL (fun q => decCC_mono q) _ _) hg04) hA4) ?_
  rintro ⟨r5, m5⟩ rs a5 - ⟨⟨hS5, hg5, hrs, hrsb⟩, hA5⟩
  dsimp only at hS5 hg5 hrs hrsb
  rw [crsK5_some]
  refine RSim.lstep (K := crsK6) rfl fun ⟨r6, m6⟩ h6 => ?_
  rw [getD_zero, getD_one] at hrs hrsb
  obtain ⟨hS6, hg6, hd6, ht6⟩ := consW_stage h6 hS5 hrsb hgH hrs
  rw [crsK6_some]
  refine RSim.pure_some ⟨⟨hS6, hg04.trans (hg5.trans hg6), ?_, ?_⟩, consW_afr h6 hA5⟩ <;>
    simp only [getD_zero, getD_one, List.headD_cons, List.tail_cons]
  · exact hd6
  · exact Nat.le_of_eq ht6

/-- **`class_rules_ok` refines `classRulesOk`** (through `class_gen_rule`'s and `class_rule_ok`'s
stubs): the rules, a handle slice below the top. -/
@[refines ConRon.Arena.classRulesOk]
theorem classRulesOk_refines (p : Prog) (hp : CrsProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (visT visR : Word) (feR : IFEnv) (g rco rcl cgo cgl cvR c xo xl : Word)
    (G : ClassGen) (recCls : List Nat) (cvGs : List IConstantVal) (cv : IConstantVal) (Xs : List ClassCtor)
    (hS : StageR dn visR feR s₀.mem a₀) (hG : DecB (fun m => decCG m g.toNat) s₀.mem G)
    (hns : G.nP + G.slots.length < 2 ^ 64)
    (hrc : DecB (fun m => decNL m rco.toNat rcl.toNat) s₀.mem recCls) (hrcb : rco.toNat + rcl.toNat < 2 ^ 64)
    (hcg : DecB (fun m => decPL m (decCVp m) cgo.toNat cgl.toNat) s₀.mem cvGs)
    (hcgb : cgo.toNat + cgl.toNat < 2 ^ 64)
    (hcv : decCVp s₀.mem cvR.toNat = some cv) (hext : CVExt s₀.mem cvR.toNat)
    (hXs : DecB (fun m => decPL m (decCC m) xo.toNat xl.toNat) s₀.mem Xs) (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_rules_ok" [visT, visR, g, rco, rcl, cgo, cgl, cvR, c, xo, xl]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classRulesOk V visT.toNat feR G recCls cvGs cv c.toNat Xs) a₀ ∧
      KP dn visR feR s₀.mem decEL (r, s'.mem)
        (AM.st (ConRon.Arena.classRulesOk V visT.toNat feR G recCls cvGs cv c.toNat Xs) a₀)
        (AM.res (ConRon.Arena.classRulesOk V visT.toNat feR G recCls cvGs cv c.toNat Xs) a₀) ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (classRulesOk_spec p hp n s₀ visT visR g rco rcl cgo cgl cvR c xo xl) fun _ _ ⟨hl, hw⟩ =>
    let h := (crsW_sim dn visT visR feR g rco rcl cgo cgl cvR c G recCls cvGs cv hns hrcb hcgb n _ a₀ xo xl Xs hS hG
      hrc hcg hcv hext hXs hA).am hw
    ⟨hl, h.1, h.2.1, h.2.2⟩

end L.Ind
