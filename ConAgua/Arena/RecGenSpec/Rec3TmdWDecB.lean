import ConAgua.Arena.RecClassSpec.ClassGenRule
import ConAgua.Arena.RecGenSpec.CfhW
import ConAgua.Arena.RecGenSpec.CrsProg
import ConAgua.Arena.RecGenSpec.DecRR
import ConAgua.Arena.RecGenSpec.Rec3CVX
import ConAgua.Arena.RecGenSpec.RgW
import ConAgua.Arena.IndSumSpec.Row

/-!
# Rec3TmdWDecB

`crsW`, `crsK1`, `crsK2`, `crsK3`, `crsK4`, `crsW_nil` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

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

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `target_major_at`'s record, decoded below the tops -/

/-- A `TargetMajor` record below the top with empty slices reads the same in the cut pools. -/
theorem rec3DecTM_trunc {m : Mem} {q : Nat} (hq : q + 13 ≤ iwTop m) (h3 : iwN m (q + 3) = some 0)
    (h7 : iwN m (q + 7) = some 0) (h10 : iwN m (q + 10) = some 0) (h12 : iwN m (q + 12) = some 0) :
    decTM (truncM m) q = decTM m q := by
  have e : ∀ k, k < 13 → iwN (truncM m) (q + k) = iwN m (q + k) := fun k hk => iwN_truncM (by omega)
  have eh : ∀ {kk : IdxKind} k, k < 13 → (iwH (truncM m) (q + k) : Option (Idx kk)) = iwH m (q + k) :=
    fun k hk => iwH_truncM (by omega)
  have eh0 : ∀ {kk : IdxKind}, (iwH (truncM m) q : Option (Idx kk)) = iwH m q := eh 0 (by omega)
  simp only [decTM, decAt, Nat.add_assoc, Nat.reduceAdd, eh0, eh 1 (by omega), e 2 (by omega),
    e 3 (by omega), e 4 (by omega), e 5 (by omega), e 6 (by omega), e 7 (by omega), e 8 (by omega),
    e 9 (by omega), e 10 (by omega), e 11 (by omega), e 12 (by omega), h3, h7, h10, h12]
  simp [decHL, hslice?, decPL]

/-- **`target_major_default`'s record is decoded below the tops.** -/
theorem rec3TmdW_decB {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {r : List Word} {tm : TargetMajor} (h : tmdW m = some (r, m')) (hS : StageR dn vis fe m a)
    (hd : decTM m' (r.headD 0).toNat = some tm) : DecB (fun m => decTM m (r.headD 0).toNat) m' tm := by
  rw [tmdW_eq] at h
  obtain ⟨⟨ra, m1⟩, h1, h⟩ := of_K h rfl
  rw [tmdK1_some] at h
  obtain ⟨_x1, _a1, _hr1, hS1, _hg1, _hw1, _hl1⟩ := naF_ok dn vis fe m m1 a ra h1 hS
  obtain ⟨ls, hp, h⟩ := of_K h rfl
  rw [tmdK2_some] at h
  obtain ⟨⟨r3, m2⟩, hmk, h⟩ := of_K h rfl
  rw [tmdK3_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨-, -, hsz, -, hc⟩ := hS1.2
  simp only [mkTMW] at hmk
  rcases hal : allocW m1 13 with _ | qm
  · rw [hal] at hmk; simp at hmk
  obtain ⟨q, m1a⟩ := qm
  rw [hal] at hmk
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hmk)
  obtain ⟨hq, rfl, hroom⟩ := allocW_facts hal hsz
  subst hq
  have hroom' : (rdW (m1.arr64 CTL) 200).toNat + 13 ≤ (m1.arr64 IW).size := by simpa using hroom
  have hmem : tmWr (allocMem m1 13) (rdW (m1.arr64 CTL) 200) (ra.headD 0) ls 0 0 0 0 0 0 0 0 0 0 0 =
      wrIW (allocMem m1 13) (rdW (m1.arr64 CTL) 200)
        [ra.headD 0, ls, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
    rw [← tmMem_eq]; rfl
  obtain ⟨hget, -, -, htop⟩ := recMem_post m1 [ra.headD 0, ls, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 13 rfl hc
    (by simpa using hroom') hsz
  simp only [List.headD_cons] at hd ⊢
  rw [hmem] at hd ⊢
  have hz : ∀ k (hk : k < 13),
      iwN (wrIW (allocMem m1 13) (rdW (m1.arr64 CTL) 200) [ra.headD 0, ls, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
        ((rdW (m1.arr64 CTL) 200).toNat + k) =
        some (([ra.headD 0, ls, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List Word)[k]'(by simpa using hk)).toNat := by
    intro k hk
    simp only [iwN, nat?, iwA, hget k (by simpa using hk)]
    rw [List.getElem?_eq_getElem (by simp; omega)]; rfl
  have htop' : iwTop (wrIW (allocMem m1 13) (rdW (m1.arr64 CTL) 200)
      [ra.headD 0, ls, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) = (rdW (m1.arr64 CTL) 200).toNat + 13 := by
    simp only [iwTop, htop]; rw [UInt64.toNat_add]; simp only [UInt64.reduceToNat]; omega
  show decTM (truncM _) _ = some tm
  rw [rec3DecTM_trunc (by omega) (hz 3 (by omega)) (hz 7 (by omega)) (hz 10 (by omega)) (hz 12 (by omega))]
  exact hd

/-- **`target_major_at`, its record decoded below the tops.** -/
theorem rec3TMA_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem)
    (a : AState) (mo ml c : Word) (ms : List TargetMajor) (hS : StageR dn vis fe m a)
    (hms : DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) m ms) (hb : mo.toNat + ml.toNat < 2 ^ 64) :
    RSim (tmaW n m mo ml c) (ConRon.Arena.targetMajorAt ms c.toNat) a
      (fun b a' tm => StageR dn vis fe b.2 a' ∧ IWGrow m b.2 ∧
        DecB (fun m => decTM m (b.1.headD 0).toNat) b.2 tm) := by
  have hms0 : decPL m (decTM m) mo.toNat ml.toNat = some ms :=
    hms.get (OMono.decPL (fun q => decTM_mono q) _ _)
  have hlen := decPL_length m hms0
  intro b hb'
  obtain ⟨tm, a', hrun, hS', hg, hd⟩ := tmaW_sim dn vis fe n m a mo ml c ms hS hms0 hb b hb'
  refine ⟨tm, a', hrun, hS', hg, ?_⟩
  rcases n with _ | n
  · simp [tmaW] at hb'
  by_cases hcl : c < ml
  · rw [tmaW_hit n m mo ml c hcl] at hb'
    cases hb'
    have hc' : c.toNat < ml.toNat := UInt64.lt_iff_toNat_lt.mp hcl
    obtain ⟨v, hv, hdv⟩ := decPL_getH (truncM m) hms c.toNat hc'
    obtain ⟨-, hv'⟩ := rec2IwN_trunc hv
    have hrd := iwN_rdW_at (w := mo) (k := c.toNat) hv' hS.2.2.2.1
    have hcw : mo + UInt64.ofNat c.toNat = mo + c := by simp
    rw [hcw] at hrd
    have hrun' : ConRon.Arena.targetMajorAt ms c.toNat = pure (ms[c.toNat]'(by omega)) := by
      simp [ConRon.Arena.targetMajorAt, List.getElem?_eq_getElem (by omega : c.toNat < ms.length)]
    rw [hrun'] at hrun
    have hx : ms[c.toNat]'(by omega) = tm := by injection hrun with e; injection e
    simp only [List.headD_cons]
    rw [hrd.1, UInt64.toNat_ofNat_of_lt' hrd.2, ← hx]
    exact (show DecB (fun m => decTM m v) m _ from hdv).grow (decTM_mono _) (IWGrow.refl m)
  · rw [tmaW_miss n m mo ml c hcl] at hb'
    obtain ⟨⟨r0, m0⟩, ho, hb'⟩ := of_K hb' rfl
    rw [tmaK_some] at hb'
    cases hb'
    rcases n with _ | n
    · cases ho
    simp only [fuelW_succ] at ho
    simp only [List.headD_cons] at hd ⊢
    exact rec3TmdW_decB ho hS hd

/-- The slice of results: decoded below the tops, and below the top. -/
def decRRS (m' : Mem) (r : List Word) (xs : List (IConstantVal × TargetMajor × List EIdx)) : Prop :=
  DecB (fun m => decPL m (decRR m) (r.headD 0).toNat (r.tail.headD 0).toNat) m' xs ∧
    (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m'

/-- A fresh `rec4` record of decoded-below-the-tops parts is decoded below the tops. -/
theorem rec3Rec4_decB {m m' : Mem} {cvw mw ro rl : Word} {q : Nat} {cv : IConstantVal} {M : TargetMajor}
    {rhss : List EIdx} (hget : ∀ j < 4, (m'.arr64 IW)[q + j]? = [cvw, mw, ro, rl][j]?)
    (hq : q + 4 ≤ iwTop m') (hg : IWGrow m m')
    (hcv : DecB (fun m => decCVp m cvw.toNat) m cv) (hM : DecB (fun m => decTM m mw.toNat) m M)
    (hr : DecB (fun m => (decHL m ro.toNat rl.toNat : Option (List EIdx))) m rhss) :
    DecB (fun m => decRR m q) m' (cv, M, rhss) := by
  have hw : ∀ j (hj : j < 4), iwN (truncM m') (q + j) = some ([cvw, mw, ro, rl][j]'(by simpa using hj)).toNat :=
    fun j hj => by
      rw [iwN_truncM (by omega)]
      simp only [iwN, nat?, iwA, hget j hj]
      rw [List.getElem?_eq_getElem (by simp; omega)]; rfl
  have h0 := hw 0 (by omega)
  have h1 := hw 1 (by omega)
  have h2 := hw 2 (by omega)
  have h3 := hw 3 (by omega)
  simp only [Nat.add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2 h3
  show decRR (truncM m') q = _
  have e1 : decCVp (truncM m') cvw.toNat = some cv := hcv.grow (OMono.decCVp _) hg
  have e2 : decTM (truncM m') mw.toNat = some M := hM.grow (decTM_mono _) hg
  have e3 : (decHL (truncM m') ro.toNat rl.toNat : Option (List EIdx)) = some rhss := hr.grow (OMono.decHL _ _) hg
  simp only [decRR, decAt, h0, h1, Nat.add_assoc, Nat.reduceAdd, h2, h3, Option.bind_eq_bind,
    Option.bind_some, e1, e2, e3]
  rfl

/-- A stable constant record is decoded below the tops. -/
theorem rec3CVX_decB {m : Mem} {p : Nat} {cv : IConstantVal} (h : StabD (fun m => decCVX m p) m cv) :
    DecB (fun m => decCVp m p) m cv := by
  obtain ⟨h1, h2⟩ := rec3CVX h
  show decCV (erA (truncM m)) p = some cv
  rw [rec2DecCV_agree (a := erA m) (T := erTop m) (fun i hi => truncM_er_eq hi) h2.1 h2.2]
  exact h1

/-- A stable constant slice is decoded below the tops. -/
theorem rec3SPL_decB {m : Mem} {o l : Nat} {cvs : List IConstantVal} (h : SPL decCVX m o l cvs) :
    DecB (fun m => decPL m (decCVp m) o l) m cvs := by
  obtain ⟨hb, ps, hps, hf⟩ := h
  show decPL (truncM m) (decCVp (truncM m)) o l = some cvs
  have e : decNL (truncM m) o l = some ps := decNL_decB hps hb
  rw [decPL_eq_bind, e]
  simp only [Option.bind_some]
  clear e hps hb
  induction hf with
  | nil => rfl
  | @cons q x qs xs h1 _ ih =>
    have e1 : decCVp (truncM m) q = some x := rec3CVX_decB h1
    simp only [List.mapM_cons, e1, ih]; rfl

def crrK4 (n : Nat) (y : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => crrK5 (consW n m4 y (r4.headD 0) (r4.tail.headD 0))

mutual
/-- **The model of `class_recs_rules_ok_go`.** -/
noncomputable def crrW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, visT, visR, g, rco, rcl, cgo, cgl, vo, vl, co, cl =>
    if vl = 0 then some ([0, 0], m)
    else if cl = 0 then some ([0, 0], m)
    else crrK1 cR n visT visR g rco rcl cgo cgl vo vl co cl (rdW (m.arr64 IW) vo) (rdW (m.arr64 IW) co)
      (crsW cR n m visT visR g rco rcl cgo cgl (rdW (m.arr64 IW) vo) (rdW (m.arr64 IW) co)
        (crrXs m g (rdW (m.arr64 IW) co)).1 (crrXs m g (rdW (m.arr64 IW) co)).2)
noncomputable def crrK1 (cR : CallM) (n : Nat) (visT visR g rco rcl cgo cgl vo vl co cl cvG c : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => crrK2 cR n visT visR g rco rcl cgo cgl vo vl co cl cvG (r1.headD 0) (r1.tail.headD 0)
      (tmaW n m1 (rdW (m1.arr64 IW) (g + 3)) (rdW (m1.arr64 IW) (g + 4)) c)
noncomputable def crrK2 (cR : CallM) (n : Nat) (visT visR g rco rcl cgo cgl vo vl co cl cvG ro rl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => crrK3 cR n visT visR g rco rcl cgo cgl vo vl co cl (recW m2 4 [cvG, r2.headD 0, ro, rl])
noncomputable def crrK3 (cR : CallM) (n : Nat) (visT visR g rco rcl cgo cgl vo vl co cl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) =>
    crrK4 n (r3.headD 0) (crrW cR n m3 visT visR g rco rcl cgo cgl (vo + 1) (vl - 1) (co + 1) (cl - 1))
end

/-- **The model of `class_recs_rules_ok`.** -/
noncomputable def crraW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, visT, visR, g, rco, rcl, cgo, cgl =>
    crrK5 (crrW cR n m visT visR g rco rcl cgo cgl cgo cgl rco rcl)

section arms
variable (cR : CallM) (n : Nat) (m m1 m2 m3 m4 m5 : Mem) (visT visR g rco rcl cgo cgl vo vl co cl cvG c ro rl y : Word)
  (r1 r2 r3 r4 r5 : List Word)
theorem crrXs_hit (h : c < rdW (m.arr64 IW) (g + 10)) : crrXs m g c =
    (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (g + 9) + c)),
     rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (g + 9) + c) + 1)) := by
  rw [crrXs, ite_eq_left h]
theorem crrXs_miss (h : ¬ c < rdW (m.arr64 IW) (g + 10)) : crrXs m g c = (0, 0) := by
  rw [crrXs, ite_eq_right h]
theorem crrW_nil1 (h : vl = 0) : crrW cR (n + 1) m visT visR g rco rcl cgo cgl vo vl co cl = some ([0, 0], m) := by
  simp [crrW, h]
theorem crrW_nil2 (h1 : ¬ vl = 0) (h : cl = 0) :
    crrW cR (n + 1) m visT visR g rco rcl cgo cgl vo vl co cl = some ([0, 0], m) := by
  simp only [crrW]; rw [ite_eq_right h1, ite_eq_left h]
theorem crrW_cons (h1 : ¬ vl = 0) (h : ¬ cl = 0) : crrW cR (n + 1) m visT visR g rco rcl cgo cgl vo vl co cl =
    crrK1 cR n visT visR g rco rcl cgo cgl vo vl co cl (rdW (m.arr64 IW) vo) (rdW (m.arr64 IW) co)
      (crsW cR n m visT visR g rco rcl cgo cgl (rdW (m.arr64 IW) vo) (rdW (m.arr64 IW) co)
        (crrXs m g (rdW (m.arr64 IW) co)).1 (crrXs m g (rdW (m.arr64 IW) co)).2) := by
  simp only [crrW]; rw [ite_eq_right h1, ite_eq_right h]
theorem crrK1_some : crrK1 cR n visT visR g rco rcl cgo cgl vo vl co cl cvG c (some (r1, m1)) =
    crrK2 cR n visT visR g rco rcl cgo cgl vo vl co cl cvG (r1.headD 0) (r1.tail.headD 0)
      (tmaW n m1 (rdW (m1.arr64 IW) (g + 3)) (rdW (m1.arr64 IW) (g + 4)) c) := by rw [crrK1]
theorem crrK2_some : crrK2 cR n visT visR g rco rcl cgo cgl vo vl co cl cvG ro rl (some (r2, m2)) =
    crrK3 cR n visT visR g rco rcl cgo cgl vo vl co cl (recW m2 4 [cvG, r2.headD 0, ro, rl]) := by rw [crrK2]
theorem crrK3_some : crrK3 cR n visT visR g rco rcl cgo cgl vo vl co cl (some (r3, m3)) =
    crrK4 n (r3.headD 0) (crrW cR n m3 visT visR g rco rcl cgo cgl (vo + 1) (vl - 1) (co + 1) (cl - 1)) := by
  rw [crrK3]
theorem crrK4_some : crrK4 n y (some (r4, m4)) = crrK5 (consW n m4 y (r4.headD 0) (r4.tail.headD 0)) := rfl
theorem crrK5_some : crrK5 (some (r5, m5)) = some ([r5.headD 0, r5.tail.headD 0], m5) := rfl
theorem crraW_eq : crraW cR (n + 1) m visT visR g rco rcl cgo cgl =
    crrK5 (crrW cR n m visT visR g rco rcl cgo cgl cgo cgl rco rcl) := rfl
end arms

grind_pattern [ind_grind] crrXs_hit => crrXs m g c
grind_pattern [ind_grind] crrXs_miss => crrXs m g c
grind_pattern [ind_grind] crrW_nil1 => crrW cR (n + 1) m visT visR g rco rcl cgo cgl vo vl co cl
grind_pattern [ind_grind] crrW_nil2 => crrW cR (n + 1) m visT visR g rco rcl cgo cgl vo vl co cl
grind_pattern [ind_grind] crrW_cons => crrW cR (n + 1) m visT visR g rco rcl cgo cgl vo vl co cl
grind_pattern [ind_grind] crrK1_some => crrK1 cR n visT visR g rco rcl cgo cgl vo vl co cl cvG c (some (r1, m1))
grind_pattern [ind_grind] crrK2_some => crrK2 cR n visT visR g rco rcl cgo cgl vo vl co cl cvG ro rl (some (r2, m2))
grind_pattern [ind_grind] crrK3_some => crrK3 cR n visT visR g rco rcl cgo cgl vo vl co cl (some (r3, m3))
grind_pattern [ind_grind] crrK4_some => crrK4 n y (some (r4, m4))
grind_pattern [ind_grind] crrK5_some => crrK5 (some (r5, m5))
grind_pattern [ind_grind] crraW_eq => crraW cR (n + 1) m visT visR g rco rcl cgo cgl

/-- The lookups `class_recs_rules_ok` needs. -/
structure CrrProg (p : Prog) : Prop where
  crs : CrsProg p
  pw : p.lookup "pin_word" = some pinWordL
  mtm : p.lookup "mk_target_major" = some mkTargetMajor
  tmd : p.lookup "target_major_default" = some targetMajorDefault
  tma : p.lookup "target_major_at" = some targetMajorAt
  na : NaF p
  rec4 : p.lookup "rec4" = some rec4
  go : p.lookup "class_recs_rules_ok_go" = some classRecsRulesOkGo
  top : p.lookup "class_recs_rules_ok" = some classRecsRulesOkL

set_option maxHeartbeats 1000000 in
theorem classRecsRulesOkGo_spec (p : Prog) (h : CrrProg p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) :
    ∀ (s₀ : St) (visT visR g rco rcl cgo cgl vo vl co cl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_recs_rules_ok_go" [visT, visR, g, rco, rcl, cgo, cgl, vo, vl, co, cl]
    ⦃fun r s' => LocEq s' s₀ ∧ crrW cR n s₀.mem visT visR g rco rcl cgo cgl vo vl co cl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ visT visR g rco rcl cgo cgl vo vl co cl
    rw [invoke_eq _ h.go]; simp only [callFn, classRecsRulesOkGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ visT visR g rco rcl cgo cgl vo vl co cl
    rw [invoke_eq _ h.go]
    simp only [callFn, classRecsRulesOkGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        classRulesOk_spec p h.crs cR hcR n,
        targetMajorAt_spec p h.crs.alloc h.pw h.mtm h.tmd h.tma h.na n,
        rec4_specW p h.crs.alloc n h.rec4, slCons_specW p h.crs.alloc h.crs.copy h.crs.cons n, ih] <;>
      finish (gen := 20) (instances := 5000) [rdW_eq, loc_init4, loc_init5, loc_init6, loc_init7, loc_init8,
        loc_init9, loc_init10]

theorem classRecsRulesOk_spec (p : Prog) (h : CrrProg p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) (s₀ : St) (visT visR g rco rcl cgo cgl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_recs_rules_ok" [visT, visR, g, rco, rcl, cgo, cgl]
    ⦃fun r s' => LocEq s' s₀ ∧ crraW cR n s₀.mem visT visR g rco rcl cgo cgl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.top]
  simp only [callFn, classRecsRulesOkL]
  rcases n with _ | n
  · vcgen [exec] <;> grind
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, classRecsRulesOkGo_spec p h cR hcR n] <;>
    finish (gen := 20) [loc_init4, loc_init5, loc_init6]

/-! ## The relational lemma -/

/-- The constructors of class `c`, as `class_recs_rules_ok_go` reads them. -/
theorem rec3CtorsAt {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}
    {g c : Word} {G : ClassGen} (hS : StageR dn vis fe m a) (hG : DecB (fun m => decCG m g.toNat) m G) :
    DecB (fun m' => decPL m' (decCC m') (crrXs m g c).1.toNat (crrXs m g c).2.toNat) m (G.ctors.getD c.toNat []) := by
  have hsz := hS.2.2.2.1
  obtain ⟨-, o9, l9, h9, h10, hct⟩ := rec3CG_parts hG
  obtain ⟨e9, t9⟩ := rec2RdN (w := g) (k := 9) h9 hsz
  obtain ⟨e10, t10⟩ := rec2RdN (w := g) (k := 10) h10 hsz
  simp only [show UInt64.ofNat 9 = (9 : Word) from rfl, show UInt64.ofNat 10 = (10 : Word) from rfl] at e9 e10
  have hlen : G.ctors.length = l9 := decPL_length _ hct
  by_cases hc : c < rdW (m.arr64 IW) (g + 10)
  · rw [crrXs_hit (h := hc)]
    rw [e10] at hc
    have hc' : c.toNat < l9 := by have := UInt64.lt_iff_toNat_lt.mp hc; rw [t10] at this; exact this
    obtain ⟨v, hv, hdv⟩ := decPL_getH (truncM m) hct c.toNat hc'
    obtain ⟨-, hvm⟩ := rec2IwN_trunc hv
    obtain ⟨ev, tv⟩ := rec2RdN (w := UInt64.ofNat o9) (k := c.toNat) (by rw [t9]; exact hvm) hsz
    simp only [UInt64.ofNat_toNat] at ev
    simp only [decLH] at hdv
    obtain ⟨xo, xl, hxo, hxl, hxs⟩ := decAt_some hdv
    obtain ⟨exo, txo⟩ := rec2RdN (w := UInt64.ofNat v) (k := 0) (by rw [tv]; exact (rec2IwN_trunc hxo).2) hsz
    obtain ⟨exl, txl⟩ := rec2RdN (w := UInt64.ofNat v) (k := 1) (by rw [tv]; exact (rec2IwN_trunc hxl).2) hsz
    simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero,
      show UInt64.ofNat 1 = (1 : Word) from rfl] at exo exl
    simp only [e9, ev, exo, exl, txo, txl]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : c.toNat < G.ctors.length),
      Option.getD_some]
    exact hxs
  · rw [crrXs_miss (h := hc)]
    rw [e10] at hc
    have hc' : ¬ c.toNat < l9 := fun x => hc (by rw [← t10] at x; exact UInt64.lt_iff_toNat_lt.mpr x)
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : G.ctors.length ≤ c.toNat),
      Option.getD_none]
    show decPL (truncM m) _ _ _ = some []
    simp [decPL]

end L.Ind

end

end
