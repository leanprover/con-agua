import ConAgua.Arena.IndRealOpf3
import ConAgua.Arena.RecCheckSpec.ErToIwWStage

/-!
# IhW

`classRecOf_spec`, `crOf`, `crOf_eq`, `decCVp_name`, `classRecOfW_ok`, `msK` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem classRecOf_spec (p : Prog) (hp : p.lookup "class_rec_of" = some classRecOf) (n : Nat) :
    ∀ (s₀ : St) (rco rcl cgo cgl t : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_rec_of" [rco, rcl, cgo, cgl, t]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ classRecOfW n s₀.mem rco rcl cgo cgl t = some r; ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ rco rcl cgo cgl t; rw [invoke_eq _ hp]; simp only [callFn, classRecOf]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ rco rcl cgo cgl t
    rw [invoke_eq _ hp]
    simp only [callFn, classRecOf]
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih]
    all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Locals.init, List.getD_cons_zero, List.getD_cons_succ, Cmp.eval,
      BinOp.eval, Nat.reduceEqDiff, reduceIte, beq_iff_eq, bne_iff_ne, ne_eq] at *)
    all_goals grind (gen := 20) [lang_grind, arena_grind, ind_grind, croK]

/-- The twin's `classRecOf`, as a recursion on the shifted lists. -/
def crOf (t : Nat) : List Nat → List IConstantVal → Option NIdx
  | _, [] => none
  | rc, cv :: cs => if rc.headD 0 == t then some cv.name else crOf t rc.tail cs

theorem crOf_eq (t : Nat) : ∀ (cs : List IConstantVal) (rc : List Nat),
    ((List.range cs.length).find? fun r => rc.getD r 0 == t).map (fun r => (cs.getD r default).name) =
      crOf t rc cs := by
  intro cs
  induction cs with
  | nil => intro rc; simp [crOf]
  | cons cv cs ih =>
    intro rc
    have e0 : rc.getD 0 0 = rc.headD 0 := by cases rc <;> simp
    have e1 : ∀ r, rc.getD (r + 1) 0 = rc.tail.getD r 0 := by intro r; cases rc <;> simp
    rw [List.length_cons, List.range_succ_eq_map, List.find?_cons, e0]
    by_cases h : (rc.headD 0 == t) = true
    · simp only [h, crOf, ite_true, Option.map_some]; rfl
    · have h' : ¬ (rc.headD 0 == t) = true := h
      simp only [h', crOf, Bool.false_eq_true, ite_false]
      rw [← ih rc.tail, List.find?_map]
      simp only [Option.map_map, Function.comp_def, e1, List.getD_cons_succ]

theorem decCVp_name {m : Mem} {q : Nat} {cv : IConstantVal} (h : decCVp m q = some cv) :
    ∃ w, (m.arr64 EREC)[q]? = some w ∧ w.toNat < 2 ^ 32 ∧ decI w = cv.name := by
  simp only [decCVp, decCV, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨nm, hnm, -, -, -, -, -, rfl⟩ := h
  simp only [hd?] at hnm
  cases hq : (erA m)[q]? with
  | none => simp [hq] at hnm
  | some w =>
    simp only [hq] at hnm
    by_cases hl : w.toNat < 2 ^ 32
    · simp [hl] at hnm
      exact ⟨w, by simpa [erA] using hq, hl, hnm⟩
    · simp [hl] at hnm

theorem classRecOfW_ok (n : Nat) : ∀ (m : Mem) (rco rcl cgo cgl t : Word) (r : List Word)
    (rc : List Nat) (cs : List IConstantVal),
    classRecOfW n m rco rcl cgo cgl t = some r → decNL m rco.toNat rcl.toNat = some rc →
    decPL m (decCVp m) cgo.toNat cgl.toNat = some cs → rco.toNat + rcl.toNat < 2 ^ 64 →
    cgo.toNat + cgl.toNat < 2 ^ 64 →
    (crOf t.toNat rc cs = none → r = [0, 0]) ∧
    ∀ nm, crOf t.toNat rc cs = some nm → r.headD 0 = 1 ∧ (r.tail.headD 0).toNat < 2 ^ 32 ∧
      decI (r.tail.headD 0) = nm := by
  induction n with
  | zero => intro m rco rcl cgo cgl t r rc cs h; simp [classRecOfW] at h
  | succ n ih =>
    intro m rco rcl cgo cgl t r rc cs h hrc hcs hb1 hb2
    by_cases hcgl : cgl = 0
    · rw [classRecOfW_nil n m rco rcl cgo cgl t hcgl] at h
      simp only [Option.some.injEq] at h
      subst h
      have : cgl.toNat = 0 := by rw [hcgl]; rfl
      rw [this] at hcs
      simp [decPL] at hcs
      subst hcs
      exact ⟨fun _ => rfl, fun nm hnm => by simp [crOf] at hnm⟩
    · obtain ⟨c1, hc1, hcgl1⟩ := wordSucc_of_ne hcgl
      rw [hc1] at hcs
      obtain ⟨pn, cv, cs', rfl, hpn, hcv, hcs'⟩ := decPL_cons hcs
      have hgo : cgo.toNat < (m.arr64 IW).size := iwN_lt hpn
      have hpn' := iwN_rdW hpn (by omega)
      rw [UInt64.ofNat_toNat] at hpn'
      obtain ⟨wn, hwn1, hwn2, hwn3⟩ := decCVp_name hcv
      have hcgo1 : (cgo + 1).toNat = cgo.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      -- the first recursion-count entry and the shifted slice
      obtain ⟨v, rc', P1, P2, P3, P4, P5, P6⟩ : ∃ (v : Word) (rc' : List Nat),
          (if rcl ≠ 0 then rdW (m.arr64 IW) rco else 0) = v ∧
          (rcl ≠ 0 → rco.toNat < (m.arr64 IW).size) ∧ rc.headD 0 = v.toNat ∧ rc.tail = rc' ∧
          decNL m (rco + 1).toNat (if rcl ≠ 0 then rcl - 1 else 0).toNat = some rc' ∧
          (rco + 1).toNat + (if rcl ≠ 0 then rcl - 1 else 0).toNat < 2 ^ 64 := by
        by_cases hrcl : rcl = 0
        · have hr0 : rcl.toNat = 0 := by rw [hrcl]; rfl
          rw [hr0] at hrc
          simp [decNL] at hrc
          subst hrc
          refine ⟨0, [], by simp [hrcl], fun h => absurd hrcl h, by simp, by simp, ?_, ?_⟩
          · simp [hrcl, decNL]
          · simp [hrcl]; omega
        · obtain ⟨r1, hr1, hrcl1⟩ := wordSucc_of_ne hrcl
          rw [hr1, decNL_succ] at hrc
          simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hrc
          obtain ⟨x, hx, xs, hxs, rfl⟩ := hrc
          have hx' := iwN_rdW hx (by omega)
          rw [UInt64.ofNat_toNat] at hx'
          have hrco1 : (rco + 1).toNat = rco.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
          refine ⟨UInt64.ofNat x, xs, by simp [hrcl, hx'.1], fun _ => iwN_lt hx, ?_, rfl, ?_, ?_⟩
          · rw [UInt64.toNat_ofNat_of_lt' hx'.2]; rfl
          · simp only [hrcl, ne_eq, not_false_eq_true, ite_true, hrco1, hrcl1]; exact hxs
          · simp only [hrcl, ne_eq, not_false_eq_true, ite_true, hrco1, hrcl1]; omega
      have hxv : (v = t) ↔ (rc.headD 0 == t.toNat) = true := by
        rw [P3]
        constructor
        · intro e; subst e; simp
        · intro e; simp at e; exact UInt64.toNat_inj.mp e
      have hcrOf : crOf t.toNat rc (cv :: cs') =
          if (rc.headD 0 == t.toNat) = true then some cv.name else crOf t.toNat rc' cs' := by
        simp only [crOf, P4]
      by_cases hvt : v = t
      · rw [classRecOfW_hit n m rco rcl cgo cgl t hcgl P2 (by rw [P1]; exact hvt)] at h
        have hpe : pn < (m.arr64 EREC).size := (Array.getElem?_eq_some_iff.mp hwn1).1
        have hg : cgo.toNat < (m.arr64 IW).size ∧
            (rdW (m.arr64 IW) cgo).toNat < (m.arr64 EREC).size := by
          refine ⟨hgo, ?_⟩
          have e : (m.arr64 IW)[cgo.toNat]? = some (UInt64.ofNat pn) := by
            have := hpn'.1
            simpa [rdW, hgo] using this
          rw [hpn'.1, UInt64.toNat_ofNat_of_lt' hpn'.2]; exact hpe
        rw [ite_eq_left hg] at h
        simp only [Option.some.injEq] at h
        subst h
        have hrd : rdW (m.arr64 EREC) (rdW (m.arr64 IW) cgo) = wn := by
          rw [hpn'.1]
          simp [rdW, UInt64.toNat_ofNat_of_lt' hpn'.2, hwn1]
        rw [hrd, hcrOf, ite_eq_left (hxv.mp hvt)]
        refine ⟨fun e => by simp at e, fun nm hnm => ?_⟩
        simp only [Option.some.injEq] at hnm
        subst hnm
        exact ⟨rfl, by simpa using hwn2, by simpa using hwn3⟩
      · rw [classRecOfW_miss n m rco rcl cgo cgl t hcgl P2 (by rw [P1]; exact hvt)] at h
        obtain ⟨r1, hr, h⟩ := of_K h rfl
        simp only [croK, Option.some.injEq] at h
        subst h
        have hcs'' : decPL m (decCVp m) (cgo + 1).toNat (cgl - 1).toNat = some cs' := by
          rw [hcgo1, hcgl1]; exact hcs'
        obtain ⟨g1, g2⟩ := ih m (rco + 1) _ (cgo + 1) (cgl - 1) t r1 rc' cs' hr P5 hcs'' P6
          (by rw [hcgo1, hcgl1]; omega)
        have hn : ¬ (rc.headD 0 == t.toNat) = true := fun e => hvt (hxv.mpr e)
        rw [hcrOf, ite_eq_right hn]
        refine ⟨fun e => ?_, fun nm hnm => ?_⟩
        · have := g1 e; simp [this]
        · obtain ⟨a1, a2, a3⟩ := g2 nm hnm
          exact ⟨a1, a2, a3⟩

/-! ## `class_read_motive_slot` (the `while` rewritten as a self-recursion on the shifted slice) -/

/-- After the recursive call: shift the position. -/
def msK : Option (List Word) → Option (List Word)
  | none => none
  | some r => if r.headD 0 = 0 then some [0, 0] else some [1, r.tail.headD 0 + 1]

/-- **The model of `class_read_motive_slot`.** -/
def msW : Nat → Mem → Word → Word → Word → Option (List Word)
  | 0, _, _, _, _ => none
  | n + 1, m, so, sl, c =>
    if sl = 0 then some [0, 0]
    else if ¬ so.toNat < (m.arr64 IW).size then none
    else if ¬ (rdW (m.arr64 IW) so).toNat < (m.arr64 IW).size then none
    else if rdW (m.arr64 IW) (rdW (m.arr64 IW) so) = 0 then
      (if c = 0 then some [1, 0] else msK (msW n m (so + 1) (sl - 1) (c - 1)))
    else msK (msW n m (so + 1) (sl - 1) c)

section arms
variable (n : Nat) (m : Mem) (so sl c : Word)
theorem msW_nil (h : sl = 0) : msW (n + 1) m so sl c = some [0, 0] := by simp [msW, h]
theorem msW_hit (h : sl ≠ 0) (h1 : so.toNat < (m.arr64 IW).size)
    (h2 : (rdW (m.arr64 IW) so).toNat < (m.arr64 IW).size) (h3 : rdW (m.arr64 IW) (rdW (m.arr64 IW) so) = 0)
    (hc : c = 0) : msW (n + 1) m so sl c = some [1, 0] := by
  simp [msW, h, h1, h2, h3, hc]
theorem msW_mot (h : sl ≠ 0) (h1 : so.toNat < (m.arr64 IW).size)
    (h2 : (rdW (m.arr64 IW) so).toNat < (m.arr64 IW).size) (h3 : rdW (m.arr64 IW) (rdW (m.arr64 IW) so) = 0)
    (hc : c ≠ 0) : msW (n + 1) m so sl c = msK (msW n m (so + 1) (sl - 1) (c - 1)) := by
  simp [msW, h, h1, h2, h3, hc]
theorem msW_min (h : sl ≠ 0) (h1 : so.toNat < (m.arr64 IW).size)
    (h2 : (rdW (m.arr64 IW) so).toNat < (m.arr64 IW).size) (h3 : rdW (m.arr64 IW) (rdW (m.arr64 IW) so) ≠ 0) :
    msW (n + 1) m so sl c = msK (msW n m (so + 1) (sl - 1) c) := by
  simp [msW, h, h1, h2, h3]
end arms

grind_pattern [ind_grind] msW_nil => msW (n + 1) m so sl c
grind_pattern [ind_grind] msW_hit => msW (n + 1) m so sl c
grind_pattern [ind_grind] msW_mot => msW (n + 1) m so sl c
grind_pattern [ind_grind] msW_min => msW (n + 1) m so sl c

theorem classReadMotiveSlot_spec (p : Prog) (hp : p.lookup "class_read_motive_slot" = some classReadMotiveSlot)
    (n : Nat) : ∀ (s₀ : St) (so sl c : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_read_motive_slot" [so, sl, c]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ msW n s₀.mem so sl c = some r; ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ so sl c; rw [invoke_eq _ hp]; simp only [callFn, classReadMotiveSlot]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ so sl c
    rw [invoke_eq _ hp]
    simp only [callFn, classReadMotiveSlot]
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih]
    all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Locals.init, List.getD_cons_zero, List.getD_cons_succ, Cmp.eval,
      BinOp.eval, Nat.reduceEqDiff, reduceIte, beq_iff_eq] at *)
    all_goals grind (gen := 20) [lang_grind, arena_grind, ind_grind, msK]

/-- The indices of the motive slots, counted from `j`. -/
def motIdx : Nat → List ClassSlot → List Nat
  | _, [] => []
  | j, .motive _ :: sls => j :: motIdx (j + 1) sls
  | j, .minor .. :: sls => motIdx (j + 1) sls

theorem motIdx_shift : ∀ (sls : List ClassSlot) (j : Nat), motIdx (j + 1) sls = (motIdx j sls).map (· + 1) := by
  intro sls
  induction sls with
  | nil => intro j; simp [motIdx]
  | cons sl sls ih =>
    intro j
    cases sl with
    | motive k => simp [motIdx, ih (j + 1)]
    | minor c C ihs => simp [motIdx, ih (j + 1)]

theorem motIdx_eq : ∀ (j : Nat) (sls : List ClassSlot),
    ((List.range sls.length).filter (fun s => match (sls[s]? : Option ClassSlot) with
      | some (.motive _) => true
      | _ => false)).map (j + ·) = motIdx j sls := by
  intro j sls
  induction sls generalizing j with
  | nil => simp [motIdx]
  | cons sl sls ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map]
    have e : (fun s : Nat => match ((sl :: sls)[s]? : Option ClassSlot) with
        | some (.motive _) => true | _ => false) ∘ Nat.succ =
        (fun s : Nat => match (sls[s]? : Option ClassSlot) with
        | some (.motive _) => true | _ => false) := by
      funext s; simp
    rw [e]
    have ih' := ih (j + 1)
    have e2 : ∀ L : List Nat, (L.map Nat.succ).map (j + ·) = L.map ((j + 1) + ·) := by
      intro L; simp [List.map_map, Function.comp_def]; intro x _; omega
    cases sl with
    | motive k => simp [motIdx, e2, ih']
    | minor c C ihs => simp [motIdx, e2, ih']

/-- The result words of a motive-position query. -/
def msRes : Option Nat → List Word
  | some i => [1, UInt64.ofNat i]
  | none => [0, 0]

theorem msK_of (o : Option Nat) (r1 : List Word) (h : r1 = msRes o) :
    msK (some r1) = some (msRes (o.map (· + 1))) := by
  subst h
  cases o <;> simp [msK, msRes, UInt64.ofNat_add]

theorem msW_ok (n : Nat) : ∀ (m : Mem) (so sl c : Word) (r : List Word) (sls : List ClassSlot),
    msW n m so sl c = some r → decPL m (decCS m) so.toNat sl.toNat = some sls →
    so.toNat + sl.toNat < 2 ^ 64 → r = msRes ((motIdx 0 sls)[c.toNat]?) := by
  induction n with
  | zero => intro m so sl c r sls h; simp [msW] at h
  | succ n ih =>
    intro m so sl c r sls h hdec hb
    by_cases hsl : sl = 0
    · rw [msW_nil n m so sl c hsl] at h
      simp only [Option.some.injEq] at h
      subst h
      have : sl.toNat = 0 := by rw [hsl]; rfl
      rw [this] at hdec
      simp [decPL] at hdec
      subst hdec
      simp [motIdx, msRes]
    · obtain ⟨s1, hs1, hsl1⟩ := wordSucc_of_ne hsl
      rw [hs1] at hdec
      obtain ⟨pn, sl', rest, rfl, hpn, hcs, hdec'⟩ := decPL_cons hdec
      have hso : so.toNat < (m.arr64 IW).size := iwN_lt hpn
      have hpn' := iwN_rdW hpn (by omega)
      rw [UInt64.ofNat_toNat] at hpn'
      have hpsz := decCS_ptr_lt hcs
      have htag := decCS_tag hcs
      have htag' := iwN_rdW htag (by have := hpn'.2; omega)
      have hpl : (rdW (m.arr64 IW) so).toNat < (m.arr64 IW).size := by
        rw [hpn'.1, UInt64.toNat_ofNat_of_lt' hpn'.2]; exact hpsz
      have hso1 : (so + 1).toNat = so.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hdec1 : decPL m (decCS m) (so + 1).toNat (sl - 1).toNat = some rest := by
        rw [hso1, hsl1]; exact hdec'
      have hrd : rdW (m.arr64 IW) (rdW (m.arr64 IW) so) = UInt64.ofNat (if sl'.isMinor then 1 else 0) := by
        rw [hpn'.1]; exact htag'.1
      cases sl' with
      | motive k =>
        have hz : rdW (m.arr64 IW) (rdW (m.arr64 IW) so) = 0 := by rw [hrd]; rfl
        by_cases hc : c = 0
        · rw [msW_hit n m so sl c hsl hso hpl hz hc] at h
          simp only [Option.some.injEq] at h
          subst h
          have : c.toNat = 0 := by rw [hc]; rfl
          simp [motIdx, this, msRes]
        · rw [msW_mot n m so sl c hsl hso hpl hz hc] at h
          obtain ⟨r1, hr, h⟩ := of_K h rfl
          have hc1 : (c - 1).toNat = c.toNat - 1 := by
            have : c.toNat ≠ 0 := fun e => hc (UInt64.toNat_inj.mp (by simpa using e))
            rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp
          have g := ih m (so + 1) (sl - 1) (c - 1) r1 rest hr hdec1 (by rw [hso1, hsl1]; omega)
          rw [msK_of _ r1 g] at h
          simp only [Option.some.injEq] at h
          subst h
          have hcne : c.toNat ≠ 0 := fun e => hc (UInt64.toNat_inj.mp (by simpa using e))
          obtain ⟨c', hc'⟩ : ∃ c', c.toNat = c' + 1 := ⟨c.toNat - 1, by omega⟩
          rw [hc1, hc'] at *
          simp only [motIdx, motIdx_shift, List.getElem?_cons_succ, List.getElem?_map, Nat.add_sub_cancel]
      | minor c0 C0 ihs =>
        have hnz : rdW (m.arr64 IW) (rdW (m.arr64 IW) so) ≠ 0 := by
          rw [hrd]; simp [ClassSlot.isMinor]
        rw [msW_min n m so sl c hsl hso hpl hnz] at h
        obtain ⟨r1, hr, h⟩ := of_K h rfl
        have g := ih m (so + 1) (sl - 1) c r1 rest hr hdec1 (by rw [hso1, hsl1]; omega)
        rw [msK_of _ r1 g] at h
        simp only [Option.some.injEq] at h
        subst h
        simp only [motIdx, motIdx_shift, List.getElem?_map]

/-! ## `class_gen_slot_var` (through `pin_word`, `intern_sort`, `intern_fvar`) -/

/-- The word model of `pin_word(k)`. -/
def pinWordW (m : Mem) (k : Word) : Option Word :=
  if 0 < (m.arr64 PINS).size ∧ rdW (m.arr64 PINS) 0 ≠ 0 then
    (if k.toNat < (m.arr64 PINS).size then some (rdW (m.arr64 PINS) k) else none)
  else none

theorem pinWord_specW (p : Prog) (hp : p.lookup "pin_word" = some pinWordL) (n : Nat) (s₀ : St)
    (k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pin_word" [k]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ pinWordW s₀.mem k = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, pinWordL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64]
    all_goals (try simp only [Locals.init, List.getD_cons_zero, Cmp.eval, beq_iff_eq] at *)
    all_goals grind [lang_grind, arena_grind, ind_grind, pinWordW]

/-- After the sort interning. -/
def svK2 (_m : Mem) (g s : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (z, m1) =>
    if 4294967296 ≤ z then none
    else if g.toNat < (m1.arr64 IW).size then
      (match fvinternW m1 (rdW (m1.arr64 IW) g + s) z with
       | none => none
       | some (fv, m2) => if 4294967296 ≤ fv then none else some ([fv], m2))
    else none

/-- **The model of `class_gen_slot_var`.** -/
def slotVarW (m : Mem) (g s : Word) : Option (List Word × Mem) :=
  match pinWordW m 53 with
  | none => none
  | some u => if 4294967296 ≤ u then none else svK2 m g s (sointernW m u)

theorem slotVar_spec (p : Prog) (hpin : p.lookup "pin_word" = some pinWordL)
    (hsf : p.lookup "sort_find" = some sortFind) (hsp : p.lookup "sort_push" = some sortPush)
    (his : p.lookup "intern_sort" = some internSort)
    (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
    (hif : p.lookup "intern_fvar" = some internFVar)
    (hp : p.lookup "class_gen_slot_var" = some classGenSlotVar) (n : Nat) (s₀ : St) (g s : Word) :
    ⦃fun s_ => s_ = s₀⦄ invoke p (exec p n) "class_gen_slot_var" [g, s]
    ⦃fun r s' => LocEq s' s₀ ∧ slotVarW s₀.mem g s = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, classGenSlotVar]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      pinWord_specW p hpin n, internSort_spec p hsf hsp his n, internFVar_spec p hff hfp hif n]
    all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Cmp.eval,
      BinOp.eval, Nat.reduceEqDiff, reduceIte,
      decide_eq_true_eq] at *)
    all_goals grind [lang_grind, arena_grind, ind_grind, slotVarW, svK2]

theorem pinWordW_some {m : Mem} {u : Word} (h : pinWordW m 53 = some u) : pinW m 0 ≠ 0 ∧ u = pinW m 53 := by
  simp only [pinWordW] at h
  split at h
  · rename_i hh; split at h
    · cases h; exact ⟨hh.2, rfl⟩
    · cases h
  · cases h

theorem slotVarW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem)
    (a : AState) (g s : Word) (G : ClassGen) (r : List Word) (hS : StageR dn vis fe m a)
    (hg : iwN m g.toNat = some G.nP) (hgt : g.toNat < iwTop m) (hns : G.nP + s.toNat < 2 ^ 64)
    (h : slotVarW m g s = some (r, m')) :
    ∃ x a', (ConRon.Arena.ClassGen.slotVar G s.toNat).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ (r.headD 0).toNat < 2 ^ 32 ∧ decE (r.headD 0) = x := by
  simp only [slotVarW] at h
  split at h
  · cases h
  rename_i u hpw
  obtain ⟨hpin, rfl⟩ := pinWordW_some hpw
  obtain ⟨hu, h⟩ := of_ite_none h
  obtain ⟨⟨z, m1⟩, hso, h⟩ := of_K h rfl
  simp only [svK2] at h
  obtain ⟨hz, h⟩ := of_ite_none h
  obtain ⟨hg0, h⟩ := of_ite_none' h
  have hu32 : (pinW m 53).toNat < 2 ^ 32 := by have : ¬ (4294967296 : Nat) ≤ (pinW m 53).toNat := hu; omega
  have hz32 : z.toNat < 2 ^ 32 := by have : ¬ (4294967296 : Nat) ≤ z.toNat := hz; omega
  have hzl : zeroLevel.run a = .ok (decI (pinW m 53), a) := pinZeroLevel_run (hS.1.pins.full hpin)
  obtain ⟨a1, hrun1, hS1, hg1⟩ := internSort_stage hS _ hu32 hso
  have hrd : rdW (m1.arr64 IW) g = UInt64.ofNat G.nP := by
    have e1 := (iwN_rdW hg (by have := g.toNat_lt; omega))
    rw [UInt64.ofNat_toNat] at e1
    have : (m1.arr64 IW)[g.toNat]? = (m.arr64 IW)[g.toNat]? := hg1.2.2.1 g.toNat hgt
    simp only [rdW] at e1 ⊢; rw [this]; exact e1.1
  rw [hrd] at h
  split at h
  · cases h
  rename_i fv m2 hfv
  obtain ⟨hf, h⟩ := of_ite_none h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨a2, hrun2, hS2, hg2⟩ := internFVar_stage hS1 (UInt64.ofNat G.nP + s) z hz32 hfv
  have hsum : (UInt64.ofNat G.nP + s).toNat = G.nP + s.toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (show G.nP < 2 ^ 64 by omega)]; exact Nat.mod_eq_of_lt hns
  have hf32 : fv.toNat < 2 ^ 32 := by have : ¬ (4294967296 : Nat) ≤ fv.toNat := hf; omega
  refine ⟨decE fv, a2, ?_, hS2, hg1.trans hg2, by simpa using hf32, rfl⟩
  rw [hsum] at hrun2
  simp only [ConRon.Arena.ClassGen.slotVar]
  simp only [StateT.run] at hzl hrun1 hrun2 ⊢
  simp only [StateT.bind, hzl, bind, Except.bind, hrun1]
  exact hrun2

/-! ## `class_gen_mot_var` -/

/-- The returned word. -/
def mvK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

/-- After the motive-slot search. -/
def mvK (m : Mem) (g : Word) : Option (List Word) → Option (List Word × Mem)
  | none => none
  | some r => mvK2 (slotVarW m g (if r.headD 0 = 0 then 0 else r.tail.headD 0))

/-- **The model of `class_gen_mot_var`.** -/
def motVarW (n : Nat) (m : Mem) (g c : Word) : Option (List Word × Mem) :=
  mvK m g (msW n m (rdW (m.arr64 IW) (g + 7)) (rdW (m.arr64 IW) (g + 8)) c)

section mvarms
variable (m : Mem) (g : Word) (r : List Word)
theorem mvK_some : mvK m g (some r) = mvK2 (slotVarW m g (if r.headD 0 = 0 then 0 else r.tail.headD 0)) := rfl
theorem mvK2_some (m' : Mem) : mvK2 (some (r, m')) = some ([r.headD 0], m') := rfl
end mvarms

grind_pattern [ind_grind] mvK_some => mvK m g (some r)
grind_pattern [ind_grind] mvK2_some => mvK2 (some (r, m'))

theorem motVar_spec (p : Prog) (hpin : p.lookup "pin_word" = some pinWordL)
    (hsf : p.lookup "sort_find" = some sortFind) (hsp : p.lookup "sort_push" = some sortPush)
    (his : p.lookup "intern_sort" = some internSort)
    (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
    (hif : p.lookup "intern_fvar" = some internFVar)
    (hsv : p.lookup "class_gen_slot_var" = some classGenSlotVar)
    (hms : p.lookup "class_read_motive_slot" = some classReadMotiveSlot)
    (hp : p.lookup "class_gen_mot_var" = some classGenMotVar) (n : Nat) (s₀ : St) (g c : Word) :
    ⦃fun s_ => s_ = s₀⦄ invoke p (exec p (n + 1)) "class_gen_mot_var" [g, c]
    ⦃fun r s' => LocEq s' s₀ ∧ motVarW n s₀.mem g c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, classGenMotVar]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
    classReadMotiveSlot_spec p hms n, slotVar_spec p hpin hsf hsp his hff hfp hif hsv n]
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Locals.init, List.getD_cons_zero, List.getD_cons_succ, Cmp.eval,
    BinOp.eval, Nat.reduceEqDiff, reduceIte, beq_iff_eq] at *)
  all_goals grind (gen := 20) [lang_grind, arena_grind, ind_grind, motVarW]

theorem motIdx_lt : ∀ (sls : List ClassSlot) (j i : Nat), i ∈ motIdx j sls → j ≤ i ∧ i < j + sls.length := by
  intro sls
  induction sls with
  | nil => intro j i h; simp [motIdx] at h
  | cons sl sls ih =>
    intro j i h
    cases sl with
    | motive k =>
      simp only [motIdx, List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · have := ih (j + 1) i h; simp; omega
    | minor c C ihs =>
      simp only [motIdx] at h
      have := ih (j + 1) i h; simp; omega

theorem motVarW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat)
    (m m' : Mem) (a : AState) (g c : Word) (G : ClassGen) (r : List Word) (hS : StageR dn vis fe m a)
    (hg : iwN m g.toNat = some G.nP) (hgt : g.toNat < iwTop m)
    (hsl : decAt m (decPL m (decCS m)) (g.toNat + 7) = some G.slots)
    (hns : G.nP + G.slots.length < 2 ^ 64) (hgb : g.toNat + 9 < 2 ^ 64)
    (hsz : (m.arr64 IW).size < 2 ^ 64) (h : motVarW n m g c = some (r, m')) :
    ∃ x a', (ConRon.Arena.ClassGen.motVar G c.toNat).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ (r.headD 0).toNat < 2 ^ 32 ∧ decE (r.headD 0) = x := by
  obtain ⟨o, l, ho, hl, hdec⟩ := decAt_some hsl
  have ho' := iwN_off (k := 7) ho (by omega)
  have hl' := iwN_off (k := 8) (by simpa [Nat.add_assoc] using hl) (by omega)
  have e : UInt64.ofNat g.toNat = g := UInt64.ofNat_toNat
  rw [e] at ho' hl'
  simp only [show UInt64.ofNat 7 = 7 from rfl, show UInt64.ofNat 8 = 8 from rfl] at ho' hl'
  simp only [motVarW, ho'.2, hl'.2] at h
  have hob : o < 2 ^ 64 := (iwN_rdW ho (by omega)).2
  have hlb : l < 2 ^ 64 := (iwN_rdW (by simpa [Nat.add_assoc] using hl) (by omega)).2
  have hol : o + l < 2 ^ 64 := by
    rcases decPL_le hdec with h0 | h0
    · omega
    · omega
  obtain ⟨r1, hms, h⟩ := of_K h rfl
  have g1 := msW_ok n m _ _ c r1 G.slots hms (by simpa [UInt64.toNat_ofNat_of_lt' hob, UInt64.toNat_ofNat_of_lt' hlb] using hdec)
    (by simp [UInt64.toNat_ofNat_of_lt' hob, UInt64.toNat_ofNat_of_lt' hlb]; exact hol)
  have hmot : ConRon.Arena.ClassRead.motiveSlot G.slots c.toNat = (motIdx 0 G.slots)[c.toNat]? := by
    have := motIdx_eq 0 G.slots
    simp only [Nat.zero_add, List.map_id'] at this
    simp only [ConRon.Arena.ClassRead.motiveSlot]
    erw [this]
  obtain ⟨sv, hsv1, hsv2⟩ : ∃ sv : Word, sv.toNat = ((motIdx 0 G.slots)[c.toNat]?).getD 0 ∧
      (if r1.headD 0 = 0 then 0 else r1.tail.headD 0) = sv := by
    rw [g1]
    cases ho2 : (motIdx 0 G.slots)[c.toNat]? with
    | none => exact ⟨0, rfl, by simp [msRes]⟩
    | some i =>
      have hi : i ∈ motIdx 0 G.slots := List.mem_of_getElem? ho2
      have := (motIdx_lt G.slots 0 i hi).2
      exact ⟨UInt64.ofNat i, by simp; omega, by simp [msRes]⟩
  simp only [mvK, hsv2] at h
  obtain ⟨⟨r2, m2⟩, hsw, h⟩ := of_K h rfl
  simp only [mvK2, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hsvb : G.nP + sv.toNat < 2 ^ 64 := by
    rw [hsv1]
    cases ho2 : (motIdx 0 G.slots)[c.toNat]? with
    | none => simp; omega
    | some i =>
      have hi : i ∈ motIdx 0 G.slots := List.mem_of_getElem? ho2
      have := (motIdx_lt G.slots 0 i hi).2
      simp; omega
  obtain ⟨x, a', hrun, hS', hgr, h1, h2⟩ := slotVarW_ok dn vis fe _ _ a g sv G r2 hS hg hgt hsvb hsw
  refine ⟨x, a', ?_, hS', hgr, by simpa using h1, by simpa using h2⟩
  simp only [ConRon.Arena.ClassGen.motVar, hmot, ← hsv1]
  exact hrun

theorem ctag_iff (w : Word) (hw : w.toNat < 2 ^ 32) (k : Nat) (hk : k < 16) :
    (decE w).tag = UInt32.ofNat k ↔ w >>> 28 = UInt64.ofNat k := by
  rw [decE_tag w hw]
  have h28 : (w >>> 28).toNat < 16 := by
    rw [UInt64.toNat_shiftRight]; simp; omega
  constructor
  · intro h
    have := congrArg UInt32.toNat h
    simp [UInt64.toNat_toUInt32] at this
    apply UInt64.toNat_inj.mp
    simp [UInt64.toNat_ofNat_of_lt' (by omega : k < 2 ^ 64)]
    rw [UInt64.toNat_shiftRight] at *
    simp at *
    omega
  · intro h
    rw [h]; apply UInt32.toNat_inj.mp
    simp

theorem ETables.getConst_of_get_r (t : ETables) (i : EIdx) (n : NIdx) (us : LsIdx)
    (h : t.get i = some (.const n us)) : t.getConst i = some (n, us) := by
  unfold ETables.get at h
  unfold ETables.getConst
  repeat' (first | (simp at h; done) | split at h)
  cases hn : t.consts.node? i.idxNat <;> simp [hn] at h ⊢
  exact h

theorem EStore.viewConst_of_view_r (st : EStore) (i : EIdx) (n : NIdx) (us : LsIdx)
    (h : st.view i = some (.const n us)) : st.viewConst i = some (n, us) := by
  unfold EStore.view at h
  unfold EStore.viewConst EStore.persGetConst
  split at h
  · simp only [*, ite_true]; exact ETables.getConst_of_get_r _ _ _ _ h
  · split at h
    · simp only [*, ite_true]; split <;> simp_all [ETables.getConst_of_get_r _ _ _ _ h]
    · simp at h

theorem eViewW_head6 (m : Mem) (w : Word) (hne : eViewW m w ≠ []) (hg : w >>> 28 = 6) :
    (eViewW m w).headD 0 = 6 := by
  unfold eViewW at hne ⊢
  simp (config := {decide := true}) only [hg, ite_true, ite_false] at hne ⊢
  by_cases c1 : 4294967295 < w
  · simp [c1] at hne
  by_cases c2 : tierW w ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [c1, c2] at hne
  by_cases c3 : tcnt m FORALL (tierW w) ≤ idxW w
  · simp [c1, c2, c3] at hne
  simp [c1, c2, c3]

theorem ETables.getBind_of_get_forall (t : ETables) (i : EIdx) (ty b : EIdx)
    (h : t.get i = some (.forallE ty b)) : t.getBind i = some (ty, b) := by
  unfold ETables.get at h
  unfold ETables.getBind
  repeat' (first | (simp at h; done) | split at h)
  rename_i h1 h2 h3 h4 h5 h6 h7
  have h7' : Idx.tag i = ETag.forallE := by simpa using h7
  have hne : ETag.forallE ≠ ETag.lam := by decide
  cases hn : t.foralls.node? i.idxNat <;> simp [hn, h7', hne] at h ⊢
  exact h

theorem EStore.viewBind_of_view_forall (st : EStore) (i : EIdx) (ty b : EIdx)
    (h : st.view i = some (.forallE ty b)) : st.viewBind i = some (ty, b) := by
  unfold EStore.view at h
  unfold EStore.viewBind EStore.persGetBind
  split at h
  · simp only [*, ite_true]; exact ETables.getBind_of_get_forall _ _ _ _ h
  · split at h
    · simp only [*, ite_true]; split <;> simp_all [ETables.getBind_of_get_forall _ _ _ _ h]
    · simp at h

/-! ## `class_gen_ih_parts` (through the `open_pis_at_fvars_f` and `get_app_args` stubs) -/

/-- After `get_app_args`. -/
def ihK2 (nPc xo xl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) =>
    if nPc < r.tail.headD 0 then some ([1, xo, xl, r.headD 0 + nPc, r.tail.headD 0 - nPc], m2)
    else some ([1, xo, xl, r.headD 0, 0], m2)

/-- After `open_pis_at_fvars_f`. -/
def ihK1 (nPc : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if r.headD 0 = 0 then some ([0, 0, 0, 0, 0], m1)
    else ihK2 nPc (r.tail.headD 0) (r.tail.tail.headD 0)
      (gaaF m1 [CWF, r.tail.tail.tail.headD 0])

/-- **The model of `class_gen_ih_parts`.** -/
def ihW (m : Mem) (g t tele w d : Word) : Option (List Word × Mem) :=
  ihK1 (if t < rdW (m.arr64 IW) (g + 4) then rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (g + 3) + t) + 4) else 0)
    (opfF m [tele, w, d])

section arms
variable (nPc xo xl : Word) (r : List Word) (m1 : Mem)
theorem ihK2_some : ihK2 nPc xo xl (some (r, m1)) =
    (if nPc < r.tail.headD 0 then some ([1, xo, xl, r.headD 0 + nPc, r.tail.headD 0 - nPc], m1)
    else some ([1, xo, xl, r.headD 0, 0], m1)) := rfl
theorem ihK1_some : ihK1 nPc (some (r, m1)) =
    (if r.headD 0 = 0 then some ([0, 0, 0, 0, 0], m1)
    else ihK2 nPc (r.tail.headD 0) (r.tail.tail.headD 0)
      (gaaF m1 [CWF, r.tail.tail.tail.headD 0])) := rfl
end arms
grind_pattern [ind_grind] ihK2_some => ihK2 nPc xo xl (some (r, m1))
grind_pattern [ind_grind] ihK1_some => ihK1 nPc (some (r, m1))

set_option maxHeartbeats 1600000 in
theorem classGenIhParts_spec (p : Prog) (hp : p.lookup "class_gen_ih_parts" = some classGenIhParts)
    (had : AdF p) (hopf : OpfF p) (n : Nat) (s₀ : St) (g t tele w d : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "class_gen_ih_parts" [g, t, tele, w, d]
    ⦃fun r s' => LocEq s' s₀ ∧ ihW s₀.mem g t tele w d = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, classGenIhParts]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
    opfF_spec p hopf n, gaaF_spec p had n]
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Locals.init, List.getD_cons_zero, List.getD_cons_succ, Cmp.eval,
    BinOp.eval, Nat.reduceEqDiff, reduceIte, beq_iff_eq,
    decide_eq_true_eq] at *)
  all_goals grind (gen := 20) [lang_grind, arena_grind, ind_grind, ihW]

theorem decTM_nPc {m : Mem} {p : Nat} {M : TargetMajor} (h : decTM m p = some M) :
    iwN m (p + 4) = some M.nPc := by
  simp only [decTM, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨_, _, _, _, _, _, a3, ha3, _, _, _, _, _, _, _, _, _, _, rfl⟩ := h
  exact ha3

theorem decHL_drop {k' : IdxKind} {m : Mem} : ∀ (k : Nat) {o l : Nat} {xs : List (Idx k')},
    decHL m o l = some xs → k ≤ l → decHL m (o + k) (l - k) = some (xs.drop k) := by
  intro k
  induction k with
  | zero => intro o l xs h _; simpa using h
  | succ k ih =>
    intro o l xs h hk
    obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    obtain ⟨x, ys, rfl, hys, -⟩ := decHL_cons_r h
    have := ih hys (by omega)
    have e1 : o + 1 + k = o + (k + 1) := by omega
    have e2 : l' - k = l' + 1 - (k + 1) := by omega
    rw [e1, e2] at this
    simpa using this

/-- The `nPc` word `class_gen_ih_parts` reads, against the twin's `(g.cls[t]?).map nPc`. -/
theorem ihNPc_word {m : Mem} {g t : Word} {cls : List TargetMajor}
    (hcls : decAt m (decPL m (decTM m)) (g.toNat + 3) = some cls)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    (if t < rdW (m.arr64 IW) (g + 4) then
        rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (g + 3) + t) + 4) else 0) =
      UInt64.ofNat (match cls[t.toNat]? with | some M => M.nPc | none => 0) ∧
    (match cls[t.toNat]? with | some M => M.nPc | none => 0) < 2 ^ 64 := by
  obtain ⟨o, l, ho, hl, hdec⟩ := decAt_some hcls
  have hg64 : g.toNat + 4 < 2 ^ 64 := by have := iwN_lt hl; omega
  have e : UInt64.ofNat g.toNat = g := UInt64.ofNat_toNat
  have ho' := iwN_off (k := 3) ho (by omega)
  have hl' := iwN_off (k := 4) (by simpa [Nat.add_assoc] using hl) (by omega)
  rw [e] at ho' hl'
  simp only [show UInt64.ofNat 3 = 3 from rfl, show UInt64.ofNat 4 = 4 from rfl] at ho' hl'
  have hob : o < 2 ^ 64 := (iwN_rdW ho (by omega)).2
  have hlb : l < 2 ^ 64 := (iwN_rdW (by simpa [Nat.add_assoc] using hl) (by omega)).2
  rw [ho'.2, hl'.2]
  by_cases ht : t.toNat < l
  · have hlt : t < UInt64.ofNat l := by
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hlb]; exact ht
    obtain ⟨v, hv, hM⟩ := decPL_getH m hdec t.toNat ht
    have hsome : cls[t.toNat]? = some (cls[t.toNat]'(by rw [decPL_length m hdec]; exact ht)) :=
      List.getElem?_eq_getElem _
    rw [hsome]
    have hn4 := decTM_nPc hM
    have hvb : v < 2 ^ 64 := (iwN_rdW hv (by have := iwN_lt hv; omega)).2
    have hadd : UInt64.ofNat o + t = UInt64.ofNat (o + t.toNat) := by
      rw [UInt64.ofNat_add, UInt64.ofNat_toNat]
    have hrv := iwN_rdW hv (by have := iwN_lt hv; omega)
    have h4 := iwN_off (k := 4) hn4 (by have := iwN_lt hn4; omega)
    simp only [show UInt64.ofNat 4 = 4 from rfl] at h4
    refine ⟨?_, (iwN_rdW hn4 (by have := iwN_lt hn4; omega)).2⟩
    simp only [hlt, ite_true, hadd, hrv.1, h4.2]
  · have hlt : ¬ t < UInt64.ofNat l := by
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hlb]; exact ht
    have hnone : cls[t.toNat]? = none := by
      rw [List.getElem?_eq_none_iff, decPL_length m hdec]; omega
    refine ⟨?_, by simp [hnone]⟩
    simp [hlt, hnone]

theorem iwH_lt {k : IdxKind} {m : Mem} {i : Nat} {x : Idx k} (h : iwH m i = some x) :
    i < (m.arr64 IW).size := by
  simp only [iwH, hd?, iwA] at h
  cases hw : (m.arr64 IW)[i]? with
  | none => simp [hw] at h
  | some w => exact (Array.getElem?_eq_some_iff.mp hw).1

theorem decHL_le {k : IdxKind} {m : Mem} : ∀ {o l : Nat} {xs : List (Idx k)},
    decHL m o l = some xs → l = 0 ∨ o + l ≤ (m.arr64 IW).size := by
  intro o l
  induction l generalizing o with
  | zero => intro xs _; exact Or.inl rfl
  | succ l ih =>
    intro xs h
    obtain ⟨x, ys, -, hys, hx⟩ := decHL_cons_r h
    have h1 := iwH_lt hx
    rcases ih hys with h0 | h0
    · right; omega
    · right; omega

/-- What `class_gen_ih_parts` returns against the twin's `Option (xs, args.drop nPc)`. -/
def IhRes (m' : Mem) (r : List Word) : Option (List EIdx × List EIdx) → Prop
  | none => r.headD 0 = 0
  | some (xs, ys) => r.headD 0 = 1 ∧
      decHL m' (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat = some xs ∧
      (r.tail.headD 0).toNat + (r.tail.tail.headD 0).toNat ≤ iwTop m' ∧
      decHL m' (r.tail.tail.tail.headD 0).toNat (r.tail.tail.tail.tail.headD 0).toNat = some ys ∧
      (r.tail.tail.tail.headD 0).toNat + (r.tail.tail.tail.tail.headD 0).toNat ≤ iwTop m'

theorem ihW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem)
    (a : AState) (g t tele w d : Word) (G : ClassGen) (r : List Word) (hS : StageR dn vis fe m a)
    (hw : H w) (hcls : decAt m (decPL m (decTM m)) (g.toNat + 3) = some G.cls)
    (hsz : (m.arr64 IW).size < 2 ^ 64) (hA : AbsOK m)
    (h : ihW m g t tele w d = some (r, m')) :
    ∃ res a', (ConRon.Arena.ClassGen.ihParts G t.toNat tele.toNat (decI w) d.toNat).run a = .ok (res, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ IhRes m' r res ∧ AbsOK m' := by
  simp only [ihW] at h
  obtain ⟨hnp0, hnp64⟩ := ihNPc_word (t := t) hcls hsz
  rw [hnp0] at h
  obtain ⟨⟨r1, m1⟩, hs, h⟩ := of_K h rfl
  obtain ⟨res1, a1, hrun1, ⟨hS1, hg1, hdec1⟩, hA1⟩ := opfF_ok dn vis fe tele w d hw m m1 a r1 hs ⟨hS, hA⟩
  cases res1 with
  | none =>
    have h0 : r1.headD 0 = 0 := hdec1
    rw [ihK1_some, ite_eq_left h0] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨none, a1, ?_, hS1, hg1, rfl, hA1⟩
    simp only [ConRon.Arena.ClassGen.ihParts, StateT.run_bind]
    rw [hrun1]
    rfl
  | some xl =>
    obtain ⟨xs, leaf⟩ := xl
    obtain ⟨h1, hxs, hleaf⟩ := hdec1
    have h0 : r1.headD 0 ≠ 0 := by rw [h1]; decide
    rw [ihK1_some, ite_eq_right h0] at h
    have hleaf3 : r1.tail.tail.tail.headD 0 = (r1.drop 3).headD 0 := by
      rcases r1 with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
    rw [hleaf3] at h
    obtain ⟨hl1, hl2⟩ := hleaf
    obtain ⟨⟨r2, m2⟩, ha, h⟩ := of_K h rfl
    obtain ⟨args, a2, hrun2, hS2, hg2, hdec2⟩ := gaaF_ok dn vis fe CWF ((r1.drop 3).headD 0) hl1 m1 m2 a1 r2 ha hS1
    have hA2 : AbsOK m2 := gaaF_afr ha hA1
    generalize hN : (match G.cls[t.toNat]? with | some M => M.nPc | none => 0) = N at hnp64 h
    have gd : ∀ (l : List Word), l.getD 0 0 = l.headD 0 ∧ l.getD 1 0 = l.tail.headD 0 ∧
        l.getD 2 0 = l.tail.tail.headD 0 := by
      intro l; rcases l with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> simp
    obtain ⟨hxs', hxtop'⟩ := hxs
    obtain ⟨hdec2', hatop'⟩ := hdec2
    rw [(gd r1).2.1, (gd r1).2.2] at hxs' hxtop'
    simp only [show (0 : Nat) + 1 = 1 from rfl, (gd r2).1, (gd r2).2.1] at hdec2' hatop'
    have hxs2 : decHL m2 (r1.tail.headD 0).toNat (r1.tail.tail.headD 0).toNat = some xs := by
      rw [decHL_grow hg2 hxtop']; exact hxs'
    have hlen := decHL_length m2 hdec2'
    rw [ihK2_some] at h
    have hTW : (UInt64.ofNat N).toNat = N := UInt64.toNat_ofNat_of_lt' hnp64
    have htwin : (ConRon.Arena.ClassGen.ihParts G t.toNat tele.toNat (decI w) d.toNat).run a =
        .ok (some (xs, args.drop N), a2) := by
      have hunf : ConRon.Arena.ClassGen.ihParts G t.toNat tele.toNat (decI w) d.toNat =
          (do match ← openPisAtFvarsF tele.toNat (decI w) d.toNat with
              | none => pure none
              | some (xs, leaf) => do
                let args ← getAppArgs coreWalkFuel leaf
                pure (some (xs, args.drop (match G.cls[t.toNat]? with | some M => M.nPc | none => 0)))) := rfl
      rw [hunf]
      simp only [StateT.run_bind]
      rw [hrun1]
      simp only [bind, Except.bind]
      have hrun2' : (getAppArgs coreWalkFuel leaf).run a1 = .ok (args, a2) := by
        rw [CWF_eq, show (decI ((r1.drop 3).headD 0) : EIdx) = leaf from hl2] at hrun2; exact hrun2
      rw [hN]
      simp only [StateT.run] at hrun2' ⊢
      simp only [bind, Except.bind, StateT.bind, hrun2']
      rfl
    have hao : (r2.headD 0).toNat + (r2.tail.headD 0).toNat < 2 ^ 64 ∨ (r2.tail.headD 0).toNat = 0 := by
      rcases decHL_le hdec2' with h0 | h0
      · right; exact h0
      · left; obtain ⟨-, -, hsz2, -, -⟩ := hS2.2; omega
    by_cases hlt : UInt64.ofNat N < r2.tail.headD 0
    · rw [ite_eq_left hlt] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hNl : N < (r2.tail.headD 0).toNat := by
        have := UInt64.lt_iff_toNat_lt.mp hlt
        rwa [hTW] at this
      have hsum : (r2.headD 0 + UInt64.ofNat N).toNat = (r2.headD 0).toNat + N := by
        simp only [UInt64.toNat_add, hTW]
        apply Nat.mod_eq_of_lt
        rcases hao with h0 | h0 <;> omega
      have hsub : (r2.tail.headD 0 - UInt64.ofNat N).toNat = (r2.tail.headD 0).toNat - N := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hTW]; omega)), hTW]
      have hdr := decHL_drop N hdec2' (by omega)
      refine ⟨some (xs, args.drop N), a2, htwin, hS2, hg1.trans hg2, ?_, hA2⟩
      refine ⟨rfl, ?_, ?_, ?_, ?_⟩
      · simpa using hxs2
      · have := hg2.1; simpa using Nat.le_trans hxtop' this
      · show decHL m2 (r2.headD 0 + UInt64.ofNat N).toNat (r2.tail.headD 0 - UInt64.ofNat N).toNat = _
        rw [hsum, hsub]; exact hdr
      · show (r2.headD 0 + UInt64.ofNat N).toNat + (r2.tail.headD 0 - UInt64.ofNat N).toNat ≤ iwTop m2
        rw [hsum, hsub]; omega
    · rw [ite_eq_right hlt] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hNl : (r2.tail.headD 0).toNat ≤ N := by
        have : ¬ (UInt64.ofNat N).toNat < (r2.tail.headD 0).toNat := fun hh =>
          hlt (UInt64.lt_iff_toNat_lt.mpr hh)
        rw [hTW] at this; omega
      have hnil : args.drop N = [] := List.drop_eq_nil_of_le (by omega)
      refine ⟨some (xs, args.drop N), a2, htwin, hS2, hg1.trans hg2, ?_, hA2⟩
      refine ⟨rfl, ?_, ?_, ?_, ?_⟩
      · simpa using hxs2
      · have := hg2.1; simpa using Nat.le_trans hxtop' this
      · rw [hnil]; simp [decHL, hslice?]
      · show (r2.headD 0).toNat + (0 : Word).toNat ≤ iwTop m2
        simp only [UInt64.toNat_zero]; omega

theorem eViewW_head3 (m : Mem) (w : Word) (hne : eViewW m w ≠ []) (hg : w >>> 28 = 3) :
    (eViewW m w).headD 0 = 3 := by
  unfold eViewW at hne ⊢
  simp (config := {decide := true}) only [hg, ite_true, ite_false] at hne ⊢
  by_cases c1 : 4294967295 < w
  · simp [c1] at hne
  by_cases c2 : tierW w ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [c1, c2] at hne
  by_cases c3 : tcnt m CONST (tierW w) ≤ idxW w
  · simp [c1, c2, c3] at hne
  simp [c1, c2, c3]

theorem decTM_ind {m : Mem} {p : Nat} {M : TargetMajor} (h : decTM m p = some M) :
    iwH m p = some M.ind := by
  simp only [decTM, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨w5, h5, a1, ha1, w4, h4, w3, h3, w2, h2, ac, hac, w1, hw1, w0, h0, a, ha, rfl⟩ := h
  exact h5

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

theorem tpd_step (x d b b' : EIdx) (e : Word) (xs : List EIdx) (a a1 a2 : AState) (res : Option (List EIdx))
    (htag : ((decE e).tag == ETag.forallE) = true) (hvb : a.store.viewBind (decE e) = some (d, b))
    (h1 : (instantiate1Fast coreWalkFuel b x 0) a = .ok (b', a1))
    (h2 : (ConRon.Arena.targetPiDomsWith xs b') a1 = .ok (res, a2)) :
    (ConRon.Arena.targetPiDomsWith (x :: xs) (decE e)) a =
      .ok ((match res with | some ds => some (d :: ds) | none => none), a2) := by
  simp only [ConRon.Arena.targetPiDomsWith, htag, ite_true]
  have e2 : (ConRon.Arena.viewBind (decE e)) a = .ok (a.store.viewBind (decE e), a) := rfl
  rw [hvb] at e2
  simp only [bind, StateT.bind, e2, Except.bind]
  simp only [h1, h2]
  cases res <;> rfl

theorem pdW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (xo xl e : Word) (r : List Word) (xs : List EIdx),
    pdW n m xo xl e = some (r, m') → StageR dn vis fe m a → H e →
    decHL m xo.toNat xl.toNat = some xs → xo.toNat + xl.toNat < 2 ^ 64 →
    xo.toNat + xl.toNat ≤ iwTop m →
    ∃ res a', (ConRon.Arena.targetPiDomsWith xs (decI e)).run a = .ok (res, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ PdRes m' r res := by
  induction n with
  | zero => intro m m' a xo xl e r xs h; simp [pdW] at h
  | succ n ih =>
    intro m m' a xo xl e r xs h hS he hxs hb hbt
    by_cases hxl : xl = 0
    · rw [pdW_nil n m xo xl e hxl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hz : xl.toNat = 0 := by rw [hxl]; rfl
      rw [hz] at hxs
      simp [decHL, hslice?] at hxs
      subst hxs
      refine ⟨some [], a, rfl, hS, IWGrow.refl m, ?_⟩
      simp [PdRes, decHL, hslice?]
    · obtain ⟨x, xs', w, rfl, hxs', hw1, hw2, hw3, hxo1, hxl1⟩ := rcSl_step hxs hxl hb
      have hftag : (decE e).tag = ETag.forallE ↔ e >>> 28 = 6 := ctag_iff e he 6 (by decide)
      by_cases hf : e >>> 28 ≠ 6
      · rw [pdW_nf n m xo xl e hxl hf] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        refine ⟨none, a, ?_, hS, IWGrow.refl m, rfl⟩
        have : ¬ (decE e).tag = ETag.forallE := fun hc => hf (hftag.mp hc)
        have htag' : ((decE e).tag == ETag.forallE) = false := by simpa using this
        have e1 : (decI e : EIdx) = decE e := rfl
        rw [e1]
        simp only [ConRon.Arena.targetPiDomsWith, htag', Bool.false_eq_true, ite_false]
        rfl
      have hf6 : e >>> 28 = 6 := by simpa using hf
      by_cases hev : eViewW m e = []
      · rw [pdW_ev n m xo xl e hxl (by simpa using hf) hev] at h; simp at h
      rw [pdW_cons n m xo xl e hxl (by simpa using hf) hev] at h
      obtain ⟨v, hv, hR⟩ := eViewW_ok m a hS.1.arena.1 e hev
      have hhead := eViewW_head6 m e hev hf6
      have hdec : ∃ ty b : EIdx, v = .forallE ty b ∧ (eViewW m e).tail.headD 0 = (eViewW m e).getD 1 0 ∧
          (eViewW m e).tail.tail.headD 0 = (eViewW m e).getD 2 0 ∧
          ((eViewW m e).getD 1 0).toNat < 2 ^ 32 ∧ decE ((eViewW m e).getD 1 0) = ty ∧
          ((eViewW m e).getD 2 0).toNat < 2 ^ 32 ∧ decE ((eViewW m e).getD 2 0) = b := by
        cases v <;> simp only [ViewR] at hR
        case forallE ty b =>
          refine ⟨ty, b, rfl, ?_, ?_, hR.2.1, hR.2.2.1, hR.2.2.2.1, hR.2.2.2.2⟩ <;>
          · cases hh : eViewW m e with
            | nil => exact absurd hh hev
            | cons a1 t => cases t with
              | nil => simp
              | cons a2 t2 => cases t2 <;> simp
        all_goals first | exact absurd (hhead.symm.trans hR.1) (by decide) | exact absurd (hhead.symm.trans hR) (by decide)
      obtain ⟨ty, bb, rfl, ht1, ht2, hdlt, hdd, hblt, hbd⟩ := hdec
      rw [hw1, ht1, ht2] at h
      rcases hi : i1F m [CWF, (eViewW m e).getD 2 0, w, 0] with _ | ⟨ri, m1⟩ <;> simp only [hi, pdK1, reduceCtorEq] at h
      obtain ⟨t1, a1, hrun1, hS1, hg1, hd11, hd12⟩ :=
        i1F_ok dn vis fe ((eViewW m e).getD 2 0) w 0 hblt m m1 a ri hi hS
      rcases hr : pdW n m1 (xo + 1) (xl - 1) (ri.headD 0) with _ | ⟨r2, m2⟩ <;> rw [hr] at h <;>
        try (simp only [pdK2, reduceCtorEq] at h; done)
      have hxs1 : decHL m1 (xo + 1).toNat (xl - 1).toNat = some xs' := by
        rw [decHL_grow hg1 (by omega)]; exact hxs'
      obtain ⟨res2, a2, hrun2, hS2, hg2, hres2⟩ := ih m1 m2 a1 (xo + 1) (xl - 1) (ri.headD 0) r2 xs' hr hS1 hd11
        hxs1 (by omega) (by have := hg1.1; omega)
      have htag : ((decE e).tag == ETag.forallE) = true := by simpa using hftag.mpr hf6
      have hvb := EStore.viewBind_of_view_forall _ _ _ _ hv
      have hrun1' : (instantiate1Fast coreWalkFuel bb (decI w) 0) a = .ok (t1, a1) := by
        have := hrun1
        have e3 : (decI ((eViewW m e).getD 2 0) : EIdx) = decE ((eViewW m e).getD 2 0) := rfl
        have h0 : (0 : Word).toNat = 0 := rfl
        rw [CWF_eq, e3, hbd, h0] at this
        exact this
      have hrun2' : (ConRon.Arena.targetPiDomsWith xs' t1) a1 = .ok (res2, a2) := by
        rw [← hd12]; exact hrun2
      have e1 : (decI e : EIdx) = decE e := rfl
      cases res2 with
      | none =>
        have hstep := tpd_step (decI w) ty bb t1 e xs' a a1 a2 none htag hvb hrun1' hrun2'
        have hr0 : r2.headD 0 = 0 := hres2
        rw [pdK2_none n m2 (r := r2) (d := (eViewW m e).getD 1 0) hr0] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        refine ⟨none, a2, ?_, hS2, hg1.trans hg2, rfl⟩
        rw [e1, ← hw3]; exact hstep
      | some ds =>
        have hstep := tpd_step (decI w) ty bb t1 e xs' a a1 a2 (some ds) htag hvb hrun1' hrun2'
        obtain ⟨hr1, hdd2, hle⟩ := hres2
        have hr1' : r2.headD 0 ≠ 0 := by rw [hr1]; decide
        rw [pdK2_ok n m2 (r := r2) (d := (eViewW m e).getD 1 0) hr1'] at h
        rcases hc : consW n m2 ((eViewW m e).getD 1 0) (r2.tail.headD 0) (r2.tail.tail.headD 0) with _ | ⟨r3, m3⟩ <;> simp only [hc, pdK3, reduceCtorEq] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        obtain ⟨hS3, hg3, hd3, ht3⟩ := consW_stage hc hS2 hle hdlt hdd2
        refine ⟨some (ty :: ds), a2, ?_, hS3, (hg1.trans hg2).trans hg3, ?_⟩
        · rw [e1, ← hw3]; exact hstep
        · refine ⟨rfl, ?_, ?_⟩
          · rw [← hdd]; simpa [decE_eq] using hd3
          · simpa using Nat.le_of_eq ht3

end L.Ind

end

end
