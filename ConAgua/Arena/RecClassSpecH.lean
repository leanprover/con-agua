import ConAgua.Arena.RecClassSpecG

/-!
# `RecClass`: `classRead` (lane `indproofs2`, helper `rec`)
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Models -/

/-- The lookups `class_read` needs. -/
structure ReadProg (p : Prog) : Prop extends SlotsProg p where
  mp : p.lookup "class_read_mot_pos" = some classReadMotPos
  rcl : p.lookup "class_read_rec_cls" = some classReadRecCls
  rfin : p.lookup "class_read_finish" = some classReadFinish
  ns : p.lookup "class_read_n_slots" = some classReadNSlots
  rd : p.lookup "class_read" = some classRead

l_model classReadMotPos_spec (p : Prog) (hP : ReadProg p)
  fns [hP.mp ↦ motPosW list]
  specs [slCons_specW p hP.a hP.c hP.sc n]
  grind [arena_grind] simp [rdW_eq, getElem_rdW']

def frK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => some ([1, r3.headD 0], m3)

def frK2 (so sl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then some ([0, 0], m2)
    else frK3 (recW m2 4 [so, sl, r2.tail.headD 0, r2.tail.tail.headD 0])

def frK1 (cR : CallM) (N : Nat) (nP so sl ro rl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => frK2 so sl (crW cR N m1 nP (r1.headD 0) (r1.tail.headD 0) ro rl)

/-- **The model of `class_read_finish`.** -/
def readFinW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | N + 1, m, nP, so, sl, ro, rl => frK1 cR N nP so sl ro rl (motPosW N m so sl 0)

/-- **The model of `class_read_n_slots`**: `rP - nP`, truncated. -/
def tsubW (a b : Word) : Word := if b ≤ a then a - b else 0

def rdK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => some ([r3.headD 0, r3.tail.headD 0], m3)

def rdK2 (cR : CallM) (N : Nat) (nP ro rl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then some ([0, 0], m2)
    else rdK3 (readFinW cR N m2 nP (r2.tail.headD 0) (r2.tail.tail.headD 0) ro rl)

def rdK1 (cR : CallM) (N : Nat) (p vis nP ro rl rc0 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 0 then some ([0, 0], m1)
    else rdK2 cR N nP ro rl (slotsW cR N m1 p vis nP (tsubW (rdW (m1.arr64 IW) (rc0 + 1)) nP) 0 0 nP
      (r1.tail.tail.tail.headD 0))

/-- **The model of `class_read`.** -/
def readW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | N + 1, m, p, vis, nP, ro, rl =>
    if rl = 0 then some ([0, 0], m)
    else rdK1 cR N p vis nP ro rl (rdW (m.arr64 IW) ro)
      (cR N "open_pis_at_fvars_f" [nP, rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) ro) + 3), 0] m)

/-! ## Arms -/

section arms
variable (N : Nat) (m m1 m2 m3 : Mem) (so sl j nP ro rl p vis rc0 a b : Word) (r r1 r2 r3 : List Word)
  (cR : CallM)
theorem readFinW_eq : readFinW cR (N + 1) m nP so sl ro rl = frK1 cR N nP so sl ro rl (motPosW N m so sl 0) := rfl
theorem frK1_some : frK1 cR N nP so sl ro rl (some (r1, m1)) =
    frK2 so sl (crW cR N m1 nP (r1.headD 0) (r1.tail.headD 0) ro rl) := rfl
theorem frK2_fail (h : r2.headD 0 = 0) : frK2 so sl (some (r2, m2)) = some ([0, 0], m2) := by
  rw [frK2, ite_eq_left h]
theorem frK2_ok (h : r2.headD 0 ≠ 0) : frK2 so sl (some (r2, m2)) =
    frK3 (recW m2 4 [so, sl, r2.tail.headD 0, r2.tail.tail.headD 0]) := by rw [frK2, ite_eq_right h]
theorem frK3_some : frK3 (some (r3, m3)) = some ([1, r3.headD 0], m3) := rfl
theorem tsubW_le (h : b ≤ a) : tsubW a b = a - b := by simp [tsubW, h]
theorem tsubW_gt (h : ¬ b ≤ a) : tsubW a b = 0 := by simp [tsubW, h]
theorem readW_nil (h : rl = 0) : readW cR (N + 1) m p vis nP ro rl = some ([0, 0], m) := by
  simp [readW, h]
theorem readW_ok (h : rl ≠ 0) : readW cR (N + 1) m p vis nP ro rl =
    rdK1 cR N p vis nP ro rl (rdW (m.arr64 IW) ro)
      (cR N "open_pis_at_fvars_f" [nP, rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) ro) + 3), 0] m) := by
  simp [readW, h]
theorem rdK1_fail (h : r1.headD 0 = 0) : rdK1 cR N p vis nP ro rl rc0 (some (r1, m1)) = some ([0, 0], m1) := by
  rw [rdK1, ite_eq_left h]
theorem rdK1_ok (h : r1.headD 0 ≠ 0) : rdK1 cR N p vis nP ro rl rc0 (some (r1, m1)) =
    rdK2 cR N nP ro rl (slotsW cR N m1 p vis nP (tsubW (rdW (m1.arr64 IW) (rc0 + 1)) nP) 0 0 nP
      (r1.tail.tail.tail.headD 0)) := by rw [rdK1, ite_eq_right h]
theorem rdK2_fail (h : r2.headD 0 = 0) : rdK2 cR N nP ro rl (some (r2, m2)) = some ([0, 0], m2) := by
  rw [rdK2, ite_eq_left h]
theorem rdK2_ok (h : r2.headD 0 ≠ 0) : rdK2 cR N nP ro rl (some (r2, m2)) =
    rdK3 (readFinW cR N m2 nP (r2.tail.headD 0) (r2.tail.tail.headD 0) ro rl) := by rw [rdK2, ite_eq_right h]
theorem rdK3_some : rdK3 (some (r3, m3)) = some ([r3.headD 0, r3.tail.headD 0], m3) := rfl
end arms

grind_pattern [ind_grind] readFinW_eq => readFinW cR (N + 1) m nP so sl ro rl
grind_pattern [ind_grind] frK1_some => frK1 cR N nP so sl ro rl (some (r1, m1))
grind_pattern [ind_grind] frK2_fail => frK2 so sl (some (r2, m2))
grind_pattern [ind_grind] frK2_ok => frK2 so sl (some (r2, m2))
grind_pattern [ind_grind] frK3_some => frK3 (some (r3, m3))
grind_pattern [ind_grind] tsubW_le => tsubW a b
grind_pattern [ind_grind] tsubW_gt => tsubW a b
grind_pattern [ind_grind] readW_nil => readW cR (N + 1) m p vis nP ro rl
grind_pattern [ind_grind] readW_ok => readW cR (N + 1) m p vis nP ro rl
grind_pattern [ind_grind] rdK1_fail => rdK1 cR N p vis nP ro rl rc0 (some (r1, m1))
grind_pattern [ind_grind] rdK1_ok => rdK1 cR N p vis nP ro rl rc0 (some (r1, m1))
grind_pattern [ind_grind] rdK2_fail => rdK2 cR N nP ro rl (some (r2, m2))
grind_pattern [ind_grind] rdK2_ok => rdK2 cR N nP ro rl (some (r2, m2))
grind_pattern [ind_grind] rdK3_some => rdK3 (some (r3, m3))

/-! ## Specs -/

theorem classReadFinish_spec (p : Prog) (hP : ReadProg p) (cR : CallM) (hcR : CallSpec p cR) (N : Nat)
    (s₀ : St) (nP so sl ro rl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p N) "class_read_finish" [nP, so, sl, ro, rl]
    ⦃fun r s' => LocEq s' s₀ ∧ readFinW cR N s₀.mem nP so sl ro rl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.rfin]; simp only [callFn, classReadFinish]
  rcases N with _ | N
  · vcgen [exec] <;> grind
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      classReadMotPos_spec p hP N,
      classReadRecCls_spec p hP.fh hP.v hP.f hP.cm hP.c hP.a hP.sc hP.rcl hP.ad cR hcR N,
      rec4_specW p hP.a N hP.r4] <;>
    finish (gen := 20) [rdW_eq]

theorem classReadNSlots_spec (p : Prog) (hP : ReadProg p) (N : Nat) (s₀ : St) (a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p N) "class_read_n_slots" [a, b]
    ⦃fun r s' => s' = s₀ ∧ r = [tsubW a b]; ⊤⦄ := by
  rw [invoke_eq _ hP.ns]; simp only [callFn, classReadNSlots]
  rcases N with _ | N
  · vcgen [exec] <;> grind
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs] <;>
    finish (gen := 20)

theorem classRead_spec (p : Prog) (hP : ReadProg p) (cR : CallM) (hcR : CallSpec p cR) (N : Nat) (s₀ : St)
    (q vis nP ro rl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p N) "class_read" [q, vis, nP, ro, rl]
    ⦃fun r s' => LocEq s' s₀ ∧ readW cR N s₀.mem q vis nP ro rl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.rd]; simp only [callFn, classRead]
  rcases N with _ | N
  · vcgen [exec] <;> grind
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      hcR N "open_pis_at_fvars_f", classReadNSlots_spec p hP N,
      (classReadSlots_specs p hP.toSlotsProg cR hcR N).1, classReadFinish_spec p hP cR hcR N] <;>
    finish (gen := 20) [rdW_eq, loc_init4, loc_init5, loc_init6, loc_init7]

end L.Ind

namespace L.Ind

open L.Arena

/-! ## Relational lemmas -/

/-- The motive test `classRead` filters the prefix positions by. -/
def motF (slots : List ClassSlot) (s : Nat) : Bool :=
  match slots[s]? with
  | some (.motive _) => true
  | _ => false

theorem FA2.get {α β : Type} {R : α → β → Prop} : ∀ {as : List α} {bs : List β}, FA2 R as bs →
    ∀ j (h1 : j < as.length) (h2 : j < bs.length), R (as[j]'h1) (bs[j]'h2)
  | _, _, .nil, j, h1, _ => by simp at h1
  | _, _, .cons h hs, 0, _, _ => h
  | _, _, .cons _ hs, j + 1, h1, h2 => FA2.get hs j (by simpa using h1) (by simpa using h2)

theorem SPL.get {α : Type} {dec : Mem → Nat → Option α} {m : Mem} {o l : Nat} {xs : List α}
    (h : SPL dec m o l xs) (j : Nat) (hj : j < l) :
    ∃ q, iwN m (o + j) = some q ∧ StabD (fun m => dec m q) m (xs[j]'(by rw [h.length]; exact hj)) := by
  obtain ⟨-, ps, hps, hf⟩ := h
  have hpl := decNL_length m hps
  have hq := mapM_opt_get (fun j => iwN m (o + j)) (List.range l) ps hps j (by simpa using hj)
  simp only [List.getElem_range] at hq
  exact ⟨ps[j]'(by omega), hq, FA2.get hf j (by omega) _⟩

theorem range'_filter_step (f : Nat → Bool) (j k : Nat) :
    (List.range' j (k + 1)).filter f = if f j then j :: (List.range' (j + 1) k).filter f
      else (List.range' (j + 1) k).filter f := by
  simp only [List.range'_succ, List.filter_cons]
  try (split <;> rfl)

theorem motPosW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (a : AState)
    (so sl : Word) (slots : List ClassSlot) (N : Nat) : ∀ (m m' : Mem) (j : Word) (r : List Word),
    motPosW N m so sl j = some (r, m') → StageR dn vis fe m a → SPL decCS m so.toNat sl.toNat slots →
    j.toNat ≤ sl.toNat →
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      decNL m' (r.headD 0).toNat (r.tail.headD 0).toNat =
        some ((List.range' j.toNat (sl.toNat - j.toNat)).filter (motF slots)) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  induction N with
  | zero => intro m m' j r h; simp [motPosW] at h
  | succ N ih =>
  intro m m' j r h hS hsp hj
  by_cases he : sl ≤ j
  · rw [motPosW.arm1 (hc1 := he)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : sl.toNat - j.toNat = 0 := by have := UInt64.le_iff_toNat_le.mp he; omega
    refine ⟨hS, IWGrow.refl m, ?_, by simp⟩
    simp [this, decNL]
  rw [motPosW.arm2 (hc1 := he)] at h
  have hjl : j.toNat < sl.toNat := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp he)
  have := sl.toNat_lt
  have hlen : j.toNat < slots.length := by rw [hsp.length]; exact hjl
  have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h rfl
  obtain ⟨hS1, hg1, hd1, ht1⟩ := ih m m1 (j + 1) r1 h1 hS hsp (by rw [hj1]; omega)
  rw [hj1] at hd1
  obtain ⟨q, hq, hst⟩ := hsp.get j.toNat hjl
  have hsz := hS.2.2.2.1
  have hb := hsp.1
  have hrd := iwN_rdW_at (w := so) (k := j.toNat) hq hsz
  rw [show so + UInt64.ofNat j.toNat = so + j by simp] at hrd
  have hrd1 : rdW (m1.arr64 IW) (so + j) = UInt64.ofNat q := by
    rw [← hrd.1]; simp only [rdW]
    rw [show (so + j).toNat = so.toNat + j.toNat by
      rw [UInt64.toNat_add]; have := hS.2.1; exact Nat.mod_eq_of_lt (by omega), hg1.2.2.1 _ (by omega)]
  have htag := decCS_tag (hst.grow hg1).get
  have hrq := iwN_rdW htag (by have := iwN_lt htag; omega)
  rw [show UInt64.ofNat q = UInt64.ofNat q from rfl] at hrq
  have hsplit : sl.toNat - j.toNat = (sl.toNat - (j.toNat + 1)) + 1 := by omega
  by_cases hm : (slots[j.toNat]'hlen).isMinor = true
  · rw [motPosW.k_class_read_mot_pos.arm2 (hc1 := by rw [hrd1, hrq.1]; simp [hm])] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hf : motF slots j.toNat = false := by
      simp only [motF, List.getElem?_eq_getElem hlen]
      revert hm; generalize slots[j.toNat] = x; cases x <;> simp [ClassSlot.isMinor]
    refine ⟨hS1, hg1, ?_, by simpa using ht1⟩
    simp only [List.headD_cons, List.tail_cons]
    rw [hsplit, range'_filter_step, hf]; simpa using hd1
  · rw [motPosW.k_class_read_mot_pos.arm1 (hc1 := by rw [hrd1, hrq.1]; simp at hm; simp [hm])] at h
    obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h rfl
    rw [motPosW.k_sl_cons.arm1] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨hS2, hg2, hd2, ht2⟩ := consW_stageN h2 hS1 ht1 hd1
    have hf : motF slots j.toNat = true := by
      simp only [motF, List.getElem?_eq_getElem hlen]
      revert hm; generalize slots[j.toNat] = x; cases x <;> simp [ClassSlot.isMinor]
    refine ⟨hS2, hg1.trans hg2, ?_, by simpa using Nat.le_of_eq ht2⟩
    simp only [List.headD_cons, List.tail_cons]
    rw [hsplit, range'_filter_step, hf]; simpa using hd2

/-- The twin's `classRead` after the slots. -/
def readFinTw (nP : Nat) (slots : List ClassSlot) (recs : List RecShape) : AM (Option ClassRead) := do
  match ← ConRon.Arena.classReadRecCls nP ((List.range slots.length).filter (motF slots)) recs with
  | none => pure none
  | some recCls => pure (some ⟨slots, recCls⟩)

/-- `class_read`'s result: `none`, or a stably decoding `ClassRead` record. -/
def decRead (m' : Mem) (r : List Word) : Option ClassRead → Prop
  | none => r.headD 0 = 0
  | some cr => r.headD 0 = 1 ∧ StabD (fun m => decCR m (r.tail.headD 0).toNat) m' cr ∧
      ∃ so sl, iwN m' (r.tail.headD 0).toNat = some so ∧ iwN m' ((r.tail.headD 0).toNat + 1) = some sl ∧
        SPL decCS m' so sl cr.slots

/-- The recursors decoded below the tops, their slice word-addressable (a major index past
`2^64 - 2` is `class_read_rec_cls`' capacity abort, lane `indproofs4`). -/
def RecsDec (m : Mem) (ro rl : Word) (recs : List RecShape) : Prop :=
  DecB (fun m => decPL m (decRS m) ro.toNat rl.toNat) m recs ∧ ro.toNat + rl.toNat < 2 ^ 64

theorem RecsDec.dec {m m' : Mem} {ro rl : Word} {recs : List RecShape} (h : RecsDec m ro rl recs)
    (hg : IWGrow m m') : decPL m' (decRS m') ro.toNat rl.toNat = some recs :=
  h.1.stab (OMono.decPL decRS_mono _ _) m' hg

theorem RecsDec.grow {m m' : Mem} {ro rl : Word} {recs : List RecShape} (h : RecsDec m ro rl recs)
    (hg : IWGrow m m') : RecsDec m' ro rl recs :=
  ⟨h.1.grow (OMono.decPL decRS_mono _ _) hg, h.2⟩

theorem iwN_truncM_get {m : Mem} {i v : Nat} (h : iwN (truncM m) i = some v) :
    i < iwTop m ∧ iwN m i = some v := by
  simp only [iwN, nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h
  obtain ⟨hi, hw'⟩ := truncM_iw_get hw
  exact ⟨hi, by simp [iwN, nat?, hw']⟩

theorem motPosW_afr : ∀ (N : Nat) (m m' : Mem) (so sl j : Word) (r : List Word),
    motPosW N m so sl j = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, h => by simp [motPosW] at h
  | N + 1, m, m', so, sl, j, r, h => by
    simp only [motPosW, motPosW.k_class_read_mot_pos.eq_def, motPosW.k_sl_cons.eq_def] at h
    afr_auto h [motPosW_afr N _ _ _ _ _ _, consW_afr]

theorem readFinW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (cR : CallM)
    (J : Mem → Prop) (hO : OpfJ cR J dn vis fe) (N : Nat) (m : Mem)
    (a : AState) (nP so sl ro rl : Word) (slots : List ClassSlot) (recs : List RecShape)
    (hS : StageR dn vis fe m a) (hJ : J m) (hsp : SPL decCS m so.toNat sl.toNat slots)
    (hrecs : RecsDec m ro rl recs) :
    RSim (readFinW cR N m nP so sl ro rl) (readFinTw nP.toNat slots recs) a
      (fun b a' x => KP dn vis fe m decRead b a' x ∧ J b.2) := by
  rcases N with _ | N
  · exact RSim.none
  rw [readFinW_eq]
  refine RSim.lstep (K := frK1 cR N nP so sl ro rl) rfl ?_
  rintro ⟨r1, m1⟩ h1
  obtain ⟨hS1, hg1, hd1, ht1⟩ := motPosW_ok dn vis fe a so sl slots N m m1 0 r1 h1 hS hsp (by simp)
  have hJ1 := hO.1 _ _ (motPosW_afr _ _ _ _ _ _ _ h1) hJ
  simp only [UInt64.toNat_zero, Nat.sub_zero] at hd1
  rw [← hsp.length, ← List.range_eq_range'] at hd1
  rw [frK1_some]
  have hcr : RSim (crW cR N m1 nP (r1.headD 0) (r1.tail.headD 0) ro rl)
      (ConRon.Arena.classReadRecCls nP.toNat ((List.range slots.length).filter (motF slots)) recs) a
      (fun b a' x => StageR dn vis fe b.2 a' ∧ IWGrow m1 b.2 ∧ CrRes b.2 b.1 x ∧ J b.2) := by
    rintro ⟨r, m'⟩ h
    exact crW_ok dn vis fe cR J hO N m1 m' a nP _ _ ro rl r recs _ h hS1 hJ1 (hrecs.dec hg1)
      (fun m3 hg3 => hrecs.dec (hg1.trans hg3)) hd1 ht1 hrecs.2
  refine RSim.bind (K := frK2 so sl) rfl hcr ?_
  rintro ⟨r2, m2⟩ x a2 - ⟨hS2, hg2, hc2, hJ2⟩
  dsimp only at hS2 hg2 hc2 hJ2
  have hg12 := hg1.trans hg2
  rcases x with _ | cs
  · rw [frK2_fail (h := hc2)]; exact RSim.pure_some ⟨⟨hS2, hg12, rfl⟩, hJ2⟩
  obtain ⟨h21, hdn2, ht2⟩ := hc2
  rw [frK2_ok (h := by rw [h21]; decide)]
  refine RSim.lstep (K := frK3) rfl ?_
  rintro ⟨r3, m3⟩ h3
  obtain ⟨hS3, hg3, hr3, hget, htop⟩ := recW_stage h3 hS2 rfl
  have hJ3 := hO.1 _ _ (recW_afr h3) hJ2
  rw [frK3_some, hr3]
  have hq : rdW (m2.arr64 CTL) 200 = rdW (m2.arr64 CTL) 200 := rfl
  have k0 := rec_iwN_stab hq hget htop 0 (by simp)
  have k1 := rec_iwN_stab hq hget htop 1 (by simp)
  have k2 := rec_iwN_stab hq hget htop 2 (by simp)
  have k3 := rec_iwN_stab hq hget htop 3 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at k0 k1 k2 k3
  have hsp3 := hsp.grow (hg12.trans hg3)
  refine RSim.pure_some ⟨⟨hS3, hg12.trans hg3, rfl, ?_, so.toNat, sl.toNat, ?_, ?_, ?_⟩, hJ3⟩
  all_goals simp only [List.headD_cons, List.tail_cons]
  · intro m' hg
    have e1 : iwN m' ((rdW (m2.arr64 CTL) 200).toNat + 0 + 1) = some sl.toNat := by simpa using k1 m' hg
    have e3 : iwN m' ((rdW (m2.arr64 CTL) 200).toNat + 2 + 1) = some (r2.tail.tail.headD 0).toNat :=
      k3 m' hg
    have hdn' : decNL m' (r2.tail.headD 0).toNat (r2.tail.tail.headD 0).toNat = some cs := by
      rw [decNL_grow (hg3.trans hg) ht2]; exact hdn2
    simp only [decCR, decAt, Nat.add_zero] at e1 ⊢
    simp only [k0 m' hg, e1, k2 m' hg, e3, (hsp3.grow hg).decPL, hdn', Option.bind_eq_bind,
      Option.bind_some]
    rfl
  · simpa using k0 _ (IWGrow.refl _)
  · simpa using k1 _ (IWGrow.refl _)
  · exact hsp3

theorem decRS_rP {m : Mem} {p : Nat} {R : RecShape} (h : decRS m p = some R) :
    ∃ q, iwN m p = some q ∧ decCVp m q = some R.cvR ∧ iwN m (p + 1) = some R.rP := by
  simp only [decRS, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨q, hq, cv, hcv, rP, hrP, mI, hmI, tg, htg, rh, hrh, rfl⟩ := h
  exact ⟨q, hq, hcv, hrP⟩

theorem readW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (cR : CallM)
    (J : Mem → Prop) (hO : OpfJ cR J dn vis fe) (N : Nat) (m : Mem)
    (a : AState) (p nP ro rl : Word) (bs : BlockShape) (recs : List RecShape)
    (hS : StageR dn vis fe m a) (hJ : J m) (hb : BSOK m p.toNat bs) (hrecs : RecsDec m ro rl recs) :
    RSim (readW cR N m p vis nP ro rl) (ConRon.Arena.classRead bs fe nP.toNat recs) a
      (fun b a' x => KP dn vis fe m decRead b a' x ∧ J b.2) := by
  rcases N with _ | N
  · exact RSim.none
  have hdp := hrecs.dec (IWGrow.refl m)
  have hsz := hS.2.2.2.1
  have hts : iwTop m ≤ (m.arr64 IW).size := hS.2.1
  by_cases hrl : rl = 0
  · rw [readW_nil (h := hrl)]
    have : recs = [] := by
      have := decPL_length m hdp; rw [hrl] at this; exact List.eq_nil_of_length_eq_zero this
    subst this
    rw [ConRon.Arena.classRead]
    exact RSim.pure_some ⟨⟨hS, IWGrow.refl m, rfl⟩, hJ⟩
  obtain ⟨k, hk⟩ : ∃ k, rl.toNat = k + 1 :=
    ⟨rl.toNat - 1, by have : rl.toNat ≠ 0 := fun e => hrl (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  have hdpT := hrecs.1
  simp only [DecB] at hdpT
  rw [hk] at hdpT hdp
  obtain ⟨p0, rc0, rest, rfl, hp0T, hrcT, -⟩ := decPL_cons hdpT
  obtain ⟨hro, hp0⟩ := iwN_truncM_get hp0T
  obtain ⟨q, hqT, hcvT, hrPT⟩ := decRS_rP hrcT
  obtain ⟨hp0lt, hq⟩ := iwN_truncM_get hqT
  obtain ⟨hp1lt, hrP⟩ := iwN_truncM_get hrPT
  have hcv : decCVp m q = some rc0.cvR := (OMono.decCVp q).mono _ _ _ (IWGrow.refl m).truncExt hcvT
  rw [readW_ok (h := hrl)]
  rw [ConRon.Arena.classRead]
  have hrd0 := (iwN_rdW hp0 (by omega)).1
  rw [UInt64.ofNat_toNat] at hrd0
  have hrdq := iwN_rdW hq (by omega)
  have hqb : q < 2 ^ 64 := hrdq.2
  have hq3 : (UInt64.ofNat q).toNat + 3 < 2 ^ 64 := by
    rw [UInt64.toNat_ofNat_of_lt' hqb]
    have := hS.2.2.2.2.1
    obtain ⟨w, hw, -⟩ := hd?_some (decCV_type hcv)
    have := (Array.getElem?_eq_some_iff.mp hw).1
    simp only [erA] at this; omega
  obtain ⟨htyH, htyE⟩ := decCVp_type (q := UInt64.ofNat q)
    (by rw [UInt64.toNat_ofNat_of_lt' hqb]; exact hcv) hq3
  rw [hrd0, hrdq.1]
  rw [← htyE]
  refine RSim.bind (K := rdK1 cR N p vis nP ro rl (UInt64.ofNat p0)) rfl (hO.sim N hS hJ htyH) ?_
  rintro ⟨r1, m1⟩ o a1 - ⟨⟨hS1, hg1, ho⟩, hJ1⟩
  dsimp only at hS1 hg1 ho hJ1
  rcases o with _ | fb
  · rw [rdK1_fail (h := ho)]; exact RSim.pure_some ⟨⟨hS1, hg1, rfl⟩, hJ1⟩
  obtain ⟨fvs, body⟩ := fb
  obtain ⟨h11, -, hbH, rfl⟩ := ho
  rw [drop3_headD] at hbH ⊢
  rw [rdK1_ok (h := by rw [h11]; decide)]
  have hrP1 : rdW (m1.arr64 IW) (UInt64.ofNat p0 + 1) = UInt64.ofNat rc0.rP := by
    have h := iwN_rdW_at (w := UInt64.ofNat p0) (k := 1) (m := m)
      (by rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]; exact hrP) hsz
    rw [show UInt64.ofNat 1 = (1 : Word) from rfl] at h
    rw [← h.1]; simp only [rdW]
    rw [show (UInt64.ofNat p0 + 1).toNat = p0 + 1 by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]; simp; omega,
      hg1.2.2.1 _ hp1lt]
  have hrPb : rc0.rP < 2 ^ 64 := (iwN_rdW hrP (by omega)).2
  rw [hrP1]
  have hts1 : (tsubW (UInt64.ofNat rc0.rP) nP).toNat = rc0.rP - nP.toNat := by
    by_cases hle : nP ≤ UInt64.ofNat rc0.rP
    · rw [tsubW_le _ _ hle, UInt64.toNat_sub_of_le _ _ hle, UInt64.toNat_ofNat_of_lt' hrPb]
    · rw [tsubW_gt _ _ hle]
      have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hle)
      rw [UInt64.toNat_ofNat_of_lt' hrPb] at this; simp; omega
  have hsl := (slots_sims dn vis fe cR J hO p nP bs N).1 m1 a1 (tsubW (UInt64.ofNat rc0.rP) nP) 0 0 nP
    (r1.tail.tail.tail.headD 0) [] hS1 hJ1 hbH (hb.grow hg1) (by simp [decNL]) (by simp)
    (by rw [hts1]; have := nP.toNat_lt; omega)
  rw [hts1] at hsl
  try simp only [UInt64.toNat_zero] at hsl
  refine RSim.bind (K := rdK2 cR N nP ro rl) rfl hsl ?_
  rintro ⟨r2, m2⟩ o a2 - ⟨⟨hS2, hg2, ho2⟩, hJ2⟩
  dsimp only at hS2 hg2 ho2 hJ2
  have hg12 := hg1.trans hg2
  rcases o with _ | slots
  · rw [rdK2_fail (h := ho2)]; exact RSim.pure_some ⟨⟨hS2, hg12, rfl⟩, hJ2⟩
  obtain ⟨h21, hsp⟩ := ho2
  rw [rdK2_ok (h := by rw [h21]; decide)]
  refine RSim.bindPure (K := rdK3) rfl (readFinW_sim dn vis fe cR J hO N m2 a2 nP _ _ ro rl slots _ hS2
    hJ2 hsp (hrecs.grow hg12)) ?_
  rintro ⟨r3, m3⟩ x a3 - ⟨⟨hS3, hg3, hd3⟩, hJ3⟩
  rw [rdK3_some]
  refine RSim.pure_some ⟨⟨hS3, hg12.trans hg3, ?_⟩, hJ3⟩
  cases x <;> exact hd3

end L.Ind

namespace L.Ind

open L.Arena

/-- **`class_read` refines `classRead` and keeps `AbsOK`**: `classRead_refines` with the program's
own `open_pis_at_fvars_f` (`opfF_ok`), so the walk memos are well formed after (no `AbsKeep`
premise). -/
theorem classRead_refinesA (p : Prog) (hP : ReadProg p) (hOpf : OpfF p) (N : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (q nP ro rl : Word)
    (bs : BlockShape) (recs : List RecShape) (hS : StageR dn vis fe s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hb : BSOK s₀.mem q.toNat bs) (hrecs : RecsDec s₀.mem ro rl recs) :
    ⦃fun s => s = s₀⦄ invoke p (exec p N) "class_read" [q, vis, nP, ro, rl]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classRead bs fe nP.toNat recs) a₀ ∧
      KP dn vis fe s₀.mem decRead (r, s'.mem) (AM.st (ConRon.Arena.classRead bs fe nP.toNat recs) a₀)
        (AM.res (ConRon.Arena.classRead bs fe nP.toNat recs) a₀) ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (classRead_spec p hP (realCall p) (realCall_spec p) N s₀ q vis nP ro rl) fun _ _ ⟨hl, hw⟩ =>
    let ⟨hok, hK, hA'⟩ := (readW_sim dn vis fe (realCall p) AbsOK (opfJ_real hOpf dn vis fe) N _ a₀ q nP
      ro rl bs recs hS hA hb hrecs).am hw
    ⟨hl, hok, hK, hA'⟩

end L.Ind
