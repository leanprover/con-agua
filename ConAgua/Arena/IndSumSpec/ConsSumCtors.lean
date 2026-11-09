module

import ConAgua.Arena.IndInstallSpec.BlockCapsAt
import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved
public import ConAgua.Arena.DeclRec
public import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.Arena.IndPosSpec.NestBlockOfKey
import ConAgua.L.WordOff
import ConRon.Bridge.Grind
public import ConAgua.Arena.IndDecStab
public import ConAgua.Arena.WhnfBase
import all ConAgua.Arena.IndSum

@[expose] public section

/-!
# ConsSumCtors: `ConRon.Arena.consSumCtors`

The refinement theorems `consSumCtors_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `ctor_info_rec` -/

/-- The memory after `ctor_info_rec`'s seven `erec_put`s (each copy reads the memory of its time). -/
def ciRecMem (m1 : Mem) (q cv nP nF : Word) : Mem :=
  let m2 := erecPutMem m1 q 4
  let m3 := erecPutMem m2 (q + 1) (erRd m2 cv)
  let m4 := erecPutMem m3 (q + 2) (erRd m3 (cv + 1))
  let m5 := erecPutMem m4 (q + 3) (erRd m4 (cv + 2))
  let m6 := erecPutMem m5 (q + 4) (erRd m5 (cv + 3))
  erecPutMem (erecPutMem m6 (q + 5) nP) (q + 6) nF

/-- The model of `ctor_info_rec(cv, nP, nF)`. -/
def ciRecW (m : Mem) (cv nP nF : Word) : Option (Word × Mem) :=
  match erAllocW m 7 with
  | none => none
  | some (q, m1) =>
    if 4294967296 ≤ erRd (ciRecMem m1 q cv nP nF) (q + 1) then none
    else some (q, ciRecMem m1 q cv nP nF)

theorem ciRec_specW (p : Prog) (ha : p.lookup "erec_alloc" = some erecAlloc)
    (hpu : p.lookup "erec_put" = some erecPut)
    (hp : p.lookup "ctor_info_rec" = some ctorInfoRecL) (n : Nat) (s₀ : St) (cv nP nF : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ctor_info_rec" [cv, nP, nF]
    ⦃fun r s' => LocEq s' s₀ ∧ ciRecW s₀.mem cv nP nF = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, ctorInfoRecL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        erecAlloc_specW p ha n, erecPut_specW p hpu n] <;>
      finish [ciRecW, ciRecMem, erRd]

/-! ## `cons_sum_ctors`: the word model -/

/-- The returned view. -/
def cscK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

mutual
/-- The model of `cons_sum_ctors(nP, o, l, vis)` at exec fuel `n`. -/
def cscW (p : Prog) : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, nP, o, l, vis =>
    if l = 0 then some ([vis], m)
    else cscK1 p n nP o l vis (ciRecW m (rdW (m.arr64 IW) (rdW (m.arr64 IW) o)) nP
      (rdW (m.arr64 IW) (rdW (m.arr64 IW) o + 1)))
/-- After `ctor_info_rec`: the push. -/
def cscK1 (p : Prog) (n : Nat) (nP o l vis : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (q, m1) => cscK2 p n nP o l (callW p n "env_push" [vis, q] m1)
/-- After `env_push`: the rest. -/
def cscK2 (p : Prog) (n : Nat) (nP o l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rv, m2) => cscK3 (cscW p n m2 nP (o + 1) (l - 1) (rv.headD 0))
end

section arms
variable (p : Prog) (n : Nat) (m m1 m2 : Mem) (nP o l vis q : Word) (rv : List Word)
theorem cscW_nil (h : l = 0) : cscW p (n + 1) m nP o l vis = some ([vis], m) := by simp [cscW, h]
theorem cscW_cons (h : l ≠ 0) : cscW p (n + 1) m nP o l vis = cscK1 p n nP o l vis (ciRecW m
    (rdW (m.arr64 IW) (rdW (m.arr64 IW) o)) nP (rdW (m.arr64 IW) (rdW (m.arr64 IW) o + 1))) := by
  simp [cscW, h]
theorem cscK1_some : cscK1 p n nP o l vis (some (q, m1)) =
    cscK2 p n nP o l (callW p n "env_push" [vis, q] m1) := by simp [cscK1]
theorem cscK2_some : cscK2 p n nP o l (some (rv, m2)) =
    cscK3 (cscW p n m2 nP (o + 1) (l - 1) (rv.headD 0)) := by simp [cscK2]
theorem cscK3_some : cscK3 (some (rv, m2)) = some ([rv.headD 0], m2) := rfl
end arms
attribute [ind_grind] cscW_nil cscW_cons cscK1_some cscK2_some cscK3_some

section spec
variable (p : Prog) (ha : p.lookup "erec_alloc" = some erecAlloc)
  (hpu : p.lookup "erec_put" = some erecPut) (hci : p.lookup "ctor_info_rec" = some ctorInfoRecL)
  (hp : p.lookup "cons_sum_ctors" = some consSumCtorsL)

include ha hpu hci hp in
theorem csc_spec (n : Nat) : ∀ (s₀ : St) (nP o l vis : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "cons_sum_ctors" [nP, o, l, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ cscW p n s₀.mem nP o l vis = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ nP o l vis; rw [invoke_eq _ hp]; simp only [callFn, consSumCtorsL]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ nP o l vis
    rw [invoke_eq _ hp]
    simp only [callFn, consSumCtorsL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        ciRec_specW p ha hpu hci n, callW_spec p n "env_push", ih] <;> finish (gen := 20) [rdW_eq]

end spec

/-! ## `ctor_info_rec` under the stage relation -/

theorem rdW_set64_ne_er {m : Mem} {x y v : Word} (h : x.toNat ≠ y.toNat) :
    rdW ((m.set64 EREC x v).arr64 EREC) y = rdW (m.arr64 EREC) y := by
  simp only [rdW, Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  simp [h]

/-- The four copied words of a constant, decoded at a shifted place, decode the same. -/
theorem decCV_shift {a : Nat → Option Word} {q c : Nat} (h0 : a q = a c) (h1 : a (q + 1) = a (c + 1))
    (h2 : a (q + 2) = a (c + 2)) (h3 : a (q + 3) = a (c + 3)) : decCV a q = decCV a c := by
  simp only [decCV, hlist?, hd?, nat?, h0, h1, Nat.add_assoc, show 1 + 1 = 2 from rfl, h2, h3]

theorem ciRecMem_eq {m1 : Mem} {q cq nP nF : Word}
    (hfr : ∀ x ∈ [cq, cq + 1, cq + 2, cq + 3], ∀ j < 7,
      erTier x ≠ erTier (q + UInt64.ofNat j) ∨ erOff x ≠ erOff (q + UInt64.ofNat j)) :
    ciRecMem m1 q cq nP nF = wrER m1 q [4, erRd m1 cq, erRd m1 (cq + 1), erRd m1 (cq + 2),
      erRd m1 (cq + 3), nP, nF] := by
  have f0 : ∀ x ∈ [cq, cq + 1, cq + 2, cq + 3], erTier x ≠ erTier q ∨ erOff x ≠ erOff q :=
    fun x hx => by simpa using hfr x hx 0 (by decide)
  have f1 : ∀ x ∈ [cq, cq + 1, cq + 2, cq + 3], erTier x ≠ erTier (q + 1) ∨ erOff x ≠ erOff (q + 1) :=
    fun x hx => hfr x hx 1 (by decide)
  have f2 : ∀ x ∈ [cq, cq + 1, cq + 2, cq + 3], erTier x ≠ erTier (q + 2) ∨ erOff x ≠ erOff (q + 2) :=
    fun x hx => hfr x hx 2 (by decide)
  have f3 : ∀ x ∈ [cq, cq + 1, cq + 2, cq + 3], erTier x ≠ erTier (q + 3) ∨ erOff x ≠ erOff (q + 3) :=
    fun x hx => hfr x hx 3 (by decide)
  simp only [ciRecMem, wrER]
  rw [show q + 1 + 1 = q + 2 by ac_rfl, show q + 2 + 1 = q + 3 by ac_rfl,
    show q + 3 + 1 = q + 4 by ac_rfl, show q + 4 + 1 = q + 5 by ac_rfl,
    show q + 5 + 1 = q + 6 by ac_rfl]
  simp (disch := first
    | exact f0 _ (by simp) | exact f1 _ (by simp) | exact f2 _ (by simp) | exact f3 _ (by simp))
    only [erRd_erecPutMem_ne]

/-- **`ctor_info_rec` under the stage relation**: a fresh `.ctorInfo` record of the constant at `cq`
(decoded in the record pool below its top), the stage relation kept. -/
theorem ciRec_stage {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {cq nP nF q : Word} {cv : IConstantVal} (h : ciRecW m cq nP nF = some (q, m'))
    (hS : StageR vis fe m a) (hcv : decCV (erecP m) cq.toNat = some cv) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      decCI (erecP m') q.toNat = some (.ctorInfo cv nP.toNat nF.toNat) := by
  rcases h1 : erAllocW m 7 with _ | ⟨q1, m1⟩
  · simp [ciRecW, h1] at h
  have e : ciRecW m cq nP nF = if 4294967296 ≤ erRd (ciRecMem m1 q1 cq nP nF) (q1 + 1)
      then none else some (q1, ciRecMem m1 q1 cq nP nF) := by simp [ciRecW, h1]
  rw [e] at h
  split at h
  · cases h
  obtain ⟨rfl, rfl⟩ : q1 = q ∧ ciRecMem m1 q1 cq nP nF = m' := by simpa using h
  -- the constant's four words, in the old pool
  have hcv0 := hcv
  simp only [decCV, hlist?, bind, Option.bind_eq_some_iff, pure] at hcv0
  obtain ⟨nm, hnm, lps, ⟨lo, hlo, ll, hll, -⟩, t, ht, -⟩ := hcv0
  obtain ⟨w0, hw0, -, -⟩ := hd?_some hnm
  obtain ⟨w1, hw1, -⟩ : ∃ w, erecP m (cq.toNat + 1) = some w ∧ w.toNat = lo := by
    simp only [nat?, Option.map_eq_some_iff] at hlo; exact hlo
  obtain ⟨w2, hw2, -⟩ : ∃ w, erecP m (cq.toNat + 2) = some w ∧ w.toNat = ll := by
    simp only [nat?, Option.map_eq_some_iff, Nat.add_assoc] at hll; exact hll
  obtain ⟨w3, hw3, -, -⟩ := hd?_some ht
  have hW : ∀ i < 4, ∃ w, erecP m (cq.toNat + i) = some w := by
    intro i hi
    rcases i with _ | _ | _ | _ | i
    · exact ⟨w0, by simpa using hw0⟩
    · exact ⟨w1, hw1⟩
    · exact ⟨w2, hw2⟩
    · exact ⟨w3, hw3⟩
    · omega
  have r0 : erRd m cq = w0 := (erRd_of_erecP (by simpa using hw0)).1
  obtain ⟨r1, e1⟩ := erRd_add (j := 1) (cq := cq) (m := m) hw1 (by decide)
  obtain ⟨r2, e2⟩ := erRd_add (j := 2) (cq := cq) (m := m) hw2 (by decide)
  obtain ⟨r3, e3⟩ := erRd_add (j := 3) (cq := cq) (m := m) hw3 (by decide)
  simp only [show (UInt64.ofNat 1 : Word) = 1 from rfl, show (UInt64.ofNat 2 : Word) = 2 from rfl,
    show (UInt64.ofNat 3 : Word) = 3 from rfl] at r1 r2 r3 e1 e2 e3
  have hfr : ∀ x ∈ [cq, cq + 1, cq + 2, cq + 3], ∀ j < 7,
      erTier x ≠ erTier (q1 + UInt64.ofNat j) ∨ erOff x ≠ erOff (q1 + UInt64.ofNat j) := by
    intro x hx j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact erFresh h1 hS.iw (by simpa using hw0) hj
    · exact erFresh h1 hS.iw (by rw [e1]; exact hw1) hj
    · exact erFresh h1 hS.iw (by rw [e2]; exact hw2) hj
    · exact erFresh h1 hS.iw (by rw [e3]; exact hw3) hj
  obtain ⟨-, hf1, -⟩ := erAllocW_spec h1 hS.iw
  have hr1 : ∀ x, erRd m1 x = erRd m x := fun x => by
    unfold erRd; rw [hf1.arr _ (by simp) (by rw [tierA_EREC]; split <;> decide)]
  rw [ciRecMem_eq hfr, hr1, hr1, hr1, hr1, r0, r1, r2, r3]
  obtain ⟨hS', hg, -, -, -, -, hget⟩ := erRec_stage h1 hS [4, w0, w1, w2, w3, nP, nF] (by simp)
  refine ⟨hS', hg, ?_⟩
  generalize wrER m1 q1 _ = M at hS' hg hget
  have hw : ∀ i, i < 4 → erecP M (q1.toNat + 1 + i) = erecP M (cq.toNat + i) := by
    intro i hi
    obtain ⟨w, hw⟩ := hW i hi
    rw [IWGrow.ext hg _ _ hw, Nat.add_assoc, hget (1 + i) (by simp; omega)]
    rcases i with _ | _ | _ | _ | i
    · simp at hw ⊢; rw [hw0] at hw; exact Option.some.inj hw
    · simp at hw ⊢; rw [hw1] at hw; exact Option.some.inj hw
    · simp at hw ⊢; rw [hw2] at hw; exact Option.some.inj hw
    · simp at hw ⊢; rw [hw3] at hw; exact Option.some.inj hw
    · omega
  have hcv' : decCV (erecP M) (q1.toNat + 1) = some cv := by
    rw [decCV_shift (by simpa using hw 0 (by decide)) (by simpa using hw 1 (by decide))
      (by simpa [Nat.add_assoc] using hw 2 (by decide)) (by simpa [Nat.add_assoc] using hw 3 (by decide))]
    exact ArrExt.decCV (IWGrow.ext hg) hcv
  have n0 : nat? (erecP M) q1.toNat = some 4 := by
    have := hget 0 (by simp); simp only [Nat.add_zero] at this; simp [nat?, this]
  have n5 : nat? (erecP M) (q1.toNat + 5) = some nP.toNat := by simp [nat?, hget 5 (by simp)]
  have n6 : nat? (erecP M) (q1.toNat + 6) = some nF.toNat := by simp [nat?, hget 6 (by simp)]
  simp only [decCI, Option.bind_eq_bind, n0, Option.bind_some, hcv', n5, n6, Option.pure_def]

/-! ## `cons_sum_ctors`: the relation to the twin -/

theorem decCVp_truncM {m : Mem} {q : Nat} {cv : IConstantVal} (h : decCVp (truncM m) q = some cv) :
    decCV (erecP m) q = some cv := by
  rw [decCVp, truncM_erA] at h; exact h

/-- **`env_push` of a decoded record under the stage relation**: the new view relates the pushed
environment; the pools are kept. -/
theorem envPush_stage {p : Prog} (hrs : p.lookup "env_row_set" = some envRowSetL)
    (hpu : p.lookup "env_push" = some envPushL) {n : Nat} {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {c : Word} {r : List Word} {ci : IConstantInfo}
    (hc : callW p n "env_push" [vis, c] m = some (r, m'))
    (hS : StageR vis fe m a) (hci : decCI (erecP m) c.toNat = some ci) :
    StageR (r.headD 0) (fe.push ci) m' a ∧ IWGrow m m' := by
  obtain ⟨s', hs', -, hr, hE, hm⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envPush_refines p hrs hpu n ⟨m, Locals.init []⟩ vis c hS.check.env hci) hc
  subst hs' hr
  simp only [List.headD_cons]
  rw [hm] at hE ⊢
  exact StageR.of_own hS hE

/-- A pointer word of the pool read below the top, as the model reads it. -/
theorem rdW_of_iwN_truncM {m : Mem} {o : Word} {v : Nat} (h : iwN (truncM m) o.toNat = some v) :
    ∃ w, rdW (m.arr64 IW) o = w ∧ w.toNat = v ∧ o.toNat < iwTop m := by
  simp only [iwN, nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h
  obtain ⟨hi, hw'⟩ := truncM_iw_get hw
  exact ⟨w, rdW_of_get? rfl hw', rfl, hi⟩

/-- **`cons_sum_ctors`' model refines `consSumCtors`**: the view returned relates the environment
with the constructors pushed. -/
theorem cscW_ok (p : Prog) (hRp : RecProg p) (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (vis : Word) (fe : IFEnv) (nP o l : Word) (cs : List (IConstantVal × Nat))
      (r : List Word),
    cscW p k m nP o l vis = some (r, m') → StageR vis fe m a →
    DecB (fun m => decPL m (decCN m) o.toNat l.toNat) m cs →
    StageR (r.headD 0) (consSumCtors nP.toNat cs fe) m' a ∧ IWGrow m m' := by
  induction k with
  | zero => intro m m' a vis fe nP o l cs r h; simp [cscW] at h
  | succ k ih =>
    intro m m' a vis fe nP o l cs r h hS hcs
    by_cases hl : l = 0
    · rw [cscW_nil p k m nP o l vis hl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have : cs = [] := by
        have := hcs; simp only [DecB, hl, decPL] at this; simpa using this.symm
      subst this
      exact ⟨hS, IWGrow.refl _⟩
    rw [cscW_cons p k m nP o l vis hl] at h
    obtain ⟨L, hL⟩ : ∃ L, l.toNat = L + 1 :=
      ⟨l.toNat - 1, by have : l.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
    have hcs' : decPL (truncM m) (decCN (truncM m)) o.toNat (L + 1) = some cs := by
      have := hcs; simp only [DecB, hL] at this; exact this
    cases cs with
    | nil => have := decPL_length (m := truncM m) hcs'; simp at this
    | cons c cs =>
    obtain ⟨cv, nF⟩ := c
    obtain ⟨pv, hpv, hc⟩ := decPL_head hcs'
    have htail := decPL_tail hcs'
    obtain ⟨⟨cqN, hcq, hcv⟩, hnF⟩ := decCN_some hc
    obtain ⟨w, hw, hwv, ho⟩ := rdW_of_iwN_truncM hpv
    have hcq' : iwN (truncM m) w.toNat = some cqN := by rw [hwv]; exact hcq
    obtain ⟨w2, hw2, hw2v, hpvlt⟩ := rdW_of_iwN_truncM hcq'
    have hw1 : (w + 1).toNat = pv + 1 := by
      have := hS.iw.iwSize; have := hS.iw.iw; rw [UInt64.toNat_add, hwv]; simp; omega
    have hnF' : iwN (truncM m) (w + 1).toNat = some nF := by rw [hw1]; exact hnF
    obtain ⟨w3, hw3, hw3v, -⟩ := rdW_of_iwN_truncM hnF'
    rw [hw, hw2, hw3] at h
    rcases h1 : ciRecW m w2 nP w3 with _ | ⟨q, m1⟩
    · rw [h1] at h; simp [cscK1] at h
    rw [h1, cscK1_some] at h
    have hcvE : decCV (erecP m) w2.toNat = some cv := by rw [hw2v]; exact decCVp_truncM hcv
    obtain ⟨hS1, hg1, hci⟩ := ciRec_stage h1 hS hcvE
    rcases h2 : callW p k "env_push" [vis, q] m1 with _ | ⟨rv, m2⟩
    · rw [h2] at h; simp [cscK2] at h
    rw [h2, cscK2_some] at h
    obtain ⟨hS2, hg2⟩ := envPush_stage hRp.rs hRp.push h2 hS1 hci
    rcases h3 : cscW p k m2 nP (o + 1) (l - 1) (rv.headD 0) with _ | ⟨rr, m3⟩
    · rw [h3] at h; simp [cscK3] at h
    rw [h3, cscK3_some] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have ho1 : (o + 1).toNat = o.toNat + 1 := by
      have := hS.iw.iwSize; have := hS.iw.iw; rw [UInt64.toNat_add]; simp; omega
    have hl1 : (l - 1).toNat = L := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
    have htail' : DecB (fun m => decPL m (decCN m) (o + 1).toNat (l - 1).toNat) m2 cs := by
      rw [ho1, hl1]
      exact DecB.grow (OMono.decPL decCN_mono _ _) (hg1.trans hg2) htail
    obtain ⟨hS3, hg3⟩ := ih m2 m3 a (rv.headD 0) _ nP (o + 1) (l - 1) cs rr h3 hS2 htail'
    exact ⟨by simpa [consSumCtors, hw3v] using hS3, (hg1.trans hg2).trans hg3⟩

/-- **`cons_sum_ctors` refines `consSumCtors`**: from the stage relation at `vis` of `fe` and the
constructor list decoded below the tops, a returning run returns the view of the environment with
the constructors' `.ctorInfo` records pushed, in order. -/
@[refines ConRon.Arena.consSumCtors]
theorem consSumCtors_refines (p : Prog) (hRp : RecProg p)
    (hci : p.lookup "ctor_info_rec" = some ctorInfoRecL)
    (hp : p.lookup "cons_sum_ctors" = some consSumCtorsL) (n : Nat) (s₀ : St) (a₀ : AState)
    (fe : IFEnv) (vis nP o l : Word) (cs : List (IConstantVal × Nat))
    (hS : StageR vis fe s₀.mem a₀) (hcs : DecB (fun m => decPL m (decCN m) o.toNat l.toNat) s₀.mem cs) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "cons_sum_ctors" [nP, o, l, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ StageR (r.headD 0) (consSumCtors nP.toNat cs fe) s'.mem a₀ ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (csc_spec p hRp.alloc hRp.put hci hp n s₀ nP o l vis) ?_
  rintro r s' ⟨hl, hm⟩
  exact ⟨hl, cscW_ok p hRp n _ _ a₀ vis fe nP o l cs r hm hS hcs⟩

end L.Ind

end
