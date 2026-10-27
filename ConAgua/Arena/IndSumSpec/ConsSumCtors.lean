import ConAgua.Arena.IndInstallSpec.BlockCapsAt
import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved
import ConAgua.Arena.DeclRec
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr

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

/-- The memory after `ctor_info_rec`'s seven writes (each copy reads the memory of its time). -/
def ciRecMem (m1 : Mem) (q cv nP nF : Word) : Mem :=
  let m2 := m1.set64 EREC q 4
  let m3 := m2.set64 EREC (q + 1) (rdW (m2.arr64 EREC) cv)
  let m4 := m3.set64 EREC (q + 2) (rdW (m3.arr64 EREC) (cv + 1))
  let m5 := m4.set64 EREC (q + 3) (rdW (m4.arr64 EREC) (cv + 2))
  let m6 := m5.set64 EREC (q + 4) (rdW (m5.arr64 EREC) (cv + 3))
  (m6.set64 EREC (q + 5) nP).set64 EREC (q + 6) nF

/-- The model of `ctor_info_rec(cv, nP, nF)`. -/
def ciRecW (m : Mem) (cv nP nF : Word) : Option (Word × Mem) :=
  match erAllocW m 7 with
  | none => none
  | some (q, m1) =>
    if 4294967296 ≤ rdW ((ciRecMem m1 q cv nP nF).arr64 EREC) (q + 1) then none
    else some (q, ciRecMem m1 q cv nP nF)

theorem ciRec_specW (p : Prog) (ha : p.lookup "erec_alloc" = some erecAlloc)
    (hp : p.lookup "ctor_info_rec" = some ctorInfoRecL) (n : Nat) (s₀ : St) (cv nP nF : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ctor_info_rec" [cv, nP, nF]
    ⦃fun r s' => LocEq s' s₀ ∧ ciRecW s₀.mem cv nP nF = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, ctorInfoRecL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        erecAlloc_specW p ha n] <;>
      finish [ciRecW, ciRecMem]

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
  (hci : p.lookup "ctor_info_rec" = some ctorInfoRecL)
  (hp : p.lookup "cons_sum_ctors" = some consSumCtorsL)

include ha hci hp in
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
        ciRec_specW p ha hci n, callW_spec p n "env_push", ih] <;> finish (gen := 20) [rdW_eq]

end spec

/-! ## `ctor_info_rec` under the stage relation -/

theorem rdW_set64_ne_er {m : Mem} {x y v : Word} (h : x.toNat ≠ y.toNat) :
    rdW ((m.set64 EREC x v).arr64 EREC) y = rdW (m.arr64 EREC) y := by
  simp only [rdW, Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  simp [h]

/-- The four copied words of a constant, decoded at a shifted place, decode the same. -/
theorem decCV_shift {a : Array Word} {q c : Nat} (h0 : a[q]? = a[c]?) (h1 : a[q + 1]? = a[c + 1]?)
    (h2 : a[q + 2]? = a[c + 2]?) (h3 : a[q + 3]? = a[c + 3]?) : decCV a q = decCV a c := by
  simp only [decCV, hlist?, hd?, nat?, h0, h1, h2, h3]

theorem ciRecMem_eq {m1 : Mem} {q cq nP nF : Word} (hlt : cq.toNat + 4 ≤ q.toNat)
    (hq : q.toNat + 7 < 2 ^ 64) :
    ciRecMem m1 q cq nP nF = wrER m1 q [4, rdW (m1.arr64 EREC) cq, rdW (m1.arr64 EREC) (cq + 1),
      rdW (m1.arr64 EREC) (cq + 2), rdW (m1.arr64 EREC) (cq + 3), nP, nF] := by
  have t1 : (q + 1).toNat = q.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have t2 : (q + 2).toNat = q.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have t3 : (q + 3).toNat = q.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  have c1 : (cq + 1).toNat = cq.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have c2 : (cq + 2).toNat = cq.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have c3 : (cq + 3).toNat = cq.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  simp only [ciRecMem, wrER]
  rw [show q + 1 + 1 = q + 2 by ac_rfl, show q + 2 + 1 = q + 3 by ac_rfl,
    show q + 3 + 1 = q + 4 by ac_rfl, show q + 4 + 1 = q + 5 by ac_rfl,
    show q + 5 + 1 = q + 6 by ac_rfl]
  simp (disch := ((try simp only [t1, t2, t3, c1, c2, c3]); omega)) only [rdW_set64_ne_er]

/-- **`ctor_info_rec` under the stage relation**: a fresh `.ctorInfo` record of the constant at `cq`
(decoded in the record pool below its top), the stage relation kept. -/
theorem ciRec_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {cq nP nF q : Word} {cv : IConstantVal} (h : ciRecW m cq nP nF = some (q, m'))
    (hS : StageR dn vis fe m a) (hcv : decCV (erecP m) cq.toNat = some cv) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      decCI (erecP m') dn q.toNat = some (.ctorInfo cv nP.toNat nF.toNat) := by
  rcases h1 : erAllocW m 7 with _ | ⟨q1, m1⟩
  · simp [ciRecW, h1] at h
  have e : ciRecW m cq nP nF = if 4294967296 ≤ rdW ((ciRecMem m1 q1 cq nP nF).arr64 EREC) (q1 + 1)
      then none else some (q1, ciRecMem m1 q1 cq nP nF) := by simp [ciRecW, h1]
  rw [e] at h
  split at h
  · cases h
  obtain ⟨rfl, rfl⟩ : q1 = q ∧ ciRecMem m1 q1 cq nP nF = m' := by simpa using h
  -- the constant's words lie below the old top
  have h3 : (erecP m)[cq.toNat + 3]? ≠ none := by
    have := decCV_type hcv; intro e; simp [hd?, e] at this
  have hcq : cq.toNat + 4 ≤ erTop m := by
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp h3; have := erecP_lt hv; omega
  have hE1 : m1.arr64 EREC = m.arr64 EREC := by
    simp only [erAllocW] at h1; split at h1; · cases h1
    split at h1; · cases h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨-, rfl⟩ := h1
    simp only [erAllocMem]; exact Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  obtain ⟨-, hEtop, -, hEsz, -⟩ := hS.2
  have hq1 : q1.toNat = erTop m := by
    simp only [erAllocW] at h1; split at h1; · cases h1
    split at h1; · cases h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨rfl, -⟩ := h1; rfl
  obtain ⟨hS', hg, -, htop', hget⟩ := erRec_stage h1 hS [4, rdW (m.arr64 EREC) cq,
    rdW (m.arr64 EREC) (cq + 1), rdW (m.arr64 EREC) (cq + 2), rdW (m.arr64 EREC) (cq + 3), nP, nF]
    (by simp)
  have hroom : q1.toNat + 7 < 2 ^ 64 := by
    obtain ⟨-, h2, -, h4, -⟩ := hS'.2; simp only [List.length_cons, List.length_nil] at htop'; omega
  rw [ciRecMem_eq (by omega) hroom, hE1]
  refine ⟨hS', hg, ?_⟩
  generalize hM : wrER m1 q1 _ = M at hS' hg htop' hget
  -- the new record's words, in the pool below the new top
  have hP : ∀ j, j < 7 → (erecP M)[q1.toNat + j]? = ((M.arr64 EREC))[q1.toNat + j]? :=
    fun j hj => erecP_getE (by simp at htop'; omega)
  have c1 : (cq + 1).toNat = cq.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have c2 : (cq + 2).toNat = cq.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have c3 : (cq + 3).toNat = cq.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  have hw : ∀ i, i < 4 → (erecP M)[q1.toNat + 1 + i]? = (erecP M)[cq.toNat + i]? := by
    intro i hi
    rw [show q1.toNat + 1 + i = q1.toNat + (i + 1) by omega, hP (i + 1) (by omega),
      hget (i + 1) (by simp; omega), erecP_getE (by omega), hg.2.2.2 _ (by omega)]
    have hlt : cq.toNat + i < (m.arr64 EREC).size := by simp only [erTop] at hEtop hcq; omega
    rcases i with _ | _ | _ | _ | i
    all_goals first
      | omega
      | (simp only [Nat.add_zero, Nat.zero_add] at hlt ⊢
         simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, rdW, c1, c2, c3,
          Array.getElem?_eq_getElem hlt, Option.getD_some])
  have hcv' : decCV (erecP M) (q1.toNat + 1) = some cv := by
    rw [decCV_shift (by simpa using hw 0 (by decide)) (by simpa using hw 1 (by decide))
      (by simpa [Nat.add_assoc] using hw 2 (by decide)) (by simpa [Nat.add_assoc] using hw 3 (by decide))]
    exact ArrExt.decCV (IWGrow.erecPExtR hg) hcv
  have e0 : (erecP M)[q1.toNat]? = some 4 := by
    have a1 := hP 0 (by decide); have a2 := hget 0 (by simp)
    simp only [Nat.add_zero] at a1 a2; rw [a1, a2]; rfl
  have n0 : nat? (erecP M) q1.toNat = some 4 := by simp [nat?, e0]
  have n5 : nat? (erecP M) (q1.toNat + 5) = some nP.toNat := by
    simp [nat?, hP 5 (by decide), hget 5 (by simp)]
  have n6 : nat? (erecP M) (q1.toNat + 6) = some nF.toNat := by
    simp [nat?, hP 6 (by decide), hget 6 (by simp)]
  simp only [decCI, Option.bind_eq_bind, n0, Option.bind_some, hcv', n5, n6, Option.pure_def]

/-! ## `cons_sum_ctors`: the relation to the twin -/

theorem decCVp_truncM {m : Mem} {q : Nat} {cv : IConstantVal} (h : decCVp (truncM m) q = some cv) :
    decCV (erecP m) q = some cv := by
  refine ArrExt.decCV (fun i v hv => ?_) h
  obtain ⟨hi, hv'⟩ := truncM_er_get hv
  rw [erecP_getE hi]; exact hv'

/-- A pointer word of the pool read below the top, as the model reads it. -/
theorem rdW_of_iwN_truncM {m : Mem} {o : Word} {v : Nat} (h : iwN (truncM m) o.toNat = some v) :
    ∃ w, rdW (m.arr64 IW) o = w ∧ w.toNat = v ∧ o.toNat < iwTop m := by
  simp only [iwN, nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h
  obtain ⟨hi, hw'⟩ := truncM_iw_get hw
  exact ⟨w, rdW_of_get? rfl hw', rfl, hi⟩

/-- **`cons_sum_ctors`' model refines `consSumCtors`**: the view returned relates the environment
with the constructors pushed. -/
theorem cscW_ok (p : Prog) (hRp : RecProg p) {dn : NIdx → Option ConLeche.Name} (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (vis : Word) (fe : IFEnv) (nP o l : Word) (cs : List (IConstantVal × Nat))
      (r : List Word),
    cscW p k m nP o l vis = some (r, m') → StageR dn vis fe m a →
    DecB (fun m => decPL m (decCN m) o.toNat l.toNat) m cs →
    StageR dn (r.headD 0) (consSumCtors nP.toNat cs fe) m' a ∧ IWGrow m m' := by
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
    obtain ⟨hI1, -, hIsz, -, -⟩ := hS.2
    have hcq' : iwN (truncM m) w.toNat = some cqN := by rw [hwv]; exact hcq
    obtain ⟨w2, hw2, hw2v, hpvlt⟩ := rdW_of_iwN_truncM hcq'
    have hw1 : (w + 1).toNat = pv + 1 := by rw [UInt64.toNat_add, hwv]; simp; omega
    have hnF' : iwN (truncM m) (w + 1).toNat = some nF := by rw [hw1]; exact hnF
    obtain ⟨w3, hw3, hw3v, -⟩ := rdW_of_iwN_truncM hnF'
    rw [hw, hw2, hw3] at h
    rcases h1 : ciRecW m w2 nP w3 with _ | ⟨q, m1⟩
    · rw [h1] at h; simp [cscK1] at h
    rw [h1, cscK1_some] at h
    have hcvE : decCV (erecP m) w2.toNat = some cv := by rw [hw2v]; exact decCVp_truncM hcv
    obtain ⟨hS1, hg1, hci⟩ := ciRec_stage h1 hS hcvE
    obtain ⟨wn, hwn, hwnl, -⟩ := decCI_name hci
    have hwn' : (rdW (m1.arr64 EREC) (q + 1)).toNat < 2 ^ 32 := by
      have hq1 : (q + 1).toNat = q.toNat + 1 := by
        have := erecP_lt hwn; obtain ⟨-, h2, -, h4, -⟩ := hS1.2; rw [UInt64.toNat_add]; simp; omega
      rw [rdW_of_get? hq1.symm (erecP_get hwn)]; exact hwnl
    rcases h2 : callW p k "env_push" [vis, q] m1 with _ | ⟨rv, m2⟩
    · rw [h2] at h; simp [cscK2] at h
    rw [h2, cscK2_some] at h
    obtain ⟨s4, hs4, -, hW4⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
      (envPush_specW p hRp k ⟨m1, Locals.init []⟩ vis q hwn') h2
    subst hs4
    obtain ⟨hS2, hg2⟩ := envPushW_ok hW4 hS1 hci
    rcases h3 : cscW p k s4.mem nP (o + 1) (l - 1) (rv.headD 0) with _ | ⟨rr, m3⟩
    · rw [h3] at h; simp [cscK3] at h
    rw [h3, cscK3_some] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have ho1 : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hl1 : (l - 1).toNat = L := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
    have htail' : DecB (fun m => decPL m (decCN m) (o + 1).toNat (l - 1).toNat) s4.mem cs := by
      rw [ho1, hl1]
      exact DecB.grow (OMono.decPL decCN_mono _ _) (hg1.trans hg2) htail
    obtain ⟨hS3, hg3⟩ := ih s4.mem m3 a (rv.headD 0) _ nP (o + 1) (l - 1) cs rr h3 hS2 htail'
    exact ⟨by simpa [consSumCtors, hw3v] using hS3, (hg1.trans hg2).trans hg3⟩

/-- **`cons_sum_ctors` refines `consSumCtors`**: from the stage relation at `vis` of `fe` and the
constructor list decoded below the tops, a returning run returns the view of the environment with
the constructors' `.ctorInfo` records pushed, in order. -/
@[refines ConRon.Arena.consSumCtors]
theorem consSumCtors_refines (p : Prog) (hRp : RecProg p)
    (hci : p.lookup "ctor_info_rec" = some ctorInfoRecL)
    (hp : p.lookup "cons_sum_ctors" = some consSumCtorsL) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis nP o l : Word) (cs : List (IConstantVal × Nat))
    (hS : StageR dn vis fe s₀.mem a₀) (hcs : DecB (fun m => decPL m (decCN m) o.toNat l.toNat) s₀.mem cs) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "cons_sum_ctors" [nP, o, l, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ StageR dn (r.headD 0) (consSumCtors nP.toNat cs fe) s'.mem a₀ ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (csc_spec p hRp.alloc hci hp n s₀ nP o l vis) ?_
  rintro r s' ⟨hl, hm⟩
  exact ⟨hl, cscW_ok p hRp n _ _ a₀ vis fe nP o l cs r hm hS hcs⟩

end L.Ind

end
