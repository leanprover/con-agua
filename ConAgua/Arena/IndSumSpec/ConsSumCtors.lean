module

import ConAgua.Arena.IndInstallSpec.BlockCapsAt
import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved
public import ConAgua.Arena.DeclRec
public import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConRon.Bridge.Grind
public import ConAgua.Arena.IndDecStab
public import ConAgua.Arena.WhnfBase
public import ConAgua.Arena.StageFlags
import all ConAgua.Arena.IndSum
import ConAgua.Arena.DeclCvg
import ConAgua.Arena.RecInfoW
import ConAgua.Arena.RecLayout.CIDec

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

/-- The memory after `ctor_info_rec`'s eight `erec_put`s (each copy reads the memory of its time). -/
def ciRecMem (m1 : Mem) (q cv nP nF T : Word) : Mem :=
  let m2 := erecPutMem m1 q 4
  let m3 := erecPutMem m2 (q + (CI.cv + CV.name)) (erRd m2 cv)
  let m4 := erecPutMem m3 (q + (CI.cv + CV.lpsOff)) (erRd m3 (cv + CV.lpsOff))
  let m5 := erecPutMem m4 (q + (CI.cv + CV.lpsLen)) (erRd m4 (cv + CV.lpsLen))
  let m6 := erecPutMem m5 (q + (CI.cv + CV.type)) (erRd m5 (cv + CV.type))
  erecPutMem (erecPutMem (erecPutMem m6 (q + CI.ctorNparams) nP) (q + CI.ctorNfields) nF)
    (q + CI.ctorInduct) T

/-- The model of `ctor_info_rec(cv, nP, nF, T)`. -/
def ciRecW (m : Mem) (cv nP nF T : Word) : Option (Word × Mem) :=
  match erAllocW m CI.ctorSize with
  | none => none
  | some (q, m1) =>
    if 4294967296 ≤ erRd (ciRecMem m1 q cv nP nF T) (q + (CI.cv + CV.name)) then none
    else if 4294967296 ≤ T then none
    else some (q, ciRecMem m1 q cv nP nF T)

theorem ciRec_specW (p : Prog) (ha : p.lookup "erec_alloc" = some erecAlloc)
    (hpu : p.lookup "erec_put" = some erecPut)
    (hp : p.lookup "ctor_info_rec" = some ctorInfoRecL) (n : Nat) (s₀ : St) (cv nP nF T : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ctor_info_rec" [cv, nP, nF, T]
    ⦃fun r s' => LocEq s' s₀ ∧ ciRecW s₀.mem cv nP nF T = some (r.headD 0, s'.mem); ⊤⦄ := by
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

l_model csc_spec (p : Prog) (ha : p.lookup "erec_alloc" = some erecAlloc)
    (hpu : p.lookup "erec_put" = some erecPut) (hci : p.lookup "ctor_info_rec" = some ctorInfoRecL)
    (hp : p.lookup "cons_sum_ctors" = some consSumCtorsL)
  fns [hp ↦ cscW list]
  specs [ciRec_specW p ha hpu hci n, callW_spec p n "env_push"]
  grind [arena_grind, ind_grind] finish [rdW_eq] gen 20

/-! ## `ctor_info_rec` under the stage relation -/

/-- **The stores are the record's image** (`CI.ctorImg`, `wrERo`), when the constant value's words
are not in the record's region. -/
theorem ciRecMem_eq {m1 : Mem} {q cv nP nF T : Word}
    (hfr : ∀ x ∈ [cv, cv + CV.lpsOff, cv + CV.lpsLen, cv + CV.type], ∀ o : Word,
      o.toNat < CI.ctorSize.toNat → erTier x ≠ erTier (q + o) ∨ erOff x ≠ erOff (q + o)) :
    ciRecMem m1 q cv nP nF T = wrERo m1 q (CI.ctorImg 4 (erRd m1 cv)
      (erRd m1 (cv + CV.lpsOff)) (erRd m1 (cv + CV.lpsLen)) (erRd m1 (cv + CV.type)) nP nF T) := by
  have h0 : ∀ x ∈ [cv, cv + CV.lpsOff, cv + CV.lpsLen, cv + CV.type],
      erTier x ≠ erTier q ∨ erOff x ≠ erOff q := fun x hx => by
    simpa using hfr x hx 0 (by decide)
  simp only [ciRecMem]
  -- the reads first (each at a word outside the record), then the stores in field order
  simp (disch := first | exact h0 _ (by simp) | exact hfr _ (by simp) _ (by decide))
    only [erRd_erecPutMem_ne]
  -- the image's entries in order (the layout's numbers: a whole-record writer)
  simp [wrERo, CI.ctorImg, recImg, rec_unfold, UInt64.add_assoc]

/-- **`ctor_info_rec` under the stage relation**: a fresh `.ctorInfo` record of the constant at `cq`
(decoded in the record pool below its top), the stage relation kept. -/
theorem ciRec_stage {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {cq nP nF T q : Word} {cv : IConstantVal} (h : ciRecW m cq nP nF T = some (q, m'))
    (hS : StageR vis fe m a) (hcv : decCV (erecP m) cq.toNat = some cv) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      decCI (erecP m') q.toNat = some (.ctorInfo cv nP.toNat nF.toNat (decI T)) := by
  rcases h1 : erAllocW m CI.ctorSize with _ | ⟨q1, m1⟩
  · simp [ciRecW, h1] at h
  have e : ciRecW m cq nP nF T = if 4294967296 ≤ erRd (ciRecMem m1 q1 cq nP nF T) (q1 + (CI.cv + CV.name))
      then none else if 4294967296 ≤ T then none else some (q1, ciRecMem m1 q1 cq nP nF T) := by
    simp [ciRecW, h1]
  rw [e] at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i hT
  have hTlt : T.toNat < 2 ^ 32 := by
    have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hT); simpa using this
  obtain ⟨rfl, rfl⟩ : q1 = q ∧ ciRecMem m1 q1 cq nP nF T = m' := by simpa using h
  obtain ⟨⟨w0, hw0, -⟩, -, ⟨w3, hw3, -⟩⟩ := decCV_words hcv
  obtain ⟨w1, w2, hw1, hw2, -⟩ := decCV_slice hcv
  have r := erRdOK m
  have hfr : ∀ x ∈ [cq, cq + CV.lpsOff, cq + CV.lpsLen, cq + CV.type], ∀ o : Word,
      o.toNat < CI.ctorSize.toNat → erTier x ≠ erTier (q1 + o) ∨ erOff x ≠ erOff (q1 + o) := by
    intro x hx o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact erFreshW h1 hS.iw hw0 ho
    · exact erFreshW h1 hS.iw (by rw [rd_off_toNat r hw1]; exact hw1) ho
    · exact erFreshW h1 hS.iw (by rw [rd_off_toNat r hw2]; exact hw2) ho
    · exact erFreshW h1 hS.iw (by rw [rd_off_toNat r hw3]; exact hw3) ho
  obtain ⟨-, hf1, -⟩ := erAllocW_spec h1 hS.iw
  have hr1 : ∀ x, erRd m1 x = erRd m x := fun x => by
    unfold erRd; rw [hf1.arr _ (by simp) (by rw [tierA_EREC]; split <;> decide)]
  rw [ciRecMem_eq hfr, hr1, hr1, hr1, hr1]
  generalize hI : CI.ctorImg 4 (erRd m cq) (erRd m (cq + CV.lpsOff)) (erRd m (cq + CV.lpsLen))
    (erRd m (cq + CV.type)) nP nF T = I
  have hIl : I.length = CI.ctorSize.toNat := by rw [← hI, CI.ctorImg_length]
  obtain ⟨hS', hg, -, -, -, -, hget⟩ := erRecO_stage h1 hS I hIl.symm
  refine ⟨hS', hg, ?_⟩
  generalize wrERo m1 q1 I = M at hS' hg hget
  have g := fun {o : Word} {x : Word} (e : I[o.toNat]? = some (some x)) => hget o.toNat x e
  obtain ⟨en, enl, hsl, -, et, etl⟩ := decCV_rd r hcv
  have adj : ∀ f : Word, f.toNat ≤ 64 →
      q1.toNat + (CI.cv + f).toNat = q1.toNat + CI.cv.toNat + f.toNat := fun f hf => by
    rw [CI.cv_add_toNat hf, Nat.add_assoc]
  have hw : CVRecW (erecP M) (q1.toNat + CI.cv.toNat) (erRd m cq) (erRd m (cq + CV.lpsOff))
      (erRd m (cq + CV.lpsLen)) (erRd m (cq + CV.type)) :=
    ⟨by rw [← adj _ CV.name_le]; exact g (hI ▸ CI.ctorImg_name ..),
      by rw [← adj _ CV.lpsOff_le]; exact g (hI ▸ CI.ctorImg_lo ..),
      by rw [← adj _ CV.lpsLen_le]; exact g (hI ▸ CI.ctorImg_ll ..),
      by rw [← adj _ CV.type_le]; exact g (hI ▸ CI.ctorImg_ty ..)⟩
  have hcv' : decCV (erecP M) (q1.toNat + CI.cv.toNat) = some cv := by
    rw [decCV_of_words hw enl etl (ArrExt.hslice? (IWGrow.ext hg) hsl), ← en, ← et]
  have n0 := g (o := CI.kind) (hI ▸ CI.ctorImg_kind ..)
  rw [show CI.kind.toNat = 0 from rfl, Nat.add_zero] at n0
  exact decCI_ctorInfo_iff.mpr ⟨by simp [nat?, n0], hcv',
    by simp [nat?, g (hI ▸ CI.ctorImg_nparams ..)], by simp [nat?, g (hI ▸ CI.ctorImg_nfields ..)],
    by simp [hd?, g (hI ▸ CI.ctorImg_induct ..), hTlt]⟩

/-! ## `cons_sum_ctors`: the relation to the twin -/

theorem decCVp_truncM {m : Mem} {q : Nat} {cv : IConstantVal} (h : decCVp (truncM m) q = some cv) :
    decCV (erecP m) q = some cv := by
  rw [decCVp, truncM_erA] at h; exact h

/-- **`env_push` of a decoded record under the stage relation**: the new view relates the pushed
environment; the pools are kept. -/
theorem envPush_stage {p : Prog} (hP : EnvFlagsProg p) {n : Nat} {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {c : Word} {r : List Word} {ci : IConstantInfo}
    (hc : callW p n "env_push" [vis, c] m = some (r, m'))
    (hS : StageR vis fe m a) (hci : decCI (erecP m) c.toNat = some ci) :
    StageR (r.headD 0) (fe.push ci) m' a ∧ IWGrow m m' := by
  obtain ⟨s', hs', -, hr, -, -, -, hE, hm⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envPush_refines hP n ⟨m, Locals.init []⟩ vis c hS.check.env hci (by have := hS.iw.ctl; omega)) hc
  subst hs' hr
  simp only [List.headD_cons]
  rw [hm] at hE ⊢
  exact StageR.of_ownFlags hS hE

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
    ∀ (m m' : Mem) (a : AState) (vis : Word) (fe : IFEnv) (nP T o l : Word)
      (cs : List (IConstantVal × Nat)) (r : List Word),
    cscW p k m nP T o l vis = some (r, m') → StageR vis fe m a →
    DecB (fun m => decPL m (decCN m) o.toNat l.toNat) m cs →
    StageR (r.headD 0) (consSumCtors nP.toNat (decI T) cs fe) m' a ∧ IWGrow m m' := by
  induction k with
  | zero => intro m m' a vis fe nP T o l cs r h; simp [cscW] at h
  | succ k ih =>
    intro m m' a vis fe nP T o l cs r h hS hcs
    by_cases hl : l = 0
    · rw [cscW.arm1 p k m nP T o l vis hl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have : cs = [] := by
        have := hcs; simp only [DecB, hl, decPL] at this; simpa using this.symm
      subst this
      exact ⟨hS, IWGrow.refl _⟩
    rw [cscW.arm2 p k m nP T o l vis hl] at h
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
    rcases h1 : ciRecW m w2 nP w3 T with _ | ⟨q, m1⟩
    · rw [h1, cscW.k_ctor_info_rec.none] at h; cases h
    rw [h1, cscW.k_ctor_info_rec.arm1] at h
    have hcvE : decCV (erecP m) w2.toNat = some cv := by rw [hw2v]; exact decCVp_truncM hcv
    obtain ⟨hS1, hg1, hci⟩ := ciRec_stage h1 hS hcvE
    rcases h2 : callW p k "env_push" [vis, q] m1 with _ | ⟨rv, m2⟩
    · rw [h2, cscW.k_env_push.none] at h; cases h
    rw [h2, cscW.k_env_push.arm1] at h
    obtain ⟨hS2, hg2⟩ := envPush_stage hRp.ef h2 hS1 hci
    rcases h3 : cscW p k m2 nP T (o + 1) (l - 1) (rv.headD 0) with _ | ⟨rr, m3⟩
    · rw [h3, cscW.k_cons_sum_ctors.none] at h; cases h
    rw [h3, cscW.k_cons_sum_ctors.arm1] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have ho1 : (o + 1).toNat = o.toNat + 1 := by
      have := hS.iw.iwSize; have := hS.iw.iw; rw [UInt64.toNat_add]; simp; omega
    have hl1 : (l - 1).toNat = L := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
    have htail' : DecB (fun m => decPL m (decCN m) (o + 1).toNat (l - 1).toNat) m2 cs := by
      rw [ho1, hl1]
      exact DecB.grow (OMono.decPL decCN_mono _ _) (hg1.trans hg2) htail
    obtain ⟨hS3, hg3⟩ := ih m2 m3 a (rv.headD 0) _ nP T (o + 1) (l - 1) cs rr h3 hS2 htail'
    exact ⟨by simpa [consSumCtors, hw3v] using hS3, (hg1.trans hg2).trans hg3⟩

/-- **`cons_sum_ctors` refines `consSumCtors`**: from the stage relation at `vis` of `fe` and the
constructor list decoded below the tops, a returning run returns the view of the environment with
the constructors' `.ctorInfo` records pushed, in order. -/
@[refines ConRon.Arena.consSumCtors]
theorem consSumCtors_refines (p : Prog) (hRp : RecProg p)
    (hci : p.lookup "ctor_info_rec" = some ctorInfoRecL)
    (hp : p.lookup "cons_sum_ctors" = some consSumCtorsL) (n : Nat) (s₀ : St) (a₀ : AState)
    (fe : IFEnv) (vis nP T o l : Word) (cs : List (IConstantVal × Nat))
    (hS : StageR vis fe s₀.mem a₀) (hcs : DecB (fun m => decPL m (decCN m) o.toNat l.toNat) s₀.mem cs) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "cons_sum_ctors" [nP, T, o, l, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ StageR (r.headD 0) (consSumCtors nP.toNat (decI T) cs fe) s'.mem a₀ ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (csc_spec p hRp.alloc hRp.put hci hp n s₀ nP T o l vis) ?_
  rintro r s' ⟨hl, hm⟩
  exact ⟨hl, cscW_ok p hRp n _ _ a₀ vis fe nP T o l cs r hm hS hcs⟩

end L.Ind

end
