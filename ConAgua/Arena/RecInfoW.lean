module

public import ConAgua.Arena.IndMaster
import ConAgua.Arena.RecLayout.CIDec

@[expose] public section

/-!
# A fresh `.recInfo` record, written field by field

`rec_info_rec` (`RecCheck.lean`) and `class_fe_r_rec` (`RecGen.lean`) allocate a recursor's
record and store its fields by name: the kind word `5`, the constant value at `cv` (read field by
field, between the stores), the recursor's fields. `recInfoMem` is the memory after the stores,
`recInfoMem_eq` the same as the record's image (`CI.recInfoImg`, `wrERo`), and `recInfo_stage` the
record under the stage relation: it decodes as the `.recInfo` constant.
-/

open ConRon.Arena

namespace L.Ind

open L.Arena

/-- The memory after a recursor record's stores at the fresh `q` (the constant value read at `cv`
between them). -/
def recInfoMem (m1 : Mem) (q cv mi rp isK reo rel : Word) : Mem :=
  let m2 := erecPutMem m1 q 5
  let m3 := erecPutMem m2 (q + (CI.cv + CV.name)) (erRd m2 cv)
  let m4 := erecPutMem m3 (q + (CI.cv + CV.lpsOff)) (erRd m3 (cv + CV.lpsOff))
  let m5 := erecPutMem m4 (q + (CI.cv + CV.lpsLen)) (erRd m4 (cv + CV.lpsLen))
  let m6 := erecPutMem m5 (q + (CI.cv + CV.type)) (erRd m5 (cv + CV.type))
  erecPutMem (erecPutMem (erecPutMem (erecPutMem (erecPutMem m6 (q + CI.recMajor) mi)
    (q + CI.recPrefix) rp) (q + CI.recRulesOff) reo) (q + CI.recRulesLen) rel) (q + CI.recIsK) isK

/-- **The stores are the record's image**, when the constant value's words are not in the
record's region. -/
theorem recInfoMem_eq {m1 : Mem} {q cv mi rp isK reo rel : Word}
    (hfr : ∀ x ∈ [cv, cv + CV.lpsOff, cv + CV.lpsLen, cv + CV.type], ∀ o : Word,
      o.toNat < CI.recSize.toNat → erTier x ≠ erTier (q + o) ∨ erOff x ≠ erOff (q + o)) :
    recInfoMem m1 q cv mi rp isK reo rel = wrERo m1 q (CI.recInfoImg 5 (erRd m1 cv)
      (erRd m1 (cv + CV.lpsOff)) (erRd m1 (cv + CV.lpsLen)) (erRd m1 (cv + CV.type)) mi rp reo rel
      isK) := by
  have h0 : ∀ x ∈ [cv, cv + CV.lpsOff, cv + CV.lpsLen, cv + CV.type],
      erTier x ≠ erTier q ∨ erOff x ≠ erOff q := fun x hx => by
    simpa using hfr x hx 0 (by decide)
  simp only [recInfoMem]
  -- the reads first (each at a word outside the record), then the stores in field order
  simp (disch := first | exact h0 _ (by simp) | exact hfr _ (by simp) _ (by decide))
    only [erRd_erecPutMem_ne]
  -- the image's entries in order (the layout's numbers: a whole-record writer)
  simp [wrERo, CI.recInfoImg, recImg, rec_unfold, UInt64.add_assoc]

/-- A fresh region's word `q + o` is not an old word. -/
theorem erFreshW {m m1 : Mem} {k q x : Word} (h : erAllocW m k = some (q, m1)) (hW : IWOK m)
    {v : Word} (hx : erecP m x.toNat = some v) {o : Word} (ho : o.toNat < k.toNat) :
    erTier x ≠ erTier (q + o) ∨ erOff x ≠ erOff (q + o) := by
  have := erFresh h hW hx ho
  rwa [UInt64.ofNat_toNat] at this

/-- **A fresh `.recInfo` record under the stage relation**: allocated (`CI.recSize`), stored
field by field, it decodes as the constant at `cv` with the recursor's fields. -/
theorem recInfo_stage {vis : Word} {fe : IFEnv} {a : AState}
    {m m1 : Mem} {cv mi rp isK reo rel q : Word} {cvv : IConstantVal} {rules : List IRecRule}
    (h1 : erAllocW m CI.recSize = some (q, m1))
    (hS : StageR vis fe m a) (hcv : decCV (erecP m) cv.toNat = some cvv)
    (hru : decRules (erecP m) reo.toNat rel.toNat = some rules) :
    StageR vis fe (recInfoMem m1 q cv mi rp isK reo rel) a ∧
      IWGrow m (recInfoMem m1 q cv mi rp isK reo rel) ∧
      decCI (erecP (recInfoMem m1 q cv mi rp isK reo rel)) q.toNat =
        some (.recInfo cvv mi.toNat rp.toNat (isK != 0) rules) := by
  obtain ⟨⟨w0, hw0, -⟩, -, ⟨w3, hw3, -⟩⟩ := decCV_words hcv
  obtain ⟨w1, w2, hw1, hw2, -⟩ := decCV_slice hcv
  have r := erRdOK m
  have hfr : ∀ x ∈ [cv, cv + CV.lpsOff, cv + CV.lpsLen, cv + CV.type], ∀ o : Word,
      o.toNat < CI.recSize.toNat → erTier x ≠ erTier (q + o) ∨ erOff x ≠ erOff (q + o) := by
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
  rw [recInfoMem_eq hfr, hr1, hr1, hr1, hr1]
  generalize hI : CI.recInfoImg 5 (erRd m cv) (erRd m (cv + CV.lpsOff)) (erRd m (cv + CV.lpsLen))
    (erRd m (cv + CV.type)) mi rp reo rel isK = I
  have hIl : I.length = CI.recSize.toNat := by rw [← hI, CI.recInfoImg_length]
  obtain ⟨hS', hg, -, -, -, -, hget⟩ := erRecO_stage h1 hS I hIl.symm
  refine ⟨hS', hg, ?_⟩
  generalize wrERo m1 q I = M at hS' hg hget
  have g := fun {o : Word} {x : Word} (e : I[o.toNat]? = some (some x)) => hget o.toNat x e
  obtain ⟨en, enl, hsl, -, et, etl⟩ := decCV_rd r hcv
  have adj : ∀ f : Word, f.toNat ≤ 64 →
      q.toNat + (CI.cv + f).toNat = q.toNat + CI.cv.toNat + f.toNat := fun f hf => by
    rw [CI.cv_add_toNat hf, Nat.add_assoc]
  have hw : CVRecW (erecP M) (q.toNat + CI.cv.toNat) (erRd m cv) (erRd m (cv + CV.lpsOff))
      (erRd m (cv + CV.lpsLen)) (erRd m (cv + CV.type)) :=
    ⟨by rw [← adj _ CV.name_le]; exact g (hI ▸ CI.recInfoImg_name ..),
      by rw [← adj _ CV.lpsOff_le]; exact g (hI ▸ CI.recInfoImg_lo ..),
      by rw [← adj _ CV.lpsLen_le]; exact g (hI ▸ CI.recInfoImg_ll ..),
      by rw [← adj _ CV.type_le]; exact g (hI ▸ CI.recInfoImg_ty ..)⟩
  have hcv' : decCV (erecP M) (q.toNat + CI.cv.toNat) = some cvv := by
    rw [decCV_of_words hw enl etl (ArrExt.hslice? (IWGrow.ext hg) hsl), ← en, ← et]
  have n0 := g (o := CI.kind) (hI ▸ CI.recInfoImg_kind ..)
  rw [show CI.kind.toNat = 0 from rfl, Nat.add_zero] at n0
  refine decCI_recInfo_iff.mpr ⟨by simp [nat?, n0], hcv',
    by simp [nat?, g (hI ▸ CI.recInfoImg_major ..)], by simp [nat?, g (hI ▸ CI.recInfoImg_prefix ..)],
    by simp [bool?, g (hI ▸ CI.recInfoImg_isK ..)], reo.toNat, rel.toNat,
    by simp [nat?, g (hI ▸ CI.recInfoImg_rulesOff ..)], by simp [nat?, g (hI ▸ CI.recInfoImg_rulesLen ..)],
    (IWGrow.ext hg).decRules hru⟩

end L.Ind
