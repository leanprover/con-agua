import ConAgua.Arena.IndCopy
import ConAgua.Arena.DerRel
import ConAgua.Arena.ExprMk

/-!
# The master callees of the inductive stage, under the stage relation (lane `indproofs`)

The stage calls master's expression constructors (`intern_bvar`, `intern_fvar`, `intern_sort`,
`intern_const`, `mk_app`, `mk_lam`, `mk_forall`, `mk_let`, `mk_proj`). Their L side is master's
word model and spec (`binternW`/`internBVar_spec`, `mkAppW`/`mkApp_spec`, …); this file gives the
twin side in the stage's shape, sorry-free: from `StageR` a model run is a successful
`internE` run, with `StageR` after (the writes are below array 64 and `CTL[64]`, the twin keeps
caches and pins: `StageR.of_walk`) and the pool only grown. A refinement through these callees
uses the master spec inside `vcgen` and the `_stage` lemma afterwards, as for a stub's `RelAM`.
-/

open ConRon.Arena

namespace L.Ind

open L.Arena

/-- The frame of a `mk_*` tail: the interning's, plus the derived-range array. -/
theorem mkK_frame {A : ArrId} (hA : A ≠ CTL) {c s d : Word} {x : Option (Word × Mem)} {m m' : Mem}
    {r : Word} {A₀ : List ArrId} {C₀ : List Word}
    (hx : ∀ r₁ m₁, x = some (r₁, m₁) → MemFrame A₀ C₀ m m₁) (h : mkK A c s d x = some (r, m')) :
    MemFrame (A :: A₀) C₀ m m' := by
  match x, hx, h with
  | some (r₁, m₁), hx, h =>
    rw [mkK_some] at h
    split at h
    · cases h
    · rename_i m₂ hP
      cases h
      exact ((hx _ _ rfl).mono (fun b hb => by simp [hb]) (by simp)).trans
        ((derPutW_frame A hA _ _ _ _ _ _ hP).mono (by simp) (by simp))

section
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m' : Mem} {a : AState}
  {r : Word}

/-- From the `AM.ok`/`ArenaD`/`AM.res` triple of a master `_ok`/`_D` lemma, a frame below 64
and `Keeps cp`: the stage relation after. -/
theorem stage_of_ok {op : AM EIdx} {A : List ArrId} {C : List Word} (hS : StageR dn vis fe m a)
    (hok : AM.ok op a) (hD : ArenaD m' (AM.st op a)) (hres : AM.res op a = decE r)
    (hf : MemFrame A C m m') (hA : ∀ b ∈ A, b < 64) (hC : ∀ x ∈ C, x.toNat < 64)
    (hk : Keeps cp op) :
    ∃ a', op.run a = .ok (decE r, a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' := by
  have hrun := AM.run_of_ok op a hok
  rw [hres] at hrun
  obtain ⟨h1, h2⟩ := StageR.of_walk hS hD hf hA hC (hk.run hrun)
  exact ⟨_, hrun, h1, h2⟩

theorem internBVar_stage (hS : StageR dn vis fe m a) (u : Word) (hI : binternW m u = some (r, m')) :
    ∃ a', (internE (.bvar u.toNat)).run a = .ok (decE r, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' := by
  obtain ⟨hok, hD, hres⟩ := internBVar_D m a hS.1.arena u r m' hI
  have hI₂ := hI; rw [binternW_eq] at hI₂
  exact stage_of_ok hS hok hD hres (internM_frame _ bvarSch_wf _ _ _ _ _ _ _ _ hI₂)
    (by simp [bvarSch, BREC, BSLOT]) (by simp [bvarSch]) (keeps_internE _)

theorem internFVar_stage (hS : StageR dn vis fe m a) (u ty : Word) (hty : ty.toNat < 2 ^ 32)
    (hI : fvinternW m u ty = some (r, m')) :
    ∃ a', (internE (.fvar u.toNat (decE ty))).run a = .ok (decE r, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' := by
  obtain ⟨hok, hD, hres⟩ := internFVar_D m a hS.1.arena u ty r hty m' hI
  have hI₂ := hI; rw [fvinternW_eq] at hI₂
  exact stage_of_ok hS hok hD hres (internM_frame _ fvarSch_wf _ _ _ _ _ _ _ _ hI₂)
    (by simp [fvarSch, FVREC, FVSLOT]) (by simp [fvarSch]) (keeps_internE _)

theorem internSort_stage (hS : StageR dn vis fe m a) (u : Word) (hu : u.toNat < 2 ^ 32)
    (hI : sointernW m u = some (r, m')) :
    ∃ a', (internE (.sort (decI u))).run a = .ok (decE r, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' := by
  obtain ⟨hok, hD, hres⟩ := internSort_D m a hS.1.arena u r hu m' hI
  have hI₂ := hI; rw [sointernW_eq] at hI₂
  exact stage_of_ok hS hok hD hres (internM_frame _ sortSch_wf _ _ _ _ _ _ _ _ hI₂)
    (by simp [sortSch, SOREC, SOSLOT]) (by simp [sortSch]) (keeps_internE _)

theorem internConst_stage (hS : StageR dn vis fe m a) (f x : Word) (hf : f.toNat < 2 ^ 32)
    (hx : x.toNat < 2 ^ 32) (hI : ceinternW m f x = some (r, m')) :
    ∃ a', (internE (.const (decI (k := .name) f) (decI (k := .levels) x))).run a = .ok (decE r, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' := by
  obtain ⟨hok, hD, hres⟩ := internConst_D m a hS.1.arena f x r hf hx m' hI
  have hI₂ := hI; rw [ceinternW_eq] at hI₂
  exact stage_of_ok hS hok hD hres (internM_frame _ constSch_wf _ _ _ _ _ _ _ _ hI₂)
    (by simp [constSch, CREC, CSLOT]) (by simp [constSch]) (keeps_internE _)

theorem mkApp_stage (hS : StageR dn vis fe m a) (f x : Word) (hI : mkAppW m f x = some (r, m')) :
    ∃ a', (internE (.app (decE f) (decE x))).run a = .ok (decE r, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' := by
  obtain ⟨hok, hD, hres⟩ := mkApp_ok m a hS.1.arena f x r m' hI
  have hf : MemFrame [ADER, AREC, ASLOT] [4, 5] m m' := by
    unfold mkAppW at hI; split at hI; · cases hI
    exact mkK_frame (by decide) (fun r₁ m₁ hx => by
      rw [ainternW_eq] at hx; exact internM_frame _ appSch_wf _ _ _ _ _ _ _ _ hx) hI
  exact stage_of_ok hS hok hD hres hf (by simp [ADER, AREC, ASLOT]) (by simp) (keeps_internE _)

theorem mkLam_stage (hS : StageR dn vis fe m a) (t b : Word) (hI : mkLamW m t b = some (r, m')) :
    ∃ a', (internE (.lam (decE t) (decE b))).run a = .ok (decE r, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' := by
  obtain ⟨hok, hD, hres⟩ := mkLam_ok m a hS.1.arena t b r m' hI
  have hf : MemFrame [LADER, LAREC, LASLOT] [28, 29] m m' := by
    unfold mkLamW at hI; split at hI; · cases hI
    exact mkK_frame (by decide) (fun r₁ m₁ hx => by
      rw [lainternW_eq] at hx; exact internM_frame _ lamSch_wf _ _ _ _ _ _ _ _ hx) hI
  exact stage_of_ok hS hok hD hres hf (by simp [LADER, LAREC, LASLOT]) (by simp) (keeps_internE _)

theorem mkForall_stage (hS : StageR dn vis fe m a) (t b : Word) (hI : mkForallW m t b = some (r, m')) :
    ∃ a', (internE (.forallE (decE t) (decE b))).run a = .ok (decE r, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' := by
  obtain ⟨hok, hD, hres⟩ := mkForall_ok m a hS.1.arena t b r m' hI
  have hf : MemFrame [FADER, FAREC, FASLOT] [30, 31] m m' := by
    unfold mkForallW at hI; split at hI; · cases hI
    exact mkK_frame (by decide) (fun r₁ m₁ hx => by
      rw [fainternW_eq] at hx; exact internM_frame _ forallSch_wf _ _ _ _ _ _ _ _ hx) hI
  exact stage_of_ok hS hok hD hres hf (by simp [FADER, FAREC, FASLOT]) (by simp) (keeps_internE _)

theorem mkLet_stage (hS : StageR dn vis fe m a) (t v b : Word) (hI : mkLetW m t v b = some (r, m')) :
    ∃ a', (internE (.letE (decE t) (decE v) (decE b))).run a = .ok (decE r, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' := by
  obtain ⟨hok, hD, hres⟩ := mkLet_ok m a hS.1.arena t v b r m' hI
  have hf : MemFrame [LEDER, LEREC, LESLOT] [20, 21] m m' := by
    unfold mkLetW at hI; split at hI; · cases hI
    exact mkK_frame (by decide) (fun r₁ m₁ hx => by
      rw [leinternW_eq] at hx; exact internM_frame _ letSch_wf _ _ _ _ _ _ _ _ hx) hI
  exact stage_of_ok hS hok hD hres hf (by simp [LEDER, LEREC, LESLOT]) (by simp) (keeps_internE _)

theorem mkProj_stage (hS : StageR dn vis fe m a) (n i e : Word) (hI : mkProjW m n i e = some (r, m')) :
    ∃ a', (internE (.proj (decI n) i.toNat (decE e))).run a = .ok (decE r, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' := by
  obtain ⟨hok, hD, hres⟩ := mkProj_ok m a hS.1.arena n i e r m' hI
  have hf : MemFrame [PJDER, PJREC, PJSLOT] [32, 33] m m' := by
    unfold mkProjW at hI; split at hI; · cases hI
    exact mkK_frame (by decide) (fun r₁ m₁ hx => by
      rw [pjinternW_eq] at hx; exact internM_frame _ projSch_wf _ _ _ _ _ _ _ _ hx) hI
  exact stage_of_ok hS hok hD hres hf (by simp [PJDER, PJREC, PJSLOT]) (by simp) (keeps_internE _)

end

/-! ## The pool's `sl_cons` under the stage relation -/

/-- The pool's top after a `sl_cons` stays within the array. -/
theorem consW_room {n : Nat} {m m' : Mem} {x o l : Word} {r : List Word}
    (h : consW n m x o l = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hsrc : o.toNat + l.toNat ≤ iwTop m)
    (hx : x.toNat < 2 ^ 32) {xs : List EIdx} (hxs : decHL m o.toNat l.toNat = some xs) :
    iwTop m' ≤ (m'.arr64 IW).size := by
  obtain ⟨-, -, -, hf, -, ht⟩ := consW_dec h hsz hc hsrc hx hxs
  rw [← ht, hf.2.2.1 IW]
  simp only [consW] at h
  by_cases h0 : l + 1 = 0
  · simp [h0] at h
  simp only [h0, if_false] at h
  simp only [allocW] at h
  by_cases h1 : m.len64 IW < rdW (m.arr64 CTL) 200
  · simp [h1] at h
  by_cases h2 : m.len64 IW - rdW (m.arr64 CTL) 200 < l + 1
  · simp [h1, h2] at h
  have hlen : (m.len64 IW).toNat = (m.arr64 IW).size := by simp [Mem.len64]; omega
  have : ¬ (m.len64 IW).toNat < (rdW (m.arr64 CTL) 200).toNat := h1
  have h2' : ¬ (m.len64 IW - rdW (m.arr64 CTL) 200).toNat < (l + 1).toNat := h2
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)] at h2'
  omega

/-- **`sl_cons` keeps the stage relation**: the pool grew by the new slice, which decodes to
`x :: xs`. -/
theorem consW_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {x o l : Word} {r : List Word} {xs : List EIdx}
    (h : consW n m x o l = some (r, m')) (hS : StageR dn vis fe m a)
    (hsrc : o.toNat + l.toNat ≤ iwTop m) (hx : x.toNat < 2 ^ 32)
    (hxs : decHL m o.toNat l.toNat = some xs) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some (decI x :: xs) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
  obtain ⟨hI1, hE1, hsz, hEs, hc⟩ := hS.2
  obtain ⟨hr, hd, hg, hf, -, ht⟩ := consW_dec h hsz hc hsrc hx hxs
  have hroom := consW_room h hsz hc hsrc hx hxs
  have h129 : rdW (m'.arr64 CTL) 129 = rdW (m.arr64 CTL) 129 := hf.2.1 129 (by simp)
  have hE : m'.arr64 EREC = m.arr64 EREC := hf.1 EREC (by simp [EREC, IW]) (by decide)
  subst hr
  refine ⟨⟨CheckR.frame_iw hf hS.1, hroom, ?_, ?_, ?_, ?_⟩, hg, by simpa using hd, by simpa using ht⟩
  · simp only [erTop, h129, hE]; exact hE1
  · rw [hf.2.2.1 IW]; exact hsz
  · rw [hE]; exact hEs
  · rw [hf.2.2.1 CTL]; exact hc

end L.Ind
