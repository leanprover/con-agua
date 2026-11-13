module

public import ConAgua.Front.IndInstallRefine
public import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Arena.RecLayout.CapsDec
import ConAgua.Front.IndApplyRefine
import ConAgua.Front.IndApplyRefine2
import ConAgua.L.WordOff

@[expose] public section

/-!
# `install_ind_d` refines `installIndD`, II: the type and constructor records

`typeW_twin`, `ctorRW_twin`: `ind_type`/`ind_ctor` allocate a record above `DLP`'s top and write
it; it decodes (`decCI`) as the twin's `indInfo`/`ctorInfo` constant in any pool that agrees with
the memory from the record on (`RecAt`).
-/

open L.Arena
open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend (IndCtorRec IndTypeRec IndRecRec CVRec RuleRec)
open ConAgua.Front.FieldsLink
open L.Front.Fields (listN itemsN)


namespace L.Front.Ind

/-- The value of a twin computation that runs `.ok` (else `default`). -/
def resOf {α : Type} [Inhabited α] (x : AM α) (a : AState) : α :=
  match x.run a with
  | .ok (c, _) => c
  | .error _ => default

theorem resOf_eq {α : Type} [Inhabited α] {x : AM α} {a a' : AState} {c : α}
    (h : x.run a = .ok (c, a')) : resOf x a = c := by
  simp [resOf, h]

/-- **The constant record at `q`** decodes as `ci` in every pool that holds `m`'s words from `q`
to the top. -/
def RecAt (m : Mem) (q : Nat) (ci : IConstantInfo) : Prop :=
  ∀ P, AgreesFrom P m q → decCI (aread P) q = some ci

theorem RecAt.keep {m m' : Mem} {q : Nat} {ci : IConstantInfo} (h : RecAt m q ci)
    (ht : topN m DLP ≤ topN m' DLP) (hk : ∀ i, q ≤ i → i ≤ topN m DLP → wd m' DLP i = wd m DLP i) :
    RecAt m' q ci :=
  fun P hP => h P (fun i h1 h2 => by rw [hP i h1 (Nat.le_trans h2 ht), hk i h1 h2])

theorem range_map_eq {α β : Type} (l : List α) (f : Nat → β) (g : α → β)
    (h : ∀ j (hj : j < l.length), f j = g l[j]) : (List.range l.length).map f = l.map g := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range]; exact h j h1

/-- A pool agreeing with `m` from `q` holds word `i` (in range). -/
theorem AgreesFrom.get {P : Array Word} {m : Mem} {q : Nat} (h : AgreesFrom P m q) {i : Nat}
    (h1 : q ≤ i) (h2 : i ≤ topN m DLP) : P[i]? = some (wd m DLP i) := h i h1 h2

/-! ## The capabilities -/

theorem capsM_frame (m : Mem) (q : Word) : MemFrame [DLP] [] m (capsM m q) := by
  unfold capsM
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  exact MemFrame.set64 _ DLP (by decide) _ _

theorem capsM_size (m : Mem) (q : Word) : ((capsM m q).arr64 DLP).size = (m.arr64 DLP).size :=
  (capsM_frame m q).size DLP

/-- `ind_caps`' words decode as the default capabilities. -/
theorem capsM_dec (m : Mem) (q : Word) (hs : q.toNat + Caps.size.toNat ≤ (m.arr64 DLP).size)
    (hq : q.toNat + Caps.size.toNat < 2 ^ 64) (P : Array Word)
    (h : ∀ k, k < Caps.size.toNat → P[q.toNat + k]? = some (wd (capsM m q) DLP (q.toNat + k))) :
    decCaps (aread P) q.toNat = some {} := by
  have hw0 : CapsRecW (aread ((capsM m q).arr64 DLP)) q.toNat 0 0 0 0 0 0 0 0 :=
    capsRecW_set64 (m := m) (A := DLP) hs hq
  have hw := hw0.shift (b := aread P) (e := q.toNat) (fun j hj => by
    have hj' : q.toNat + j < ((capsM m q).arr64 DLP).size := by rw [capsM_size]; omega
    simp only [aread_apply, h j hj, wd, Array.getElem?_eq_getElem hj', Option.getD_some])
  rw [decCaps_of_words hw (xs := []) (ys := []) (by simp [hslice?]) (by simp [hslice?])]
  rfl

/-- `ind_caps` writes only its record's words. -/
theorem capsM_out (m : Mem) (q : Word) (hq : q.toNat + Caps.size.toNat < 2 ^ 64) (j : Nat)
    (hj : j < q.toNat ∨ q.toNat + Caps.size.toNat ≤ j) : wd (capsM m q) DLP j = wd m DLP j := by
  have e : ∀ f : Word, f.toNat < Caps.size.toNat → (q + f).toNat ≠ j := fun f hf => by
    rw [UInt64.toNat_add]; omega
  unfold capsM
  rw [wd_set_ne _ _ _ _ _ (e _ Caps.ctorsLen_lt), wd_set_ne _ _ _ _ _ (e _ Caps.ctorsOff_lt),
    wd_set_ne _ _ _ _ _ (e _ Caps.nparams_lt), wd_set_ne _ _ _ _ _ (e _ Caps.allLen_lt),
    wd_set_ne _ _ _ _ _ (e _ Caps.allOff_lt), wd_set_ne _ _ _ _ _ (e _ Caps.neverZero_lt),
    wd_set_ne _ _ _ _ _ (e _ Caps.nIdx_lt), wd_set_ne _ _ _ _ _ (e _ Caps.eta_lt)]

/-! ## The type and constructor records -/

/-- **An `indInfo` record's layout**: the kind word, the constant value, the capabilities. -/
theorem ind_layout : 0 < CI.cv.toNat ∧ CI.cv.toNat + CV.size.toNat ≤ CI.indCaps.toNat ∧
    CI.indSize.toNat = CI.indCaps.toNat + Caps.size.toNat ∧ CI.indSize.toNat ≤ 128 :=
  ⟨CI.cv_pos, by simp [CI.cv, CV.size, CI.indCaps], CI.indSize_toNat,
    by simp [CI.indSize, CI.indCaps, Caps.size]⟩

/-- **A `ctorInfo` record's layout**: the kind word, the constant value, the three fields in
order. -/
theorem ctor_layout : 0 < CI.cv.toNat ∧ CI.cv.toNat + CV.size.toNat ≤ CI.ctorNparams.toNat ∧
    CI.ctorNparams.toNat < CI.ctorNfields.toNat ∧ CI.ctorNfields.toNat < CI.ctorInduct.toNat ∧
    CI.ctorInduct.toNat < CI.ctorSize.toNat ∧ CI.ctorSize.toNat ≤ 128 := by
  simp [CI.cv, CV.size, CI.ctorNparams, CI.ctorNfields, CI.ctorInduct, CI.ctorSize]

/-- The twin's constant of a type record (`installIndD`'s `types`). -/
def tyT (st : StateD) (t : IndTypeRec) : AM IConstantInfo := do
  pure (IConstantInfo.indInfo (← parseCVD st t.cv) {})

/-- The twin's constant of a constructor record (`installIndD`'s `ctors`). -/
def ctT (st : StateD) (c : IndCtorRec) (T : NIdx) : AM IConstantInfo := do
  pure (IConstantInfo.ctorInfo (← parseCVD st c.cv) c.numParams c.numFields T)

theorem rdW_wdI (m : Mem) (A : ArrId) (t w : Word) (h : t.toNat + w.toNat < 2 ^ 64) :
    rdW (m.arr64 A) (t + w) = wd m A (t.toNat + w.toNat) := by
  simp only [rdW, wd, L.toNat_add_of_lt t w h]

/-- **`ind_type` against the twin's type constant.** -/
theorem typeW_twin {b : ByteArray} {m m' : Mem} {st : StateD} (a : AState) (hD : LkR m st)
    {t q : Word} {ty : IndTypeRec} (hF : CVF b m t.toNat ty.cv) (ht : t.toNat + 3 < 2 ^ 63)
    (h : typeW b.data m t = some (q, m')) :
    (tyT st ty).run a = .ok (resOf (tyT st ty) a, a) ∧ PExt m m' ∧ q.toNat = topN m DLP + 1 ∧
      LkR m' st ∧ RecAt m' q.toNat (resOf (tyT st ty) a) := by
  have hps := hD.psize
  have hpt := hD.ptop
  rw [typeW.arm1] at h
  rcases h1 : allocW m DLP CI.indSize with _ | ⟨q1, m₁⟩ <;> rw [h1] at h
  · rw [typeW.k_dind_alloc.none] at h; cases h
  rw [typeW.k_dind_alloc.arm1] at h
  simp only [DIND, Mem.arr64_set64_ne _ _ _ _ _ (show (IFR : TieredArray) ≠ DLP by decide)] at h
  obtain ⟨P1, P2, P3, P4, P5⟩ := allocP_facts hD.psize hD.ptop h1
  obtain ⟨l1, l2, l3, l4⟩ := ind_layout
  have := CV.size_pos; have := Caps.size_pos
  have hifr : m₁.arr64 IFR = m.arr64 IFR := P1.other IFR (by decide) (by decide)
  have hsm1 : (m₁.arr64 DLP).size = (m.arr64 DLP).size := P1.size DLP
  cases h2 : cvW b.data (m₁.set64 DLP q1 3) (q1 + CI.cv) (rdW (m₁.arr64 IFR) t) (rdW (m₁.arr64 IFR) (t + 1))
      (rdW (m₁.arr64 IFR) (t + 2)) with
  | none => rw [h2, typeW.k_ind_cv.none] at h; cases h
  | some m₂ =>
  rw [h2, typeW.k_ind_cv.arm1, capsW_eq, typeW.k_ind_caps.arm1] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have Pq : PExt m (m₁.set64 DLP q1 3) := P1.set q1 3 (by omega) (by omega)
  have hs1 : ((m₁.set64 DLP q1 3).arr64 DLP).size = (m.arr64 DLP).size := Pq.size DLP
  have ht1 : topN (m₁.set64 DLP q1 3) DLP = topN m DLP + CI.indSize.toNat := by
    rw [← P3]; unfold topN; rw [wd_set_ne _ _ _ _ _ (by omega)]
  have hL1 : LkR (m₁.set64 DLP q1 3) st := hD.frame Pq.frame (by rw [ht1, hs1]; omega)
  obtain ⟨n0, l0, y0⟩ := hF
  have r0 : rdW (m₁.arr64 IFR) t = wd m IFR t.toNat := by rw [hifr]; rfl
  have r1 : rdW (m₁.arr64 IFR) (t + 1) = wd m IFR (t.toNat + 1) := by
    rw [hifr, rdW_wdI _ _ _ _ (by simp; omega)]; rfl
  have r2 : rdW (m₁.arr64 IFR) (t + 2) = wd m IFR (t.toNat + 2) := by
    rw [hifr, rdW_wdI _ _ _ _ (by simp; omega)]; rfl
  rw [r0, r1, r2] at h2
  have hq1 : (q1 + CI.cv).toNat = q1.toNat + CI.cv.toNat := L.toNat_add_of_lt _ _ (by omega)
  obtain ⟨cvp, C1, C2, C3, C3', C4, C5, C6⟩ :=
    cvW_facts a hL1 n0.1 y0.1 l0 (by omega) (by rw [hq1, ht1]; omega) h2
  have hrun : (tyT st ty).run a = .ok (.indInfo cvp {}, a) := by
    unfold tyT; rw [run_bind _ _ a _ C1]; rfl
  rw [resOf_eq hrun]
  have hs2 : (m₂.arr64 DLP).size = (m.arr64 DLP).size := by rw [C2.size DLP, hs1]
  have ht2 : topN m₂ DLP = topN m DLP + CI.indSize.toNat + ty.cv.levelParams.length := by rw [C3, ht1]
  have hq5 : (q1 + CI.indCaps).toNat = q1.toNat + CI.indCaps.toNat := L.toNat_add_of_lt _ _ (by simp; omega)
  have hc0 : ∀ i, (i < q1.toNat + CI.indCaps.toNat ∨ q1.toNat + CI.indSize.toNat ≤ i) → wd (capsM m₂ (q1 + CI.indCaps)) DLP i = wd m₂ DLP i :=
    fun i hi => capsM_out _ _ (by omega) i (by omega)
  have ht3 : topN (capsM m₂ (q1 + CI.indCaps)) DLP = topN m₂ DLP := by
    unfold topN; rw [hc0 0 (by omega)]
  refine ⟨hrun, ⟨Pq.frame.trans (C2.trans (capsM_frame _ _)), by rw [ht3, ht2]; omega,
    fun i h1 h2 => ?_⟩, P2, ?_, ?_⟩
  · rw [hc0 i (by omega), C4 i h1 (by omega), Pq.keep i h1 h2]
  · exact hD.frame (Pq.frame.trans (C2.trans (capsM_frame _ _)))
      (by rw [ht3, capsM_size]; exact C3')
  · intro P hP
    have g0 : P[q1.toNat]? = some 3 := by
      rw [hP.get (Nat.le_refl _) (by rw [ht3, ht2]; omega), hc0 _ (by omega),
        C4 _ (by omega) (by omega), wd_set_eq _ _ _ _ _ rfl (by omega)]
    have gcv : decCV (L.Arena.aread P) (q1.toNat + CI.cv.toNat) = some cvp := by
      rw [← hq1]
      exact C6 (L.Arena.aread P) (fun i hi => by
        rw [L.Arena.aread_apply, hP.get (by omega) (by rw [ht3, ht2]; omega), hc0 i (by omega)])
    have gcaps : decCaps (L.Arena.aread P) (q1.toNat + CI.indCaps.toNat) = some {} := by
      rw [← hq5]
      exact capsM_dec m₂ (q1 + CI.indCaps) (by rw [hs2]; omega) (by omega) P
        (fun k hk => hP.get (by omega) (by rw [ht3, ht2]; omega))
    exact decCI_indInfo_iff.mpr ⟨by simp [nat?, g0], gcv, gcaps⟩


/-- **`ind_ctor` against the twin's constructor constant.** -/
theorem ctorRW_twin {b : ByteArray} {m m' : Mem} {st : StateD} (a : AState) (hD : LkR m st)
    {c tt q : Word} {ct : IndCtorRec} (hF : CtF b m c.toNat ct) (hc : c.toNat + 6 < 2 ^ 63)
    (htt : tt.toNat < 2 ^ 32) (h : ctorRW b.data m c tt = some (q, m')) :
    (ctT st ct (decI tt)).run a = .ok (resOf (ctT st ct (decI tt)) a, a) ∧ PExt m m' ∧
      q.toNat = topN m DLP + 1 ∧ LkR m' st ∧ RecAt m' q.toNat (resOf (ctT st ct (decI tt)) a) := by
  have hps := hD.psize
  have hpt := hD.ptop
  rw [ctorRW.arm1] at h
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := ctor_layout
  have := CV.size_pos
  rcases h1 : allocW m DLP CI.ctorSize with _ | ⟨q1, m₁⟩ <;> rw [h1] at h
  · rw [ctorRW.k_dind_alloc.none] at h; cases h
  rw [ctorRW.k_dind_alloc.arm1] at h
  simp only [DIND, Mem.arr64_set64_ne _ _ _ _ _ (show (IFR : TieredArray) ≠ DLP by decide)] at h
  obtain ⟨P1, P2, P3, P4, P5⟩ := allocP_facts hD.psize hD.ptop h1
  have hifr : m₁.arr64 IFR = m.arr64 IFR := P1.other IFR (by decide) (by decide)
  have hsm1 : (m₁.arr64 DLP).size = (m.arr64 DLP).size := P1.size DLP
  cases h2 : cvW b.data (m₁.set64 DLP q1 4) (q1 + CI.cv) (rdW (m₁.arr64 IFR) c) (rdW (m₁.arr64 IFR) (c + 1))
      (rdW (m₁.arr64 IFR) (c + 2)) with
  | none => rw [h2, ctorRW.k_ind_cv.none] at h; cases h
  | some m₂ =>
  rw [h2, ctorRW.k_ind_cv.arm1] at h
  simp only [DIND, Mem.arr64_set64_ne _ _ _ _ _ (show (IFR : TieredArray) ≠ DLP by decide), Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have Pq : PExt m (m₁.set64 DLP q1 4) := P1.set q1 4 (by omega) (by omega)
  have hs1 : ((m₁.set64 DLP q1 4).arr64 DLP).size = (m.arr64 DLP).size := Pq.size DLP
  have ht1 : topN (m₁.set64 DLP q1 4) DLP = topN m DLP + CI.ctorSize.toNat := by
    rw [← P3]; unfold topN; rw [wd_set_ne _ _ _ _ _ (by omega)]
  have hL1 : LkR (m₁.set64 DLP q1 4) st := hD.frame Pq.frame (by rw [ht1, hs1]; omega)
  obtain ⟨⟨n0, l0, y0⟩, f0, p0, -, -⟩ := hF
  have r0 : rdW (m₁.arr64 IFR) c = wd m IFR c.toNat := by rw [hifr]; rfl
  have r1 : rdW (m₁.arr64 IFR) (c + 1) = wd m IFR (c.toNat + 1) := by
    rw [hifr, rdW_wdI _ _ _ _ (by simp; omega)]; rfl
  have r2 : rdW (m₁.arr64 IFR) (c + 2) = wd m IFR (c.toNat + 2) := by
    rw [hifr, rdW_wdI _ _ _ _ (by simp; omega)]; rfl
  rw [r0, r1, r2] at h2
  have hq1 : (q1 + CI.cv).toNat = q1.toNat + CI.cv.toNat := L.toNat_add_of_lt _ _ (by omega)
  obtain ⟨cvp, C1, C2, C3, C3', C4, C5, C6⟩ :=
    cvW_facts a hL1 n0.1 y0.1 l0 (by omega) (by rw [hq1, ht1]; omega) h2
  have hrun : (ctT st ct (decI tt)).run a = .ok (.ctorInfo cvp ct.numParams ct.numFields (decI tt), a) := by
    unfold ctT; rw [run_bind _ _ a _ C1]; rfl
  rw [resOf_eq hrun]
  have hs2 : (m₂.arr64 DLP).size = (m.arr64 DLP).size := by rw [C2.size DLP, hs1]
  have ht2 : topN m₂ DLP = topN m DLP + CI.ctorSize.toNat + ct.cv.levelParams.length := by rw [C3, ht1]
  have hifr2 : m₂.arr64 IFR = m.arr64 IFR := by rw [C2.1 IFR (by decide) (by decide), Pq.other IFR (by decide) (by decide)]
  have hq5 : (q1 + CI.ctorNparams).toNat = q1.toNat + CI.ctorNparams.toNat := L.toNat_add_of_lt _ _ (by omega)
  have hq6 : (q1 + CI.ctorNfields).toNat = q1.toNat + CI.ctorNfields.toNat := L.toNat_add_of_lt _ _ (by omega)
  have hq7 : (q1 + CI.ctorInduct).toNat = q1.toNat + CI.ctorInduct.toNat := L.toNat_add_of_lt _ _ (by omega)
  have w5 : rdW (m₂.arr64 IFR) (c + 5) = wd m IFR (c.toNat + 5) := by
    rw [hifr2, rdW_wdI _ _ _ _ (by simp; omega)]; rfl
  have w4 : rdW (m₂.arr64 IFR) (c + 4) = wd m IFR (c.toNat + 4) := by
    rw [hifr2, rdW_wdI _ _ _ _ (by simp; omega)]; rfl
  rw [w5, w4]
  have hc0 : ∀ i, (i < q1.toNat + CI.ctorNparams.toNat ∨ q1.toNat + CI.ctorSize.toNat ≤ i) →
      wd (((m₂.set64 DLP (q1 + CI.ctorNparams) (wd m IFR (c.toNat + 5))).set64 DLP (q1 + CI.ctorNfields)
        (wd m IFR (c.toNat + 4))).set64 DLP (q1 + CI.ctorInduct) tt) DLP i = wd m₂ DLP i := fun i hi => by
    rw [wd_set_ne _ _ _ _ _ (by omega), wd_set_ne _ _ _ _ _ (by omega), wd_set_ne _ _ _ _ _ (by omega)]
  have hsz : ((((m₂.set64 DLP (q1 + CI.ctorNparams) (wd m IFR (c.toNat + 5))).set64 DLP (q1 + CI.ctorNfields)
      (wd m IFR (c.toNat + 4))).set64 DLP (q1 + CI.ctorInduct) tt).arr64 DLP).size = (m.arr64 DLP).size := by
    simp only [L.Mem.size64_set64]; exact hs2
  have hfr : MemFrame [DLP] [] m₂ (((m₂.set64 DLP (q1 + CI.ctorNparams) (wd m IFR (c.toNat + 5))).set64 DLP
      (q1 + CI.ctorNfields) (wd m IFR (c.toNat + 4))).set64 DLP (q1 + CI.ctorInduct) tt) :=
    ((MemFrame.set64 _ DLP (by decide) _ _).trans (MemFrame.set64 _ DLP (by decide) _ _)).trans
      (MemFrame.set64 _ DLP (by decide) _ _)
  have ht3 : topN (((m₂.set64 DLP (q1 + CI.ctorNparams) (wd m IFR (c.toNat + 5))).set64 DLP
      (q1 + CI.ctorNfields) (wd m IFR (c.toNat + 4))).set64 DLP (q1 + CI.ctorInduct) tt) DLP = topN m₂ DLP := by
    unfold topN; rw [hc0 0 (by omega)]
  refine ⟨hrun, ⟨Pq.frame.trans (C2.trans hfr), by rw [ht3, ht2]; omega,
    fun i h1 h2 => ?_⟩, P2, ?_, ?_⟩
  · rw [hc0 i (by omega), C4 i h1 (by omega), Pq.keep i h1 h2]
  · exact hD.frame (Pq.frame.trans (C2.trans hfr)) (by rw [ht3, hsz, ← hs2]; exact C3')
  · intro P hP
    have g0 : P[q1.toNat]? = some 4 := by
      rw [hP.get (Nat.le_refl _) (by rw [ht3, ht2]; omega), hc0 _ (by omega),
        C4 _ (by omega) (by omega), wd_set_eq _ _ _ _ _ rfl (by omega)]
    have gcv : decCV (L.Arena.aread P) (q1.toNat + CI.cv.toNat) = some cvp := by
      rw [← hq1]
      exact C6 (L.Arena.aread P) (fun i hi => by
        rw [L.Arena.aread_apply, hP.get (by omega) (by rw [ht3, ht2]; omega), hc0 i (by omega)])
    have g5 : P[q1.toNat + CI.ctorNparams.toNat]? = some (wd m IFR (c.toNat + 5)) := by
      rw [hP.get (by omega) (by rw [ht3, ht2]; omega), wd_set_ne _ _ _ _ _ (by omega),
        wd_set_ne _ _ _ _ _ (by omega), wd_set_eq _ _ _ _ _ hq5 (by omega)]
    have g6 : P[q1.toNat + CI.ctorNfields.toNat]? = some (wd m IFR (c.toNat + 4)) := by
      rw [hP.get (by omega) (by rw [ht3, ht2]; omega), wd_set_ne _ _ _ _ _ (by omega),
        wd_set_eq _ _ _ _ _ hq6 (by simp only [L.Mem.size64_set64]; omega)]
    have g7 : P[q1.toNat + CI.ctorInduct.toNat]? = some tt := by
      rw [hP.get (by omega) (by rw [ht3, ht2]; omega),
        wd_set_eq _ _ _ _ _ hq7 (by simp only [L.Mem.size64_set64]; omega)]
    exact decCI_ctorInfo_iff.mpr ⟨by simp [nat?, g0], gcv, by simp [nat?, g5, p0.1],
      by simp [nat?, g6, f0.1], by simp [hd?, g7, htt]⟩


end L.Front.Ind
