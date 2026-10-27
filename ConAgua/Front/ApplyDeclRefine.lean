import ConAgua.Front.ApplyExprRefine
import ConAgua.Front.DeclIface
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# `apply_decl` refines con-ron's `processLineCoreD`

`applyDeclW_refines`: if `apply_decl`'s model succeeds on fields `f` that con-leche's scanner
relates to the declaration record `d` (`DeclR`, `DeclIface.lean`), then con-ron's
`applyLine st (.decl d)` is `pure (.inl st')` (no interning, no verdict), the memory after is
related to the same arena state by `ArenaD` and to `st'` by `StateDR`: the record is appended to
`DECL`, its universe parameter names to `DLP` (`DeclsF`, `StateDR.lean`).
-/

open Std.WP
open scoped Lean.Order
open L.Arena
open ConRon.Arena ConLeche
open ConRon.Arena.Frontend
open ConLeche.Frontend
open L.Front.Fields (rdNatN NONE itemsN listN DFld itemsN_end itemsN_close itemsN_digit
  itemsN_noprog itemsN_other)
open ConAgua.Front.FieldsLink
open L.Scan.Leaves (numEndN)


namespace L.Front

/-! ## Array writes -/

theorem arr_set64 (m : Mem) (a : ArrId) (i v : Word) (j : Nat) :
    ((m.set64 a i v).arr64 a)[j]? =
      if i.toNat = j ∧ j < (m.arr64 a).size then some v else (m.arr64 a)[j]? := by
  rw [Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases h : i.toNat = j
  · subst h
    by_cases h2 : i.toNat < (m.arr64 a).size
    · simp [h2]
    · simp [h2]
  · simp [h]

theorem MemFrame.set64' {A : List ArrId} {C : List Word} {m m₁ : Mem} (h : MemFrame A C m m₁)
    (a : ArrId) (ha : a ≠ CTL) (hA : a ∈ A) (i v : Word) : MemFrame A C m (m₁.set64 a i v) :=
  h.trans ((MemFrame.set64 m₁ a ha i v).mono (by simpa using hA) (by simp))

/-! ## `lp_put`'s copy loop -/

/-- The end of `lp_put`'s loop: the top word written. -/
theorem lp_fin (m : Mem) (top cnt : Word) (hr : 1 + top.toNat + cnt.toNat ≤ (m.arr64 DLP).size) :
    MemFrame [DLP] [] m (m.set64 DLP 0 (top + cnt)) ∧
    (∀ j, 0 < j → ((m.set64 DLP 0 (top + cnt)).arr64 DLP)[j]? = (m.arr64 DLP)[j]?) ∧
    ((m.set64 DLP 0 (top + cnt)).arr64 DLP)[0]? = some (top + cnt) := by
  refine ⟨MemFrame.set64 _ _ (by decide) _ _, fun j hj => ?_, ?_⟩
  · rw [arr_set64, ite_eq_right (fun h => by simp at h; omega)]
  · rw [arr_set64, ite_eq_left ⟨by simp, by omega⟩]

theorem lpLoopM_facts (b : Array UInt8) (top : Word) : ∀ (m : Mem) (i cnt : Word) (m' : Mem),
    lpLoopM b m top i cnt = some m' →
    1 + top.toNat + cnt.toNat ≤ (m.arr64 DLP).size → (m.arr64 DLP).size < 2 ^ 63 →
    (lsCntN b i cnt).toNat = cnt.toNat + (itemsN b i).length ∧
    MemFrame [DLP] [] m m' ∧
    1 + top.toNat + (lsCntN b i cnt).toNat ≤ (m.arr64 DLP).size ∧
    (∀ j, 0 < j → j < 1 + top.toNat + cnt.toNat → (m'.arr64 DLP)[j]? = (m.arr64 DLP)[j]?) ∧
    (∀ k (hk : k < (itemsN b i).length),
      (m'.arr64 DLP)[1 + top.toNat + cnt.toNat + k]? = some (tblW m NID (itemsN b i)[k])) ∧
    (∀ x ∈ itemsN b i, tblOK m NID x = true) ∧
    (m'.arr64 DLP)[0]? = some (top + lsCntN b i cnt) := by
  intro m i cnt
  fun_induction lpLoopM b m top i cnt with
  | case1 m i cnt h1 h2 =>
    intro m' h hr hs
    cases h
    obtain ⟨f1, f3, f4⟩ := lp_fin m top cnt hr
    rw [lsCntN_close _ _ _ h1 h2, itemsN_close _ _ h1 h2]
    exact ⟨by simp, f1, hr, fun j hj _ => f3 j hj, fun k hk => by simp at hk, by simp, f4⟩
  | case2 m i cnt h1 h2 h3 h4 h5 => intro m' h; cases h
  | case3 m i cnt h1 h2 h3 h4 h5 h6 ih =>
    intro m' h hr hs
    obtain ⟨hok, hlt⟩ := h6
    have hlen : (m.len64 DLP).toNat = (m.arr64 DLP).size := by
      simp only [Mem.len64]; exact toNat_ofNat_size _ hs
    have htc : (1 + top + cnt).toNat = 1 + top.toNat + cnt.toNat := by
      rw [UInt64.toNat_add, UInt64.toNat_add]; simp; omega
    have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
    rw [hlen, htc] at hlt'
    have hc1 : (cnt + 1).toNat = cnt.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hP : ∀ B, B ≠ DLP →
        (m.set64 DLP (1 + top + cnt) (tblW m NID (rdNatN b i (UInt64.ofNat (numEndN b i.toNat))))).arr64 B =
          m.arr64 B := fun B hB => Mem.arr64_set64_ne _ _ _ _ _ hB
    obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := ih m' h
      (by rw [size_set64, hc1]; omega) (by rw [size_set64]; exact hs)
    rw [lsCntN_digit _ _ _ h1 h2 h3 h4, itemsN_digit _ _ h1 h2 h3 h4]
    rw [size_set64] at i3
    refine ⟨by rw [i1, hc1]; simp; omega, (MemFrame.set64 _ _ (by decide) _ _).trans i2, i3,
      fun j hj0 hj => ?_, fun k hk => ?_, ?_, i7⟩
    · rw [i4 j hj0 (by rw [hc1]; omega), arr_set64, htc]
      simp [show 1 + top.toNat + cnt.toNat ≠ j by omega]
    · cases k with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero]
        rw [i4 _ (by omega) (by rw [hc1]; omega), arr_set64, htc]
        simp; omega
      | succ k =>
        simp only [List.getElem_cons_succ]
        have := i5 k (by simpa using hk)
        rw [hc1, tblW_congr (TblSame.of_eq (hP NID (by decide)) (hP _ (by decide)) (hP CTL (by decide)))] at this
        rw [← this]; congr 1; omega
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hok
      · rw [← tblOK_congr (TblSame.of_eq (hP NID (by decide)) (hP _ (by decide)) (hP CTL (by decide)))]; exact i6 x hx
  | case4 m i cnt h1 h2 h3 h4 h5 h6 => intro m' h; cases h
  | case5 m i cnt h1 h2 h3 h4 =>
    intro m' h hr hs
    cases h
    obtain ⟨f1, f3, f4⟩ := lp_fin m top cnt hr
    rw [lsCntN_noprog _ _ _ h1 h2 h3 h4, itemsN_noprog _ _ h1 h2 h3 h4]
    exact ⟨by simp, f1, hr, fun j hj _ => f3 j hj, fun k hk => by simp at hk, by simp, f4⟩
  | case6 m i cnt h1 h2 h3 ih =>
    intro m' h hr hs
    rw [lsCntN_other _ _ _ h1 h2 h3, itemsN_other _ _ h1 h2 h3]
    exact ih m' h hr hs
  | case7 m i cnt h1 =>
    intro m' h hr hs
    cases h
    obtain ⟨f1, f3, f4⟩ := lp_fin m top cnt hr
    rw [lsCntN_end _ _ _ h1, itemsN_end _ _ h1]
    exact ⟨by simp, f1, hr, fun j hj _ => f3 j hj, fun k hk => by simp at hk, by simp, f4⟩

/-! ## `decl_push` -/

theorem MemFrame.ofRecM (m : Mem) (x k n o l t v q h : Word) :
    MemFrame [DECL] [] m (L.Front.recM m x k n o l t v q h) := by
  have fr : ∀ m₁ i v, MemFrame [DECL] [] m m₁ → MemFrame [DECL] [] m (m₁.set64 DECL i v) :=
    fun m₁ i v h => MemFrame.set64' h DECL (by decide) (by simp) i v
  unfold L.Front.recM
  exact fr _ _ _ (fr _ _ _ (fr _ _ _ (fr _ _ _ (fr _ _ _ (fr _ _ _ (fr _ _ _
    (MemFrame.set64 m DECL (by decide) _ _)))))))

theorem pushW_facts (m m' : Mem) (k n o l t v q h : Word) (c : Word)
    (hc : rdW (m.arr64 DECL) 0 = c) (hp : pushW m k n o l t v q h = some m')
    (hs : (m.arr64 DECL).size < 2 ^ 63) :
    MemFrame [DECL] [] m m' ∧ c.toNat < 2 ^ 60 ∧ 1 + 8 * c.toNat + 8 ≤ (m.arr64 DECL).size ∧
    (m'.arr64 DECL)[0]? = some (c + 1) ∧
    (∀ j, 0 < j → j < 1 + 8 * c.toNat → (m'.arr64 DECL)[j]? = (m.arr64 DECL)[j]?) ∧
    dw (m'.arr64 DECL) c.toNat 0 = k ∧ dw (m'.arr64 DECL) c.toNat 1 = n ∧
    dw (m'.arr64 DECL) c.toNat 2 = o ∧ dw (m'.arr64 DECL) c.toNat 3 = l ∧
    dw (m'.arr64 DECL) c.toNat 4 = t ∧ dw (m'.arr64 DECL) c.toNat 5 = v ∧
    dw (m'.arr64 DECL) c.toNat 6 = q ∧ dw (m'.arr64 DECL) c.toNat 7 = h := by
  unfold pushW at hp
  rw [hc] at hp
  split at hp
  · cases hp
  split at hp
  · cases hp
  rename_i h0 h1
  split at hp
  · cases hp
  rename_i h2
  cases hp
  have hlen : (m.len64 DECL).toNat = (m.arr64 DECL).size := by
    simp only [Mem.len64]; exact toNat_ofNat_size _ hs
  have hc60 : c.toNat < 2 ^ 60 := by
    have := UInt64.not_le.mp h1; rw [UInt64.lt_iff_toNat_lt] at this; simpa using this
  have hx : (1 + c * 8).toNat = 1 + 8 * c.toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_mul]; simp; omega
  have hroom : 1 + 8 * c.toNat + 8 ≤ (m.arr64 DECL).size := by
    have := UInt64.not_lt.mp h2
    rw [UInt64.le_iff_toNat_le, hlen, UInt64.toNat_add, hx] at this; simp at this; omega
  have e1 : (1 + c * 8 + 1).toNat = 1 + 8 * c.toNat + 1 := by
    rw [UInt64.toNat_add, hx]; simp; omega
  have e2 : (1 + c * 8 + 2).toNat = 1 + 8 * c.toNat + 2 := by
    rw [UInt64.toNat_add, hx]; simp; omega
  have e3 : (1 + c * 8 + 3).toNat = 1 + 8 * c.toNat + 3 := by
    rw [UInt64.toNat_add, hx]; simp; omega
  have e4 : (1 + c * 8 + 4).toNat = 1 + 8 * c.toNat + 4 := by
    rw [UInt64.toNat_add, hx]; simp; omega
  have e5 : (1 + c * 8 + 5).toNat = 1 + 8 * c.toNat + 5 := by
    rw [UInt64.toNat_add, hx]; simp; omega
  have e6 : (1 + c * 8 + 6).toNat = 1 + 8 * c.toNat + 6 := by
    rw [UInt64.toNat_add, hx]; simp; omega
  have e7 : (1 + c * 8 + 7).toNat = 1 + 8 * c.toNat + 7 := by
    rw [UInt64.toNat_add, hx]; simp; omega
  have hsR : ((recM m (1 + c * 8) k n o l t v q h).arr64 DECL).size = (m.arr64 DECL).size :=
    (MemFrame.ofRecM _ _ _ _ _ _ _ _ _ _).2.2.1 DECL
  refine ⟨?_, hc60, hroom, ?_, fun j hj0 hj => ?_, ?_⟩
  · exact MemFrame.set64' (MemFrame.ofRecM _ _ _ _ _ _ _ _ _ _) DECL (by decide) (by simp) _ _
  · rw [arr_set64, ite_eq_left ⟨by simp, by rw [hsR]; omega⟩]
  · rw [arr_set64]
    simp only [recM, arr_set64, size_set64, e1, e2, e3, e4, e5, e6, e7, hx]
    simp only [show (0 : Word).toNat = 0 from rfl]
    repeat (first | rw [if_pos (by omega)] | rw [ite_eq_right (by omega)])
  · simp only [dw, arr_set64, recM, size_set64, e1, e2, e3, e4, e5, e6, e7, hx,
      show (0 : Word).toNat = 0 from rfl, true_and]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (repeat (first | rw [ite_eq_left (by omega)] | rw [ite_eq_right (by omega)])) <;> rfl

/-! ## The declarations relation, appended to -/

theorem sliceL_congr (P P' : Array Word) (o l : Nat) (h : ∀ j, o ≤ j → j < o + l → P'[j]? = P[j]?) :
    sliceL P' o l = sliceL P o l := by
  simp only [sliceL]
  congr 1
  funext k
  rw [h _ (by omega) (by omega)]

theorem DeclAt_mono (D D' P P' : Array Word) (i : Nat) (d : IDeclaration)
    (hD : ∀ j, 0 < j → j < 1 + 8 * i + 8 → D'[j]? = D[j]?)
    (hP : ∀ j, 0 < j → j < 1 + (P[0]?.getD 0).toNat → P'[j]? = P[j]?)
    (htop : (P[0]?.getD 0).toNat ≤ (P'[0]?.getD 0).toNat) (h : DeclAt D P i d) :
    DeclAt D' P' i d := by
  have hw : ∀ k, k < 8 → dw D' i k = dw D i k := fun k hk => by
    simp only [dw]; rw [hD _ (by omega) (by omega)]
  have hcv : ∀ cv, CVAt D P i cv → CVAt D' P' i cv := by
    intro cv ⟨c1, c2, c3, c4⟩
    rw [CVAt, hw 1 (by omega), hw 2 (by omega), hw 3 (by omega), hw 4 (by omega)]
    refine ⟨c1, c2, by omega, ?_⟩
    rw [sliceL_congr P P' _ _ (fun j hj1 hj2 => hP j (by omega) (by omega))]
    exact c4
  cases d with
  | axiomDecl cv => obtain ⟨h0, h1⟩ := h; exact ⟨by rw [hw 0 (by omega)]; exact h0, hcv cv h1⟩
  | defnDecl cv v hh =>
    obtain ⟨h0, h1, h2, h3⟩ := h
    exact ⟨by rw [hw 0 (by omega)]; exact h0, hcv cv h1, by rw [hw 5 (by omega)]; exact h2,
      by rw [hw 6 (by omega), hw 7 (by omega)]; exact h3⟩
  | thmDecl cv v =>
    obtain ⟨h0, h1, h2⟩ := h
    exact ⟨by rw [hw 0 (by omega)]; exact h0, hcv cv h1, by rw [hw 5 (by omega)]; exact h2⟩
  | opaqueDecl cv v =>
    obtain ⟨h0, h1, h2⟩ := h
    exact ⟨by rw [hw 0 (by omega)]; exact h0, hcv cv h1, by rw [hw 5 (by omega)]; exact h2⟩
  | quotDecl kk cv =>
    obtain ⟨h0, h1, h2⟩ := h
    exact ⟨by rw [hw 0 (by omega)]; exact h0, hcv cv h1, by rw [hw 6 (by omega)]; exact h2⟩
  | basisDecl _ => exact h.elim
  | indDecl _ _ => exact h.elim

theorem DeclAtF_mono (D D' P P' : Array Word) (i : Nat) (d : IDeclaration)
    (hD : ∀ j, 0 < j → j < 1 + 8 * i + 8 → D'[j]? = D[j]?)
    (hP : ∀ j, 0 < j → j < 1 + (P[0]?.getD 0).toNat → P'[j]? = P[j]?)
    (htop : (P[0]?.getD 0).toNat ≤ (P'[0]?.getD 0).toNat) (hPs : P'.size = P.size)
    (h : DeclAtF D P i d) : DeclAtF D' P' i d := by
  cases d with
  | indDecl b nP =>
    have hw : ∀ k, k < 8 → dw D' i k = dw D i k := fun k hk => by
      simp only [dw]; rw [hD _ (by omega) (by omega)]
    obtain ⟨h0, h4, t, ht, hb⟩ := h
    refine ⟨by rw [hw 0 (by omega)]; exact h0, by rw [hw 4 (by omega)]; exact h4, t, by omega, ?_⟩
    rw [hw 2 (by omega), hw 3 (by omega), trunc_congr P P' t hPs (fun j h1 h2 => hP j h1 (by omega))]
    exact hb
  | axiomDecl _ | defnDecl _ _ _ | thmDecl _ _ | opaqueDecl _ _ | quotDecl _ _ | basisDecl _ =>
    simp only [DeclAtF] at h ⊢
    exact DeclAt_mono D D' P P' i _ hD hP htop h

theorem DeclsF.push (D P D' P' : Array Word) (ds : Array IDeclaration) (x : IDeclaration)
    (h : DeclsF D P ds) (hDs : D'.size = D.size) (hPs : P'.size = P.size)
    (hc : (D'[0]?.getD 0).toNat = ds.size + 1) (hroom : 1 + 8 * (ds.size + 1) ≤ D.size)
    (htop : (P[0]?.getD 0).toNat ≤ (P'[0]?.getD 0).toNat)
    (htop' : (P'[0]?.getD 0).toNat + 1 ≤ P.size)
    (hDo : ∀ j, 0 < j → j < 1 + 8 * ds.size → D'[j]? = D[j]?)
    (hPo : ∀ j, 0 < j → j < 1 + (P[0]?.getD 0).toNat → P'[j]? = P[j]?)
    (hnew : DeclAtF D' P' ds.size x) : DeclsF D' P' (ds.push x) := by
  refine ⟨by rw [hDs]; exact h.dsize, by rw [hPs]; exact h.psize, by simpa using hc,
    by rw [hDs]; simpa using hroom, by rw [hPs]; exact htop', fun i hi => ?_⟩
  simp only [Array.size_push] at hi
  rw [Array.getElem_push]
  split
  · rename_i hi'
    exact DeclAtF_mono D D' P P' i _ (fun j hj0 hj => hDo j hj0 (by omega)) hPo htop hPs (h.recs i hi')
  · have : i = ds.size := by omega
    subst this; exact hnew

/-! ## The twin's common data -/

/-- A universe parameter list whose items are bound name ids: `mapM st.name` is pure. -/
theorem mapM_name (m : Mem) (st : StateD) (hN : TblR m NID st.names) :
    ∀ (xs : List Word) (us : List Nat), ItemsR xs us → (∀ x ∈ xs, tblOK m NID x = true) →
      us.mapM st.name = pure (xs.map fun x => decI (tblW m NID x))
  | [], [], _, _ => rfl
  | x :: xs, u :: us, ⟨hx, hxs⟩, hok => by
    obtain ⟨hg, -, hn⟩ := tbl_read hN x (hok x (by simp))
    rw [List.mapM_cons, itemR_eq hx hn,
      mapM_name m st hN xs us hxs (fun y hy => hok y (by simp [hy]))]
    simp [StateD.name, hg]
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim

/-- The record a kind word `k` stands for (`decl_kind`'s result). -/
def declOf (k q hn : Word) (cvp : IConstantVal) (e : EIdx) : IDeclaration :=
  if k = 1 then .axiomDecl cvp
  else if k = 2 then .defnDecl cvp e (hintW q hn)
  else if k = 3 then .thmDecl cvp e
  else if k = 4 then .opaqueDecl cvp e
  else .quotDecl (quotW q) cvp

/-- **The common part**: `decl_cv` reads the name and the type, appends the universe parameter
names and the record; con-ron's `parseCVD` is pure with the same data, and the value (kinds
`2`‥`4`) is a bound expression. -/
theorem cv_core (b : ByteArray) (m m' : Mem) (a₀ : AState) (st : StateD) (hA : ArenaD m a₀)
    (hD : StateDR m st) (f : DFld) (cv : CVRec) (hcv : CVR b cv f) (k q : Word)
    (hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5)
    (h : declCvW b.data m k q f.name f.lps f.type f.value f.hn = some m') :
    ∃ (cvp : IConstantVal) (e : EIdx), parseCVD st cv = pure cvp ∧
      ((k = 2 ∨ k = 3 ∨ k = 4) → ∀ vv, ItemR f.value vv → getDeclD st vv = pure e) ∧
      ArenaD m' a₀ ∧ StateDR m' { st with decls := st.decls.push (declOf k q f.hn cvp e) } := by
  obtain ⟨hcn, hcl, hct⟩ := hcv
  unfold declCvW at h
  have hok : tblOK m NID f.name = true ∧ tblOK m EID f.type = true :=
    Classical.byContradiction fun hok => by simp [hok] at h
  simp only [hok, and_self, ↓reduceIte] at h
  obtain ⟨hgn, hwn, hnn⟩ := tbl_read hD.names _ hok.1
  obtain ⟨hgt, hwt, hnt⟩ := tbl_read hD.exprs _ hok.2
  cases hP : lpPutW b.data m f.lps with
  | none => rw [hP, declK1_none] at h; cases h
  | some m₁ =>
  rw [hP, declK1_some] at h
  -- `lp_put`
  have hDR := hD.decls
  unfold lpPutW at hP
  split at hP
  · cases hP
  rename_i hz
  have hps := hDR.psize
  have hptop := hDR.ptop
  have hrd : rdW (m.arr64 DLP) 0 = (m.arr64 DLP)[0]?.getD 0 := rfl
  obtain ⟨F1, F2, F3, F4, F5, F6, F7⟩ := lpLoopM_facts b.data (rdW (m.arr64 DLP) 0) m (f.lps + 1) 0 m₁
    hP (by rw [hrd]; simp; omega) hps
  simp only [UInt64.toNat_zero, Nat.add_zero] at F1 F4 F5
  have hxs : itemsN b.data (f.lps + 1) = listN b.data f.lps := rfl
  rw [hxs] at F1 F5 F6
  have hmap := mapM_name m st hD.names _ _ hcl F6
  have hP1 : ∀ B, B ≠ DLP → B ≠ CTL → m₁.arr64 B = m.arr64 B := fun B hB hC =>
    F2.1 B (by simpa using hB) hC
  -- the value
  let e : EIdx := decI (tblW m EID f.value)
  let cvp : IConstantVal := ⟨decI (tblW m NID f.name), (listN b.data f.lps).map fun x =>
    decI (tblW m NID x), decI (tblW m EID f.type)⟩
  have hpc : parseCVD st cv = pure cvp := by
    simp [parseCVD, StateD.name, getDeclD, StateD.expr, itemR_eq hcn hnn, itemR_eq hct hnt, hgn,
      hgt, hmap, cvp]
  -- the push
  have hpush : ∃ v, pushW m₁ k (tblW m NID f.name) (rdW (m.arr64 DLP) 0) (lsCntN b.data (f.lps + 1) 0)
      (tblW m EID f.type) v q f.hn = some m' ∧ ((k = 2 ∨ k = 3 ∨ k = 4) → v = tblW m EID f.value ∧
        tblOK m EID f.value = true) := by
    split at h
    · rename_i h234
      split at h
      · rename_i hv
        have hT : TblSame m m₁ EID := TblSame.of_frameD F2 (.inr (.inr rfl)) (by simp [DLP, EID])
          (by simp [DLP, EID]) (by simp) (by simp)
        rw [tblOK_congr hT] at hv
        exact ⟨_, by rw [tblW_congr hT] at h; exact h, fun _ => ⟨rfl, hv⟩⟩
      · cases h
    · rename_i h234; exact ⟨0, h, fun h' => absurd h' h234⟩
  obtain ⟨v, hpu, hv⟩ := hpush
  have hds : (m₁.arr64 DECL).size < 2 ^ 63 := by rw [hP1 DECL (by decide) (by decide)]; exact hDR.dsize
  have hcnt : rdW (m₁.arr64 DECL) 0 = rdW (m.arr64 DECL) 0 := by rw [hP1 DECL (by decide) (by decide)]
  obtain ⟨G1, G2, G3, G4, G5, w0, w1, w2, w3, w4, w5, w6, w7⟩ :=
    pushW_facts m₁ m' _ _ _ _ _ _ _ _ _ hcnt hpu hds
  have hcn' : (rdW (m.arr64 DECL) 0).toNat = st.decls.size := hDR.count
  have hm'P : m'.arr64 DLP = m₁.arr64 DLP := G1.1 DLP (by simp) (by decide)
  have hm'D : m₁.arr64 DECL = m.arr64 DECL := hP1 DECL (by decide) (by decide)
  refine ⟨cvp, e, hpc, fun h234 vv hvv => ?_, ?_, ?_⟩
  · obtain ⟨-, hvok⟩ := hv h234
    obtain ⟨hge, -, hne⟩ := tbl_read hD.exprs _ hvok
    simp [getDeclD, StateD.expr, itemR_eq hvv hne, hge, e]
  · -- `ArenaD`: only `DLP` and `DECL` changed
    have hf : MemFrame [DLP, DECL] [] m m' :=
      (F2.mono (by simp) (by simp)).trans (G1.mono (by simp) (by simp))
    exact ⟨ArenaR.frame_ext _ _ (by simp [DLP, DECL]) (by simp) _ _ hf _ hA.1,
      DerR.frameT hf (by simp [DLP, DECL]) hA.2⟩
  · -- `StateDR`
    have hf : MemFrame [DLP, DECL] [] m m' :=
      (F2.mono (by simp) (by simp)).trans (G1.mono (by simp) (by simp))
    have hfr : ∀ B, B ≠ DLP → B ≠ DECL → B ≠ CTL → m'.arr64 B = m.arr64 B :=
      fun B h1 h2 h3 => hf.1 B (by simp [h1, h2]) h3
    have htc : (rdW (m.arr64 DLP) 0 + lsCntN b.data (f.lps + 1) 0).toNat =
        (rdW (m.arr64 DLP) 0).toNat + (lsCntN b.data (f.lps + 1) 0).toNat := by
      rw [UInt64.toNat_add]; simp; omega
    have hc1 : (rdW (m.arr64 DECL) 0 + 1).toNat = (rdW (m.arr64 DECL) 0).toNat + 1 := by
      rw [UInt64.toNat_add]; simp; omega
    have hP0 : (m'.arr64 DLP)[0]?.getD 0 = rdW (m.arr64 DLP) 0 + lsCntN b.data (f.lps + 1) 0 := by
      rw [hm'P, F7]; rfl
    have hD0 : (m'.arr64 DECL)[0]?.getD 0 = rdW (m.arr64 DECL) 0 + 1 := by rw [G4]; rfl
    refine ⟨hD.names.frame hf (.inl rfl) (by simp [DLP, DECL, idArrs]) (by simp),
      hD.levels.frame hf (.inr (.inl rfl)) (by simp [DLP, DECL, idArrs]) (by simp),
      hD.exprs.frame hf (.inr (.inr rfl)) (by simp [DLP, DECL, idArrs]) (by simp), ?_,
      by rw [hf.2.2.1, hf.2.2.1]; exact hD.ifs⟩
    rw [hcn'] at G3
    refine DeclsF.push _ _ _ _ _ _ hDR (by rw [G1.2.2.1, hm'D]) (by rw [hm'P, F2.2.2.1])
      (by rw [hD0, hc1, hcn']) (by rw [← hm'D]; omega)
      (by rw [hP0, htc, ← hrd]; omega) (by rw [hP0, htc]; omega)
      (fun j hj0 hj => by rw [G5 j hj0 (by rw [hcn']; exact hj), hm'D])
      (fun j hj0 hj => by rw [hm'P]; exact F4 j hj0 (by rw [hrd]; omega)) ?_
    -- the new record
    have hlist : (sliceL (m'.arr64 DLP) (1 + (rdW (m.arr64 DLP) 0).toNat)
        (lsCntN b.data (f.lps + 1) 0).toNat).map decI = cvp.levelParams := by
      rw [hm'P]
      simp only [cvp, sliceL, List.map_ofFn]
      apply List.ext_getElem
      · simp [F1]
      · intro k hk1 hk2
        simp only [List.getElem_ofFn, List.getElem_map, Function.comp]
        rw [F5 k (by simpa [F1] using hk1)]
        rfl
    have hCV : CVAt (m'.arr64 DECL) (m'.arr64 DLP) st.decls.size cvp := by
      rw [← hcn']
      refine ⟨by rw [w1], by rw [w4], ?_, by rw [w2, w3]; exact hlist⟩
      rw [w2, w3, hP0, htc]; exact Nat.le_refl _
    rw [← hcn'] at hCV ⊢
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by rw [w0], hCV⟩
    · obtain ⟨hve, -⟩ := hv (.inl rfl)
      exact ⟨by rw [w0], hCV, by rw [w5, hve], by rw [w6, w7]⟩
    · obtain ⟨hve, -⟩ := hv (.inr (.inl rfl))
      exact ⟨by rw [w0], hCV, by rw [w5, hve]⟩
    · obtain ⟨hve, -⟩ := hv (.inr (.inr rfl))
      exact ⟨by rw [w0], hCV, by rw [w5, hve]⟩
    · exact ⟨by rw [w0], hCV, by rw [w6]⟩

theorem declKindW_some (pl hk hn flag k q : Word) (h : declKindW pl hk hn flag = some (k, q)) :
    (pl = 20 ∧ flag = 0 ∧ k = 1) ∨
    (pl = 21 ∧ flag = 1 ∧ k = 2 ∧ q = hk ∧ hk ≠ 0 ∧ hk ≤ 3 ∧ ¬ (hk = 3 ∧ hn = NONE)) ∨
    (pl = 22 ∧ k = 3) ∨ (pl = 23 ∧ flag = 0 ∧ k = 4) ∨
    (pl = 24 ∧ k = 5 ∧ q = flag ∧ flag ≠ 0 ∧ flag ≤ 4) := by
  unfold declKindW at h
  split at h
  · split at h <;> simp_all
  split at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp_all
    · cases h
  split at h
  · simp_all
  split at h
  · split at h <;> simp_all
  split at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp_all
    · cases h
  · cases h

/-- **`apply_decl`'s model refines con-ron's declaration step**: on fields `f` that con-leche's
scanner relates to the declaration record `d` (`DeclR`), a successful `apply_decl` is
`applyLine st (.decl d) = pure (.inl st')` (no interning, no verdict), with `ArenaD` of the same
arena state and `StateDR m' st'`. -/
theorem applyDeclW_refines (b : ByteArray) (m m' : Mem) (a₀ : AState) (st : StateD)
    (hA : ArenaD m a₀) (hD : StateDR m st) (f : DFld) (d : DeclRec) (hE : DeclR b d f)
    (h : applyDeclW b.data m f.pl f.name f.lps f.type f.value f.hk f.hn f.flag = some m') :
    ∃ st', applyLine st (.decl d) = pure (.inl st') ∧ ArenaD m' a₀ ∧ StateDR m' st' := by
  unfold applyDeclW at h
  cases hK : declKindW f.pl f.hk f.hn f.flag with
  | none => rw [hK, declK0_none] at h; cases h
  | some kq =>
  obtain ⟨k, q⟩ := kq
  rw [hK, declK0_some] at h
  have hks := declKindW_some _ _ _ _ _ _ hK
  have hk5 : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by
    rcases hks with ⟨-, -, h⟩ | ⟨-, -, h, -⟩ | ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩ <;> simp [h]
  cases d with
  | ax cv u =>
    obtain ⟨hpl, hcv, hfl⟩ := hE
    obtain ⟨cvp, e, hpc, -, hA', hD'⟩ := cv_core b m m' a₀ st hA hD f cv hcv k q hk5 h
    rcases hks with ⟨-, h0, rfl⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;>
      (try (rw [hpl] at h1; exact absurd h1 (by decide)))
    have hu : u = false := by cases u <;> simp_all
    subst hu
    refine ⟨_, ?_, hA', hD'⟩
    simp [applyLine, applyDeclD, processLineCoreD, hpc, pushDecl, declOf]
  | defn cv v hints safety =>
    obtain ⟨hpl, hcv, hvv, hh, hsf⟩ := hE
    obtain ⟨cvp, e, hpc, hge, hA', hD'⟩ := cv_core b m m' a₀ st hA hD f cv hcv k q hk5 h
    rcases hks with ⟨h1, -⟩ | ⟨-, h0, rfl, rfl, hk0, hk3, hkn⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;>
      (try (rw [hpl] at h1; exact absurd h1 (by decide)))
    have hs := hsf h0
    subst hs
    have hg := hge (.inl rfl) v hvv
    refine ⟨_, ?_, hA', hD'⟩
    cases hints with
    | «abbrev» =>
      simp only [HintsR] at hh
      simp [applyLine, applyDeclD, processLineCoreD, hpc, pushDecl, declOf, hg, hintW, hh]
    | «opaque» =>
      simp only [HintsR] at hh
      simp [applyLine, applyDeclD, processLineCoreD, hpc, pushDecl, declOf, hg, hintW, hh]
    | regular n =>
      obtain ⟨h3, hn⟩ := hh
      have : f.hn ≠ NONE := fun h' => hkn ⟨h3, h'⟩
      simp [applyLine, applyDeclD, processLineCoreD, hpc, pushDecl, declOf, hg, hintW, h3,
        itemR_eq hn this]
  | thm cv v =>
    obtain ⟨hpl, hcv, hvv⟩ := hE
    obtain ⟨cvp, e, hpc, hge, hA', hD'⟩ := cv_core b m m' a₀ st hA hD f cv hcv k q hk5 h
    rcases hks with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, rfl⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;>
      (try (rw [hpl] at h1; exact absurd h1 (by decide)))
    have hg := hge (.inr (.inl rfl)) v hvv
    refine ⟨_, ?_, hA', hD'⟩
    simp [applyLine, applyDeclD, processLineCoreD, hpc, pushDecl, declOf, hg]
  | opaq cv v u =>
    obtain ⟨hpl, hcv, hvv, hfl⟩ := hE
    obtain ⟨cvp, e, hpc, hge, hA', hD'⟩ := cv_core b m m' a₀ st hA hD f cv hcv k q hk5 h
    rcases hks with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h0, rfl⟩ | ⟨h1, -⟩ <;>
      (try (rw [hpl] at h1; exact absurd h1 (by decide)))
    have hu : u = false := by cases u <;> simp_all
    subst hu
    have hg := hge (.inr (.inr rfl)) v hvv
    refine ⟨_, ?_, hA', hD'⟩
    simp [applyLine, applyDeclD, processLineCoreD, hpc, pushDecl, declOf, hg]
  | quot cv kind =>
    obtain ⟨hpl, hcv, hq⟩ := hE
    obtain ⟨cvp, e, hpc, -, hA', hD'⟩ := cv_core b m m' a₀ st hA hD f cv hcv k q hk5 h
    rcases hks with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, rfl, rfl, hf0, hf4⟩ <;>
      (try (rw [hpl] at h1; exact absurd h1 (by decide)))
    obtain ⟨q1, q2, q3, q4⟩ := hq
    refine ⟨_, ?_, hA', hD'⟩
    have hf : f.flag = 1 ∨ f.flag = 2 ∨ f.flag = 3 ∨ f.flag = 4 := by
      have := UInt64.le_iff_toNat_le.mp hf4
      have h0 : f.flag.toNat ≠ 0 := fun h' => hf0 (UInt64.toNat_inj.mp (by simpa using h'))
      have : f.flag.toNat = 1 ∨ f.flag.toNat = 2 ∨ f.flag.toNat = 3 ∨ f.flag.toNat = 4 := by
        simp at this; omega
      rcases this with h | h | h | h
      · exact .inl (UInt64.toNat_inj.mp (by simpa using h))
      · exact .inr (.inl (UInt64.toNat_inj.mp (by simpa using h)))
      · exact .inr (.inr (.inl (UInt64.toNat_inj.mp (by simpa using h))))
      · exact .inr (.inr (.inr (UInt64.toNat_inj.mp (by simpa using h))))
    rcases hf with h' | h' | h' | h'
    · rw [q1 h']; simp [applyLine, applyDeclD, processLineCoreD, hpc, pushDecl, declOf, quotW, h']
    · rw [q2 h']; simp [applyLine, applyDeclD, processLineCoreD, hpc, pushDecl, declOf, quotW, h']
    · rw [q3 h']; simp [applyLine, applyDeclD, processLineCoreD, hpc, pushDecl, declOf, quotW, h']
    · rw [q4 h']; simp [applyLine, applyDeclD, processLineCoreD, hpc, pushDecl, declOf, quotW, h']
  | ind tys cts rcs =>
    have hpl : f.pl = 25 := hE.1
    rcases hks with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;>
      (rw [hpl] at h1; exact absurd h1 (by decide))

/-- The same in `AM` terms: `applyLine st (.decl d)` succeeds from `a₀`, leaves the arena state
alone and gives the parse state `st'`. -/
@[refines_part ConRon.Arena.Frontend.processLineCoreD "axiom, def, thm, opaque, quot"]
theorem applyDeclW_refinesAM (b : ByteArray) (m m' : Mem) (a₀ : AState) (st : StateD)
    (hA : ArenaD m a₀) (hD : StateDR m st) (f : DFld) (d : DeclRec) (hE : DeclR b d f)
    (h : applyDeclW b.data m f.pl f.name f.lps f.type f.value f.hk f.hn f.flag = some m') :
    ∃ st', AM.ok (applyLine st (.decl d)) a₀ ∧ (applyLine st (.decl d)).run a₀ = .ok (.inl st', a₀) ∧
      AM.st (applyLine st (.decl d)) a₀ = a₀ ∧ ArenaD m' a₀ ∧ StateDR m' st' := by
  obtain ⟨st', hp, hA', hD'⟩ := applyDeclW_refines b m m' a₀ st hA hD f d hE h
  exact ⟨st', by rw [hp]; trivial, by rw [hp]; rfl, by rw [hp]; rfl, hA', hD'⟩

end L.Front
