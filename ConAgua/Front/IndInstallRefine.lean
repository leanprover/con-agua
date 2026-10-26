import ConAgua.Front.IndApplyRefine9

/-!
# `install_ind_d` refines `installIndD`, I: the constant records in `DLP`

Every record the install writes is allocated above `DLP`'s top and decodes (`decCI`) as the twin's
constant once it is written; later allocations keep it (`PExt`). The pieces: `cvW_facts` (a
constant value: name, the universe parameters' `lp_put` slice, type), `capsM`, `ruleM`, the three
record kinds (`typeW_dec`, `ctorRW_dec`, `recRW_dec`).
-/

open L.Arena
open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend (IndCtorRec IndTypeRec IndRecRec CVRec RuleRec)
open ConAgua.Front.FieldsLink
open L.Front.Fields (listN itemsN)


namespace L.Front.Ind

/-! ## The pool's growth -/

/-- **What the install does to `DLP`**: appends (its top grows, the words up to the old top kept),
nothing else. -/
structure PExt (m m' : Mem) : Prop where
  frame : MemFrame [DLP] [] m m'
  top : topN m DLP ≤ topN m' DLP
  keep : ∀ i, 1 ≤ i → i ≤ topN m DLP → wd m' DLP i = wd m DLP i

theorem PExt.refl (m : Mem) : PExt m m := ⟨MemFrame.refl _ _ _, Nat.le_refl _, fun _ _ _ => rfl⟩

theorem PExt.trans {m₁ m₂ m₃ : Mem} (h₁ : PExt m₁ m₂) (h₂ : PExt m₂ m₃) : PExt m₁ m₃ :=
  ⟨h₁.frame.trans h₂.frame, Nat.le_trans h₁.top h₂.top,
    fun i h1 h2 => (h₂.keep i h1 (Nat.le_trans h2 h₁.top)).trans (h₁.keep i h1 h2)⟩

theorem PExt.other {m m' : Mem} (h : PExt m m') (A : ArrId) (h1 : A ≠ DLP) (h2 : A ≠ CTL) :
    m'.arr64 A = m.arr64 A := h.frame.1 A (by simp [h1]) h2

theorem PExt.size {m m' : Mem} (h : PExt m m') (A : ArrId) : (m'.arr64 A).size = (m.arr64 A).size :=
  h.frame.2.2.1 A

/-- A write at an index above the top keeps a `PExt`. -/
theorem PExt.set {m m' : Mem} (h : PExt m m') (i v : Word) (hi : topN m DLP < i.toNat)
    (ht : 0 < i.toNat) : PExt m (m'.set64 DLP i v) :=
  ⟨h.frame.trans (MemFrame.set64 _ _ (by decide) _ _), by
    have := h.top; simp only [topN, wd_setA, show (0 : Word).toNat = 0 from rfl]
    rw [if_neg (by omega)]; exact this, fun j h1 h2 => by
      rw [wd_setA, if_neg (by omega)]; exact h.keep j h1 h2⟩

/-- The `DLP` allocator. -/
theorem allocP_facts {m m' : Mem} {k o : Word} (hs : (m.arr64 DLP).size < 2 ^ 63)
    (ht : topN m DLP + 1 ≤ (m.arr64 DLP).size) (h : allocW m DLP k = some (o, m')) :
    PExt m m' ∧ o.toNat = topN m DLP + 1 ∧ topN m' DLP = topN m DLP + k.toNat ∧
      topN m DLP + 1 + k.toNat ≤ (m.arr64 DLP).size ∧ (∀ i, i ≠ 0 → wd m' DLP i = wd m DLP i) := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := allocW_factsA (by decide) hs (by omega) h
  exact ⟨⟨a5, by omega, fun i h1 _ => a4 i (by omega)⟩, a1, a2, a3, a4⟩

/-! ## The truncated pool -/

theorem trunc_get (P : Array Word) (t j : Nat) (h1 : 1 ≤ j) (h2 : j ≤ t) (hs : t < P.size) :
    (trunc P t)[j]? = P[j]? := by
  simp only [trunc, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, Array.getElem?_extract,
    Array.size_extract, Nat.sub_zero, Nat.zero_add]
  rw [if_neg (by omega), if_pos (by omega)]


/-- What the install reads of the front's state: the name and expression tables, `DLP`'s size and
top. (Unlike `StateDR` it survives the writes of the block's pointers below the top.) -/
structure LkR (m : Mem) (st : StateD) : Prop where
  names : TblR m NID st.names
  exprs : TblR m EID st.exprs
  psize : (m.arr64 DLP).size < 2 ^ 63
  ptop : topN m DLP + 1 ≤ (m.arr64 DLP).size

theorem StateDR.lkR {m : Mem} {st : StateD} (h : StateDR m st) : LkR m st :=
  ⟨h.names, h.exprs, h.decls.psize, h.decls.ptop⟩

theorem LkR.frame {m m' : Mem} {st : StateD} (h : LkR m st) (hf : MemFrame [DLP] [] m m')
    (ht : topN m' DLP + 1 ≤ (m'.arr64 DLP).size) : LkR m' st :=
  ⟨h.names.frame hf (.inl rfl) (by simp [DLP, idArrs]) (by simp),
    h.exprs.frame hf (.inr (.inr rfl)) (by simp [DLP, idArrs]) (by simp), by rw [hf.2.2.1]; exact h.psize,
    ht⟩

theorem lkR_name {m : Mem} {st : StateD} (hD : LkR m st) {x w : Word} (a : AState)
    (h : lkW m NID x = some w) :
    (st.name x.toNat).run a = .ok (decI w, a) ∧ w.toNat < 2 ^ 32 := by
  unfold lkW at h
  split at h
  · rename_i hok
    cases h
    obtain ⟨h1, h2⟩ := hD.names.read _ _ _ _ hok
    exact ⟨by simp [StateD.name, h1]; rfl, h2⟩
  · cases h

theorem lkR_expr {m : Mem} {st : StateD} (hD : LkR m st) {x w : Word} (a : AState)
    (h : lkW m EID x = some w) :
    (getDeclD st x.toNat).run a = .ok (decE w, a) ∧ w.toNat < 2 ^ 32 := by
  unfold lkW at h
  split at h
  · rename_i hok
    cases h
    obtain ⟨h1, h2⟩ := hD.exprs.read _ _ _ _ hok
    exact ⟨by simp [getDeclD, StateD.expr, h1, decE_eq]; rfl, h2⟩
  · cases h

/-- The pool `P` holds `m`'s `DLP` words from `lo` up to `m`'s top. -/
def AgreesFrom (P : Array Word) (m : Mem) (lo : Nat) : Prop :=
  ∀ i, lo ≤ i → i ≤ topN m DLP → P[i]? = some (wd m DLP i)

theorem itemsR_length : ∀ (xs : List Word) (us : List Nat), ItemsR xs us → xs.length = us.length
  | [], [], _ => rfl
  | _ :: xs, _ :: us, h => by simp [itemsR_length xs us h.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem wd_some (m : Mem) (A : ArrId) (i : Nat) (h : i < (m.arr64 A).size) :
    (m.arr64 A)[i]? = some (wd m A i) := by
  simp [wd, Array.getElem?_eq_getElem h]

theorem mapM_some_ofI {α β : Type} (f : α → Option β) (g : α → β) :
    ∀ l : List α, (∀ x ∈ l, f x = some (g x)) → l.mapM f = some (l.map g)
  | [], _ => rfl
  | x :: xs, h => by
    simp [List.mapM_cons, h x (by simp), mapM_some_ofI f g xs (fun y hy => h y (by simp [hy]))]

theorem range_map_getElem! {α β : Type} [Inhabited α] (l : List α) (g : α → β) :
    (List.range l.length).map (fun j => g l[j]!) = l.map g := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range]; rw [getElem!_pos l j h1]

theorem hd?_of {k : IdxKind} {a : Array Word} {i : Nat} {w : Word} (h : a[i]? = some w)
    (hw : w.toNat < 2 ^ 32) : (hd? a i : Option (Idx k)) = some (decI w) := by
  simp [hd?, h, hw]

/-- A constant value from its words (handles below `2^32`). -/
theorem decCV_of {a : Array Word} {q : Nat} {wn wt s ll : Word} {f : Nat → Word}
    (h0 : a[q]? = some wn) (hn : wn.toNat < 2 ^ 32) (h1 : a[q + 1]? = some s)
    (h2 : a[q + 2]? = some ll) (h3 : a[q + 3]? = some wt) (ht : wt.toNat < 2 ^ 32)
    (hs : ∀ j < ll.toNat, a[s.toNat + j]? = some (f j) ∧ (f j).toNat < 2 ^ 32) :
    decCV a q = some ⟨decI wn, (List.range ll.toNat).map (fun j => decI (f j)), decI wt⟩ := by
  have h2' : a[q + 1 + 1]? = some ll := h2
  have hsl : (hslice? a s.toNat ll.toNat : Option (List NIdx)) =
      some ((List.range ll.toNat).map fun j => decI (f j)) :=
    mapM_some_ofI _ _ _ (fun j hj => hd?_of (hs j (List.mem_range.mp hj)).1 (hs j (List.mem_range.mp hj)).2)
  simp [decCV, hlist?, nat?, hd?_of h0 hn, hd?_of h3 ht, h1, h2', hsl]

/-- The words of `cvM`. -/
theorem cvM_wd (m : Mem) (q n o l t : Word) (j : Nat) (hq : q.toNat + 3 < (m.arr64 DLP).size)
    (hq4 : q.toNat + 4 < 2 ^ 64) :
    wd (cvM m q n o l t) DLP j =
      if j = q.toNat then n else if j = q.toNat + 1 then o + 1 else if j = q.toNat + 2 then l
      else if j = q.toNat + 3 then t else wd m DLP j := by
  have e1 : (q + 1).toNat = q.toNat + 1 := widx2 _ _ (by simp; omega)
  have e2 : (q + 2).toNat = q.toNat + 2 := widx2 _ _ (by simp; omega)
  have e3 : (q + 3).toNat = q.toNat + 3 := widx2 _ _ (by simp; omega)
  simp only [cvM, wd_setA, size_set64, e1, e2, e3, true_and]
  by_cases h0 : j = q.toNat
  · subst h0; simp; omega
  by_cases h1 : j = q.toNat + 1
  · subst h1; simp; omega
  by_cases h2 : j = q.toNat + 2
  · subst h2; simp; omega
  by_cases h3 : j = q.toNat + 3
  · subst h3; simp; omega
  simp [Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3, h0, h1, h2, h3]

/-- **`ind_cv` against `parseCVD`**: the constant value's four words at `q`, its universe
parameters appended by `lp_put`; they decode as the twin's constant value. -/
@[refines_part ConRon.Arena.Frontend.parseCVD "a block's constant values (ind_cv)"]
theorem cvW_facts {b : ByteArray} {m m' : Mem} {st : StateD} (a : AState) (hD : LkR m st)
    {q nm lps ty : Word} {cv : CVRec}
    (hnm : nm.toNat = cv.name) (hty : ty.toNat = cv.type) (hlps : ItemsR (listN b.data lps) cv.levelParams)
    (hq1 : 1 ≤ q.toNat) (hq : q.toNat + 4 ≤ topN m DLP + 1)
    (h : cvW b.data m q nm lps ty = some m') :
    ∃ cvp, (parseCVD st cv).run a = .ok (cvp, a) ∧ MemFrame [DLP] [] m m' ∧
      topN m' DLP = topN m DLP + cv.levelParams.length ∧ topN m' DLP + 1 ≤ (m'.arr64 DLP).size ∧
      (∀ i, 1 ≤ i → i < q.toNat → wd m' DLP i = wd m DLP i) ∧
      (∀ i, q.toNat + 4 ≤ i → i ≤ topN m DLP → wd m' DLP i = wd m DLP i) ∧
      (∀ P, (∀ i, (q.toNat ≤ i ∧ i < q.toNat + 4) ∨ (topN m DLP < i ∧ i ≤ topN m' DLP) →
        P[i]? = some (wd m' DLP i)) → decCV P q.toNat = some cvp) := by
  have hps := hD.psize
  have hptop : topN m DLP + 1 ≤ (m.arr64 DLP).size := hD.ptop
  unfold cvW at h
  rcases hn : lkW m NID nm with _ | nh <;> simp only [hn, wK, reduceCtorEq] at h
  rcases ht : lkW m EID ty with _ | th <;> simp only [ht, wK, reduceCtorEq] at h
  rcases hl : lpPutW b.data m lps with _ | m₁ <;> simp only [hl, mK, reduceCtorEq] at h
  simp only [Option.some.injEq] at h
  subst h
  obtain ⟨n1, n2⟩ := lkR_name hD a hn
  obtain ⟨y1, y2⟩ := lkR_expr hD a ht
  rw [hnm] at n1; rw [hty] at y1
  unfold lpPutW at hl
  split at hl; cases hl
  have hrdN : (rdW (m.arr64 DLP) 0).toNat = topN m DLP := rfl
  obtain ⟨F1, F2, F3, F4, F5, F6, F7⟩ := lpLoopM_facts b.data (rdW (m.arr64 DLP) 0) m (lps + 1) 0 m₁
    hl (by rw [hrdN, UInt64.toNat_zero]; omega) hps
  simp only [UInt64.toNat_zero, Nat.add_zero] at F1 F4 F5
  have hxs : itemsN b.data (lps + 1) = listN b.data lps := rfl
  rw [hxs] at F1 F5 F6
  have hlen := itemsR_length _ _ hlps
  have hmap := mapM_name m st hD.names _ _ hlps F6
  let cvp : IConstantVal := ⟨decI nh, (listN b.data lps).map fun x => decI (tblW m NID x), decE th⟩
  have hpc : (parseCVD st cv).run a = .ok (cvp, a) := by
    unfold parseCVD
    rw [run_bind _ _ a _ n1, run_bind _ _ a _ y1, hmap]; rfl
  have hs1 : (m₁.arr64 DLP).size = (m.arr64 DLP).size := F2.2.2.1 DLP
  have htop1 : topN m₁ DLP = topN m DLP + (listN b.data lps).length := by
    show ((m₁.arr64 DLP)[0]?.getD 0).toNat = _
    rw [F7]; simp only [Option.getD_some]
    rw [widx2 _ _ (by rw [F1, hrdN]; omega), F1, hrdN]; simp
  have hq3 : q.toNat + 3 < (m₁.arr64 DLP).size := by rw [hs1]; omega
  have htopF : topN (cvM m₁ q nh (rdW (m.arr64 DLP) 0) (lsCntN b.data (lps + 1) 0) th) DLP =
      topN m DLP + (listN b.data lps).length := by
    rw [← htop1]
    unfold topN; rw [cvM_wd _ _ _ _ _ _ 0 hq3 (by omega)]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  refine ⟨cvp, hpc, F2.trans (by
      unfold cvM; exact ((((MemFrame.set64 _ _ (by decide) _ _).trans (MemFrame.set64 _ _ (by decide) _ _)).trans
        (MemFrame.set64 _ _ (by decide) _ _)).trans (MemFrame.set64 _ _ (by decide) _ _))), ?_, ?_, ?_, ?_, ?_⟩
  · rw [htopF, ← hlen]
  · rw [htopF]; unfold cvM; simp only [size_set64]; rw [hs1]; rw [F1, hrdN] at F3; omega
  · intro i h1 h2
    rw [cvM_wd _ _ _ _ _ _ i hq3 (by omega)]
    simp only [show i ≠ q.toNat by omega, show i ≠ q.toNat + 1 by omega, show i ≠ q.toNat + 2 by omega,
      show i ≠ q.toNat + 3 by omega, if_false]
    simp only [wd]; rw [F4 i (by omega) (by rw [hrdN]; omega)]
  · intro i h1 h2
    rw [cvM_wd _ _ _ _ _ _ i hq3 (by omega)]
    simp only [show i ≠ q.toNat by omega, show i ≠ q.toNat + 1 by omega, show i ≠ q.toNat + 2 by omega,
      show i ≠ q.toNat + 3 by omega, if_false]
    simp only [wd]; rw [F4 i (by omega) (by rw [hrdN]; omega)]
  · intro P hP
    have hw := fun j => cvM_wd m₁ q nh (rdW (m.arr64 DLP) 0) (lsCntN b.data (lps + 1) 0) th j hq3 (by omega)
    have e0 := hP q.toNat (.inl ⟨by omega, by omega⟩)
    have e1 := hP (q.toNat + 1) (.inl ⟨by omega, by omega⟩)
    have e2 := hP (q.toNat + 2) (.inl ⟨by omega, by omega⟩)
    have e3 := hP (q.toNat + 3) (.inl ⟨by omega, by omega⟩)
    rw [hw] at e0 e1 e2 e3
    simp only [if_pos rfl, show q.toNat + 1 ≠ q.toNat by omega, show q.toNat + 2 ≠ q.toNat by omega,
      show q.toNat + 2 ≠ q.toNat + 1 by omega, show q.toNat + 3 ≠ q.toNat by omega,
      show q.toNat + 3 ≠ q.toNat + 1 by omega, show q.toNat + 3 ≠ q.toNat + 2 by omega, if_false,
      if_true, ↓reduceIte] at e0 e1 e2 e3
    have ho : (rdW (m.arr64 DLP) 0 + 1).toNat = topN m DLP + 1 := by
      rw [UInt64.toNat_add, hrdN]; simp; omega
    have hc : (lsCntN b.data (lps + 1) 0).toNat = (listN b.data lps).length := by
      rw [F1]; simp
    have := decCV_of (f := fun j => tblW m NID (listN b.data lps)[j]!) e0 n2 e1 e2 e3 y2 (fun j hj => by
      rw [hc] at hj
      have hmem : (listN b.data lps)[j]! ∈ listN b.data lps := by
        rw [getElem!_pos (listN b.data lps) j hj]; exact List.getElem_mem hj
      refine ⟨?_, (tbl_read hD.names _ (F6 _ hmem)).2.1⟩
      rw [ho, hP _ (.inr ⟨by omega, by rw [htopF]; omega⟩), hw]
      simp only [show topN m DLP + 1 + j ≠ q.toNat by omega, show topN m DLP + 1 + j ≠ q.toNat + 1 by omega,
        show topN m DLP + 1 + j ≠ q.toNat + 2 by omega, show topN m DLP + 1 + j ≠ q.toNat + 3 by omega,
        if_false]
      have := F5 j hj
      rw [hrdN, show 1 + topN m DLP + j = topN m DLP + 1 + j by omega] at this
      simp only [wd]; rw [this, getElem!_pos (listN b.data lps) j hj]; rfl)
    rw [this, hc, range_map_getElem! (listN b.data lps) (fun x => (decI (tblW m NID x) : NIdx))]
    simp only [cvp, decE_eq]

end L.Front.Ind
