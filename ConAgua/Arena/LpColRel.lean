import ConAgua.Arena.ConsLibRel
import ConAgua.Arena.LpCol

/-!
# The level-parameter columns: the relation, generically (helper `whnf4-d23`)

A table with a column (`LpCol.lean`) relates node `i` of tier `t` to the word `A[2 i + t] =
f (derAt i)`, `f` the bit of the derived record as a word (`b2w ∘ (·.hasParam)` for levels and
level lists, `b2w ∘ lpOfData` for expressions): `ColT`, both tiers behind a lens `ColT2`. A table
whose bit is a constant (`zero`, `param`) has the arena-only `ConstT2`. Both also say that the
derived array is as long as the node array (con-ron's `StoreWF` clause), so that `derAt i` of a
node is the pushed record and not the `default`.

An `intern_*` with a column is `mkK A S.ca (cnt2 m S.ca) bit (internM …)` (the model's
equation, per table): the library's interning, then, if the table grew, the bit at the new node.
`mkK_internM_frame` is its frame, `mkK_split` its two halves, `colMk`/`constMk` the column across
it (`DerRel.lean`'s `derMk`, for any lens).
-/

open ConRon.Arena ConLeche

set_option linter.unusedSimpArgs false

namespace L.Arena

/-! ## Moved here from `DerRel.lean` (generic in the table) -/

/-- The count of a tier in L is its node count. -/
theorem cnt_tier {α δ : Type} {k : IdxKind} [BEq α] [Hashable α] (S : Schema)
    (R : Mem → Word → Word → α → Prop) (hs : Mem → Word → Word → Word) (m : Mem) (on : Bool)
    (P Q : Tbl α (Idx k) δ) (hR : StoreR S R hs m on P Q) (t : Word) (ht : t ≤ 1) :
    (cntW S m t).toNat = (if t = 0 then P else Q).nodes.size := by
  rcases word_le_one t ht with rfl | rfl
  · simpa using hR.2.2.1.1
  · simpa using hR.2.2.2.1.1

theorem idxW_hdW (g t n : Word) (_hg : g.toNat < 16) (ht : t ≤ 1) (hn : n.toNat < 2 ^ 27) :
    idxW (hdW g t n) = n ∧ tierW (hdW g t n) = t := by
  have ht' : t.toNat ≤ 1 := ht
  constructor
  · apply UInt64.toNat_inj.mp
    simp only [idxW, hdW, UInt64.toNat_and]
    have : (134217727 : Word).toNat = 2 ^ 27 - 1 := rfl
    rw [this, Nat.and_two_pow_sub_one_eq_mod]
    simp only [UInt64.toNat_add, UInt64.toNat_mul]
    simp; omega
  · apply UInt64.toNat_inj.mp
    simp only [tierW, bit27_toNat, hdW, UInt64.toNat_add, UInt64.toNat_mul]
    simp; omega

theorem derPutW_frame (A : ArrId) (hA : A ≠ CTL) (c : Word) (m₁ m' : Mem) (s r d : Word)
    (h : derPutW A c m₁ s r d = some m') : MemFrame [A] [] m₁ m' := by
  unfold derPutW at h
  split at h
  · cases h; exact MemFrame.refl _ _ _
  split at h
  · cases h
  · cases h; exact MemFrame.set64 m₁ A hA _ _

/-- Two record positions `2 i + t` differ when the nodes or the tiers do. -/
theorem ix_ne (i j : Nat) (t u : Word) (hi : i < 2 ^ 27) (hj : j < 2 ^ 27) (ht : t ≤ 1)
    (hu : u ≤ 1) (h : i ≠ j ∨ t ≠ u) : UInt64.ofNat i * 2 + t ≠ UInt64.ofNat j * 2 + u := by
  intro e
  have e' := congrArg UInt64.toNat e
  have ht' : t.toNat ≤ 1 := ht
  have hu' : u.toNat ≤ 1 := hu
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat'] at e'
  simp at e'
  try rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)] at e'
  rcases h with h | h
  · omega
  · exact h (UInt64.toNat_inj.mp (by omega))

theorem cnt2_eq (S : Schema) (m : Mem) : cnt2 m S.ca = cntW S m 0 + cntW S m 1 := by
  simp [cnt2, cntW]

/-! ## Handles of any kind -/

theorem idxW_tierW_of_decI {k : IdxKind} (r w : Word) (h : (decI r : Idx k) = decI w) :
    idxW r = idxW w ∧ tierW r = tierW w := by
  have e : r.toUInt32 = w.toUInt32 := by
    simp only [decI] at h; exact Idx.ofWord.inj h
  have e' : r.toNat % 2 ^ 32 = w.toNat % 2 ^ 32 := by
    have := congrArg UInt32.toNat e; simpa [UInt64.toNat_toUInt32] using this
  constructor
  · apply UInt64.toNat_inj.mp
    simp only [idxW, UInt64.toNat_and]
    have : (134217727 : Word).toNat = 2 ^ 27 - 1 := rfl
    rw [this, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]; omega
  · apply UInt64.toNat_inj.mp
    simp only [tierW, bit27_toNat]; omega

/-- The handle words of the node an append made: its index and tier. -/
theorem new_handleI {k : IdxKind} (r : Word) (g : UInt32) (t : Word) (n : Nat) (hg : g.toNat < 16)
    (ht : t ≤ 1) (hn : n < 2 ^ 27) (h : (decI r : Idx k) = decI (hdW g.toUInt64 t (UInt64.ofNat n))) :
    idxW r = UInt64.ofNat n ∧ tierW r = t := by
  obtain ⟨h1, h2⟩ := idxW_tierW_of_decI r _ h
  obtain ⟨h3, h4⟩ := idxW_hdW g.toUInt64 t (UInt64.ofNat n) (by simpa using hg) ht
    (by simp; omega)
  exact ⟨h1.trans h3, h2.trans h4⟩

/-! ## The twin's interning, by cases, for any lens -/

section proto
variable {α δ : Type} {k : IdxKind} [BEq α] [Hashable α]

/-- The run of `protoRun`: a hit (state unchanged), or an append to the tier the store is in,
returning the handle of the new node (`DerRel.lean`'s `protoRun_cases`, for any lens). -/
theorem protoRun_casesG (L : Lens α δ k) (key : α) (tag : UInt32) (pf : Option (Idx k))
    (d : δ) (err : CheckError) (a a' : AState) (y : Idx k)
    (h : protoRun L key tag pf d err a = .ok (y, a')) :
    a' = a ∨
    (L.on a = false ∧ (L.getP a).nodes.size < 2 ^ 27 ∧
      y = decI (hdW tag.toUInt64 0 (UInt64.ofNat (L.getP a).nodes.size)) ∧
      a' = L.setP a ((L.getP a).push key d y)) ∨
    (L.on a = true ∧ (L.getS a).nodes.size < 2 ^ 27 ∧
      y = decI (hdW tag.toUInt64 1 (UInt64.ofNat (L.getS a).nodes.size)) ∧
      a' = L.setS a ((L.getS a).push key d y)) := by
  unfold protoRun at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact .inl h.2.symm
  · split at h
    · rename_i hon
      split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact .inl h.2.symm
      · split at h
        · rename_i hc
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine .inr (.inr ⟨hon, by simpa [Tbl.size, Idx.idxCap] using hc, ?_, ?_⟩) <;>
            simp only [show Idx.tierS = UInt32.ofNat 1 from rfl, mk_eq, Tbl.size] <;> rfl
        · simp at h
    · rename_i hon
      split at h
      · rename_i hc
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine .inr (.inl ⟨by simpa using hon, by simpa [Tbl.size, Idx.idxCap] using hc, ?_, ?_⟩) <;>
          simp only [show Idx.tierP = UInt32.ofNat 0 from rfl, mk_eq, Tbl.size] <;> rfl
      · simp at h

/-- The same through an operation's run equation. -/
theorem AM.proto_casesG (L : Lens α δ k) (op : AM (Idx k)) (key : α) (tag : UInt32)
    (pf : Option (Idx k)) (d : δ) (err : CheckError) (a : AState)
    (hrun : op.run a = protoRun L key tag pf d err a) (hok : AM.ok op a) :
    AM.st op a = a ∨
    (L.on a = false ∧ (L.getP a).nodes.size < 2 ^ 27 ∧
      AM.res op a = decI (hdW tag.toUInt64 0 (UInt64.ofNat (L.getP a).nodes.size)) ∧
      AM.st op a = L.setP a ((L.getP a).push key d (AM.res op a))) ∨
    (L.on a = true ∧ (L.getS a).nodes.size < 2 ^ 27 ∧
      AM.res op a = decI (hdW tag.toUInt64 1 (UInt64.ofNat (L.getS a).nodes.size)) ∧
      AM.st op a = L.setS a ((L.getS a).push key d (AM.res op a))) :=
  protoRun_casesG L key tag pf d err a _ _ (hrun.symm.trans (AM.run_of_ok op a hok))

end proto

/-! ## The `lp` bit of each arm of `EStore.derOfView` -/

theorem lp_derBVar (st : EStore) (i : Nat) : lpOfData (st.derOfView (.bvar i)) = false := by
  simp only [EStore.derOfView, EStore.derOfBVar]
  exact lpOfData_pack _ _ _ _ (satSucc_lt i) (by decide)

theorem lp_derFVar (st : EStore) (idx : Nat) (ty : EIdx) :
    lpOfData (st.derOfView (.fvar idx ty)) = lpOfData (st.derived ty) := by
  simp only [EStore.derOfView, EStore.derOfFVar]
  exact lpOfData_pack _ _ _ _ (by decide) (satSucc_lt idx)

theorem lp_derSort (st : EStore) (u : LIdx) :
    lpOfData (st.derOfView (.sort u)) = (st.lder u).hasParam := by
  simp only [EStore.derOfView, EStore.derOfSort]
  exact lpOfData_pack _ _ _ _ (by decide) (by decide)

theorem lp_derConst (st : EStore) (n : NIdx) (us : LsIdx) :
    lpOfData (st.derOfView (.const n us)) = (st.lsder us).hasParam := by
  simp only [EStore.derOfView, EStore.derOfConst]
  exact lpOfData_pack _ _ _ _ (by decide) (by decide)

theorem lp_derLit (st : EStore) (l : ConLeche.Literal) : lpOfData (st.derOfView (.lit l)) = false := by
  simp only [EStore.derOfView, EStore.derOfLit]
  exact lpOfData_pack _ _ _ _ (by decide) (by decide)

theorem lp_derApp (st : EStore) (f x : EIdx) :
    lpOfData (st.derOfView (.app f x)) = (lpOfData (st.derived f) || lpOfData (st.derived x)) := by
  simp only [EStore.derOfView, EStore.derOfApp]
  exact lpOfData_pack _ _ _ _ (max_lt_32768 (bvarOfData_lt _) (bvarOfData_lt _))
    (max_lt_32768 (fvarOfData_lt _) (fvarOfData_lt _))

theorem lp_derBind (st : EStore) (tag : UInt64) (ty b : EIdx) :
    lpOfData (st.derOfBindAt tag ty b) = (lpOfData (st.derived ty) || lpOfData (st.derived b)) := by
  simp only [EStore.derOfBindAt, derOfBind]
  exact lpOfData_pack _ _ _ _ (max_lt_32768 (bvarOfData_lt _) (satPred_lt (bvarOfData_lt _)))
    (max_lt_32768 (fvarOfData_lt _) (fvarOfData_lt _))

theorem lp_derLet (st : EStore) (ty v b : EIdx) :
    lpOfData (st.derOfView (.letE ty v b)) =
      (lpOfData (st.derived ty) || lpOfData (st.derived v) || lpOfData (st.derived b)) := by
  simp only [EStore.derOfView, EStore.derOfLetAt, derOfLet]
  exact lpOfData_pack _ _ _ _
    (max_lt_32768 (max_lt_32768 (bvarOfData_lt _) (bvarOfData_lt _)) (satPred_lt (bvarOfData_lt _)))
    (max_lt_32768 (max_lt_32768 (fvarOfData_lt _) (fvarOfData_lt _)) (fvarOfData_lt _))

theorem lp_derProj (st : EStore) (n : NIdx) (i : Nat) (e : EIdx) :
    lpOfData (st.derOfView (.proj n i e)) = lpOfData (st.derived e) := by
  simp only [EStore.derOfView, EStore.derOfProj]
  exact lpOfData_pack _ _ _ _ (bvarOfData_lt _) (fvarOfData_lt _)

/-! ## The bits as words -/

/-- An expression's `lp` bit as a word. -/
def lpW (d : UInt64) : Word := b2w (lpOfData d)

/-- A level's or level list's `hasParam` bit as a word. -/
def hpW (d : LDer) : Word := b2w d.hasParam

/-- The column write of an append is in bounds: `c < len >> 1`, `t ≤ 1`, `c < 2^27`. -/
theorem col_room (c t L : Word) (ht : t ≤ 1) (h1 : c < 134217728) (h2 : c < L >>> 1) :
    c * 2 + t < L := by
  have ht' : t.toNat ≤ 1 := ht
  have h1' : c.toNat < 134217728 := h1
  have h2' : c.toNat < L.toNat / 2 := by
    have := UInt64.lt_iff_toNat_lt.mp h2
    simpa [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow] using this
  apply UInt64.lt_iff_toNat_lt.mpr
  rw [UInt64.toNat_add, UInt64.toNat_mul]
  simp
  omega

/-- The column write of an append is in bounds, as `toNat` (`ConsSch.WF.colRoom`). -/
theorem colRoom_of (m : Mem) (A : ArrId) (c t : Word) (ht : t ≤ 1) (h1 : c < 134217728)
    (h2 : c < m.len64 A >>> 1) : (c * 2 + t).toNat < (m.arr64 A).size := by
  have := col_room c t (m.len64 A) ht h1 h2
  rw [UInt64.lt_iff_toNat_lt, len64_eq, UInt64.toNat_ofNat'] at this
  exact Nat.lt_of_lt_of_le this (Nat.mod_le _ _)

/-! ## The relations -/

section col
variable {α δ : Type} {k : IdxKind} [BEq α] [Hashable α] [Inhabited δ]

/-- **One tier's column**: as many derived records as nodes, and node `i`'s word `A[2 i + t]` is
`f` of its derived record. -/
def ColT (A : ArrId) (f : δ → Word) (m : Mem) (t : Word) (tb : Tbl α (Idx k) δ) : Prop :=
  tb.der.size = tb.nodes.size ∧
    ∀ i x, tb.nodes[i]? = some x → rdW (m.arr64 A) (UInt64.ofNat i * 2 + t) = f (tb.derAt i)

/-- **A table's column**: both tiers behind the lens. -/
def ColT2 (L : Lens α δ k) (A : ArrId) (f : δ → Word) (m : Mem) (a : AState) : Prop :=
  ColT A f m 0 (L.getP a) ∧ ColT A f m 1 (L.getS a)

/-- **A table whose bit is a constant**: as many derived records as nodes, each satisfying `pr`. -/
def ConstT (pr : δ → Prop) (tb : Tbl α (Idx k) δ) : Prop :=
  tb.der.size = tb.nodes.size ∧ ∀ i x, tb.nodes[i]? = some x → pr (tb.derAt i)

def ConstT2 (L : Lens α δ k) (pr : δ → Prop) (a : AState) : Prop :=
  ConstT pr (L.getP a) ∧ ConstT pr (L.getS a)

theorem colT_mono {A : ArrId} {f : δ → Word} {m m' : Mem} {t : Word} {tb : Tbl α (Idx k) δ}
    (h : ColT A f m t tb)
    (he : ∀ i, i < tb.nodes.size → rdW (m'.arr64 A) (UInt64.ofNat i * 2 + t) =
      rdW (m.arr64 A) (UInt64.ofNat i * 2 + t)) : ColT A f m' t tb := by
  refine ⟨h.1, fun i x hx => ?_⟩
  have hi : i < tb.nodes.size := by
    rcases Nat.lt_or_ge i tb.nodes.size with hl | hl
    · exact hl
    · rw [Array.getElem?_eq_none hl] at hx; cases hx
  rw [he i hi]; exact h.2 i x hx

/-- **A column survives a writer that keeps its array.** -/
theorem ColT2.frame {L : Lens α δ k} {A : ArrId} {f : δ → Word} {m m' : Mem} {a : AState}
    (h : ColT2 L A f m a) (he : m'.arr64 A = m.arr64 A) : ColT2 L A f m' a :=
  ⟨colT_mono h.1 (fun _ _ => by rw [he]), colT_mono h.2 (fun _ _ => by rw [he])⟩

/-- `ColT2.frame` across a `MemFrame` that avoids the column. -/
theorem ColT2.frameM {L : Lens α δ k} {A : ArrId} {f : δ → Word} {Ar : List ArrId} {C : List Word}
    {m m' : Mem} {a : AState} (h : ColT2 L A f m a) (hf : MemFrame Ar C m m') (hA : A ∉ Ar)
    (hc : A ≠ CTL) : ColT2 L A f m' a :=
  h.frame (hf.1 A hA hc)

theorem tbl_push_size (tb : Tbl α (Idx k) δ) (key : α) (d : δ) (y : Idx k) :
    (tb.push key d y).nodes.size = tb.nodes.size + 1 ∧ (tb.push key d y).der.size = tb.der.size + 1 := by
  cases tb; simp [Tbl.push]

/-- An append keeps the column if the new word is the new record's. -/
theorem colT_push {A : ArrId} {f : δ → Word} {m m' : Mem} {t : Word} {tb : Tbl α (Idx k) δ}
    (h : ColT A f m t tb) (key : α) (d : δ) (y : Idx k)
    (he : ∀ i, i < tb.nodes.size → rdW (m'.arr64 A) (UInt64.ofNat i * 2 + t) =
      rdW (m.arr64 A) (UInt64.ofNat i * 2 + t))
    (hn : rdW (m'.arr64 A) (UInt64.ofNat tb.nodes.size * 2 + t) = f d) :
    ColT A f m' t (tb.push key d y) := by
  obtain ⟨hs, hc⟩ := h
  obtain ⟨hpn, hpd⟩ := tbl_push_size tb key d y
  have hp : (tb.push key d y).nodes = tb.nodes.push key ∧ (tb.push key d y).der = tb.der.push d := by
    cases tb; exact ⟨rfl, rfl⟩
  refine ⟨by rw [hpn, hpd, hs], fun i x hx => ?_⟩
  have hda : (tb.push key d y).derAt i = (tb.der.push d).getD i default := by
    simp only [Tbl.derAt, hp.2]
  rw [hp.1] at hx
  rw [hda]
  rw [Array.getElem?_push] at hx
  split at hx
  · rename_i hi'
    subst hi'
    have e1 : (tb.der.push d).getD tb.nodes.size default = d := by simp [Array.getD, ← hs]
    rw [e1, hn]
  · rename_i hne
    have hi : i < tb.nodes.size := by
      rcases Nat.lt_or_ge i tb.nodes.size with hl | hl
      · exact hl
      · rw [Array.getElem?_eq_none hl] at hx; cases hx
    have hi' : i < tb.der.size := by rw [hs]; exact hi
    have := hc i x hx
    have e1 : (tb.der.push d).getD i default = tb.der[i] := by
      simp [Array.getD, hi', Array.getElem_push_lt hi'] <;> intro h <;> omega
    have e2 : tb.derAt i = tb.der[i] := by simp [Tbl.derAt, Array.getD, hi']
    rw [e1, he i hi, this, e2]

/-- An append keeps a constant bit if the new record has it. -/
theorem constT_push {pr : δ → Prop} {tb : Tbl α (Idx k) δ} (h : ConstT pr tb) (key : α) (d : δ)
    (y : Idx k) (hd : pr d) : ConstT pr (tb.push key d y) := by
  obtain ⟨hs, hc⟩ := h
  obtain ⟨hpn, hpd⟩ := tbl_push_size tb key d y
  have hp : (tb.push key d y).nodes = tb.nodes.push key ∧ (tb.push key d y).der = tb.der.push d := by
    cases tb; exact ⟨rfl, rfl⟩
  refine ⟨by rw [hpn, hpd, hs], fun i x hx => ?_⟩
  have hda : (tb.push key d y).derAt i = (tb.der.push d).getD i default := by
    simp only [Tbl.derAt, hp.2]
  rw [hp.1] at hx
  rw [hda]
  rw [Array.getElem?_push] at hx
  split at hx
  · rename_i hi'
    subst hi'
    have e1 : (tb.der.push d).getD tb.nodes.size default = d := by simp [Array.getD, ← hs]
    rw [e1]; exact hd
  · have hi : i < tb.nodes.size := by
      rcases Nat.lt_or_ge i tb.nodes.size with hl | hl
      · exact hl
      · rw [Array.getElem?_eq_none hl] at hx; cases hx
    have hi' : i < tb.der.size := by rw [hs]; exact hi
    have := hc i x hx
    have e1 : (tb.der.push d).getD i default = tb.der[i] := by
      simp [Array.getD, hi', Array.getElem_push_lt hi'] <;> intro h <;> omega
    have e2 : tb.derAt i = tb.der[i] := by simp [Tbl.derAt, Array.getD, hi']
    rw [e1]; rw [e2] at this; exact this

/-- The empty table has every column. -/
theorem colT_empty (A : ArrId) (f : δ → Word) (m : Mem) (t : Word) :
    ColT A f m t (Tbl.empty : Tbl α (Idx k) δ) :=
  ⟨rfl, fun i x h => by simp [Tbl.empty] at h⟩

theorem constT_empty (pr : δ → Prop) : ConstT pr (Tbl.empty : Tbl α (Idx k) δ) :=
  ⟨rfl, fun i x h => by simp [Tbl.empty] at h⟩

/-- **A constant bit across an interning** (`zero`, `param`). -/
theorem constMk (L : Lens α δ k) (pr : δ → Prop) (a a' : AState) (key : α) (d : δ) (y : Idx k)
    (tag : UInt32) (hc : ConstT2 L pr a) (hd : pr d)
    (hst : a' = a ∨
      (L.on a = false ∧ (L.getP a).nodes.size < 2 ^ 27 ∧
        y = decI (hdW tag.toUInt64 0 (UInt64.ofNat (L.getP a).nodes.size)) ∧
        a' = L.setP a ((L.getP a).push key d y)) ∨
      (L.on a = true ∧ (L.getS a).nodes.size < 2 ^ 27 ∧
        y = decI (hdW tag.toUInt64 1 (UInt64.ofNat (L.getS a).nodes.size)) ∧
        a' = L.setS a ((L.getS a).push key d y))) : ConstT2 L pr a' := by
  rcases hst with rfl | ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩
  · exact hc
  · rw [ConstT2, L.getP_setP, L.getS_setP]; exact ⟨constT_push hc.1 key d y hd, hc.2⟩
  · rw [ConstT2, L.getP_setS, L.getS_setS]; exact ⟨hc.1, constT_push hc.2 key d y hd⟩

end col

/-! ## Reading a column -/

theorem derAt_out {α δ : Type} {k : IdxKind} [BEq α] [Hashable α] [Inhabited δ]
    {tb : Tbl α (Idx k) δ} (hs : tb.der.size = tb.nodes.size) (i : Nat) (hi : tb.nodes.size ≤ i) :
    tb.derAt i = default := by
  simp only [Tbl.derAt, Array.getD_eq_getD_getElem?]
  rw [Array.getElem?_eq_none (by rw [hs]; exact hi)]; rfl

/-- **A column read with the count check is `f` of the derived record** (`f default = 0`: a
dangling index reads `0`, the twin's `default`). -/
theorem col_read {α δ : Type} {k : IdxKind} [BEq α] [Hashable α] [Inhabited δ] (S : Schema)
    (R : Mem → Word → Word → α → Prop) (hs : Mem → Word → Word → Word) (A : ArrId) (f : δ → Word)
    (m : Mem) (on : Bool) (P Q : Tbl α (Idx k) δ) (hT : StoreR S R hs m on P Q)
    (hc0 : ColT A f m 0 P) (hc1 : ColT A f m 1 Q) (hf0 : f default = 0) (t i : Word) (ht : t ≤ 1) :
    (if i < rdW (m.arr64 CTL) (S.ca + t) then rdW (m.arr64 A) (i * 2 + t) else 0) =
      f ((if t = 0 then P else Q).derAt i.toNat) := by
  have hcnt := cnt_tier S R hs m on P Q hT t ht
  have hc : ColT A f m t (if t = 0 then P else Q) := by
    rcases word_le_one t ht with rfl | rfl
    · simpa using hc0
    · simpa using hc1
  simp only [cntW] at hcnt
  split
  · rename_i hlt
    have hi : i.toNat < (if t = 0 then P else Q).nodes.size := by
      rw [← hcnt]; exact UInt64.lt_iff_toNat_lt.mp hlt
    have := hc.2 i.toNat _ (Array.getElem?_eq_getElem hi)
    simpa only [UInt64.ofNat_toNat] using this
  · rename_i hge
    rw [derAt_out hc.1 _ (by rw [← hcnt]; exact UInt64.not_lt.mp hge |> UInt64.le_iff_toNat_le.mp), hf0]

/-- **A constant bit with the count check.** -/
theorem const_read {α δ : Type} {k : IdxKind} [BEq α] [Hashable α] [Inhabited δ] (S : Schema)
    (R : Mem → Word → Word → α → Prop) (hs : Mem → Word → Word → Word) (f : δ → Word) (v : Word)
    (m : Mem) (on : Bool) (P Q : Tbl α (Idx k) δ) (hT : StoreR S R hs m on P Q)
    (hc0 : ConstT (fun d => f d = v) P) (hc1 : ConstT (fun d => f d = v) Q) (hf0 : f default = 0)
    (t i : Word) (ht : t ≤ 1) :
    (if i < rdW (m.arr64 CTL) (S.ca + t) then v else 0) = f ((if t = 0 then P else Q).derAt i.toNat) := by
  have hcnt := cnt_tier S R hs m on P Q hT t ht
  have hc : ConstT (fun d => f d = v) (if t = 0 then P else Q) := by
    rcases word_le_one t ht with rfl | rfl
    · simpa using hc0
    · simpa using hc1
  simp only [cntW] at hcnt
  split
  · rename_i hlt
    have hi : i.toNat < (if t = 0 then P else Q).nodes.size := by
      rw [← hcnt]; exact UInt64.lt_iff_toNat_lt.mp hlt
    exact (hc.2 i.toNat _ (Array.getElem?_eq_getElem hi)).symm
  · rename_i hge
    rw [derAt_out hc.1 _ (by rw [← hcnt]; exact UInt64.not_lt.mp hge |> UInt64.le_iff_toNat_le.mp), hf0]

/-! ## Handle decoding at any kind (moved here from `PromoteNRef.lean`) -/

theorem decI_tag {k : IdxKind} (h : Word) (hh : h.toNat < 2 ^ 32) :
    (decI h : Idx k).tag = (h >>> 28).toUInt32 := by
  simp only [decI, Idx.tag]
  apply UInt32.toNat_inj.mp
  simp [UInt32.toNat_div, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  omega

theorem decI_idx {k : IdxKind} (h : Word) : (decI h : Idx k).idxNat = (idxW h).toNat := by
  simp only [decI, Idx.idxNat, Idx.index, idxW]
  simp [UInt32.toNat_mod, UInt64.toNat_toUInt32, UInt64.toNat_and]
  have : (134217727 : Nat) = 2 ^ 27 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

theorem decI_tag_eq {k : IdxKind} (h : Word) (hh : h.toNat < 2 ^ 32) (g : Nat) (hg : g < 16) :
    ((decI h : Idx k).tag = UInt32.ofNat g) ↔ (h >>> 28 = UInt64.ofNat g) := by
  rw [decI_tag h hh]
  have hgt : (h >>> 28).toNat < 16 := by
    simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; omega
  constructor
  · intro e; apply UInt64.toNat_inj.mp
    have := congrArg UInt32.toNat e
    simp [UInt64.toNat_toUInt32] at this ⊢; omega
  · intro e; rw [e]; apply UInt32.toNat_inj.mp; simp

/-! ## An interning with a column -/

/-- The two halves of a `mkK`. -/
theorem mkK_split (A : ArrId) (c s x : Word) (r : Option (Word × Mem)) (w : Word) (m' : Mem)
    (h : mkK A c s x r = some (w, m')) :
    ∃ m₁, r = some (w, m₁) ∧ derPutW A c m₁ s w x = some m' := by
  match r, h with
  | some (w₁, m₁), h =>
    simp only [mkK] at h
    split at h
    · cases h
    · rename_i m₂ hp
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨m₁, rfl, hp⟩

/-- **The frame of an interning with a column**: the table's arrays, the column, the counts. -/
theorem mkK_internM_frame (S : Schema) (hS : S.WF) (A : ArrId) (hA : A ≠ CTL) (s x : Word) (m : Mem)
    (sk : Word) (pk : Word → Bool) (vs rs₀ rs₁ : List Word) {H : Mem → Word → Word → Word}
    (w : Word) (m' : Mem) (h : mkK A S.ca s x (internM S m sk pk vs rs₀ rs₁ H) = some (w, m')) :
    MemFrame [S.ra, S.sa, A] [S.ca, S.ca + 1] m m' := by
  obtain ⟨m₁, h₁, hp⟩ := mkK_split A S.ca s x _ w m' h
  exact (MemFrame.mono (internM_frame S hS m sk pk vs rs₀ rs₁ w m₁ h₁) (by simp) (fun _ h => h)).trans
    (MemFrame.mono (derPutW_frame A hA S.ca m₁ m' s w x hp) (by simp) (by simp))


/-- **The L model of an `intern_*` with a column**: `internM`, with the bit `x` written at the new
node's position `A[2 c + t]` after an append (`*_push` writes it last). -/
def internMD (S : Schema) (A : ArrId) (x : Word) (m : Mem) (sk : Word) (pk : Word → Bool)
    (vs rs₀ rs₁ : List Word) (H : Mem → Word → Word → Word) : Option (Word × Mem) :=
  if sk = 0 ∧ rs₀ = [] then none
  else if sk = 0 ∧ rs₀.headD 0 ≠ 0 then some (hdW S.tag.toUInt64 0 (rs₀.tail.headD 0), m)
  else if rdW (m.arr64 CTL) 1 ≠ 0 then
    if rs₁ = [] then none
    else if rs₁.headD 0 ≠ 0 then some (hdW S.tag.toUInt64 1 (rs₁.tail.headD 0), m)
    else if pk 1 then
      match growIf S.sa S.ca H m ((pushG S m 1 vs (rs₁.tail.tail.headD 0) (cntW S m 1)).set64 A
          (cntW S m 1 * 2 + 1) x) (cntW S m 1) with
      | some m' => some (hdW S.tag.toUInt64 1 (cntW S m 1), m')
      | none => none
    else none
  else if pk 0 then
    match growIf S.sa S.ca H m ((pushG S m 0 vs (rs₀.tail.tail.headD 0) (cntW S m 0)).set64 A
        (cntW S m 0 * 2 + 0) x) (cntW S m 0) with
    | some m' => some (hdW S.tag.toUInt64 0 (cntW S m 0), m')
    | none => none
  else none

theorem optMatch_some {o : Option Mem} {a w : Word} {m' : Mem}
    (h : (match o with | some m₁ => some (a, m₁) | none => none) = some (w, m')) : o = some m' := by
  cases o <;> simp_all

/-- **What an `intern_*` with a column changes**: the table's two arrays, the column, the counts. -/
theorem internMD_frame (S : Schema) (hS : S.WF) (A : ArrId) (hA : A ≠ CTL) (x : Word) (m : Mem)
    (sk : Word) (pk : Word → Bool) (vs rs₀ rs₁ : List Word) {H : Mem → Word → Word → Word}
    (w : Word) (m' : Mem) (h : internMD S A x m sk pk vs rs₀ rs₁ H = some (w, m')) :
    MemFrame [S.ra, S.sa, A] [S.ca, S.ca + 1] m m' := by
  have hp : ∀ t, t ≤ 1 → ∀ j m₂, growIf S.sa S.ca H m ((pushG S m t vs j (cntW S m t)).set64 A
      (cntW S m t * 2 + t) x) (cntW S m t) = some m₂ → MemFrame [S.ra, S.sa, A] [S.ca, S.ca + 1] m m₂ := by
    intro t ht j m₂ hg
    obtain ⟨g1, g2, g3⟩ := growIf_frame _ _ _ _ _ _ _ hg
    have hq := (MemFrame.mono (A' := [S.ra, S.sa, A]) (C' := [S.ca, S.ca + 1])
      (pushG_frame S hS m t ht vs j (cntW S m t)) (by simp) (fun _ h => h)).trans
      (MemFrame.mono (A' := [S.ra, S.sa, A]) (C' := [S.ca, S.ca + 1])
        (MemFrame.set64 (pushG S m t vs j (cntW S m t)) A hA (cntW S m t * 2 + t) x) (by simp) (by simp))
    refine ⟨fun b hb hc => ?_, fun y hy => ?_, fun b => (g2 b).trans (hq.2.2.1 b), g3.trans hq.2.2.2⟩
    · have : b ≠ S.sa := fun e => hb (by simp [e])
      rw [g1 b this]; exact hq.1 b hb hc
    · rw [g1 CTL hS.sa_ctl.symm]; exact hq.2.1 y hy
  simp only [internMD] at h
  repeat' split at h
  all_goals first
    | simp at h; done
    | (try simp only [Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨-, rfl⟩ := h
       first | exact MemFrame.refl _ _ _ | exact hp 0 (by decide) _ _ ‹_› |
         exact hp 1 (by decide) _ _ ‹_›)

theorem word_succ_ne (a : Word) : a + 1 ≠ a := by grind

theorem cnt2_pushG (S : Schema) (hS : S.WF) (m : Mem) (t : Word) (ht : t ≤ 1) (vs : List Word)
    (j : Word) (hctl : S.ca.toNat + 2 ≤ (m.arr64 CTL).size) :
    cnt2 (pushG S m t vs j (cntW S m t)) S.ca ≠ cnt2 m S.ca := by
  have hca := hS.ca
  rw [cnt2_eq, cnt2_eq]
  simp only [cntW]
  rw [pushG_ctl S hS _ _ _ _ _ ht, pushG_ctl S hS _ _ _ _ _ ht]
  rcases word_le_one t ht with rfl | rfl
  · have e1 : (S.ca + 0).toNat < (m.arr64 CTL).size := by simp; omega
    have ne : S.ca + 1 ≠ S.ca + 0 := by
      intro h; have := congrArg UInt64.toNat h; simp [UInt64.toNat_add] at this; omega
    simp only [e1, and_true, ite_true, ne, ite_false]
    grind
  · have e1 : (S.ca + 1).toNat < (m.arr64 CTL).size := by
      rw [UInt64.toNat_add]; simp; omega
    have ne : S.ca + 0 ≠ S.ca + 1 := by
      intro h; have := congrArg UInt64.toNat h; simp [UInt64.toNat_add] at this; omega
    simp only [e1, and_true, ite_true, ne, ite_false]
    grind

/-- **`internMD` is the library's interning followed by the `mk_*` tail** (`mkK`), given the
count words in `CTL` (`StoreR`), the append's room for the handle and the column, and a column
apart from the slots and the hash (the growth commutes with the column write). -/
theorem internMD_mkK (S : Schema) (hS : S.WF) (A : ArrId) (x : Word) (m : Mem) (sk : Word)
    (pk : Word → Bool) (vs rs₀ rs₁ : List Word) (H : Mem → Word → Word → Word)
    (hA : A ≠ S.sa) (hAc : A ≠ CTL) (hH : ∀ (m : Mem) (k x : Word) (t i : Word),
      H (m.set64 A k x) t i = H m t i)
    (hctl : S.ca.toNat + 2 ≤ (m.arr64 CTL).size)
    (hpk : ∀ t, t ≤ 1 → pk t = true →
      (cntW S m t).toNat < 2 ^ 27 ∧ cntW S m t * 2 + t < m.len64 A) :
    internMD S A x m sk pk vs rs₀ rs₁ H =
      mkK A S.ca (cnt2 m S.ca) x (internM S m sk pk vs rs₀ rs₁ H) := by
  have htag : S.tag.toUInt64.toNat < 16 := by have := hS.tag; simpa using this
  have hit : ∀ w, mkK A S.ca (cnt2 m S.ca) x (some (w, m)) = some (w, m) := fun w => by
    simp [mkK, derPutW]
  have push : ∀ t, t ≤ 1 → pk t = true → ∀ j,
      mkK A S.ca (cnt2 m S.ca) x (pushM S H m t vs j) =
      match growIf S.sa S.ca H m ((pushG S m t vs j (cntW S m t)).set64 A
          (cntW S m t * 2 + t) x) (cntW S m t) with
      | some m' => some (hdW S.tag.toUInt64 t (cntW S m t), m')
      | none => none := by
    intro t ht hp j
    obtain ⟨hc, hl⟩ := hpk t ht hp
    obtain ⟨hi, hti⟩ := idxW_hdW S.tag.toUInt64 t (cntW S m t) htag ht hc
    rw [growIf_set64 _ _ _ _ _ _ A _ x hA hAc (hH · _ x)]
    simp only [pushM]
    cases hg : growIf S.sa S.ca H m (pushG S m t vs j (cntW S m t)) (cntW S m t) with
    | none => rfl
    | some m₂ =>
      obtain ⟨g1, g2, -⟩ := growIf_frame _ _ _ _ _ _ _ hg
      have hcnt : cnt2 m₂ S.ca = cnt2 (pushG S m t vs j (cntW S m t)) S.ca := by
        simp only [cnt2, g1 CTL hS.sa_ctl.symm]
      have hl' : ¬ m₂.len64 A ≤ cntW S m t * 2 + t := by
        rw [len64_eq, g2, pushG_size, ← len64_eq]; exact UInt64.not_le.mpr hl
      simp only [Option.map, mkK, derPutW, hcnt, cnt2_pushG S hS m t ht vs j hctl, ite_false, hi,
        hti, hl']
  simp only [internMD, internM]
  split
  · rfl
  split
  · exact (hit _).symm
  split
  · split
    · rfl
    split
    · exact (hit _).symm
    split
    · rename_i hp; exact (push 1 (by decide) hp _).symm
    · rfl
  split
  · rename_i hp; exact (push 0 (by decide) hp _).symm
  · rfl

section colMk
variable {α δ : Type} {k : IdxKind} [BEq α] [Hashable α] [Inhabited δ] (S : Schema) (hS : S.WF)
  (R : Mem → Word → Word → α → Prop) (hsh : Mem → Word → Word → Word) (L : Lens α δ k)

include hS in
/-- **The column across an interning** (`DerRel.lean`'s `derMk` for any lens): after the library's
interning (`m` to `m₁`, the arena `a` to `a'`, result `r`) and `derPutW`, the column holds of `a'`
and `m'`, if the word written is `f` of the new record. -/
theorem colMk (A : ArrId) (f : δ → Word) (m m₁ m' : Mem) (a a' : AState) (key : α) (d : δ)
    (y : Idx k) (r dd : Word)
    (hT : StoreR S R hsh m (L.on a) (L.getP a) (L.getS a))
    (hT₁ : StoreR S R hsh m₁ (L.on a') (L.getP a') (L.getS a'))
    (hc : ColT2 L A f m a) (hfr : m₁.arr64 A = m.arr64 A)
    (hst : a' = a ∨
      (L.on a = false ∧ (L.getP a).nodes.size < 2 ^ 27 ∧
        y = decI (hdW S.tag.toUInt64 0 (UInt64.ofNat (L.getP a).nodes.size)) ∧
        a' = L.setP a ((L.getP a).push key d y)) ∨
      (L.on a = true ∧ (L.getS a).nodes.size < 2 ^ 27 ∧
        y = decI (hdW S.tag.toUInt64 1 (UInt64.ofNat (L.getS a).nodes.size)) ∧
        a' = L.setS a ((L.getS a).push key d y)))
    (hres : (decI r : Idx k) = y) (hdd : dd = f d)
    (hput : derPutW A S.ca m₁ (cnt2 m S.ca) r dd = some m') :
    ColT2 L A f m' a' := by
  have hfrA : ∀ i t, rdW (m₁.arr64 A) (UInt64.ofNat i * 2 + t) =
      rdW (m.arr64 A) (UInt64.ofNat i * 2 + t) := fun i t => by rw [hfr]
  have c0 := cnt_tier S R hsh m _ _ _ hT 0 (by decide)
  have c1 := cnt_tier S R hsh m _ _ _ hT 1 (by decide)
  have d0 := cnt_tier S R hsh m₁ _ _ _ hT₁ 0 (by decide)
  have d1 := cnt_tier S R hsh m₁ _ _ _ hT₁ 1 (by decide)
  simp only [ite_true, show (1 : Word) ≠ 0 by decide, ite_false] at c0 c1 d0 d1
  have b0 := hT.2.2.1.2.1
  have b1 := hT.2.2.2.1.2.1
  have htag := hS.tag
  rcases hst with rfl | ⟨hoff, hsz, hy, rfl⟩ | ⟨hon', hsz, hy, rfl⟩
  · have e : cnt2 m₁ S.ca = cnt2 m S.ca := by
      rw [cnt2_eq, cnt2_eq, UInt64.toNat_inj.mp (c0.trans d0.symm),
        UInt64.toNat_inj.mp (c1.trans d1.symm)]
    simp only [derPutW, e, ite_true, Option.some.injEq] at hput
    subst hput
    exact hc.frame hfr
  · rw [L.getP_setP] at d0
    rw [L.getS_setP] at d1
    have hpsz := (tbl_push_size (L.getP a) key d y).1
    have ne : cnt2 m₁ S.ca ≠ cnt2 m S.ca := by
      intro e
      rw [cnt2_eq, cnt2_eq] at e
      have e' := congrArg UInt64.toNat e
      rw [UInt64.toNat_add, UInt64.toNat_add, d0, d1] at e'
      simp only [hpsz] at e'
      have := (cntW S m 0).toNat_lt; have := (cntW S m 1).toNat_lt; omega
    obtain ⟨hi, ht⟩ := new_handleI r S.tag 0 _ htag (by decide) hsz (hres.trans hy)
    simp only [derPutW, ne, ite_false, hi, ht] at hput
    split at hput
    · cases hput
    rename_i hlen
    simp only [Option.some.injEq] at hput
    subst hput
    have hq : (UInt64.ofNat (L.getP a).nodes.size * 2 + 0).toNat < (m₁.arr64 A).size := by
      have h1 := UInt64.not_le.mp hlen
      rw [UInt64.lt_iff_toNat_lt, len64_eq, UInt64.toNat_ofNat'] at h1
      exact Nat.lt_of_lt_of_le h1 (Nat.mod_le _ _)
    have rd : ∀ i t, i < 2 ^ 27 → t ≤ 1 → (i ≠ (L.getP a).nodes.size ∨ t ≠ 0) →
        rdW ((m₁.set64 A (UInt64.ofNat (L.getP a).nodes.size * 2 + 0) dd).arr64 A)
          (UInt64.ofNat i * 2 + t) = rdW (m.arr64 A) (UInt64.ofNat i * 2 + t) := by
      intro i t hi ht hne
      rw [rdW_set64, ite_eq_right (fun h => ix_ne _ _ _ _ hsz hi (by decide) ht
        (hne.elim (fun h => .inl (Ne.symm h)) (fun h => .inr (Ne.symm h))) h.2.1), hfrA]
    refine ⟨?_, ?_⟩
    · rw [L.getP_setP]
      refine colT_push hc.1 key d y (fun i hi => rd i 0 (Nat.lt_trans hi hsz) (by decide) (.inl (Nat.ne_of_lt hi))) ?_
      rw [rdW_set64, ite_eq_left ⟨rfl, rfl, hq⟩, hdd]
    · rw [L.getS_setP]
      exact colT_mono hc.2 (fun i hi => rd i 1 (by omega) (by decide) (.inr (by decide)))
  · rw [L.getP_setS] at d0
    rw [L.getS_setS] at d1
    have hpsz := (tbl_push_size (L.getS a) key d y).1
    have ne : cnt2 m₁ S.ca ≠ cnt2 m S.ca := by
      intro e
      rw [cnt2_eq, cnt2_eq] at e
      have e' := congrArg UInt64.toNat e
      rw [UInt64.toNat_add, UInt64.toNat_add, d0, d1] at e'
      simp only [hpsz] at e'
      have := (cntW S m 0).toNat_lt; have := (cntW S m 1).toNat_lt; omega
    obtain ⟨hi, ht⟩ := new_handleI r S.tag 1 _ htag (by decide) hsz (hres.trans hy)
    simp only [derPutW, ne, ite_false, hi, ht] at hput
    split at hput
    · cases hput
    rename_i hlen
    simp only [Option.some.injEq] at hput
    subst hput
    have hq : (UInt64.ofNat (L.getS a).nodes.size * 2 + 1).toNat < (m₁.arr64 A).size := by
      have h1 := UInt64.not_le.mp hlen
      rw [UInt64.lt_iff_toNat_lt, len64_eq, UInt64.toNat_ofNat'] at h1
      exact Nat.lt_of_lt_of_le h1 (Nat.mod_le _ _)
    have rd : ∀ i t, i < 2 ^ 27 → t ≤ 1 → (i ≠ (L.getS a).nodes.size ∨ t ≠ 1) →
        rdW ((m₁.set64 A (UInt64.ofNat (L.getS a).nodes.size * 2 + 1) dd).arr64 A)
          (UInt64.ofNat i * 2 + t) = rdW (m.arr64 A) (UInt64.ofNat i * 2 + t) := by
      intro i t hi ht hne
      rw [rdW_set64, ite_eq_right (fun h => ix_ne _ _ _ _ hsz hi (by decide) ht
        (hne.elim (fun h => .inl (Ne.symm h)) (fun h => .inr (Ne.symm h))) h.2.1), hfrA]
    refine ⟨?_, ?_⟩
    · rw [L.getP_setS]
      exact colT_mono hc.1 (fun i hi => rd i 0 (by omega) (by decide) (.inr (by decide)))
    · rw [L.getS_setS]
      refine colT_push hc.2 key d y (fun i hi => rd i 1 (Nat.lt_trans hi hsz) (by decide) (.inl (Nat.ne_of_lt hi))) ?_
      rw [rdW_set64, ite_eq_left ⟨rfl, rfl, hq⟩, hdd]

end colMk

section colMkC
variable {α δ : Type} {k : IdxKind} [BEq α] [Hashable α] [Inhabited δ]

/-- **The column across an interning** (`consInternM`, any table with a column `A`): the column
holds of the arena state after and the memory after, if the word the push writes is `f` of the
new record. -/
theorem colMkC {C : ConsSch} (hW : C.WF) {A : ArrId} (hA : C.col = some A)
    {R : Mem → Word → Word → α → Prop} (L : Lens α δ k) (f : δ → Word)
    {m m' : Mem} {a a' : AState} {ks : List Word} {w : Word} {key : α} {d : δ} {y : Idx k}
    (hR : ConsR C R m (L.on a) (L.getP a) (L.getS a))
    (hR' : ConsR C R m' (L.on a') (L.getP a') (L.getS a'))
    (hc : ColT2 L A f m a) (hI : consInternM C m ks = some (w, m'))
    (hst : a' = a ∨
      (L.on a = false ∧ (L.getP a).nodes.size < 2 ^ 27 ∧
        y = decI (hdW C.tag.toUInt64 0 (UInt64.ofNat (L.getP a).nodes.size)) ∧
        a' = L.setP a ((L.getP a).push key d y)) ∨
      (L.on a = true ∧ (L.getS a).nodes.size < 2 ^ 27 ∧
        y = decI (hdW C.tag.toUInt64 1 (UInt64.ofNat (L.getS a).nodes.size)) ∧
        a' = L.setS a ((L.getS a).push key d y)))
    (hdd : C.colM m (pushArgs C ks (C.qhM m ks)) = f d) : ColT2 L A f m' a' := by
  obtain ⟨-, hAsa, -, -⟩ := hW.col A hA
  have c0 := hR.cnt 0 (by decide)
  have c1 := hR.cnt 1 (by decide)
  have d0 := hR'.cnt 0 (by decide)
  have d1 := hR'.cnt 1 (by decide)
  have k0 := hR.cap 0 (by decide)
  have k1 := hR.cap 1 (by decide)
  simp only [ite_true, show (1 : Word) ≠ 0 by decide, ite_false] at c0 c1 d0 d1 k0 k1
  have hp0 := (tbl_push_size (L.getP a) key d y).1
  have hp1 := (tbl_push_size (L.getS a) key d y).1
  rcases consInternM_out hW hI with rfl | ⟨t, ht, hok, -, he, -, -⟩
  · rcases hst with rfl | ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩
    · exact hc
    · rw [L.getP_setP] at d0; omega
    · rw [L.getS_setS] at d1; omega
  have hcm : ∀ t', t' ≤ 1 → cntC C m' t' = if t' = t then cntC C m t + 1 else cntC C m t' := by
    intro t' ht'
    rw [show cntC C m' t' = cntC C (pushRec C m t ks) t' by
      simp only [cntC, he CTL hW.sch.sa_ctl.symm]]
    exact pushRec_cnt C hW m t ht ks hR.ctl t' ht'
  have hAm := pushRec_col C hW hA m t ks
  rw [← he A hAsa] at hAm
  have hq := hW.colRoom A hA m t ht hok
  have hc27 : (cntC C m t).toNat < 2 ^ 27 := by
    simp only [pushOKC, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.1
  have hsucc : (cntC C m t + 1).toNat = (cntC C m t).toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  have hct : cntC C m t = UInt64.ofNat (cntC C m t).toNat := (UInt64.ofNat_toNat).symm
  -- reads of the column after the append
  have rd : ∀ i t', i < 2 ^ 27 → t' ≤ 1 → (i ≠ (cntC C m t).toNat ∨ t' ≠ t) →
      rdW (m'.arr64 A) (UInt64.ofNat i * 2 + t') = rdW (m.arr64 A) (UInt64.ofNat i * 2 + t') := by
    intro i t' hi ht' hne
    rw [hAm, rdW_set!]
    have := ix_ne _ _ _ _ hc27 hi ht ht' (hne.elim (fun h => .inl (Ne.symm h)) (fun h => .inr (Ne.symm h)))
    rw [← hct] at this
    exact if_neg (fun h => this (UInt64.toNat_inj.mp h.1))
  have rdn : rdW (m'.arr64 A) (UInt64.ofNat (cntC C m t).toNat * 2 + t) = f d := by
    rw [hAm, rdW_set!, ← hct, if_pos ⟨rfl, hq⟩, hdd]
  rcases word_le_one t ht with rfl | rfl
  · have e0 := hcm 0 (by decide)
    have e1 := hcm 1 (by decide)
    simp only [ite_true, show (1 : Word) ≠ 0 by decide, ite_false] at e0 e1
    rcases hst with rfl | ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩
    · rw [e0, hsucc] at d0; omega
    · rw [L.getP_setP] at d0
      simp only [ColT2, L.getP_setP, L.getS_setP]
      refine ⟨colT_push hc.1 key d y (fun i hi => rd i 0 (by omega) (by decide) (.inl (by omega))) ?_,
        colT_mono hc.2 (fun i hi => rd i 1 (by omega) (by decide) (.inr (by decide)))⟩
      rw [← c0]; exact rdn
    · rw [L.getS_setS, e1] at d1; omega
  · have e0 := hcm 0 (by decide)
    have e1 := hcm 1 (by decide)
    simp only [ite_true, show (0 : Word) ≠ 1 by decide, ite_false] at e0 e1
    rcases hst with rfl | ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩
    · rw [e1, hsucc] at d1; omega
    · rw [L.getP_setP, e0] at d0; omega
    · rw [L.getS_setS] at d1
      simp only [ColT2, L.getP_setS, L.getS_setS]
      refine ⟨colT_mono hc.1 (fun i hi => rd i 0 (by omega) (by decide) (.inr (by decide))),
        colT_push hc.2 key d y (fun i hi => rd i 1 (by omega) (by decide) (.inl (by omega))) ?_⟩
      rw [← c1]; exact rdn

end colMkC

end L.Arena
