import ConAgua.Arena.ConsLibRel
import ConAgua.Arena.LpCol
import Std.Tactic.BVDecide.Normalize.Prop
set_option linter.unusedSectionVars false

/-!
# The level-parameter columns: the relation, generically (helper `whnf4-d23`)

A table with a column (`LpCol.lean`) relates node `i` of tier `t` to the word `A[2 i + t] =
f (derAt i)`, `f` the bit of the derived record as a word (`b2w ∘ (·.hasParam)` for levels and
level lists, `b2w ∘ lpOfData` for expressions): `ColT`, both tiers behind a lens `ColT2`. A table
whose bit is a constant (`zero`, `param`) has the arena-only `ConstT2`. Both also say that the
derived array is as long as the node array (con-ron's `StoreWF` clause), so that `derAt i` of a
node is the pushed record and not the `default`.

An `intern_*` with a column is the library's `consInternM` of a schema with a column
(`ConsSch.col`): on an append the push writes the new node's bit. `colMkC`/`constMk` carry the
column across it (`DerRel.lean`'s `derMk`, for any lens).
-/

open ConRon.Arena ConLeche


namespace L.Arena

/-! ## Moved here from `DerRel.lean` (generic in the table) -/

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
    (h : derPutW A c m₁ s r d = some m') : MemFrame [A, A + 256] [] m₁ m' := by
  unfold derPutW at h
  split at h
  · cases h; exact MemFrame.refl _ _ _
  split at h
  · cases h
  · cases h
    rcases tierA_cases' A (tierW r) with e | e <;> rw [e]
    · exact (MemFrame.set64 m₁ A hA _ _).mono (by simp) (by simp)
    · exact (MemFrame.set64 m₁ _ (by simp [CTL]) _ _).mono (by simp) (by simp)

/-- **The frame of a `mk_*`**: the interning's arrays and counts, then the derived column `A`. -/
theorem mkK_frame {C : ConsSch} (hW : C.WF) {A : ArrId} (hA : A ≠ CTL) {c s d r : Word}
    {m m' : Mem} {ks : List Word} (h : mkK A c s d (consInternM C m ks) = some (r, m')) :
    MemFrame (C.wset ++ [A, A + 256]) [C.ca, C.ca + 1] m m' := by
  rcases hI : consInternM C m ks with _ | ⟨r₁, m₁⟩ <;> rw [hI] at h
  · cases h
  rcases hP : derPutW A c m₁ s r₁ d with _ | m₂ <;> simp only [mkK_some, hP, reduceCtorEq] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact ((consInternM_frame hW hI).mono (by simp_all) (by simp)).trans
    ((derPutW_frame A hA c _ _ _ _ _ hP).mono (by simp) (by simp))

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

theorem word_succ_ne (a : Word) : a + 1 ≠ a := by grind

theorem cnt2_eq (C : ConsSch) (m : Mem) : cnt2 m C.ca = cntC C m 0 + cntC C m 1 := by
  simp [cnt2, cntC]

/-! ## Handles of any kind -/

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

/-- The column write of an append is in bounds, as `toNat` (`ConsSch.WF.colRoom`): `c` below the
length of tier `t`'s column array. -/
theorem colRoom_of (m : Mem) (A : ArrId) (c t : Word) (h2 : c < m.len64 (tierA A t)) :
    c.toNat < (m.arr64 (tierA A t)).size := by
  rw [UInt64.lt_iff_toNat_lt, len64_eq, UInt64.toNat_ofNat'] at h2
  exact Nat.lt_of_lt_of_le h2 (Nat.mod_le _ _)

/-! ## The relations -/

section col
variable {α δ : Type} {k : IdxKind} [BEq α] [Hashable α] [Inhabited δ]

/-- **One tier's column**: as many derived records as nodes, and node `i`'s word `A⟨t⟩[i]` is `f`
of its derived record. -/
def ColT (A : ArrId) (f : δ → Word) (m : Mem) (t : Word) (tb : Tbl α (Idx k) δ) : Prop :=
  tb.der.size = tb.nodes.size ∧
    ∀ i x, tb.nodes[i]? = some x → rdW (m.arr64 (tierA A t)) (UInt64.ofNat i) = f (tb.derAt i)

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
    (he : ∀ i, i < tb.nodes.size → rdW (m'.arr64 (tierA A t)) (UInt64.ofNat i) =
      rdW (m.arr64 (tierA A t)) (UInt64.ofNat i)) : ColT A f m' t tb := by
  refine ⟨h.1, fun i x hx => ?_⟩
  have hi : i < tb.nodes.size := (Array.getElem?_eq_some_iff.mp hx).1
  rw [he i hi]; exact h.2 i x hx

/-- **A column survives a writer that keeps its arrays** (both tiers). -/
theorem ColT2.frame {L : Lens α δ k} {A : ArrId} {f : δ → Word} {m m' : Mem} {a : AState}
    (h : ColT2 L A f m a) (he : m'.arr64 A = m.arr64 A) (he' : m'.arr64 (A + 256) = m.arr64 (A + 256)) :
    ColT2 L A f m' a :=
  ⟨colT_mono h.1 (fun _ _ => by simp only [tierA_zero, he]),
    colT_mono h.2 (fun _ _ => by simp only [tierA_one, he'])⟩

/-- `ColT2.frame` across a `MemFrame` that avoids the column (both tiers). -/
theorem ColT2.frameM {L : Lens α δ k} {A : ArrId} {f : δ → Word} {Ar : List ArrId} {C : List Word}
    {m m' : Mem} {a : AState} (h : ColT2 L A f m a) (hf : MemFrame Ar C m m') (hA : A ∉ Ar)
    (hA' : A + 256 ∉ Ar) (hc : A ≠ CTL) : ColT2 L A f m' a :=
  h.frame (hf.1 A hA hc) (hf.1 _ hA' (by simp [CTL]))

theorem tbl_push_size (tb : Tbl α (Idx k) δ) (key : α) (d : δ) (y : Idx k) :
    (tb.push key d y).nodes.size = tb.nodes.size + 1 ∧ (tb.push key d y).der.size = tb.der.size + 1 := by
  cases tb; simp [Tbl.push]

/-- A node of an appended table: the new one (its record `d`) or an old one (its old record). -/
theorem tbl_push_get {tb : Tbl α (Idx k) δ} (hs : tb.der.size = tb.nodes.size) (key : α) (d : δ)
    (y : Idx k) {i : Nat} {x : α} (hx : (tb.push key d y).nodes[i]? = some x) :
    (i = tb.nodes.size ∧ (tb.push key d y).derAt i = d) ∨
      (tb.nodes[i]? = some x ∧ i < tb.nodes.size ∧ (tb.push key d y).derAt i = tb.derAt i) := by
  have hp : (tb.push key d y).nodes = tb.nodes.push key ∧ (tb.push key d y).der = tb.der.push d := by
    cases tb; exact ⟨rfl, rfl⟩
  simp only [Tbl.derAt, hp.2]
  rw [hp.1, Array.getElem?_push] at hx
  split at hx
  · rename_i hi'; subst hi'; exact .inl ⟨rfl, by simp [Array.getD, ← hs]⟩
  · have hi : i < tb.nodes.size := (Array.getElem?_eq_some_iff.mp hx).1
    have hi' : i < tb.der.size := by rw [hs]; exact hi
    refine .inr ⟨hx, hi, ?_⟩
    simp [Array.getD, hi', Array.getElem_push_lt hi'] <;> intro h <;> omega

/-- An append keeps the column if the new word is the new record's. -/
theorem colT_push {A : ArrId} {f : δ → Word} {m m' : Mem} {t : Word} {tb : Tbl α (Idx k) δ}
    (h : ColT A f m t tb) (key : α) (d : δ) (y : Idx k)
    (he : ∀ i, i < tb.nodes.size → rdW (m'.arr64 (tierA A t)) (UInt64.ofNat i) =
      rdW (m.arr64 (tierA A t)) (UInt64.ofNat i))
    (hn : rdW (m'.arr64 (tierA A t)) (UInt64.ofNat tb.nodes.size) = f d) :
    ColT A f m' t (tb.push key d y) := by
  obtain ⟨hpn, hpd⟩ := tbl_push_size tb key d y
  refine ⟨by rw [hpn, hpd, h.1], fun i x hx => ?_⟩
  rcases tbl_push_get h.1 key d y hx with ⟨rfl, e⟩ | ⟨hx', hi, e⟩
  · rw [e, hn]
  · rw [e, he i hi, h.2 i x hx']

/-- An append keeps a constant bit if the new record has it. -/
theorem constT_push {pr : δ → Prop} {tb : Tbl α (Idx k) δ} (h : ConstT pr tb) (key : α) (d : δ)
    (y : Idx k) (hd : pr d) : ConstT pr (tb.push key d y) := by
  obtain ⟨hpn, hpd⟩ := tbl_push_size tb key d y
  refine ⟨by rw [hpn, hpd, h.1], fun i x hx => ?_⟩
  rcases tbl_push_get h.1 key d y hx with ⟨rfl, e⟩ | ⟨hx', -, e⟩
  · rw [e]; exact hd
  · rw [e]; exact h.2 i x hx'

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
theorem col_read {α δ : Type} {k : IdxKind} [BEq α] [Hashable α] [Inhabited δ] {C : ConsSch}
    {R : Mem → Word → Word → α → Prop} (A : ArrId) (f : δ → Word)
    (m : Mem) (on : Bool) (P Q : Tbl α (Idx k) δ) (hT : ConsR C R m on P Q)
    (hc0 : ColT A f m 0 P) (hc1 : ColT A f m 1 Q) (hf0 : f default = 0) (t i : Word) (ht : t ≤ 1) :
    (if i < rdW (m.arr64 CTL) (C.ca + t) then rdW (m.arr64 (tierA A t)) i else 0) =
      f ((if t = 0 then P else Q).derAt i.toNat) := by
  have hcnt := hT.cnt t ht
  have hc : ColT A f m t (if t = 0 then P else Q) := by
    rcases word_le_one t ht with rfl | rfl
    · simpa using hc0
    · simpa using hc1
  simp only [cntC] at hcnt
  split
  · rename_i hlt
    have hi : i.toNat < (if t = 0 then P else Q).nodes.size := by
      rw [← hcnt]; exact UInt64.lt_iff_toNat_lt.mp hlt
    have := hc.2 i.toNat _ (Array.getElem?_eq_getElem hi)
    simpa only [UInt64.ofNat_toNat] using this
  · rename_i hge
    rw [derAt_out hc.1 _ (by rw [← hcnt]; exact UInt64.not_lt.mp hge |> UInt64.le_iff_toNat_le.mp), hf0]

/-- **A constant bit with the count check.** -/
theorem const_read {α δ : Type} {k : IdxKind} [BEq α] [Hashable α] [Inhabited δ] {C : ConsSch}
    {R : Mem → Word → Word → α → Prop} (f : δ → Word) (v : Word)
    (m : Mem) (on : Bool) (P Q : Tbl α (Idx k) δ) (hT : ConsR C R m on P Q)
    (hc0 : ConstT (fun d => f d = v) P) (hc1 : ConstT (fun d => f d = v) Q) (hf0 : f default = 0)
    (t i : Word) (ht : t ≤ 1) :
    (if i < rdW (m.arr64 CTL) (C.ca + t) then v else 0) = f ((if t = 0 then P else Q).derAt i.toNat) := by
  have hcnt := hT.cnt t ht
  have hc : ConstT (fun d => f d = v) (if t = 0 then P else Q) := by
    rcases word_le_one t ht with rfl | rfl
    · simpa using hc0
    · simpa using hc1
  simp only [cntC] at hcnt
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
      simp only [cntC, he CTL (hW.sch.sa_ctl' t).symm]]
    exact pushRec_cnt C hW m t ht ks hR.ctl t' ht'
  have hAl := hW.colLt A hA
  have hAm := pushRec_col C hW hA m t ks
  rw [← he _ (tierA_ne hAl hW.sch.sa_lt hAsa t t)] at hAm
  have hq := hW.colRoom A hA m t ht hok
  have hc27 : (cntC C m t).toNat < 2 ^ 27 := by
    simp only [pushOKC, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.1
  have hsucc : (cntC C m t + 1).toNat = (cntC C m t).toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  have hct : cntC C m t = UInt64.ofNat (cntC C m t).toNat := (UInt64.ofNat_toNat).symm
  -- reads of the column after the append: tier `t`'s array has the new word, the other tier's
  -- array is untouched
  have rd : ∀ i, i < 2 ^ 27 → i ≠ (cntC C m t).toNat →
      rdW (m'.arr64 (tierA A t)) (UInt64.ofNat i) = rdW (m.arr64 (tierA A t)) (UInt64.ofNat i) := by
    intro i hi hne
    rw [hAm, rdW_set!]
    refine ite_eq_right (fun h => hne ?_)
    have := h.1
    rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)] at this
    exact this.symm
  have rdn : rdW (m'.arr64 (tierA A t)) (UInt64.ofNat (cntC C m t).toNat) = f d := by
    rw [hAm, rdW_set!, ← hct, ite_eq_left ⟨rfl, hq⟩, hdd]
  have rdo : ∀ t', t' ≤ 1 → t' ≠ t → m'.arr64 (tierA A t') = m.arr64 (tierA A t') := by
    intro t' ht' hne
    rw [he _ (tierA_ne hAl hW.sch.sa_lt hAsa t' t), pushRec,
      colW_arr C _ _ _ _ _ (fun A' hA' => by
        rw [hA] at hA'; cases hA'; exact tierA_ne_tier _ ht ht' (Ne.symm hne)),
      Mem.arr64_set64_ne _ _ _ _ _ (by
        simpa using (tierA_ne hAl (show CTL < 256 by decide) (hW.col A hA).2.2.1 t' 0)),
      wrRecK_eq, wrRec_arr_ne C.sch _ _ _ (tierA_ne hAl hW.sch.ra_lt (hW.col A hA).1 t' t)]
  rcases word_le_one t ht with rfl | rfl
  · have e0 := hcm 0 (by decide)
    have e1 := hcm 1 (by decide)
    simp only [ite_true, show (1 : Word) ≠ 0 by decide, ite_false] at e0 e1
    rcases hst with rfl | ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩
    · rw [e0, hsucc] at d0; omega
    · rw [L.getP_setP] at d0
      simp only [ColT2, L.getP_setP, L.getS_setP]
      refine ⟨colT_push hc.1 key d y (fun i hi => rd i (by omega) (by omega)) ?_,
        colT_mono hc.2 (fun i hi => by rw [rdo 1 (by decide) (by decide)])⟩
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
      refine ⟨colT_mono hc.1 (fun i hi => by rw [rdo 0 (by decide) (by decide)]),
        colT_push hc.2 key d y (fun i hi => rd i (by omega) (by omega)) ?_⟩
      rw [← c1]; exact rdn

end colMkC

end L.Arena
