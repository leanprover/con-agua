module

import ConAgua.Front.IndApplyRefine2
public import ConAgua.Front.IndApplySpec2
public import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Front.ApplyDeclRefine
import ConAgua.Front.ApplyExprRefine
import ConAgua.Front.IndApplyRefine
public import ConAgua.Front.IndRel
public import ConAgua.Front.StateDR

@[expose] public section

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
    m'.arr64 A = m.arr64 A := h.frame.1 A (by simp [h1]) (TieredArray.t0_ne h2)

theorem PExt.size {m m' : Mem} (h : PExt m m') (A : ArrId) : (m'.arr64 A).size = (m.arr64 A).size :=
  h.frame.size A

/-- A write at an index above the top keeps a `PExt`. -/
theorem PExt.set {m m' : Mem} (h : PExt m m') (i v : Word) (hi : topN m DLP < i.toNat)
    (ht : 0 < i.toNat) : PExt m (m'.set64 DLP i v) :=
  ⟨h.frame.trans (MemFrame.set64 _ _ (by decide) _ _), by
    have := h.top; simp only [topN, wd_setA]
    rw [ite_eq_right (by omega)]; exact this, fun j h1 h2 => by
      rw [wd_setA, ite_eq_right (by omega)]; exact h.keep j h1 h2⟩

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
  rw [ite_eq_right (by omega), ite_eq_left (by omega)]


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
  ⟨h.names.frame hf (.inl rfl) (by simp [DLP, idArrs, NID, LID, EID, NIDS, LIDS, EIDS]) (by simp),
    h.exprs.frame hf (.inr (.inr rfl)) (by simp [DLP, idArrs, NID, LID, EID, NIDS, LIDS, EIDS]) (by simp), by rw [hf.size]; exact h.psize,
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
    (hw : w.toNat < 2 ^ 32) : (hd? (aread a) i : Option (Idx k)) = some (decI w) := by
  sorry

/-- A constant value from its words (handles below `2^32`). -/
theorem decCV_of {a : Array Word} {q : Nat} {wn wt s ll : Word} {f : Nat → Word}
    (h0 : a[q]? = some wn) (hn : wn.toNat < 2 ^ 32) (h1 : a[q + 1]? = some s)
    (h2 : a[q + 2]? = some ll) (h3 : a[q + 3]? = some wt) (ht : wt.toNat < 2 ^ 32)
    (hs : ∀ j < ll.toNat, a[s.toNat + j]? = some (f j) ∧ (f j).toNat < 2 ^ 32) :
    decCV (aread a) q = some ⟨decI wn, (List.range ll.toNat).map (fun j => decI (f j)), decI wt⟩ := by
  sorry

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
      (∀ P : Nat → Option Word, (∀ i, (q.toNat ≤ i ∧ i < q.toNat + 4) ∨ (topN m DLP < i ∧ i ≤ topN m' DLP) →
        P i = some (wd m' DLP i)) → decCV P q.toNat = some cvp) := by
  sorry

end L.Front.Ind
