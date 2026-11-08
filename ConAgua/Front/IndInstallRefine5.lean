module

import ConAgua.Front.IndInstallRefine4
import ConAgua.Front.IndApplyRefine5
import ConAgua.Front.IndInstallRefine3
public import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Front.ApplyDeclRefine
import ConAgua.Front.IndApplyRefine
public import ConAgua.Front.IndInstallRefine2

@[expose] public section

/-!
# `install_ind_d` refines `installIndD`, V: the block

`installW_twin`: `install_ind_d` (after `validate_ind_d`) against the twin's `installIndD`: the
block's slots and constant records in `DLP`, above the old top, pushed as one `DECL` record of kind
`6`; the result is the twin's state with the `indDecl` pushed (`StateDR`, `IndDeclAt` with `t` the
final top), the arena untouched (`ArenaD`).
-/

open L.Arena
open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend (IndCtorRec IndTypeRec IndRecRec CVRec RuleRec)


namespace L.Front.Ind

instance : Inhabited IndTypeRec := ⟨⟨⟨0, [], 0⟩, [], false, false, false, 0, 0, 0⟩⟩
instance : Inhabited IndRecRec := ⟨⟨⟨0, [], 0⟩, false, false, 0, 0, 0, 0, []⟩⟩

theorem CVF.congr {b : ByteArray} {m m' : Mem} {p : Nat} {cv : CVRec} (h : m'.arr64 IFR = m.arr64 IFR)
    (hF : CVF b m p cv) : CVF b m' p cv := by
  unfold CVF wd at *; rw [h]; exact hF

theorem CtF.congr {b : ByteArray} {m m' : Mem} {p : Nat} {ct : IndCtorRec} (h : m'.arr64 IFR = m.arr64 IFR)
    (hF : CtF b m p ct) : CtF b m' p ct := by
  unfold CtF CVF OptW NumW wd at *; rw [h]; exact hF

theorem RecF.congr {b : ByteArray} {m m' : Mem} {p : Nat} {rc : IndRecRec} (h : m'.arr64 IFR = m.arr64 IFR)
    (h' : m'.arr64 IFL = m.arr64 IFL) (hF : RecF b m p rc) : RecF b m' p rc := by
  unfold RecF RuleF CVF BoolW NumW topN wd at *; rw [h, h']; exact hF

theorem ofNat_toNat_lt (k : Nat) (h : k < 2 ^ 64) : (UInt64.ofNat k).toNat = k :=
  UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)

theorem getElem!_eq {α : Type} [Inhabited α] (l : List α) (k : Nat) (h : k < l.length) : l[k]! = l[k] :=
  getElem!_pos l k h

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- A memory from which a frame keeps the words outside `[lo, hi)` below the top keeps a slot outside
it and a record above `hi`. -/
theorem slot_keep {m m' : Mem} {lo hi : Nat}
    (ht : topN m DLP ≤ topN m' DLP)
    (hk : ∀ i, 1 ≤ i → i ≤ topN m DLP → (i < lo ∨ hi ≤ i) → wd m' DLP i = wd m DLP i)
    {s : Nat} (hs1 : 1 ≤ s) (hs2 : s ≤ topN m DLP) (hs : s < lo ∨ hi ≤ s)
    {ci : IConstantInfo} (hhi : 1 ≤ hi) (hp : hi ≤ (wd m DLP s).toNat) (hr : RecAt m (wd m DLP s).toNat ci) :
    wd m' DLP s = wd m DLP s ∧ RecAt m' (wd m' DLP s).toNat ci := by
  have e := hk s hs1 hs2 hs
  refine ⟨e, ?_⟩
  rw [e]
  exact hr.keep ht (fun i h1 h2 => hk i (by omega) h2 (.inr (by omega)))
-/

theorem block_get {α : Type} [Inhabited α] (A B C : List α) (j : Nat) :
    (A ++ B ++ C)[j]! = if j < A.length then A[j]! else if j < A.length + B.length then B[j - A.length]!
      else C[j - A.length - B.length]! := by
  rw [List.append_assoc]
  by_cases h1 : j < A.length
  · rw [ite_eq_left h1, getElem!_pos (A ++ (B ++ C)) j (by simp; omega), getElem!_pos A j h1,
      List.getElem_append_left h1]
  · rw [ite_eq_right h1]
    by_cases h2 : j < A.length + B.length
    · rw [ite_eq_left h2, getElem!_pos (A ++ (B ++ C)) j (by simp; omega), getElem!_pos B (j - A.length) (by omega),
        List.getElem_append_right (by omega), List.getElem_append_left (by omega)]
    · rw [ite_eq_right h2]
      by_cases h3 : j < A.length + B.length + C.length
      · rw [getElem!_pos (A ++ (B ++ C)) j (by simp; omega), getElem!_pos C (j - A.length - B.length) (by omega),
          List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
      · rw [getElem!_neg (A ++ (B ++ C)) j (by simp; omega), getElem!_neg C (j - A.length - B.length) (by omega)]

theorem getElem?_of_wd {m m' : Mem} {j : Nat} (hs : (m'.arr64 DLP).size = (m.arr64 DLP).size)
    (hj : j < (m.arr64 DLP).size) (h : wd m' DLP j = wd m DLP j) : (m'.arr64 DLP)[j]? = (m.arr64 DLP)[j]? := by
  rw [wd_some _ _ _ (by omega), wd_some _ _ _ hj, h]

/-- **`install_ind_d` refines `installIndD`.** -/
@[refines ConRon.Arena.Frontend.installIndD]
theorem installW_twin {b : ByteArray} {n : Nat} {m m' : Mem} {a : AState} {st : StateD}
    (hA : ArenaD m a) (hD : StateDR m st)
    {to tn co cn ro rn oo np : Word} {tys : List IndTypeRec} {cts : List IndCtorRec}
    {rcs : List IndRecRec} {ordered : List IndCtorRec}
    (hF : IndFR b m to tn co cn ro rn tys cts rcs) (hIFR : topN m IFR < 2 ^ 62)
    (hIFL : topN m IFL < 2 ^ 62) (hord : ordered.length = cts.length)
    (hoo : oo.toNat + cts.length < 2 ^ 63)
    (hptr : ∀ p (hp : p < ordered.length), ∃ k, ∃ _ : k < cts.length,
      wd m IFL (oo.toNat + p) = co + 10 * UInt64.ofNat k ∧ ordered[p] = cts[k])
    (h : installW n b.data m to tn oo cn ro rn np = some m') :
    ∃ st', (ConRon.Arena.Frontend.installIndD st tys ordered rcs np.toNat).run a = .ok (st', a) ∧
      ArenaD m' a ∧ StateDR m' st' ∧ MemFrame [DLP, DECL] [] m m' := by
  sorry

end L.Front.Ind
