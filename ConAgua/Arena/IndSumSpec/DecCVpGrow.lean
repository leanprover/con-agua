module

public import ConAgua.Arena.IndView
import ConRon.Bridge.Grind
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr

@[expose] public section

/-!
# DecCVpGrow

`decCVp_grow`, `hd?_rdW`, `getSort_of_get`, `viewSort_of_view`, `eViewW_head2` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Constant values read from `EREC` below its top -/

theorem decCVp_grow {m m' : Mem} (hg : IWGrow m m') {cq : Nat} (_hcq : cq + 4 ≤ erTop m)
    (_hsl : ∀ lo ll, nat? (erA m) (cq + 1) = some lo → nat? (erA m) (cq + 2) = some ll →
      lo + ll ≤ erTop m ∨ ll = 0) {cv : IConstantVal} (h : decCVp m cq = some cv) :
    decCVp m' cq = some cv :=
  hg.erecGrow.ext.decCV h

/-- A record's handle field, as the word L reads. -/
theorem hd?_rdW {k : IdxKind} {a : Array Word} {i : Nat} {x : Idx k} (h : hd? (aread a) i = some x)
    (hi : i < 2 ^ 64) : ∃ w, rdW a (UInt64.ofNat i) = w ∧ w.toNat < 2 ^ 32 ∧ decI w = x := by
  simp only [hd?, aread_apply] at h
  cases hw : a[i]? with
  | none => simp [hw] at h
  | some w =>
    simp only [hw] at h
    by_cases hl : w.toNat < 2 ^ 32
    · simp [hl] at h
      have hiw : (UInt64.ofNat i).toNat = i := by simp; omega
      exact ⟨w, by simp [rdW, hiw, hw], hl, h⟩
    · simp [hl] at h

/-! ## `check_sum_tele` -/

theorem getSort_of_get (t : ETables) (i : EIdx) (u : LIdx) (ht : i.tag = ETag.sort)
    (h : t.get i = some (.sort u)) : t.getSort i = some u := by
  unfold ETables.get at h
  rw [ht] at h
  simp only [show (ETag.sort == ETag.bvar) = false by decide,
    show (ETag.sort == ETag.fvar) = false by decide, show (ETag.sort == ETag.sort) = true by decide,
    ite_true, ite_false, Bool.false_eq_true] at h
  unfold ETables.getSort
  cases e : t.sorts.node? i.idxNat with
  | none => rw [e] at h; cases h
  | some r => rw [e] at h; simp at h; simp [h]

theorem viewSort_of_view (st : EStore) (i : EIdx) (u : LIdx) (ht : i.tag = ETag.sort)
    (h : st.view i = some (.sort u)) : st.viewSort i = some u := by
  unfold EStore.view at h; unfold EStore.viewSort EStore.persGetSort
  split at h
  · rw [ite_eq_left (by assumption)]; exact getSort_of_get _ _ _ ht h
  · rw [ite_eq_right (by assumption)]
    split at h
    · rw [ite_eq_left (by assumption)]; exact getSort_of_get _ _ _ ht h
    · cases h

theorem eViewW_head2 (m : Mem) (h : Word) (hg : tagW h = 2) (hne : eViewW m h ≠ []) :
    (eViewW m h).headD 0 = 2 := by
  revert hne; unfold eViewW
  simp only [hg, show ((2 : Word) = 0) = False from by decide, show ((2 : Word) = 1) = False from by decide,
    ite_false, ite_true]
  repeat' split
  all_goals simp

theorem viewSort_run {a : AState} {h : EIdx} {u : Option LIdx} (hv : a.store.viewSort h = u) :
    (viewSort h).run a = .ok (u, a) := by
  simp [viewSort, hv, StateT.run_get]; rfl

end L.Ind

end
