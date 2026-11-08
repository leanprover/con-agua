module

public import ConAgua.Arena.IndPartsSpec.BpcW
import ConAgua.Arena.IndPartsSpec.BsW
import ConAgua.Arena.IndGrindAttr
public import ConAgua.Arena.IndDecStab

@[expose] public section

/-!
# PartsSliceCopy

`erCopyW_zero`, `partsErLt`, `partsHslice_last`, `partsErToIw_zero`, `partsSliceCopy`, `partsLpsCopy` and the lemmas only they use.
-/


/-!
# Refinements of `IndParts`, part 13 (lane `indproofs2`, helper `parts`): `blockShape?`'s pins

The reserved-name and level-parameter pins (`block_shape_pins_formers`/`_recs`/`_ctors`/`_ok`,
pure in the twin: one `Bool`), and the eliminator (`block_shape_large`). Shared pieces: a constant's
level parameters copied by `er_to_iw` (`partsLpsCopy`), `reserved_contains` against the twin's
`reservedBasisNames` (`partsResCont`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## A constant's level parameters, copied -/

theorem erCopyW_zero (n : Nat) (m : Mem) (d o o' : Word) : erCopyW n m d o 0 = erCopyW n m d o' 0 := by
  cases n <;> rfl

theorem partsErLt {m : Mem} {i v : Nat} (h : nat? (erA (truncM m)) i = some v) : i < erTop m := by
  simp only [nat?, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, -⟩ := h; exact (truncM_er_get hx).1

theorem partsHslice_last {k : IdxKind} {a : Array Word} : ∀ (l o : Nat) (xs : List (Idx k)),
    hslice? (aread a) o (l + 1) = some xs → ∃ w, a[o + l]? = some w
  | 0, o, xs, h => by
    rw [hslice?_succ] at h
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, -⟩ := h
    obtain ⟨w, hw, -, -⟩ := hd?_some hx
    exact ⟨w, by simpa using hw⟩
  | l + 1, o, xs, h => by
    rw [hslice?_succ] at h
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, -, ys, hys, -⟩ := h
    obtain ⟨w, hw⟩ := partsHslice_last l (o + 1) ys hys
    exact ⟨w, by rw [show o + (l + 1) = o + 1 + l by omega]; exact hw⟩

theorem partsErToIw_zero (n : Nat) (m : Mem) (o : Word) : erToIwW n m o 0 = erToIwW n m 0 0 := by
  simp only [erToIwW]
  rcases allocW m 0 with _ | ⟨q, m1⟩
  · rfl
  · simp only; rw [erCopyW_zero _ _ _ o 0]

/-- **`er_to_iw` of an `EREC` handle slice decoded below the tops.** -/
theorem partsSliceCopy {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m m' : Mem} {o l : Word} {r : List Word} {xs : List NIdx} (h : erToIwW n m o l = some (r, m'))
    (hS : StageR vis fe m a) (hs : hslice? (erA (truncM m)) o.toNat l.toNat = some xs) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some xs ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
  sorry

/-- `er_to_iw` of a constant's level-parameter slice (decoded below the tops), as a handle slice. -/
theorem partsLpsCopy {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m m' : Mem} {q : Nat} {cv : IConstantVal} {r : List Word}
    (h : erToIwW n m (rdW (m.arr64 EREC) (UInt64.ofNat q + 1)) (rdW (m.arr64 EREC) (UInt64.ofNat q + 2)) =
      some (r, m'))
    (hS : StageR vis fe m a) (hcv : DecB (fun m => decCVp m q) m cv) (hq : q < 2 ^ 64) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some cv.levelParams ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
  sorry

section arms
variable (n : Nat) (m m1 : Mem) (cto ctl lo ll cv b e : Word) (rp : List Word)
theorem bpfW_nil (h : ctl = 0) : bpfW (n + 1) m cto ctl lo ll = some ([1], m) := by simp [bpfW, h]
theorem bpfW_cons (h : ctl ≠ 0) : bpfW (n + 1) m cto ctl lo ll = bpfK1 n cto ctl lo ll (rdW (m.arr64 IW) cto) m
    (resContW n m (rdW (m.arr64 EREC) (rdW (m.arr64 IW) cto))) := by simp [bpfW, h]
theorem bpfK1_res (h : b ≠ 0) : bpfK1 n cto ctl lo ll cv m (some b) = some ([0], m) := by
  simp only [bpfK1]; exact ite_eq_left h
theorem bpfK1_ok (h : ¬ b ≠ 0) : bpfK1 n cto ctl lo ll cv m (some b) =
    bpfK2 n cto ctl lo ll (erToIwW n m (rdW (m.arr64 EREC) (cv + 1)) (rdW (m.arr64 EREC) (cv + 2))) := by
  simp only [bpfK1]; exact ite_eq_right h
theorem bpfK2_some : bpfK2 n cto ctl lo ll (some (rp, m1)) =
    bpfK3 n cto ctl lo ll m1 (eqW n m1 (rp.headD 0) (rp.tail.headD 0) lo ll) := by simp [bpfK2]
theorem bpfK3_ne (h : e = 0) : bpfK3 n cto ctl lo ll m1 (some e) = some ([0], m1) := by
  simp only [bpfK3]; exact ite_eq_left h
theorem bpfK3_eq (h : ¬ e = 0) : bpfK3 n cto ctl lo ll m1 (some e) =
    pinK4 (bpfW n m1 (cto + 1) (ctl - 1) lo ll) := by simp only [bpfK3]; exact ite_eq_right h
theorem pinK4_some : pinK4 (some (rp, m1)) = some ([rp.headD 0], m1) := rfl
end arms
attribute [ind_grind] bpfW_nil bpfW_cons bpfK1_res bpfK1_ok bpfK2_some bpfK3_ne bpfK3_eq pinK4_some

section arms
variable (n : Nat) (m m1 : Mem) (nP cso csl lo ll cv b e : Word) (rp : List Word)
theorem bpcW_nil (h : csl = 0) : bpcW (n + 1) m nP cso csl lo ll = some ([1], m) := by simp [bpcW, h]
theorem bpcW_np (h : csl ≠ 0) (h2 : rdW (m.arr64 IW) (rdW (m.arr64 IW) cso + 1) ≠ nP) :
    bpcW (n + 1) m nP cso csl lo ll = some ([0], m) := by simp [bpcW, h, h2]
theorem bpcW_cons (h : csl ≠ 0) (h2 : ¬ rdW (m.arr64 IW) (rdW (m.arr64 IW) cso + 1) ≠ nP) :
    bpcW (n + 1) m nP cso csl lo ll = bpcK1 n nP cso csl lo ll (rdW (m.arr64 IW) (rdW (m.arr64 IW) cso)) m
      (resContW n m (rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) cso)))) := by
  simp only [bpcW]; rw [ite_eq_right h, ite_eq_right h2]
theorem bpcK1_res (h : b ≠ 0) : bpcK1 n nP cso csl lo ll cv m (some b) = some ([0], m) := by
  simp only [bpcK1]; exact ite_eq_left h
theorem bpcK1_ok (h : ¬ b ≠ 0) : bpcK1 n nP cso csl lo ll cv m (some b) =
    bpcK2 n nP cso csl lo ll (erToIwW n m (rdW (m.arr64 EREC) (cv + 1)) (rdW (m.arr64 EREC) (cv + 2))) := by
  simp only [bpcK1]; exact ite_eq_right h
theorem bpcK2_some : bpcK2 n nP cso csl lo ll (some (rp, m1)) =
    bpcK3 n nP cso csl lo ll m1 (eqW n m1 (rp.headD 0) (rp.tail.headD 0) lo ll) := by simp [bpcK2]
theorem bpcK3_ne (h : e = 0) : bpcK3 n nP cso csl lo ll m1 (some e) = some ([0], m1) := by
  simp only [bpcK3]; exact ite_eq_left h
theorem bpcK3_eq (h : ¬ e = 0) : bpcK3 n nP cso csl lo ll m1 (some e) =
    pinK4 (bpcW n m1 nP (cso + 1) (csl - 1) lo ll) := by simp only [bpcK3]; exact ite_eq_right h
end arms
attribute [ind_grind] bpcW_nil bpcW_np bpcW_cons bpcK1_res bpcK1_ok bpcK2_some bpcK3_ne bpcK3_eq

end L.Ind

end
