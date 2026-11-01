module

public import ConAgua.Arena.IlpRd
import ConAgua.Arena.RecCheckSpec.TruncSl
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.Arena.IndPosSpec.InstW
import ConAgua.Arena.IndSim
import ConAgua.Arena.RecClassSpec.CloseLams
public import ConAgua.Arena.IndDecStab
public import ConAgua.Arena.RecCheckSpec.RcLook

@[expose] public section

/-!
# DecTMSlices

What `class_ctor_of`'s refinement reads: `decTM_slices`, `decB_decPL_bound`, `tcW_mfr`, `instW_ok0`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Reading the records -/

/-- A `TargetMajor` decoded below the tops: its entries' slice (words 9, 10) and its parameters'
slice (words 2, 3). -/
theorem decTM_slices {m : Mem} {mw : Word} {M : TargetMajor} (h : DecB (fun m => decTM m mw.toNat) m M)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    (∃ o l : Nat, rdW (m.arr64 IW) (mw + 9) = UInt64.ofNat o ∧ rdW (m.arr64 IW) (mw + 10) = UInt64.ofNat l ∧
      o < 2 ^ 64 ∧ l < 2 ^ 64 ∧ DecB (fun m => decPL m (decNCN m) o l) m M.nfs) ∧
    HSl0 m (rdW (m.arr64 IW) (mw + 2)) (rdW (m.arr64 IW) (mw + 3)) M.ds ∧ mw.toNat + 13 < 2 ^ 64 := by
  have h' : decTM (truncM m) mw.toNat = some M := h
  simp only [decTM, bind, Option.bind_eq_some_iff, pure] at h'
  obtain ⟨i, hi, lv, hlv, ds, hds, nPc, hnPc, nIdx, hnIdx, ctors, hctors, mem, hmem, nfs, hnfs, pf, hpf, hM⟩ := h'
  cases hM
  obtain ⟨o, l, ho, hl, hd⟩ := decAt_some hnfs
  obtain ⟨o2, l2, ho2, hl2, hd2⟩ := decAt_some hds
  obtain ⟨o3, l3, ho3, hl3, -⟩ := decAt_some hpf
  obtain ⟨h12, -⟩ := rec2IwN_trunc hl3
  obtain ⟨-, ho'⟩ := rec2IwN_trunc ho
  obtain ⟨-, hl'⟩ := rec2IwN_trunc hl
  have r9 := iwN_rdW_at (w := mw) (k := 9) ho' hsz
  have r10 := iwN_rdW_at (w := mw) (k := 10) (by simpa [Nat.add_assoc] using hl') hsz
  refine ⟨⟨o, l, by simpa using r9.1, by simpa using r10.1, r9.2, r10.2, hd⟩, ?_, by
    have := (rdW (m.arr64 CTL) 200).toNat_lt; simp only [iwTop] at h12; omega⟩
  have := truncSl (w := mw) (i := 2) ho2 (by simpa [Nat.add_assoc] using hl2) hd2 hsz
  simpa using this

/-- A pointer slice decoded below the tops is empty or below the top. -/
theorem decB_decPL_bound {α : Type} {f : Mem → Nat → Option α} {m : Mem} {o l : Nat} {xs : List α}
    (h : DecB (fun m => decPL m (f m) o l) m xs) : l = 0 ∨ o + l ≤ iwTop m := by
  rcases Nat.eq_zero_or_pos l with h0 | h0
  · exact .inl h0
  right
  obtain ⟨v, hv, -⟩ := decPL_getH (truncM m) (show decPL (truncM m) (f (truncM m)) o l = some xs from h) (l - 1) (by omega)
  have := (rec2IwN_trunc hv).1
  omega

/-- `target_ctor_at` writes no walk memo. -/
theorem tcW_mfr {cR : CallM} {n : Nat} (hF : IlpFr cR) {m m' : Mem} {M c : Word} {r : List Word}
    (h : tcW cR n m M c = some (r, m')) : MFr [] [] m m' := by
  simp only [tcW] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.refl _ _ _
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h rfl
  simp only [tcK1] at h
  refine (posmemo_cvLpsW_mfr h1).trans ?_
  obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h rfl
  simp only [tcK2, Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.2]
  obtain ⟨A, C, hA, hC, hfr⟩ := hF _ _ _ _ _ h2
  exact MFr.of_frame hfr hA hC

/-- `inst_pis_with` with its arguments a slice below the top unless empty. -/
theorem instW_ok0 (n : Nat) {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {vis : Word} {m m' : Mem}
    {a : AState} {ao al e : Word} {args : List EIdx} {r : List Word} (h : instW n m ao al e = some (r, m'))
    (hS : StageR dn vis fe m a) (he : H e) (hsl : HSl0 m ao al args) :
    ∃ x a', (ConRon.Arena.instPisWith args (decI e)).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ decOE m' r x := by
  rcases hsl.2 with h0 | hb
  · subst h0
    have : args = [] := by have := decHL_length _ hsl.1; simpa using this
    subst this
    rcases n with _ | n
    · simp [instW] at h
    rw [instW_nil (h := rfl)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨some (decI e), a, rfl, hS, IWGrow.refl _, rfl, he, rfl⟩
  · exact instW_ok n dn fe vis m m' a ao al e args r h hS he hsl.1 (hS.lt64 hb) hb

end L.Ind

end
