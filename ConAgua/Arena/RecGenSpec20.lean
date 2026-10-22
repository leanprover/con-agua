import ConAgua.Arena.RecGenSpec19

/-!
# `checkBlockClasses` (lane `indproofs3`, helper `indproofs3-pos-cls`)

`class_read`'s slots decode stably (`StabD`, `SPL`); `class_read_classes` and the keys' readers need
them below the pool's top. **A stable decoding lies below the top**: a word it reads above the top
could be changed by a pool growth (`IWGrow` constrains only the words below the top), and changing
it changes the decoding (`stab_decCK_ext`, `stab_decCS_ext`, by such a perturbation).
-/

set_option experimental.vcgen true
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Perturbations above the top -/

/-- Writing a word at or above the top is a pool growth. -/
theorem perturb {m : Mem} {i : Nat} (hi : iwTop m ≤ i) (hil : i < (m.arr64 IW).size)
    (hsz : (m.arr64 IW).size < 2 ^ 64) (v : Word) :
    IWGrow m (m.set64 IW (UInt64.ofNat i) v) ∧ ((m.set64 IW (UInt64.ofNat i) v).arr64 IW)[i]? = some v ∧
      ∀ j, j ≠ i → ((m.set64 IW (UInt64.ofNat i) v).arr64 IW)[j]? = (m.arr64 IW)[j]? := by
  have hie : (UInt64.ofNat i : Word).toNat = i := UInt64.toNat_ofNat_of_lt' (show i < 2 ^ 64 by omega)
  refine ⟨(IWGrow.refl m).set_iw _ v (by rw [hie]; exact hi), ?_, fun j hj => ?_⟩
  · rw [set64IW_get, hie]; simp [hil]
  · rw [set64IW_get, hie]; simp [hj]

theorem iwN_set_word {m : Mem} {i : Nat} {v : Nat} (h : iwN m i = some v) :
    ∃ w : Word, (m.arr64 IW)[i]? = some w ∧ w.toNat = v := by
  simp only [iwN, nat?, iwA, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h; exact ⟨w, hw, rfl⟩

theorem word_succ_ne (w : Word) : (w + 1).toNat ≠ w.toNat := by
  intro h
  rw [UInt64.toNat_add] at h
  have := w.toNat_lt
  simp at h; omega

/-- **A stably decoding class key lies below the top** (`CKExt`). -/
theorem stab_decCK_ext {m : Mem} {k : Nat} {ck : ClassKey} (h : StabD (fun m => decCK m k) m ck)
    (hsz : (m.arr64 IW).size < 2 ^ 64) : CKExt m k := by
  have h0 := h.get
  have hgetN : ∀ {m : Mem}, decCK m k = some ck → ∃ c u o l : Nat, iwN m (k + 2) = some o ∧
      iwN m (k + 3) = some l ∧ decHL m o l = some ck.ds ∧ (iwH m k : Option NIdx) = some ck.ind ∧
      (iwH m (k + 1) : Option LsIdx) = some ck.lvls ∧ c = c ∧ u = u := by
    intro m hm
    simp only [decCK, decAt, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hm
    obtain ⟨c, hc, u, hu, ds, ⟨o, ho, l, hl, hds⟩, rfl⟩ := hm
    exact ⟨0, 0, o, l, ho, hl, hds, hc, hu, rfl, rfl⟩
  obtain ⟨-, -, o, l, ho, hl, hds, -, -, -, -⟩ := hgetN h0
  -- the length word lies below the top
  have hk3 : k + 3 < iwTop m := by
    rcases Nat.lt_or_ge (k + 3) (iwTop m) with hlt | hge
    · exact hlt
    exfalso
    obtain ⟨w, hw, rfl⟩ := iwN_set_word hl
    have hil := (Array.getElem?_eq_some_iff.mp hw).1
    obtain ⟨hg, hset, hother⟩ := perturb hge hil hsz (w + 1)
    obtain ⟨-, -, o', l', ho', hl', hds', -, -, -, -⟩ := hgetN (h _ hg)
    have e : iwN (m.set64 IW (UInt64.ofNat (k + 3)) (w + 1)) (k + 3) = some (w + 1).toNat := by
      simp only [iwN, nat?, iwA]; rw [hset]; rfl
    rw [e] at hl'; cases hl'
    have e1 := decHL_length _ hds; have e2 := decHL_length _ hds'
    exact word_succ_ne w (by omega)
  refine ⟨by omega, fun o' l' ho' hl' => ?_⟩
  rw [ho] at ho'; rw [hl] at hl'; cases ho'; cases hl'
  rcases Nat.eq_zero_or_pos l with hl0 | hpos
  · exact Or.inr hl0
  left
  rcases Nat.lt_or_ge (o + l - 1) (iwTop m) with hlt | hge
  · omega
  exfalso
  have hlast := decHL_getI hds (l - 1) (by omega)
  rw [show o + (l - 1) = o + l - 1 by omega] at hlast
  obtain ⟨w, hw, hwH, hwd⟩ := hd?_some hlast
  simp only [iwA] at hw
  have hil := (Array.getElem?_eq_some_iff.mp hw).1
  obtain ⟨hg, hset, hother⟩ := perturb hge hil hsz (w + 1)
  obtain ⟨-, -, o', l', ho', hl', hds', -, -, -, -⟩ := hgetN (h _ hg)
  have e2 : iwN (m.set64 IW (UInt64.ofNat (o + l - 1)) (w + 1)) (k + 2) = some o := by
    simp only [iwN, nat?, iwA]; rw [hother _ (by omega)]; simpa [iwN, nat?, iwA] using ho
  have e3 : iwN (m.set64 IW (UInt64.ofNat (o + l - 1)) (w + 1)) (k + 3) = some l := by
    simp only [iwN, nat?, iwA]; rw [hother _ (by omega)]; simpa [iwN, nat?, iwA] using hl
  rw [e2] at ho'; rw [e3] at hl'; cases ho'; cases hl'
  have hlast' := decHL_getI hds' (l - 1) (by omega)
  rw [show o + (l - 1) = o + l - 1 by omega] at hlast'
  obtain ⟨w', hw', hwH', hwd'⟩ := hd?_some hlast'
  simp only [iwA] at hw'
  rw [hset] at hw'; cases hw'
  have : (decI w : EIdx) = decI (w + 1) := by
    first | exact hwd.symm.trans hwd' | exact hwd.trans hwd'.symm | exact hwd.symm.trans hwd'.symm | exact hwd.trans hwd'
  exact word_succ_ne w (congrArg UInt64.toNat ((clsDecI_inj hwH hwH').mp this).symm)

end L.Ind
