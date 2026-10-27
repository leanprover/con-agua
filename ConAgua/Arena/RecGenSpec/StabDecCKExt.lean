import ConAgua.Arena.RecGenSpec.SlRGrow
import ConAgua.Arena.RecStab

/-!
# StabDecCKExt

`perturb`, `iwN_set_word`, `word_succ_ne`, `stab_decCK_ext`, `decCK_lt_size`, `decCS_some_cases` and the lemmas only they use.
-/

set_option experimental.vcgen true

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

theorem decCK_lt_size {m : Mem} {k : Nat} {ck : ClassKey} (h : decCK m k = some ck) : k < (m.arr64 IW).size := by
  simp only [decCK, bind, Option.bind_eq_some_iff] at h
  obtain ⟨c, hc, -⟩ := h
  obtain ⟨w, hw, -, -⟩ := hd?_some hc
  exact (Array.getElem?_eq_some_iff.mp hw).1

theorem decCS_some_cases {m : Mem} {p : Nat} {s : ClassSlot} (h : decCS m p = some s) :
    (iwN m p = some 0 ∧ ∃ kp k, iwN m (p + 1) = some kp ∧ decCK m kp = some k ∧ s = .motive k) ∨
    (iwN m p = some 1 ∧ ∃ c, iwN m (p + 1) = some c ∧ ∃ cc ihs, s = .minor c cc ihs) := by
  simp only [decCS, bind, Option.bind_eq_some_iff] at h
  obtain ⟨t, ht, h⟩ := h
  rcases t with _ | _ | t
  · left
    simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨kp, hkp, k, hk, rfl⟩ := h
    exact ⟨ht, kp, k, hkp, hk, rfl⟩
  · right
    simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨c, hc, cc, hcc, ihs, hihs, rfl⟩ := h
    exact ⟨ht, c, hc, cc, ihs, rfl⟩
  · simp at h

/-- **A stably decoding class slot lies below the top**, and so does a motive's key. -/
theorem stab_decCS_ext {m : Mem} {sp : Nat} {slot : ClassSlot} (h : StabD (fun m => decCS m sp) m slot)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    sp + 2 ≤ iwTop m ∧ ∀ kp, iwN m sp = some 0 → iwN m (sp + 1) = some kp → CKExt m kp := by
  have h0 := h.get
  have hs1 : sp + 1 < iwTop m := by
    rcases Nat.lt_or_ge (sp + 1) (iwTop m) with hlt | hge
    · exact hlt
    exfalso
    rcases decCS_some_cases h0 with ⟨ht, kp, k, hkp, hk, rfl⟩ | ⟨ht, c, hc, cc, ihs, rfl⟩
    · obtain ⟨w, hw, -⟩ := iwN_set_word hkp
      have hil := (Array.getElem?_eq_some_iff.mp hw).1
      obtain ⟨hg, hset, hother⟩ := perturb hge hil hsz (UInt64.ofNat (2 ^ 64 - 1))
      have ht' : iwN (m.set64 IW (UInt64.ofNat (sp + 1)) (UInt64.ofNat (2 ^ 64 - 1))) sp = some 0 := by
        simp only [iwN, nat?, iwA]; rw [hother _ (by omega)]; simpa [iwN, nat?, iwA] using ht
      rcases decCS_some_cases (h _ hg) with ⟨-, kp', k', hkp', hk', -⟩ | ⟨ht'', -⟩
      · have e : iwN (m.set64 IW (UInt64.ofNat (sp + 1)) (UInt64.ofNat (2 ^ 64 - 1))) (sp + 1) =
            some (2 ^ 64 - 1) := by simp only [iwN, nat?, iwA]; rw [hset]; rfl
        rw [e] at hkp'; cases hkp'
        have h1 := decCK_lt_size hk'
        have h2 : ((m.set64 IW (UInt64.ofNat (sp + 1)) (UInt64.ofNat (2 ^ 64 - 1))).arr64 IW).size =
            (m.arr64 IW).size := (set64IW_frame m _ _).2.2.1 IW
        omega
      · rw [ht'] at ht''; cases ht''
    · obtain ⟨w, hw, rfl⟩ := iwN_set_word hc
      have hil := (Array.getElem?_eq_some_iff.mp hw).1
      obtain ⟨hg, hset, hother⟩ := perturb hge hil hsz (w + 1)
      have ht' : iwN (m.set64 IW (UInt64.ofNat (sp + 1)) (w + 1)) sp = some 1 := by
        simp only [iwN, nat?, iwA]; rw [hother _ (by omega)]; simpa [iwN, nat?, iwA] using ht
      have h1 := h _ hg
      rcases decCS_some_cases h1 with ⟨ht'', -⟩ | ⟨-, c', hc', cc', ihs', heq⟩
      · rw [ht'] at ht''; cases ht''
      · have e : iwN (m.set64 IW (UInt64.ofNat (sp + 1)) (w + 1)) (sp + 1) = some (w + 1).toNat := by
          simp only [iwN, nat?, iwA]; rw [hset]; rfl
        rw [e] at hc'; cases hc'
        simp only [ClassSlot.minor.injEq] at heq
        exact word_succ_ne w heq.1.symm
  refine ⟨by omega, fun kp ht hkp => ?_⟩
  rcases decCS_some_cases h0 with ⟨-, kp', k, hkp', hk, rfl⟩ | ⟨ht', -⟩
  · rw [hkp] at hkp'; cases hkp'
    refine stab_decCK_ext (ck := k) (fun m' hg => ?_) hsz
    have h1 := h m' hg
    have e0 : iwN m' sp = some 0 := by rw [iwN_grow hg (by omega)]; exact ht
    have e1 : iwN m' (sp + 1) = some kp := by rw [iwN_grow hg hs1]; exact hkp
    rcases decCS_some_cases h1 with ⟨-, kp'', k'', hkp'', hk'', heq⟩ | ⟨ht'', -⟩
    · rw [e1] at hkp''; cases hkp''
      simp only [ClassSlot.motive.injEq] at heq
      rw [← heq] at hk''; exact hk''
    · rw [e0] at ht''; cases ht''
  · rw [ht] at ht'; cases ht'

end L.Ind
