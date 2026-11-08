module

public import ConAgua.Arena.RecGenSpec.SlRGrow
public import ConAgua.Arena.RecStab
import ConAgua.Arena.IndInstallSpec.DomsW
public import ConAgua.Arena.RecClassSpec.Classes

@[expose] public section

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
  sorry

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
  sorry

end L.Ind
