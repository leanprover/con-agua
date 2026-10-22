import ConAgua.Arena.InferBodySpineF

/-!
# The binder telescopes: `infer_lams`, `infer_pis`, their leaves, `infer_lam`, `infer_forall`

The telescopes keep two stacks growing in step: the free variables `fvs` on the spine stack `SPN`
(array 144, top `CTL[136]`; `SpineR`) and the second list `stk` on the binder stack `BSTK`
(array 145, top `CTL[137]`; `BStkR`, a slice of words). `CoreS` survives writes to both
(`CoreS.frame_stk`, `CoreS.frame`).

**What the callees must keep.** `CoreAfter` (lane `whnf`'s `StackKept`) says nothing about
`BSTK`: a knot slot run inside the telescope could, as far as its spec goes, overwrite the binder
stack below its top. The telescopes assume it of the callees they call while the stack holds
entries (`BStkCallees`: `infer`, `whnf`, `inst_list`, `ar_entry`, `ensure_sort` keep `BSTK` below
`CTL[137]`, and `CTL[137]`); the interning callees are proved to (their frames, `BKept.of_frame`).
Discharging `BStkCallees` needs `StackKept` (or `CoreAfter`) to carry the binder stack, which every
core body would then prove (DESIGN.md).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

namespace L.Arena

/-! ## The binder stack -/

/-- The binder stack's top. -/
def bTop (m : Mem) : Word := rdW (m.arr64 CTL) 137

/-- **A slice of the binder stack**, as words. -/
structure BStkR (m : Mem) (lo k : Word) (ws : Array Word) : Prop where
  size : ws.size = k.toNat
  bound : lo.toNat + k.toNat ≤ (m.arr64 BSTK).size
  get : ∀ (i : Nat) (h : i < ws.size), ws[i] = rdW (m.arr64 BSTK) (lo + i.toUInt64)

/-- The binder stack below its top is kept, and so is the top. -/
def BKept (m m' : Mem) : Prop :=
  bTop m' = bTop m ∧ (m'.arr64 BSTK).size = (m.arr64 BSTK).size ∧
    ∀ j : Word, j < bTop m → rdW (m'.arr64 BSTK) j = rdW (m.arr64 BSTK) j

theorem BKept.refl (m : Mem) : BKept m m := ⟨rfl, rfl, fun _ _ => rfl⟩

theorem BKept.trans {m₁ m₂ m₃ : Mem} (h₁ : BKept m₁ m₂) (h₂ : BKept m₂ m₃) : BKept m₁ m₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, fun j hj => (h₂.2.2 j (h₁.1 ▸ hj)).trans (h₁.2.2 j hj)⟩

theorem BKept.of_frame {m m' : Mem} {A : List ArrId} {C : List Word} (hf : MemFrame A C m m')
    (hA : BSTK ∉ A) (hC : (137 : Word) ∉ C) : BKept m m' := by
  have hb : m'.arr64 BSTK = m.arr64 BSTK := hf.1 BSTK hA (by decide)
  exact ⟨hf.2.1 137 hC, by rw [hb], fun j _ => by rw [hb]⟩

/-- **The callees a telescope calls while its binder stack holds entries keep it.** -/
def BStkCallees (p : Prog) : Prop :=
  ∀ (n : Nat) (f : FnName) (vs : List Word) (m : Mem) (r : List Word) (m' : Mem),
    (f = "infer" ∨ f = "whnf" ∨ f = "inst_list" ∨ f = "ar_entry" ∨ f = "ensure_sort") →
    callW p n f vs m = some (r, m') → BKept m m'

theorem BStkR.keep {m m' : Mem} {lo k : Word} {ws : Array Word} (h : BStkR m lo k ws)
    (hK : BKept m m') (htop : lo.toNat + k.toNat ≤ (bTop m).toNat)
    (hsz : (m.arr64 BSTK).size < 2 ^ 63) : BStkR m' lo k ws := by
  have hb := h.bound
  refine ⟨h.size, hK.2.1 ▸ hb, fun i hi => ?_⟩
  have hi' : i < k.toNat := h.size ▸ hi
  have hlt : lo + i.toUInt64 < bTop m := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_ofNat']
    have : i % 2 ^ 64 = i := Nat.mod_eq_of_lt (by omega)
    rw [this, Nat.mod_eq_of_lt (by omega)]; omega
  rw [hK.2.2 _ hlt]; exact h.get i hi

theorem BStkR.empty (m : Mem) (lo : Word) (h : lo.toNat ≤ (m.arr64 BSTK).size) : BStkR m lo 0 #[] :=
  ⟨rfl, by simpa using h, fun i hi => by simp at hi⟩

theorem BStkR.push {m : Mem} {lo k : Word} {ws : Array Word} (h : BStkR m lo k ws)
    (hcap : (m.arr64 BSTK).size < 2 ^ 63) (hb : (lo + k).toNat < (m.arr64 BSTK).size) (v : Word) :
    BStkR (m.set64 BSTK (lo + k) v) lo (k + 1) (ws.push v) := by
  have hsz := h.bound
  have hsize := h.size
  have h1 : (1 : Word).toNat = 1 := by decide
  have hoc : (lo + k).toNat = lo.toNat + k.toNat := by simp only [UInt64.toNat_add]; omega
  have hcnt1 : (k + 1).toNat = k.toNat + 1 := by simp only [UInt64.toNat_add, h1]; omega
  have hidx : ∀ i : Nat, i ≤ k.toNat → (lo + (i.toUInt64 : Word)).toNat = lo.toNat + i := by
    intro i hi
    simp only [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
  have heqv : lo + (k.toNat.toUInt64 : Word) = lo + k :=
    UInt64.toNat_inj.mp (by rw [hidx k.toNat (by omega), hoc])
  refine ⟨by rw [Array.size_push, h.size, hcnt1], by rw [size_set64L, hcnt1]; omega, fun i hi => ?_⟩
  rw [Array.size_push, h.size] at hi
  rw [rdW_set64]
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hi'
  · rw [Array.getElem_push, dif_pos (by rw [h.size]; exact hi'), h.get i (by rw [h.size]; exact hi')]
    rw [if_neg]
    rintro ⟨-, hco, -⟩
    have := congrArg UInt64.toNat hco
    rw [hidx i (by omega), hoc] at this
    omega
  · have hieq : i = k.toNat := hi'
    subst hieq
    rw [Array.getElem_push, dif_neg (by omega), heqv, if_pos ⟨rfl, rfl, hb⟩]

theorem BStkR.frame {m m' : Mem} {lo k : Word} {ws : Array Word} (h : BStkR m lo k ws)
    (hb : m'.arr64 BSTK = m.arr64 BSTK) : BStkR m' lo k ws :=
  ⟨h.size, hb ▸ h.bound, fun i hi => by rw [hb]; exact h.get i hi⟩

end L.Arena
