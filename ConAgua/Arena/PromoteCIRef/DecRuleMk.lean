import ConAgua.Arena.IndInstallSpec.Frame
import ConAgua.Arena.PromoteCIInfra

/-!
# DecRuleMk

`decFire`, `decRule_fire`, `decRule_mk`, `SlotGrow`, `SlotGrow.of_grow`, `SlotGrow.toGrow` and the lemmas only they use.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## The firing mode of a rule record -/

/-- The firing mode of the rule record at `q` (`decRule`'s `fire`). -/
def decFire (a : Array Word) (q : Nat) : Option IRecRuleFire := do
  match ← nat? a (q + 3) with
  | 0 => some IRecRuleFire.plain
  | 1 => some (IRecRuleFire.nested (← hlist? a (q + 4)) (← hlist? a (q + 6)))
  | _ => none

theorem decRule_fire {a : Array Word} {q : Nat} {rl : IRecRule} (h : decRule a q = some rl) :
    decFire a q = some rl.fire := by
  unfold decRule at h
  unfold decFire
  cases hk : nat? a (q + 3) with
  | none => simp [hk] at h
  | some k =>
    simp only [hk, Option.bind_eq_bind, Option.bind_some] at h ⊢
    rcases k with _ | _ | k
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, h⟩ := h
      cases h; rfl
    · simp only [Option.bind_eq_some_iff] at h ⊢
      obtain ⟨l1, hl1, l2, hl2, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ := h
      cases h
      exact ⟨l1, hl1, l2, hl2, rfl⟩
    · simp at h

/-- Assemble a rule record from its words. -/
theorem decRule_mk {a : Array Word} {q : Nat} {c : NIdx} {nf cpar : Nat} {fire : IRecRuleFire}
    {kb eb : Bool} {rh : EIdx}
    (hc : hd? a q = some c) (hnf : nat? a (q + 1) = some nf) (hcp : nat? a (q + 2) = some cpar)
    (hf : decFire a q = some fire) (hr : hd? a (q + 8) = some rh) (hk : bool? a (q + 9) = some kb)
    (he : bool? a (q + 10) = some eb) :
    decRule a q = some ⟨c, nf, cpar, fire, rh, kb, eb⟩ := by
  unfold decRule
  unfold decFire at hf
  cases hk3 : nat? a (q + 3) with
  | none => simp [hk3] at hf
  | some t =>
    simp only [hk3, Option.bind_eq_bind, Option.bind_some] at hf ⊢
    rcases t with _ | _ | t
    · simp only [Option.some.injEq] at hf
      subst hf
      simp [hc, hnf, hcp, hr, hk, he]
    · simp only [Option.bind_eq_some_iff, Option.some.injEq] at hf
      obtain ⟨l1, hl1, l2, hl2, rfl⟩ := hf
      simp [hl1, hl2, hc, hnf, hcp, hr, hk, he]
    · simp at hf

/-! ## Slots -/

/-- **The pool grew and only the words `[lo, hi)` below the old top changed.** -/
def SlotGrow (m m' : Mem) (lo hi : Nat) : Prop :=
  erecTop m ≤ erecTop m' ∧
    (∀ i, i < erecTop m → (i < lo ∨ hi ≤ i) → (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
    (m'.arr64 EREC).size = (m.arr64 EREC).size

theorem SlotGrow.of_grow {m m' : Mem} (h : ErecGrow m m') (lo hi : Nat) : SlotGrow m m' lo hi :=
  ⟨h.1, fun i hi _ => h.2.1 i hi, h.2.2⟩

/-- A grow whose slot lies above the old top is a plain growth. -/
theorem SlotGrow.toGrow {m m' : Mem} {lo hi : Nat} (h : SlotGrow m m' lo hi)
    (hlo : erecTop m ≤ lo) : ErecGrow m m' :=
  ⟨h.1, fun i hi => h.2.1 i hi (Or.inl (by omega)), h.2.2⟩

/-- Two slot growths of nested slots compose: the second slot lies inside the first,
or the second growth is a plain one. -/
theorem SlotGrow.trans {m₁ m₂ m₃ : Mem} {lo hi lo' hi' : Nat} (h₁ : SlotGrow m₁ m₂ lo hi)
    (h₂ : SlotGrow m₂ m₃ lo' hi') (hl : lo ≤ lo') (hh : hi' ≤ hi) : SlotGrow m₁ m₃ lo hi := by
  refine ⟨Nat.le_trans h₁.1 h₂.1, fun i hi1 hi2 => ?_, h₂.2.2.trans h₁.2.2⟩
  rw [h₂.2.1 i (by have := h₁.1; omega) (by omega), h₁.2.1 i hi1 hi2]

theorem arenaD_erecFrame {m m' : Mem} {a : AState} {pm : PMemo} (hD : ArenaD m a) (hP : PMemoR m pm)
    (hf : MemFrame [EREC] [] m m') : ArenaD m' a ∧ PMemoR m' pm :=
  ⟨⟨ArenaR.frame_ext _ _ (by simp [EREC]) (by simp) m _ hf a hD.1,
    DerR.frameM _ _ m _ hf (by simp [EREC]) a hD.2⟩,
    hP.frame (by simp [EREC]) (by simp) hf⟩

theorem hslice?_pre_le {m : Mem} {D o l : Nat} {k : IdxKind} {xs : List (Idx k)}
    (h : hslice? (preE m D) o l = some xs) : l = 0 ∨ o + l ≤ D := by
  rcases hslice?_bound h with h0 | h0
  · exact .inl h0
  · right
    have : (preE m D).size ≤ D := by simp [preE, Nat.min_le_left]
    omega

theorem nat?_of_pre {m : Mem} {T i : Nat} {w : Word} (hi : i < T) (h : (m.arr64 EREC)[i]? = some w) :
    nat? (preE m T) i = some w.toNat := by
  simp [nat?, preE_of_get hi h]

theorem hd?_of_pre {m : Mem} {T i : Nat} {w : Word} {k : IdxKind} (hi : i < T)
    (h : (m.arr64 EREC)[i]? = some w) (hw : w.toNat < 2 ^ 32) :
    (hd? (preE m T) i : Option (Idx k)) = some (decI w) := by
  simp [hd?, preE_of_get hi h, hw]

end L.Arena
