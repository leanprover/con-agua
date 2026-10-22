import ConAgua.Rom.CIReadRefW
import ConAgua.Arena.RomCI

/-!
# The ROM constant readers' refinements: the invariant and the decoding frame (helper `decls4-rom`)

* **`Inv m₀ a₀ m a`**: what holds between the entry (`m₀`, `a₀`, at `StageR`) and every point of a
  reader's run: `ArenaD`, the twin keeping its caches and pins, writes only to the ROM interner's
  arrays (`ExprA`/`ExprC`), `EREC`, `IW` and their tops, the pools only grown from `m₀` (`IWGrow`),
  and `IWOK`. It gives `StageR` back at every environment (`Inv.stage`).
* **`Holds SE SI f m x`**: the decoder `f` gives `x` in every memory that agrees with `m` on the
  `EREC` words `SE` and the `IW` words `SI`. The readers fill records whose words are written in
  several calls (`rci_cv` writes its name word, then the level-parameter slice, then its type
  word); a `Holds` fact survives every later write outside its words (`Holds.keep`), and at the
  end, all words below the tops, it is `DecB` (`Holds.decB`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Rom

open L.Arena L.Ind

/-- The arrays a reader writes: the ROM interner's, the records and the pool. -/
def RciA : List ArrId := EREC :: IW :: ExprA
/-- The `CTL` words a reader writes. -/
def RciC : List Word := 129 :: 200 :: ExprC

/-- **The readers' invariant**, from the entry `m₀`, `a₀`. -/
structure Inv (m₀ : Mem) (a₀ : AState) (m : Mem) (a : AState) : Prop where
  arena : ArenaD m a
  cp : cp a = cp a₀
  frame : MemFrame RciA RciC m₀ m
  grow : IWGrow m₀ m
  ok : IWOK m

theorem Inv.refl {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}
    (hS : StageR dn vis fe m a) : Inv m a m a :=
  ⟨hS.1.arena, rfl, MemFrame.refl _ _ _, IWGrow.refl m, hS.2⟩

/-- **`StageR` back** from the entry's. -/
theorem Inv.stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m₀ m : Mem}
    {a₀ a : AState} (hS : StageR dn vis fe m₀ a₀) (h : Inv m₀ a₀ m a) : StageR dn vis fe m a := by
  have hc : a.caches = a₀.caches := congrArg Prod.fst h.cp
  have hp : a.pins = a₀.pins := congrArg Prod.snd h.cp
  have hf := h.frame
  have hg : ErecGrow m₀ m := ⟨h.grow.2.1, h.grow.2.2.2, hf.2.2.1 EREC⟩
  refine ⟨⟨h.arena, ?_, ?_, ?_⟩, h.ok⟩
  · rw [hc]; exact hS.1.core.frame (by unfold AvoidA; decide) (by unfold AvoidC; decide) hf
  · rw [hp]; exact hS.1.pins.frame (by unfold AvoidA; decide) hf
  · exact EnvR.grow (fun b h1 h2 => hf.1 b (fun hm => by
        simp only [RciA, ExprA, RomA, StoreA, List.mem_cons, List.mem_range] at hm; omega)
        (fun hm => by subst hm; simp [CTL] at h1))
      (hf.2.1 128 (by decide)) hg hS.1.env

/-! ## The steps -/

section steps
variable {m₀ m m' : Mem} {a₀ a a' : AState}

theorem Inv.expr (h : Inv m₀ a₀ m a) (hA : ArenaD m' a') (hf : MemFrame ExprA ExprC m m')
    (hk : cp a' = cp a) : Inv m₀ a₀ m' a' ∧ m'.arr64 EREC = m.arr64 EREC ∧ m'.arr64 IW = m.arr64 IW ∧
      erTop m' = erTop m ∧ iwTop m' = iwTop m := by
  have hE : m'.arr64 EREC = m.arr64 EREC := hf.1 EREC (by decide) (by decide)
  have hI : m'.arr64 IW = m.arr64 IW := hf.1 IW (by decide) (by decide)
  have h129 : erTop m' = erTop m := by simp only [erTop]; rw [hf.2.1 129 (by decide)]
  have h200 : iwTop m' = iwTop m := by simp only [iwTop]; rw [hf.2.1 200 (by decide)]
  refine ⟨⟨hA, hk.trans h.cp, h.frame.trans (hf.mono (by intro b hb; simp [RciA, hb])
    (by intro x hx; simp [RciC, hx])), ?_, ?_⟩, hE, hI, h129, h200⟩
  · obtain ⟨g1, g2, g3, g4⟩ := h.grow
    exact ⟨h200 ▸ g1, h129 ▸ g2, fun i hi => by rw [hI]; exact g3 i hi,
      fun i hi => by rw [hE]; exact g4 i hi⟩
  · obtain ⟨o1, o2, o3, o4, o5⟩ := h.ok
    exact ⟨by rw [h200, hI]; exact o1, by rw [h129, hE]; exact o2, by rw [hI]; exact o3,
      by rw [hE]; exact o4, by rw [hf.2.2.1 CTL]; exact o5⟩

/-- A word written in `EREC` at an allocated index above the entry's top. -/
theorem Inv.setER (h : Inv m₀ a₀ m a) (i w : Word) (hi : erTop m₀ ≤ i.toNat) :
    Inv m₀ a₀ (m.set64 EREC i w) a := by
  have hf := MemFrame.set64 m EREC (by decide) i w
  have hE : ∀ j, j ≠ i.toNat → ((m.set64 EREC i w).arr64 EREC)[j]? = (m.arr64 EREC)[j]? := by
    intro j hj
    rw [Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    simp [Ne.symm hj]
  have hI : (m.set64 EREC i w).arr64 IW = m.arr64 IW := hf.1 IW (by decide) (by decide)
  have hC : (m.set64 EREC i w).arr64 CTL = m.arr64 CTL := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have h129 : erTop (m.set64 EREC i w) = erTop m := by simp only [erTop, hC]
  have h200 : iwTop (m.set64 EREC i w) = iwTop m := by simp only [iwTop, hC]
  refine ⟨ArenaD.frameHi hf (by simp) (by simp) h.arena, h.cp,
    h.frame.trans (hf.mono (by simp [RciA]) (by simp)), ?_, ?_⟩
  · obtain ⟨g1, g2, g3, g4⟩ := h.grow
    exact ⟨h200 ▸ g1, h129 ▸ g2, fun j hj => by rw [hI]; exact g3 j hj,
      fun j hj => by rw [hE j (by omega)]; exact g4 j hj⟩
  · obtain ⟨o1, o2, o3, o4, o5⟩ := h.ok
    exact ⟨by rw [h200, hI]; exact o1, by rw [h129, hf.2.2.1 EREC]; exact o2, by rw [hI]; exact o3,
      by rw [hf.2.2.1 EREC]; exact o4, by rw [hC]; exact o5⟩

end steps

end L.Rom
