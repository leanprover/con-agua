import ConAgua.Arena.ArenaRel

/-! Spike (lane `scale`): what `grind` pays for `ArenaR` in its context. Not imported by `ConAgua`. -/

open ConRon.Arena
set_option profiler true
set_option profiler.threshold 50

namespace L.Arena.Spike

-- T1: no relation in the context
theorem g1 (m : Mem) (x y : Nat) (hx : x < 5) (hy : y = x + 1) (c : Word)
    (hc : rdW (m.arr64 CTL) 4 = c) : y ≤ 5 ∧ rdW (m.arr64 CTL) 4 = c := by grind

-- T2: `ArenaR` as one opaque hypothesis
theorem g2 (m : Mem) (a : AState) (hA : ArenaR m a) (x y : Nat) (hx : x < 5) (hy : y = x + 1) (c : Word)
    (hc : rdW (m.arr64 CTL) 4 = c) : y ≤ 5 ∧ rdW (m.arr64 CTL) 4 = c := by grind

-- T3: the 22 named fields in the context (each an opaque named predicate)
theorem g3 (m : Mem) (a : AState) (hA : ArenaR m a) (x y : Nat) (hx : x < 5) (hy : y = x + 1) (c : Word)
    (hc : rdW (m.arr64 CTL) 4 = c) : y ≤ 5 ∧ rdW (m.arr64 CTL) 4 = c := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22⟩ := hA
  grind

-- T4: two tables' relations unfolded to their clauses (the `∀`s exposed)
theorem g4 (m : Mem) (a : AState) (hA : ArenaR m a) (x y : Nat) (hx : x < 5) (hy : y = x + 1) (c : Word)
    (hc : rdW (m.arr64 CTL) 4 = c) : y ≤ 5 ∧ rdW (m.arr64 CTL) 4 = c := by
  have h1 := hA.app
  have h2 := hA.sort
  simp only [AppR, SortR, StoreR, TierR] at h1 h2
  grind

-- T5: every store table unfolded (the `∀`s of 19 tables exposed) and the three memos
theorem g5 (m : Mem) (a : AState) (hA : ArenaR m a) (x y : Nat) (hx : x < 5) (hy : y = x + 1) (c : Word)
    (hc : rdW (m.arr64 CTL) 4 = c) : y ≤ 5 ∧ rdW (m.arr64 CTL) 4 = c := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22⟩ := hA
  simp only [LitR, AppR, SortR, ConstR, LetR, BVarR, FVarR, LamR, ForallR, ProjR, ZeroR, SuccR, MaxR,
    ImaxR, ParamR, LsR, NAnonR, NStrR, NNumR, StoreR, TierR, MemoRG] at *
  grind

end L.Arena.Spike
