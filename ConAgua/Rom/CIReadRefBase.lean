import ConAgua.Rom.CIReadRefW
import ConAgua.Arena.RomCI

/-!
# The ROM constant readers' refinements: the invariant and the decoding frame (helper `decls4-rom`)

* **`RInv m₀ a₀ T m a`**: what holds between the entry (`m₀`, `a₀`, at `StageR`) and every point of a
  reader's run: `ArenaD`, the twin keeping its caches and pins, writes only to the ROM interner's
  arrays (`ExprA`/`ExprC`), `EREC`, `IW` and their tops, the pools only grown from `m₀` (`IWGrow`),
  and `IWOK`. It gives `StageR` back at every environment (`RInv.stage`).
* **`Holds SE SI f m x`**: the decoder `f` gives `x` in every memory that agrees with `m` on the
  `EREC` words `SE` and the `IW` words `SI`. The readers fill records whose words are written in
  several calls (`rci_cv` writes its name word, then the level-parameter slice, then its type
  word); a `Holds` fact survives every later write outside its words (`Holds.keep`), and at the
  end, all words below the tops, it is `DecB` (`Holds.decB`).
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Rom

open L.Arena L.Ind

/-- The arrays a reader writes: the ROM interner's, the records and the pool. -/
def RciA : List ArrId := EREC :: IW :: ExprA
/-- The `CTL` words a reader writes. -/
def RciC : List Word := 129 :: 200 :: ExprC

theorem rciA_mem {b : Nat} (h : b ∈ RciA) :
    b = 136 ∨ b = 200 ∨ b = 139 ∨ b = 150 ∨ b = 138 ∨ b < 64 ∨ (256 ≤ b ∧ b < 320) := by
  simp only [RciA, ExprA, RomA, StoreA, EREC, IW, RMEMO, RSET, RSTK, List.mem_cons] at h
  rcases h with h | h | h | h | h | h
  any_goals (subst h; simp)
  simp only [lowTierArrs, List.mem_append, List.mem_range, List.mem_map] at h
  rcases h with h | ⟨y, hy, e⟩
  · omega
  · have e' : (y : Nat) + 256 = b := e
    omega

theorem rciC_mem {x : Word} (h : x ∈ RciC) :
    x = 129 ∨ x = 200 ∨ x = 132 ∨ x = 148 ∨ x = 149 ∨ x = 131 ∨ x.toNat < 64 := by
  simp only [RciC, ExprC, RomC, StoreC, List.mem_cons, List.mem_map, List.mem_range] at h
  rcases h with h | h | h | h | h | h | ⟨y, hy, rfl⟩
  all_goals first | (subst h; simp) | skip
  right; right; right; right; right; right
  rw [UInt64.toNat_ofNat']; omega

theorem rciA_core : AvoidA 96 128 RciA := by
  intro b hb
  rcases rciA_mem hb with rfl | rfl | rfl | rfl | rfl | h | h
  all_goals first | decide | (simp only [ArrId] at *; omega)

theorem rciA_pins : AvoidA 128 129 RciA := by
  intro b hb
  rcases rciA_mem hb with rfl | rfl | rfl | rfl | rfl | h | h
  all_goals first | decide | (simp only [ArrId] at *; omega)

theorem rciC_core : AvoidC 96 128 RciC := by
  intro x hx
  rcases rciC_mem hx with rfl | rfl | rfl | rfl | rfl | rfl | h
  all_goals first | decide | (left; omega)

/-- **The readers' invariant**, from the entry `m₀`, `a₀`. -/
structure RInv (m₀ : Mem) (a₀ : AState) (T : Nat) (m : Mem) (a : AState) : Prop where
  arena : ArenaD m a
  hcp : cp a = cp a₀
  frame : MemFrame RciA RciC m₀ m
  grow : IWGrow m₀ m
  ok : IWOK m
  /-- The pool's top is `T` (no reader below `rci_block` allocates in `IW`). -/
  top : iwTop m = T
  /-- The pool's mode (lane tierpool). -/
  mode : ModeOK m

theorem RInv.refl {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}
    (hS : StageR dn vis fe m a) : RInv m a (iwTop m) m a :=
  ⟨hS.1.arena, rfl, MemFrame.refl _ _ _, IWGrow.refl m, hS.2, rfl, hS.1.mode⟩

/-- **`StageR` back** from the entry's. -/
theorem RInv.stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m₀ m : Mem}
    {a₀ a : AState} {T : Nat} (hS : StageR dn vis fe m₀ a₀) (h : RInv m₀ a₀ T m a) : StageR dn vis fe m a := by
  have hc : a.caches = a₀.caches := congrArg Prod.fst h.hcp
  have hp : a.pins = a₀.pins := congrArg Prod.snd h.hcp
  have hf := h.frame
  have hg : ErecGrow m₀ m := ⟨h.grow.2.1, h.grow.2.2.2, hf.2.2.1 EREC⟩
  refine ⟨⟨h.arena, ?_, ?_, ?_, h.mode⟩, h.ok⟩
  · rw [hc]; exact hS.1.core.frame rciA_core rciC_core hf
  · rw [hp]; exact hS.1.pins.frame rciA_pins hf
  · exact EnvR.grow (fun b h1 h2 h3 => hf.1 b (fun hm => by
        rcases rciA_mem hm with h | h | h | h | h | h | h <;> omega)
        (fun hm => by subst hm; simp [CTL] at h1))
      (hf.2.1 128 (by decide)) hg
      (TblSame.of_frame
        (fun b hb => by rcases rciA_mem hb with h | h | h | h | h | h | h <;> simp only [ArrId] at * <;> omega)
        (fun b hb => by rcases rciA_mem hb with h | h | h | h | h | h | h <;> simp only [ArrId] at * <;> omega)
        (fun hm => by
          rcases rciA_mem hm with h | h | h | h | h | h | h <;> simp only [ETAB, ArrId] at * <;> omega)
        (by decide) hf) hS.1.env

/-! ## The steps -/

section steps
variable {m₀ m m' : Mem} {a₀ a a' : AState} {T : Nat}

theorem RInv.expr (h : RInv m₀ a₀ T m a) (hA : ArenaD m' a') (hmo : ModeOK m') (hf : MemFrame ExprA ExprC m m')
    (hk : cp a' = cp a) : RInv m₀ a₀ T m' a' ∧ m'.arr64 EREC = m.arr64 EREC ∧ m'.arr64 IW = m.arr64 IW ∧
      erTop m' = erTop m ∧ iwTop m' = iwTop m := by
  have hE : m'.arr64 EREC = m.arr64 EREC := hf.1 EREC (by decide) (by decide)
  have hI : m'.arr64 IW = m.arr64 IW := hf.1 IW (by decide) (by decide)
  have h129 : erTop m' = erTop m := by simp only [erTop]; rw [hf.2.1 129 (by decide)]
  have h200 : iwTop m' = iwTop m := by simp only [iwTop]; rw [hf.2.1 200 (by decide)]
  refine ⟨⟨hA, hk.trans h.hcp, h.frame.trans (hf.mono (by intro b hb; simp [RciA, hb])
    (by intro x hx; simp [RciC, hx])), ?_, ?_, h200.trans h.top, hmo⟩, hE, hI, h129, h200⟩
  · obtain ⟨g1, g2, g3, g4⟩ := h.grow
    exact ⟨h200 ▸ g1, h129 ▸ g2, fun i hi => by rw [hI]; exact g3 i hi,
      fun i hi => by rw [hE]; exact g4 i hi⟩
  · obtain ⟨o1, o2, o3, o4, o5⟩ := h.ok
    exact ⟨by rw [h200, hI]; exact o1, by rw [h129, hE]; exact o2, by rw [hI]; exact o3,
      by rw [hE]; exact o4, by rw [hf.2.2.1 CTL]; exact o5⟩

/-- A word written in `EREC` at an allocated index above the entry's top. -/
theorem RInv.setER (h : RInv m₀ a₀ T m a) (i w : Word) (hi : erTop m₀ ≤ i.toNat) :
    RInv m₀ a₀ T (m.set64 EREC i w) a := by
  have hf := MemFrame.set64 m EREC (by decide) i w
  have hE : ∀ j, j ≠ i.toNat → ((m.set64 EREC i w).arr64 EREC)[j]? = (m.arr64 EREC)[j]? := by
    intro j hj
    rw [Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    simp [Ne.symm hj]
  have hI : (m.set64 EREC i w).arr64 IW = m.arr64 IW := hf.1 IW (by decide) (by decide)
  have hC : (m.set64 EREC i w).arr64 CTL = m.arr64 CTL := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have h129 : erTop (m.set64 EREC i w) = erTop m := by simp only [erTop, hC]
  have h200 : iwTop (m.set64 EREC i w) = iwTop m := by simp only [iwTop, hC]
  refine ⟨ArenaD.frameHi hf (by intro b hb; simp at hb; subst hb; decide) (by simp) h.arena, h.hcp,
    h.frame.trans (hf.mono (by simp [RciA]) (by simp)), ?_, ?_, h200.trans h.top,
    h.mode.frame hf (by simp) (by simp)⟩
  · obtain ⟨g1, g2, g3, g4⟩ := h.grow
    exact ⟨h200 ▸ g1, h129 ▸ g2, fun j hj => by rw [hI]; exact g3 j hj,
      fun j hj => by rw [hE j (by omega)]; exact g4 j hj⟩
  · obtain ⟨o1, o2, o3, o4, o5⟩ := h.ok
    exact ⟨by rw [h200, hI]; exact o1, by rw [h129, hf.2.2.1 EREC]; exact o2, by rw [hI]; exact o3,
      by rw [hf.2.2.1 EREC]; exact o4, by rw [hC]; exact o5⟩

/-- `erec_alloc(k)`: the records' top raised by `k`. -/
theorem RInv.erAlloc (h : RInv m₀ a₀ T m a) {k o : Word} (hw : erAllocW m k = some (o, m')) :
    RInv m₀ a₀ T m' a ∧ o.toNat = erTop m ∧ erTop m' = erTop m + k.toNat ∧
      m'.arr64 EREC = m.arr64 EREC ∧ m'.arr64 IW = m.arr64 IW ∧ iwTop m' = iwTop m := by
  obtain ⟨o1, o2, o3, o4, o5⟩ := h.ok
  simp only [erAllocW] at hw
  by_cases h1 : m.len64 EREC < rdW (m.arr64 CTL) 129
  · simp [h1] at hw
  by_cases h2 : m.len64 EREC - rdW (m.arr64 CTL) 129 < k
  · simp [h1, h2] at hw
  simp only [h1, h2, ite_false, Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  have hlen : (m.len64 EREC).toNat = (m.arr64 EREC).size := by simp [Mem.len64]; omega
  have hq : (rdW (m.arr64 CTL) 129).toNat ≤ (m.arr64 EREC).size := by
    have : ¬ (m.len64 EREC).toNat < (rdW (m.arr64 CTL) 129).toNat := h1
    omega
  have hroom : (rdW (m.arr64 CTL) 129).toNat + k.toNat ≤ (m.arr64 EREC).size := by
    have : ¬ (m.len64 EREC - rdW (m.arr64 CTL) 129).toNat < k.toNat := h2
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)] at this
    omega
  have hf : MemFrame [] [129] m (erAllocMem m k) := MemFrame.setCtl m 129 _
  have hE : (erAllocMem m k).arr64 EREC = m.arr64 EREC := hf.1 EREC (by simp) (by decide)
  have hI : (erAllocMem m k).arr64 IW = m.arr64 IW := hf.1 IW (by simp) (by decide)
  have htop : erTop (erAllocMem m k) = erTop m + k.toNat := by
    simp only [erTop, erAllocMem, rdW_set64]
    rw [ite_eq_left ⟨trivial, trivial, by simp; omega⟩, UInt64.toNat_add]
    omega
  have h200 : iwTop (erAllocMem m k) = iwTop m := by simp only [iwTop]; rw [hf.2.1 200 (by decide)]
  refine ⟨⟨ArenaD.frameHi hf (by simp) (by simp) h.arena, h.hcp,
    h.frame.trans (hf.mono (by simp) (by simp [RciC])), ?_, ?_, h200.trans h.top,
    h.mode.frame hf (by decide) (by decide)⟩, rfl, htop, hE, hI,
    h200⟩
  · obtain ⟨g1, g2, g3, g4⟩ := h.grow
    exact ⟨h200 ▸ g1, by rw [htop]; omega, fun j hj => by rw [hI]; exact g3 j hj,
      fun j hj => by rw [hE]; exact g4 j hj⟩
  · exact ⟨by rw [h200, hI]; exact o1, by rw [htop, hE]; simp only [erTop]; omega, by rw [hI]; exact o3,
      by rw [hE]; exact o4, by rw [hf.2.2.1 CTL]; exact o5⟩

/-- `iw_alloc(k)`: the pool's top raised by `k`. -/
theorem RInv.iwAlloc (h : RInv m₀ a₀ T m a) {k o : Word} (hw : allocW m k = some (o, m')) :
    RInv m₀ a₀ (T + k.toNat) m' a ∧ o.toNat = iwTop m ∧ iwTop m' = iwTop m + k.toNat ∧
      m'.arr64 EREC = m.arr64 EREC ∧ m'.arr64 IW = m.arr64 IW ∧ erTop m' = erTop m := by
  obtain ⟨o1, o2, o3, o4, o5⟩ := h.ok
  obtain ⟨hq, rfl, hroom⟩ := allocW_facts hw o3
  have hf := allocMem_frame m k
  have hE : (allocMem m k).arr64 EREC = m.arr64 EREC := hf.1 EREC (by simp [EREC, IW]) (by decide)
  have hI : (allocMem m k).arr64 IW = m.arr64 IW := by
    simp only [allocMem]; exact Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have htop : iwTop (allocMem m k) = iwTop m + k.toNat := by
    simp only [iwTop, allocMem_top m k o5, ← hq]
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have h129 : erTop (allocMem m k) = erTop m := by simp only [erTop]; rw [hf.2.1 129 (by simp)]
  have hqi : o.toNat = iwTop m := by simp only [iwTop, hq]
  refine ⟨⟨ArenaD.frameHi hf (by intro b hb; simp at hb; subst hb; decide) (by simp) h.arena, h.hcp,
    h.frame.trans (hf.mono (by simp [RciA]) (by simp [RciC])), ?_, ?_, by rw [htop, h.top],
    h.mode.frame hf (by decide) (by decide)⟩, hqi, htop,
    hE, hI, h129⟩
  · obtain ⟨g1, g2, g3, g4⟩ := h.grow
    exact ⟨by rw [htop]; omega, h129 ▸ g2, fun j hj => by rw [hI]; exact g3 j hj,
      fun j hj => by rw [hE]; exact g4 j hj⟩
  · exact ⟨by rw [htop, hI]; omega, by rw [h129, hE]; exact o2, by rw [hI]; exact o3,
      by rw [hE]; exact o4, by rw [hf.2.2.1 CTL]; exact o5⟩

/-- A word written in `IW` at an allocated index above the entry's pool top. -/
theorem RInv.setIW (h : RInv m₀ a₀ T m a) (i w : Word) (hi : iwTop m₀ ≤ i.toNat) :
    RInv m₀ a₀ T (m.set64 IW i w) a := by
  have hf := MemFrame.set64 m IW (by decide) i w
  have hI : ∀ j, j ≠ i.toNat → ((m.set64 IW i w).arr64 IW)[j]? = (m.arr64 IW)[j]? := by
    intro j hj
    rw [Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    simp [Ne.symm hj]
  have hE : (m.set64 IW i w).arr64 EREC = m.arr64 EREC := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have hC : (m.set64 IW i w).arr64 CTL = m.arr64 CTL := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have h129 : erTop (m.set64 IW i w) = erTop m := by simp only [erTop, hC]
  have h200 : iwTop (m.set64 IW i w) = iwTop m := by simp only [iwTop, hC]
  refine ⟨ArenaD.frameHi hf (by intro b hb; simp at hb; subst hb; decide) (by simp) h.arena, h.hcp,
    h.frame.trans (hf.mono (by simp [RciA]) (by simp)), ?_, ?_, h200.trans h.top,
    h.mode.frame hf (by simp) (by simp)⟩
  · obtain ⟨g1, g2, g3, g4⟩ := h.grow
    exact ⟨h200 ▸ g1, h129 ▸ g2, fun j hj => by rw [hI j (by omega)]; exact g3 j hj,
      fun j hj => by rw [hE]; exact g4 j hj⟩
  · obtain ⟨o1, o2, o3, o4, o5⟩ := h.ok
    exact ⟨by rw [h200, hf.2.2.1 IW]; exact o1, by rw [h129, hE]; exact o2,
      by rw [hf.2.2.1 IW]; exact o3, by rw [hE]; exact o4, by rw [hC]; exact o5⟩

end steps

end L.Rom

/-! ## Decodings that depend on given words -/

namespace L.Rom

open L.Arena L.Ind

/-- The decoder `f` gives `x` in every memory agreeing with `m` on the `EREC` words `SE` and the
`IW` words `SI`. -/
def Holds {α : Type} (SE SI : Nat → Prop) (f : Mem → Option α) (m : Mem) (x : α) : Prop :=
  ∀ m', (∀ i, SE i → (erA m')[i]? = (erA m)[i]?) → (∀ i, SI i → (iwA m')[i]? = (iwA m)[i]?) →
    f m' = some x

section holds
variable {α β γ δ : Type} {SE SI SE' SI' : Nat → Prop} {m m' : Mem}

theorem Holds.get {f : Mem → Option α} {x : α} (h : Holds SE SI f m x) : f m = some x :=
  h m (fun _ _ => rfl) (fun _ _ => rfl)

theorem Holds.keep {f : Mem → Option α} {x : α} (h : Holds SE SI f m x)
    (hE : ∀ i, SE i → (erA m')[i]? = (erA m)[i]?) (hI : ∀ i, SI i → (iwA m')[i]? = (iwA m)[i]?) :
    Holds SE SI f m' x :=
  fun m'' h1 h2 => h m'' (fun i hi => (h1 i hi).trans (hE i hi)) (fun i hi => (h2 i hi).trans (hI i hi))

theorem Holds.mono {f : Mem → Option α} {x : α} (h : Holds SE SI f m x) (hE : ∀ i, SE i → SE' i)
    (hI : ∀ i, SI i → SI' i) : Holds SE' SI' f m x :=
  fun m'' h1 h2 => h m'' (fun i hi => h1 i (hE i hi)) (fun i hi => h2 i (hI i hi))

theorem Holds.congr {f g : Mem → Option α} {x : α} (h : Holds SE SI f m x)
    (hfg : ∀ m, f m = some x → g m = some x) : Holds SE SI g m x :=
  fun m'' h1 h2 => hfg m'' (h m'' h1 h2)

/-- Two decodings give a third. -/
theorem Holds.comb {f : Mem → Option α} {g : Mem → Option β} {h : Mem → Option γ} {x : α} {y : β}
    {z : γ} {SE₂ SI₂ : Nat → Prop} (hf : Holds SE SI f m x) (hg : Holds SE₂ SI₂ g m y)
    (hc : ∀ m, f m = some x → g m = some y → h m = some z) :
    Holds (fun i => SE i ∨ SE₂ i) (fun i => SI i ∨ SI₂ i) h m z :=
  fun m'' h1 h2 => hc m'' (hf m'' (fun i hi => h1 i (.inl hi)) (fun i hi => h2 i (.inl hi)))
    (hg m'' (fun i hi => h1 i (.inr hi)) (fun i hi => h2 i (.inr hi)))

/-- Nothing read. -/
theorem Holds.const (x : α) : Holds (fun _ => False) (fun _ => False) (fun _ => some x) m x :=
  fun _ _ _ => rfl

/-- One `EREC` word. -/
theorem Holds.er {i : Nat} {w : Word} (h : (erA m)[i]? = some w) :
    Holds (fun j => j = i) (fun _ => False) (fun m => (erA m)[i]?) m w :=
  fun _m'' h1 _ => (h1 i rfl).trans h

/-- One `IW` word. -/
theorem Holds.iw {i : Nat} {w : Word} (h : (iwA m)[i]? = some w) :
    Holds (fun _ => False) (fun j => j = i) (fun m => (iwA m)[i]?) m w :=
  fun _m'' _ h2 => (h2 i rfl).trans h

/-- **At the end**: every word read below the tops, the decoding is `DecB`. -/
theorem Holds.decB {f : Mem → Option α} {x : α} (h : Holds SE SI f m x)
    (hE : ∀ i, SE i → i < erTop m) (hI : ∀ i, SI i → i < iwTop m) : DecB f m x :=
  h (truncM m) (fun i hi => truncM_er_eq (hE i hi)) (fun i hi => truncM_iw_eq (hI i hi))

end holds

/-! ## Region keeping -/

/-- `EREC` below `m`'s top unchanged outside `R`. -/
def EKeep (R : Nat → Prop) (m m' : Mem) : Prop :=
  erTop m ≤ erTop m' ∧ ∀ i, i < erTop m → ¬ R i → (erA m')[i]? = (erA m)[i]?

theorem EKeep.refl (R : Nat → Prop) (m : Mem) : EKeep R m m := ⟨Nat.le_refl _, fun _ _ _ => rfl⟩

theorem EKeep.trans {R : Nat → Prop} {m₁ m₂ m₃ : Mem} (h₁ : EKeep R m₁ m₂) (h₂ : EKeep R m₂ m₃) :
    EKeep R m₁ m₃ :=
  ⟨Nat.le_trans h₁.1 h₂.1, fun i hi hr => (h₂.2 i (Nat.lt_of_lt_of_le hi h₁.1) hr).trans (h₁.2 i hi hr)⟩

theorem EKeep.mono {R R' : Nat → Prop} {m m' : Mem} (h : EKeep R m m') (hR : ∀ i, R i → R' i) :
    EKeep R' m m' := ⟨h.1, fun i hi hr => h.2 i hi (fun h' => hr (hR i h'))⟩

theorem EKeep.of_eq {R : Nat → Prop} {m m' : Mem} (hE : m'.arr64 EREC = m.arr64 EREC)
    (ht : erTop m ≤ erTop m') : EKeep R m m' := ⟨ht, fun i _ _ => by simp only [erA, hE]⟩

theorem EKeep.set {R : Nat → Prop} (m : Mem) (i : Word) (w : Word) (hi : R i.toNat) :
    EKeep R m (m.set64 EREC i w) := by
  refine ⟨by simp only [erTop]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]; exact Nat.le_refl _,
    fun j _ hj => ?_⟩
  simp only [erA]
  rw [Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  have : i.toNat ≠ j := fun e => hj (e ▸ hi)
  simp [this]

/-- A decoding reading words below the top and outside `R` survives. -/
theorem Holds.ekeep {α : Type} {SE SI R : Nat → Prop} {f : Mem → Option α} {x : α} {m m' : Mem}
    (h : Holds SE SI f m x) (hk : EKeep R m m') (hS : ∀ i, SE i → i < erTop m ∧ ¬ R i)
    (hI : m'.arr64 IW = m.arr64 IW) : Holds SE SI f m' x :=
  h.keep (fun i hi => hk.2 i (hS i hi).1 (hS i hi).2) (fun i _ => by simp only [iwA, hI])

end L.Rom
