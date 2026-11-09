module

public import ConAgua.Arena.IndDecStab
public import ConAgua.Arena.IndMaster
public import ConAgua.Arena.RomExprRef
public import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Arena.IndCopy2
import ConAgua.Arena.DerRel
import ConAgua.Arena.ErecRd
public import ConAgua.Rom.ReadScr

@[expose] public section

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

/-- The arrays a reader writes: the ROM interner's, the records (both tiers) and the pool. -/
def RciA : List TieredArray :=
  (EREC : TieredArray) :: tier1 EREC :: (IW : TieredArray) :: ExprA
/-- The `CTL` words a reader writes. -/
def RciC : List Word := 129 :: 130 :: 200 :: ExprC

theorem rciA_arr {b : TieredArray} (h : b ∈ RciA) :
    b.arr = EREC ∨ b.arr = IW ∨ b.arr = RMEMO ∨ b.arr = RSET ∨ b.arr = RSTK ∨ b.arr < 64 := by
  simp only [RciA, ExprA, RomA, StoreA, List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | h
  · exact .inl rfl
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr (.inl rfl))
  · exact .inr (.inr (.inr (.inl rfl)))
  · exact .inr (.inr (.inr (.inr (.inl rfl))))
  · exact .inr (.inr (.inr (.inr (.inr (storeTier_of_mem h)))))

theorem rciC_mem {x : Word} (h : x ∈ RciC) :
    x = 129 ∨ x = 130 ∨ x = 200 ∨ x = 132 ∨ x = 148 ∨ x = 149 ∨ x = 131 ∨ x.toNat < 64 := by
  simp only [RciC, ExprC, RomC, StoreC, List.mem_cons, List.mem_map, List.mem_range] at h
  rcases h with h | h | h | h | h | h | h | ⟨y, hy, rfl⟩
  all_goals first | (subst h; simp) | skip
  right; right; right; right; right; right; right
  rw [UInt64.toNat_ofNat']; omega

theorem rciA_core : AvoidA 96 128 RciA := fun b hb => by
  have := rciA_arr hb; simp only [EREC, IW, RMEMO, RSET, RSTK] at this; omega

theorem rciA_pins : AvoidA 128 129 RciA := fun b hb => by
  have := rciA_arr hb; simp only [EREC, IW, RMEMO, RSET, RSTK] at this; omega

theorem rciC_core : AvoidC 96 128 RciC := by
  intro x hx
  rcases rciC_mem hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
  all_goals first | decide | (left; omega)

/-! ## The flag's tier

`erec_alloc` allocates in the tier of the scratch flag `CTL[1]`: tier 0 (tagged addresses below
`2^40`) while it is off, tier 1 (at `2^40 + o`) while it is on. A reader never moves the flag
(`RInv.fl`), so all its records are in one tier, between the entry's top `erT m₀` and the current
one `erT m`. -/

/-- `ArenaD` across a writer of arrays from `64` on that are no arena arrays (both `EREC` tiers). -/
theorem ArenaD.frameE {A : List TieredArray} {C : List Word} {m m' : Mem} {a : AState}
    (hf : MemFrame A C m m') (hA : ∀ b ∈ A, 64 ≤ b.arr ∧ b ∉ arenaArrs) (hC : ∀ x ∈ C, 64 ≤ x.toNat)
    (h : ArenaD m a) : ArenaD m' a :=
  ⟨h.base.frame (fun b hb h' => (hA b hb).2 h') (fun x hx => not_mem_arenaCtl x (hC x hx)) hf,
   DerR.frameM A C m m' hf (fun b hb => by have := (hA b hb).1; omega) a h.der⟩

/-- The flag word's test across a run that keeps `scratchOn`, from `ArenaR` at both ends. -/
theorem flag_keep {mem mem' : Mem} {a a' : AState} (hA : ArenaR mem a) (hA' : ArenaR mem' a')
    (hsc : a'.store.scratchOn = a.store.scratchOn) :
    (rdW (mem'.arr64 CTL) 1 = 0 ↔ rdW (mem.arr64 CTL) 1 = 0) := by
  have h1 := ConsR.flag hA.sort; have h2 := ConsR.flag hA'.sort
  rw [hsc, ← h1] at h2
  constructor
  · intro e; rw [e] at h2; simpa using h2.symm
  · intro e; rw [e] at h2; simpa using h2

/-- The flag's tier base, as a tagged address. -/
def erB (m : Mem) : Nat := if rdW (m.arr64 CTL) 1 = 0 then 0 else 2 ^ 40

/-- The flag's tier top, as a tagged address: where `erec_alloc` allocates next. -/
def erT (m : Mem) : Nat := if rdW (m.arr64 CTL) 1 = 0 then erecTop m else 2 ^ 40 + erecTop1 m

theorem erT_congr {m m' : Mem} (h : m'.arr64 CTL = m.arr64 CTL) : erT m' = erT m ∧ erB m' = erB m := by
  exact ⟨by simp only [erT, erecTop, erecTop1, h], by simp only [erB, h]⟩

theorem erB_le_erT (m : Mem) : erB m ≤ erT m := by
  unfold erB erT; split <;> omega

/-- The flag's tier is in bounds: its top below the tier's end, and tier 1 below `2^41`. -/
theorem erT_lt {m : Mem} (h : IWOK m) : erT m < erB m + 2 ^ 40 ∧ erT m < 2 ^ 41 := by
  have := h.er; have := h.erCap; have := h.er1; have := h.er1Cap
  unfold erT erB; simp only [erTop, erecTop, erecTop1] at *; split <;> omega

/-- A word of the flag's tier, below its top, read back after a write. -/
theorem er_put_get {m : Mem} (h : IWOK m) (i w : Word) (hb : erB m ≤ i.toNat) (ht : i.toNat < erT m) :
    erA (erecPutMem m i w) i.toNat = some w := by
  have := h.er; have := h.erCap; have := h.er1; have := h.er1Cap
  simp only [erTop] at *
  unfold erT erB at *; simp only [erecTop, erecTop1] at *
  by_cases e : rdW (m.arr64 CTL) 1 = 0 <;> simp only [e, ite_true, ite_false] at hb ht
  all_goals apply erecP_putMem_self
  all_goals simp only [erTopOf, erOff, erTier, erecTop, erecTop1]
  all_goals split <;> omega

/-- Every other word below `2^41` reads as before a write. -/
theorem er_put_ne (m : Mem) (i w : Word) (j : Nat) (hj : j ≠ i.toNat) (hj1 : j < 2 ^ 41)
    (hi1 : i.toNat < 2 ^ 41) : erA (erecPutMem m i w) j = erA m j :=
  erecP_putMem_other (by omega)

/-- A write in the flag's tier above `m₀`'s top keeps every record `m₀` has. -/
theorem IWGrow.put {m₀ m : Mem} (hg : IWGrow m₀ m) (hok : IWOK m) (i w : Word)
    (hfl : rdW (m.arr64 CTL) 1 = 0 ↔ rdW (m₀.arr64 CTL) 1 = 0) (hi : erT m₀ ≤ i.toNat)
    (hi' : i.toNat < erT m) : IWGrow m₀ (erecPutMem m i w) := by
  have hc := erecPutMem_ctl m i w
  have k1 : erecTop m ≤ (m.arr64 EREC).size := hok.er
  have k2 : (m.arr64 EREC).size < 2 ^ 40 := hok.erCap
  have k3 : erecTop1 m ≤ (m.arr64 (tier1 EREC)).size := hok.er1
  have k4 : (m.arr64 (tier1 EREC)).size < 2 ^ 40 := hok.er1Cap
  have k5 : erecTop m₀ ≤ erecTop m := hg.er
  have k6 : erecTop1 m₀ ≤ erecTop1 m := hg.er1
  have hR : (i.toNat / 2 ^ 40 % 2 = 0 → erecTop m₀ ≤ i.toNat % 2 ^ 40) ∧
      (¬ i.toNat / 2 ^ 40 % 2 = 0 → erecTop1 m₀ ≤ i.toNat % 2 ^ 40) := by
    unfold erT at hi hi'
    by_cases e2 : rdW (m₀.arr64 CTL) 1 = 0
    · rw [if_pos e2] at hi; rw [if_pos (hfl.2 e2)] at hi'; constructor <;> intro <;> omega
    · rw [if_neg e2] at hi; rw [if_neg (fun h' => e2 (hfl.1 h'))] at hi'; constructor <;> intro <;> omega
  refine ⟨by simp only [iwTop, hc]; exact hg.iw, by simp only [erTop, hc]; exact hg.er,
    fun j hj => ?_, fun j hj => ?_, by simp only [erecTop1, hc]; exact hg.er1, fun j hj => ?_⟩
  · rw [erecPutMem_arr, if_neg (by unfold erTier; split <;> decide)]; exact hg.iwGet j hj
  · rw [erecPutMem_arr]; unfold erTier; split
    · rename_i e
      have hj' : j < erecTop m₀ := hj
      have : ¬ (erOff i = j) := by have := hR.1 e; simp only [erOff]; omega
      simp [Array.getElem?_setIfInBounds, this, hg.erGet j hj]
    · exact hg.erGet j hj
  · rw [erecPutMem_arr]; unfold erTier; split
    · exact hg.er1Get j hj
    · rename_i e
      have : ¬ (erOff i = j) := by have := hR.2 e; simp only [erOff]; omega
      simp [Array.getElem?_setIfInBounds, this, hg.er1Get j hj]

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
  /-- The scratch flag's test is the entry's: every record is in one tier. -/
  fl : rdW (m.arr64 CTL) 1 = 0 ↔ rdW (m₀.arr64 CTL) 1 = 0

theorem RInv.refl {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}
    (hS : StageR vis fe m a) : RInv m a (iwTop m) m a :=
  ⟨hS.check.arena, rfl, MemFrame.refl _ _ _, IWGrow.refl m, hS.iw, rfl, hS.check.mode, Iff.rfl⟩

/-- **`StageR` back** from the entry's. -/
theorem RInv.stage {vis : Word} {fe : IFEnv} {m₀ m : Mem}
    {a₀ a : AState} {T : Nat} (hS : StageR vis fe m₀ a₀) (h : RInv m₀ a₀ T m a) : StageR vis fe m a := by
  have hc : a.caches = a₀.caches := congrArg Prod.fst h.hcp
  have hp : a.pins = a₀.pins := congrArg Prod.snd h.hcp
  have hf := h.frame
  refine ⟨⟨h.arena, ?_, ?_, ?_, h.mode⟩, h.ok⟩
  · rw [hc]; exact hS.check.core.frame rciA_core rciC_core hf
  · rw [hp]; exact hS.check.pins.frame rciA_pins hf
  · refine hS.check.env.growF hf (fun b hb => ?_) (fun x hx => ?_) h.grow.erecGrow
    · rcases rciA_arr hb with e | e | e | e | e | e
      · exact .inl e
      all_goals (right; apply not_mem_envArrs; (try simp only [IW, RMEMO, RSET, RSTK] at e); omega)
    · rcases rciC_mem hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | e
      · exact .inl rfl
      · exact .inr (.inl rfl)
      all_goals (right; right; apply not_mem_envCtl)
      all_goals first | (simp; done) | omega

/-! ## The steps -/

section steps
variable {m₀ m m' : Mem} {a₀ a a' : AState} {T : Nat}

theorem RInv.erB_eq (h : RInv m₀ a₀ T m a) : erB m = erB m₀ := by
  unfold erB; by_cases e : rdW (m₀.arr64 CTL) 1 = 0
  · rw [if_pos (h.fl.2 e), if_pos e]
  · rw [if_neg (fun h' => e (h.fl.1 h')), if_neg e]

theorem RInv.erT_mono (h : RInv m₀ a₀ T m a) : erT m₀ ≤ erT m := by
  have k1 : erecTop m₀ ≤ erecTop m := h.grow.er
  have k2 : erecTop1 m₀ ≤ erecTop1 m := h.grow.er1
  unfold erT
  by_cases e : rdW (m₀.arr64 CTL) 1 = 0
  · rw [if_pos (h.fl.2 e), if_pos e]; omega
  · rw [if_neg (fun h' => e (h.fl.1 h')), if_neg e]; omega

theorem RInv.er_lt (h : RInv m₀ a₀ T m a) : erT m < 2 ^ 41 := (erT_lt h.ok).2

theorem RInv.iw_lt (h : RInv m₀ a₀ T m a) : iwTop m < 2 ^ 64 := by
  have := h.ok.iw; have := h.ok.iwSize; omega

/-- Across a store interner's call (a `MemFrame ExprA ExprC`) that keeps `cp` and the twin's
`scratchOn`. -/
theorem RInv.expr (h : RInv m₀ a₀ T m a) (hA : ArenaD m' a') (hmo : ModeOK m') (hf : MemFrame ExprA ExprC m m')
    (hk : cp a' = cp a) (hsc : a'.store.scratchOn = a.store.scratchOn) :
    RInv m₀ a₀ T m' a' ∧ m'.arr64 EREC = m.arr64 EREC ∧ m'.arr64 (tier1 EREC) = m.arr64 (tier1 EREC) ∧
      m'.arr64 IW = m.arr64 IW ∧ erT m' = erT m ∧ iwTop m' = iwTop m ∧ erA m' = erA m := by
  have hE : m'.arr64 EREC = m.arr64 EREC := hf.arr EREC (by decide) (by decide)
  have hE1 : m'.arr64 (tier1 EREC) = m.arr64 (tier1 EREC) := hf.arr (tier1 EREC) (by decide) (by decide)
  have hI : m'.arr64 IW = m.arr64 IW := hf.arr IW (by decide) (by decide)
  have h129 : erecTop m' = erecTop m := by simp only [erecTop]; rw [hf.ctl 129 (by decide)]
  have h130 : erecTop1 m' = erecTop1 m := by simp only [erecTop1]; rw [hf.ctl 130 (by decide)]
  have h200 : iwTop m' = iwTop m := by simp only [iwTop]; rw [hf.ctl 200 (by decide)]
  have hfl := flag_keep h.arena.base hA.base hsc
  have hT : erT m' = erT m := by
    unfold erT; by_cases e : rdW (m.arr64 CTL) 1 = 0
    · rw [if_pos (hfl.2 e), if_pos e, h129]
    · rw [if_neg (fun h' => e (hfl.1 h')), if_neg e, h130]
  refine ⟨⟨hA, hk.trans h.hcp, h.frame.trans (hf.mono (by intro b hb; simp [RciA, hb])
    (by intro x hx; simp [RciC, hx])), ?_, ?_, h200.trans h.top, hmo, hfl.trans h.fl⟩, hE, hE1, hI, hT, h200,
    ?_⟩
  · exact h.grow.trans (IWGrow.of_keep hf ⟨by decide, by decide, by decide⟩
      ⟨by decide, by decide, by decide⟩)
  · exact IWOK.of_keep hf ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩ h.ok
  · funext i; simp only [erA, erecP, hE, hE1, h129, h130]

/-- **A word written** with `erec_put` in the flag's tier, between the entry's top and the
current one. -/
theorem RInv.putER (h : RInv m₀ a₀ T m a) (i w : Word) (hi : erT m₀ ≤ i.toNat) (hi' : i.toNat < erT m) :
    RInv m₀ a₀ T (erecPutMem m i w) a ∧ erA (erecPutMem m i w) i.toNat = some w ∧
      (∀ j, j ≠ i.toNat → j < 2 ^ 41 → erA (erecPutMem m i w) j = erA m j) ∧
      erT (erecPutMem m i w) = erT m ∧ (erecPutMem m i w).arr64 IW = m.arr64 IW ∧
      iwTop (erecPutMem m i w) = iwTop m := by
  have hf := erecPutMem_frame m i w
  have hc := erecPutMem_ctl m i w
  have hI : (erecPutMem m i w).arr64 IW = m.arr64 IW := hf.arr IW (by decide) (by decide)
  have h200 : iwTop (erecPutMem m i w) = iwTop m := by simp only [iwTop, hc]
  have hlt := h.er_lt
  have hb : erB m ≤ i.toNat := by rw [h.erB_eq]; exact Nat.le_trans (erB_le_erT m₀) hi
  refine ⟨⟨ArenaD.frameE hf (by intro b hb; simp at hb; rcases hb with rfl | rfl <;> decide) (by simp) h.arena,
    h.hcp, h.frame.trans (hf.mono (by simp [RciA]) (by simp)), IWGrow.put h.grow h.ok i w h.fl hi hi', ?_, h200.trans h.top,
    h.mode.frame hf (by simp) (by simp), by rw [hc]; exact h.fl⟩, er_put_get h.ok i w hb hi',
    fun j hj hj1 => er_put_ne m i w j hj hj1 (by omega), (erT_congr hc).1, hI, h200⟩
  · have hs : ∀ b, ((erecPutMem m i w).arr64 b).size = (m.arr64 b).size := by
      intro b; rw [erecPutMem_arr]; split <;> simp
    have := (IWOK_iff m).1 h.ok
    rw [IWOK_iff]
    simp only [iwTop, erTop, erecTop1, hc, hs]
    exact this

/-- `erec_alloc(k)`: the flag tier's top raised by `k`, the address its old top. -/
theorem RInv.erAlloc (h : RInv m₀ a₀ T m a) {k o : Word} (hw : erAllocW m k = some (o, m')) :
    RInv m₀ a₀ T m' a ∧ o.toNat = erT m ∧ erT m' = erT m + k.toNat ∧
      m'.arr64 EREC = m.arr64 EREC ∧ m'.arr64 (tier1 EREC) = m.arr64 (tier1 EREC) ∧
      m'.arr64 IW = m.arr64 IW ∧ iwTop m' = iwTop m ∧ ArrExt (erA m) (erA m') := by
  obtain ⟨hg, hf, hoff, htop, -, htier, hlt, hok'⟩ := erAllocW_spec hw h.ok
  have hE : m'.arr64 EREC = m.arr64 EREC := hf.arr EREC (by simp) (by decide)
  have hE1 : m'.arr64 (tier1 EREC) = m.arr64 (tier1 EREC) := hf.arr (tier1 EREC) (by simp) (by decide)
  have hI : m'.arr64 IW = m.arr64 IW := hf.arr IW (by simp) (by decide)
  have h200 : iwTop m' = iwTop m := by simp only [iwTop]; rw [hf.ctl 200 (by decide)]
  have h1 : rdW (m'.arr64 CTL) 1 = rdW (m.arr64 CTL) 1 := hf.ctl 1 (by decide)
  have hgI : IWGrow m m' := ⟨by omega, hg.top, fun j _ => by rw [hI], hg.get, hg.top1, hg.get1⟩
  have hT : o.toNat = erT m ∧ erT m' = erT m + k.toNat := by
    simp only [erOff, erTopOf] at hoff htop
    unfold erT; rw [h1]
    by_cases e : rdW (m.arr64 CTL) 1 = 0
    · have := htier.2 e; simp only [this, ite_true, e] at hoff htop ⊢; omega
    · have : ¬ o.toNat / 2 ^ 40 % 2 = 0 := fun h' => e (htier.1 h')
      simp only [this, ite_false, e] at hoff htop ⊢; omega
  refine ⟨⟨ArenaD.frameHi hf (by simp) (by simp) h.arena, h.hcp,
    h.frame.trans (hf.mono (by simp) (by simp [RciC])), h.grow.trans hgI, hok', h200.trans h.top,
    h.mode.frame hf (by decide) (by decide), by rw [h1]; exact h.fl⟩, hT.1, hT.2, hE, hE1, hI, h200, hg.ext⟩

/-- `iw_alloc(k)`: the pool's top raised by `k`. -/
theorem RInv.iwAlloc (h : RInv m₀ a₀ T m a) {k o : Word} (hw : allocW m k = some (o, m')) :
    RInv m₀ a₀ (T + k.toNat) m' a ∧ o.toNat = iwTop m ∧ iwTop m' = iwTop m + k.toNat ∧
      m'.arr64 IW = m.arr64 IW ∧ erT m' = erT m ∧ erA m' = erA m := by
  obtain ⟨hq, rfl, hroom⟩ := allocW_facts hw h.ok.iwSize
  have hf := allocMem_frame m k
  have hE : (allocMem m k).arr64 EREC = m.arr64 EREC := hf.arr EREC (by simp [EREC, IW]) (by decide)
  have hE1 : (allocMem m k).arr64 (tier1 EREC) = m.arr64 (tier1 EREC) :=
    hf.arr (tier1 EREC) (by simp [EREC, IW]) (by decide)
  have hI : (allocMem m k).arr64 IW = m.arr64 IW := by
    simp only [allocMem]; exact Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have htop : iwTop (allocMem m k) = iwTop m + k.toNat := by
    have := h.ok.iwSize
    simp only [iwTop, allocMem_top m k h.ok.ctl, ← hq]
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have h129 : erecTop (allocMem m k) = erecTop m := by simp only [erecTop]; rw [hf.ctl 129 (by simp)]
  have h130 : erecTop1 (allocMem m k) = erecTop1 m := by simp only [erecTop1]; rw [hf.ctl 130 (by simp)]
  have h1 : rdW ((allocMem m k).arr64 CTL) 1 = rdW (m.arr64 CTL) 1 := hf.ctl 1 (by simp)
  have hqi : o.toNat = iwTop m := by simp only [iwTop, hq]
  refine ⟨⟨ArenaD.frameHi hf (by intro b hb; simp at hb; subst hb; decide) (by simp) h.arena, h.hcp,
    h.frame.trans (hf.mono (by simp [RciA]) (by simp [RciC])), ?_, ?_, by rw [htop, h.top],
    h.mode.frame hf (by decide) (by decide), by rw [h1]; exact h.fl⟩, hqi, htop, hI,
    by simp only [erT, h1, h129, h130], erecP_frame hf (by simp [EREC, IW]) (by simp [EREC, IW]) (by simp) (by simp)⟩
  · exact h.grow.trans ⟨by rw [htop]; omega, by have : erTop (allocMem m k) = erTop m := h129; omega,
      fun j _ => by rw [hI], fun j _ => by rw [hE], by rw [h130]; exact Nat.le_refl _, fun j _ => by rw [hE1]⟩
  · have := (IWOK_iff m).1 h.ok
    rw [IWOK_iff]
    rw [htop, hI, show erTop (allocMem m k) = erTop m from h129, hE, hf.size CTL, hE1, h130]
    exact ⟨by omega, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2⟩

/-- A word written in `IW` at an allocated index above the entry's pool top. -/
theorem RInv.setIW (h : RInv m₀ a₀ T m a) (i w : Word) (hi : iwTop m₀ ≤ i.toNat) :
    RInv m₀ a₀ T (m.set64 IW i w) a ∧ erT (m.set64 IW i w) = erT m ∧ erA (m.set64 IW i w) = erA m := by
  have hf := MemFrame.set64 m IW (by decide) i w
  have hI : ∀ j, j ≠ i.toNat → ((m.set64 IW i w).arr64 IW)[j]? = (m.arr64 IW)[j]? := by
    intro j hj
    rw [Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    simp [Ne.symm hj]
  have hE : (m.set64 IW i w).arr64 EREC = m.arr64 EREC := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have hE1 : (m.set64 IW i w).arr64 (tier1 EREC) = m.arr64 (tier1 EREC) :=
    Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have hC : (m.set64 IW i w).arr64 CTL = m.arr64 CTL := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have h200 : iwTop (m.set64 IW i w) = iwTop m := by simp only [iwTop, hC]
  refine ⟨⟨ArenaD.frameHi hf (by intro b hb; simp at hb; subst hb; decide) (by simp) h.arena, h.hcp,
    h.frame.trans (hf.mono (by simp [RciA]) (by simp)), ?_, ?_, h200.trans h.top,
    h.mode.frame hf (by simp) (by simp), by rw [hC]; exact h.fl⟩, (erT_congr hC).1,
    erecP_frame hf (by simp [EREC, IW]) (by simp [EREC, IW]) (by simp) (by simp)⟩
  · obtain ⟨g1, g2, g3, g4, g5, g6⟩ := h.grow
    exact ⟨h200 ▸ g1, by simp only [erTop, hC] at *; exact g2, fun j hj => by rw [hI j (by omega)]; exact g3 j hj,
      fun j hj => by rw [hE]; exact g4 j hj, by simp only [erecTop1, hC]; exact g5,
      fun j hj => by rw [hE1]; exact g6 j hj⟩
  · have := (IWOK_iff m).1 h.ok
    rw [IWOK_iff]
    simp only [erecTop1, iwTop, erTop, hC, hE, hE1, Mem.size_arr64_set64] at this ⊢
    exact this

end steps

end L.Rom

/-! ## Decodings that depend on given words -/

namespace L.Rom

open L.Arena L.Ind

/-- The decoder `f` gives `x` in every memory agreeing with `m` on the `EREC` words `SE` and the
`IW` words `SI`. -/
def Holds {α : Type} (SE SI : Nat → Prop) (f : Mem → Option α) (m : Mem) (x : α) : Prop :=
  ∀ m', (∀ i, SE i → erA m' i = erA m i) → (∀ i, SI i → iwA m' i = iwA m i) →
    f m' = some x

section holds
variable {α β γ δ : Type} {SE SI SE' SI' : Nat → Prop} {m m' : Mem}

theorem Holds.get {f : Mem → Option α} {x : α} (h : Holds SE SI f m x) : f m = some x :=
  h m (fun _ _ => rfl) (fun _ _ => rfl)

theorem Holds.keep {f : Mem → Option α} {x : α} (h : Holds SE SI f m x)
    (hE : ∀ i, SE i → erA m' i = erA m i) (hI : ∀ i, SI i → iwA m' i = iwA m i) :
    Holds SE SI f m' x := fun m'' h1 h2 =>
  h m'' (fun i hi => (h1 i hi).trans (hE i hi)) (fun i hi => (h2 i hi).trans (hI i hi))

theorem Holds.mono {f : Mem → Option α} {x : α} (h : Holds SE SI f m x) (hE : ∀ i, SE i → SE' i)
    (hI : ∀ i, SI i → SI' i) : Holds SE' SI' f m x := fun m'' h1 h2 =>
  h m'' (fun i hi => h1 i (hE i hi)) (fun i hi => h2 i (hI i hi))

theorem Holds.congr {f g : Mem → Option α} {x : α} (h : Holds SE SI f m x)
    (hfg : ∀ m, f m = some x → g m = some x) : Holds SE SI g m x := fun m'' h1 h2 =>
  hfg m'' (h m'' h1 h2)

/-- Two decodings give a third. -/
theorem Holds.comb {f : Mem → Option α} {g : Mem → Option β} {h : Mem → Option γ} {x : α} {y : β}
    {z : γ} {SE₂ SI₂ : Nat → Prop} (hf : Holds SE SI f m x) (hg : Holds SE₂ SI₂ g m y)
    (hc : ∀ m, f m = some x → g m = some y → h m = some z) :
    Holds (fun i => SE i ∨ SE₂ i) (fun i => SI i ∨ SI₂ i) h m z := fun m'' h1 h2 =>
  hc m'' (hf m'' (fun i hi => h1 i (.inl hi)) (fun i hi => h2 i (.inl hi)))
    (hg m'' (fun i hi => h1 i (.inr hi)) (fun i hi => h2 i (.inr hi)))

/-- Nothing read. -/
theorem Holds.const (x : α) : Holds (fun _ => False) (fun _ => False) (fun _ => some x) m x :=
  fun _ _ _ => rfl

/-- One `EREC` word. -/
theorem Holds.er {i : Nat} {w : Word} (h : erA m i = some w) :
    Holds (fun j => j = i) (fun _ => False) (fun m => erA m i) m w := fun _ h1 _ =>
  (h1 i rfl).trans h

/-- One `IW` word. -/
theorem Holds.iw {i : Nat} {w : Word} (h : iwA m i = some w) :
    Holds (fun _ => False) (fun j => j = i) (fun m => iwA m i) m w := fun _ _ h2 =>
  (h2 i rfl).trans h

/-- **At the end**: every `IW` word read below the pool's top, the decoding is `DecB` (the
record pool `erA` reads below its tops already). -/
theorem Holds.decB {f : Mem → Option α} {x : α} (h : Holds SE SI f m x)
    (hI : ∀ i, SI i → i < iwTop m) : DecB f m x :=
  h (truncM m) (fun _ _ => truncM_er_eq) (fun i hi => truncM_iw_eq (hI i hi))

end holds

/-! ## Region keeping -/

/-- The flag tier's records of `m` (between its base and its top) unchanged outside `R`. -/
def EKeep (R : Nat → Prop) (m m' : Mem) : Prop :=
  erT m ≤ erT m' ∧ ∀ i, erB m ≤ i → i < erT m → ¬ R i → erA m' i = erA m i

theorem EKeep.refl (R : Nat → Prop) (m : Mem) : EKeep R m m := ⟨Nat.le_refl _, fun _ _ _ _ => rfl⟩

theorem EKeep.trans {R : Nat → Prop} {m₁ m₂ m₃ : Mem} (h₁ : EKeep R m₁ m₂) (h₂ : EKeep R m₂ m₃)
    (hb : erB m₂ = erB m₁) : EKeep R m₁ m₃ :=
  ⟨Nat.le_trans h₁.1 h₂.1, fun i hb' hi hr =>
    (h₂.2 i (hb ▸ hb') (Nat.lt_of_lt_of_le hi h₁.1) hr).trans (h₁.2 i hb' hi hr)⟩

theorem EKeep.mono {R R' : Nat → Prop} {m m' : Mem} (h : EKeep R m m') (hR : ∀ i, R i → R' i) :
    EKeep R' m m' := ⟨h.1, fun i hb hi hr => h.2 i hb hi (fun h' => hr (hR i h'))⟩

theorem EKeep.of_eq {R : Nat → Prop} {m m' : Mem} (hE : erA m' = erA m) (ht : erT m ≤ erT m') :
    EKeep R m m' := ⟨ht, fun i _ _ _ => by rw [hE]⟩

/-- A decoding reading words of the flag tier below the top and outside `R` survives. -/
theorem Holds.ekeep {α : Type} {SE SI R : Nat → Prop} {f : Mem → Option α} {x : α} {m m' : Mem}
    (h : Holds SE SI f m x) (hk : EKeep R m m') (hS : ∀ i, SE i → erB m ≤ i ∧ i < erT m ∧ ¬ R i)
    (hI : m'.arr64 IW = m.arr64 IW) : Holds SE SI f m' x :=
  h.keep (fun i hi => hk.2 i (hS i hi).1 (hS i hi).2.1 (hS i hi).2.2) (fun i _ => by simp only [iwA, hI])

end L.Rom
