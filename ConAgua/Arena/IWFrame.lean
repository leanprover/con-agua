module

public import ConAgua.Arena.IndIface
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr

@[expose] public section

/-!
# The work pool's invariant `IWOK` and its growth `IWGrow`: the frame lemmas

`IWOK` and `IWGrow` are in `IndIface.lean`; this file is where they are built and taken apart.
Outside these two files a proof never builds or destructures them positionally: it uses the field
names (`h.iw`, `h.erCap`, …), the lemmas here (frames with defaulted side conditions: `IWOK.frame`,
`IWOK.of_keep`, `IWGrow.of_keep`; writers: `IWOK.of_iw`, `IWGrow.set_iw`, `IWGrow.put`, …), or
`grind [IWOK_iff, ind_grind]`.

**Attribute set** `ind_grind` (the last section): `IWGrow.refl`, `IWGrow.trans` (a `grind_pattern`
on the two growth facts), and the frame lemmas `IWOK.frameG`, `IWGrow.of_keepG`, `IWOK.of_iw`,
whose side conditions `grind` decides on a literal write set.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `IWOK` across frames and writers -/

/-- `IWOK` across a writer of `IW` and its top alone, the new top within the array. -/
theorem IWOK.of_iw {m m' : Mem} (hf : MemFrame [IW] [200] m m') (h : IWOK m)
    (hroom : iwTop m' ≤ (m'.arr64 IW).size) : IWOK m' := by
  have hE := hf.arr EREC (by decide) (by decide)
  have hE1 := hf.arr (tier1 EREC) (by decide) (by decide)
  have hc := hf.size CTL
  have hI := hf.size IW
  have h1 := (IWOK_iff m).1 h
  simp only [IWOK_iff, erTop, erecTop1, hE, hE1, hc, hI, hf.ctl 129 (by decide),
    hf.ctl 130 (by decide)] at h1 ⊢
  exact ⟨by rw [← hI]; exact hroom, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2⟩

/-- `IWOK` from a frame that keeps the pool arrays and the tops (`IW`, `EREC` in both tiers,
`CTL[129]`, `CTL[130]`, `CTL[200]`). -/
theorem IWOK.of_keep {A : List TieredArray} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : (IW : TieredArray) ∉ A ∧ (EREC : TieredArray) ∉ A ∧ tier1 EREC ∉ A)
    (hC : (129 : Word) ∉ C ∧ (130 : Word) ∉ C ∧ (200 : Word) ∉ C) (h : IWOK m) : IWOK m' := by
  have hI := hf.arr IW hA.1 (by decide)
  have hE := hf.arr EREC hA.2.1 (by decide)
  have hE1 := hf.arr (tier1 EREC) hA.2.2 (by decide)
  have hc := hf.size CTL
  simp only [IWOK_iff, iwTop, erTop, erecTop1, hI, hE, hE1, hc, hf.ctl _ hC.1, hf.ctl _ hC.2.1,
    hf.ctl _ hC.2.2]
  exact (IWOK_iff m).1 h

/-- `IWOK` survives a frame that keeps both `EREC` tiers and the tops `CTL[129]`, `CTL[130]`,
`CTL[200]` (it reads only the size of `IW`). -/
theorem IWOK.frameC {m m' : Mem} {A : List TieredArray} {C : List Word} (hf : MemFrame A C m m')
    (hE : (EREC : TieredArray) ∉ A) (hE1 : (tier1 EREC : TieredArray) ∉ A) (h129 : (129 : Word) ∉ C)
    (h130 : (130 : Word) ∉ C) (h200 : (200 : Word) ∉ C) (h : IWOK m) : IWOK m' := by
  have hR : m'.arr64 EREC = m.arr64 EREC := hf.arr _ hE (by decide)
  have hR1 : m'.arr64 (tier1 EREC) = m.arr64 (tier1 EREC) := hf.arr _ hE1 (by decide)
  have := (IWOK_iff m).mp h
  simp only [IWOK_iff, iwTop, erTop, erecTop1, hR, hR1, hf.size, hf.ctl _ h129,
    hf.ctl _ h130, hf.ctl _ h200] at this ⊢
  exact this


/-- `IWOK` across a writer of the record pool's arrays (sizes and tops kept). -/
theorem IWOK.of_er {m m' : Mem} (hf : MemFrame [EREC, tier1 EREC] [] m m') (h : IWOK m) : IWOK m' := by
  have hI := hf.arr IW (by decide) (by decide)
  have hc := hf.size CTL
  have h1 := (IWOK_iff m).1 h
  simp only [IWOK_iff, iwTop, erTop, erecTop1, hI, hc, hf.size EREC, hf.size (tier1 EREC),
    hf.ctl 129 (by simp), hf.ctl 130 (by simp), hf.ctl 200 (by simp)] at h1 ⊢
  exact h1


/-! ## `IWGrow` across frames and writers -/

/-- A writer of neither `IW`, `EREC` nor `CTL[129]`, `CTL[200]` keeps the pool's growth. -/
theorem IWGrow.of_frame {A : List TieredArray} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : (IW : TieredArray) ∉ A ∧ (EREC : TieredArray) ∉ A ∧ tier1 EREC ∉ A)
    (hC : (200 : Word) ∉ C ∧ (129 : Word) ∉ C ∧ (130 : Word) ∉ C) : IWGrow m m' := by
  have hI : m'.arr64 IW = m.arr64 IW := hf.arr IW hA.1 (by decide)
  have hE : m'.arr64 EREC = m.arr64 EREC := hf.arr EREC hA.2.1 (by decide)
  have hE1 : m'.arr64 (tier1 EREC) = m.arr64 (tier1 EREC) := hf.arr _ hA.2.2 (by decide)
  refine ⟨?_, ?_, fun i _ => by rw [hI], fun i _ => by rw [hE], ?_, fun i _ => by rw [hE1]⟩
  · simp only [iwTop, hf.ctl 200 hC.1]; exact Nat.le_refl _
  · simp only [erTop, hf.ctl 129 hC.2.1]; exact Nat.le_refl _
  · simp only [erecTop1, hf.ctl 130 hC.2.2]; exact Nat.le_refl _


/-- A write to `IW` at or above the top keeps the growth. -/
theorem IWGrow.set_iw {m m' : Mem} (h : IWGrow m m') (k v : Word) (hk : iwTop m ≤ k.toNat) :
    IWGrow m (m'.set64 IW k v) := by
  refine ⟨?_, ?_, fun i hi => ?_, fun i hi => ?_, ?_, fun i hi => ?_⟩
  · simp only [iwTop, rdW_set64]; simp [show (CTL : TieredArray) ≠ IW by decide]; exact h.iw
  · simp only [erTop, rdW_set64]; simp [show (CTL : TieredArray) ≠ IW by decide]; exact h.er
  · rw [Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    have : ¬ (k.toNat = i) := by omega
    simp only [this, ite_false]; exact h.iwGet i hi
  · rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]; exact h.erGet i hi
  · simp only [erecTop1, rdW_set64]; simp [show (CTL : TieredArray) ≠ IW by decide]; exact h.er1
  · rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]; exact h.er1Get i hi

/-- Raising the top keeps the growth. -/
theorem IWGrow.set_top {m m' : Mem} (h : IWGrow m m') (t : Word) (ht : iwTop m' ≤ t.toNat)
    (hc : 200 < (m'.arr64 CTL).size) :
    IWGrow m (m'.set64 CTL 200 t) := by
  refine ⟨?_, ?_, fun i hi => ?_, fun i hi => ?_, ?_, fun i hi => ?_⟩
  · simp only [iwTop, rdW_set64]; simp [hc]; have := h.iw; simp only [iwTop] at this ht; omega
  · simp only [erTop, rdW_set64]; simp; exact h.er
  · rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]; exact h.iwGet i hi
  · rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]; exact h.erGet i hi
  · simp only [erecTop1, rdW_set64]; simp; exact h.er1
  · rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]; exact h.er1Get i hi


/-- **A write at or above a base state's top of its tier keeps the growth from the base.** -/
theorem IWGrow.put {m₀ m : Mem} {a v : Word} (hg : IWGrow m₀ m) (h : erTopOf m₀ a ≤ erOff a) :
    IWGrow m₀ (erecPutMem m a v) := by
  have hc := erecPutMem_ctl m a v
  have hI : (erecPutMem m a v).arr64 IW = m.arr64 IW := by
    rw [erecPutMem_arr, ite_eq_right_iff.mpr (fun e => absurd e ?_)]; unfold erTier; split <;> decide
  simp only [erTopOf, erOff] at h
  refine ⟨?_, ?_, fun i hi => by rw [hI]; exact hg.iwGet i hi, fun i hi => ?_, ?_, fun i hi => ?_⟩
  · simp only [iwTop, hc]; exact hg.iw
  · simp only [erTop, hc]; exact hg.er
  · rw [erecPutMem_arr]; unfold erTier; split
    · rename_i e; simp only [e, ite_true] at h
      have : ¬ (a.toNat % 2 ^ 40 = i) := by have := hg.er; simp only [erTop, erecTop] at *; omega
      simp [erOff, this, hg.erGet i hi]
    · simp [hg.erGet i hi]
  · simp only [erecTop1, hc]; exact hg.er1
  · rw [erecPutMem_arr]; unfold erTier; split
    · simp [hg.er1Get i hi]
    · rename_i e; simp only [e, ite_false] at h
      have : ¬ (a.toNat % 2 ^ 40 = i) := by omega
      simp [erOff, this, hg.er1Get i hi]


/-- A frame that grew the pool by `N` words from the old top, leaving everything below as it
was, is an `IWGrow`. -/
theorem iwGrow_of_frame {m m' : Mem} {N : Word} (hf : MemFrame [IW] [200] m m')
    (htop : rdW (m'.arr64 CTL) 200 = rdW (m.arr64 CTL) 200 + N)
    (hroom : iwTop m + N.toNat ≤ (m.arr64 IW).size) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hlow : ∀ i < iwTop m, (m'.arr64 IW)[i]? = (m.arr64 IW)[i]?) : IWGrow m m' := by
  refine { iw := ?_, er := ?_, iwGet := hlow, erGet := ?_, er1 := ?_, er1Get := ?_ }
  · simp only [iwTop, htop]; rw [UInt64.toNat_add]; simp only [iwTop] at hroom; omega
  · simp only [erTop]; rw [hf.ctl 129 (by simp)]; exact Nat.le_refl _
  · intro i _; rw [hf.arr EREC (by decide) (by decide)]
  · simp only [erecTop1]; rw [hf.ctl 130 (by simp)]; exact Nat.le_refl _
  · intro i _; rw [hf.arr (tier1 EREC) (by decide) (by decide)]

/-! ## Reads the invariant decides -/

/-- **`EREC⦃a⦄` below the tier-0 top is the tier-0 word `a`** (the pool is addressable: `IWOK.erCap`),
so the ROM's relations (`PinSetR`, `TPinsR`, `SliceR`, over `m.arr64 EREC`) read what L reads. -/
theorem erRd_lo {m : Mem} (h : IWOK m) {a : Word} (ha : a.toNat < erecTop m) :
    erRd m a = rdW (m.arr64 EREC) a := by
  have h1 := h.er; have h2 := h.erCap
  have h40 : a.toNat < 2 ^ 40 := by unfold erTop at h1; unfold erecTop at ha; omega
  have e1 : a >>> 40 = 0 := UInt64.toNat_inj.mp (by rw [L.Arena.tag_tier_toNat]; simp; omega)
  have e2 : a &&& 1099511627775 = a :=
    UInt64.toNat_inj.mp (by rw [L.Arena.tag_idx_toNat]; omega)
  simp only [erRd, e1, e2]
  rfl


/-- `erRd` does not read `IW`. -/
theorem erRd_set_iw (m : Mem) (d v a : Word) : erRd (m.set64 IW d v) a = erRd m a := by
  unfold erRd; rw [Mem.arr64_set64_ne _ _ _ _ _ (by rw [tierA_EREC]; split <;> decide)]


theorem erecPutMem_iw (m : Mem) (a v : Word) : (erecPutMem m a v).arr64 IW = m.arr64 IW :=
  (erecPutMem_frame m a v).arr IW (by decide) (by decide)


/-! ## The frame lemmas in `grind` shape (the set `ind_grind`)

`IWOK.frame` and `IWGrow.of_keep` take their side conditions by `decide` (defaulted) or as one
conjunction; `grind` cannot run a tactic, so the forms below take them as separate hypotheses, which
`grind` decides on a literal write set with `List.mem_cons`/`List.not_mem_nil` (also in the set).
New forms beside the old ones, same facts. A proof that frames the invariant is then
`grind [ind_grind]` (or, through the conjunction, `grind [IWOK_iff, ind_grind, iwTop, erTop,
erecTop1]`), and names no field. -/

/-- `IWOK.frame` in `grind` shape. -/
theorem IWOK.frameG {m m' : Mem} {A : List TieredArray} {C : List Word} (hf : MemFrame A C m m')
    (h : IWOK m) (hA : (IW : TieredArray) ∉ A) (hE : (EREC : TieredArray) ∉ A)
    (hE1 : (tier1 EREC : TieredArray) ∉ A) (h129 : (129 : Word) ∉ C) (h130 : (130 : Word) ∉ C)
    (h200 : (200 : Word) ∉ C) : IWOK m' :=
  IWOK.of_keep hf ⟨hA, hE, hE1⟩ ⟨h129, h130, h200⟩ h

/-- `IWGrow.of_keep` in `grind` shape. -/
theorem IWGrow.of_keepG {A : List TieredArray} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : (IW : TieredArray) ∉ A) (hE : (EREC : TieredArray) ∉ A) (hE1 : tier1 EREC ∉ A)
    (h129 : (129 : Word) ∉ C) (h130 : (130 : Word) ∉ C) (h200 : (200 : Word) ∉ C) : IWGrow m m' :=
  IWGrow.of_keep hf ⟨hA, hE, hE1⟩ ⟨h129, h130, h200⟩

grind_pattern [ind_grind] IWOK.frameG => MemFrame A C m m', IWOK m
grind_pattern [ind_grind] IWGrow.of_keepG => MemFrame A C m m'
grind_pattern [ind_grind] IWOK.of_iw => MemFrame [IW] [200] m m', IWOK m
grind_pattern [ind_grind] IWGrow.refl => IWGrow m m
grind_pattern [ind_grind] IWGrow.trans => IWGrow m₁ m₂, IWGrow m₂ m₃
attribute [ind_grind =] List.mem_cons
attribute [ind_grind .] List.not_mem_nil

end L.Ind

namespace L.Arena

/-- `IWOK` survives a frame that keeps `IW`, both `EREC` tiers and the three tops `CTL[129]`,
`CTL[130]`, `CTL[200]` (the tier-1 premises last, discharged by `decide` for a concrete frame). -/
theorem IWOK.frame {m m' : Mem} {A : List TieredArray} {C : List Word} (hf : MemFrame A C m m')
    (hA : (L.Ind.IW : TieredArray) ∉ A) (hE : (EREC : TieredArray) ∉ A) (h129 : (129 : Word) ∉ C) (h200 : (200 : Word) ∉ C)
    (h : L.Ind.IWOK m) (hE1 : (tier1 EREC : TieredArray) ∉ A := by decide)
    (h130 : (130 : Word) ∉ C := by decide) : L.Ind.IWOK m' := by
  have hI : m'.arr64 L.Ind.IW = m.arr64 L.Ind.IW := hf.arr _ hA (by decide)
  have hR : m'.arr64 EREC = m.arr64 EREC := hf.arr _ hE (by decide)
  have hR1 : m'.arr64 (tier1 EREC) = m.arr64 (tier1 EREC) := hf.arr _ hE1 (by decide)
  have hc : (m'.arr64 CTL).size = (m.arr64 CTL).size := hf.size CTL
  have := (L.Ind.IWOK_iff m).mp h
  simp only [L.Ind.IWOK_iff, L.Ind.iwTop, L.Ind.erTop, erecTop1, hI, hR, hR1, hc, hf.ctl _ h129,
    hf.ctl _ h130, hf.ctl _ h200] at this ⊢
  exact this


end L.Arena
