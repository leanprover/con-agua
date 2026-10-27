import ConAgua.Arena.FreezeTruncBase

/-!
# The truncation theorem, part 3: a store under truncation of its tier 0 (lane parmode)

`storeR_trunc`: a two-tier table (`StoreR`, `StoreLib.lean`) whose tier-0 record array is cut
to `count₀ · w` words and whose tier-0 slot array is cut to `2 + 2 n` words keeps its relation,
the table sitting at word 2 (`koW = 0`: the offset word is never written; `TierLay` states it
for tier 0), given that the tier-1 arrays and `CTL` are unchanged, and
that the instance's node relation and hash survive any change that keeps the node's own words
(`RTrans`). `rTrans_local`: a node relation that reads only its record (`RLocal … [] []`) and
has the store library's frame (`RFrame`) has `RTrans` for any memory of the same shape.
-/

namespace L.Arena

open ConRon.Arena

theorem tierA_zero' (a : ArrId) : tierA a 0 = a := by simp [tierA]
theorem tierA_one' (a : ArrId) : tierA a 1 = a + 256 := by simp [tierA, tierOff]

section store
variable {α δ : Type} {k : IdxKind} [BEq α] [Hashable α]
variable (S : Schema) (R : Mem → Word → Word → α → Prop) (hs : Mem → Word → Word → Word)
  (KP : Mem → Word → Word → Word → Prop)

/-- **The instance's transfer** from `m` to `m'`: a node whose words are the same in both has
the same relations and hash. -/
def RTrans (m m' : Mem) : Prop :=
  ∀ t i, (∀ f, f < S.w → fld S m' t i f = fld S m t i f) →
    (∀ a, R m t i a → R m' t i a) ∧ hs m' t i = hs m t i

/-- What the truncation does to a store: `CTL` and tier 1 kept, tier 0's records cut to the
count, tier 0's slots cut to the table. -/
structure StoreTr (m m' : Mem) : Prop where
  ctl : m'.arr64 CTL = m.arr64 CTL
  ra1 : m'.arr64 (S.ra + 256) = m.arr64 (S.ra + 256)
  sa1 : m'.arr64 (S.sa + 256) = m.arr64 (S.sa + 256)
  ra0 : m'.arr64 S.ra = (m.arr64 S.ra).extract 0 (cntW S m 0 * S.w).toNat
  sa0 : m'.arr64 S.sa = (m.arr64 S.sa).extract 0 (2 + 2 * knW S.sa m 0).toNat

theorem mul_toNat_small {c w : Word} (hc : c.toNat ≤ 2 ^ 27) (hw : w.toNat ≤ 256) :
    (c * w).toNat = c.toNat * w.toNat := by
  rw [UInt64.toNat_mul]; apply Nat.mod_eq_of_lt
  have := Nat.mul_le_mul hc hw
  omega

/-- The tier-0 fields of a node below the count survive. -/
theorem fld_trunc0 (hS : S.WF) {m m' : Mem} (hT : StoreTr S m m') (hc : (cntW S m 0).toNat ≤ 2 ^ 27)
    {i f : Word} (hi : i.toNat < (cntW S m 0).toNat) (hf : f < S.w) :
    fld S m' 0 i f = fld S m 0 i f := by
  simp only [fld, tierA_zero', hT.ra0]
  apply rdW_extract
  have hw := hS.w_le
  rw [S.ad_toNat hS i f (by omega) hf, mul_toNat_small hc hw]
  have hf' : f.toNat < S.w.toNat := hf
  have := Nat.mul_le_mul_right S.w.toNat (show i.toNat + 1 ≤ (cntW S m 0).toNat by omega)
  rw [Nat.add_mul] at this
  omega

section slots
variable {m m' : Mem} (hT : StoreTr S m m') (hG : GrowR S m) (hko : koW S.sa m 0 = 0)
include hT hG hko

theorem ext_slot_toNat : (2 + 2 * knW S.sa m 0).toNat = 2 + 2 * (knW S.sa m 0).toNat := by
  have := (knW_toNat S m hG 0 (by decide)).1
  rw [UInt64.toNat_add, UInt64.toNat_mul]; simp; omega

theorem knW_trunc0 : knW S.sa m' 0 = knW S.sa m 0 ∧ koW S.sa m' 0 = koW S.sa m 0 := by
  have e : (2 + 2 * (rdW (m.arr64 S.sa) 0 + SN0)).toNat = 2 + 2 * (knW S.sa m 0).toNat :=
    ext_slot_toNat S hT hG hko
  simp only [knW, koW, tierA_zero', hT.sa0]
  constructor
  · rw [rdW_extract]; rw [e]; simp only [UInt64.toNat_zero]; omega
  · rw [rdW_extract]; rw [e]; simp only [UInt64.toNat_one]; omega

theorem slots_trunc0 (j : Word) (hj : j < nSl S m 0) :
    slotW S m' 0 j = slotW S m 0 j ∧ slotK S m' 0 j = slotK S m 0 j := by
  have e := ext_slot_toNat S hT hG hko
  obtain ⟨hn, ho⟩ := knW_trunc0 S hT hG hko
  have hkr : krW S.sa m' 0 = krW S.sa m 0 := by simp only [krW, ho]
  have hkr2 : (krW S.sa m 0).toNat = 2 := by simp only [krW, hko]; rfl
  obtain ⟨k1, k2⟩ := kslot_toNat S m hG 0 (by decide) j hj
  have hjn : j.toNat < (knW S.sa m 0).toNat := hj
  have hbase : baseW m' 0 = baseW m 0 := by simp only [baseW, hT.ctl]
  simp only [slotW, slotK, slotV, hkr, hbase, tierA_zero', hT.sa0]
  constructor
  · rw [rdW_extract]; rw [e, k1]; omega
  · rw [rdW_extract]; rw [e, k2]; omega

end slots

/-- **A store keeps its relation when its tier 0 is cut to its extent.** -/
theorem storeR_trunc (hS : S.WF) (hK : KFrame S hs KP) {m m' : Mem} (hT : StoreTr S m m')
    (hR : RTrans S R hs m m') {on : Bool} {tbP tbS : Tbl α (Idx k) δ}
    (h : StoreR S R hs KP m on tbP tbS) : StoreR S R hs KP m' on tbP tbS := by
  obtain ⟨⟨hctl, hb⟩, hfl, hT0, hT1, hG⟩ := h
  have hko : koW S.sa m 0 = 0 := hG.1.2.2.2.2 rfl
  have hcnt : ∀ t, cntW S m' t = cntW S m t := fun t => by simp only [cntW, hT.ctl]
  refine ⟨⟨by rw [hT.ctl]; exact hctl, by rw [hT.ctl]; exact hb⟩, by rw [hT.ctl]; exact hfl,
    ?_, ?_, ?_⟩
  · -- tier 0
    obtain ⟨hc, hcap, hrs, hrec, hsome, hback, hsl, hkp, hrun⟩ := hT0
    have hc27 : (cntW S m 0).toNat ≤ 2 ^ 27 := by rw [hc]; exact hcap
    have hfl0 : ∀ i : Word, i.toNat < tbP.nodes.size → ∀ f, f < S.w →
        fld S m' 0 i f = fld S m 0 i f := fun i hi f hf =>
      fld_trunc0 S hS hT hc27 (by rw [hc]; exact hi) hf
    have hn : nSl S m' 0 = nSl S m 0 := (knW_trunc0 S hT hG hko).1
    have hsl0 := slots_trunc0 S hT hG hko
    have hpos : 0 < nSl S m 0 := by
      have := (lay S m hG 0 (by decide)).1
      exact UInt64.lt_iff_toNat_lt.mpr (by simp; omega)
    refine ⟨by rw [hcnt]; exact hc, hcap, ?_, fun i a ha => ?_, hsome, hback, ?_, ?_, ?_⟩
    · rw [tierA_zero', hT.ra0, size_extract0, mul_toNat_small hc27 hS.w_le, hc]
      rw [tierA_zero'] at hrs
      exact Nat.le_min.mpr ⟨by rw [Nat.mul_comm]; exact Nat.le_refl _, hrs⟩
    · have hi := (Array.getElem?_eq_some_iff.mp ha).1
      exact (hR 0 i (hfl0 i hi)).1 a (hrec i a ha)
    · intro j hj; rw [hn] at hj; rw [(hsl0 j hj).1]; exact hsl j hj
    · intro j hj hne; rw [hn] at hj; rw [(hsl0 j hj).1] at hne ⊢; rw [(hsl0 j hj).2]
      have hle := hsl j hj
      have hv : (slotW S m 0 j - 1).toNat < tbP.nodes.size := by
        have : (slotW S m 0 j).toNat ≠ 0 := fun h0 => hne (UInt64.toNat_inj.mp (by simpa using h0))
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
      exact hK m m' 0 _ (hfl0 _ hv) (hR 0 _ (hfl0 _ hv)).2 _ (hkp j hj hne)
    · intro i hi
      obtain ⟨d, h1, h2⟩ := hrun i hi
      have hh : hs m' 0 i = hs m 0 i := (hR 0 i (hfl0 i hi)).2
      have hw : ∀ e, walkW (nSl S m 0) (homeW (hs m 0 i) (nSl S m 0)) e < nSl S m 0 := fun e =>
        walkW_lt _ _ _ (homeW_lt _ _ hpos)
      refine ⟨d, ?_, fun e he => ?_⟩
      · simp only [homeS, hn, hh] at h1 ⊢; rw [(hsl0 _ (hw d)).1]; exact h1
      · simp only [homeS, hn, hh] at h2 ⊢; rw [(hsl0 _ (hw e)).1]; exact h2 e he
  · -- tier 1
    have hra : m'.arr64 (tierA S.ra 1) = m.arr64 (tierA S.ra 1) := by rw [tierA_one', hT.ra1]
    have hsa : m'.arr64 (tierA S.sa 1) = m.arr64 (tierA S.sa 1) := by rw [tierA_one', hT.sa1]
    have hfl1 : ∀ i f, fld S m' 1 i f = fld S m 1 i f := fun i f => by simp only [fld, hra]
    exact tierR_mono S R hs KP m m' 1 tbS hra hsa (hcnt 1) (by simp only [baseW, hT.ctl])
      (fun i a h => (hR 1 i (fun f _ => hfl1 i f)).1 a h) (fun i => (hR 1 i (fun f _ => hfl1 i f)).2)
      (fun i K h => hK m m' 1 i (fun f _ => hfl1 i f) (hR 1 i (fun f _ => hfl1 i f)).2 K h) hT1
  · -- layout
    obtain ⟨hn, ho⟩ := knW_trunc0 S hT hG hko
    have e := ext_slot_toNat S hT hG hko
    obtain ⟨⟨a0, a1, a2, a3, -⟩, h1⟩ := hG
    refine ⟨⟨?_, by rw [hn]; exact a1, by rw [hn]; exact a2, ?_, fun _ => by rw [ho, hko]⟩, ?_⟩
    · rw [tierA_zero', hT.sa0, size_extract0]; rw [tierA_zero'] at a0; omega
    · rw [hn, ho, tierA_zero', hT.sa0, size_extract0, e, hko]; rw [tierA_zero', hko] at a3
      simp only [UInt64.toNat_zero, Nat.add_zero] at a3 ⊢
      exact Nat.le_min.mpr ⟨Nat.le_refl _, a3⟩
    · simpa only [TierLay, knW, koW, tierA_one', hT.sa1] using h1

end store

/-! ## Instances whose node relation reads only its record -/

section loc
variable {α : Type} {S : Schema} {R : Mem → Word → Word → α → Prop} {hs : Mem → Word → Word → Word}

/-- **A node relation local to its record has the transfer** between memories of one shape. -/
theorem rTrans_local (hS : S.WF) (hF : RFrame S R hs) (hL : RLocal S R hs [] []) {m m' : Mem}
    (hw : m'.words.size = m.words.size) : RTrans S R hs m m' := by
  intro t i hf
  let m₁ := (m.setA S.ra (m'.arr64 S.ra)).setA (S.ra + 256) (m'.arr64 (S.ra + 256))
  have hw1 : (m.setA S.ra (m'.arr64 S.ra)).words.size = m.words.size := Mem.setA_words ..
  have hne : S.ra ≠ S.ra + 256 := Nat.ne_of_lt (Nat.lt_add_of_pos_right (by decide))
  have e0 : m₁.arr64 S.ra = m'.arr64 S.ra := by
    simp only [m₁]; rw [Mem.setA_arr, ite_eq_right (fun h => hne h.1)]
    exact Mem.setA_self m m' _ hw
  have e1 : m₁.arr64 (S.ra + 256) = m'.arr64 (S.ra + 256) := Mem.setA_self _ m' _ (hw.trans hw1.symm)
  have eo : ∀ b, b ≠ S.ra → b ≠ S.ra + 256 → m₁.arr64 b = m.arr64 b := fun b h1 h2 => by
    simp only [m₁]; rw [Mem.setA_arr, ite_eq_right (fun h => h2 h.1), Mem.setA_arr, ite_eq_right (fun h => h1 h.1)]
  have et : ∀ t, m₁.arr64 (tierA S.ra t) = m'.arr64 (tierA S.ra t) := fun t => by
    rcases tierA_cases' S.ra t with e | e <;> rw [e]
    · exact e0
    · exact e1
  have hctl : m₁.arr64 CTL = m.arr64 CTL := eo CTL hS.ra_ctl.symm (by simp [CTL])
  have hout : OutEq S m m₁ := ⟨fun b h1 h1' _ _ _ => eo b h1 h1', by rw [hctl]⟩
  have hf1 : ∀ f, f < S.w → fld S m₁ t i f = fld S m t i f := fun f hf' => by
    simp only [fld, et]; exact hf f hf'
  have h1 := hF m m₁ t i hout hf1
  have h2 := hL m₁ m' (fun t => (et t).symm) (by simp) (by simp)
  exact ⟨fun a ha => h2.1 t i a (h1.1 a ha), (h2.2 t i).trans h1.2⟩

end loc

end L.Arena
