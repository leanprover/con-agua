import ConAgua.Arena.FreezeTrunc

/-!
# A fresh worker memory, part 1: what `freshMem` does to each array (lane parmode)

`freshMem m` (`FreezeRel.lean`) is `truncFrozen m` with `CTL` cut to its seed (its first 256
words, then zeros) and every other array of `freshZ` zero. It is reached in two frames:

* `ctlCut t`: `t` with `CTL` cut (`ctlCut_frame`: a `MemFrame [] (hiC n)`, the `CTL` words from
  256 on; no relation reads them, every frame lemma takes them);
* `freshMem m` from `ctlCut (truncFrozen m)`: a `MemFrame freshZ []` (`fresh_frame`), the arrays of
  `freshZ` zero (`fresh_zero`) and `CTL` the same.

Beside it, the generic pieces: a memo over a zero array is the empty memo (`memoRV_zeros`), and a
store whose tier-1 arrays are zeroed keeps its relation when its scratch tier is empty
(`storeR_fresh`).
-/

namespace L.Arena

open ConRon.Arena

/-! ## `CTL` cut to its seed -/

theorem rdW_zeros (n : Nat) (x : Word) : rdW (zeros n) x = 0 := by
  simp only [rdW, zeros]
  by_cases h : x.toNat < n
  · simp [h]
  · simp [h]

theorem freshCtl_size (c : Array Word) : (freshCtl c).size = c.size := by
  simp only [freshCtl, zeros, Array.size_append, size_extract0, Array.size_replicate]; omega

theorem freshCtl_empty : freshCtl #[] = #[] := by decide

theorem rdW_freshCtl (c : Array Word) (x : Word) :
    rdW (freshCtl c) x = if x.toNat < 256 then rdW c x else 0 := by
  simp only [rdW, freshCtl, zeros]
  rw [Array.getElem?_append]
  split
  · rename_i h
    have h1 : x.toNat < 256 := by rw [size_extract0] at h; omega
    rw [ite_eq_left h1, get?_extract c h1]
  · rename_i h
    rw [size_extract0] at h
    rw [Array.getElem?_replicate]
    split
    · split
      · rename_i h1 h2; omega
      · rfl
    · split
      · rename_i h1 h2
        have : c.size ≤ x.toNat := by omega
        simp [Array.getElem?_eq_none this]
      · rfl

/-- The `CTL` words from 256 below `n` (as a list, for `MemFrame`). -/
def hiC (n : Nat) : List Word :=
  ((List.range n).filter (fun k => 256 ≤ k ∧ k < 2 ^ 64)).map UInt64.ofNat

theorem hiC_ge {n : Nat} {x : Word} (h : x ∈ hiC n) : 256 ≤ x.toNat := by
  simp only [hiC, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨k, ⟨-, h1, h2⟩, rfl⟩ := h
  rw [UInt64.toNat_ofNat_of_lt' h2]; exact h1

theorem hiC_mem {n : Nat} {x : Word} (h1 : 256 ≤ x.toNat) (h2 : x.toNat < n) : x ∈ hiC n := by
  simp only [hiC, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨x.toNat, ⟨h2, h1, x.toNat_lt⟩, UInt64.ofNat_toNat⟩

/-- `t` with `CTL` cut to its seed. -/
def ctlCut (t : Mem) : Mem := t.setA CTL (freshCtl (t.arr64 CTL))

theorem ctlCut_arr (t : Mem) (b : ArrId) :
    (ctlCut t).arr64 b = if b = CTL then freshCtl (t.arr64 CTL) else t.arr64 b := by
  rw [ctlCut, Mem.setA_arr]
  by_cases hb : b = CTL
  · subst hb
    by_cases hs : CTL < t.words.size
    · simp [hs]
    · simp only [hs, and_false, ↓reduceIte]
      rw [Mem.arr64_oob t CTL hs, freshCtl_empty]
  · simp [hb]

theorem ctlCut_words (t : Mem) : (ctlCut t).words.size = t.words.size := Mem.setA_words ..

/-- **Cutting `CTL` is a frame of the `CTL` words from 256 on.** -/
theorem ctlCut_frame (t : Mem) : MemFrame [] (hiC (t.arr64 CTL).size) t (ctlCut t) := by
  refine ⟨fun b _ hb => by rw [ctlCut_arr, ite_eq_right hb], fun x hx => ?_, fun b => ?_, ctlCut_words t⟩
  · rw [ctlCut_arr, ite_eq_left rfl, rdW_freshCtl]
    split
    · rfl
    · rename_i h
      have : (t.arr64 CTL).size ≤ x.toNat :=
        Nat.le_of_not_lt fun hc => hx (hiC_mem (by omega) hc)
      simp [rdW, Array.getElem?_eq_none this]
  · rw [ctlCut_arr]; split
    · rename_i h; subst h; exact freshCtl_size _
    · rfl

/-! ## The fresh memory -/

theorem freshMem_words (m : Mem) : (freshMem m).words.size = (truncFrozen m).words.size := by
  simp [freshMem]

theorem freshMem_arr (m : Mem) (b : ArrId) : (freshMem m).arr64 b =
    if b = CTL then freshCtl ((truncFrozen m).arr64 CTL)
    else if b ∈ freshZ then zeros ((truncFrozen m).arr64 b).size else (truncFrozen m).arr64 b := by
  by_cases h : b < (truncFrozen m).words.size
  · have e : (freshMem m).arr64 b = (fun a =>
        if a = CTL then freshCtl ((truncFrozen m).arr64 CTL)
        else if a ∈ freshZ then zeros ((truncFrozen m).arr64 a).size
        else (truncFrozen m).arr64 a) b := by
      simp only [freshMem, Mem.arr64, Array.getD_eq_getD_getElem?, Array.getElem?_map,
        Array.getElem?_range, h, ↓reduceIte, Option.map_some, Option.getD_some]
    rw [e]
  · have ho : ∀ c, ¬ c < (truncFrozen m).words.size → (truncFrozen m).arr64 c = #[] :=
      fun c hc => Mem.arr64_oob _ c hc
    rw [Mem.arr64_oob _ b (by rw [freshMem_words]; exact h)]
    split
    · rename_i hb; subst hb; rw [ho _ h, freshCtl_empty]
    · split
      · rw [ho _ h]; rfl
      · rw [ho _ h]

/-- **The fresh memory from the cut one is a frame of `freshZ`.** -/
theorem fresh_frame (m : Mem) : MemFrame freshZ [] (ctlCut (truncFrozen m)) (freshMem m) := by
  refine ⟨fun b hb hc => ?_, fun x _ => ?_, fun b => ?_, ?_⟩
  · rw [freshMem_arr, ctlCut_arr, ite_eq_right hc, ite_eq_right hc, ite_eq_right hb]
  · rw [freshMem_arr, ctlCut_arr, ite_eq_left rfl, ite_eq_left rfl]
  · rw [freshMem_arr, ctlCut_arr]
    split
    · rfl
    · split
      · simp [zeros]
      · rfl
  · rw [freshMem_words, ctlCut_words]

theorem fresh_ctl (m : Mem) : (freshMem m).arr64 CTL = (ctlCut (truncFrozen m)).arr64 CTL := by
  rw [freshMem_arr, ctlCut_arr, ite_eq_left rfl, ite_eq_left rfl]

/-- **An array of `freshZ` other than `CTL` is zero** in the fresh memory. -/
theorem fresh_zero (m : Mem) {b : ArrId} (hb : b ∈ freshZ) (hc : b ≠ CTL) (x : Word) :
    rdW ((freshMem m).arr64 b) x = 0 := by
  rw [freshMem_arr, ite_eq_right hc, ite_eq_left hb, rdW_zeros]

/-! ## Memos over a zero array -/

section memo
variable {κ ν : Type} [BEq κ] [Hashable κ]

/-- **A memo over a zero array is the empty memo**, at the `CTL` of a related memory. -/
theorem memoRV_zeros (S : MemoSch) (K : MemoKey κ) (VR : Mem → Word → ν → Prop) {m m' : Mem}
    {mp : Std.HashMap κ ν} (hR : MemoRV S K VR m mp) (hc : m'.arr64 CTL = m.arr64 CTL)
    (hz : ∀ x, rdW (m'.arr64 S.arr) x = 0) : MemoRV S K VR m' (∅ : Std.HashMap κ ν) := by
  have he : epG S m' = epG S m := by simp only [epG, hc]
  have hne : epG S m ≠ 0 := hR.2.1
  have hpos : 0 < (epG S m).toNat := by
    rcases Nat.eq_zero_or_pos (epG S m).toNat with h | h
    · exact absurd (UInt64.toNat_inj.mp (by simpa using h)) hne
    · exact h
  exact memoRV_fresh S K VR m' (by rw [hc]; exact hR.1) (by rw [he]; exact hne)
    (by rw [hz, he]; simpa using hpos) (fun j _ => by simp only [mstG, hz, he]; simpa using hpos)

theorem memoRG_zeros (S : MemoSch) (K : MemoKey κ) {dv : Word → ν} {m m' : Mem}
    {mp : Std.HashMap κ ν} (hR : MemoRG S K dv m mp) (hc : m'.arr64 CTL = m.arr64 CTL)
    (hz : ∀ x, rdW (m'.arr64 S.arr) x = 0) : MemoRG S K dv m' (∅ : Std.HashMap κ ν) :=
  memoRV_zeros S K _ hR hc hz

end memo

/-! ## A store whose scratch tier is empty, its tier-1 arrays zeroed -/

section store
variable {α δ : Type} {k : IdxKind} [BEq α] [Hashable α]
variable (S : Schema) (R : Mem → Word → Word → α → Prop) (hs : Mem → Word → Word → Word)
  (KP : Mem → Word → Word → Word → Prop)

/-- **A store keeps its relation when its tier-1 slot array is zeroed**, its scratch table empty,
`CTL` and the tier-0 arrays kept (and the node relation transferred, `RTrans`). -/
theorem storeR_fresh (hK : KFrame S hs KP) {m m' : Mem} (hc : m'.arr64 CTL = m.arr64 CTL)
    (hra : m'.arr64 S.ra = m.arr64 S.ra) (hsa : m'.arr64 S.sa = m.arr64 S.sa)
    (hsa1 : ∀ x, rdW (m'.arr64 (S.sa + 256)) x = 0)
    (hsz : (m'.arr64 (S.sa + 256)).size = (m.arr64 (S.sa + 256)).size)
    (hR : RTrans S R hs m m') {on : Bool} {tbP tbS : Tbl α (Idx k) δ} (h0 : tbS.nodes.size = 0)
    (h : StoreR S R hs KP m on tbP tbS) : StoreR S R hs KP m' on tbP tbS := by
  obtain ⟨⟨hctl, hb⟩, hfl, hT0, hT1, hG⟩ := h
  have hf0 : ∀ i f, fld S m' 0 i f = fld S m 0 i f := fun i f => by simp only [fld, tierA_zero', hra]
  refine ⟨⟨by rw [hc]; exact hctl, by rw [hc]; exact hb⟩, by rw [hc]; exact hfl, ?_, ?_, ?_⟩
  · exact tierR_mono S R hs KP m m' 0 tbP (by rw [tierA_zero']; exact hra)
      (by rw [tierA_zero']; exact hsa) (by simp only [cntW, hc]) (by simp only [baseW, hc])
      (fun i a h => (hR 0 i (fun f _ => hf0 i f)).1 a h) (fun i => (hR 0 i (fun f _ => hf0 i f)).2)
      (fun i K h => hK m m' 0 i (fun f _ => hf0 i f) (hR 0 i (fun f _ => hf0 i f)).2 K h) hT0
  · obtain ⟨hc', hcap, -, -, -, hback, -, -, -⟩ := hT1
    have hnone : ∀ (i : Word) (a : α), tbS.nodes[i.toNat]? = some a → False := fun i a ha => by
      have := (Array.getElem?_eq_some_iff.mp ha).1; omega
    have hsl : ∀ j, slotW S m' 1 j = 0 := fun j => by
      simp only [slotW, slotV, slotRd, tierA_one', hsa1]; simp
    refine ⟨by simp only [cntW, hc]; exact hc', hcap, by rw [h0]; simp,
      fun i a ha => (hnone i a ha).elim, fun i a ha => (hnone i a ha).elim, hback,
      fun j _ => by rw [hsl]; simp, fun j _ hne => absurd (hsl j) hne,
      fun i hi => absurd hi (by omega)⟩
  · obtain ⟨h0', ⟨a0, a1, a2, a3, -⟩⟩ := hG
    refine ⟨?_, ?_⟩
    · simpa only [TierLay, knW, koW, tierA_zero', hsa] using h0'
    · have hk : knW S.sa m' 1 = 8 := by simp only [knW, tierA_one', hsa1]; rfl
      have ho : koW S.sa m' 1 = 0 := by simp only [koW, tierA_one', hsa1]
      rw [tierA_one'] at a0 a3
      refine ⟨by rw [tierA_one', hsz]; exact a0, by rw [hk]; decide, by rw [hk]; decide, ?_,
        fun h => absurd h (by decide)⟩
      rw [hk, ho, tierA_one', hsz]
      simp only [UInt64.toNat_zero]
      have : (8 : Word).toNat = 8 := rfl
      rw [this]; omega

end store

/-! ## The pool below a tier-0 top -/

/-- The pool's reads below the top are kept, the top is kept and is in tier 0 (the saved tier-0
top `PT0[0]` may change: `PoolOK` and `SliceOK` read it only while the top is in tier 1). -/
structure PoolTr0 (m m' : Mem) : Prop where
  top : m'.top = m.top
  low : m.top.toNat < 2 ^ 40
  v : Agree (vpool m') (vpool m) m.top.toNat
  t : Agree (tpool m') (tpool m) m.top.toNat

theorem PoolTr0.rslice {m m' : Mem} (h : PoolTr0 m m') {t o l : Word} (hs : RSlice m t o l) :
    RSlice m' t o l := by
  obtain ⟨⟨h1, -⟩, h3⟩ := hs
  exact ⟨⟨by rw [h.top]; exact h1, .inl (by rw [h.top]; exact h.low)⟩, h3⟩

/-- A memory that agrees with `m` on the pool's arrays and `CTL` has `m`'s pool. -/
theorem PoolTr0.left {m m₁ m' : Mem} (h : PoolTr0 m m') (h0 : m₁.arr64 POOL = m.arr64 POOL)
    (h1 : m₁.arr64 POOL1 = m.arr64 POOL1) (hc : m₁.arr64 CTL = m.arr64 CTL) : PoolTr0 m₁ m' := by
  have ht : m₁.top = m.top := by simp only [Mem.top, hc]
  refine ⟨h.top.trans ht.symm, by rw [ht]; exact h.low, ?_, ?_⟩
  · rw [vpool_congr h0 h1, ht]; exact h.v
  · rw [tpool_congr h0 h1, ht]; exact h.t

/-- **A memory with the same `POOL` and `CTL`, the top in tier 0, has the same pool.** -/
theorem poolTr0_of {m m' : Mem} (h0 : m'.arr64 POOL = m.arr64 POOL)
    (hc : m'.arr64 CTL = m.arr64 CTL) (htop : m.top.toNat < 2 ^ 40) : PoolTr0 m m' := by
  have hv : Agree (vpool m') (vpool m) m.top.toNat := fun j hj => by
    rw [vpool_getNat? _ j (by omega), vpool_getNat? _ j (by omega), prd_nat _ j (by omega),
      prd_nat _ j (by omega), ite_eq_left (by omega), h0]
  refine ⟨by simp only [Mem.top, hc], htop, hv, fun j hj => ?_⟩
  rw [tpool_vpool _ j (by omega), tpool_vpool _ j (by omega)]; exact hv j hj

section pooltab
variable {α : Type} {S : Schema} {R : Mem → Word → Word → α → Prop} {hs : Mem → Word → Word → Word}

/-- **A node relation that reads its record and the pool below the top has the transfer**
to a memory with the pool kept (`PoolTr0`). -/
theorem rTrans_pool0 (hF : RFrame S R hs)
    (hP : ∀ m₁ m₂ : Mem, (∀ t, m₂.arr64 (tierA S.ra t) = m₁.arr64 (tierA S.ra t)) → PoolTr0 m₁ m₂ →
      (∀ t i a, R m₁ t i a → R m₂ t i a) ∧ ∀ t i, hs m₂ t i = hs m₁ t i)
    (hx : ∀ b ∈ [POOL, POOL1, CTL], b ≠ S.ra ∧ b ≠ S.ra + 256)
    {m m' : Mem} (hw : m'.words.size = m.words.size) (hp : PoolTr0 m m') : RTrans S R hs m m' := by
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
  have hb : ∀ b ∈ [POOL, POOL1, CTL], m₁.arr64 b = m.arr64 b := fun b hb' =>
    eo b (hx b hb').1 (hx b hb').2
  have hctl : m₁.arr64 CTL = m.arr64 CTL := hb CTL (by simp)
  have hout : OutEq S m m₁ := ⟨fun b h1 h1' _ _ _ => eo b h1 h1', by rw [hctl]⟩
  have hf1 : ∀ f, f < S.w → fld S m₁ t i f = fld S m t i f := fun f hf' => by
    simp only [fld, et]; exact hf f hf'
  have h1 := hF m m₁ t i hout hf1
  have h2 := hP m₁ m' (fun t => (et t).symm) (hp.left (hb POOL (by simp)) (hb POOL1 (by simp)) hctl)
  exact ⟨fun a ha => h2.1 t i a (h1.1 a ha), (h2.2 t i).trans h1.2⟩

end pooltab

theorem RecRel_ptr0 {m m' : Mem} (hr : ∀ t, m'.arr64 (tierA REC t) = m.arr64 (tierA REC t))
    (hp : PoolTr0 m m') (t i : Word) (k : LitNode) (h : RecRel m t i k) : RecRel m' t i k := by
  obtain ⟨⟨N⟩ | ⟨s⟩⟩ := k
  · simp only [RecRel, NatRec_raw, hr] at h ⊢
    obtain ⟨h0, hsl, hnm, hpv, hh⟩ := h
    have hle := hsl.le
    exact ⟨h0, hp.rslice hsl, Agree.norm _ _ _ _ _ hp.v hle hnm,
      by rw [Agree.pv _ _ _ _ _ hp.v hle, hpv], by rw [Agree.hashN _ _ _ _ _ hp.t hle, hh]⟩
  · simp only [RecRel, StrRec_raw, hr] at h ⊢
    obtain ⟨h0, hsl, hw, hh⟩ := h
    have hle := hsl.le
    exact ⟨h0, hp.rslice hsl, by rw [Agree.sliceL _ _ _ _ _ hp.v hle, hw],
      by rw [Agree.hashN _ _ _ _ _ hp.t hle, hh]⟩

theorem NsRecRel_ptr0 {m m' : Mem} (hr : ∀ t, m'.arr64 (tierA NSREC t) = m.arr64 (tierA NSREC t))
    (hp : PoolTr0 m m') (t i : Word) (k : StrNode) (h : NsRecRel m t i k) : NsRecRel m' t i k := by
  simp only [NsRecRel_raw, nsQ, nsO, nsL, hr] at h ⊢
  obtain ⟨h0, hsl, hw, hh⟩ := h
  have hle := hsl.le
  exact ⟨h0, hp.rslice hsl, by rw [Agree.sliceL _ _ _ _ _ hp.v hle, hw],
    by rw [Agree.hashN _ _ _ _ _ hp.t hle, hh]⟩

theorem LsRecRel_ptr0 {m m' : Mem} (hr : ∀ t, m'.arr64 (tierA LSREC t) = m.arr64 (tierA LSREC t))
    (hp : PoolTr0 m m') (t i : Word) (k : ListNode) (h : LsRecRel m t i k) : LsRecRel m' t i k := by
  simp only [LsRecRel_raw, lsO, lsL, hr] at h ⊢
  obtain ⟨hsl, hw, hh⟩ := h
  have hle := hsl.le
  exact ⟨hp.rslice hsl, by rw [Agree.sliceL _ _ _ _ _ hp.v hle, hw],
    by rw [Agree.hashN _ _ _ _ _ hp.t hle, hh]⟩

end L.Arena
