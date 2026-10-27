import ConAgua.Arena.FreezeTruncArena

/-!
# The truncation theorem (lane parmode, docs/design/parmode.md, "Redesign", "Step 4")

`PhaseBStart.trunc`: what phase A leaves for phase B survives cutting every frozen array to its
extent (`truncFrozen`). Each relation reads a frozen array only below its extent: a store's
tier-0 records below `count₀ · w`, its slot table within `2 + 2 n` (`FreezeTruncStore.lean`),
the columns below `count₀`, the pool below its top (`FreezeTruncArena.lean`), `PINS` below 71,
`EREC` below `CTL[129]` (`erecP`), `PEND` below `3 CTL[130]`, the env index's tier-0 rows below
`2 · (name count)`, and the relations over the other arrays read nothing that changes
(`FreezeTruncKeep.lean`).

Three facts the truncation needs are invariants of the library relations: a frozen slot table
sits at word 2 (tier 0's offset word is `0`, `TierLay`; the extent `2 + 2 n` assumes it), `PoolOK`
bounds the saved tier-0 top `PT0[0]` by `POOL`'s size only while the top is in tier 1 (`POOL` is
cut to the top), and `PendR` bounds the pending count by `2^62` (so `PEND`'s extent `3 · CTL[130]`
does not wrap). `EnvKeysIn m fe` (every name the environment indexes, in its constant index and its table map, is a tier-0 name below its
table's count, which `EnvR` does not say) follows from the twin's invariant (`envKeysIn_of`), and
the scratch flag `CTL[1] = 0` (so the pool top is in tier 0) from `TwinPend.off`.
`PhaseBStart.trunc'` is the theorem without hypotheses.
-/

namespace L.Arena

open ConRon.Arena

/-! ## The pins -/

theorem PinsR.trunc {m : Mem} {p : Pins} (h : PinsR m p) : PinsR (truncFrozen m) p := by
  have hw : ∀ i, i < 71 → pinW (truncFrozen m) i = pinW m i := fun i hi => by
    simp only [pinW, truncFrozen_pins, getD_extract _ hi]
  refine ⟨fun h0 => ?_⟩
  have hf := h.full (by rwa [← hw 0 (by decide)])
  refine ⟨by rw [truncFrozen_pins, size_extract0]; have := hf.size; omega, hf.names_size,
    fun i hi => by rw [hw _ (by omega)]; exact hf.names_lt i hi,
    fun i hi => by rw [hw _ (by omega)]; exact hf.names i hi,
    by rw [hw _ (by decide), hw _ (by decide), hw _ (by decide)]; exact hf.lv_lt,
    by rw [hw _ (by decide)]; exact hf.emptyLevels, by rw [hw _ (by decide)]; exact hf.zeroLevel,
    by rw [hw _ (by decide)]; exact hf.sortOne,
    fun i hi => by rw [hw _ (by omega)]; exact hf.reserved_lt i hi, ?_⟩
  rw [hf.reserved]
  apply List.map_congr_left
  intro i hi
  rw [hw _ (by simp at hi; omega)]

/-! ## The record pool -/

theorem erecTop_trunc (m : Mem) : erecTop (truncFrozen m) = erecTop m := by
  simp only [erecTop, truncFrozen_ctl]

theorem erecP_trunc (m : Mem) : erecP (truncFrozen m) = erecP m := by
  simp only [erecP, erecTop_trunc, truncFrozen_erec]
  apply Array.ext_getElem?
  intro i
  simp only [Array.getElem?_extract, Nat.sub_zero, Nat.zero_add, Array.size_extract]
  by_cases h1 : i < erecTop m <;> by_cases h2 : i < (m.arr64 EREC).size <;> simp [h2]

theorem rdW_erec_trunc (m : Mem) {x : Word} (hx : x.toNat < erecTop m) :
    rdW ((truncFrozen m).arr64 EREC) x = rdW (m.arr64 EREC) x := by
  rw [truncFrozen_erec]; exact rdW_extract _ hx

theorem IWOK.trunc {m : Mem} (h : L.Ind.IWOK m) : L.Ind.IWOK (truncFrozen m) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hI : (truncFrozen m).arr64 L.Ind.IW = m.arr64 L.Ind.IW := truncFrozen_other m _ (by decide)
  have he : ((truncFrozen m).arr64 EREC).size = min (erecTop m) (m.arr64 EREC).size := by
    rw [truncFrozen_erec, size_extract0]
  have ht : L.Ind.erTop m = erecTop m := rfl
  simp only [L.Ind.IWOK, L.Ind.iwTop, L.Ind.erTop, hI, truncFrozen_ctl, he] at *
  refine ⟨h1, ?_, h3, by omega, h5⟩
  simp only [erecTop] at he ⊢; omega

theorem PinSetsR.trunc {m : Mem} {ips : List INatOpPinSet} (h : L.Rom.PinSetsR m ips) :
    L.Rom.PinSetsR (truncFrozen m) ips := by
  obtain ⟨h1, h2, h3⟩ := h
  have hc := truncFrozen_ctl m
  have ht := L.Rom.top_lt m
  refine ⟨by rw [hc]; exact h1, by rw [hc, erecTop_trunc]; exact h2, fun k hk => ?_⟩
  rw [hc, rdW_erec_trunc m (by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]; omega)]
  refine L.Rom.PinSetR.keep (h3 k hk) ⟨Nat.le_of_eq (erecTop_trunc m).symm, fun i hi => ?_⟩
  rw [truncFrozen_erec]
  simp only [Array.getElem?_extract, Nat.zero_add]
  by_cases h2 : i < (m.arr64 EREC).size <;> simp [hi, h2, Nat.lt_min]

/-! ## The pending checks -/

theorem PendR.trunc {m : Mem} {pend : Array PendingCheck}
    (h : PendR m pend) : PendR (truncFrozen m) pend := by
  have hp : 3 * pendCount m < 2 ^ 64 := by have := h.bound; omega
  have hc := truncFrozen_ctl m
  have hn : pendCount (truncFrozen m) = pendCount m := by simp only [pendCount, hc]
  have hp' : 3 * (rdW (m.arr64 CTL) 130).toNat < 2 ^ 64 := hp
  have he : (3 * rdW (m.arr64 CTL) 130).toNat = 3 * pendCount m := by
    simp only [pendCount]; rw [UInt64.toNat_mul]; simp; omega
  refine ⟨by rw [hn]; exact h.count, fun j hj => ?_, by rw [hn]; exact h.bound⟩
  have hj' : j < pendCount m := by rw [h.count]; exact hj
  have hr : ∀ i, i < 3 → nat? ((truncFrozen m).arr64 PEND) (3 * j + i) = nat? (m.arr64 PEND) (3 * j + i) :=
    fun i hi => by simp only [nat?, truncFrozen_pend, he, get?_extract _ (show 3 * j + i < 3 * pendCount m by omega)]
  rw [← h.recs j hj]
  simp only [decPend, erecP_trunc]
  rw [show 3 * j = 3 * j + 0 from rfl, hr 0 (by decide), hr 1 (by decide), hr 2 (by decide)]

/-! ## The environment -/

/-- The name table with tag `g` (`anonymous`, `str`, `num`). -/
def nmCS : Nat → ConsSch
  | 0 => nanonCS
  | 1 => nstrCS
  | _ => nnumCS

/-- The tier-0 name count of the name table with tag `g` (`anonymous`, `str`, `num`). -/
def nmCnt (m : Mem) (g : Nat) : Nat := (rdW (m.arr64 CTL) (UInt64.ofNat (nmCS g).ca.toNat)).toNat

/-- **Every name the environment indexes is a tier-0 name below its table's count**, in the
constant index and in the table map. -/
structure EnvKeysIn (m : Mem) (fe : IFEnv) : Prop where
  idx : ∀ n : NIdx, (fe.idx[n]?).isSome → rowTag n.word.toUInt64 ≤ 2 →
    rowTier n.word.toUInt64 = 0 ∧ rowIx n.word.toUInt64 + 1 < 2 * nmCnt m (rowTag n.word.toUInt64)
  tbls : ∀ n : NIdx, (fe.tbls[n]?).isSome → rowTag n.word.toUInt64 ≤ 2 →
    rowTier n.word.toUInt64 = 0 ∧ tblIx n.word.toUInt64 < nmCnt m (rowTag n.word.toUInt64)

theorem getD_extract' (a : Array Word) (e i : Nat) :
    (a.extract 0 e)[i]?.getD 0 = if i < e then a[i]?.getD 0 else 0 := by
  split
  · exact getD_extract a (by assumption)
  · rename_i h
    simp only [Array.getElem?_extract, Nat.sub_zero, Nat.zero_add]
    split
    · omega
    · rfl

section env
variable {m : Mem} (hcnt : ∀ g, g ≤ 2 → nmCnt m g ≤ 2 ^ 27)
include hcnt

/-- A tier-0 row array of the env index under the truncation. -/
theorem eix_trunc (g : Nat) (hg : g ≤ 2) :
    (truncFrozen m).arr64 (132 + g) = (m.arr64 (132 + g)).extract 0 (2 * nmCnt m g) := by
  have h2 : ∀ c : Word, c.toNat ≤ 2 ^ 27 → (2 * c).toNat = 2 * c.toNat := fun c hc => by
    rw [UInt64.toNat_mul]; simp; omega
  rcases (show g = 0 ∨ g = 1 ∨ g = 2 by omega) with rfl | rfl | rfl
  · rw [show 132 + 0 = EIXA from rfl, truncFrozen_eixa]; exact congrArg _ (h2 _ (hcnt 0 (by decide)))
  · rw [show 132 + 1 = EIXS from rfl, truncFrozen_eixs]; exact congrArg _ (h2 _ (hcnt 1 (by decide)))
  · rw [show 132 + 2 = EIXN from rfl, truncFrozen_eixn]; exact congrArg _ (h2 _ (hcnt 2 (by decide)))

theorem row_trunc (w : Word) :
    (rowC (truncFrozen m) w = rowC m w ∨ rowC (truncFrozen m) w = 0) ∧
    (rowTier w = 0 → rowTag w ≤ 2 → rowIx w + 1 < 2 * nmCnt m (rowTag w) →
      rowC (truncFrozen m) w = rowC m w ∧ rowP (truncFrozen m) w = rowP m w) ∧
    (rowTier w ≠ 0 → rowC (truncFrozen m) w = rowC m w ∧ rowP (truncFrozen m) w = rowP m w) := by
  have ht : rowTier w = 0 ∨ rowTier w = 1 := by simp only [rowTier]; omega
  unfold rowC rowP
  by_cases hg : rowTag w ≤ 2
  · simp only [hg, ↓reduceIte]
    rcases ht with ht | ht
    · have ha : rowArr w = 132 + rowTag w := by
        unfold rowArr; rw [ht]; show (132 + rowTag w + 8 * 0 : Nat) = 132 + rowTag w; omega
      rw [ha, eix_trunc hcnt _ hg, getD_extract', getD_extract']
      refine ⟨by split <;> simp, fun _ _ hr => ?_, fun h => absurd ht h⟩
      rw [ite_eq_left (by omega), ite_eq_left (by omega)]; exact ⟨rfl, rfl⟩
    · have ha : rowArr w ∉ fzSrcs := by
        have : rowArr w = 140 + rowTag w := by
          unfold rowArr; rw [ht]; show (132 + rowTag w + 8 * 1 : Nat) = 140 + rowTag w; omega
        rw [this]; rcases (show rowTag w = 0 ∨ rowTag w = 1 ∨ rowTag w = 2 by omega) with e | e | e <;>
          rw [e] <;> decide
      rw [truncFrozen_other m _ ha]
      exact ⟨.inl rfl, fun h => by omega, fun _ => ⟨rfl, rfl⟩⟩
  · simp [hg]

omit hcnt in
/-- A tier-0 table-row array under the truncation. -/
theorem tix_trunc (g : Nat) (hg : g ≤ 2) :
    (truncFrozen m).arr64 (129 + g) = (m.arr64 (129 + g)).extract 0 (nmCnt m g) := by
  rcases (show g = 0 ∨ g = 1 ∨ g = 2 by omega) with rfl | rfl | rfl
  · rw [show 129 + 0 = TIXA from rfl, truncFrozen_tixa]; rfl
  · rw [show 129 + 1 = TIXS from rfl, truncFrozen_tixs]; rfl
  · rw [show 129 + 2 = TIXN from rfl, truncFrozen_tixn]; rfl

omit hcnt in
theorem tblRow_trunc (w : Word) :
    (tblRow (truncFrozen m) w = tblRow m w ∨ tblRow (truncFrozen m) w = 0) ∧
    (rowTier w = 0 → rowTag w ≤ 2 → tblIx w < nmCnt m (rowTag w) →
      tblRow (truncFrozen m) w = tblRow m w) := by
  have ht : rowTier w = 0 ∨ rowTier w = 1 := by simp only [rowTier]; omega
  unfold tblRow
  by_cases hg : rowTag w ≤ 2
  · simp only [hg, ↓reduceIte]
    rcases ht with ht | ht
    · have ha : tblArr w = 129 + rowTag w := by
        unfold tblArr; rw [ht]; show (129 + rowTag w + 256 * 0 : Nat) = 129 + rowTag w; omega
      rw [ha, tix_trunc _ hg, getD_extract']
      refine ⟨by split <;> simp, fun _ _ hr => ?_⟩
      rw [ite_eq_left hr]
    · have ha : tblArr w ∉ fzSrcs := by
        have : tblArr w = 385 + rowTag w := by
          unfold tblArr; rw [ht]; show (129 + rowTag w + 256 * 1 : Nat) = 385 + rowTag w; omega
        rw [this]; rcases (show rowTag w = 0 ∨ rowTag w = 1 ∨ rowTag w = 2 by omega) with e | e | e <;>
          rw [e] <;> decide
      rw [truncFrozen_other m _ ha]
      exact ⟨.inl rfl, fun h => by omega⟩
  · simp [hg]

theorem EnvR.trunc {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    (hk : EnvKeysIn m fe) (h : EnvR dn m vis fe) : EnvR dn (truncFrozen m) vis fe := by
  have hN : (truncFrozen m).arr64 ECON = m.arr64 ECON := truncFrozen_other m _ (by decide)
  have hc := truncFrozen_ctl m
  -- a row the environment holds reads the same
  have hin : ∀ n : NIdx, rowTag n.word.toUInt64 ≤ 2 → (fe.idx[n]?).isSome →
      rowC (truncFrozen m) n.word.toUInt64 = rowC m n.word.toUInt64 ∧
      rowP (truncFrozen m) n.word.toUInt64 = rowP m n.word.toUInt64 := fun n hn hs => by
    obtain ⟨ht, hr⟩ := hk.idx n hs hn
    exact (row_trunc hcnt _).2.1 ht hn hr
  -- a row the environment does not hold is empty
  have hout : ∀ n : NIdx, rowTag n.word.toUInt64 ≤ 2 → fe.idx[n]? = none →
      rowC m n.word.toUInt64 = 0 := fun n hn hs => by
    have := h.keys n hn
    rw [hs] at this
    simp only [Option.map_none, rowW] at this
    split at this
    · assumption
    · simp at this
  -- a table row the environment holds reads the same, one it does not is empty
  have tin : ∀ n : NIdx, rowTag n.word.toUInt64 ≤ 2 → (fe.tbls[n]?).isSome →
      tblRow (truncFrozen m) n.word.toUInt64 = tblRow m n.word.toUInt64 := fun n hn hs => by
    obtain ⟨ht, hr⟩ := hk.tbls n hs hn
    exact (tblRow_trunc _).2 ht hn hr
  have tout : ∀ n : NIdx, rowTag n.word.toUInt64 ≤ 2 → fe.tbls[n]? = none →
      tblRow (truncFrozen m) n.word.toUInt64 = 0 := fun n hn hs => by
    have := h.tkeys n hn
    rw [hs] at this
    have h0 : tblRow m n.word.toUInt64 = 0 := by simpa using this.symm
    rcases (tblRow_trunc n.word.toUInt64).1 with e' | e'
    · rw [e']; exact h0
    · exact e'
  have hET : (truncFrozen m).arr64 ETAB = m.arr64 ETAB := truncFrozen_other m _ (by decide)
  refine ⟨h.vis, fun n hn => ?_, fun n hn h0 => ?_, ?_, fun n hn => ?_, fun n hn h0 => ?_, ?_⟩
  · cases e : fe.idx[n]? with
    | none =>
      have h0 := hout n hn e
      have : rowC (truncFrozen m) n.word.toUInt64 = 0 := by
        rcases (row_trunc hcnt n.word.toUInt64).1 with e' | e'
        · rw [e']; exact h0
        · exact e'
      simp only [rowW, this, ↓reduceIte, Option.map_none]
    | some r =>
      have := hin n hn (by simp [e])
      rw [← e, h.keys n hn]; simp only [rowW, this.1, this.2]
  · have hs : (fe.idx[n]?).isSome := by
      cases e : fe.idx[n]? with
      | some _ => rfl
      | none =>
        exfalso; apply h0
        rcases (row_trunc hcnt n.word.toUInt64).1 with e' | e' <;> rw [e']
        exact hout n hn e
    have := hin n hn hs
    rw [this.2, erecP_trunc]
    exact h.vals n hn (by rw [← this.1]; exact h0)
  · rw [← h.consts]; simp only [envConsts, envLen, hc, erecP_trunc, hN]
  · cases e : fe.tbls[n]? with
    | none => rw [tout n hn e]; simp
    | some t => rw [tin n hn (by simp [e]), ← e]; exact h.tkeys n hn
  · have hs : (fe.tbls[n]?).isSome := by
      cases e : fe.tbls[n]? with
      | some _ => rfl
      | none => exact absurd (tout n hn e) h0
    rw [tin n hn hs] at h0 ⊢
    rw [erecP_trunc]
    exact h.tvals n hn h0
  · rw [← h.tables]; simp only [envTables, tblCnt, hc, erecP_trunc, hET]

end env

/-! ## The whole relation -/

theorem ModeOK.trunc {m : Mem} (h : ModeOK m) : ModeOK (truncFrozen m) := by
  unfold ModeOK at *; simp only [Mem.flag, Mem.top, truncFrozen_ctl]; exact h

/-- The name counts of a related store fit in a handle's index. -/
theorem nmCnt_le {m : Mem} {a : AState} (h : ArenaR m a) (g : Nat) (hg : g ≤ 2) :
    nmCnt m g ≤ 2 ^ 27 := by
  rcases (show g = 0 ∨ g = 1 ∨ g = 2 by omega) with rfl | rfl | rfl
  · have := ConsR.cnt0 h.nanon (ca := nanonCS.ca.toNat) (by decide)
    have := h.nanon.cap 0 (by decide); simp at this; unfold nmCnt; simp only [nmCS]; omega
  · have := ConsR.cnt0 h.nstr (ca := nstrCS.ca.toNat) (by decide)
    have := h.nstr.cap 0 (by decide); simp at this; unfold nmCnt; simp only [nmCS]; omega
  · have := ConsR.cnt0 h.nnum (ca := nnumCS.ca.toNat) (by decide)
    have := h.nnum.cap 0 (by decide); simp at this; unfold nmCnt; simp only [nmCS]; omega

section main
variable {m : Mem} (htop : m.top.toNat < 2 ^ 40)
include htop

theorem CheckR.trunc {dn : NIdx → Option ConLeche.Name} {a : AState} {vis : Word} {fe : IFEnv}
    (hk : EnvKeysIn m fe) (h : CheckR dn m a vis fe) : CheckR dn (truncFrozen m) a vis fe :=
  ⟨h.arena.trunc htop, (keepNF_trunc m).coreR h.core, h.pins.trunc,
    h.env.trunc (nmCnt_le h.arena.1) hk, h.mode.trunc⟩

theorem LoopR.trunc {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {a : AState}
    {vis : Word} {fe : IFEnv} {pend : Array PendingCheck} {ds : Array IDeclaration}
    (hk : EnvKeysIn m fe) (h : LoopR pins dn m a vis fe pend ds) :
    LoopR pins dn (truncFrozen m) a vis fe pend ds :=
  ⟨h.check.trunc htop hk, h.pend.trunc, (keepNF_trunc m).declsF h.decls, IWOK.trunc h.iw,
    let ⟨pm, hm⟩ := h.pmemo; ⟨pm, (keepNF_trunc m).pmemoR hm⟩, PinSetsR.trunc h.pinsets⟩

end main

theorem LoopMem.trunc {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState}
    (h : LoopMem dn m a) : LoopMem dn (truncFrozen m) a := by
  have hk := keepNF_trunc m
  refine ⟨?_, by rw [hk.arr _ (by decide)]; exact h.spn, by rw [hk.arr _ (by decide)]; exact h.bstk,
    ?_, h.dnP⟩
  · rw [truncFrozen_erec, size_extract0]; have := h.erec; omega
  · have : pinW (truncFrozen m) 0 = pinW m 0 := by
      simp only [pinW, truncFrozen_pins, getD_extract _ (show 0 < 71 by decide)]
    rw [this]; exact h.flag

/-- With the scratch flag off (the twin's `scratchOn` is `false`), the pool top is in tier 0. -/
theorem top_tier0_of {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} (h : CheckR dn m a vis fe) (hoff : a.store.scratchOn = false) :
    m.top.toNat < 2 ^ 40 := by
  have hf := h.arena.1.app.flag
  rw [hoff] at hf
  have h0 : m.flag = 0 := by
    simp only [Mem.flag]
    have : rdW (m.arr64 CTL) 1 = 0 := by simpa using hf
    simpa only [rdW, UInt64.toNat_one] using this
  rcases h.mode with h1 | h1
  · exact absurd h0 h1
  · exact h1

/-- **The truncation theorem**: what phase A leaves for phase B survives cutting every frozen
array to its extent. -/
theorem PhaseBStart.trunc {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}
    {ds : Array IDeclaration} {fe : IFEnv} {pend : Array PendingCheck} {m : Mem} {a : AState}
    {v : Word} (hk : EnvKeysIn m fe) (h : PhaseBStart pins dn ds fe pend m a v) :
    PhaseBStart pins dn ds fe pend (truncFrozen m) a v :=
  have htop := top_tier0_of h.loop.check h.twin.off
  ⟨h.loop.trunc htop hk, h.mem.trunc, (keepNF_trunc m).coreMemos h.core, h.twin,
    (keepNF_trunc m).crOK h.cr⟩

/-! ## `EnvKeysIn` at phase B's start -/

theorem denoteN_view {st : NStore} {n : NIdx} {x : ConLeche.Name} (h : denoteN st n = some x) :
    (st.view n).isSome := by
  unfold denoteN at h
  rw [denoteNAux] at h
  cases e : st.view n with
  | none => rw [e] at h; simp at h
  | some _ => rfl

/-- A persistent name handle that denotes is a tier-0 name below its table's count. -/
theorem nameIn_of {m : Mem} {a : AState} (hR : ArenaR m a) {n : NIdx} {nm : ConLeche.Name}
    (hper : n.isPersistent = true) (hdn : denoteN a.store.ns n = some nm)
    (_hn : rowTag n.word.toUInt64 ≤ 2) :
    rowTier n.word.toUInt64 = 0 ∧ n.word.toUInt64.toNat % 2 ^ 27 < nmCnt m (rowTag n.word.toUInt64) := by
  have hv := denoteN_view hdn
  simp only [NStore.view, hper, ↓reduceIte, EStore.ns, NTables.get] at hv
  have hw : n.word.toUInt64.toNat = n.word.toNat := UInt32.toNat_toUInt64 _
  have hwl := n.word.toNat_lt
  have htier : n.word.toNat / 134217728 % 2 = 0 := by
    have := hper; simp only [Idx.isPersistent, Idx.tier, beq_iff_eq] at this
    have := congrArg UInt32.toNat this
    simpa [UInt32.toNat_mod, UInt32.toNat_div] using this
  have htag : ∀ g : UInt32, n.tag = g → n.word.toNat / 268435456 = g.toNat := fun g e => by
    have := congrArg UInt32.toNat e; simpa [Idx.tag, UInt32.toNat_div] using this
  have hidx : n.idxNat = n.word.toNat % 134217728 := by
    simp [Idx.idxNat, Idx.index, UInt32.toNat_mod]
  simp only [rowTag, rowTier, hw] at _hn ⊢
  refine ⟨htier, ?_⟩
  by_cases h0 : n.tag == NTag.anonymous
  · simp only [h0, ↓reduceIte, Option.isSome_map] at hv
    have e := htag _ (beq_iff_eq.mp h0)
    have hl := (Option.isSome_iff_exists.mp hv).choose_spec
    have hlt := (Array.getElem?_eq_some_iff.mp hl).1
    have hcnt := ConsR.cnt0 hR.nanon (ca := nanonCS.ca.toNat) (by decide)
    rw [e]; simp only [nmCnt, nmCS, NTag.anonymous, UInt32.toNat_zero] at hcnt ⊢
    rw [hidx] at hlt; omega
  by_cases h1 : n.tag == NTag.str
  · simp only [h0, h1, ↓reduceIte, Option.isSome_map, Bool.false_eq_true] at hv
    have e := htag _ (beq_iff_eq.mp h1)
    have hl := (Option.isSome_iff_exists.mp hv).choose_spec
    have hlt := (Array.getElem?_eq_some_iff.mp hl).1
    have hcnt := ConsR.cnt0 hR.nstr (ca := nstrCS.ca.toNat) (by decide)
    rw [e]; simp only [nmCnt, nmCS, NTag.str] at hcnt ⊢
    rw [hidx] at hlt; simp at hcnt ⊢; omega
  by_cases h2 : n.tag == NTag.num
  · simp only [h0, h1, h2, ↓reduceIte, Option.isSome_map, Bool.false_eq_true] at hv
    have e := htag _ (beq_iff_eq.mp h2)
    have hl := (Option.isSome_iff_exists.mp hv).choose_spec
    have hlt := (Array.getElem?_eq_some_iff.mp hl).1
    have hcnt := ConsR.cnt0 hR.nnum (ca := nnumCS.ca.toNat) (by decide)
    rw [e]; simp only [nmCnt, nmCS, NTag.num] at hcnt ⊢
    rw [hidx] at hlt; simp at hcnt ⊢; omega
  · simp [h0, h1, h2] at hv

/-- A table of a list that denotes has a structure name that denotes. -/
theorem denoteProjTableList_name {st : EStore} :
    ∀ (ts : List IProjTable) (xs : List ConLeche.ProjTable), Frontend.denoteProjTableList st ts = some xs →
    ∀ t ∈ ts, ∃ nm, denoteN st.ns t.structName = some nm
  | [], _, _, t, ht => by simp at ht
  | u :: us, xs, h, t, ht => by
    simp only [Frontend.denoteProjTableList] at h
    cases hu : Frontend.denoteProjTable st u with
    | none => rw [hu] at h; simp at h
    | some x =>
      cases hus : Frontend.denoteProjTableList st us with
      | none => rw [hu, hus] at h; simp at h
      | some xs' =>
        rcases List.mem_cons.mp ht with rfl | ht
        · unfold Frontend.denoteProjTable at hu
          split at hu
          · rename_i sn _ _ hsn _ _; exact ⟨sn, hsn⟩
          · simp at hu
        · exact denoteProjTableList_name us xs' hus t ht

/-- **Every name the environment indexes is a tier-0 name below its table's count**, at phase
B's start: the index is the list's (`IFEnvCoh`), a listed name is found (`IFEnvOK.hit`), so it
denotes, so its node exists, and it is persistent (`PersIFEnv`); a table's key is its table's
structure name (`IFEnvCoh`), which denotes (`denoteFEnv`) and is persistent. -/
theorem envKeysIn_of {m : Mem} {a : AState} {fe : IFEnv} {pend : List PendingCheck}
    (hR : ArenaR m a) (hT : TwinPend fe pend a) : EnvKeysIn m fe := by
  obtain ⟨env, pendP, hok, -, -⟩ := hT.fold
  have hcoh := hok.coh
  refine ⟨fun n hs hn => ?_, fun n hs hn => ?_⟩
  · obtain ⟨⟨c, ci⟩, hp⟩ := Option.isSome_iff_exists.mp hs
    have hc : c < fe.visibleBelow := by
      rw [hcoh.1]
      exact ConRon.Bridge.mkIFEnvGo_lt _ n c ci (by rw [← hcoh.idx n]; exact hp)
    have hf : fe.find? n = some ci := by simp [IFEnv.find?, hp, hc]
    obtain ⟨nm, c', hdn, -, -⟩ := hok.check.ienv.hit n ci hf
    have hper : n.isPersistent = true := (hok.persEnv.idx n _ hp).1
    obtain ⟨ht, hl⟩ := nameIn_of hR hper hdn hn
    exact ⟨ht, by simp only [rowIx]; omega⟩
  · obtain ⟨t, hp⟩ := Option.isSome_iff_exists.mp hs
    have hper : n.isPersistent = true := (hok.persEnv.tbls n t hp).1
    have hfind := hp
    rw [hcoh.tbls n, ConRon.Bridge.mkIFEnvTblsGo_find?] at hfind
    have hmem := List.mem_of_find?_eq_some hfind
    have hname : t.structName = n := by simpa using List.find?_some hfind
    have hden := hok.denote
    simp only [ConRon.Bridge.denoteFEnv] at hden
    obtain ⟨-, htabs⟩ := ConRon.Bridge.denoteIEnv_some.mp hden
    obtain ⟨nm, hdn⟩ := denoteProjTableList_name _ _ htabs t hmem
    rw [hname] at hdn
    exact nameIn_of hR hper hdn hn

/-- **The truncation theorem, without hypotheses** (the environment's discharged). -/
theorem PhaseBStart.trunc' {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}
    {ds : Array IDeclaration} {fe : IFEnv} {pend : Array PendingCheck} {m : Mem} {a : AState}
    {v : Word} (h : PhaseBStart pins dn ds fe pend m a v) :
    PhaseBStart pins dn ds fe pend (truncFrozen m) a v :=
  h.trunc (envKeysIn_of h.loop.check.arena.1 h.twin)

/-- `PhaseBStart.trunc'` (the name the lane asked for). -/
theorem PhaseBStart.trunc'' {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}
    {ds : Array IDeclaration} {fe : IFEnv} {pend : Array PendingCheck} {m : Mem} {a : AState}
    {v : Word} (h : PhaseBStart pins dn ds fe pend m a v) :
    PhaseBStart pins dn ds fe pend (truncFrozen m) a v :=
  h.trunc'

end L.Arena
