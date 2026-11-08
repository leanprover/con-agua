module

import ConAgua.Arena.FreezeTruncArena
import ConAgua.Arena.FreezeTruncKeep
public import ConAgua.Arena.FreezeRel

@[expose] public section

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
  sorry

/-! ## The record pool -/

theorem erecTop_trunc (m : Mem) : erecTop (truncFrozen m) = erecTop m := by
  simp only [erecTop, truncFrozen_ctl]

theorem erecP_trunc (m : Mem) : erecP (truncFrozen m) = erecP m := by
  sorry

theorem rdW_erec_trunc (m : Mem) {x : Word} (hx : x.toNat < erecTop m) :
    rdW ((truncFrozen m).arr64 EREC) x = rdW (m.arr64 EREC) x := by
  rw [truncFrozen_erec]; exact rdW_extract _ hx

theorem IWOK.trunc {m : Mem} (h : L.Ind.IWOK m) : L.Ind.IWOK (truncFrozen m) := by
  sorry

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

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem PendR.trunc {m : Mem}
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
-/

/-! ## The environment -/

/-- The name table with tag `g` (`anonymous`, `str`, `num`). -/
def nmCS : Nat → ConsSch
  | 0 => nanonCS
  | 1 => nstrCS
  | _ => nnumCS

/-- The tier-0 name count of the name table with tag `g` (`anonymous`, `str`, `num`). -/
def nmCnt (m : Mem) (g : Nat) : Nat := (rdW (m.arr64 CTL) (UInt64.ofNat (nmCS g).ca.toNat)).toNat

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **Every name the environment indexes is a tier-0 name below its table's count**, in the
constant index and in the table map. -/
structure EnvKeysIn (m : Mem) (fe : IFEnv) : Prop where
  idx : ∀ n : NIdx, (fe.idx[n]?).isSome → rowTag n.word.toUInt64 ≤ 2 →
    rowTier n.word.toUInt64 = 0 ∧ rowIx n.word.toUInt64 + 1 < 2 * nmCnt m (rowTag n.word.toUInt64)
  tbls : ∀ n : NIdx, (fe.tbls[n]?).isSome → rowTag n.word.toUInt64 ≤ 2 →
    rowTier n.word.toUInt64 = 0 ∧ tblIx n.word.toUInt64 < nmCnt m (rowTag n.word.toUInt64)
-/

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
    (truncFrozen m).arr64 ((132 + g : ArrId) : TieredArray) =
      (m.arr64 ((132 + g : ArrId) : TieredArray)).extract 0 (2 * nmCnt m g) := by
  have h2 : ∀ c : Word, c.toNat ≤ 2 ^ 27 → (2 * c).toNat = 2 * c.toNat := fun c hc => by
    rw [UInt64.toNat_mul]; simp; omega
  rcases (show g = 0 ∨ g = 1 ∨ g = 2 by omega) with rfl | rfl | rfl
  · rw [show (132 + 0 : ArrId) = EIXA from rfl, truncFrozen_eixa]; exact congrArg _ (h2 _ (hcnt 0 (by decide)))
  · rw [show (132 + 1 : ArrId) = EIXS from rfl, truncFrozen_eixs]; exact congrArg _ (h2 _ (hcnt 1 (by decide)))
  · rw [show (132 + 2 : ArrId) = EIXN from rfl, truncFrozen_eixn]; exact congrArg _ (h2 _ (hcnt 2 (by decide)))

/- ronsync2 stage 2: commented out (statement at the old twin/L)
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
        exact rowArr_tier0 hg ht
      rw [ha, eix_trunc hcnt _ hg, getD_extract', getD_extract']
      refine ⟨by split <;> simp, fun _ _ hr => ?_, fun h => absurd ht h⟩
      rw [ite_eq_left (by omega), ite_eq_left (by omega)]; exact ⟨rfl, rfl⟩
    · have ha : (rowArr w : TieredArray) ∉ fzSrcs := by
        have : rowArr w = 140 + rowTag w := by
          exact rowArr_tier1 hg ht
        rw [this]; rcases (show rowTag w = 0 ∨ rowTag w = 1 ∨ rowTag w = 2 by omega) with e | e | e <;>
          rw [e] <;> decide
      rw [truncFrozen_other m _ ha]
      exact ⟨.inl rfl, fun h => by omega, fun _ => ⟨rfl, rfl⟩⟩
  · simp [hg]
-/

omit hcnt in
/-- A tier-0 table-row array under the truncation. -/
theorem tix_trunc (g : Nat) (hg : g ≤ 2) :
    (truncFrozen m).arr64 (tixArr g) = (m.arr64 (tixArr g)).extract 0 (nmCnt m g) := by
  rcases (show g = 0 ∨ g = 1 ∨ g = 2 by omega) with rfl | rfl | rfl
  · rw [show tixArr 0 = TIXA from rfl, truncFrozen_tixa]; rfl
  · rw [show tixArr 1 = TIXS from rfl, truncFrozen_tixs]; rfl
  · rw [show tixArr 2 = TIXN from rfl, truncFrozen_tixn]; rfl

/- ronsync2 stage 2: commented out (statement at the old twin/L)
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
    · rw [tblArr_tier0 ht, tix_trunc _ hg, getD_extract']
      refine ⟨by split <;> simp, fun _ _ hr => ?_⟩
      rw [ite_eq_left hr]
    · have ha : tblArr w ∉ fzSrcs := by
        rw [tblArr_tier1 ht]; rcases tixArr_mem (rowTag w) with e | e | e <;> rw [e] <;> decide
      rw [truncFrozen_other m _ ha]
      exact ⟨.inl rfl, fun h => by omega⟩
  · simp [hg]
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem EnvR.trunc {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    (hk : EnvKeysIn m fe) (h : EnvR m vis fe) : EnvR (truncFrozen m) vis fe := by
  sorry
-/

end env

/-! ## The whole relation -/

theorem ModeOK.trunc {m : Mem} (h : ModeOK m) : ModeOK (truncFrozen m) := by
  unfold ModeOK at *; simp only [Mem.flag, Mem.top, truncFrozen_ctl]; exact h

/-- The name counts of a related store fit in a handle's index. -/
theorem nmCnt_le {m : Mem} {a : AState} (h : ArenaR m a) (g : Nat) (hg : g ≤ 2) :
    nmCnt m g ≤ 2 ^ 27 := by
  rcases (show g = 0 ∨ g = 1 ∨ g = 2 by omega) with rfl | rfl | rfl
  · have := ConsR.cnt0 h.nanon (ca := nanonCS.ca.toNat) (by decide)
    have := h.nanon.cap 0 (by decide)
    simp only [show nanonCS.wide = false from rfl, capS] at this; simp at this
    unfold nmCnt; simp only [nmCS]; omega
  · have := ConsR.cnt0 h.nstr (ca := nstrCS.ca.toNat) (by decide)
    have := h.nstr.cap 0 (by decide)
    simp only [show nstrCS.wide = false from rfl, capS] at this; simp at this
    unfold nmCnt; simp only [nmCS]; omega
  · have := ConsR.cnt0 h.nnum (ca := nnumCS.ca.toNat) (by decide)
    have := h.nnum.cap 0 (by decide)
    simp only [show nnumCS.wide = false from rfl, capS] at this; simp at this
    unfold nmCnt; simp only [nmCS]; omega

section main
variable {m : Mem} (htop : m.top.toNat < 2 ^ 40)
include htop

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem CheckR.trunc {dn : NIdx → Option ConLeche.Name} {a : AState} {vis : Word} {fe : IFEnv}
    (hk : EnvKeysIn m fe) (h : CheckR m a vis fe) : CheckR (truncFrozen m) a vis fe := by
  sorry
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem LoopR.trunc {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {a : AState}
    {vis : Word} {fe : IFEnv} {ds : Array IDeclaration}
    (hk : EnvKeysIn m fe) (h : LoopR pins m a vis fe ds) :
    LoopR pins (truncFrozen m) a vis fe ds := by
  sorry
-/

end main

theorem LoopMem.trunc {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState}
    (h : LoopMem dn m a) : LoopMem dn (truncFrozen m) a := by
  sorry

/-- With the scratch flag off (the twin's `scratchOn` is `false`), the pool top is in tier 0. -/
theorem top_tier0_of {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} (h : CheckR m a vis fe) (hoff : a.store.scratchOn = false) :
    m.top.toNat < 2 ^ 40 := by
  have hf := h.arena.base.app.flag
  rw [hoff] at hf
  have h0 : m.flag = 0 := by
    simp only [Mem.flag]
    have : rdW (m.arr64 CTL) 1 = 0 := by simpa using hf
    simpa only [rdW, UInt64.toNat_one] using this
  rcases h.mode with h1 | h1
  · exact absurd h0 h1
  · exact h1

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **The truncation theorem**: what phase A leaves for phase B survives cutting every frozen
array to its extent. -/
theorem PhaseBStart.trunc {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}
    {ds : Array IDeclaration} {fe : IFEnv} {m : Mem} {a : AState}
    {v : Word} (hk : EnvKeysIn m fe) (h : PhaseBStart pins dn ds fe pend m a v) :
    PhaseBStart pins dn ds fe pend (truncFrozen m) a v :=
  have htop := top_tier0_of h.loop.check h.twin.off
  ⟨h.loop.trunc htop hk, h.mem.trunc, (keepNF_trunc m).coreMemos h.core, h.twin,
    (keepNF_trunc m).crOK h.cr⟩
-/

/-! ## `EnvKeysIn` at phase B's start -/

theorem denoteN_view {st : NStore} {n : NIdx} {x : ConLeche.Name} (h : denoteN st n = some x) :
    (st.view n).isSome := by
  unfold denoteN at h
  rw [denoteNAux] at h
  cases e : st.view n with
  | none => rw [e] at h; simp at h
  | some _ => rfl

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- A persistent name handle that denotes is a tier-0 name below its table's count. -/
theorem nameIn_of {m : Mem} {a : AState} (hR : ArenaR m a) {n : NIdx} {nm : ConLeche.Name}
    (hper : n.isPersistent = true) (hdn : denoteN a.store.ns n = some nm)
    (hn : rowTag n.word.toUInt64 ≤ 2) :
    rowTier n.word.toUInt64 = 0 ∧ tblIx n.word.toUInt64 < nmCnt m (rowTag n.word.toUInt64) := by
  have hv := denoteN_view hdn
  simp only [NStore.view, hper, ↓reduceIte, EStore.ns, NTables.get] at hv
  have hw := word_lt32 n
  have hnr := rowTag_narrow hn
  have htier : rowTier n.word.toUInt64 = 0 := by
    have hp := decI_pers (k := .name) n.word.toUInt64 hw
    rw [decI_word, hper] at hp
    have : tierW n.word.toUInt64 = 0 := by simpa using hp.symm
    rw [← tierW_toNat_row, this]; rfl
  have htag : ∀ g : UInt32, n.tag = g → rowTag n.word.toUInt64 = g.toNat := fun g e => by
    have ht := decI_tag (k := .name) n.word.toUInt64 hw
    rw [decI_word, e] at ht
    have hl := rowTag_lt n.word.toUInt64
    rw [ht]; simp only [rowTag, UInt64.toNat_toUInt32] at hl ⊢; omega
  have hidx : n.idxNat = tblIx n.word.toUInt64 := by
    have := decI_idx (k := .name) n.word.toUInt64 hnr
    rwa [decI_word] at this
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
-/

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

/- ronsync2 stage 2: commented out (statement at the old twin/L)
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
    exact ⟨ht, by simp only [rowIx, tblIx] at hl ⊢; omega⟩
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
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **The truncation theorem, without hypotheses** (the environment's discharged). -/
theorem PhaseBStart.trunc' {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}
    {ds : Array IDeclaration} {fe : IFEnv} {m : Mem} {a : AState}
    {v : Word} (h : PhaseBStart pins dn ds fe pend m a v) :
    PhaseBStart pins dn ds fe pend (truncFrozen m) a v :=
  h.trunc (envKeysIn_of h.loop.check.arena.base h.twin)
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- `PhaseBStart.trunc'` (the name the lane asked for). -/
theorem PhaseBStart.trunc'' {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}
    {ds : Array IDeclaration} {fe : IFEnv} {m : Mem} {a : AState}
    {v : Word} (h : PhaseBStart pins dn ds fe pend m a v) :
    PhaseBStart pins dn ds fe pend (truncFrozen m) a v :=
  h.trunc'
-/

end L.Arena
