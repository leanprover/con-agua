import ConAgua.Arena.ArenaRel
import ConAgua.Arena.DerRel
import ConAgua.Arena.PromoteTwin

/-!
# The scratch flag `CTL[1]` written: the arena relation at the flags `onA b`

The promotion's bracket `pi_*` writes `CTL[1] := 0` around an interner and puts the old word
back. Under `ArenaR`, writing `CTL[1] := w` relates the same tables at the four stores' flags
`w != 0` (`onA`, `PromoteTwin.lean`): a table's relation reads the flag only in `StoreR`'s flag
clause (`storeR_flag`), the tiers read their counts, the slot base and their own arrays. The
memos and the derived ranges do not read `CTL[1]`.
-/

open ConRon.Arena

set_option linter.unusedSimpArgs false

namespace L.Arena

section flag
variable {α δ : Type} {k : IdxKind} [BEq α] [Hashable α]
variable (S : Schema) (R : Mem → Word → Word → α → Prop) (hs : Mem → Word → Word → Word)

theorem storeR_flag (hS : S.WF) (hfr : RFrame S R hs) (m : Mem) (on : Bool)
    (P Q : Tbl α (Idx k) δ) (h : StoreR S R hs m on P Q) (w : Word) :
    StoreR S R hs (m.set64 CTL 1 w) (w != 0) P Q := by
  obtain ⟨⟨hsz, hscb⟩, _, hP, hQ⟩ := h
  have hsz' : ((m.set64 CTL 1 w).arr64 CTL).size = (m.arr64 CTL).size := size_set64 _ _ _ _ _
  have h1 : (1 : Word).toNat < (m.arr64 CTL).size := by
    have := hS.ca.1; simp; omega
  have hrd : ∀ x, x ≠ 1 → rdW ((m.set64 CTL 1 w).arr64 CTL) x = rdW (m.arr64 CTL) x := by
    intro x hx; rw [rdW_set64]; simp [Ne.symm hx]
  have hra : (m.set64 CTL 1 w).arr64 S.ra = m.arr64 S.ra :=
    Mem.arr64_set64_ne _ _ _ _ _ hS.ra_ctl
  have hsa : (m.set64 CTL 1 w).arr64 S.sa = m.arr64 S.sa :=
    Mem.arr64_set64_ne _ _ _ _ _ hS.sa_ctl
  have hout : OutEq S m (m.set64 CTL 1 w) :=
    ⟨fun b _ _ hb => Mem.arr64_set64_ne _ _ _ _ _ hb, hrd 0 (by decide)⟩
  have hfld : ∀ t i f, f < S.w → fld S (m.set64 CTL 1 w) t i f = fld S m t i f := by
    intro t i f _; simp only [fld, hra]
  have hscb' : SCB ≠ (1 : Word) := by decide
  have tier : ∀ (t : Word) (tb : Tbl α (Idx k) δ), t ≤ 1 → TierR S R hs m t tb →
      TierR S R hs (m.set64 CTL 1 w) t tb := by
    intro t tb ht hT
    refine tierR_mono S R hs m _ t tb hra hsa ?_ ?_ (fun i a hr => ((hfr _ _ t i hout (hfld t i)).1 a hr))
      (fun i => (hfr _ _ t i hout (hfld t i)).2) hT
    · simp only [cntW]
      apply hrd
      rcases word_le_one t ht with rfl | rfl
      · simpa using hS.scb.2.2.1
      · simpa using hS.scb.2.2.2
    · simp only [baseW, hrd SCB hscb']
  refine ⟨⟨by rw [hsz']; exact hsz, by rw [hrd SCB hscb']; exact hscb⟩, ?_,
    tier 0 P (by decide) hP, tier 1 Q (by decide) hQ⟩
  have h1' : 1 < (m.arr64 CTL).size := by simpa using h1
  rw [rdW_set64]; simp [h1']

end flag

/-- The four flags of a related state agree (each table's relation has its store's flag equal to
`CTL[1] != 0`). -/
theorem ArenaR.flagsEq {m : Mem} {a : AState} (hR : ArenaR m a) : FlagsEq a.store :=
  ⟨hR.ls.2.1.symm.trans hR.app.2.1, hR.zero.2.1.symm.trans hR.app.2.1,
    hR.nanon.2.1.symm.trans hR.app.2.1⟩

/-- The flag `CTL[1]` is the flag of the expression store. -/
theorem ArenaR.flag_eq {m : Mem} {a : AState} (hR : ArenaR m a) :
    (rdW (m.arr64 CTL) 1 != 0) = a.store.scratchOn := hR.app.2.1

/-- **Writing `CTL[1]`** relates the same tables at the flags `w != 0`. -/
theorem ArenaR.flag {m : Mem} {a : AState} (hR : ArenaR m a) (w : Word) :
    ArenaR (m.set64 CTL 1 w) (onA (w != 0) a) := by
  have hf : MemFrame [] [1] m (m.set64 CTL 1 w) := MemFrame.setCtl m 1 w
  exact ⟨⟨by
      obtain ⟨⟨hc, h0, hp, ht⟩, -⟩ := hR.lit
      refine ⟨by rw [Mem.words_size_set64]; exact hc, by rw [size_set64]; exact h0,
        by rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]; exact hp, ?_⟩
      have : (m.set64 CTL 1 w).top = m.top := by
        simp only [top_rdW, rdW_set64]; simp
      rw [this, Mem.arr64_set64_ne _ _ _ _ _ (by decide)]; exact ht,
      storeR_flag litSch RecRel litH litS_wf litFrame m _ _ _ hR.lit.2 w⟩,
    storeR_flag appSch ARecRel ahash appSch_wf appFrame m _ _ _ hR.app w,
    storeR_flag sortSch SoRecRel sohash sortSch_wf sortFrame m _ _ _ hR.sort w,
    storeR_flag constSch CeRecRel cehash constSch_wf constFrame m _ _ _ hR.const w,
    storeR_flag letSch LeRecRel lehash letSch_wf letFrame m _ _ _ hR.letE w,
    storeR_flag bvarSch BRecRel bhash bvarSch_wf bvarFrame m _ _ _ hR.bvar w,
    storeR_flag fvarSch FVRecRel fvhash fvarSch_wf fvarFrame m _ _ _ hR.fvar w,
    storeR_flag lamSch LaRecRel lahash lamSch_wf laFrame m _ _ _ hR.lam w,
    storeR_flag forallSch FaRecRel fahash forallSch_wf faFrame m _ _ _ hR.forallE w,
    storeR_flag projSch PJRecRel pjhash projSch_wf projFrame m _ _ _ hR.proj w,
    storeR_flag zeroSch ZRecRel zhash zeroSch_wf zeroFrame m _ _ _ hR.zero w,
    storeR_flag succSch SRecRel shash succSch_wf succFrame m _ _ _ hR.succ w,
    storeR_flag maxSch MRecRel mhash maxSch_wf maxFrame m _ _ _ hR.max w,
    storeR_flag imaxSch IRecRel imhash iimaxSch_wf imaxFrame m _ _ _ hR.imax w,
    storeR_flag paramSch PRecRel phash paramSch_wf paramFrame m _ _ _ hR.param w,
    storeR_flag lsSch LsRecRel lshash lsSch_wf lsFrame m _ _ _ hR.ls w,
    storeR_flag nanonSch NaRecRel nahash nanonSch_wf naFrame m _ _ _ hR.nanon w,
    storeR_flag nstrSch NsRecRel nshash nstrSch_wf nstrFrame m _ _ _ hR.nstr w,
    storeR_flag nnumSch NnRecRel nnhash nnumSch_wf nnFrame m _ _ _ hR.nnum w,
    hR.memos.frame (by simp) (by simp [memoCtl]) hf⟩

/-- The derived ranges read the expression tables only. -/
theorem DerR.onA {m : Mem} {a : AState} (hD : DerR m a) (b : Bool) : DerR m (onA b a) :=
  ⟨hD.bvar, hD.fvar, hD.sort, hD.const, hD.lit, hD.app, hD.lam, hD.forallE, hD.letE, hD.proj⟩

theorem DerR.setCtl {m : Mem} {a : AState} (hD : DerR m a) (c w : Word) :
    DerR (m.set64 CTL c w) a :=
  DerR.frameM [] [c] m _ (MemFrame.setCtl m c w) (by simp) a hD

/-- **Writing `CTL[1]`** under `ArenaD`. -/
theorem ArenaD.flag {m : Mem} {a : AState} (hD : ArenaD m a) (w : Word) :
    ArenaD (m.set64 CTL 1 w) (onA (w != 0) a) :=
  ⟨hD.1.flag w, (hD.2.setCtl 1 w).onA _⟩

/-! ## With the flag clear, an interning answers a persistent handle word

An `intern_*` model (`internM`) with `CTL[1] = 0` answers `hdW tag 0 i` for a node `i < 2^27` of
the persistent tier: a handle word below `2^32` with tier bit `0`. -/

theorem hdW0_toNat (g i : Word) (hg : g.toNat < 16) (hi : i.toNat < 2 ^ 27) :
    (hdW g 0 i).toNat = g.toNat * 268435456 + i.toNat := by
  simp only [hdW, UInt64.toNat_add, UInt64.toNat_mul]
  have e1 : (0x10000000 : Word).toNat = 268435456 := rfl
  have e2 : (0 : Word).toNat = 0 := rfl
  rw [e1, e2]
  omega

/-- A persistent handle word: below `2^32`, tier bit `0`. -/
def PW (w : Word) : Prop := w.toNat < 2 ^ 32 ∧ tierW w = 0

theorem hdW0_pw (g i : Word) (hg : g.toNat < 16) (hi : i.toNat < 2 ^ 27) : PW (hdW g 0 i) := by
  have ht := hdW0_toNat g i hg hi
  refine ⟨by omega, ?_⟩
  have h27 := bit27_toNat (hdW g 0 i)
  apply UInt64.toNat_inj.mp
  rw [show tierW (hdW g 0 i) = (hdW g 0 i >>> 27) &&& 1 from rfl, h27, ht]
  show (g.toNat * 268435456 + i.toNat) / 2 ^ 27 % 2 = 0
  omega

/-- A persistent handle word decodes to a persistent handle. -/
theorem PW.pers {k : IdxKind} {w : Word} (h : PW w) : (decI w : Idx k).isPersistent = true := by
  rw [isPersistent_decI w h.1]; simp only [beq_iff_eq]; exact h.2

section t0
variable {α δ : Type} {k : IdxKind} [BEq α] [Hashable α] (S : Schema)
  (R : Mem → Word → Word → α → Prop) (hs : Mem → Word → Word → Word)

/-- A hit's index is below the tier's node count (`WhnfCoreApp.lean`'s `hit_idx_lt`, restated
here to keep this file's imports below the whnf family). -/
theorem hitIdx_lt (m : Mem) (t : Word) (tb : Tbl α (Idx k) δ) (hT : TierR S R hs m t tb)
    (mt : Word → Bool) (x : Word) (rs : List Word) (hP : ProbeOKG S m t mt x rs)
    (hr : rs ≠ []) (hh : rs.headD 0 ≠ 0) : (rs.tail.headD 0).toNat < 2 ^ 27 := by
  obtain ⟨-, hs2, hs3, hj⟩ := (hP hr).1 hh
  obtain ⟨-, hcap, -, -, -, -, ⟨hsl, -⟩⟩ := hT
  have h1 := hsl _ hj
  rw [hs2] at h1
  have h3 : (rs.tail.headD 0 + 1).toNat ≠ 0 := fun h => hs3 (by rw [hs2]; exact UInt64.toNat_inj.mp (by simpa using h))
  rw [UInt64.toNat_add] at h1 h3
  simp only [UInt64.toNat_one] at h1 h3
  have := (rs.tail.headD 0).toNat_lt
  omega

/-- **With the flag clear, an interned handle word is persistent.** -/
theorem internM_pw (hS : S.WF) (m : Mem) (on : Bool) (tbP tbS : Tbl α (Idx k) δ)
    (hR : StoreR S R hs m on tbP tbS) (hfl : rdW (m.arr64 CTL) 1 = 0) (mt : Word → Word → Bool)
    (x0 : Word) (rs₀ rs₁ : List Word) (hP0 : ProbeOKG S m 0 (mt 0) x0 rs₀)
    (pk : Word → Bool) (hpk : ∀ t, pk t = true → PushRoom S m t) (sk : Word) (vs : List Word)
    (w : Word) (m' : Mem) (hI : internM S m sk pk vs rs₀ rs₁ = some (w, m')) : PW w := by
  have hg : S.tag.toUInt64.toNat < 16 := by
    rw [UInt32.toNat_toUInt64]; exact hS.tag
  obtain ⟨-, -, hT0, -⟩ := hR
  simp only [internM, hfl, ne_eq, not_true_eq_false, ↓reduceIte] at hI
  split at hI
  · simp at hI
  rename_i hn0
  split at hI
  · rename_i hh
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hI)
    exact hdW0_pw _ _ hg (hitIdx_lt S R hs m 0 _ hT0 _ _ rs₀ hP0 (fun h => hn0 ⟨hh.1, h⟩) hh.2)
  split at hI
  · rename_i hpk0
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hI)
    exact hdW0_pw _ _ hg (hpk 0 hpk0).1
  · simp at hI

end t0

end L.Arena
