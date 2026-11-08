module

import ConAgua.Arena.InstLPRef
import ConAgua.Front.IdTable
import ConRon.Arena.WFProofs
public import ConAgua.Arena.InstLPSpec
public import ConAgua.Arena.LevelInternRef

@[expose] public section

/-!
# `rec_fire_levels` refines `recFireLevels`

The model (`InstLPSpec.lean`, over its callees' runs) at the specs of `ls_node`, `keys_push`,
`sle_go`/`slp_go`, `spn_ls`, then the lemmas of `InstLPRef.lean`: the readbacks of the keys and
the universe arguments (`readNamesM_run`, `lp_readLevelsM_run`), the list (`sleW_ok`, `slpW_ok`),
the list node (`spnLsW_ok`), the stack top put back.
-/

open ConRon.Arena ConLeche
open Std.WP
open scoped Lean.Order


namespace L.Arena

theorem LsStore.intern_ls' (st : LsStore) (w : LsNodeView) : (st.intern w).1.ls = st.ls := by
  simp only [LsStore.intern]
  split
  · rfl
  · split
    · split <;> rfl
    · rfl

/-- **The twin's `internLsNode` extends the list store and keeps the level store.** -/
theorem internLsNode_ext (v : LsNodeView) (a a' : AState) (i : LsIdx)
    (h : (internLsNode v).run a = .ok (i, a')) :
    a'.store.lss.ls = a.store.lss.ls ∧ LsExt a.store.lss a'.store.lss := by
  unfold internLsNode at h
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at h
  split at h
  · simp only [StateT.run_pure] at h
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
    exact ⟨rfl, LsExt.refl _⟩
  · split at h <;> split at h <;> first
      | (simp only [StateT.bind, StateT.pure, StateT.run,
          bind, Except.bind, pure, Except.pure] at h
         injection h with h
         obtain ⟨-, rfl⟩ := Prod.mk.inj h
         refine ⟨LsStore.intern_ls' _ v, LsExt.of_view_mono ?_ fun j w hw => LsStore.view_intern_mono _ v hw⟩
         rw [show ∀ st : EStore, (st.internLevels v).1.lss.ls = st.lss.ls from
           fun st => LsStore.intern_ls' _ v]
         exact LExt.refl _)
      | simp [fail, throwThe, MonadExceptOf.throw, StateT.run, bind, StateT.lift,
          Except.bind] at h

/-! ## The cache invariants across a store extension -/

theorem ReadLsCOK.ext {a a' : AState} (hc : ReadLsCOK a) (hx : LsExt a.store.lss a'.store.lss)
    (hca : a'.caches.readLsC = a.caches.readLsC) : ReadLsCOK a' := by
  intro h l e; rw [hca] at e; exact hx.lst _ _ (hc h l e)

theorem ReadLCOK.of_ls {a a' : AState} (hc : ReadLCOK a) (hls : a'.store.lss.ls = a.store.lss.ls)
    (hca : a'.caches.readLC = a.caches.readLC) : ReadLCOK a' := by
  intro h l e; rw [hca] at e; have := hc h l e; simp only [EStore.ls] at this ⊢; rw [hls]; exact this

theorem ReadNCOK.of_ls {a a' : AState} (hc : ReadNCOK a) (hls : a'.store.lss.ls = a.store.lss.ls)
    (hca : a'.caches.readNC = a.caches.readNC) : ReadNCOK a' := by
  intro h l e; rw [hca] at e; have := hc h l e; simp only [EStore.ns] at this ⊢; rw [hls]; exact this

/-! ## `rec_fire_levels` -/

/-- The fire datum at the record words: kind `0` plain (the constructor's level parameters the
`EREC` name slice `(qo, qc)`), else nested (the stored levels the `EREC` slice `(fvo, fvc)`). -/
def FireR (m : Mem) (a : AState) (fk fvo fvc qo qc : Word) (rl : IRecRule) (cvjLps : List NIdx) :
    Prop :=
  (fk = 0 ∧ rl.fire = .plain ∧ hslice? (erecP m) qo.toNat qc.toNat = some cvjLps ∧
      qo.toNat + qc.toNat < 2 ^ 64 ∧ ∀ q ∈ cvjLps, ∃ nm, denoteN a.store.lss.ls.ns q = some nm) ∨
    (fk ≠ 0 ∧ ∃ lvls pins, rl.fire = .nested lvls pins ∧
      hslice? (erecP m) fvo.toNat fvc.toNat = some lvls ∧ fvo.toNat + fvc.toNat < 2 ^ 64 ∧
      ∀ u ∈ lvls, ∃ L, denoteL a.store.ls u = some L)

/-- What `rec_fire_levels` writes. -/
abbrev rflArrs : List TieredArray :=
  (LH : TieredArray) :: (SPN : TieredArray) :: (POOL : TieredArray) :: (POOL1 : TieredArray) :: (LSREC : TieredArray) :: (LSSLOT : TieredArray) :: (LSHP : TieredArray) :: (tier1 LSREC) :: (tier1 LSSLOT) :: (tier1 LSHP) :: lvArrs
abbrev rflCtl : List Word := 136 :: 192 :: 0 :: 40 :: 41 :: lvCtl

/-- **What a run of `rec_fire_levels` gives**: the twin's state and the memory facts a core
caller needs (the stack top put back, the pool only grown, the frame). -/
def RFLOk (m m' : Mem) (a a' : AState) (r : Word) : Prop :=
  ArenaD m' a' ∧ NStoreWF a'.store.lss.ls.ns ∧ ReadNCOK a' ∧ ReadLCOK a' ∧ ReadLsCOK a' ∧
    a'.caches = { { { a.caches with readLC := a'.caches.readLC } with readNC := a'.caches.readNC }
      with readLsC := a'.caches.readLsC } ∧
    a'.pins = a.pins ∧ a'.memos = a.memos ∧ r.toNat < 2 ^ 32 ∧
    spTop m' = spTop m ∧ (∀ i : Word, i < spTop m → spW m' i = spW m i) ∧
    Agree (vpool m') (vpool m) m.top.toNat ∧
    m.top.toNat ≤ m'.top.toNat ∧ pcap m' = pcap m ∧
    MemFrame rflArrs rflCtl m m'

/-- **The tail of `rec_fire_levels`**: the list node interned from the stack slice, the stack top
put back; from the list stage's facts to `RFLOk`. -/
theorem rflTail_ok (p : Prog) (hL : LsProg p) (n : Nat) (m m₁ m₂ m₃ : Mem) (a a₂ : AState)
    (b c l : Word) (hs : List LIdx) (rs : List Word) (hmode : ModeOK m)
    (hsz : (m.arr64 SPN).size < 2 ^ 63) (hctl : 136 < (m.arr64 CTL).size)
    (hbc : b.toNat ≤ c.toNat) (hcl : c.toNat + l.toNat ≤ (m.arr64 SPN).size)
    (hb : b = spTop m)
    (hf₁ : MemFrame [SPN] [136] m m₁)
    (hbel₁ : ∀ i : Word, i.toNat < b.toNat → rdW (m₁.arr64 SPN) i = rdW (m.arr64 SPN) i)
    (hA₂ : ArenaD m₂ a₂) (hnwf₂ : NStoreWF a₂.store.lss.ls.ns) (hnc₂ : ReadNCOK a₂)
    (hlc₂ : ReadLCOK a₂) (hlsc₂ : ReadLsCOK a₂)
    (hca₂ : a₂.caches = { { { a.caches with readLC := a₂.caches.readLC } with readNC := a₂.caches.readNC }
      with readLsC := a₂.caches.readLsC })
    (hpi₂ : a₂.pins = a.pins) (hme₂ : a₂.memos = a.memos)
    (hsl₂ : sliceL (m₂.arr64 SPN) c.toNat l.toNat = lsWords hs)
    (hbl₂ : ∀ i : Word, i.toNat < c.toNat → rdW (m₂.arr64 SPN) i = rdW (m₁.arr64 SPN) i)
    (hf₂ : MemFrame (LH :: SPN :: lvArrs) (192 :: lvCtl) m₁ m₂)
    (h4 : callW p n "spn_ls" [c, l] m₂ = some (rs, m₃)) :
    ∃ a₃, (internLsNode hs).run a₂ = .ok (decI (rs.headD 0), a₃) ∧
      RFLOk m (m₃.set64 CTL 136 b) a a₃ (rs.headD 0) := by
  obtain ⟨s₄, hs₄m, -, hW₄⟩ := triple_of_callW (spnLs_spec p hL n ⟨m₂, Locals.init []⟩ c l
    (by show pcap m₂ < 2 ^ 64; have := hA₂.base.lit.1.cap; omega) hA₂.base.lit.1.top41) h4
  rw [hs₄m] at hW₄
  have hcl64 : c.toNat + l.toNat < 2 ^ 64 := by omega
  have hmode₂ : ModeOK m₂ :=
    (hmode.frame hf₁ (by simp) (by simp)).frame hf₂ (by simp [lvCtl]) (by simp [lvCtl])
  obtain ⟨a₃, hrun, hA₃, hr, hf₃, hpool₃, htop₃, hpsz₃, hca₃, hpi₃, hme₃⟩ :=
    spnLsW_ok n m₂ m₃ a₂ c l (rs.headD 0) hs hA₂ hmode₂ hsl₂ hcl64 hW₄
  obtain ⟨hls₃, hlsx₃⟩ := internLsNode_ext _ _ _ _ hrun
  have hframe : MemFrame rflArrs rflCtl m (m₃.set64 CTL 136 b) :=
    (hf₁.mono (by simp; try grind) (by simp)).trans ((hf₂.mono (by simp; try grind) (by simp)).trans
      ((hf₃.mono (by simp; try grind) (by simp)).trans ((MemFrame.setCtl _ _ _).mono (by simp; try grind) (by simp))))
  have hctl' : (136 : Word).toNat < (m₃.arr64 CTL).size := by
    have := hframe.size CTL
    rw [Mem.size_arr64_set64] at this; rw [this]; simpa using hctl
  have hspn₃ : (m₃.set64 CTL 136 b).arr64 SPN = m₂.arr64 SPN := by
    rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
    exact hf₃.1 SPN (by simp [tier1, SPN, POOL, POOL1, LSREC, LSSLOT, LSHP]) (by decide)
  have hpool₁ : m₁.arr64 POOL = m.arr64 POOL := hf₁.arr POOL (by simp [SPN, POOL]) (by decide)
  have hpool₁' : m₁.arr64 POOL1 = m.arr64 POOL1 := hf₁.arr POOL1 (by simp [SPN, POOL1]) (by decide)
  have hpool₁v := vpool_congr hpool₁ hpool₁'
  have hpool₁c := pcap_congr' hpool₁ hpool₁'
  have hpool₂ : m₂.arr64 POOL = m₁.arr64 POOL := hf₂.arr POOL (by simp [tier1, lvArrs, LH, SPN, POOL, ZREC, ZSLOT,
    SREC, SSLOT, SHP, MREC, MSLOT, MHP, IREC, ISLOT, IHP, PREC, PSLOT]) (by decide)
  have hpool₂' : m₂.arr64 POOL1 = m₁.arr64 POOL1 := hf₂.arr POOL1 (by simp [tier1, lvArrs, LH, SPN, POOL1, ZREC, ZSLOT,
    SREC, SSLOT, SHP, MREC, MSLOT, MHP, IREC, ISLOT, IHP, PREC, PSLOT]) (by decide)
  have hpool₂v := vpool_congr hpool₂ hpool₂'
  have hpool₂c := pcap_congr' hpool₂ hpool₂'
  have htop₁ : m₁.top = m.top := by simp only [top_rdW]; exact hf₁.ctl 0 (by simp)
  have htop₂ : m₂.top = m₁.top := by simp only [top_rdW]; exact hf₂.ctl 0 (by simp [lvCtl])
  have hpool' : (m₃.set64 CTL 136 b).arr64 POOL = m₃.arr64 POOL := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have htop' : (m₃.set64 CTL 136 b).top = m₃.top := by
    simp only [top_rdW]; rw [rdW_set64]; simp
  refine ⟨a₃, hrun, ⟨arenaD_frame_hi hA₃ (MemFrame.setCtl _ _ _) (by simp) (by simp), ?_, ?_, ?_, ?_, ?_,
    by rw [hpi₃, hpi₂], by rw [hme₃, hme₂], hr, ?_, ?_, ?_, ?_, ?_, hframe⟩⟩
  · rw [hls₃]; exact hnwf₂
  · exact hnc₂.of_ls hls₃ (by rw [hca₃])
  · exact hlc₂.of_ls hls₃ (by rw [hca₃])
  · exact hlsc₂.ext hlsx₃ (by rw [hca₃])
  · rw [hca₃]; rw [hca₂]
  · simp only [spTop]; rw [rdW_set64]; simp only [hctl', and_self, ↓reduceIte]
    rw [hb]; rfl
  · intro i hi
    have hi' : i.toNat < b.toNat := by rw [hb]; exact UInt64.lt_iff_toNat_lt.mp hi
    simp only [spW]; rw [hspn₃, hbl₂ i (by omega), hbel₁ i hi']
  · rw [vpool_set64_ne _ _ _ _ ⟨by decide, by decide⟩, ← hpool₁v, ← hpool₂v]
    rw [htop₂, htop₁] at hpool₃; exact hpool₃
  · rw [htop']; rw [htop₂, htop₁] at htop₃; exact htop₃
  · rw [pcap_set64, hpsz₃, hpool₂c, hpool₁c]

/-- **The model of `rec_fire_levels` refines `recFireLevels`**: the keys an `EREC` name slice
that reads back, the universe arguments a list that reads back, the fire datum at the rule's
words (`FireR`), the twin's store invariant and readback caches as hypotheses. -/
@[refines ConRon.Arena.recFireLevels]
theorem recFireLevelsW_ok (p : Prog) (hL : LsProg p) (n : Nat) (m m' : Mem) (a : AState)
    (fk fvo fvc po pc us qo qc r : Word) (rl : IRecRule) (lps cvjLps : List NIdx) (ks : List Name)
    (vs : List Level) (hA : ArenaD m a) (hmode : ModeOK m) (hwf : StoreWF a.store) (hnc : ReadNCOK a) (hlc : ReadLCOK a)
    (hlsc : ReadLsCOK a) (hsz : (m.arr64 SPN).size < 2 ^ 63) (hctl : 136 < (m.arr64 CTL).size)
    (hus : us.toNat < 2 ^ 32) (hdus : denoteLs a.store.lss (decI us) = some vs)
    (hlps : hslice? (erecP m) po.toNat pc.toNat = some lps) (hpb : po.toNat + pc.toNat < 2 ^ 64)
    (hks : lps.mapM (denoteN a.store.lss.ls.ns) = some ks)
    (hfire : FireR m a fk fvo fvc qo qc rl cvjLps)
    (hW : recFireLevelsW p n m fk fvo fvc po pc us qo qc = some (r, m')) :
    ∃ a', (recFireLevels rl lps (decI us) cvjLps).run a = .ok (decI r, a') ∧ RFLOk m m' a a' r := by
  sorry

end L.Arena
