import ConAgua.Arena.InstLPRef

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
  (fk = 0 ∧ rl.fire = .plain ∧ hslice? (m.arr64 EREC) qo.toNat qc.toNat = some cvjLps ∧
      qo.toNat + qc.toNat < 2 ^ 64 ∧ ∀ q ∈ cvjLps, ∃ nm, denoteN a.store.lss.ls.ns q = some nm) ∨
    (fk ≠ 0 ∧ ∃ lvls pins, rl.fire = .nested lvls pins ∧
      hslice? (m.arr64 EREC) fvo.toNat fvc.toNat = some lvls ∧ fvo.toNat + fvc.toNat < 2 ^ 64 ∧
      ∀ u ∈ lvls, ∃ L, denoteL a.store.ls u = some L)

/-- What `rec_fire_levels` writes. -/
abbrev rflArrs : List ArrId :=
  LH :: SPN :: POOL :: POOL1 :: LSREC :: LSSLOT :: LSHP :: (tier1 LSREC) :: (tier1 LSSLOT) :: (tier1 LSHP) :: lvArrs
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
    (by show pcap m₂ < 2 ^ 64; have := hA₂.1.lit.1.2.2.1; omega) hA₂.1.lit.1.top41) h4
  rw [hs₄m] at hW₄
  have hcl64 : c.toNat + l.toNat < 2 ^ 64 := by omega
  have hmode₂ : ModeOK m₂ :=
    (hmode.frame hf₁ (by simp) (by simp)).frame hf₂ (by simp [lvCtl]) (by simp [lvCtl])
  obtain ⟨a₃, hrun, hA₃, hr, hf₃, hpool₃, htop₃, hpsz₃, hca₃, hpi₃, hme₃⟩ :=
    spnLsW_ok n m₂ m₃ a₂ c l (rs.headD 0) hs hA₂ hmode₂ hsl₂ hcl64 hW₄
  obtain ⟨hls₃, hlsx₃⟩ := internLsNode_ext _ _ _ _ hrun
  have hframe : MemFrame rflArrs rflCtl m (m₃.set64 CTL 136 b) :=
    (hf₁.mono (by simp) (by simp)).trans ((hf₂.mono (by simp) (by simp)).trans
      ((hf₃.mono (by simp) (by simp)).trans ((MemFrame.setCtl _ _ _).mono (by simp) (by simp))))
  have hctl' : (136 : Word).toNat < (m₃.arr64 CTL).size := by
    have := hframe.2.2.1 CTL
    rw [Mem.size_arr64_set64] at this; rw [this]; simpa using hctl
  have hspn₃ : (m₃.set64 CTL 136 b).arr64 SPN = m₂.arr64 SPN := by
    rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
    exact hf₃.1 SPN (by simp [tier1, tierOff, SPN, POOL, POOL1, LSREC, LSSLOT, LSHP]) (by decide)
  have hpool₁ : m₁.arr64 POOL = m.arr64 POOL := hf₁.1 POOL (by simp [SPN, POOL]) (by decide)
  have hpool₁' : m₁.arr64 POOL1 = m.arr64 POOL1 := hf₁.1 POOL1 (by simp [SPN, POOL1]) (by decide)
  have hpool₁v := vpool_congr hpool₁ hpool₁'
  have hpool₁c := pcap_congr' hpool₁ hpool₁'
  have hpool₂ : m₂.arr64 POOL = m₁.arr64 POOL := hf₂.1 POOL (by simp [tier1, tierOff, lvArrs, LH, SPN, POOL, ZREC, ZSLOT,
    SREC, SSLOT, SHP, MREC, MSLOT, MHP, IREC, ISLOT, IHP, PREC, PSLOT]) (by decide)
  have hpool₂' : m₂.arr64 POOL1 = m₁.arr64 POOL1 := hf₂.1 POOL1 (by simp [tier1, tierOff, lvArrs, LH, SPN, POOL1, ZREC, ZSLOT,
    SREC, SSLOT, SHP, MREC, MSLOT, MHP, IREC, ISLOT, IHP, PREC, PSLOT]) (by decide)
  have hpool₂v := vpool_congr hpool₂ hpool₂'
  have hpool₂c := pcap_congr' hpool₂ hpool₂'
  have htop₁ : m₁.top = m.top := by simp only [top_rdW]; exact hf₁.2.1 0 (by simp)
  have htop₂ : m₂.top = m₁.top := by simp only [top_rdW]; exact hf₂.2.1 0 (by simp [lvCtl])
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
    (hlps : hslice? (m.arr64 EREC) po.toNat pc.toNat = some lps) (hpb : po.toNat + pc.toNat < 2 ^ 64)
    (hks : lps.mapM (denoteN a.store.lss.ls.ns) = some ks)
    (hfire : FireR m a fk fvo fvc qo qc rl cvjLps)
    (hW : recFireLevelsW p n m fk fvo fvc po pc us qo qc = some (r, m')) :
    ∃ a', (recFireLevels rl lps (decI us) cvjLps).run a = .ok (decI r, a') ∧ RFLOk m m' a a' r := by
  unfold recFireLevelsW at hW
  rcases h1 : callW p n "ls_node" [us] m with _ | ⟨vs', m₀⟩ <;> rw [h1] at hW
  · cases hW
  obtain ⟨s₁, hs₁m, hs₁, -, hv'⟩ := triple_of_callW (lsNode_spec p hL.ls_node n ⟨m, Locals.init []⟩ us) h1
  have hm₀ : m₀ = m := by rw [← hs₁m, hs₁]
  subst hm₀
  obtain ⟨ids, hvw, hdl'⟩ := denoteLs_view a (decI us) vs hdus
  obtain ⟨e₁, t₁, sl₁⟩ := lsNodeW_store hA.1 hus hvw
  rw [hv', e₁] at hW
  simp only [List.headD_cons, List.tail_cons] at hW
  rcases h2 : callW p n "keys_push" [po, pc] m₀ with _ | ⟨bs, m₁⟩ <;> rw [h2] at hW
  · cases hW
  obtain ⟨s₂, hs₂m, -, hW₂⟩ := triple_of_callW (keysPush_spec p hL.toLvSubProg n ⟨m₀, Locals.init []⟩ po pc) h2
  rw [hs₂m] at hW₂
  have hk := lp_nmsR_of_hslice a.store.lss.ls.ns m₀ EREC lps ks po pc hlps hpb hks
  obtain ⟨hb, hk₁, hf₁, htop₁, hroom, hbel₁⟩ := keysPushW_ok n m₀ m₁ po pc (bs.headD 0) ks hk hsz hctl hW₂
  -- the twin's readbacks
  obtain ⟨c₁, hrn, hnc₁, el₁, els₁, eq₁⟩ := readNamesM_run a hnc lps ks hks
  obtain ⟨c₂, hrl, hlsc₂, el₂, en₂, eq₂⟩ := lp_readLevelsM_run { a with caches := c₁ } (decI us) vs hdus
    (fun h l e => hlsc h l (by rw [← els₁]; exact e))
  generalize hal : ({ { a with caches := c₁ } with caches := c₂ } : AState) = al at hrl hlsc₂
  have hstl : al.store = a.store := by rw [← hal]
  have hA₁ : ArenaD m₁ al := by
    rw [← hal]; exact (arenaD_frame_hi hA hf₁ (by simp [SPN]) (by simp)).with_caches _
  have hlcl : ReadLCOK al := by
    intro h l e; rw [← hal] at e; simp only at e; rw [el₂, el₁] at e
    have := hlc h l e; rw [hstl]; exact this
  have hncl : ReadNCOK al := by
    intro h l e; rw [← hal] at e; simp only at e; rw [en₂] at e
    have := hnc₁ h l e; rw [hstl]; exact this
  have hlscl : ReadLsCOK al := hlsc₂
  have herec₁ : m₁.arr64 EREC = m₀.arr64 EREC := hf₁.1 EREC (by simp [SPN, EREC]) (by decide)
  have hpool₁ : m₁.arr64 POOL = m₀.arr64 POOL := hf₁.1 POOL (by simp [SPN, POOL]) (by decide)
  have hpool₁' : m₁.arr64 POOL1 = m₀.arr64 POOL1 := hf₁.1 POOL1 (by simp [SPN, POOL1]) (by decide)
  have hpool₁v := vpool_congr hpool₁ hpool₁'
  have hpool₁c := pcap_congr' hpool₁ hpool₁'
  have htopm₁ : m₁.top = m₀.top := by simp only [top_rdW]; exact hf₁.2.1 0 (by simp)
  have hsz₁ : (m₁.arr64 SPN).size = (m₀.arr64 SPN).size := hf₁.2.2.1 SPN
  have hlen : (m₁.len64 SPN).toNat = (m₀.arr64 SPN).size := by
    rw [← hsz₁]; exact L.Front.toNat_ofNat_size _ (by rw [hsz₁]; exact hsz)
  have hk₁' : NmsR (nameN al.store.lss.ls.ns) m₁ SPN (bs.headD 0) pc ks := by rw [hstl]; exact hk₁
  unfold rflK at hW
  rcases hfire with ⟨hfk, hpl, hq, hqb, hqd⟩ | ⟨hfk, lvls, pins, hnest, hfv, hfvb, hfvd⟩
  · -- plain
    simp only [hfk, ne_eq, not_true_eq_false, ↓reduceIte] at hW
    by_cases u1 : m₁.len64 SPN < spTop m₁
    · simp [u1] at hW
    by_cases u2 : m₁.len64 SPN - spTop m₁ < qc
    · simp [u1, u2] at hW
    simp only [u1, u2, ↓reduceIte] at hW
    have u2' := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp u2)
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.not_lt.mp u1), hlen] at u2'
    have u1' := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp u1)
    rw [hlen] at u1'
    cases h3 : callW p n "slp_go" [qo, qc, spTop m₁, bs.headD 0, pc, tfld m₀ LVLS (tierW us) (idxW us) 0,
        tfld m₀ LVLS (tierW us) (idxW us) 1] m₁ with
    | none => rw [h3] at hW; cases hW
    | some q =>
    obtain ⟨xs, m₂⟩ := q
    rw [h3] at hW
    dsimp only at hW
    obtain ⟨s₃, hs₃m, -, hW₃⟩ := triple_of_callW (slpGo_spec p hL n ⟨m₁, Locals.init []⟩ _ _ _ _ _ _ _) h3
    rw [hs₃m] at hW₃
    obtain ⟨hs, a₂, hrun₂, hA₂, hwf₂, hnc₂, hx₂, hpi₂, hme₂, hca₂, hsl₂, hbl₂, hf₂⟩ :=
      slpW_ok ks vs ids (bs.headD 0) pc _ _ cvjLps n m₁ m₂ al qo qc (spTop m₁) hA₁ (by rw [hstl]; exact hwf)
        hncl (by rw [herec₁]; exact hq) hqb (by rw [hstl]; exact hqd) hk₁' (by omega)
        (by rw [hpool₁v]; exact sl₁) (by rw [htopm₁]; exact t₁) (by rw [hstl]; exact hdl')
        (by rw [hsz₁]; omega) (by rw [hsz₁]; exact hsz) hW₃
    rcases h4 : callW p n "spn_ls" [spTop m₁, qc] m₂ with _ | ⟨rs, m₃⟩ <;> rw [h4] at hW
    · cases hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hbc : (bs.headD 0).toNat ≤ (spTop m₁).toNat := by omega
    obtain ⟨a₃, hrun₃, hok⟩ := rflTail_ok p hL n m₀ m₁ m₂ m₃ a a₂ (bs.headD 0) (spTop m₁) qc hs rs hmode hsz hctl
      hbc (by omega) hb hf₁ hbel₁ hA₂ (StoreWF.nwf hwf₂) hnc₂ (hlcl.ext hx₂ (by rw [hca₂]))
      (hlscl.ext hx₂.lss (by rw [hca₂])) (by rw [hca₂, ← hal]; dsimp only; rw [eq₂]; dsimp only; rw [eq₁])
      (by rw [hpi₂, ← hal]) (by rw [hme₂, ← hal]) hsl₂ hbl₂ (hf₂.mono (by simp) (by simp)) h4
    refine ⟨a₃, ?_, hok⟩
    simp only [recFireLevels, hpl, StateT.run_bind, hrn, except_ok_bind, hrl, hrun₂, hrun₃]
  · -- nested
    simp only [ne_eq, hfk, not_false_eq_true, ↓reduceIte] at hW
    by_cases u1 : m₁.len64 SPN < spTop m₁
    · simp [u1] at hW
    by_cases u2 : m₁.len64 SPN - spTop m₁ < fvc
    · simp [u1, u2] at hW
    simp only [u1, u2, ↓reduceIte] at hW
    have u2' := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp u2)
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.not_lt.mp u1), hlen] at u2'
    have u1' := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp u1)
    rw [hlen] at u1'
    cases h3 : callW p n "sle_go" [fvo, fvc, spTop m₁, bs.headD 0, pc, tfld m₀ LVLS (tierW us) (idxW us) 0,
        tfld m₀ LVLS (tierW us) (idxW us) 1] m₁ with
    | none => rw [h3] at hW; cases hW
    | some q =>
    obtain ⟨xs, m₂⟩ := q
    rw [h3] at hW
    dsimp only at hW
    obtain ⟨s₃, hs₃m, -, hW₃⟩ := triple_of_callW (sleGo_spec p hL n ⟨m₁, Locals.init []⟩ _ _ _ _ _ _ _) h3
    rw [hs₃m] at hW₃
    obtain ⟨hs, a₂, hrun₂, hA₂, hwf₂, hlc₂, hx₂, hpi₂, hme₂, hca₂, hsl₂, hbl₂, hf₂⟩ :=
      sleW_ok ks vs ids (bs.headD 0) pc _ _ lvls n m₁ m₂ al fvo fvc (spTop m₁) hA₁ (by rw [hstl]; exact hwf)
        hlcl (by rw [herec₁]; exact hfv) hfvb (by rw [hstl]; exact hfvd) hk₁' (by omega)
        (by rw [hpool₁v]; exact sl₁) (by rw [htopm₁]; exact t₁) (by rw [hstl]; exact hdl')
        (by rw [hsz₁]; omega) (by rw [hsz₁]; exact hsz) hW₃
    rcases h4 : callW p n "spn_ls" [spTop m₁, fvc] m₂ with _ | ⟨rs, m₃⟩ <;> rw [h4] at hW
    · cases hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hbc : (bs.headD 0).toNat ≤ (spTop m₁).toNat := by omega
    obtain ⟨a₃, hrun₃, hok⟩ := rflTail_ok p hL n m₀ m₁ m₂ m₃ a a₂ (bs.headD 0) (spTop m₁) fvc hs rs hmode hsz hctl
      hbc (by omega) hb hf₁ hbel₁ hA₂ (StoreWF.nwf hwf₂) (hncl.ext hx₂ (by rw [hca₂])) hlc₂
      (hlscl.ext hx₂.lss (by rw [hca₂])) (by rw [hca₂, ← hal]; dsimp only; rw [eq₂]; dsimp only; rw [eq₁])
      (by rw [hpi₂, ← hal]) (by rw [hme₂, ← hal]) hsl₂ hbl₂ hf₂ h4
    refine ⟨a₃, ?_, hok⟩
    simp only [recFireLevels, hnest, StateT.run_bind, hrn, except_ok_bind, hrl, hrun₂, hrun₃]

/-! ## `caps_never_zero` refines `capsNeverZero` -/

/-- **The model of `caps_never_zero` refines `capsNeverZero`** at the recursor's level parameters
(an `EREC` name slice that reads back), the universe arguments (a list that reads back) and the
family's stored sort datum `caps.sortZ` related at its words. -/
@[refines ConRon.Arena.capsNeverZero]
theorem capsNeverZeroW_run (n : Nat) (m m' : Mem) (a : AState) (po pc us swd so sc x : Word)
    (lps : List NIdx) (ks : List Name) (vs : List Level) (caps : IIndCaps) (hA : ArenaD m a)
    (hwf : NStoreWF a.store.lss.ls.ns) (hnc : ReadNCOK a) (hlsc : ReadLsCOK a)
    (hus : us.toNat < 2 ^ 32) (hsz : (m.arr64 SPN).size < 2 ^ 63)
    (hdl : denoteLs a.store.lss (decI us) = some vs)
    (hlps : hslice? (m.arr64 EREC) po.toNat pc.toNat = some lps) (hpb : po.toNat + pc.toNat < 2 ^ 64)
    (hks : lps.mapM (denoteN a.store.lss.ls.ns) = some ks)
    (hp : PWR (nameN a.store.lss.ls.ns) m EREC swd so sc caps.sortZ)
    (hW : capsNeverZeroW n m po pc us swd so sc = some (x, m')) :
    ∃ a', (capsNeverZero lps (decI us) caps).run a = .ok (x != 0, a') ∧ ArenaD m' a' ∧
      a'.store = a.store ∧ a'.pins = a.pins ∧ a'.memos = a.memos ∧
      a'.caches = { { a.caches with readNC := a'.caches.readNC } with readLsC := a'.caches.readLsC } ∧
      ReadNCOK a' ∧ ReadLsCOK a' ∧
      MemFrame [LH, SPN] [192, 136] m m' ∧ spTop m' = spTop m ∧
      (∀ i : Word, i < spTop m → spW m' i = spW m i) ∧ x.toNat < 2 ^ 32 := by
  have hk := lp_nmsR_of_hslice a.store.lss.ls.ns m EREC lps ks po pc hlps hpb hks
  obtain ⟨hA', hf, htop, hbel, hx, hlt⟩ :=
    capsNeverZeroW_ok n m m' a po pc us swd so sc x ks vs caps.sortZ hA hwf hus hsz hdl hk hp hW
  obtain ⟨c₁, hrn, hnc₁, -, els₁, eq₁⟩ := readNamesM_run a hnc lps ks hks
  have hlsc₁ : ReadLsCOK { a with caches := c₁ } := fun h l e => hlsc h l (by rw [← els₁]; exact e)
  obtain ⟨c₂, hrl, hlsc₂, -, en₂, eq₂⟩ := lp_readLevelsM_run { a with caches := c₁ } (decI us) vs hdl hlsc₁
  generalize ha₂ : ({ { a with caches := c₁ } with caches := c₂ } : AState) = a₂ at hrl hlsc₂
  have hst : a₂.store = a.store := by rw [← ha₂]
  have hpi : a₂.pins = a.pins := by rw [← ha₂]
  have hme : a₂.memos = a.memos := by rw [← ha₂]
  have hca : a₂.caches = c₂ := by rw [← ha₂]
  have hA₂ : ArenaD m' a₂ := by rw [← ha₂]; exact hA'.with_caches _
  refine ⟨a₂, ?_, hA₂, hst, hpi, hme, ?_, ?_, hlsc₂, hf, htop, hbel, hlt⟩
  · have hb : (Level.substPW ks vs caps.sortZ).isNever = (x != 0) := by
      cases h : (Level.substPW ks vs caps.sortZ).isNever
      · rw [h] at hx
        have h0 : x = 0 := Classical.byContradiction fun h0 => by have := Eq.mp hx h0; cases this
        subst h0; rfl
      · rw [h] at hx
        have h0 : x ≠ 0 := Eq.mpr hx rfl
        exact (bne_iff_ne.mpr h0).symm
    simp only [ConRon.Arena.capsNeverZero, StateT.run_bind, hrn, except_ok_bind, hrl, hb]; rfl
  · rw [hca]; conv => lhs; rw [eq₂]
    rw [en₂]; dsimp only; conv => lhs; rw [eq₁]
  · intro h l e; rw [hca, en₂] at e; rw [hst]; exact hnc₁ h l e

end L.Arena
