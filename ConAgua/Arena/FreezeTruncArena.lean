import ConAgua.Arena.FreezeTruncStore

/-!
# The truncation theorem, part 4: the store tier (`ArenaR`, `DerR`) (lane parmode)

Each cons table under `truncFrozen` (`StoreTr` from `truncFrozen_ra`/`truncFrozen_sa`), the
pool (`PoolTr`: the pool below its top is kept, and with the scratch flag off the top is in
tier 0), the three tables whose records point into the pool (`lit`, `nstr`, `ls`), the columns
(`ColT2`, `DerR`: tier 0 read below the count) and the walk memos (not frozen).

Beyond the relation, only the scratch flag being off (the top in tier 0) is assumed. A frozen slot
table sits at word 2 (tier 0's offset word is `0`, `TierLay`), and `PoolOK` bounds the saved tier-0
top `PT0[0]` only while the top is in tier 1.
-/

namespace L.Arena

open ConRon.Arena

/-- The cons tables whose tier 0 is frozen. -/
def fzCS : List ConsSch :=
  [litCS, appCS, succCS, zeroCS, maxCS, imaxCS, paramCS, sortCS, constCS, letCS, bvarCS, fvarCS,
    lamCS, forallCS, projCS, nanonCS, nstrCS, nnumCS, lsCS]

theorem fzCS_mem {C : ConsSch} (h : C ∈ fzCS) : (C.ra, C.sa, C.w.toNat, C.ca.toNat) ∈ fzStores :=
  List.mem_map_of_mem (f := fun C : ConsSch => (C.ra, C.sa, C.w.toNat, C.ca.toNat)) h

theorem storeTr_trunc (m : Mem) {C : ConsSch} (hC : C ∈ fzCS) (h1 : C.ra + 256 ∉ fzSrcs)
    (h2 : C.sa + 256 ∉ fzSrcs) : StoreTr C.sch m (truncFrozen m) := by
  have hm := fzCS_mem hC
  refine ⟨truncFrozen_ctl m, truncFrozen_other m _ h1, truncFrozen_other m _ h2, ?_, ?_⟩
  · rw [show C.sch.ra = C.ra from rfl, truncFrozen_ra m hm]
    simp only [cntW, ConsSch.sch, UInt64.ofNat_toNat]
    congr 2
    rw [show C.ca + 0 = C.ca from UInt64.add_zero _]
  · rw [show C.sch.sa = C.sa from rfl, truncFrozen_sa m hm]; rfl

/-- **A cons table whose records read only themselves keeps its relation.** -/
theorem consR_truncL {α δ : Type} {k : IdxKind} [BEq α] [Hashable α] {C : ConsSch}
    {R : Mem → Word → Word → α → Prop} {m : Mem} {on : Bool} {P Q : Tbl α (Idx k) δ}
    (hW : C.WF) (hF : RFrame C.sch R C.hsM) (hL : RLocal C.sch R C.hsM [] [])
    (hC : C ∈ fzCS) (h1 : C.ra + 256 ∉ fzSrcs) (h2 : C.sa + 256 ∉ fzSrcs)
    (h : ConsR C R m on P Q) : ConsR C R (truncFrozen m) on P Q :=
  consR_iff.mpr (storeR_trunc C.sch R C.hsM C.KP hW.sch hW.kframe (storeTr_trunc m hC h1 h2)
    (rTrans_local hW.sch hF hL (truncFrozen_words m)) (consR_iff.mp h))

section tables
variable {m : Mem} {a : AState}

theorem AppR.trunc (h : AppR m a) : AppR (truncFrozen m) a :=
  consR_truncL appCS_wf appFrame appLocal (by simp [fzCS]) (by decide) (by decide) h
theorem SortR.trunc (h : SortR m a) : SortR (truncFrozen m) a :=
  consR_truncL sortCS_wf sortFrame sortLocal (by simp [fzCS]) (by decide) (by decide) h
theorem ConstR.trunc (h : ConstR m a) : ConstR (truncFrozen m) a :=
  consR_truncL constCS_wf constFrame constLocal (by simp [fzCS]) (by decide) (by decide) h
theorem LetR.trunc (h : LetR m a) : LetR (truncFrozen m) a :=
  consR_truncL letCS_wf letFrame letELocal (by simp [fzCS]) (by decide) (by decide) h
theorem BVarR.trunc (h : BVarR m a) : BVarR (truncFrozen m) a :=
  consR_truncL bvarCS_wf bvarFrame bvarLocal (by simp [fzCS]) (by decide) (by decide) h
theorem FVarR.trunc (h : FVarR m a) : FVarR (truncFrozen m) a :=
  consR_truncL fvarCS_wf fvarFrame fvarLocal (by simp [fzCS]) (by decide) (by decide) h
theorem LamR.trunc (h : LamR m a) : LamR (truncFrozen m) a :=
  consR_truncL lamCS_wf laFrame lamLocal (by simp [fzCS]) (by decide) (by decide) h
theorem ForallR.trunc (h : ForallR m a) : ForallR (truncFrozen m) a :=
  consR_truncL forallCS_wf faFrame forallELocal (by simp [fzCS]) (by decide) (by decide) h
theorem ProjR.trunc (h : ProjR m a) : ProjR (truncFrozen m) a :=
  consR_truncL projCS_wf projFrame projLocal (by simp [fzCS]) (by decide) (by decide) h
theorem ZeroR.trunc (h : ZeroR m a) : ZeroR (truncFrozen m) a :=
  consR_truncL zeroCS_wf zeroFrame zeroLocal (by simp [fzCS]) (by decide) (by decide) h
theorem SuccR.trunc (h : SuccR m a) : SuccR (truncFrozen m) a :=
  consR_truncL succCS_wf succFrame succLocal (by simp [fzCS]) (by decide) (by decide) h
theorem MaxR.trunc (h : MaxR m a) : MaxR (truncFrozen m) a :=
  consR_truncL maxCS_wf maxFrame maxLocal (by simp [fzCS]) (by decide) (by decide) h
theorem ImaxR.trunc (h : ImaxR m a) : ImaxR (truncFrozen m) a :=
  consR_truncL imaxCS_wf imaxFrame imaxLocal (by simp [fzCS]) (by decide) (by decide) h
theorem ParamR.trunc (h : ParamR m a) : ParamR (truncFrozen m) a :=
  consR_truncL paramCS_wf paramFrame paramLocal (by simp [fzCS]) (by decide) (by decide) h
theorem NAnonR.trunc (h : NAnonR m a) : NAnonR (truncFrozen m) a :=
  consR_truncL nanonCS_wf naFrame nanonLocal (by simp [fzCS]) (by decide) (by decide) h
theorem NNumR.trunc (h : NNumR m a) : NNumR (truncFrozen m) a :=
  consR_truncL nnumCS_wf nnFrame nnumLocal (by simp [fzCS]) (by decide) (by decide) h

end tables

/-! ## The pool -/

/-- The pool's reads below the top, the top and the saved tier-0 top are kept. -/
structure PoolTr (m m' : Mem) : Prop where
  top : m'.top = m.top
  ptop : m'.ptop0 = m.ptop0
  v : Agree (vpool m') (vpool m) m.top.toNat
  t : Agree (tpool m') (tpool m) m.top.toNat

theorem PoolTr.rslice {m m' : Mem} (h : PoolTr m m') {t o l : Word} (hs : RSlice m t o l) :
    RSlice m' t o l := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hs
  exact ⟨⟨by rw [h.top]; exact h1, by rw [h.top, h.ptop]; exact h2⟩, h3⟩

/-- A memory that agrees with `m` on the pool's arrays, `PT0` and `CTL` has `m`'s pool. -/
theorem PoolTr.left {m m₁ m' : Mem} (h : PoolTr m m') (h0 : m₁.arr64 POOL = m.arr64 POOL)
    (h1 : m₁.arr64 POOL1 = m.arr64 POOL1) (hp : m₁.arr64 PT0 = m.arr64 PT0)
    (hc : m₁.arr64 CTL = m.arr64 CTL) : PoolTr m₁ m' := by
  have ht : m₁.top = m.top := by simp only [Mem.top, hc]
  refine ⟨h.top.trans ht.symm, h.ptop.trans (ptop0_congr hp).symm, ?_, ?_⟩
  · rw [vpool_congr h0 h1, ht]; exact h.v
  · rw [tpool_congr h0 h1, ht]; exact h.t

/-- **The truncation keeps the pool below the top**, when the top is in tier 0. -/
theorem poolTr_trunc (m : Mem) (htop : m.top.toNat < 2 ^ 40) : PoolTr m (truncFrozen m) := by
  have hc := truncFrozen_ctl m
  have hv : Agree (vpool (truncFrozen m)) (vpool m) m.top.toNat := fun j hj => by
    rw [vpool_getNat? _ j (by omega), vpool_getNat? _ j (by omega), prd_nat _ j (by omega),
      prd_nat _ j (by omega), ite_eq_left (by omega), truncFrozen_pool, Nat.mod_eq_of_lt (by omega),
      get?_extract _ hj]
  refine ⟨by simp only [Mem.top, hc], ptop0_congr (truncFrozen_other m PT0 (by decide)), hv,
    fun j hj => ?_⟩
  rw [tpool_vpool _ j (by omega), tpool_vpool _ j (by omega)]; exact hv j hj

theorem top_tier0 {m : Mem} (htop : m.top.toNat < 2 ^ 40) :
    m.top >>> 40 = 0 ∧ (m.top &&& 1099511627775).toNat = m.top.toNat := by
  constructor
  · apply UInt64.toNat_inj.mp; rw [tag_tier_toNat]; simp; omega
  · rw [tag_idx_toNat]; omega

/-- **The pool invariant survives the truncation**, the top in tier 0. -/
theorem PoolOK.trunc {m : Mem} (h : PoolOK m) (htop : m.top.toNat < 2 ^ 40) :
    PoolOK (truncFrozen m) := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h
  have hP := poolTr_trunc m htop
  have hc := truncFrozen_ctl m
  have hp1 : (truncFrozen m).arr64 POOL1 = m.arr64 POOL1 := truncFrozen_other m _ (by decide)
  have hsm : PSmall m := pcap_small m (by omega)
  have ⟨e1, e2⟩ := top_tier0 htop
  rw [e1, tierA_pool0, e2] at a6
  have hsz : ((truncFrozen m).arr64 POOL).size = m.top.toNat := by
    rw [truncFrozen_pool, size_extract0]; omega
  have hsm' : PSmall (truncFrozen m) := ⟨by rw [hsz]; omega, by rw [hp1]; exact hsm.2⟩
  have hpc : pcap (truncFrozen m) = pcap m := by rw [pcap_of_small _ hsm, pcap_of_small _ hsm']
  refine ⟨by rw [truncFrozen_words]; exact a1, by rw [hc]; exact a2, by rw [hpc]; exact a3,
    by rw [hpc, hP.top]; exact a4, by rw [hP.top]; exact .inl htop, ?_⟩
  rw [hP.top, e1, tierA_pool0, e2, hsz]; exact Nat.le_refl _

section pooltab
variable {α : Type} {S : Schema} {R : Mem → Word → Word → α → Prop} {hs : Mem → Word → Word → Word}

/-- **A node relation that reads its record and the pool below the top has the transfer**
to a memory with the pool kept (`PoolTr`). -/
theorem rTrans_pool (hF : RFrame S R hs)
    (hP : ∀ m₁ m₂ : Mem, (∀ t, m₂.arr64 (tierA S.ra t) = m₁.arr64 (tierA S.ra t)) → PoolTr m₁ m₂ →
      (∀ t i a, R m₁ t i a → R m₂ t i a) ∧ ∀ t i, hs m₂ t i = hs m₁ t i)
    (hx : ∀ b ∈ [POOL, POOL1, PT0, CTL], b ≠ S.ra ∧ b ≠ S.ra + 256)
    {m m' : Mem} (hw : m'.words.size = m.words.size) (hp : PoolTr m m') : RTrans S R hs m m' := by
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
  have hb : ∀ b ∈ [POOL, POOL1, PT0, CTL], m₁.arr64 b = m.arr64 b := fun b hb' =>
    eo b (hx b hb').1 (hx b hb').2
  have hctl : m₁.arr64 CTL = m.arr64 CTL := hb CTL (by simp)
  have hout : OutEq S m m₁ := ⟨fun b h1 h1' _ _ _ => eo b h1 h1', by rw [hctl]⟩
  have hf1 : ∀ f, f < S.w → fld S m₁ t i f = fld S m t i f := fun f hf' => by
    simp only [fld, et]; exact hf f hf'
  have h1 := hF m m₁ t i hout hf1
  have h2 := hP m₁ m' (fun t => (et t).symm)
    (hp.left (hb POOL (by simp)) (hb POOL1 (by simp)) (hb PT0 (by simp)) hctl)
  exact ⟨fun a ha => h2.1 t i a (h1.1 a ha), (h2.2 t i).trans h1.2⟩

end pooltab

theorem RecRel_ptr {m m' : Mem} (hr : ∀ t, m'.arr64 (tierA REC t) = m.arr64 (tierA REC t))
    (hp : PoolTr m m') (t i : Word) (k : LitNode) (h : RecRel m t i k) : RecRel m' t i k := by
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

theorem NsRecRel_ptr {m m' : Mem} (hr : ∀ t, m'.arr64 (tierA NSREC t) = m.arr64 (tierA NSREC t))
    (hp : PoolTr m m') (t i : Word) (k : StrNode) (h : NsRecRel m t i k) : NsRecRel m' t i k := by
  simp only [NsRecRel_raw, nsQ, nsO, nsL, hr] at h ⊢
  obtain ⟨h0, hsl, hw, hh⟩ := h
  have hle := hsl.le
  exact ⟨h0, hp.rslice hsl, by rw [Agree.sliceL _ _ _ _ _ hp.v hle, hw],
    by rw [Agree.hashN _ _ _ _ _ hp.t hle, hh]⟩

theorem LsRecRel_ptr {m m' : Mem} (hr : ∀ t, m'.arr64 (tierA LSREC t) = m.arr64 (tierA LSREC t))
    (hp : PoolTr m m') (t i : Word) (k : ListNode) (h : LsRecRel m t i k) : LsRecRel m' t i k := by
  simp only [LsRecRel_raw, lsO, lsL, hr] at h ⊢
  obtain ⟨hsl, hw, hh⟩ := h
  have hle := hsl.le
  exact ⟨hp.rslice hsl, by rw [Agree.sliceL _ _ _ _ _ hp.v hle, hw],
    by rw [Agree.hashN _ _ _ _ _ hp.t hle, hh]⟩

section pooltables
variable {m : Mem} {a : AState} (htop : m.top.toNat < 2 ^ 40)
include htop

theorem LitR.trunc (h : LitR m a) : LitR (truncFrozen m) a :=
  ⟨h.1.trunc htop, consR_iff.mpr (storeR_trunc _ RecRel _ _ litCS_wf.sch litCS_wf.kframe
    (storeTr_trunc m (by simp [fzCS]) (by decide) (by decide))
    (rTrans_pool litFrame (fun _ _ hr hp => ⟨RecRel_ptr hr hp,
      fun t i => congrArg (fun a => rdW a (i * 4 + 3)) (hr t)⟩) (by decide)
      (truncFrozen_words m) (poolTr_trunc m htop)) (consR_iff.mp h.2))⟩

theorem NStrR.trunc (h : NStrR m a) : NStrR (truncFrozen m) a :=
  consR_iff.mpr (storeR_trunc _ NsRecRel _ _ nstrCS_wf.sch nstrCS_wf.kframe
    (storeTr_trunc m (by simp [fzCS]) (by decide) (by decide))
    (rTrans_pool nstrFrame (fun _ _ hr hp => ⟨NsRecRel_ptr hr hp,
      fun t i => congrArg (fun a => rdW a (i * 4 + 3)) (hr t)⟩) (by decide)
      (truncFrozen_words m) (poolTr_trunc m htop)) (consR_iff.mp h))

theorem LsR.trunc (h : LsR m a) : LsR (truncFrozen m) a :=
  consR_iff.mpr (storeR_trunc _ LsRecRel _ _ lsCS_wf.sch lsCS_wf.kframe
    (storeTr_trunc m (by simp [fzCS]) (by decide) (by decide))
    (rTrans_pool lsFrame (fun _ _ hr hp => ⟨LsRecRel_ptr hr hp,
      fun t i => congrArg (fun a => rdW a (i * 3 + 2)) (hr t)⟩) (by decide)
      (truncFrozen_words m) (poolTr_trunc m htop)) (consR_iff.mp h))

end pooltables

/-! ## The columns -/

theorem rdcol_trunc (m : Mem) {c : ArrId} {ca : Nat} (hB : (c, ca) ∈ fzCols) {i : Nat}
    (hi : i < (rdW (m.arr64 CTL) (UInt64.ofNat ca)).toNat) :
    rdW ((truncFrozen m).arr64 c) (UInt64.ofNat i) = rdW (m.arr64 c) (UInt64.ofNat i) := by
  rw [truncFrozen_col m hB]
  apply rdW_extract
  have := (rdW (m.arr64 CTL) (UInt64.ofNat ca)).toNat_lt
  rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]; exact hi

/-- A table's tier-0 count, from its relation. -/
theorem ConsR.cnt0 {α δ : Type} {k : IdxKind} [BEq α] [Hashable α] {C : ConsSch}
    {R : Mem → Word → Word → α → Prop} {m : Mem} {on : Bool} {P Q : Tbl α (Idx k) δ}
    (h : ConsR C R m on P Q) {ca : Nat} (hca : UInt64.ofNat ca = C.ca) :
    (rdW (m.arr64 CTL) (UInt64.ofNat ca)).toNat = P.nodes.size := by
  have := h.cntP
  rw [cntC, UInt64.add_zero] at this
  rw [hca]; exact this

theorem ColT2.trunc {α δ : Type} {k : IdxKind} [BEq α] [Hashable α] [Inhabited δ]
    {L : Lens α δ k} {c : ArrId} {ca : Nat} {f : δ → Word} {m : Mem} {a : AState}
    (hB : (c, ca) ∈ fzCols) (h1 : c + 256 ∉ fzSrcs)
    (hc : (rdW (m.arr64 CTL) (UInt64.ofNat ca)).toNat = (L.getP a).nodes.size)
    (h : ColT2 L c f m a) : ColT2 L c f (truncFrozen m) a :=
  ⟨colT_mono h.1 (fun i hi => by
      simp only [tierA_zero]; exact rdcol_trunc m hB (by rw [hc]; exact hi)),
    colT_mono h.2 (fun _ _ => by simp only [tierA_one', truncFrozen_other m _ h1])⟩

theorem DerT2.trunc {α : Type} [BEq α] [Hashable α] {g : ETables → Tbl α EIdx UInt64}
    {c : ArrId} {ca : Nat} {m : Mem} {a : AState} (hB : (c, ca) ∈ fzCols) (h1 : c + 256 ∉ fzSrcs)
    (hc : (rdW (m.arr64 CTL) (UInt64.ofNat ca)).toNat = (g a.store.pers).nodes.size)
    (h : DerT2 a g (cP c m)) : DerT2 a g (cP c (truncFrozen m)) := by
  obtain ⟨⟨s0, h0⟩, ⟨s1, h1'⟩⟩ := h
  refine ⟨⟨s0, fun i x hx => ?_⟩, ⟨s1, fun i x hx => ?_⟩⟩
  · have hi := (Array.getElem?_eq_some_iff.mp hx).1
    have := h0 i x hx
    simp only [cP, tierA_zero] at this ⊢
    rw [rdcol_trunc m hB (by rw [hc]; exact hi)]; exact this
  · have := h1' i x hx
    simp only [cP, tierA_one'] at this ⊢
    rw [truncFrozen_other m _ h1]; exact this

/-! ## The store tier -/

section arena
variable {m : Mem} {a : AState} (htop : m.top.toNat < 2 ^ 40)
include htop

theorem ArenaR.trunc (h : ArenaR m a) : ArenaR (truncFrozen m) a :=
  { lit := h.lit.trunc htop
    app := h.app.trunc
    sort := h.sort.trunc
    const := h.const.trunc
    letE := h.letE.trunc
    bvar := h.bvar.trunc
    fvar := h.fvar.trunc
    lam := h.lam.trunc
    forallE := h.forallE.trunc
    proj := h.proj.trunc
    zero := h.zero.trunc
    succ := h.succ.trunc
    max := h.max.trunc
    imax := h.imax.trunc
    param := h.param.trunc
    ls := h.ls.trunc htop
    nanon := h.nanon.trunc
    nstr := h.nstr.trunc htop
    nnum := h.nnum.trunc
    memos := (keepNF_trunc m).memosR h.memos
    zeroHp := h.zeroHp
    paramHp := h.paramHp
    succHp := h.succHp.trunc (ca := 6) (by decide) (by decide) (ConsR.cnt0 h.succ (by decide))
    maxHp := h.maxHp.trunc (ca := 10) (by decide) (by decide) (ConsR.cnt0 h.max (by decide))
    imaxHp := h.imaxHp.trunc (ca := 12) (by decide) (by decide) (ConsR.cnt0 h.imax (by decide))
    lsHp := h.lsHp.trunc (ca := 40) (by decide) (by decide) (ConsR.cnt0 h.ls (by decide))
    sortLp := h.sortLp.trunc (ca := 16) (by decide) (by decide) (ConsR.cnt0 h.sort (by decide))
    constLp := h.constLp.trunc (ca := 18) (by decide) (by decide) (ConsR.cnt0 h.const (by decide))
    fvarLp := h.fvarLp.trunc (ca := 26) (by decide) (by decide) (ConsR.cnt0 h.fvar (by decide)) }

theorem ArenaD.trunc (h : ArenaD m a) : ArenaD (truncFrozen m) a := by
  obtain ⟨hA, hD⟩ := h
  refine ⟨hA.trunc htop, ⟨hD.bvar, hD.fvar, hD.sort, hD.const, hD.lit, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact hD.app.trunc (ca := 4) (by decide) (by decide) (ConsR.cnt0 hA.app (by decide))
  · exact hD.lam.trunc (ca := 28) (by decide) (by decide) (ConsR.cnt0 hA.lam (by decide))
  · exact hD.forallE.trunc (ca := 30) (by decide) (by decide) (ConsR.cnt0 hA.forallE (by decide))
  · exact hD.letE.trunc (ca := 20) (by decide) (by decide) (ConsR.cnt0 hA.letE (by decide))
  · exact hD.proj.trunc (ca := 32) (by decide) (by decide) (ConsR.cnt0 hA.proj (by decide))

end arena

end L.Arena
