module

public import ConAgua.Arena.FreezeFreshBase
public import ConAgua.Arena.FreezeTrunc

@[expose] public section

/-!
# A fresh worker memory, part 2: phase B starts from it (lane parmode)

docs/design/parmode.md, "Redesign", "Step 4". **`PhaseBStart.fresh`**: what phase A leaves for
phase B at memory `m` and twin state `a` holds at a thread's fresh worker memory `freshMem m`
(frozen arrays cut to their extents, owned arrays zero, `CTL` its seed) and the twin's worker
state `a.worker`, when there is a pending group.

In three steps: the truncation (`PhaseBStart.trunc'`), the cut of `CTL` to its seed
(`PhaseBStart.cut`: no relation reads a `CTL` word from 256 on), and the zeroing of `freshZ`
(`PhaseBStart.zeroed`), at `{ a with memos := Memos.empty }`, which is `a.worker` (the caches
empty and the store its own `dropScratch` when a group is left, `TwinPend.caches`,
`TwinPend.dropped`). After the zeroing:

* every store keeps tier 0 (frozen arrays, `CTL`) and has tier 1 empty: the scratch tables are
  empty (`a.store` is its own `dropScratch`), so the tier-1 counts in `CTL` are already `0`, and
  the zero tier-1 slot tables are valid empty tables (`storeR_fresh`);
* the pool keeps tier 0; `PT0` (zero) is read only while the top is in tier 1 (`PoolTr0`);
* every memo and cache over a zeroed array is the empty map (`memoRV_zeros`), the stamps in
  `CTL` being kept: the walk memos are `Memos.empty`'s, the caches `Caches.empty`'s, the
  existential memos (`CoreMemos`, `CrOK`) at `∅`;
* the env index's tier 1 (zero) holds no row, as phase A's (every indexed name is tier 0);
* the rest reads arrays outside `freshZ` and `CTL` words below 256 (frames).
-/

namespace L.Arena

open ConRon.Arena

/-! ## Step 2: `CTL` cut to its seed -/

section cut
variable {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration}
  {fe : IFEnv} {a : AState} {v : Word}


end cut

/-! ## Step 3: the zeroing -/

/-- The memory before the zeroing. -/
abbrev cutT (m : Mem) : Mem := ctlCut (truncFrozen m)

theorem ctl_mem_freshZ : (CTL : TieredArray) ∈ freshZ := by decide

theorem tier1_ne_ctl (b : ArrId) : tier1 b ≠ CTL := tier1_ne_t0 _ _

section zero
variable (m : Mem)

theorem fresh_keep {b : TieredArray} (hb : b ∉ freshZ) : (freshMem m).arr64 b = (cutT m).arr64 b :=
  (fresh_frame m).arr b hb (fun h => hb (h ▸ ctl_mem_freshZ))

theorem fresh_size (b : TieredArray) : ((freshMem m).arr64 b).size = ((cutT m).arr64 b).size :=
  (fresh_frame m).size b

theorem fresh_getD {b : TieredArray} (hb : b ∈ freshZ) (hc : b ≠ CTL) (i : Nat) :
    ((freshMem m).arr64 b)[i]?.getD 0 = 0 := by
  rw [freshMem_arr, ite_eq_right hc, ite_eq_left hb]
  simp only [zeros, Array.getElem?_replicate]
  split <;> rfl

end zero

variable {m : Mem}

/-! ### The stores -/

section stores
variable {α δ : Type} {k : IdxKind} [BEq α] [Hashable α]

/-- **A cons table whose records read only themselves keeps its relation**, its scratch table
empty. -/
theorem consR_freshL {C : ConsSch} {R : Mem → Word → Word → α → Prop} {on : Bool}
    {P Q : Tbl α (Idx k) δ} (hW : C.WF) (hF : RFrame C.sch R C.hsM)
    (hL : RLocal C.sch R C.hsM [] []) (h1 : (C.ra : TieredArray) ∉ freshZ) (h2 : (C.sa : TieredArray) ∉ freshZ)
    (h3 : tier1 C.sa ∈ freshZ) (h0 : Q.nodes.size = 0) (h : ConsR C R (cutT m) on P Q) :
    ConsR C R (freshMem m) on P Q :=
  consR_iff.mpr (storeR_fresh C.sch R C.hsM C.KP hW.kframe (fresh_ctl m) (fresh_keep m h1)
    (fresh_keep m h2) (fresh_zero m h3 (tier1_ne_ctl C.sa)) (fresh_size m _)
    (rTrans_local hW.sch hF hL) h0 (consR_iff.mp h))

/-- A cons table whose records point into the pool below a tier-0 top keeps its relation. -/
theorem consR_freshP {C : ConsSch} {R : Mem → Word → Word → α → Prop} {on : Bool}
    {P Q : Tbl α (Idx k) δ} (hW : C.WF) (hF : RFrame C.sch R C.hsM)
    (hP : ∀ m₁ m₂ : Mem, (∀ t, m₂.arr64 (tierA C.sch.ra t) = m₁.arr64 (tierA C.sch.ra t)) →
      PoolTr0 m₁ m₂ → (∀ t i a, R m₁ t i a → R m₂ t i a) ∧ ∀ t i, C.hsM m₂ t i = C.hsM m₁ t i)
    (hx : ∀ b ∈ ([POOL, POOL1, CTL] : List TieredArray), b ≠ C.sch.ra ∧ b ≠ tier1 C.sch.ra)
    (htop : (cutT m).top.toNat < 2 ^ 40)
    (h1 : (C.ra : TieredArray) ∉ freshZ) (h2 : (C.sa : TieredArray) ∉ freshZ)
    (h3 : tier1 C.sa ∈ freshZ) (h0 : Q.nodes.size = 0) (h : ConsR C R (cutT m) on P Q) :
    ConsR C R (freshMem m) on P Q :=
  consR_iff.mpr (storeR_fresh C.sch R C.hsM C.KP hW.kframe (fresh_ctl m) (fresh_keep m h1)
    (fresh_keep m h2) (fresh_zero m h3 (tier1_ne_ctl C.sa)) (fresh_size m _)
    (rTrans_pool0 hF hP hx
      (poolTr0_of (fresh_keep m (by decide)) (fresh_ctl m) htop)) h0 (consR_iff.mp h))

end stores

/-- The scratch tables of a store that is its own `dropScratch` are empty. -/
theorem scr_empty {a : AState} (hd : a.store.dropScratch = a.store) :
    a.store.scr = ETables.empty ∧ a.store.lss.scr = LsTables.empty ∧
      a.store.lss.ls.scr = LTables.empty ∧ a.store.lss.ls.ns.scr = NTables.empty := by
  rw [← hd]; exact ⟨rfl, rfl, rfl, rfl⟩

theorem PoolOK.fresh (h : PoolOK (cutT m)) (htop : (cutT m).top.toNat < 2 ^ 40) :
    PoolOK (freshMem m) := by
  have ht : (freshMem m).top = (cutT m).top := by simp only [Mem.top, fresh_ctl]
  have hpc : pcap (freshMem m) = pcap (cutT m) := by simp only [pcap, PSmall, fresh_size]
  refine ⟨by rw [fresh_ctl]; exact h.ctl, by rw [hpc]; exact h.cap, by rw [hpc, ht]; exact h.top,
    .inl (by rw [ht]; exact htop), ?_⟩
  rw [ht, fresh_size]; exact h.inTier

section arena
variable {a : AState} (hd : a.store.dropScratch = a.store)
include hd

theorem ArenaR.fresh (htop : (cutT m).top.toNat < 2 ^ 40) (h : ArenaR (cutT m) a) : ArenaR (freshMem m) { a with memos := Memos.empty } := by
  obtain ⟨e1, e2, e3, e4⟩ := scr_empty hd
  have hz : ∀ b, b ∈ freshZ → b ≠ CTL → ∀ x, rdW ((freshMem m).arr64 b) x = 0 :=
    fun b hb hc => fresh_zero m hb hc
  have hc := fresh_ctl m
  have hk : ∀ b, b ∉ freshZ → (freshMem m).arr64 b = (cutT m).arr64 b := fun b hb => fresh_keep m hb
  have col : ∀ {α δ : Type} {k : IdxKind} [BEq α] [Hashable α] [Inhabited δ] {L : Lens α δ k}
      {c : ArrId} {f : δ → Word}, (c : TieredArray) ∉ freshZ → (L.getS a).nodes.size = 0 →
      ColT2 L c f (cutT m) a → ColT2 L c f (freshMem m) a := fun hc0 h0 h =>
    ⟨colT_mono h.1 (fun i _ => by rw [_root_.L.tierA_zero, hk _ hc0]),
      colT_mono h.2 (fun i hi => absurd hi (by omega))⟩
  exact
  { lit := ⟨PoolOK.fresh h.lit.1 htop, consR_freshP litCS_wf litFrame (fun _ _ hr hp => ⟨RecRel_ptr0 hr hp,
      fun t i => congrArg (fun a => rdW a (i * 4 + 3)) (hr t)⟩) (by decide) htop (by decide)
      (by decide) (by decide) (by rw [e1]; rfl) h.lit.2⟩
    app := consR_freshL appCS_wf appFrame appLocal (by decide) (by decide) (by decide)
      (by rw [e1]; rfl) h.app
    sort := consR_freshL sortCS_wf sortFrame sortLocal (by decide) (by decide) (by decide)
      (by rw [e1]; rfl) h.sort
    const := consR_freshL constCS_wf constFrame constLocal (by decide) (by decide) (by decide)
      (by rw [e1]; rfl) h.const
    letE := consR_freshL letCS_wf letFrame letELocal (by decide) (by decide) (by decide)
      (by rw [e1]; rfl) h.letE
    bvar := consR_freshL bvarCS_wf bvarFrame bvarLocal (by decide) (by decide) (by decide)
      (by rw [e1]; rfl) h.bvar
    fvar := consR_freshL fvarCS_wf fvarFrame fvarLocal (by decide) (by decide) (by decide)
      (by rw [e1]; rfl) h.fvar
    lam := consR_freshL lamCS_wf laFrame lamLocal (by decide) (by decide) (by decide)
      (by rw [e1]; rfl) h.lam
    forallE := consR_freshL forallCS_wf faFrame forallELocal (by decide) (by decide) (by decide)
      (by rw [e1]; rfl) h.forallE
    proj := consR_freshL projCS_wf projFrame projLocal (by decide) (by decide) (by decide)
      (by rw [e1]; rfl) h.proj
    zero := consR_freshL zeroCS_wf zeroFrame zeroLocal (by decide) (by decide) (by decide)
      (by rw [e3]; rfl) h.zero
    succ := consR_freshL succCS_wf succFrame succLocal (by decide) (by decide) (by decide)
      (by rw [e3]; rfl) h.succ
    max := consR_freshL maxCS_wf maxFrame maxLocal (by decide) (by decide) (by decide)
      (by rw [e3]; rfl) h.max
    imax := consR_freshL imaxCS_wf imaxFrame imaxLocal (by decide) (by decide) (by decide)
      (by rw [e3]; rfl) h.imax
    param := consR_freshL paramCS_wf paramFrame paramLocal (by decide) (by decide) (by decide)
      (by rw [e3]; rfl) h.param
    ls := consR_freshP lsCS_wf lsFrame (fun _ _ hr hp => ⟨LsRecRel_ptr0 hr hp,
      fun t i => congrArg (fun a => rdW a (i * 3 + 2)) (hr t)⟩) (by decide) htop (by decide)
      (by decide) (by decide) (by rw [e2]; rfl) h.ls
    nanon := consR_freshL nanonCS_wf naFrame nanonLocal (by decide) (by decide) (by decide)
      (by rw [e4]; rfl) h.nanon
    nstr := consR_freshP nstrCS_wf nstrFrame (fun _ _ hr hp => ⟨NsRecRel_ptr0 hr hp,
      fun t i => congrArg (fun a => rdW a (i * 4 + 3)) (hr t)⟩) (by decide) htop (by decide)
      (by decide) (by decide) (by rw [e4]; rfl) h.nstr
    nnum := consR_freshL nnumCS_wf nnFrame nnumLocal (by decide) (by decide) (by decide)
      (by rw [e4]; rfl) h.nnum
    memos := ⟨memoRG_zeros bmSch bmKey h.memos.bvar hc (hz _ (by decide) (by decide)),
      memoRG_zeros lfSch lfKey h.memos.lift hc (hz _ (by decide) (by decide)),
      memoRG_zeros imSch lfKey h.memos.inst1 hc (hz _ (by decide) (by decide)),
      memoRG_zeros frSch bmKey h.memos.fvar hc (hz _ (by decide) (by decide))⟩
    zeroHp := h.zeroHp
    paramHp := h.paramHp
    succHp := col (by decide) (by show a.store.lss.ls.scr.succs.nodes.size = 0; rw [e3]; rfl) h.succHp
    maxHp := col (by decide) (by show a.store.lss.ls.scr.maxs.nodes.size = 0; rw [e3]; rfl) h.maxHp
    imaxHp := col (by decide) (by show a.store.lss.ls.scr.imaxs.nodes.size = 0; rw [e3]; rfl) h.imaxHp
    lsHp := col (by decide) (by show a.store.lss.scr.lists.nodes.size = 0; rw [e2]; rfl) h.lsHp
    sortLp := col (by decide) (by show a.store.scr.sorts.nodes.size = 0; rw [e1]; rfl) h.sortLp
    constLp := col (by decide) (by show a.store.scr.consts.nodes.size = 0; rw [e1]; rfl) h.constLp
    fvarLp := col (by decide) (by show a.store.scr.fvars.nodes.size = 0; rw [e1]; rfl) h.fvarLp }

omit hd in
theorem DerT2.fresh {α : Type} [BEq α] [Hashable α] {g : ETables → Tbl α EIdx UInt64} {c : ArrId}
    (hc : (c : TieredArray) ∉ freshZ) (h0 : (g a.store.scr).nodes.size = 0) (h : DerT2 a g (cP c (cutT m))) :
    DerT2 a g (cP c (freshMem m)) := by
  obtain ⟨⟨s0, h0'⟩, ⟨s1, -⟩⟩ := h
  refine ⟨⟨s0, fun i x hx => ?_⟩, ⟨s1, fun i x hx => ?_⟩⟩
  · have := h0' i x hx
    simp only [cP, L.tierA_zero] at this ⊢
    rw [fresh_keep m hc]; exact this
  · have := (Array.getElem?_eq_some_iff.mp hx).1; omega

theorem ArenaD.fresh (htop : (cutT m).top.toNat < 2 ^ 40) (h : ArenaD (cutT m) a) :
    ArenaD (freshMem m) { a with memos := Memos.empty } := by
  obtain ⟨hA, hD⟩ := h
  obtain ⟨e1, -, -, -⟩ := scr_empty hd
  refine ⟨ArenaR.fresh hd htop hA, ⟨hD.bvar, hD.fvar, hD.sort, hD.const, hD.lit, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact DerT2.fresh (by decide) (by rw [e1]; rfl) hD.app
  · exact DerT2.fresh (by decide) (by rw [e1]; rfl) hD.lam
  · exact DerT2.fresh (by decide) (by rw [e1]; rfl) hD.forallE
  · exact DerT2.fresh (by decide) (by rw [e1]; rfl) hD.letE
  · exact DerT2.fresh (by decide) (by rw [e1]; rfl) hD.proj

end arena

/-! ### The caches -/

section caches
variable {κ ν : Type} [BEq κ] [Hashable κ]

theorem ModeR.fresh {S : MemoSch} {K : MemoKey (κ × Word)} {VR : Mem → Word → ν → Prop}
    {M : Std.HashMap (κ × Word) ν} {t te : Std.HashMap κ ν}
    (hz : ∀ x, rdW ((freshMem m).arr64 S.arr) x = 0) (h : ModeR S K VR (cutT m) M 0 t te) :
    ModeR S K VR (freshMem m) ∅ 0 ∅ ∅ :=
  ⟨memoRV_zeros S K VR h.memo (fresh_ctl m) hz, bank_empty 0, fun _ => bank_empty 1,
    fun h => absurd rfl h⟩

end caches

theorem CoreR.fresh {c : Caches} (h : CoreR (cutT m) c) : CoreR (freshMem m) Caches.empty := by
  obtain ⟨M, h⟩ := h
  have hz : ∀ b, b ∈ freshZ → b ≠ CTL → ∀ x, rdW ((freshMem m).arr64 b) x = 0 :=
    fun b hb hc => fresh_zero m hb hc
  have hc := fresh_ctl m
  exact ⟨⟨∅, ∅, ∅, ∅, ∅, ∅⟩, h.wc.fresh (hz _ (by decide) (by decide)),
    h.wk.fresh (hz _ (by decide) (by decide)), h.wh.fresh (hz _ (by decide) (by decide)),
    h.inf.fresh (hz _ (by decide) (by decide)), h.io.fresh (hz _ (by decide) (by decide)),
    h.de.fresh (hz _ (by decide) (by decide)), by decide,
    memoRV_zeros _ _ _ h.ct hc (hz _ (by decide) (by decide)),
    memoRV_zeros _ _ _ h.cv hc (hz _ (by decide) (by decide)),
    memoRV_zeros _ _ _ h.rr hc (hz _ (by decide) (by decide)),
    memoRG_zeros _ _ h.lq hc (hz _ (by decide) (by decide)),
    memoRG_zeros _ _ h.lsq hc (hz _ (by decide) (by decide))⟩

/-! ### The environment -/




/-! ### The loop's relation -/

theorem ModeOK.fresh (h : ModeOK (cutT m)) : ModeOK (freshMem m) :=
  h.frame (fresh_frame m) (by simp) (by simp)

theorem IWOK.fresh (h : L.Ind.IWOK (cutT m)) : L.Ind.IWOK (freshMem m) := by
  have h0 := (L.Ind.IWOK_iff _).1 h
  simp only [L.Ind.IWOK_iff, L.Ind.iwTop, erTop, erecTop1, fresh_size, fresh_ctl] at h0 ⊢
  exact h0

section loop
variable {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration}
  {fe : IFEnv} {a : AState} {v : Word}


end loop

theorem CoreMemos.fresh (h : CoreMemos (cutT m)) : CoreMemos (freshMem m) := by
  have hz : ∀ b, b ∈ freshZ → b ≠ CTL → ∀ x, rdW ((freshMem m).arr64 b) x = 0 :=
    fun b hb hc => fresh_zero m hb hc
  have hc := fresh_ctl m
  obtain ⟨⟨_, h1⟩, ⟨_, h2⟩, ⟨⟨_, h3⟩, ⟨_, h4⟩, ⟨_, h5⟩, ⟨_, h6⟩, ⟨_, h7⟩, ⟨_, h8⟩⟩, ⟨_, h9⟩⟩ := h
  exact ⟨⟨_, memoRG_zeros _ _ h1 hc (hz _ (by decide) (by decide))⟩,
    ⟨_, memoRG_zeros _ _ h2 hc (hz _ (by decide) (by decide))⟩,
    ⟨⟨_, memoRG_zeros _ _ h3 hc (hz _ (by decide) (by decide))⟩,
    ⟨_, memoRG_zeros _ _ h4 hc (hz _ (by decide) (by decide))⟩,
    ⟨_, memoRG_zeros _ _ h5 hc (hz _ (by decide) (by decide))⟩,
    ⟨_, memoRV_zeros _ _ _ h6 hc (hz _ (by decide) (by decide))⟩,
    ⟨_, memoRV_zeros _ _ _ h7 hc (hz _ (by decide) (by decide))⟩,
    ⟨_, memoRV_zeros _ _ _ h8 hc (hz _ (by decide) (by decide))⟩⟩,
    ⟨_, memoRV_zeros _ _ _ h9 hc (hz _ (by decide) (by decide))⟩⟩

theorem CrOK.fresh (h : L.Stubs.CrOK (cutT m)) : L.Stubs.CrOK (freshMem m) := by
  obtain ⟨_, h⟩ := h
  exact ⟨_, memoRV_zeros _ _ _ h (fresh_ctl m) (fresh_zero m (by decide) (by decide))⟩

theorem LoopMem.fresh {dn : NIdx → Option ConLeche.Name} {a : AState}
    (h : LoopMem dn (cutT m) a) : LoopMem dn (freshMem m) { a with memos := Memos.empty } :=
  ⟨by rw [fresh_size]; exact h.erec, by rw [fresh_size]; exact h.spn, by rw [fresh_size]; exact h.bstk,
    by simp only [pinW, fresh_keep m (show PINS ∉ freshZ by decide)]; exact h.flag, h.dnP⟩

/-! ### The twin -/


/-- A worker with the caches empty and the store its own `dropScratch` is the state with fresh
walk memos. -/
theorem worker_eq {a : AState} (hd : a.store.dropScratch = a.store) (hc : a.caches = Caches.empty) :
    a.worker = { a with memos := Memos.empty } := by
  simp only [AState.worker, hd, ← hc]

/-! ## The store with the scratch flag off -/

theorem nstore_dropScratch_self {st : NStore} (h : NStoreWF st) (ho : st.scratchOn = false) :
    st.dropScratch = st := by
  obtain ⟨_, h⟩ := h
  have e := h.scrOff ho
  cases st; simp_all [NStore.dropScratch]

theorem lstore_dropScratch_self {st : LStore} (h : LStoreWF st) (ho : st.scratchOn = false) :
    st.dropScratch = st := by
  obtain ⟨_, h⟩ := h
  have e := h.scrOff ho
  have en := nstore_dropScratch_self h.ns (h.sync ▸ ho)
  cases st; simp_all [LStore.dropScratch]

theorem lsstore_dropScratch_self {st : LsStore} (h : LsStoreWF st) (ho : st.scratchOn = false) :
    st.dropScratch = st := by
  have e := h.scrOff ho
  have en := lstore_dropScratch_self h.ls (h.sync ▸ ho)
  cases st; simp_all [LsStore.dropScratch]

/-- **A well-formed store with the scratch flag off is its own `dropScratch`.** -/
theorem estore_dropScratch_self {st : EStore} (h : StoreWF st) (ho : st.scratchOn = false) :
    st.dropScratch = st := by
  obtain ⟨_, h⟩ := h
  have e := h.scrOff ho
  have en := lsstore_dropScratch_self h.lss (h.sync ▸ ho)
  cases st; simp_all [EStore.dropScratch]

/-! ## The jobs' relation at the fresh memory -/

section main
variable {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration}
  {I : IStreamIndex} {a : AState}

/-- **Cutting `CTL` to its seed keeps the jobs' memory half**: no relation reads a `CTL` word from
256 on. -/
theorem JobM.cut {J : Option ISolution} {t : Mem} (h : JobM pins dn ds J I t a) :
    JobM pins dn ds J I (ctlCut t) a := by
  have hf := ctlCut_frame t
  have hC : ∀ x ∈ hiC (t.arr64 CTL).size, 256 ≤ x.toNat := fun _ hx => hiC_ge hx
  have hn : ∀ k : Nat, k < 256 → (UInt64.ofNat k : Word) ∉ hiC (t.arr64 CTL).size := fun k hk hx => by
    have := hC _ hx; rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)] at this; omega
  have hA : ∀ b ∈ ([] : List TieredArray), False := fun _ h => absurd h (by simp)
  have he : erecP (ctlCut t) = erecP t :=
    erecP_congr' (hf.arr EREC (by simp) (by decide)) (hf.arr _ (by simp) (by decide))
      (hf.ctl 129 (hn 129 (by decide))) (hf.ctl 130 (hn 130 (by decide)))
  exact ⟨⟨ArenaR.frame_ext [] _ (by simp) (fun x hx => by have := hC x hx; omega) _ _ hf _ h.arena.base,
      DerR.frameM [] _ _ _ hf (by simp) _ h.arena.der⟩,
    h.core.frame (fun b hb => (hA b hb).elim) (fun x hx => .inr (by have := hC x hx; omega)) hf,
    h.pinsR.frame (fun b hb => (hA b hb).elim) hf, h.mode.frame hf (hn 0 (by decide)) (hn 1 (by decide)),
    h.idx.grow (fun b _ hr => hf.arr b (by simp) (fun e => by subst e; revert hr; decide)) (hf.ctl 128 (hn 128 (by decide)))
      (by rw [he]; exact fun _ _ h => h),
    h.below.frame (fun b hb => (hA b hb).elim) (hn 133 (by decide)) hf,
    by simp only [stampW, hf.ctl 133 (hn 133 (by decide))]; exact h.stamp,
    by rw [hf.arr _ (by simp) (by decide), hf.arr _ (by simp) (by decide)]; exact h.decls,
    IWOK.frame hf (by simp) (by simp) (hn 129 (by decide)) (hn 200 (by decide)) h.iw (by simp)
      (hn 130 (by decide)),
    by rw [hf.ctl 130 (hn 130 (by decide))]; exact h.top1,
    PinSetsR.grow h.pinsets (RecGrow.of_eq (hf.arr EREC (by simp) (by decide)) (hf.ctl 129 (hn 129 (by decide))))
      (hf.ctl 150 (hn 150 (by decide))) (hf.ctl 151 (hn 151 (by decide))),
    ⟨by rw [hf.size]; exact h.mem.erec, by rw [hf.size]; exact h.mem.spn, by rw [hf.size]; exact h.mem.bstk,
      h.mem.memos.frame hf ⟨by simp, by simp⟩ ⟨hn 50 (by decide), hn 48 (by decide)⟩ (by simp)
        ⟨hn 152 (by decide), hn 154 (by decide), hn 156 (by decide)⟩ (by simp)
        ⟨hn 54 (by decide), hn 56 (by decide), hn 58 (by decide)⟩ (by simp) (hn 214 (by decide)), h.mem.dnN⟩,
    by rw [pinW_frame hf (by simp)]; exact h.flag,
    h.memos.frame hf (fun b hb => (hA b hb).elim) (fun x hx => by have := hC x hx; omega), h.fsize,
    h.frozen.frame (fun x hx => not_mem_frozenCtl (.inr (by have := hC x hx; omega))) hf,
    h.jsol.frameX hf (fun b hb => (hA b hb).elim) (fun x hx => by
      have := hC x hx
      refine ⟨fun hs => ?_, fun e => ?_, fun e => ?_⟩
      · simp only [solCtl, SOLC, SNEXTC, SCNTC, List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl | rfl <;> revert this <;> decide
      · subst e; revert this; decide
      · subst e; revert this; decide) (by rw [he]; exact ArrExt.refl _)⟩

theorem freshZ_idx : ∀ b ∈ freshZ, ¬ (b.hi = false ∧ ((129 ≤ b.arr ∧ b.arr ≤ 134) ∨ b.arr = 137)) := by
  decide

theorem OwnBelow.fresh (m : Mem) : OwnBelow (freshMem m) := by
  intro w hw
  have hz : ∀ (b : TieredArray), b ∈ envArrs → 140 ≤ b.arr → ∀ i, rdN ((freshMem m).arr64 b) i = 0 :=
    fun b hb h1 i => fresh_getD m (by revert h1; revert hb; revert b; decide) (fun e => by subst e; revert h1; decide) i
  have hA : ∀ (t : UInt64), 140 ≤ (tierA (oixArr (rowTag w)) t).arr := fun t => by
    unfold tierA oixArr; generalize (t &&& 1 != 0) = b
    cases b <;> split <;> (try split) <;> decide
  have hB : ∀ (t : UInt64), 140 ≤ (tierA (otxArr (rowTag w)) t).arr := fun t => by
    unfold tierA otxArr; generalize (t &&& 1 != 0) = b
    cases b <;> split <;> (try split) <;> decide
  simp only [ownRow, hz _ (tierA_oix_mem _ _) (hA _), hz _ (tierA_otx_mem _ _) (hB _)]
  simp

theorem IndMemos.fresh {m : Mem} (h : IndMemos (cutT m)) : IndMemos (freshMem m) := by
  have hc := fresh_ctl m
  have hz : ∀ b, b ∈ freshZ → b ≠ CTL → ∀ x, rdW ((freshMem m).arr64 b) x = 0 :=
    fun b hb hc => fresh_zero m hb hc
  obtain ⟨⟨⟨⟨a1, h1⟩, ⟨a2, h2⟩, ⟨a3, h3⟩, ⟨a4, h4⟩, ⟨M, G, g, hR, hB, hF⟩⟩, ⟨a5, h5⟩, ⟨a6, h6⟩,
    ⟨a7, h7⟩⟩, ⟨a8, h8⟩, hcr⟩ := h
  refine ⟨⟨⟨⟨_, memoRV_zeros _ _ _ h1 hc (hz _ (by decide) (by decide))⟩,
    ⟨_, memoRV_zeros _ _ _ h2 hc (hz _ (by decide) (by decide))⟩,
    ⟨_, memoRV_zeros _ _ _ h3 hc (hz _ (by decide) (by decide))⟩,
    ⟨_, memoRV_zeros _ _ _ h4 hc (hz _ (by decide) (by decide))⟩,
    ⟨∅, G, g, memoRV_zeros _ _ _ hR hc (hz _ (by decide) (by decide)), ?_, ?_⟩⟩,
    ⟨_, memoRV_zeros _ _ _ h5 hc (hz _ (by decide) (by decide))⟩,
    ⟨_, memoRV_zeros _ _ _ h6 hc (hz _ (by decide) (by decide))⟩,
    ⟨_, memoRV_zeros _ _ _ h7 hc (hz _ (by decide) (by decide))⟩⟩,
    ⟨_, memoRV_zeros _ _ _ h8 hc (hz _ (by decide) (by decide))⟩, CrOK.fresh hcr⟩
  · unfold BankW at *; rw [hc]; exact hB
  · intro x; simp

/-- **The run's solution at the fresh memory**: the solution's rows are frozen (not zeroed), the
flag and the counters are seed words, and the walks' memos are zero (so empty, at the same
stamps). -/
theorem JSol.fresh {J : Option ISolution} (h : JSol J (cutT m)) (he : erecP (freshMem m) = erecP (cutT m)) :
    JSol J (freshMem m) := by
  have hf := fresh_frame m
  have hc := fresh_ctl m
  refine ⟨?_, fun J' e => ?_⟩
  · cases J with
    | none => exact (JSol.none (m := freshMem m) (by rw [hc]; exact h.sol)).sol
    | some J =>
      exact ⟨by simp only [ctlW, hc]; exact h.sol.1, h.sol.2.frameX hf
        (fun b hb => (by decide : ∀ b ∈ freshZ, b ∉ solArrs) b hb) (fun x hx => absurd hx (by simp))
        (by rw [he]; exact ArrExt.refl _)⟩
  · obtain ⟨⟨⟨mp, hn⟩, ⟨mq, hq⟩, h1, h2⟩, hnx⟩ := h.walk J' e
    exact ⟨⟨⟨∅, memoRV_zeros _ _ _ hn hc (fresh_zero m (by decide) (by decide))⟩,
      ⟨∅, memoRV_zeros _ _ _ hq hc (fresh_zero m (by decide) (by decide))⟩,
      by rw [hc]; exact h1, by rw [hc]; exact h2⟩, hnx⟩

/-- **The jobs' relation at a thread's fresh memory**: from the memory half at the truncated memory
(`JobM.trunc`), the store its own `dropScratch` and well formed with the scratch flag off, the jobs'
relation holds at `freshMem m`, at the state with empty walk memos and caches. -/
theorem JobM.fresh {J : Option ISolution} {m : Mem} (h : JobM pins dn ds J I (truncFrozen m) a)
    (hw : StoreWF a.store) (hoff : a.store.scratchOn = false) :
    JobR pins dn ds J I (freshMem m) { a with memos := Memos.empty, caches := Caches.empty } := by
  have hd := estore_dropScratch_self hw hoff
  have hC := h.cut
  have hf := fresh_frame m
  have htop : (cutT m).top.toNat < 2 ^ 40 := top_tier0_of hC.arena.base hC.mode hoff
  have hk : ∀ b, b ∉ freshZ → (freshMem m).arr64 b = (cutT m).arr64 b := fun b hb => fresh_keep m hb
  have he : erecP (freshMem m) = erecP (cutT m) := by
    have h1 : erecTop1 (cutT m) = 0 := by simp only [erecTop1, hC.top1]; rfl
    have h1' : erecTop1 (freshMem m) = 0 := by simp only [erecTop1, fresh_ctl, hC.top1]; rfl
    have h0 : erTop (freshMem m) = erTop (cutT m) := by simp only [erTop, fresh_ctl]
    funext i; simp only [erecP, h1, h1', h0, hk EREC (by decide), Nat.not_lt_zero, ↓reduceIte]
  have hA := (ArenaD.fresh hd htop hC.arena).caches_irrel Caches.empty
  refine ⟨⟨⟨hA.1, hA.2⟩, CoreR.fresh hC.core, hC.pinsR.frame (by decide) hf, ModeOK.fresh hC.mode,
    hC.idx.grow (fun b hb hr => hk b (fun hz => freshZ_idx b hz ⟨hb, hr⟩)) (by rw [fresh_ctl])
      (by rw [he]; exact fun _ _ h => h),
    OwnBelow.fresh m, by simp only [stampW, fresh_ctl]; exact hC.stamp,
    by rw [hk _ (by decide), hk _ (by decide)]; exact hC.decls, IWOK.fresh hC.iw,
    by rw [fresh_ctl]; exact hC.top1,
    PinSetsR.grow hC.pinsets (RecGrow.of_eq (hk EREC (by decide)) (by rw [fresh_ctl]))
      (by rw [fresh_ctl]) (by rw [fresh_ctl]),
    ⟨by rw [fresh_size]; exact hC.mem.erec, by rw [fresh_size]; exact hC.mem.spn,
      by rw [fresh_size]; exact hC.mem.bstk, CoreMemos.fresh hC.mem.memos, hC.mem.dnN⟩,
    by simp only [pinW, hk PINS (by decide)]; exact hC.flag, IndMemos.fresh hC.memos, hC.fsize,
    hC.frozen.congr (fun x _ => by rw [fresh_ctl]), hC.jsol.fresh he⟩,
    ⟨hw⟩, hoff, rfl⟩

end main

end L.Arena
