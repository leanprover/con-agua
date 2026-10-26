import ConAgua.Arena.FreezeFreshBase

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
  {fe : IFEnv} {pend : Array PendingCheck} {a : AState} {v : Word}

/-- **No relation reads a `CTL` word from 256 on**: cutting `CTL` to its seed keeps
`PhaseBStart`. -/
theorem PhaseBStart.cut {t : Mem} (h : PhaseBStart pins dn ds fe pend t a v) :
    PhaseBStart pins dn ds fe pend (ctlCut t) a v := by
  have hf := ctlCut_frame t
  have hC : ∀ x ∈ hiC (t.arr64 CTL).size, 256 ≤ x.toNat := fun _ hx => hiC_ge hx
  have hn : ∀ k : Nat, k < 256 → (UInt64.ofNat k : Word) ∉ hiC (t.arr64 CTL).size := fun k hk hx => by
    have := hC _ hx; rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)] at this; omega
  have he : erecP (ctlCut t) = erecP t :=
    erecP_congr (hf.1 EREC (by simp) (by decide)) (hf.2.1 129 (hn 129 (by decide)))
  obtain ⟨hL, hM, hCM, hT, hcr⟩ := h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, hT, ?_⟩
  · exact CheckR.frame_hi (A := []) (by simp) (fun x hx => by have := hC x hx; omega) hf hL.check
  · exact hL.pend.ext (hf.1 PEND (by simp) (by decide)) (hf.2.1 130 (hn 130 (by decide)))
      (by rw [he]; exact fun _ _ h => h)
  · rw [hf.1 _ (by simp) (by decide), hf.1 _ (by simp) (by decide)]; exact hL.decls
  · exact IWOK.frame hf (by simp) (by simp) (hn 129 (by decide)) (hn 200 (by decide)) hL.iw
  · obtain ⟨pm, hm⟩ := hL.pmemo
    exact ⟨pm, hm.frame (by simp) (fun x hx => .inr (by have := hC x hx; omega)) hf⟩
  · exact PinSetsR.grow hL.pinsets
      ⟨by simp only [L.Ind.erTop, hf.2.1 129 (hn 129 (by decide))]; exact Nat.le_refl _,
        fun i _ => by rw [hf.1 EREC (by simp) (by decide)]⟩
      (hf.2.1 150 (hn 150 (by decide))) (hf.2.1 151 (hn 151 (by decide)))
  · refine ⟨by rw [hf.2.2.1]; exact hM.erec, by rw [hf.2.2.1]; exact hM.spn,
      by rw [hf.2.2.1]; exact hM.bstk, ?_, hM.dnP⟩
    simp only [pinW, hf.1 PINS (by simp) (by decide)]; exact hM.flag
  · exact CoreMemos.frame_hi hf (by simp) (fun x hx => by have := hC x hx; omega) hCM
      (by simp) (fun x hx => .inr (by have := hC x hx; omega))
  · obtain ⟨memo, hm⟩ := hcr
    exact ⟨memo, memoRV_frame L.Stubs.crSch L.Stubs.crSch_wf bmKey L.Stubs.CrV [] _ (by simp)
      (hn 158 (by decide)) _ _ hf
      (fun _ _ h => h) memo hm⟩

end cut

/-! ## Step 3: the zeroing -/

/-- The memory before the zeroing. -/
abbrev cutT (m : Mem) : Mem := ctlCut (truncFrozen m)

theorem ctl_mem_freshZ : CTL ∈ freshZ := by decide

theorem tier1_ne_ctl (b : ArrId) : b + 256 ≠ CTL :=
  Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) (Nat.le_add_left 256 b))

section zero
variable (m : Mem)

theorem fresh_keep {b : ArrId} (hb : b ∉ freshZ) : (freshMem m).arr64 b = (cutT m).arr64 b :=
  (fresh_frame m).1 b hb (fun h => hb (h ▸ ctl_mem_freshZ))

theorem fresh_words : (freshMem m).words.size = (cutT m).words.size := (fresh_frame m).2.2.2

theorem fresh_size (b : ArrId) : ((freshMem m).arr64 b).size = ((cutT m).arr64 b).size :=
  (fresh_frame m).2.2.1 b

theorem fresh_getD {b : ArrId} (hb : b ∈ freshZ) (hc : b ≠ CTL) (i : Nat) :
    ((freshMem m).arr64 b)[i]?.getD 0 = 0 := by
  rw [freshMem_arr, if_neg hc, if_pos hb]
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
    (hL : RLocal C.sch R C.hsM [] []) (h1 : C.ra ∉ freshZ) (h2 : C.sa ∉ freshZ)
    (h3 : C.sa + 256 ∈ freshZ) (h0 : Q.nodes.size = 0) (h : ConsR C R (cutT m) on P Q) :
    ConsR C R (freshMem m) on P Q :=
  consR_iff.mpr (storeR_fresh C.sch R C.hsM C.KP hW.kframe (fresh_ctl m) (fresh_keep m h1)
    (fresh_keep m h2) (fresh_zero m h3 (tier1_ne_ctl C.sa)) (fresh_size m _)
    (rTrans_local hW.sch hF hL (fresh_words m)) h0 (consR_iff.mp h))

/-- A cons table whose records point into the pool below a tier-0 top keeps its relation. -/
theorem consR_freshP {C : ConsSch} {R : Mem → Word → Word → α → Prop} {on : Bool}
    {P Q : Tbl α (Idx k) δ} (hW : C.WF) (hF : RFrame C.sch R C.hsM)
    (hP : ∀ m₁ m₂ : Mem, (∀ t, m₂.arr64 (tierA C.sch.ra t) = m₁.arr64 (tierA C.sch.ra t)) →
      PoolTr0 m₁ m₂ → (∀ t i a, R m₁ t i a → R m₂ t i a) ∧ ∀ t i, C.hsM m₂ t i = C.hsM m₁ t i)
    (hx : ∀ b ∈ [POOL, POOL1, CTL], b ≠ C.sch.ra ∧ b ≠ C.sch.ra + 256)
    (htop : (cutT m).top.toNat < 2 ^ 40)
    (h1 : C.ra ∉ freshZ) (h2 : C.sa ∉ freshZ)
    (h3 : C.sa + 256 ∈ freshZ) (h0 : Q.nodes.size = 0) (h : ConsR C R (cutT m) on P Q) :
    ConsR C R (freshMem m) on P Q :=
  consR_iff.mpr (storeR_fresh C.sch R C.hsM C.KP hW.kframe (fresh_ctl m) (fresh_keep m h1)
    (fresh_keep m h2) (fresh_zero m h3 (tier1_ne_ctl C.sa)) (fresh_size m _)
    (rTrans_pool0 hF hP hx (fresh_words m)
      (poolTr0_of (fresh_keep m (by decide)) (fresh_ctl m) htop)) h0 (consR_iff.mp h))

end stores

/-- The scratch tables of a store that is its own `dropScratch` are empty. -/
theorem scr_empty {a : AState} (hd : a.store.dropScratch = a.store) :
    a.store.scr = ETables.empty ∧ a.store.lss.scr = LsTables.empty ∧
      a.store.lss.ls.scr = LTables.empty ∧ a.store.lss.ls.ns.scr = NTables.empty := by
  rw [← hd]; exact ⟨rfl, rfl, rfl, rfl⟩

theorem PoolOK.fresh (h : PoolOK (cutT m)) (htop : (cutT m).top.toNat < 2 ^ 40) :
    PoolOK (freshMem m) := by
  obtain ⟨a1, a2, a3, a4, -, a6⟩ := h
  have ht : (freshMem m).top = (cutT m).top := by simp only [Mem.top, fresh_ctl]
  have hpc : pcap (freshMem m) = pcap (cutT m) := by simp only [pcap, PSmall, fresh_size]
  refine ⟨by rw [fresh_words]; exact a1, by rw [fresh_ctl]; exact a2, by rw [hpc]; exact a3,
    by rw [hpc, ht]; exact a4, .inl (by rw [ht]; exact htop), ?_⟩
  rw [ht, fresh_size]; exact a6

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
      {c : ArrId} {f : δ → Word}, c ∉ freshZ → (L.getS a).nodes.size = 0 →
      ColT2 L c f (cutT m) a → ColT2 L c f (freshMem m) a := fun hc0 h0 h =>
    ⟨colT_mono h.1 (fun i _ => by rw [tierA_zero', hk _ hc0]),
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
    (hc : c ∉ freshZ) (h0 : (g a.store.scr).nodes.size = 0) (h : DerT2 a g (cP c (cutT m))) :
    DerT2 a g (cP c (freshMem m)) := by
  obtain ⟨⟨s0, h0'⟩, ⟨s1, -⟩⟩ := h
  refine ⟨⟨s0, fun i x hx => ?_⟩, ⟨s1, fun i x hx => ?_⟩⟩
  · have := h0' i x hx
    simp only [cP, tierA_zero'] at this ⊢
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

theorem row_fresh (w : Word) (hg : rowTag w ≤ 2) :
    (rowTier w = 0 → rowC (freshMem m) w = rowC (cutT m) w ∧ rowP (freshMem m) w = rowP (cutT m) w) ∧
    (rowTier w ≠ 0 → rowC (freshMem m) w = 0) := by
  have ht : rowTier w = 0 ∨ rowTier w = 1 := by simp only [rowTier]; omega
  have hg3 : rowTag w = 0 ∨ rowTag w = 1 ∨ rowTag w = 2 := by omega
  unfold rowC rowP
  simp only [hg, ↓reduceIte]
  rcases ht with ht | ht
  · have ha : rowArr w = 132 + rowTag w := by
      unfold rowArr; rw [ht]; show (132 + rowTag w + 8 * 0 : Nat) = 132 + rowTag w; omega
    have hn : rowArr w ∉ freshZ := by
      rw [ha]; rcases hg3 with e | e | e <;> rw [e] <;> decide
    rw [fresh_keep m hn]
    exact ⟨fun _ => ⟨rfl, rfl⟩, fun h => absurd ht h⟩
  · have ha : rowArr w = 140 + rowTag w := by
      unfold rowArr; rw [ht]; show (132 + rowTag w + 8 * 1 : Nat) = 140 + rowTag w; omega
    have hn : rowArr w ∈ freshZ := by
      rw [ha]; rcases hg3 with e | e | e <;> rw [e] <;> decide
    refine ⟨fun h => by omega, fun _ => fresh_getD m hn (by rw [ha]; show 140 + rowTag w ≠ (1 : Nat); omega) _⟩

theorem tblRow_fresh (w : Word) :
    (rowTier w = 0 → tblRow (freshMem m) w = tblRow (cutT m) w) ∧
    (rowTier w ≠ 0 → tblRow (freshMem m) w = 0) := by
  have ht : rowTier w = 0 ∨ rowTier w = 1 := by simp only [rowTier]; omega
  unfold tblRow
  by_cases hg : rowTag w ≤ 2
  · have hg3 : rowTag w = 0 ∨ rowTag w = 1 ∨ rowTag w = 2 := by omega
    simp only [hg, ↓reduceIte]
    rcases ht with ht | ht
    · have ha : tblArr w = 129 + rowTag w := by
        unfold tblArr; rw [ht]; show (129 + rowTag w + 256 * 0 : Nat) = 129 + rowTag w; omega
      have hn : tblArr w ∉ freshZ := by
        rw [ha]; rcases hg3 with e | e | e <;> rw [e] <;> decide
      rw [fresh_keep m hn]
      exact ⟨fun _ => rfl, fun h => absurd ht h⟩
    · have ha : tblArr w = 385 + rowTag w := by
        unfold tblArr; rw [ht]; show (129 + rowTag w + 256 * 1 : Nat) = 385 + rowTag w; omega
      have hn : tblArr w ∈ freshZ := by
        rw [ha]; rcases hg3 with e | e | e <;> rw [e] <;> decide
      exact ⟨fun h => by omega, fun _ => fresh_getD m hn (by rw [ha]; show 385 + rowTag w ≠ (1 : Nat); omega) _⟩
  · simp [hg]

theorem EnvR.fresh {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    (hk : EnvKeysIn (cutT m) fe) (h : EnvR dn (cutT m) vis fe) : EnvR dn (freshMem m) vis fe := by
  have he : erecP (freshMem m) = erecP (cutT m) :=
    erecP_congr (fresh_keep m (by decide)) (by rw [fresh_ctl])
  have hET : (freshMem m).arr64 ETAB = (cutT m).arr64 ETAB := fresh_keep m (by decide)
  refine ⟨h.vis, fun n hn => ?_, fun n hn h0 => ?_, ?_, fun n hn => ?_, fun n hn h0 => ?_, ?_⟩
  · by_cases ht : rowTier n.word.toUInt64 = 0
    · have := (row_fresh (m := m) n.word.toUInt64 hn).1 ht
      rw [h.keys n hn]; simp only [rowW, this.1, this.2]
    · have h0 := (row_fresh (m := m) n.word.toUInt64 hn).2 ht
      have hnone : fe.idx[n]? = none := by
        cases e : fe.idx[n]? with
        | none => rfl
        | some _ => exact absurd (hk.idx n (by simp [e]) hn).1 ht
      simp only [rowW, h0, ↓reduceIte, hnone, Option.map_none]
  · have ht : rowTier n.word.toUInt64 = 0 :=
      Classical.byContradiction fun ht => h0 ((row_fresh (m := m) n.word.toUInt64 hn).2 ht)
    have := (row_fresh (m := m) n.word.toUInt64 hn).1 ht
    rw [this.2, he]
    exact h.vals n hn (by rw [← this.1]; exact h0)
  · rw [← h.consts]
    simp only [envConsts, envLen, fresh_ctl, he, fresh_keep m (show ECON ∉ freshZ by decide)]
  · by_cases ht : rowTier n.word.toUInt64 = 0
    · rw [(tblRow_fresh (m := m) n.word.toUInt64).1 ht]; exact h.tkeys n hn
    · have hnone : fe.tbls[n]? = none := by
        cases e : fe.tbls[n]? with
        | none => rfl
        | some _ => exact absurd (hk.tbls n (by simp [e]) hn).1 ht
      rw [(tblRow_fresh (m := m) n.word.toUInt64).2 ht, hnone]; rfl
  · have ht : rowTier n.word.toUInt64 = 0 :=
      Classical.byContradiction fun ht => h0 ((tblRow_fresh (m := m) n.word.toUInt64).2 ht)
    rw [(tblRow_fresh (m := m) n.word.toUInt64).1 ht] at h0 ⊢
    rw [he]
    exact h.tvals n hn h0
  · rw [← h.tables]
    simp only [envTables, tblCnt, fresh_ctl, he, hET]

/-! ### The loop's relation -/

theorem ModeOK.fresh (h : ModeOK (cutT m)) : ModeOK (freshMem m) :=
  h.frame (fresh_frame m) (by simp) (by simp)

theorem IWOK.fresh (h : L.Ind.IWOK (cutT m)) : L.Ind.IWOK (freshMem m) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  simp only [L.Ind.IWOK, L.Ind.iwTop, L.Ind.erTop, fresh_ctl, fresh_size] at *
  exact ⟨h1, h2, h3, h4, h5⟩

section loop
variable {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration}
  {fe : IFEnv} {pend : Array PendingCheck} {a : AState} {v : Word}

theorem LoopR.fresh (hd : a.store.dropScratch = a.store) (hc : a.caches = Caches.empty)
    (htop : (cutT m).top.toNat < 2 ^ 40) (hk : EnvKeysIn (cutT m) fe)
    (h : LoopR pins dn (cutT m) a v fe pend ds) :
    LoopR pins dn (freshMem m) { a with memos := Memos.empty } v fe pend ds := by
  have hf := fresh_frame m
  have he : erecP (freshMem m) = erecP (cutT m) :=
    erecP_congr (fresh_keep m (by decide)) (by rw [fresh_ctl])
  refine ⟨⟨ArenaD.fresh hd htop h.check.arena, ?_, h.check.pins.frame (by decide) hf,
      h.check.env.fresh hk, ModeOK.fresh h.check.mode⟩, ?_, ?_, IWOK.fresh h.iw, ?_, ?_⟩
  · show CoreR (freshMem m) a.caches
    rw [hc]; exact CoreR.fresh h.check.core
  · exact h.pend.ext (fresh_keep m (by decide)) (by rw [fresh_ctl])
      (by rw [he]; exact fun _ _ h => h)
  · rw [fresh_keep m (by decide), fresh_keep m (by decide)]; exact h.decls
  · obtain ⟨pm, hm⟩ := h.pmemo
    exact ⟨pm, hm.frame (by decide) (by simp) hf⟩
  · exact PinSetsR.grow h.pinsets
      ⟨by simp only [L.Ind.erTop, fresh_ctl]; exact Nat.le_refl _,
        fun i _ => by rw [fresh_keep m (by decide)]⟩
      (by rw [fresh_ctl]) (by rw [fresh_ctl])

end loop

theorem CoreMemos.fresh (h : CoreMemos (cutT m)) : CoreMemos (freshMem m) := by
  have hz : ∀ b, b ∈ freshZ → b ≠ CTL → ∀ x, rdW ((freshMem m).arr64 b) x = 0 :=
    fun b hb hc => fresh_zero m hb hc
  have hc := fresh_ctl m
  obtain ⟨⟨_, h1⟩, ⟨_, h2⟩, ⟨_, h3⟩, ⟨_, h4⟩, ⟨_, h5⟩, ⟨_, h6⟩, ⟨_, h7⟩, ⟨_, h8⟩⟩ := h
  exact ⟨⟨_, memoRG_zeros _ _ h1 hc (hz _ (by decide) (by decide))⟩,
    ⟨_, memoRG_zeros _ _ h2 hc (hz _ (by decide) (by decide))⟩,
    ⟨_, memoRG_zeros _ _ h3 hc (hz _ (by decide) (by decide))⟩,
    ⟨_, memoRG_zeros _ _ h4 hc (hz _ (by decide) (by decide))⟩,
    ⟨_, memoRG_zeros _ _ h5 hc (hz _ (by decide) (by decide))⟩,
    ⟨_, memoRV_zeros _ _ _ h6 hc (hz _ (by decide) (by decide))⟩,
    ⟨_, memoRV_zeros _ _ _ h7 hc (hz _ (by decide) (by decide))⟩,
    ⟨_, memoRV_zeros _ _ _ h8 hc (hz _ (by decide) (by decide))⟩⟩

theorem CrOK.fresh (h : L.Stubs.CrOK (cutT m)) : L.Stubs.CrOK (freshMem m) := by
  obtain ⟨_, h⟩ := h
  exact ⟨_, memoRV_zeros _ _ _ h (fresh_ctl m) (fresh_zero m (by decide) (by decide))⟩

theorem LoopMem.fresh {dn : NIdx → Option ConLeche.Name} {a : AState}
    (h : LoopMem dn (cutT m) a) : LoopMem dn (freshMem m) { a with memos := Memos.empty } :=
  ⟨by rw [fresh_size]; exact h.erec, by rw [fresh_size]; exact h.spn, by rw [fresh_size]; exact h.bstk,
    by simp only [pinW, fresh_keep m (show PINS ∉ freshZ by decide)]; exact h.flag, h.dnP⟩

/-! ### The twin -/

/-- **The twin's phase-B invariant does not read the walk memos.** -/
theorem TwinPend.memos {fe : IFEnv} {pend : List PendingCheck} {a : AState} (h : TwinPend fe pend a)
    (ms : Memos) : TwinPend fe pend { a with memos := ms } := by
  obtain ⟨env, pendP, hok, hnd, hrel⟩ := h.fold
  exact ⟨⟨env, pendP,
    { check := { state := { wf := hok.check.state.wf }, caches := { hok.check.caches with },
                 pins := { hok.check.pins with }, ienv := { hok.check.ienv with } }
      envWF := hok.envWF, tblShape := hok.tblShape, persPins := { hok.persPins with }, persEnv := hok.persEnv,
      coh := hok.coh, denote := hok.denote }, hnd, hrel⟩, h.caches, h.off, h.dropped⟩

/-- A worker with the caches empty and the store its own `dropScratch` is the state with fresh
walk memos. -/
theorem worker_eq {a : AState} (hd : a.store.dropScratch = a.store) (hc : a.caches = Caches.empty) :
    a.worker = { a with memos := Memos.empty } := by
  simp only [AState.worker, hd, ← hc]

/-! ## The theorem -/

section main
variable {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration}
  {fe : IFEnv} {pend : Array PendingCheck} {a : AState} {v : Word}

/-- **Step 3**: zeroing `freshZ` after the cut, at the state with fresh walk memos. -/
theorem PhaseBStart.zeroed (hd : a.store.dropScratch = a.store) (hc : a.caches = Caches.empty)
    (h : PhaseBStart pins dn ds fe pend (cutT m) a v) :
    PhaseBStart pins dn ds fe pend (freshMem m) { a with memos := Memos.empty } v :=
  have htop := top_tier0_of h.loop.check h.twin.off
  have hk := envKeysIn_of h.loop.check.arena.1 h.twin
  ⟨h.loop.fresh hd hc htop hk, h.mem.fresh, CoreMemos.fresh h.core, h.twin.memos _, CrOK.fresh h.cr⟩

/-- **What phase A leaves for phase B holds at a thread's fresh worker memory and the twin's
worker state**, when there is a pending group. -/
theorem PhaseBStart.fresh (h : PhaseBStart pins dn ds fe pend m a v) (hne : pend.size ≠ 0) :
    PhaseBStart pins dn ds fe pend (freshMem m) a.worker v := by
  have hp : pend.toList ≠ [] := fun e => hne (by rw [← Array.length_toList, e]; rfl)
  rw [worker_eq (h.twin.dropped hp) (h.twin.caches hp)]
  exact h.trunc'.cut.zeroed (h.twin.dropped hp) (h.twin.caches hp)

end main

end L.Arena
