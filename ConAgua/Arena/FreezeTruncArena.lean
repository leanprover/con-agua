module

public import ConAgua.Arena.FreezeTruncStore
import ConAgua.Arena.FreezeTruncKeep
public import ConAgua.Arena.FreezeTruncBase

@[expose] public section

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

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem storeTr_trunc (m : Mem) {C : ConsSch} (hC : C ∈ fzCS) (h1 : tier1 C.ra ∉ fzSrcs)
    (h2 : tier1 C.sa ∉ fzSrcs) : StoreTr C.sch m (truncFrozen m) := by
  have hm := fzCS_mem hC
  refine ⟨truncFrozen_ctl m, truncFrozen_other m _ h1, truncFrozen_other m _ h2, ?_, ?_⟩
  · rw [show C.sch.ra = C.ra from rfl, truncFrozen_ra m hm]
    simp only [cntW, ConsSch.sch, UInt64.ofNat_toNat]
    congr 2
    rw [show C.ca + 0 = C.ca from UInt64.add_zero _]
  · rw [show C.sch.sa = C.sa from rfl, truncFrozen_sa m hm]; rfl
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **A cons table whose records read only themselves keeps its relation.** -/
theorem consR_truncL {α δ : Type} {k : IdxKind} [BEq α] [Hashable α] {C : ConsSch}
    {R : Mem → Word → Word → α → Prop} {m : Mem} {on : Bool} {P Q : Tbl α (Idx k) δ}
    (hW : C.WF) (hF : RFrame C.sch R C.hsM) (hL : RLocal C.sch R C.hsM [] [])
    (hC : C ∈ fzCS) (h1 : tier1 C.ra ∉ fzSrcs) (h2 : tier1 C.sa ∉ fzSrcs)
    (h : ConsR C R m on P Q) : ConsR C R (truncFrozen m) on P Q :=
  consR_iff.mpr (storeR_trunc C.sch R C.hsM C.KP hW.sch hW.kframe (storeTr_trunc m hC h1 h2)
    (rTrans_local hW.sch hF hL) (consR_iff.mp h))
-/

section tables
variable {m : Mem} {a : AState}

theorem AppR.trunc (h : AppR m a) : AppR (truncFrozen m) a := by
  sorry
theorem SortR.trunc (h : SortR m a) : SortR (truncFrozen m) a := by
  sorry
theorem ConstR.trunc (h : ConstR m a) : ConstR (truncFrozen m) a := by
  sorry
theorem LetR.trunc (h : LetR m a) : LetR (truncFrozen m) a := by
  sorry
theorem BVarR.trunc (h : BVarR m a) : BVarR (truncFrozen m) a := by
  sorry
theorem FVarR.trunc (h : FVarR m a) : FVarR (truncFrozen m) a := by
  sorry
theorem LamR.trunc (h : LamR m a) : LamR (truncFrozen m) a := by
  sorry
theorem ForallR.trunc (h : ForallR m a) : ForallR (truncFrozen m) a := by
  sorry
theorem ProjR.trunc (h : ProjR m a) : ProjR (truncFrozen m) a := by
  sorry
theorem ZeroR.trunc (h : ZeroR m a) : ZeroR (truncFrozen m) a := by
  sorry
theorem SuccR.trunc (h : SuccR m a) : SuccR (truncFrozen m) a := by
  sorry
theorem MaxR.trunc (h : MaxR m a) : MaxR (truncFrozen m) a := by
  sorry
theorem ImaxR.trunc (h : ImaxR m a) : ImaxR (truncFrozen m) a := by
  sorry
theorem ParamR.trunc (h : ParamR m a) : ParamR (truncFrozen m) a := by
  sorry
theorem NAnonR.trunc (h : NAnonR m a) : NAnonR (truncFrozen m) a := by
  sorry
theorem NNumR.trunc (h : NNumR m a) : NNumR (truncFrozen m) a := by
  sorry

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
  sorry

theorem top_tier0 {m : Mem} (htop : m.top.toNat < 2 ^ 40) :
    m.top >>> 40 = 0 ∧ (m.top &&& 1099511627775).toNat = m.top.toNat := by
  constructor
  · apply UInt64.toNat_inj.mp; rw [tag_tier_toNat]; simp; omega
  · rw [tag_idx_toNat]; omega

/-- **The pool invariant survives the truncation**, the top in tier 0. -/
theorem PoolOK.trunc {m : Mem} (h : PoolOK m) (htop : m.top.toNat < 2 ^ 40) :
    PoolOK (truncFrozen m) := by
  sorry

section pooltab
variable {α : Type} {S : Schema} {R : Mem → Word → Word → α → Prop} {hs : Mem → Word → Word → Word}

/-- **A node relation that reads its record and the pool below the top has the transfer**
to a memory with the pool kept (`PoolTr`). -/
theorem rTrans_pool (hF : RFrame S R hs)
    (hP : ∀ m₁ m₂ : Mem, (∀ t, m₂.arr64 (tierA S.ra t) = m₁.arr64 (tierA S.ra t)) → PoolTr m₁ m₂ →
      (∀ t i a, R m₁ t i a → R m₂ t i a) ∧ ∀ t i, hs m₂ t i = hs m₁ t i)
    (hx : ∀ b ∈ ([POOL, POOL1, PT0, CTL] : List TieredArray), b ≠ S.ra ∧ b ≠ tier1 S.ra)
    {m m' : Mem} (hp : PoolTr m m') : RTrans S R hs m m' := by
  intro t i hf
  let m₁ := (m.setA S.ra (m'.arr64 S.ra)).setA (tier1 S.ra) (m'.arr64 (tier1 S.ra))
  have hne : (S.ra : TieredArray) ≠ tier1 S.ra := t0_ne_tier1 _ _
  have e0 : m₁.arr64 S.ra = m'.arr64 S.ra := by
    simp only [m₁]; rw [Mem.setA_arr, ite_eq_right hne]
    exact Mem.setA_self m m' _
  have e1 : m₁.arr64 (tier1 S.ra) = m'.arr64 (tier1 S.ra) := Mem.setA_self _ m' _
  have eo : ∀ b : TieredArray, b ≠ S.ra → b ≠ tier1 S.ra → m₁.arr64 b = m.arr64 b := fun b h1 h2 => by
    simp only [m₁]; rw [Mem.setA_arr, ite_eq_right h2, Mem.setA_arr, ite_eq_right h1]
  have et : ∀ t, m₁.arr64 (tierA S.ra t) = m'.arr64 (tierA S.ra t) := fun t => by
    rcases tierA_eq_or S.ra t with e | e <;> rw [e]
    · exact e0
    · exact e1
  have hb : ∀ b ∈ ([POOL, POOL1, PT0, CTL] : List TieredArray), m₁.arr64 b = m.arr64 b := fun b hb' =>
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

theorem LitR.trunc (h : LitR m a) : LitR (truncFrozen m) a := by
  sorry

theorem NStrR.trunc (h : NStrR m a) : NStrR (truncFrozen m) a := by
  sorry

theorem LsR.trunc (h : LsR m a) : LsR (truncFrozen m) a := by
  sorry

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

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem ColT2.trunc {α δ : Type} {k : IdxKind} [BEq α] [Hashable α] [Inhabited δ]
    {L : Lens α δ k} {c : ArrId} {ca : Nat} {f : δ → Word} {m : Mem} {a : AState}
    (hB : (c, ca) ∈ fzCols) (h1 : tier1 c ∉ fzSrcs)
    (hc : (rdW (m.arr64 CTL) (UInt64.ofNat ca)).toNat = (L.getP a).nodes.size)
    (h : ColT2 L c f m a) : ColT2 L c f (truncFrozen m) a :=
  ⟨colT_mono h.1 (fun i hi => by
      simp only [tierA_zero]; exact rdcol_trunc m hB (by rw [hc]; exact hi)),
    colT_mono h.2 (fun _ _ => by simp only [tierA_one', truncFrozen_other m _ h1])⟩
-/

theorem rdpcol_trunc (m : Mem) {c : ArrId} {ca : Nat} (hB : (c, ca) ∈ fzPCols) {i : Nat}
    (hi : i < (rdW (m.arr64 CTL) (UInt64.ofNat ca)).toNat)
    (hn : (rdW (m.arr64 CTL) (UInt64.ofNat ca)).toNat < 2 ^ 63) :
    p32Get ((truncFrozen m).arr64 c) (UInt64.ofNat i) = p32Get (m.arr64 c) (UInt64.ofNat i) := by
  rw [truncFrozen_pcol m hB]
  have hn := (rdW (m.arr64 CTL) (UInt64.ofNat ca)).toNat_lt
  have hi64 : i < 2 ^ 64 := by omega
  have he : ((rdW (m.arr64 CTL) (UInt64.ofNat ca) + 1) >>> 1).toNat =
      ((rdW (m.arr64 CTL) (UInt64.ofNat ca)).toNat + 1) % 2 ^ 64 / 2 := by
    simp [UInt64.toNat_shiftRight, UInt64.toNat_add, Nat.shiftRight_eq_div_pow]
  simp only [p32Get]
  congr 1
  apply rdW_extract
  rw [he, UInt64.toNat_div, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
  simp only [show (2 : Word).toNat = 2 from rfl]
  omega

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem DerT2.trunc {α : Type} [BEq α] [Hashable α] {g : ETables → Tbl α EIdx UInt64}
    {c : ArrId} {ca : Nat} {m : Mem} {a : AState} (hB : (c, ca) ∈ fzPCols) (h1 : tier1 c ∉ fzSrcs)
    (hc : (rdW (m.arr64 CTL) (UInt64.ofNat ca)).toNat = (g a.store.pers).nodes.size)
    (hcap : (g a.store.pers).nodes.size ≤ 2 ^ 30)
    (h : DerT2 a g (cP c m)) : DerT2 a g (cP c (truncFrozen m)) := by
  obtain ⟨⟨s0, h0⟩, ⟨s1, h1'⟩⟩ := h
  refine ⟨⟨s0, fun i x hx => ?_⟩, ⟨s1, fun i x hx => ?_⟩⟩
  · have hi := (Array.getElem?_eq_some_iff.mp hx).1
    have := h0 i x hx
    simp only [cP, tierA_zero] at this ⊢
    rw [rdpcol_trunc m hB (by rw [hc]; exact hi) (by rw [hc]; omega)]; exact this
  · have := h1' i x hx
    simp only [cP, tierA_one'] at this ⊢
    rw [truncFrozen_other m _ h1]; exact this
-/

/-! ## The store tier -/

section arena
variable {m : Mem} {a : AState} (htop : m.top.toNat < 2 ^ 40)
include htop

theorem ArenaR.trunc (h : ArenaR m a) : ArenaR (truncFrozen m) a := by
  sorry

theorem ArenaD.trunc (h : ArenaD m a) : ArenaD (truncFrozen m) a := by
  sorry

end arena

end L.Arena
