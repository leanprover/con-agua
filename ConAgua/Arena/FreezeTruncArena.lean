import ConAgua.Arena.FreezeTruncStore

/-!
# The truncation theorem, part 4: the store tier (`ArenaR`, `DerR`) (lane parmode)

Each cons table under `truncFrozen` (`StoreTr` from `truncFrozen_ra`/`truncFrozen_sa`), the
pool (`PoolTr`: the pool below its top is kept, and with the scratch flag off the top is in
tier 0), the three tables whose records point into the pool (`lit`, `nstr`, `ls`), the columns
(`ColT2`, `DerR`: tier 0 read below the count) and the walk memos (not frozen).

Hypotheses beyond the relation (see `docs/design/parmode.md`):
* `SlotOff0 m`: every frozen slot table sits at word 2 (`koW = 0`; `TierLay` does not say so);
* `m.ptop0 ≤ m.top`: the saved tier-0 top is not above the top (`PoolOK` bounds `PT0[0]` by
  the size of `POOL`, which the truncation cuts to the top).
-/

namespace L.Arena

open ConRon.Arena

/-- **Every frozen slot table sits at word 2**: the offset word of tier 0 is `0`. -/
def SlotOff0 (m : Mem) : Prop := ∀ x ∈ fzStores, rdW (m.arr64 x.2.1) 1 = 0

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

theorem SlotOff0.ko {m : Mem} (h : SlotOff0 m) {C : ConsSch} (hC : C ∈ fzCS) :
    koW C.sch.sa m 0 = 0 := by
  simp only [L.Arena.koW, tierA_zero']; exact h _ (fzCS_mem hC)

/-- **A cons table whose records read only themselves keeps its relation.** -/
theorem consR_truncL {α δ : Type} {k : IdxKind} [BEq α] [Hashable α] {C : ConsSch}
    {R : Mem → Word → Word → α → Prop} {m : Mem} {on : Bool} {P Q : Tbl α (Idx k) δ}
    (hW : C.WF) (hF : RFrame C.sch R C.hsM) (hL : RLocal C.sch R C.hsM [] [])
    (hC : C ∈ fzCS) (h1 : C.ra + 256 ∉ fzSrcs) (h2 : C.sa + 256 ∉ fzSrcs) (ho : SlotOff0 m)
    (h : ConsR C R m on P Q) : ConsR C R (truncFrozen m) on P Q :=
  consR_iff.mpr (storeR_trunc C.sch R C.hsM C.KP hW.sch hW.kframe (storeTr_trunc m hC h1 h2)
    (ho.ko hC) (rTrans_local hW.sch hF hL (truncFrozen_words m)) (consR_iff.mp h))

section tables
variable {m : Mem} {a : AState} (ho : SlotOff0 m)
include ho

theorem AppR.trunc (h : AppR m a) : AppR (truncFrozen m) a :=
  consR_truncL appCS_wf appFrame appLocal (by simp [fzCS]) (by decide) (by decide) ho h
theorem SortR.trunc (h : SortR m a) : SortR (truncFrozen m) a :=
  consR_truncL sortCS_wf sortFrame sortLocal (by simp [fzCS]) (by decide) (by decide) ho h
theorem ConstR.trunc (h : ConstR m a) : ConstR (truncFrozen m) a :=
  consR_truncL constCS_wf constFrame constLocal (by simp [fzCS]) (by decide) (by decide) ho h
theorem LetR.trunc (h : LetR m a) : LetR (truncFrozen m) a :=
  consR_truncL letCS_wf letFrame letELocal (by simp [fzCS]) (by decide) (by decide) ho h
theorem BVarR.trunc (h : BVarR m a) : BVarR (truncFrozen m) a :=
  consR_truncL bvarCS_wf bvarFrame bvarLocal (by simp [fzCS]) (by decide) (by decide) ho h
theorem FVarR.trunc (h : FVarR m a) : FVarR (truncFrozen m) a :=
  consR_truncL fvarCS_wf fvarFrame fvarLocal (by simp [fzCS]) (by decide) (by decide) ho h
theorem LamR.trunc (h : LamR m a) : LamR (truncFrozen m) a :=
  consR_truncL lamCS_wf laFrame lamLocal (by simp [fzCS]) (by decide) (by decide) ho h
theorem ForallR.trunc (h : ForallR m a) : ForallR (truncFrozen m) a :=
  consR_truncL forallCS_wf faFrame forallELocal (by simp [fzCS]) (by decide) (by decide) ho h
theorem ProjR.trunc (h : ProjR m a) : ProjR (truncFrozen m) a :=
  consR_truncL projCS_wf projFrame projLocal (by simp [fzCS]) (by decide) (by decide) ho h
theorem ZeroR.trunc (h : ZeroR m a) : ZeroR (truncFrozen m) a :=
  consR_truncL zeroCS_wf zeroFrame zeroLocal (by simp [fzCS]) (by decide) (by decide) ho h
theorem SuccR.trunc (h : SuccR m a) : SuccR (truncFrozen m) a :=
  consR_truncL succCS_wf succFrame succLocal (by simp [fzCS]) (by decide) (by decide) ho h
theorem MaxR.trunc (h : MaxR m a) : MaxR (truncFrozen m) a :=
  consR_truncL maxCS_wf maxFrame maxLocal (by simp [fzCS]) (by decide) (by decide) ho h
theorem ImaxR.trunc (h : ImaxR m a) : ImaxR (truncFrozen m) a :=
  consR_truncL imaxCS_wf imaxFrame imaxLocal (by simp [fzCS]) (by decide) (by decide) ho h
theorem ParamR.trunc (h : ParamR m a) : ParamR (truncFrozen m) a :=
  consR_truncL paramCS_wf paramFrame paramLocal (by simp [fzCS]) (by decide) (by decide) ho h
theorem NAnonR.trunc (h : NAnonR m a) : NAnonR (truncFrozen m) a :=
  consR_truncL nanonCS_wf naFrame nanonLocal (by simp [fzCS]) (by decide) (by decide) ho h
theorem NNumR.trunc (h : NNumR m a) : NNumR (truncFrozen m) a :=
  consR_truncL nnumCS_wf nnFrame nnumLocal (by simp [fzCS]) (by decide) (by decide) ho h

end tables

end L.Arena
