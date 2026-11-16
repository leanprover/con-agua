module

public import ConAgua.Arena.InstListSpec
import ConAgua.Arena.Abs1Refine
public import ConAgua.Arena.WhnfBase
public import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Arena.DerRel
import ConAgua.Arena.FVarRangeRefine
import ConAgua.Arena.Inst1Refine
import ConAgua.Arena.LiftRefine
import ConAgua.Arena.SimLib
import ConAgua.L.WordOff
import ConAgua.Arena.WhnfCoreProj

@[expose] public section

/-!
# `inst_list` refines the arena's `instantiateListFast`

`Inst1Refine.lean`'s proof, twice (the pure walk `instantiateList`, the memo walk
`instantiateListGo`), with:

* **The memo tier `ArenaL := ArenaD ∧ ILR`** (`instLC` on array 50), `Abs1Refine.lean`'s `ArenaA`
  pattern: the stores keep it by their frames (`mk*W_frameA`), the twin's interning by `Keeps`.
* **The substitution as a stack slice** (`SpineR`, `WhnfBase.lean`): every statement carries
  `SpineR m o l vs` and the bound `o + l < 2^64`, and every model step leaves the stack array
  alone (`m'.arr64 ILSPN = m.arr64 ILSPN`, in each post), so the slice survives the children.
  The substitution is the twin's range `vs[N - l:N]` (`RangeR`); the `bvar` arm's recursion goes
  to the range's last `q` entries (`RangeR.last`).
-/

open ConRon.Arena ConLeche
open Std.WP
open scoped Lean.Order


namespace L.Arena

theorem ilSch_wf : ilSch.WF := ⟨by decide, by decide⟩

/-! ## The `instantiateList` memo tier -/

/-- The `instLC` relation. -/
def ILR (m : Mem) (a : AState) : Prop := MemoRG ilSch lfKey decE m a.memos.instLC

/-- `ArenaD` and the `instantiateList` memo. -/
def ArenaL (m : Mem) (a : AState) : Prop := ArenaD m a ∧ ILR m a

/-- The arena state with the `instantiateList` memo replaced. -/
def withLLC (a : AState) (mp : Std.HashMap (EIdx × Nat) EIdx) : AState :=
  { a with memos := { a.memos with instLC := mp } }

theorem instLGet_run (x : EIdx × Nat) (a : AState) :
    (instLGet x).run a = .ok (a.memos.instLC[x]?, a) := rfl

theorem instLSet_run (x : EIdx × Nat) (r : EIdx) (a : AState) :
    (instLSet x r).run a = .ok ((), withLLC a (a.memos.instLC.insert x r)) := rfl

theorem instLClear_run (a : AState) : instLClear.run a = .ok ((), withLLC a ∅) := rfl

theorem not_arenaCtl_50 : (50 : Word) ∉ arenaCtl := by
  simp [arenaCtl, storeCtl, memoCtl]
theorem not_arenaCtl_51 : (51 : Word) ∉ arenaCtl := by
  simp [arenaCtl, storeCtl, memoCtl]

/-- `ArenaR` and `DerR` do not read `instLC`. -/
theorem ArenaD.withLLC {m : Mem} {a : AState} (hD : ArenaD m a)
    (mp : Std.HashMap (EIdx × Nat) EIdx) : ArenaD m (withLLC a mp) :=
  ⟨hD.base.with_memos (MemFrame.refl [] [] m) (by simp) (by simp)
    ⟨hD.base.memos.bvar, hD.base.memos.lift, hD.base.memos.inst1, hD.base.memos.fvar⟩,
    DerR.of_store m a _ hD.der rfl⟩

theorem ArenaL.lmemo_set (m m' : Mem) (a : AState) (hA : ArenaL m a) (h c v : Word)
    (hh : h.toNat < 2 ^ 32) (hs : msetG ilSch m h c v = some m') :
    ArenaL m' (withLLC a (a.memos.instLC.insert (decE h, c.toNat) (decE v))) := by
  have hf := msetG_frame ilSch ilSch_wf m m' h c v hs
  refine ⟨ArenaD.withLLC ⟨hA.1.1.frame (by decide) (by simpa using not_arenaCtl_51) hf,
    DerR.frameM _ _ m m' hf (by decide) _ hA.1.2⟩ _, ?_⟩
  exact memoRG_set ilSch ilSch_wf lfKey decE m _ hA.2 h c v hh m' hs

theorem ArenaL.lmemo_clear (m : Mem) (a : AState) (hA : ArenaL m a)
    (h0 : rdW (m.arr64 CTL) 50 + 2 ≠ 0) : ArenaL (mclearFitG ilSch m) (withLLC a ∅) := by
  have hf := mclearFitG_frame ilSch ilSch_wf m
  have hC : ∀ x ∈ [ilSch.cs, ilSch.cs + 1], x ∉ arenaCtl := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact not_arenaCtl_50
    · exact not_arenaCtl_51
  exact ⟨ArenaD.withLLC ⟨hA.1.1.frame (by decide) hC hf, DerR.frameM _ _ m _ hf (by decide) _ hA.1.2⟩ _,
    memoRG_clearFit ilSch ilSch_wf lfKey decE m _ hA.2 h0⟩

/-- **`ILR` survives a writer apart from it, if the twin's memo did not move.** -/
theorem ILR.across {A : List TieredArray} {C : List Word} {m m' : Mem} {a a' : AState}
    (hR : ILR m a) (hf : MemFrame A C m m') (hA : (ILMEMO : TieredArray) ∉ A) (hC : (50 : Word) ∉ C)
    (he : a'.memos.instLC = a.memos.instLC) : ILR m' a' := by
  unfold ILR; rw [he]
  exact memoRG_frame ilSch ilSch_wf lfKey decE A C hA hC m m' hf _ hR

theorem keeps_internNodeE_il (v : ENodeView) : Keeps (·.memos.instLC) (internNodeE v) := by
  prim_keeps internNodeE
theorem keeps_internLamE_il (ty b : EIdx) : Keeps (·.memos.instLC) (internLamE ty b) := by
  prim_keeps internLamE
theorem keeps_internForallEE_il (ty b : EIdx) : Keeps (·.memos.instLC) (internForallEE ty b) := by
  prim_keeps internForallEE
theorem keeps_internE_il (v : ENodeView) : Keeps (·.memos.instLC) (internE v) := by
  cases v <;> simp only [internE] <;>
    first | exact keeps_internNodeE_il _ | exact keeps_internLamE_il _ _ | exact keeps_internForallEE_il _ _

theorem internE_instLC (v : ENodeView) (a : AState) (hok : AM.ok (internE v) a) :
    (AM.st (internE v) a).memos.instLC = a.memos.instLC :=
  (keeps_internE_il v).run (AM.run_of_ok _ _ hok)

/-- A writer that leaves array 144 alone keeps the stack. -/
theorem spn_of_frame {A : List TieredArray} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : (ILSPN : TieredArray) ∉ A) : m'.arr64 ILSPN = m.arr64 ILSPN := hf.arr ILSPN hA (by decide)

/-! ## The `mk_*` and `intern_bvar` under `ArenaL` -/

theorem mkApp_okL (m : Mem) (a : AState) (hA : ArenaL m a) (f x r : Word) (m' : Mem)
    (hI : mkAppW m f x = some (r, m')) :
    AM.ok (internE (.app (decE f) (decE x))) a ∧
    ArenaL m' (AM.st (internE (.app (decE f) (decE x))) a) ∧
    AM.res (internE (.app (decE f) (decE x))) a = decE r ∧ m'.arr64 ILSPN = m.arr64 ILSPN := by
  obtain ⟨hok, hD, hres⟩ := mkApp_ok m a hA.1 f x r m' hI
  have hf := L.Arena.mkAppW_frame m m' f x r hI
  exact ⟨hok, ⟨hD, hA.2.across hf (by decide) (by decide) (internE_instLC _ a hok)⟩, hres,
    spn_of_frame hf (by decide)⟩

theorem mkLam_okL (m : Mem) (a : AState) (hA : ArenaL m a) (t b r : Word) (m' : Mem)
    (hI : mkLamW m t b = some (r, m')) :
    AM.ok (internE (.lam (decE t) (decE b))) a ∧
    ArenaL m' (AM.st (internE (.lam (decE t) (decE b))) a) ∧
    AM.res (internE (.lam (decE t) (decE b))) a = decE r ∧ m'.arr64 ILSPN = m.arr64 ILSPN := by
  obtain ⟨hok, hD, hres⟩ := mkLam_ok m a hA.1 t b r m' hI
  have hf := mkLamW_frameA m m' t b r hI
  exact ⟨hok, ⟨hD, hA.2.across hf (by decide) (by decide) (internE_instLC _ a hok)⟩, hres,
    spn_of_frame hf (by decide)⟩

theorem mkForall_okL (m : Mem) (a : AState) (hA : ArenaL m a) (t b r : Word) (m' : Mem)
    (hI : mkForallW m t b = some (r, m')) :
    AM.ok (internE (.forallE (decE t) (decE b))) a ∧
    ArenaL m' (AM.st (internE (.forallE (decE t) (decE b))) a) ∧
    AM.res (internE (.forallE (decE t) (decE b))) a = decE r ∧ m'.arr64 ILSPN = m.arr64 ILSPN := by
  obtain ⟨hok, hD, hres⟩ := mkForall_ok m a hA.1 t b r m' hI
  have hf := mkForallW_frameA m m' t b r hI
  exact ⟨hok, ⟨hD, hA.2.across hf (by decide) (by decide) (internE_instLC _ a hok)⟩, hres,
    spn_of_frame hf (by decide)⟩

theorem mkLet_okL (m : Mem) (a : AState) (hA : ArenaL m a) (t v b r : Word) (m' : Mem)
    (hI : mkLetW m t v b = some (r, m')) :
    AM.ok (internE (.letE (decE t) (decE v) (decE b))) a ∧
    ArenaL m' (AM.st (internE (.letE (decE t) (decE v) (decE b))) a) ∧
    AM.res (internE (.letE (decE t) (decE v) (decE b))) a = decE r ∧
    m'.arr64 ILSPN = m.arr64 ILSPN := by
  obtain ⟨hok, hD, hres⟩ := mkLet_ok m a hA.1 t v b r m' hI
  have hf := mkLetW_frameA m m' t v b r hI
  exact ⟨hok, ⟨hD, hA.2.across hf (by decide) (by decide) (internE_instLC _ a hok)⟩, hres,
    spn_of_frame hf (by decide)⟩

theorem mkProj_okL (m : Mem) (a : AState) (hA : ArenaL m a) (n i e r : Word) (m' : Mem)
    (hI : mkProjW m n i e = some (r, m')) :
    AM.ok (internE (.proj (decI n) i.toNat (decE e))) a ∧
    ArenaL m' (AM.st (internE (.proj (decI n) i.toNat (decE e))) a) ∧
    AM.res (internE (.proj (decI n) i.toNat (decE e))) a = decE r ∧
    m'.arr64 ILSPN = m.arr64 ILSPN := by
  obtain ⟨hok, hD, hres⟩ := mkProj_ok m a hA.1 n i e r m' hI
  have hf := mkProjW_frameA m m' n i e r hI
  exact ⟨hok, ⟨hD, hA.2.across hf (by decide) (by decide) (internE_instLC _ a hok)⟩, hres,
    spn_of_frame hf (by decide)⟩

theorem internBVar_L (m : Mem) (a : AState) (hA : ArenaL m a) (u r : Word) (m' : Mem)
    (hI : binternW m u = some (r, m')) :
    AM.ok (internE (.bvar u.toNat)) a ∧ ArenaL m' (AM.st (internE (.bvar u.toNat)) a) ∧
    AM.res (internE (.bvar u.toNat)) a = decE r ∧ m'.arr64 ILSPN = m.arr64 ILSPN := by
  obtain ⟨hok, hD, hres⟩ := internBVar_D m a hA.1 u r m' hI
  have hf := binternW_frameA m m' u r hI
  exact ⟨hok, ⟨hD, hA.2.across hf (by decide) (by decide) (internE_instLC _ a hok)⟩, hres,
    spn_of_frame hf (by decide)⟩

/-! ## The substitution's slice -/

theorem eidxCopyUpto_toList (xs : Array EIdx) : ∀ (N i : Nat) (out : Array EIdx), xs.size - i ≤ N →
    (eidxCopyUpto xs xs.size i out).toList = out.toList ++ xs.toList.drop i := by
  intro N
  induction N with
  | zero =>
    intro i out hN
    rw [eidxCopyUpto]
    have : ¬ (i < xs.size ∧ i < xs.size) := fun h => by omega
    simp only [this, dite_false]
    simp [List.drop_eq_nil_of_le (by simp; omega : xs.toList.length ≤ i)]
  | succ N ih =>
    intro i out hN
    rw [eidxCopyUpto]
    by_cases hi : i < xs.size
    · simp only [hi, and_self, dite_true]
      rw [ih (i + 1) _ (by omega)]
      rw [List.drop_eq_getElem_cons (i := i) (by simp; exact hi : i < xs.toList.length)]
      simp
    · have : ¬ (i < xs.size ∧ i < xs.size) := fun h => hi h.1
      simp only [this, dite_false]
      simp [List.drop_eq_nil_of_le (by simp; omega : xs.toList.length ≤ i)]

theorem slice_word (o l q : Word) (i : Nat) (_hb : o.toNat + l.toNat < 2 ^ 64) (hq : q < l)
    (_hi : i < q.toNat) :
    o + (l - q) + i.toUInt64 = o + (l.toNat - q.toNat + i).toUInt64 := by
  have hq' : q.toNat < l.toNat := hq
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hq)]
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
  have := q.toNat_lt
  omega

/-- **The substitution's range** (the twin's `instantiateList vs N k`, `k` the slice's length): the
stack slice `(o, l)` is the range `vs[N - l:N]` of the array `vs`, itself the slice `(o₀, C)` with
`N ≤ C`. The `bvar` arm's re-entry is the same range's last `q` entries (`RangeR.last`). -/
def RangeR (m : Mem) (o l : Word) (vs : Array EIdx) (N : Nat) : Prop :=
  ∃ o₀ C : Word, SpineR m o₀ C vs ∧ o₀.toNat + C.toNat < 2 ^ 64 ∧ N ≤ C.toNat ∧ l.toNat ≤ N ∧
    o.toNat = o₀.toNat + (N - l.toNat)

theorem RangeR.of_spn {m m' : Mem} {o l : Word} {vs : Array EIdx} {N : Nat} (h : RangeR m o l vs N)
    (hs : m'.arr64 ILSPN = m.arr64 ILSPN) : RangeR m' o l vs N := by
  obtain ⟨o₀, C, hx, h1, h2, h3, h4⟩ := h
  exact ⟨o₀, C, hx.of_spn hs, h1, h2, h3, h4⟩

theorem RangeR.bound {m : Mem} {o l : Word} {vs : Array EIdx} {N : Nat} (h : RangeR m o l vs N) :
    o.toNat + l.toNat < 2 ^ 64 := by
  obtain ⟨o₀, C, -, h1, h2, h3, h4⟩ := h; omega

theorem RangeR.le_size {m : Mem} {o l : Word} {vs : Array EIdx} {N : Nat} (h : RangeR m o l vs N) :
    l.toNat ≤ N ∧ N ≤ vs.size := by
  obtain ⟨o₀, C, hx, -, h2, h3, -⟩ := h; rw [hx.size]; omega

/-- **A whole slice is its own range.** -/
theorem RangeR.ofSpine {m : Mem} {o l : Word} {vs : Array EIdx} (hx : SpineR m o l vs)
    (hb : o.toNat + l.toNat < 2 ^ 64) : RangeR m o l vs vs.size :=
  ⟨o, l, hx, hb, by have := hx.size; omega, by have := hx.size; omega, by have := hx.size; omega⟩

/-- **The range `vs[s:N]` of a slice** (`instantiateRevRange`'s, `s < N ≤ vs.size`): the stack slice
`(o₀ + s, N - s)`. -/
theorem RangeR.ofSub {m : Mem} {o₀ C : Word} {vs : Array EIdx} (hx : SpineR m o₀ C vs)
    (hb : o₀.toNat + C.toNat < 2 ^ 64) (s N : Nat) (hs : s ≤ N) (hN : N ≤ C.toNat) :
    RangeR m (o₀ + s.toUInt64) (N - s).toUInt64 vs N := by
  have hC := C.toNat_lt
  have e1 : (N - s).toUInt64.toNat = N - s := by
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
  refine ⟨o₀, C, hx, hb, hN, by rw [e1]; omega, ?_⟩
  rw [UInt64.toNat_add, e1]; simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega

/-- **The range's last `q` entries**: the `bvar` arm's re-entry. -/
theorem RangeR.last {m : Mem} {o l q : Word} {vs : Array EIdx} {N : Nat} (h : RangeR m o l vs N)
    (hq : q < l) : RangeR m (o + (l - q)) q vs N ∧ (o + (l - q)).toNat + q.toNat < 2 ^ 64 := by
  have hb := h.bound
  obtain ⟨o₀, C, hx, h1, h2, h3, h4⟩ := h
  have hq' : q.toNat < l.toNat := hq
  have ho : (o + (l - q)).toNat = o.toNat + (l.toNat - q.toNat) := by
    rw [UInt64.toNat_add, UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hq)]
    exact Nat.mod_eq_of_lt (by omega)
  exact ⟨⟨o₀, C, hx, h1, h2, by omega, by rw [ho]; omega⟩, by omega⟩

/-- **The range's entry `q` from its end** (`vs[N - 1 - q]`, the `bvar` arm's value). -/
theorem RangeR.entry {m : Mem} {o l q : Word} {vs : Array EIdx} {N : Nat} (h : RangeR m o l vs N)
    (hq : q < l) :
    q.toNat < N ∧ N ≤ vs.size ∧ ∃ hlt : N - 1 - q.toNat < vs.size,
      vs[N - 1 - q.toNat] = decE (slW m (o + (l - 1 - q))) ∧
      (slW m (o + (l - 1 - q))).toNat < 2 ^ 32 := by
  have hb := h.bound
  obtain ⟨o₀, C, hx, h1, h2, h3, h4⟩ := h
  have hq' : q.toNat < l.toNat := hq
  have hs : vs.size = C.toNat := hx.size
  have hw : o + (l - 1 - q) = o₀ + (N - 1 - q.toNat).toUInt64 := by
    apply UInt64.toNat_inj.mp
    have h1' : (1 : Word) ≤ l := by
      rw [UInt64.le_iff_toNat_le]; simp; omega
    have h2' : q ≤ l - 1 := by
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ h1']; simp; omega
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_sub_of_le _ _ h2',
      UInt64.toNat_sub_of_le _ _ h1']
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', UInt64.toNat_one]
    have := C.toNat_lt
    omega
  refine ⟨by omega, by omega, by omega, ?_, ?_⟩
  · rw [hx.get, slW, hw]; rfl
  · rw [slW, hw]; exact hx.lt _ (by omega)

/-! ## The cut-off -/

theorem instListCutoff_run (h : EIdx) (d : Nat) (a : AState) :
    (instListCutoff h d).run a =
      .ok ((decide ((bvarOfData (a.store.derived h)).toNat < satRange) &&
        decide ((bvarOfData (a.store.derived h)).toNat ≤ d)), a) := rfl

theorem ilcut_iff (m : Mem) (a : AState) (hA : ArenaL m a) (h d : Word) (hh : h.toNat < 2 ^ 32) :
    ilCut m h d ↔ (decide ((bvarOfData (a.store.derived (decE h))).toNat < satRange) &&
        decide ((bvarOfData (a.store.derived (decE h))).toNat ≤ d.toNat)) = true := by
  rw [← derBW_ok m a hA.1.1 hA.1.2 h hh]; exact cut_iff _ _

/-! ## The statements, by fuel -/

/-- The walks' relation: `ArenaL`, and the spine stack as at `m₀` (named, so `Sim` can carry it). -/
abbrev SpnR (m₀ m' : Mem) (a' : AState) : Prop := ArenaL m' a' ∧ m'.arr64 ILSPN = m₀.arr64 ILSPN

/-- What `il_go`'s model at L fuel `n` and counter `fu` says about `instantiateList vs` at the
twin fuel `fu.toNat` (exactly: the counter is the twin's `fuel`; any L fuel). -/
def ILGoOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (h d o l fu r : Word) (vs : Array EIdx) (N : Nat),
    ArenaL m a → RangeR m o l vs N → o.toNat + l.toNat < 2 ^ 64 → h.toNat < 2 ^ 32 →
    ilW n m h d o l fu = some (r, m') →
    ∃ a', (instantiateList vs N l.toNat fu.toNat (decE h) d.toNat).run a = .ok (decE r, a') ∧ ArenaL m' a' ∧
      m'.arr64 ILSPN = m.arr64 ILSPN

/-- The same for `ilg_go`'s model and `instantiateListGo vs`. -/
def ILGGoOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (h d o l fu r : Word) (vs : Array EIdx) (N : Nat),
    ArenaL m a → RangeR m o l vs N → o.toNat + l.toNat < 2 ^ 64 → h.toNat < 2 ^ 32 →
    ilgW n m h d o l fu = some (r, m') →
    ∃ a', (instantiateListGo vs N l.toNat fu.toNat (decE h) d.toNat).run a = .ok (decE r, a') ∧ ArenaL m' a' ∧
      m'.arr64 ILSPN = m.arr64 ILSPN

/-- The arena arm `arm` refines the L arm `armW` at `h`, under `ArenaL`, keeping the stack. -/
def LArmRef (n : Nat) (armW : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem))
    (arm : AM EIdx) (m m' : Mem) (a : AState) (h d o l fu r : Word) : Prop :=
  armW n m h d o l fu = some (r, m') →
    ∃ a', arm.run a = .ok (decE r, a') ∧ ArenaL m' a' ∧ m'.arr64 ILSPN = m.arr64 ILSPN

/-- The pure walk's six arms, each at its tag. -/
def ILArmOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (h d o l fu r : Word) (vs : Array EIdx) (N : Nat),
    ArenaL m a → RangeR m o l vs N → o.toNat + l.toNat < 2 ^ 64 → h.toNat < 2 ^ 32 →
    (tagW h = 4 → LArmRef n ilAppW (instListArmApp vs N l.toNat fu.toNat (decE h) d.toNat) m m' a h d o l fu r) ∧
    (tagW h = 5 → LArmRef n ilLamW (instListArmBind vs N l.toNat fu.toNat (decE h) d.toNat) m m' a h d o l fu r) ∧
    (tagW h = 6 → LArmRef n ilForallW (instListArmBind vs N l.toNat fu.toNat (decE h) d.toNat) m m' a h d o l fu r) ∧
    (tagW h = 7 → LArmRef n ilLetW (instListArmLet vs N l.toNat fu.toNat (decE h) d.toNat) m m' a h d o l fu r) ∧
    (tagW h = 9 → LArmRef n ilProjW (instListArmProj vs N l.toNat fu.toNat (decE h) d.toNat) m m' a h d o l fu r) ∧
    (tagW h = 0 → LArmRef n ilBVarW (instListArmBVar vs N l.toNat fu.toNat (decE h) d.toNat) m m' a h d o l fu r)

/-- The memo walk's five arms, each at its tag. -/
def ILGArmOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (h d o l fu r : Word) (vs : Array EIdx) (N : Nat),
    ArenaL m a → RangeR m o l vs N → o.toNat + l.toNat < 2 ^ 64 → h.toNat < 2 ^ 32 →
    (tagW h = 4 → LArmRef n ilgAppW (instListGoArmApp vs N l.toNat fu.toNat (decE h) d.toNat) m m' a h d o l fu r) ∧
    (tagW h = 5 → LArmRef n ilgLamW (instListGoArmBind vs N l.toNat fu.toNat (decE h) d.toNat) m m' a h d o l fu r) ∧
    (tagW h = 6 →
      LArmRef n ilgForallW (instListGoArmBind vs N l.toNat fu.toNat (decE h) d.toNat) m m' a h d o l fu r) ∧
    (tagW h = 7 → LArmRef n ilgLetW (instListGoArmLet vs N l.toNat fu.toNat (decE h) d.toNat) m m' a h d o l fu r) ∧
    (tagW h = 9 → LArmRef n ilgProjW (instListGoArmProj vs N l.toNat fu.toNat (decE h) d.toNat) m m' a h d o l fu r)

/-! ## The dispatchers -/

theorem ilgoOK_succ (n : Nat) (ih : ILArmOK n) : ILGoOK (n + 1) := by
  intro m m' a h d o l fu r vs N hA hsl hbd hh hb
  have hfu : ¬ fu = 0 := fun hfu => by rw [ilW.abort1 n m h d o l fu hfu] at hb; cases hb
  rw [L.toNat_eq_toNat_sub_one_add_one fu hfu, instantiateList_succ, StateT.run_bind, instListCutoff_run]
  simp only [except_ok_bind]
  by_cases hcut : ilCut m h d
  · rw [ilW.arm1 n m h d o l fu hfu hcut] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    rw [ilcut_iff m a hA h d hh] at hcut
    simp only [hcut, ↓reduceIte]
    exact ⟨a, rfl, hA, by simp⟩
  have hcut' := hcut
  rw [ilcut_iff m a hA h d hh] at hcut'
  simp only [Bool.not_eq_true] at hcut'
  simp only [hcut', Bool.false_eq_true, ↓reduceIte, decE_tag h hh]
  have arm := ih m m' a h d o l (fu - 1) r vs N hA hsl hbd hh
  have t4 : tagW h = 4 ↔ (tagW h).toUInt32 = 4 := by simpa using tag_iff h 4 hh (by decide)
  have t5 : tagW h = 5 ↔ (tagW h).toUInt32 = 5 := by simpa using tag_iff h 5 hh (by decide)
  have t6 : tagW h = 6 ↔ (tagW h).toUInt32 = 6 := by simpa using tag_iff h 6 hh (by decide)
  have t0 : tagW h = 0 ↔ (tagW h).toUInt32 = 0 := by simpa using tag_iff h 0 hh (by decide)
  have t7 : tagW h = 7 ↔ (tagW h).toUInt32 = 7 := by simpa using tag_iff h 7 hh (by decide)
  have t9 : tagW h = 9 ↔ (tagW h).toUInt32 = 9 := by simpa using tag_iff h 9 hh (by decide)
  simp only [ETag.app, ETag.isBind, ETag.lam, ETag.forallE, ETag.bvar, ETag.letE, ETag.proj,
    beq_iff_eq, Bool.or_eq_true] at *
  by_cases g4 : tagW h = 4
  · rw [ilW.arm2 n m h d o l fu hfu hcut g4] at hb
    simp only [show (tagW h).toUInt32 = 4 from (t4.mp g4), ↓reduceIte]
    exact arm.1 g4 hb
  have g4' : ¬ (tagW h).toUInt32 = 4 := fun e => g4 (t4.mpr e)
  by_cases g5 : tagW h = 5
  · rw [ilW.arm3 n m h d o l fu hfu hcut g4 g5] at hb
    simp only [show (tagW h).toUInt32 = 5 from (t5.mp g5), true_or, ↓reduceIte]
    exact arm.2.1 g5 hb
  have g5' : ¬ (tagW h).toUInt32 = 5 := fun e => g5 (t5.mpr e)
  by_cases g6 : tagW h = 6
  · rw [ilW.arm4 n m h d o l fu hfu hcut g4 g5 g6] at hb
    simp only [show (tagW h).toUInt32 = 6 from (t6.mp g6), or_true, ↓reduceIte]
    exact arm.2.2.1 g6 hb
  have g6' : ¬ (tagW h).toUInt32 = 6 := fun e => g6 (t6.mpr e)
  simp only [g4', g5', g6', or_self, ↓reduceIte]
  by_cases g7 : tagW h = 7
  · rw [ilW.arm5 n m h d o l fu hfu hcut g4 g5 g6 g7] at hb
    simp only [show (tagW h).toUInt32 = 7 from (t7.mp g7), ↓reduceIte]
    exact arm.2.2.2.1 g7 hb
  have g7' : ¬ (tagW h).toUInt32 = 7 := fun e => g7 (t7.mpr e)
  simp only [g7', ↓reduceIte]
  by_cases g9 : tagW h = 9
  · rw [ilW.arm6 n m h d o l fu hfu hcut g4 g5 g6 g7 g9] at hb
    simp only [show (tagW h).toUInt32 = 9 from (t9.mp g9), ↓reduceIte]
    exact arm.2.2.2.2.1 g9 hb
  have g9' : ¬ (tagW h).toUInt32 = 9 := fun e => g9 (t9.mpr e)
  simp only [g9', ↓reduceIte]
  by_cases g0 : tagW h = 0
  · rw [ilW.arm7 n m h d o l fu hfu hcut g4 g5 g6 g7 g9 g0] at hb
    simp only [show (tagW h).toUInt32 = 0 from (t0.mp g0), ↓reduceIte]
    exact arm.2.2.2.2.2 g0 hb
  have g0' : ¬ (tagW h).toUInt32 = 0 := fun e => g0 (t0.mpr e)
  simp only [g0', ↓reduceIte]
  rw [ilW.arm8 n m h d o l fu hfu hcut g4 g5 g6 g7 g9 g0] at hb
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
  exact ⟨a, rfl, hA, by simp⟩

theorem ilggoOK_succ (n : Nat) (ih : ILGArmOK n) (ihl : ILGoOK n) : ILGGoOK (n + 1) := by
  intro m m' a h d o l fu r vs N hA hsl hbd hh hb
  have hfu : ¬ fu = 0 := fun hfu => by rw [ilgW.abort1 n m h d o l fu hfu] at hb; cases hb
  rw [L.toNat_eq_toNat_sub_one_add_one fu hfu, instantiateListGo_succ, StateT.run_bind, instListCutoff_run]
  simp only [except_ok_bind]
  by_cases hcut : ilCut m h d
  · rw [ilgW.arm1 n m h d o l fu hfu hcut] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    rw [ilcut_iff m a hA h d hh] at hcut
    simp only [hcut, ↓reduceIte]
    exact ⟨a, rfl, hA, by simp⟩
  have hcut' := hcut
  rw [ilcut_iff m a hA h d hh] at hcut'
  simp only [Bool.not_eq_true] at hcut'
  simp only [hcut', Bool.false_eq_true, ↓reduceIte, decE_tag h hh]
  have arm := ih m m' a h d o l (fu - 1) r vs N hA hsl hbd hh
  have t4 : tagW h = 4 ↔ (tagW h).toUInt32 = 4 := by simpa using tag_iff h 4 hh (by decide)
  have t5 : tagW h = 5 ↔ (tagW h).toUInt32 = 5 := by simpa using tag_iff h 5 hh (by decide)
  have t6 : tagW h = 6 ↔ (tagW h).toUInt32 = 6 := by simpa using tag_iff h 6 hh (by decide)
  have t0 : tagW h = 0 ↔ (tagW h).toUInt32 = 0 := by simpa using tag_iff h 0 hh (by decide)
  have t7 : tagW h = 7 ↔ (tagW h).toUInt32 = 7 := by simpa using tag_iff h 7 hh (by decide)
  have t9 : tagW h = 9 ↔ (tagW h).toUInt32 = 9 := by simpa using tag_iff h 9 hh (by decide)
  simp only [ETag.app, ETag.isBind, ETag.lam, ETag.forallE, ETag.bvar, ETag.letE, ETag.proj,
    beq_iff_eq, Bool.or_eq_true] at *
  by_cases g4 : tagW h = 4
  · rw [ilgW.arm2 n m h d o l fu hfu hcut g4] at hb
    simp only [show (tagW h).toUInt32 = 4 from (t4.mp g4), ↓reduceIte]
    exact arm.1 g4 hb
  have g4' : ¬ (tagW h).toUInt32 = 4 := fun e => g4 (t4.mpr e)
  by_cases g5 : tagW h = 5
  · rw [ilgW.arm3 n m h d o l fu hfu hcut g4 g5] at hb
    simp only [show (tagW h).toUInt32 = 5 from (t5.mp g5), true_or, ↓reduceIte]
    exact arm.2.1 g5 hb
  have g5' : ¬ (tagW h).toUInt32 = 5 := fun e => g5 (t5.mpr e)
  by_cases g6 : tagW h = 6
  · rw [ilgW.arm4 n m h d o l fu hfu hcut g4 g5 g6] at hb
    simp only [show (tagW h).toUInt32 = 6 from (t6.mp g6), or_true, ↓reduceIte]
    exact arm.2.2.1 g6 hb
  have g6' : ¬ (tagW h).toUInt32 = 6 := fun e => g6 (t6.mpr e)
  simp only [g4', g5', g6', or_self, ↓reduceIte]
  by_cases g7 : tagW h = 7
  · rw [ilgW.arm5 n m h d o l fu hfu hcut g4 g5 g6 g7] at hb
    simp only [show (tagW h).toUInt32 = 7 from (t7.mp g7), ↓reduceIte]
    exact arm.2.2.2.1 g7 hb
  have g7' : ¬ (tagW h).toUInt32 = 7 := fun e => g7 (t7.mpr e)
  simp only [g7', ↓reduceIte]
  by_cases g9 : tagW h = 9
  · rw [ilgW.arm6 n m h d o l fu hfu hcut g4 g5 g6 g7 g9] at hb
    simp only [show (tagW h).toUInt32 = 9 from (t9.mp g9), ↓reduceIte]
    exact arm.2.2.2.2 g9 hb
  have g9' : ¬ (tagW h).toUInt32 = 9 := fun e => g9 (t9.mpr e)
  simp only [g9', ↓reduceIte]
  by_cases g0 : tagW h = 0
  · rw [ilgW.arm7 n m h d o l fu hfu hcut g4 g5 g6 g7 g9 g0] at hb
    simp only [show (tagW h).toUInt32 = 0 from (t0.mp g0), ↓reduceIte]
    exact ihl m m' a h d o l (fu - 1) r vs N hA hsl hbd hh hb
  have g0' : ¬ (tagW h).toUInt32 = 0 := fun e => g0 (t0.mpr e)
  simp only [g0', ↓reduceIte]
  rw [ilgW.arm8 n m h d o l fu hfu hcut g4 g5 g6 g7 g9 g0] at hb
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
  exact ⟨a, rfl, hA, by simp⟩

/-! ## The pure walk's arms -/

section arms
variable (n : Nat) (ih : ILGoOK n) (m m' : Mem) (a : AState) (hA : ArenaL m a)
  (h d o l fu r : Word) (vs : Array EIdx) (N : Nat) (hsl : RangeR m o l vs N) (hbd : o.toNat + l.toNat < 2 ^ 64)
  (hh : h.toNat < 2 ^ 32)
include ih hA hsl hbd hh

theorem lappArm_ok (hg : tagW h = 4) :
    LArmRef (n + 1) ilAppW (instListArmApp vs N l.toNat fu.toNat (decE h) d.toNat) m m' a h d o l fu r := by
  intro hb
  rw [instListArmApp]
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [ilAppW.abort1 n m h d o l fu hs] at hb; cases hb
  have hv : viewOKA m h := ⟨hs, UInt64.not_le.mp fun hc => by
    rw [ilAppW.abort2 n m h d o l fu hs hc] at hb; cases hb⟩
  obtain ⟨-, hfw, haw⟩ := view_app m a hA.1.1 h hh hv hg
  rw [ilAppW.arm1 n m h d o l fu hv.1 (UInt64.not_le.mpr hv.2)] at hb
  rw [StateT.run_bind, viewApp_run, viewApp_ok m a hA.1.1 h hh hv, except_ok_bind]
  dsimp only
  refine SimD.exists (R := SpnR m) (Sim.bindD (by simp only [ilAppW.k_il_go.none]) (fun _ _ => by rw [ilAppW.k_il_go.arm1])
    (Sim.ofD fun x m₁ e => ih m m₁ a _ d o l fu x vs N hA hsl hbd hfw e) fun x m₁ a₁ hR => ?_) hb
  obtain ⟨hA₁, hs₁⟩ := hR
  refine Sim.bindD (K := ilAppW.k_il_go_2 x) rfl (fun _ _ => rfl)
    (Sim.ofD fun y m₂ e => ih m₁ m₂ a₁ _ d o l fu y vs N hA₁ (hsl.of_spn hs₁) hbd haw e)
        fun y m₂ a₂ hR => ?_
  obtain ⟨hA₂, hs₂⟩ := hR
  refine Sim.ofOk fun r m' hb => ?_
  obtain ⟨hok, hA₃, hres, hs₃⟩ := mkApp_okL m₂ a₂ hA₂ x y r m' hb
  simp only [internAppE]
  exact ⟨hok, hres, hA₃, hs₃.trans (hs₂.trans hs₁)⟩

theorem llamArm_ok (hg : tagW h = 5) :
    LArmRef (n + 1) ilLamW (instListArmBind vs N l.toNat fu.toNat (decE h) d.toNat) m m' a h d o l fu r := by
  intro hb
  have hd1 : ¬ d + 1 = 0 := fun hd1 => by rw [ilLamW.abort1 n m h d o l fu hd1] at hb; cases hb
  rw [instListArmBind]
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [ilLamW.abort2 n m h d o l fu hd1 hs] at hb; cases hb
  have hv : viewOK m h LAM := ⟨hs, UInt64.not_le.mp fun hc => by
    rw [ilLamW.abort3 n m h d o l fu hd1 hs hc] at hb; cases hb⟩
  obtain ⟨-, hfw, haw⟩ := view_lam m a hA.1.1 h hh hv hg
  rw [ilLamW.arm1 n m h d o l fu hd1 hv.1 (UInt64.not_le.mpr hv.2)] at hb
  rw [StateT.run_bind, viewBind_run, viewBind_lam m a hA.1.1 h hh hv hg, except_ok_bind]
  dsimp only
  refine SimD.exists (R := SpnR m) (Sim.bindD (by simp only [ilLamW.k_il_go.none]) (fun _ _ => by rw [ilLamW.k_il_go.arm1])
    (Sim.ofD fun x m₁ e => ih m m₁ a _ d o l fu x vs N hA hsl hbd hfw e) fun x m₁ a₁ hR => ?_) hb
  obtain ⟨hA₁, hs₁⟩ := hR
  refine Sim.bindD (K := ilLamW.k_il_go_2 x) rfl (fun _ _ => rfl)
    (Sim.ofD fun y m₂ e => by
      simpa only [L.toNat_add_one_of_ne d hd1] using ih m₁ m₂ a₁ _ (d + 1) o l fu y vs N hA₁
          (hsl.of_spn hs₁) hbd haw e) fun y m₂ a₂ hR => ?_
  obtain ⟨hA₂, hs₂⟩ := hR
  have hbind : ∀ t b, internBindE (decE h).tag t b = internE (.lam t b) := by
    intro t b; simp [internBindE, decE_tag h hh, hg, ETag.lam, internE]
  refine Sim.ofOk fun r m' hb => ?_
  obtain ⟨hok, hA₃, hres, hs₃⟩ := mkLam_okL m₂ a₂ hA₂ x y r m' hb
  simp only [hbind]
  exact ⟨hok, hres, hA₃, hs₃.trans (hs₂.trans hs₁)⟩

theorem lforallArm_ok (hg : tagW h = 6) :
    LArmRef (n + 1) ilForallW (instListArmBind vs N l.toNat fu.toNat (decE h) d.toNat) m m' a h d o l fu r := by
  intro hb
  have hd1 : ¬ d + 1 = 0 := fun hd1 => by rw [ilForallW.abort1 n m h d o l fu hd1] at hb; cases hb
  rw [instListArmBind]
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [ilForallW.abort2 n m h d o l fu hd1 hs] at hb; cases hb
  have hv : viewOK m h FORALL := ⟨hs, UInt64.not_le.mp fun hc => by
    rw [ilForallW.abort3 n m h d o l fu hd1 hs hc] at hb; cases hb⟩
  obtain ⟨-, hfw, haw⟩ := view_forall m a hA.1.1 h hh hv hg
  rw [ilForallW.arm1 n m h d o l fu hd1 hv.1 (UInt64.not_le.mpr hv.2)] at hb
  rw [StateT.run_bind, viewBind_run, viewBind_forall m a hA.1.1 h hh hv hg, except_ok_bind]
  dsimp only
  refine SimD.exists (R := SpnR m) (Sim.bindD (by simp only [ilForallW.k_il_go.none]) (fun _ _ => by rw [ilForallW.k_il_go.arm1])
    (Sim.ofD fun x m₁ e => ih m m₁ a _ d o l fu x vs N hA hsl hbd hfw e) fun x m₁ a₁ hR => ?_) hb
  obtain ⟨hA₁, hs₁⟩ := hR
  refine Sim.bindD (K := ilForallW.k_il_go_2 x) rfl (fun _ _ => rfl)
    (Sim.ofD fun y m₂ e => by
      simpa only [L.toNat_add_one_of_ne d hd1] using ih m₁ m₂ a₁ _ (d + 1) o l fu y vs N hA₁
          (hsl.of_spn hs₁) hbd haw e) fun y m₂ a₂ hR => ?_
  obtain ⟨hA₂, hs₂⟩ := hR
  have hbind : ∀ t b, internBindE (decE h).tag t b = internE (.forallE t b) := by
    intro t b; simp [internBindE, decE_tag h hh, hg, ETag.lam, internE]
  refine Sim.ofOk fun r m' hb => ?_
  obtain ⟨hok, hA₃, hres, hs₃⟩ := mkForall_okL m₂ a₂ hA₂ x y r m' hb
  simp only [hbind]
  exact ⟨hok, hres, hA₃, hs₃.trans (hs₂.trans hs₁)⟩

theorem lletArm_ok (hg : tagW h = 7) :
    LArmRef (n + 1) ilLetW (instListArmLet vs N l.toNat fu.toNat (decE h) d.toNat) m m' a h d o l fu r := by
  intro hb
  have hd1 : ¬ d + 1 = 0 := fun hd1 => by rw [ilLetW.abort1 n m h d o l fu hd1] at hb; cases hb
  rw [instListArmLet]
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [ilLetW.abort2 n m h d o l fu hd1 hs] at hb; cases hb
  have hv : viewOK m h LET := ⟨hs, UInt64.not_le.mp fun hc => by
    rw [ilLetW.abort3 n m h d o l fu hd1 hs hc] at hb; cases hb⟩
  obtain ⟨-, htw, hvw, hbw⟩ := view_let m a hA.1.1 h hh hv hg
  rw [ilLetW.arm1 n m h d o l fu hd1 hv.1 (UInt64.not_le.mpr hv.2)] at hb
  rw [StateT.run_bind, viewLet_run, viewLet_ok m a hA.1.1 h hh hv, except_ok_bind]
  dsimp only
  refine SimD.exists (R := SpnR m) (Sim.bindD (by simp only [ilLetW.k_il_go.none]) (fun _ _ => by rw [ilLetW.k_il_go.arm1])
    (Sim.ofD fun x m₁ e => ih m m₁ a _ d o l fu x vs N hA hsl hbd htw e) fun x m₁ a₁ hR => ?_) hb
  obtain ⟨hA₁, hs₁⟩ := hR
  refine Sim.bindD (K := ilLetW.k_il_go_2 n d o l fu _ x)
    (by simp only [ilLetW.k_il_go_2.none]) (fun _ _ => by rw [ilLetW.k_il_go_2.arm1])
    (Sim.ofD fun y m₂ e => ih m₁ m₂ a₁ _ d o l fu y vs N hA₁ (hsl.of_spn hs₁) hbd hvw e)
        fun y m₂ a₂ hR => ?_
  obtain ⟨hA₂, hs₂⟩ := hR
  refine Sim.bindD (K := ilLetW.k_il_go_3 x y) rfl (fun _ _ => rfl)
    (Sim.ofD fun z m₃ e => by
      simpa only [L.toNat_add_one_of_ne d hd1] using ih m₂ m₃ a₂ _ (d + 1) o l fu z vs N hA₂
          ((hsl.of_spn hs₁).of_spn hs₂) hbd hbw e) fun z m₃ a₃ hR => ?_
  obtain ⟨hA₃, hs₃⟩ := hR
  refine Sim.ofOk fun r m' hb => ?_
  obtain ⟨hok, hA₄, hres, hs₄⟩ := mkLet_okL m₃ a₃ hA₃ x y z r m' hb
  simp only [internLetEE]
  exact ⟨hok, hres, hA₄, hs₄.trans (hs₃.trans (hs₂.trans hs₁))⟩

theorem lprojArm_ok (hg : tagW h = 9) :
    LArmRef (n + 1) ilProjW (instListArmProj vs N l.toNat fu.toNat (decE h) d.toNat) m m' a h d o l fu r := by
  intro hb
  rw [instListArmProj]
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [ilProjW.abort1 n m h d o l fu hs] at hb; cases hb
  have hv : viewOK m h PROJ := ⟨hs, UInt64.not_le.mp fun hc => by
    rw [ilProjW.abort2 n m h d o l fu hs hc] at hb; cases hb⟩
  obtain ⟨-, -, hew⟩ := view_proj m a hA.1.1 h hh hv hg
  rw [ilProjW.arm1 n m h d o l fu hv.1 (UInt64.not_le.mpr hv.2)] at hb
  rw [StateT.run_bind, viewProj_run, viewProj_ok m a hA.1.1 h hh hv, except_ok_bind]
  dsimp only
  refine SimD.exists (R := SpnR m) (Sim.bindD rfl (fun _ _ => rfl)
    (Sim.ofD fun x m₁ e => ih m m₁ a _ d o l fu x vs N hA hsl hbd hew e) fun x m₁ a₁ hR => ?_) hb
  obtain ⟨hA₁, hs₁⟩ := hR
  refine Sim.ofOk fun r m' hb => ?_
  obtain ⟨hok, hA₂, hres, hs₂⟩ := mkProj_okL m₁ a₁ hA₁ _ _ x r m' hb
  simp only [internProjE]
  exact ⟨hok, hres, hA₂, hs₂.trans hs₁⟩

theorem lbvarArm_ok (_hg : tagW h = 0) :
    LArmRef (n + 1) ilBVarW (instListArmBVar vs N l.toNat fu.toNat (decE h) d.toNat) m m' a h d o l fu r := by
  intro hb
  rw [instListArmBVar]
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [ilBVarW.abort1 n m h d o l fu hs] at hb; cases hb
  have hv : viewOK m h BVAR := ⟨hs, UInt64.not_le.mp fun hc => by
    rw [ilBVarW.abort2 n m h d o l fu hs hc] at hb; cases hb⟩
  rw [StateT.run_bind, viewBVar_run, viewBVar_ok m a hA.1.1 h hh hv, except_ok_bind]
  simp only
  generalize hJ : tfld m BVAR (tierW h) (idxW h) 0 = J at hb ⊢
  by_cases hj : J < d
  · rw [ilBVarW.arm1 n m h d o l fu hv.1 (UInt64.not_le.mpr hv.2) (hJ ▸ hj)] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    rw [ite_eq_left (UInt64.lt_iff_toNat_lt.mp hj)]
    exact ⟨a, rfl, hA, by simp⟩
  have hj' : ¬ J.toNat < d.toNat := fun e => hj (UInt64.lt_iff_toNat_lt.mpr e)
  rw [ite_eq_right hj']
  have hdJ : d ≤ J := UInt64.not_lt.mp hj
  have hsub : (J - d).toNat = J.toNat - d.toNat := UInt64.toNat_sub_of_le _ _ hdJ
  by_cases hq : J - d < l
  · have hqk : J.toNat - d.toNat < l.toNat := by rw [← hsub]; exact hq
    rw [if_pos hqk]
    obtain ⟨hqN, hNs, hlt, hvi, hvl⟩ := hsl.entry hq
    simp only [hsub] at hvi hlt hqN
    rw [dite_cond_eq_true (eq_true ⟨hqN, hNs⟩)]
    simp only [hvi]
    rw [StateT.run_bind, instListCutoff_run, except_ok_bind]
    by_cases hcv : ilCut m (slW m (o + (l - 1 - (J - d)))) d
    · rw [ilBVarW.arm2 n m h d o l fu hv.1 (UInt64.not_le.mpr hv.2) (hJ ▸ hj) (hJ ▸ hq) (hJ ▸ hcv), hJ] at hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      rw [ilcut_iff m a hA _ d hvl] at hcv
      simp only [hcv, ↓reduceIte]
      exact ⟨a, rfl, hA, by simp⟩
    · rw [ilBVarW.arm3 n m h d o l fu hv.1 (UInt64.not_le.mpr hv.2) (hJ ▸ hj) (hJ ▸ hq) (hJ ▸ hcv), hJ] at hb
      rw [ilcut_iff m a hA _ d hvl] at hcv
      simp only [Bool.not_eq_true] at hcv
      simp only [hcv, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨hsl', hbd'⟩ := hsl.last hq
      have := ih m m' a _ d _ _ fu r _ N hA hsl' hbd' hvl hb
      rw [hsub] at this
      exact this
  · rw [ilBVarW.arm4 n m h d o l fu hv.1 (UInt64.not_le.mpr hv.2) (hJ ▸ hj) (hJ ▸ hq)] at hb
    rw [hJ] at hb
    have hq' : ¬ J.toNat - d.toNat < l.toNat := by
      rw [← hsub]; exact fun e => hq (UInt64.lt_iff_toNat_lt.mpr e)
    rw [if_neg hq']
    have hlJ : l ≤ J := by
      rw [UInt64.le_iff_toNat_le]; omega
    obtain ⟨hok, hA', hres, hs'⟩ := internBVar_L m a hA _ r m' hb
    rw [UInt64.toNat_sub_of_le _ _ hlJ] at hok hA' hres
    simp only [internBVarE]
    rw [AM.run_of_ok _ _ hok, hres]
    exact ⟨_, rfl, hA', hs'⟩

end arms


/-! ## The memo walk's probe and tail -/

theorem ltail_ok (op : AM EIdx) (mkr : Option (Word × Mem)) (a₂ : AState) (h c r : Word)
    (m₂ m' : Mem) (hh : h.toNat < 2 ^ 32)
    (hmk : ∀ r₃ m₃, mkr = some (r₃, m₃) →
      AM.ok op a₂ ∧ ArenaL m₃ (AM.st op a₂) ∧ AM.res op a₂ = decE r₃ ∧
        m₃.arr64 ILSPN = m₂.arr64 ILSPN)
    (hb : ilgAppW.k_mk_app h c mkr = some (r, m')) :
    ∃ a', (do let r ← op; instLSet (decE h, c.toNat) r; pure r : AM EIdx).run a₂ =
      .ok (decE r, a') ∧ ArenaL m' a' ∧ m'.arr64 ILSPN = m₂.arr64 ILSPN := by
  cases h3 : mkr with
  | none => rw [h3, ilgAppW.k_mk_app.none] at hb; cases hb
  | some q =>
    obtain ⟨r₃, m₃⟩ := q
    rw [h3] at hb
    have hf : mfindG ilSch m₃ h c ≠ [] := fun hf => by
      rw [ilgAppW.k_mk_app.abort1 _ _ _ _ hf] at hb; cases hb
    rw [ilgAppW.k_mk_app.arm1 _ _ _ _ hf] at hb
    cases h4 : msetG ilSch m₃ h c r₃ with
    | none => rw [msetG, ite_eq_right hf] at h4; rw [h4, ilgAppW.k_ilm_put.none] at hb; cases hb
    | some m₄ =>
      have h5 := h4
      rw [msetG, ite_eq_right hf] at h5
      rw [h5, ilgAppW.k_ilm_put.arm1, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      obtain ⟨hok, hA₃, hres, hs₃⟩ := hmk r₃ m₃ h3
      refine ⟨_, ?_, ArenaL.lmemo_set m₃ m₄ _ hA₃ h c r₃ hh h4,
        (spn_of_frame (msetG_frame ilSch ilSch_wf _ _ _ _ _ h4) (by decide)).trans hs₃⟩
      simp only [StateT.run_bind, AM.run_of_ok _ _ hok, hres, except_ok_bind, instLSet_run]; rfl

theorem lprobe_ok (armW : Option (Word × Mem)) (miss : AM EIdx) (m m' : Mem) (a : AState)
    (hA : ArenaL m a) (h c r : Word) (hh : h.toNat < 2 ^ 32)
    (hhit : mfindG ilSch m h c ≠ [] → (mfindG ilSch m h c).headD 0 ≠ 0 →
      armW = some (rdW (m.arr64 ILMEMO) ((mfindG ilSch m h c).tail.headD 0 * 4 + 3), m))
    (hnone : mfindG ilSch m h c = [] → armW = none)
    (hmiss : mfindG ilSch m h c ≠ [] → (mfindG ilSch m h c).headD 0 = 0 → armW = some (r, m') →
      ∃ a', miss.run a = .ok (decE r, a') ∧ ArenaL m' a' ∧ m'.arr64 ILSPN = m.arr64 ILSPN)
    (hb : armW = some (r, m')) :
    ∃ a', (do
        match ← instLGet (decE h, c.toNat) with
        | some r => pure r
        | none => miss : AM EIdx).run a = .ok (decE r, a') ∧ ArenaL m' a' ∧
      m'.arr64 ILSPN = m.arr64 ILSPN := by
  rw [StateT.run_bind, instLGet_run, except_ok_bind]
  have hr : ¬ mfindG ilSch m h c = [] := fun hr => by rw [hnone hr] at hb; cases hb
  by_cases hh0 : (mfindG ilSch m h c).headD 0 ≠ 0
  · rw [hhit hr hh0] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    rw [show a.memos.instLC[(decE h, c.toNat)]? = _ from
      memoRG_hit ilSch lfKey decE m _ hA.2 h c hr hh0 hh]
    exact ⟨a, rfl, hA, rfl⟩
  · simp only [ne_eq, Decidable.not_not] at hh0
    rw [show a.memos.instLC[(decE h, c.toNat)]? = none from
      memoRG_miss ilSch lfKey decE m _ hA.2 h c hh hr hh0]
    exact hmiss hr hh0 hb

/-! ## The memo walk's arms -/

section garms
variable (n : Nat) (ih : ILGGoOK n) (m m' : Mem) (a : AState) (hA : ArenaL m a)
  (h d o l fu r : Word) (vs : Array EIdx) (N : Nat) (hsl : RangeR m o l vs N) (hbd : o.toNat + l.toNat < 2 ^ 64)
  (hh : h.toNat < 2 ^ 32)
include ih hA hsl hbd hh

theorem gappArm_ok (hg : tagW h = 4) :
    LArmRef (n + 1) ilgAppW (instListGoArmApp vs N l.toNat fu.toNat (decE h) d.toNat) m m' a h d o l fu r := by
  intro hb
  rw [instListGoArmApp]
  refine lprobe_ok _ _ m m' a hA h d r hh (ilgAppW.arm1 n m h d o l fu) (ilgAppW.abort1 n m h d o l fu) (fun hr hh0 hb => ?_) hb
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [ilgAppW.abort2 n m h d o l fu hr hh0 hs] at hb; cases hb
  have hv : viewOKA m h := ⟨hs, UInt64.not_le.mp fun hc => by
    rw [ilgAppW.abort3 n m h d o l fu hr hh0 hs hc] at hb; cases hb⟩
  obtain ⟨-, hfw, haw⟩ := view_app m a hA.1.1 h hh hv hg
  rw [ilgAppW.arm2 n m h d o l fu hr hh0 hv.1 (UInt64.not_le.mpr hv.2)] at hb
  rw [StateT.run_bind, viewApp_run, viewApp_ok m a hA.1.1 h hh hv, except_ok_bind]
  dsimp only
  refine SimD.exists (R := SpnR m) (Sim.bindD (by simp only [ilgAppW.k_ilg_go.none]) (fun _ _ => by rw [ilgAppW.k_ilg_go.arm1])
    (Sim.ofD fun x m₁ e => ih m m₁ a _ d o l fu x vs N hA hsl hbd hfw e) fun x m₁ a₁ hR => ?_) hb
  obtain ⟨hA1, hs1⟩ := hR
  refine Sim.bindD (K := ilgAppW.k_ilg_go_2 h d x) rfl (fun _ _ => rfl)
    (Sim.ofD fun y m₂ e => ih m₁ m₂ a₁ _ d o l fu y vs N hA1 (hsl.of_spn hs1) hbd haw e)
        fun y m₂ a₂ hR => ?_
  obtain ⟨hA2, hs2⟩ := hR
  refine Sim.ofD fun r m' hb => ?_
  obtain ⟨a', h7, h8, h9⟩ := ltail_ok _ _ a₂ h d r m₂ m' hh (fun r₉ m₉ hr₉ => mkApp_okL m₂ a₂ hA2 x y r₉ m₉ hr₉) hb
  refine ⟨a', ?_, h8, h9.trans (hs2.trans hs1)⟩
  exact h7

theorem glamArm_ok (hg : tagW h = 5) :
    LArmRef (n + 1) ilgLamW (instListGoArmBind vs N l.toNat fu.toNat (decE h) d.toNat) m m' a h d o l fu r := by
  intro hb
  have hd1 : ¬ d + 1 = 0 := fun hd1 => by rw [ilgLamW.abort1 n m h d o l fu hd1] at hb; cases hb
  rw [instListGoArmBind]
  refine lprobe_ok _ _ m m' a hA h d r hh (ilgLamW.arm1 n m h d o l fu hd1) (ilgLamW.abort2 n m h d o l fu hd1) (fun hr hh0 hb => ?_) hb
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [ilgLamW.abort3 n m h d o l fu hd1 hr hh0 hs] at hb; cases hb
  have hv : viewOK m h LAM := ⟨hs, UInt64.not_le.mp fun hc => by
    rw [ilgLamW.abort4 n m h d o l fu hd1 hr hh0 hs hc] at hb; cases hb⟩
  obtain ⟨-, hfw, haw⟩ := view_lam m a hA.1.1 h hh hv hg
  rw [ilgLamW.arm2 n m h d o l fu hd1 hr hh0 hv.1 (UInt64.not_le.mpr hv.2)] at hb
  rw [StateT.run_bind, viewBind_run, viewBind_lam m a hA.1.1 h hh hv hg, except_ok_bind]
  dsimp only
  refine SimD.exists (R := SpnR m) (Sim.bindD (by simp only [ilgLamW.k_ilg_go.none]) (fun _ _ => by rw [ilgLamW.k_ilg_go.arm1])
    (Sim.ofD fun x m₁ e => ih m m₁ a _ d o l fu x vs N hA hsl hbd hfw e) fun x m₁ a₁ hR => ?_) hb
  obtain ⟨hA1, hs1⟩ := hR
  refine Sim.bindD (K := ilgLamW.k_ilg_go_2 h d x) rfl (fun _ _ => rfl)
    (Sim.ofD fun y m₂ e => by
      simpa only [L.toNat_add_one_of_ne d hd1] using ih m₁ m₂ a₁ _ (d + 1) o l fu y vs N hA1
          (hsl.of_spn hs1) hbd haw e) fun y m₂ a₂ hR => ?_
  obtain ⟨hA2, hs2⟩ := hR
  have hbind : ∀ t b, internBindE (decE h).tag t b = internE (.lam t b) := by
    intro t b; simp [internBindE, decE_tag h hh, hg, ETag.lam, internE]
  refine Sim.ofD fun r m' hb => ?_
  obtain ⟨a', h7, h8, h9⟩ := ltail_ok _ _ a₂ h d r m₂ m' hh (fun r₉ m₉ hr₉ => mkLam_okL m₂ a₂ hA2 x y r₉ m₉ hr₉) hb
  refine ⟨a', ?_, h8, h9.trans (hs2.trans hs1)⟩
  simp only [hbind]; exact h7

theorem gforallArm_ok (hg : tagW h = 6) :
    LArmRef (n + 1) ilgForallW (instListGoArmBind vs N l.toNat fu.toNat (decE h) d.toNat) m m' a h d o l fu r := by
  intro hb
  have hd1 : ¬ d + 1 = 0 := fun hd1 => by rw [ilgForallW.abort1 n m h d o l fu hd1] at hb; cases hb
  rw [instListGoArmBind]
  refine lprobe_ok _ _ m m' a hA h d r hh (ilgForallW.arm1 n m h d o l fu hd1) (ilgForallW.abort2 n m h d o l fu hd1) (fun hr hh0 hb => ?_) hb
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [ilgForallW.abort3 n m h d o l fu hd1 hr hh0 hs] at hb; cases hb
  have hv : viewOK m h FORALL := ⟨hs, UInt64.not_le.mp fun hc => by
    rw [ilgForallW.abort4 n m h d o l fu hd1 hr hh0 hs hc] at hb; cases hb⟩
  obtain ⟨-, hfw, haw⟩ := view_forall m a hA.1.1 h hh hv hg
  rw [ilgForallW.arm2 n m h d o l fu hd1 hr hh0 hv.1 (UInt64.not_le.mpr hv.2)] at hb
  rw [StateT.run_bind, viewBind_run, viewBind_forall m a hA.1.1 h hh hv hg, except_ok_bind]
  dsimp only
  refine SimD.exists (R := SpnR m) (Sim.bindD (by simp only [ilgForallW.k_ilg_go.none]) (fun _ _ => by rw [ilgForallW.k_ilg_go.arm1])
    (Sim.ofD fun x m₁ e => ih m m₁ a _ d o l fu x vs N hA hsl hbd hfw e) fun x m₁ a₁ hR => ?_) hb
  obtain ⟨hA1, hs1⟩ := hR
  refine Sim.bindD (K := ilgForallW.k_ilg_go_2 h d x) rfl (fun _ _ => rfl)
    (Sim.ofD fun y m₂ e => by
      simpa only [L.toNat_add_one_of_ne d hd1] using ih m₁ m₂ a₁ _ (d + 1) o l fu y vs N hA1
          (hsl.of_spn hs1) hbd haw e) fun y m₂ a₂ hR => ?_
  obtain ⟨hA2, hs2⟩ := hR
  have hbind : ∀ t b, internBindE (decE h).tag t b = internE (.forallE t b) := by
    intro t b; simp [internBindE, decE_tag h hh, hg, ETag.lam, internE]
  refine Sim.ofD fun r m' hb => ?_
  obtain ⟨a', h7, h8, h9⟩ := ltail_ok _ _ a₂ h d r m₂ m' hh (fun r₉ m₉ hr₉ => mkForall_okL m₂ a₂ hA2 x y r₉ m₉ hr₉) hb
  refine ⟨a', ?_, h8, h9.trans (hs2.trans hs1)⟩
  simp only [hbind]; exact h7

theorem gletArm_ok (hg : tagW h = 7) :
    LArmRef (n + 1) ilgLetW (instListGoArmLet vs N l.toNat fu.toNat (decE h) d.toNat) m m' a h d o l fu r := by
  intro hb
  have hd1 : ¬ d + 1 = 0 := fun hd1 => by rw [ilgLetW.abort1 n m h d o l fu hd1] at hb; cases hb
  rw [instListGoArmLet]
  refine lprobe_ok _ _ m m' a hA h d r hh (ilgLetW.arm1 n m h d o l fu hd1) (ilgLetW.abort2 n m h d o l fu hd1) (fun hr hh0 hb => ?_) hb
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [ilgLetW.abort3 n m h d o l fu hd1 hr hh0 hs] at hb; cases hb
  have hv : viewOK m h LET := ⟨hs, UInt64.not_le.mp fun hc => by
    rw [ilgLetW.abort4 n m h d o l fu hd1 hr hh0 hs hc] at hb; cases hb⟩
  obtain ⟨-, htw, hvw, hbw⟩ := view_let m a hA.1.1 h hh hv hg
  rw [ilgLetW.arm2 n m h d o l fu hd1 hr hh0 hv.1 (UInt64.not_le.mpr hv.2)] at hb
  rw [StateT.run_bind, viewLet_run, viewLet_ok m a hA.1.1 h hh hv, except_ok_bind]
  dsimp only
  refine SimD.exists (R := SpnR m) (Sim.bindD (by simp only [ilgLetW.k_ilg_go.none]) (fun _ _ => by rw [ilgLetW.k_ilg_go.arm1])
    (Sim.ofD fun x m₁ e => ih m m₁ a _ d o l fu x vs N hA hsl hbd htw e) fun x m₁ a₁ hR => ?_) hb
  obtain ⟨hA1, hs1⟩ := hR
  refine Sim.bindD (K := ilgLetW.k_ilg_go_2 n h d o l fu _ x)
    (by simp only [ilgLetW.k_ilg_go_2.none]) (fun _ _ => by rw [ilgLetW.k_ilg_go_2.arm1])
    (Sim.ofD fun y m₂ e => ih m₁ m₂ a₁ _ d o l fu y vs N hA1 (hsl.of_spn hs1) hbd hvw e)
        fun y m₂ a₂ hR => ?_
  obtain ⟨hA2, hs2⟩ := hR
  refine Sim.bindD (K := ilgLetW.k_ilg_go_3 h d x y) rfl (fun _ _ => rfl)
    (Sim.ofD fun z m₃ e => by
      simpa only [L.toNat_add_one_of_ne d hd1] using ih m₂ m₃ a₂ _ (d + 1) o l fu z vs N hA2
          ((hsl.of_spn hs1).of_spn hs2) hbd hbw e) fun z m₃ a₃ hR => ?_
  obtain ⟨hA3, hs3⟩ := hR
  have hbind : ∀ t b, internBindE (decE h).tag t b = internE (.forallE t b) := by
    intro t b; simp [internBindE, decE_tag h hh, hg, ETag.lam, internE]
  refine Sim.ofD fun r m' hb => ?_
  obtain ⟨a', h7, h8, h9⟩ := ltail_ok _ _ a₃ h d r m₃ m' hh (fun r₉ m₉ hr₉ => mkLet_okL m₃ a₃ hA3 x y z r₉ m₉ hr₉) hb
  refine ⟨a', ?_, h8, h9.trans (hs3.trans (hs2.trans hs1))⟩
  simp only [internLetEE]; exact h7

theorem gprojArm_ok (hg : tagW h = 9) :
    LArmRef (n + 1) ilgProjW (instListGoArmProj vs N l.toNat fu.toNat (decE h) d.toNat) m m' a h d o l fu r := by
  intro hb
  rw [instListGoArmProj]
  refine lprobe_ok _ _ m m' a hA h d r hh (ilgProjW.arm1 n m h d o l fu) (ilgProjW.abort1 n m h d o l fu) (fun hr hh0 hb => ?_) hb
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [ilgProjW.abort2 n m h d o l fu hr hh0 hs] at hb; cases hb
  have hv : viewOK m h PROJ := ⟨hs, UInt64.not_le.mp fun hc => by
    rw [ilgProjW.abort3 n m h d o l fu hr hh0 hs hc] at hb; cases hb⟩
  obtain ⟨-, -, hew⟩ := view_proj m a hA.1.1 h hh hv hg
  rw [ilgProjW.arm2 n m h d o l fu hr hh0 hv.1 (UInt64.not_le.mpr hv.2)] at hb
  rw [StateT.run_bind, viewProj_run, viewProj_ok m a hA.1.1 h hh hv, except_ok_bind]
  dsimp only
  refine SimD.exists (R := SpnR m) (Sim.bindD rfl (fun _ _ => rfl)
    (Sim.ofD fun x m₁ e => ih m m₁ a _ d o l fu x vs N hA hsl hbd hew e) fun x m₁ a₁ hR => ?_) hb
  obtain ⟨hA1, hs1⟩ := hR
  refine Sim.ofD fun r m' hb => ?_
  obtain ⟨a', h7, h8, h9⟩ := ltail_ok _ _ a₁ h d r m₁ m' hh (fun r₉ m₉ hr₉ => mkProj_okL m₁ a₁ hA1 _ _ x r₉ m₉ hr₉) hb
  refine ⟨a', ?_, h8, h9.trans (hs1)⟩
  simp only [internProjE]; exact h7

end garms

theorem ilarmOK_succ (n : Nat) (ih : ILGoOK n) : ILArmOK (n + 1) := by
  intro m m' a h d o l fu r vs N hA hsl hbd hh
  exact ⟨lappArm_ok n ih m m' a hA h d o l fu r vs N hsl hbd hh,
    llamArm_ok n ih m m' a hA h d o l fu r vs N hsl hbd hh,
    lforallArm_ok n ih m m' a hA h d o l fu r vs N hsl hbd hh,
    lletArm_ok n ih m m' a hA h d o l fu r vs N hsl hbd hh,
    lprojArm_ok n ih m m' a hA h d o l fu r vs N hsl hbd hh,
    lbvarArm_ok n ih m m' a hA h d o l fu r vs N hsl hbd hh⟩

/-- **The model of `il_go` refines `instantiateList`** at the counter's fuel, at every L fuel. -/
theorem ilOK (n : Nat) : ILGoOK n ∧ ILArmOK n := by
  induction n with
  | zero =>
    refine ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb => by simp [ilW] at hb,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    intro _ hb <;> simp [ilAppW, ilLamW, ilForallW, ilLetW, ilProjW, ilBVarW] at hb
  | succ n ih => exact ⟨ilgoOK_succ n ih.2, ilarmOK_succ n ih.1⟩

theorem ilgarmOK_succ (n : Nat) (ih : ILGGoOK n) : ILGArmOK (n + 1) := by
  intro m m' a h d o l fu r vs N hA hsl hbd hh
  exact ⟨gappArm_ok n ih m m' a hA h d o l fu r vs N hsl hbd hh,
    glamArm_ok n ih m m' a hA h d o l fu r vs N hsl hbd hh,
    gforallArm_ok n ih m m' a hA h d o l fu r vs N hsl hbd hh,
    gletArm_ok n ih m m' a hA h d o l fu r vs N hsl hbd hh,
    gprojArm_ok n ih m m' a hA h d o l fu r vs N hsl hbd hh⟩

/-- **The model of `ilg_go` refines `instantiateListGo`** at the counter's fuel, at every L fuel. -/
theorem ilgOK (n : Nat) : ILGGoOK n ∧ ILGArmOK n := by
  induction n with
  | zero =>
    refine ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb => by simp [ilgW] at hb,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    intro _ hb <;> simp [ilgAppW, ilgLamW, ilgForallW, ilgLetW, ilgProjW] at hb
  | succ n ih => exact ⟨ilggoOK_succ n ih.2 (ilOK n).1, ilgarmOK_succ n ih.1⟩

/-! ## The entry `inst_list` refines `instantiateListFast` -/

theorem instRevRange_run (F : Nat) (e : EIdx) (vs : Array EIdx) (s n d : Nat) (a : AState) :
    (instantiateRevRange F e vs s n d).run a =
      ((instantiateListGo vs (if n < vs.size then n else vs.size)
          ((if n < vs.size then n else vs.size) - s) F e d).run (withLLC a ∅) >>=
        fun p => .ok (p.1, withLLC p.2 ∅)) := by
  have hk : (if s < (if n < vs.size then n else vs.size) then (if n < vs.size then n else vs.size) - s
      else 0) = (if n < vs.size then n else vs.size) - s := by
    by_cases h1 : n < vs.size <;> simp only [h1, ite_true, ite_false] <;> split <;> omega
  simp only [instantiateRevRange, hk, StateT.run_bind, instLClear_run, except_ok_bind]
  cases (instantiateListGo vs _ _ F e d).run (withLLC a ∅) <;> rfl

/-- **`inst_list`'s model on a range** (`instantiateListGo vs N k`, between two clears). -/
theorem instListW_range (n : Nat) (m m' : Mem) (a : AState) (hA : ArenaL m a)
    (e o l d r : Word) (vs : Array EIdx) (N : Nat) (hsl : RangeR m o l vs N)
    (he : e.toNat < 2 ^ 32) (hb : instListW n m e o l d = some (r, m')) :
    ∃ a', ((instantiateListGo vs N l.toNat coreWalkFuel (decE e) d.toNat).run (withLLC a ∅) >>=
        fun p => .ok (p.1, withLLC p.2 ∅)) = .ok (decE r, a') ∧ ArenaL m' a' ∧
      m'.arr64 ILSPN = m.arr64 ILSPN ∧ r.toNat < 2 ^ 32 := by
  simp only [instListW] at hb
  have h0 : ¬ rdW (m.arr64 CTL) 50 + 2 = 0 := fun h0 => by simp [h0] at hb
  simp only [h0, ↓reduceIte] at hb
  have hA₀ := ArenaL.lmemo_clear m a hA h0
  have hs₀ : (mclearFitG ilSch m).arr64 ILSPN = m.arr64 ILSPN :=
    spn_of_frame (mclearFitG_frame ilSch ilSch_wf m) (by decide)
  cases hw : ilgW n (mclearFitG ilSch m) e d o l 4000000000 with
  | none => simp [hw, ilclrK] at hb
  | some p =>
    obtain ⟨r₁, m₁⟩ := p
    have h1 : ¬ rdW (m₁.arr64 CTL) 50 + 2 = 0 := fun h1 => by simp [hw, ilclrK, h1] at hb
    simp only [hw, ilclrK, h1, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    obtain ⟨a₁, ha₁, hA₁, hs₁⟩ :=
      (ilgOK n).1 _ _ _ e d o l 4000000000 r₁ vs N hA₀ (hsl.of_spn hs₀) hsl.bound he hw
    rw [coreWalkFuel_toNat] at ha₁
    exact ⟨_, by rw [ha₁, decE_mask]; rfl, ArenaL.lmemo_clear m₁ a₁ hA₁ h1,
      (spn_of_frame (mclearFitG_frame ilSch ilSch_wf m₁) (by decide)).trans (hs₁.trans hs₀), mask_lt r₁⟩

theorem instListW_correct (n : Nat) (m m' : Mem) (a : AState) (hA : ArenaL m a)
    (e o l d r : Word) (vs : Array EIdx) (hsl : SpineR m o l vs) (hbd : o.toNat + l.toNat < 2 ^ 64)
    (he : e.toNat < 2 ^ 32) (hb : instListW n m e o l d = some (r, m')) :
    ∃ a', (instantiateListFast coreWalkFuel (decE e) vs d.toNat).run a = .ok (decE r, a') ∧ ArenaL m' a' ∧
      m'.arr64 ILSPN = m.arr64 ILSPN ∧ r.toNat < 2 ^ 32 := by
  obtain ⟨a', h1, h2⟩ := instListW_range n m m' a hA e o l d r vs vs.size (RangeR.ofSpine hsl hbd) he hb
  refine ⟨a', ?_, h2⟩
  rw [instantiateListFast, instRevRange_run]
  simpa [← hsl.size] using h1

/-- **`inst_list(e, o₀ + s, i - s, d)` on a sub-slice** refines `instantiateRevRange vs s i`. -/
theorem instListW_revRange (n : Nat) (m m' : Mem) (a : AState) (hA : ArenaL m a)
    (e o₀ C d r : Word) (vs : Array EIdx) (hsl : SpineR m o₀ C vs) (hbd : o₀.toNat + C.toNat < 2 ^ 64)
    (s i : Nat) (hs : s ≤ i) (hi : i ≤ C.toNat) (he : e.toNat < 2 ^ 32)
    (hb : instListW n m e (o₀ + s.toUInt64) (i - s).toUInt64 d = some (r, m')) :
    ∃ a', (instantiateRevRange coreWalkFuel (decE e) vs s i d.toNat).run a = .ok (decE r, a') ∧
      ArenaL m' a' ∧ m'.arr64 ILSPN = m.arr64 ILSPN ∧ r.toNat < 2 ^ 32 := by
  obtain ⟨a', h1, h2⟩ := instListW_range n m m' a hA e _ _ d r vs i (RangeR.ofSub hsl hbd s i hs hi) he hb
  refine ⟨a', ?_, h2⟩
  have hC := C.toNat_lt
  have e1 : (i - s).toUInt64.toNat = i - s := by
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
  have e2 : (if i < vs.size then i else vs.size) = i := by rw [hsl.size]; split <;> omega
  rw [instRevRange_run, e2]
  rw [e1] at h1
  exact h1

/-- **`inst_list(e, o, l, d)` refines the arena's `instantiateListFast coreWalkFuel` under
`ArenaL`**, at every L fuel (the walk's counter starts at `coreWalkFuel`), the substitution `vs`
the stack slice `(o, l)`; the stack is left alone. -/
@[refines ConRon.Arena.instantiateListFast]
theorem instList_refines (p : Prog) (hp : InstListProg p)
    (hpe : p.lookup "inst_list" = some instListL) (n : Nat) (s₀ : St) (a₀ : AState)
    (hA : ArenaL s₀.mem a₀) (e o l d : Word) (vs : Array EIdx) (hsl : SpineR s₀.mem o l vs)
    (hbd : o.toNat + l.toNat < 2 ^ 64) (he : e.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "inst_list" [e, o, l, d]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (instantiateListFast coreWalkFuel (decE e) vs d.toNat) a₀ ∧
      ArenaL s'.mem (AM.st (instantiateListFast coreWalkFuel (decE e) vs d.toNat) a₀) ∧
      AM.res (instantiateListFast coreWalkFuel (decE e) vs d.toNat) a₀ = decE (r.headD 0) ∧
      s'.mem.arr64 ILSPN = s₀.mem.arr64 ILSPN ∧ (r.headD 0).toNat < 2 ^ 32; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun (instList_spec' p hp hpe n s₀ e o l d)
  subst hs
  obtain ⟨a', ha', hA', hs', hlt⟩ := instListW_correct n _ _ a₀ hA e o l d _ vs hsl hbd he hI
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ ha'
  exact ⟨hloc, hok, hst ▸ hA', hres, hs', hlt⟩

/-- **`inst_list(e, o₀ + s, i - s, d)` refines `instantiateRevRange coreWalkFuel e vs s i`**: the
range `vs[s:i]` of the stack slice `(o₀, C)`, read in place (`beta_peel`'s substitution). -/
@[refines ConRon.Arena.instantiateRevRange]
theorem instList_refines_range (p : Prog) (hp : InstListProg p)
    (hpe : p.lookup "inst_list" = some instListL) (n : Nat) (s₀ : St) (a₀ : AState)
    (hA : ArenaL s₀.mem a₀) (e o₀ C d : Word) (vs : Array EIdx) (hsl : SpineR s₀.mem o₀ C vs)
    (hbd : o₀.toNat + C.toNat < 2 ^ 64) (s i : Nat) (hs : s ≤ i) (hi : i ≤ C.toNat)
    (he : e.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "inst_list" [e, o₀ + s.toUInt64, (i - s).toUInt64, d]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (instantiateRevRange coreWalkFuel (decE e) vs s i d.toNat) a₀ ∧
      ArenaL s'.mem (AM.st (instantiateRevRange coreWalkFuel (decE e) vs s i d.toNat) a₀) ∧
      AM.res (instantiateRevRange coreWalkFuel (decE e) vs s i d.toNat) a₀ = decE (r.headD 0) ∧
      s'.mem.arr64 ILSPN = s₀.mem.arr64 ILSPN ∧ (r.headD 0).toNat < 2 ^ 32; ⊤⦄ := by
  apply M.triple_of_run
  intro s' r s'' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (instList_spec' p hp hpe n s₀ e (o₀ + s.toUInt64) (i - s).toUInt64 d)
  subst hs
  obtain ⟨a', ha', hA', hs', hlt⟩ := instListW_revRange n _ _ a₀ hA e o₀ C d _ vs hsl hbd s i hs hi he hI
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ ha'
  exact ⟨hloc, hok, hst ▸ hA', hres, hs', hlt⟩

end L.Arena
