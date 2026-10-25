import ConAgua.Arena.InstListSpec
import ConAgua.Arena.Abs1Refine
import ConAgua.Arena.WhnfBase
import ConAgua.Arena.SimLib
import ConAgua.Census.Attr

/-!
# `inst_list` refines the arena's `instantiateListFast`

`Inst1Refine.lean`'s proof, twice (the pure walk `instantiateList`, the memo walk
`instantiateListGo`), with:

* **The memo tier `ArenaL := ArenaD ∧ ILR`** (`instLC` on array 50), `Abs1Refine.lean`'s `ArenaA`
  pattern: the stores keep it by their frames (`mk*W_frameA`), the twin's interning by `Keeps`.
* **The substitution as a stack slice** (`SpineR`, `WhnfBase.lean`): every statement carries
  `SpineR m o l vs` and the bound `o + l < 2^64`, and every model step leaves the stack array
  alone (`m'.arr64 ILSPN = m.arr64 ILSPN`, in each post), so the slice survives the children.
  The `bvar` arm's recursion goes to the slice's last `q` entries, `SpineR` of `lastEidx vs q`
  (`spineR_last`).
-/

open ConRon.Arena ConLeche
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

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
  ⟨hD.1.with_memos (MemFrame.refl [] [] m) (by simp) (by simp)
    ⟨hD.1.memos.bvar, hD.1.memos.lift, hD.1.memos.inst1, hD.1.memos.fvar⟩,
    DerR.of_store m a _ hD.2 rfl⟩

theorem ArenaL.lmemo_set (m m' : Mem) (a : AState) (hA : ArenaL m a) (h c v : Word)
    (hh : h.toNat < 2 ^ 32) (hs : msetG ilSch m h c v = some m') :
    ArenaL m' (withLLC a (a.memos.instLC.insert (decE h, c.toNat) (decE v))) := by
  have hf := msetG_frame ilSch ilSch_wf m m' h c v hs
  refine ⟨ArenaD.withLLC ⟨hA.1.1.frame (by decide) (by simpa using not_arenaCtl_51) hf,
    DerR.frameM _ _ m m' hf (by decide) _ hA.1.2⟩ _, ?_⟩
  exact memoRG_set ilSch ilSch_wf lfKey decE m _ hA.2 h c v hh m' hs

theorem ArenaL.lmemo_clear (m : Mem) (a : AState) (hA : ArenaL m a)
    (h0 : rdW (m.arr64 CTL) 50 + 2 ≠ 0) : ArenaL (mclearG ilSch m) (withLLC a ∅) := by
  have hf := mclearG_frame ilSch m
  have hC : ∀ x ∈ [ilSch.cs, ilSch.cs + 1], x ∉ arenaCtl := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact not_arenaCtl_50
    · exact not_arenaCtl_51
  exact ⟨ArenaD.withLLC ⟨hA.1.1.frame (by decide) hC hf, DerR.frameM _ _ m _ hf (by decide) _ hA.1.2⟩ _,
    memoRG_clear ilSch ilSch_wf lfKey decE m _ hA.2 h0⟩

/-- **`ILR` survives a writer apart from it, if the twin's memo did not move.** -/
theorem ILR.across {A : List ArrId} {C : List Word} {m m' : Mem} {a a' : AState}
    (hR : ILR m a) (hf : MemFrame A C m m') (hA : ILMEMO ∉ A) (hC : (50 : Word) ∉ C)
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
theorem spn_of_frame {A : List ArrId} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : ILSPN ∉ A) : m'.arr64 ILSPN = m.arr64 ILSPN := hf.1 ILSPN hA (by decide)

/-! ## The `mk_*` and `intern_bvar` under `ArenaL` -/

theorem mkApp_okL (m : Mem) (a : AState) (hA : ArenaL m a) (f x r : Word) (m' : Mem)
    (hI : mkAppW m f x = some (r, m')) :
    AM.ok (internE (.app (decE f) (decE x))) a ∧
    ArenaL m' (AM.st (internE (.app (decE f) (decE x))) a) ∧
    AM.res (internE (.app (decE f) (decE x))) a = decE r ∧ m'.arr64 ILSPN = m.arr64 ILSPN := by
  obtain ⟨hok, hD, hres⟩ := mkApp_ok m a hA.1 f x r m' hI
  have hf := mkAppW_frameA m m' f x r hI
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

theorem SpineR.of_spn {m m' : Mem} {o l : Word} {xs : Array EIdx} (hx : SpineR m o l xs)
    (he : m'.arr64 ILSPN = m.arr64 ILSPN) : SpineR m' o l xs where
  size := hx.size
  bound := by rw [show SPN = ILSPN from rfl, he]; exact hx.bound
  lt := fun i hi => by rw [spW, show SPN = ILSPN from rfl, he]; exact hx.lt i hi
  get := fun i hi => by rw [hx.get i hi, spW, spW, show SPN = ILSPN from rfl, he]

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

theorem lastEidx_toList (xs : Array EIdx) (k : Nat) (hk : k < xs.size) :
    (lastEidx xs k).toList = xs.toList.drop (xs.size - k) := by
  simp only [lastEidx, hk, ↓reduceIte]
  rw [eidxCopyUpto_toList xs _ _ #[] (Nat.le_refl _)]; simp

theorem lastEidx_size (xs : Array EIdx) (k : Nat) (hk : k < xs.size) : (lastEidx xs k).size = k := by
  have := congrArg List.length (lastEidx_toList xs k hk)
  simp at this; omega

theorem lastEidx_get (xs : Array EIdx) (k : Nat) (hk : k < xs.size) (i : Nat) (hi : i < (lastEidx xs k).size) :
    (lastEidx xs k)[i] = xs[xs.size - k + i]'(by rw [lastEidx_size xs k hk] at hi; omega) := by
  have e := lastEidx_toList xs k hk
  rw [← Array.getElem_toList, ← Array.getElem_toList]
  simp only [e, List.getElem_drop]

theorem slice_word (o l q : Word) (i : Nat) (hb : o.toNat + l.toNat < 2 ^ 64) (hq : q < l)
    (hi : i < q.toNat) :
    o + (l - q) + i.toUInt64 = o + (l.toNat - q.toNat + i).toUInt64 := by
  have hq' : q.toNat < l.toNat := hq
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hq)]
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
  have := q.toNat_lt
  omega

/-- **The slice's last `q` entries** are `lastEidx vs q`. -/
theorem spineR_last {m : Mem} {o l q : Word} {vs : Array EIdx} (hx : SpineR m o l vs)
    (hb : o.toNat + l.toNat < 2 ^ 64) (hq : q < l) :
    SpineR m (o + (l - q)) q (lastEidx vs q.toNat) ∧ (o + (l - q)).toNat + q.toNat < 2 ^ 64 := by
  have hq' : q.toNat < l.toNat := hq
  have hs : q.toNat < vs.size := by rw [hx.size]; exact hq'
  have ho : (o + (l - q)).toNat = o.toNat + (l.toNat - q.toNat) := by
    rw [UInt64.toNat_add, UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hq)]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨⟨lastEidx_size vs _ hs, ?_, fun i hi => ?_, fun i hi => ?_⟩, by omega⟩
  · rw [ho]; have := hx.bound; omega
  · rw [slice_word o l q i hb hq hi]; exact hx.lt _ (by omega)
  · have hi' : i < q.toNat := by rw [lastEidx_size vs _ hs] at hi; exact hi
    rw [lastEidx_get vs _ hs i hi, hx.get, slice_word o l q i hb hq hi', hx.size]

theorem spineR_entry {m : Mem} {o l q : Word} {vs : Array EIdx} (hx : SpineR m o l vs)
    (hb : o.toNat + l.toNat < 2 ^ 64) (hq : q < l) :
    ∃ hlt : vs.size - 1 - q.toNat < vs.size,
      vs[vs.size - 1 - q.toNat] = decE (slW m (o + (l - 1 - q))) ∧
      (slW m (o + (l - 1 - q))).toNat < 2 ^ 32 := by
  have hq' : q.toNat < l.toNat := hq
  have hs : vs.size = l.toNat := hx.size
  have hw : o + (l - 1 - q) = o + (vs.size - 1 - q.toNat).toUInt64 := by
    apply UInt64.toNat_inj.mp
    have h1 : (1 : Word) ≤ l := by
      rw [UInt64.le_iff_toNat_le]; simp; omega
    have h2 : q ≤ l - 1 := by
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ h1]; simp; omega
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_sub_of_le _ _ h2,
      UInt64.toNat_sub_of_le _ _ h1]
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', UInt64.toNat_one]
    rw [hs]; omega
  refine ⟨by omega, ?_, ?_⟩
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
  ∀ (m m' : Mem) (a : AState) (h d o l fu r : Word) (vs : Array EIdx),
    ArenaL m a → SpineR m o l vs → o.toNat + l.toNat < 2 ^ 64 → h.toNat < 2 ^ 32 →
    ilW n m h d o l fu = some (r, m') →
    ∃ a', (instantiateList vs fu.toNat (decE h) d.toNat).run a = .ok (decE r, a') ∧ ArenaL m' a' ∧
      m'.arr64 ILSPN = m.arr64 ILSPN

/-- The same for `ilg_go`'s model and `instantiateListGo vs`. -/
def ILGGoOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (h d o l fu r : Word) (vs : Array EIdx),
    ArenaL m a → SpineR m o l vs → o.toNat + l.toNat < 2 ^ 64 → h.toNat < 2 ^ 32 →
    ilgW n m h d o l fu = some (r, m') →
    ∃ a', (instantiateListGo vs fu.toNat (decE h) d.toNat).run a = .ok (decE r, a') ∧ ArenaL m' a' ∧
      m'.arr64 ILSPN = m.arr64 ILSPN

/-- The arena arm `arm` refines the L arm `armW` at `h`, under `ArenaL`, keeping the stack. -/
def LArmRef (n : Nat) (armW : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem))
    (arm : AM EIdx) (m m' : Mem) (a : AState) (h d o l fu r : Word) : Prop :=
  armW n m h d o l fu = some (r, m') →
    ∃ a', arm.run a = .ok (decE r, a') ∧ ArenaL m' a' ∧ m'.arr64 ILSPN = m.arr64 ILSPN

/-- The pure walk's six arms, each at its tag. -/
def ILArmOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (h d o l fu r : Word) (vs : Array EIdx),
    ArenaL m a → SpineR m o l vs → o.toNat + l.toNat < 2 ^ 64 → h.toNat < 2 ^ 32 →
    (h >>> 28 = 4 → LArmRef n ilAppW (instListArmApp vs fu.toNat (decE h) d.toNat) m m' a h d o l fu r) ∧
    (h >>> 28 = 5 → LArmRef n ilLamW (instListArmBind vs fu.toNat (decE h) d.toNat) m m' a h d o l fu r) ∧
    (h >>> 28 = 6 → LArmRef n ilForallW (instListArmBind vs fu.toNat (decE h) d.toNat) m m' a h d o l fu r) ∧
    (h >>> 28 = 7 → LArmRef n ilLetW (instListArmLet vs fu.toNat (decE h) d.toNat) m m' a h d o l fu r) ∧
    (h >>> 28 = 9 → LArmRef n ilProjW (instListArmProj vs fu.toNat (decE h) d.toNat) m m' a h d o l fu r) ∧
    (h >>> 28 = 0 → LArmRef n ilBVarW (instListArmBVar vs fu.toNat (decE h) d.toNat) m m' a h d o l fu r)

/-- The memo walk's five arms, each at its tag. -/
def ILGArmOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (h d o l fu r : Word) (vs : Array EIdx),
    ArenaL m a → SpineR m o l vs → o.toNat + l.toNat < 2 ^ 64 → h.toNat < 2 ^ 32 →
    (h >>> 28 = 4 → LArmRef n ilgAppW (instListGoArmApp vs fu.toNat (decE h) d.toNat) m m' a h d o l fu r) ∧
    (h >>> 28 = 5 → LArmRef n ilgLamW (instListGoArmBind vs fu.toNat (decE h) d.toNat) m m' a h d o l fu r) ∧
    (h >>> 28 = 6 →
      LArmRef n ilgForallW (instListGoArmBind vs fu.toNat (decE h) d.toNat) m m' a h d o l fu r) ∧
    (h >>> 28 = 7 → LArmRef n ilgLetW (instListGoArmLet vs fu.toNat (decE h) d.toNat) m m' a h d o l fu r) ∧
    (h >>> 28 = 9 → LArmRef n ilgProjW (instListGoArmProj vs fu.toNat (decE h) d.toNat) m m' a h d o l fu r)

/-! ## The dispatchers -/

theorem ilgoOK_succ (n : Nat) (ih : ILArmOK n) : ILGoOK (n + 1) := by
  intro m m' a h d o l fu r vs hA hsl hbd hh hb
  have hfu : ¬ fu = 0 := fun hfu => by rw [ilW] at hb; simp [hfu] at hb
  rw [ctrW_toNat fu hfu, instantiateList_succ, StateT.run_bind, instListCutoff_run]
  simp only [except_ok_bind]
  by_cases hcut : ilCut m h d
  · rw [ilW_cut n m h d o l fu hfu hcut] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    rw [ilcut_iff m a hA h d hh] at hcut
    simp only [hcut, ↓reduceIte]
    exact ⟨a, rfl, hA, by simp⟩
  have hcut' := hcut
  rw [ilcut_iff m a hA h d hh] at hcut'
  simp only [Bool.not_eq_true] at hcut'
  simp only [hcut', Bool.false_eq_true, ↓reduceIte, decE_tag h hh]
  have arm := ih m m' a h d o l (fu - 1) r vs hA hsl hbd hh
  have t4 : h >>> 28 = 4 ↔ (h >>> 28).toUInt32 = 4 := by simpa using tag_iff h 4 hh (by decide)
  have t5 : h >>> 28 = 5 ↔ (h >>> 28).toUInt32 = 5 := by simpa using tag_iff h 5 hh (by decide)
  have t6 : h >>> 28 = 6 ↔ (h >>> 28).toUInt32 = 6 := by simpa using tag_iff h 6 hh (by decide)
  have t0 : h >>> 28 = 0 ↔ (h >>> 28).toUInt32 = 0 := by simpa using tag_iff h 0 hh (by decide)
  have t7 : h >>> 28 = 7 ↔ (h >>> 28).toUInt32 = 7 := by simpa using tag_iff h 7 hh (by decide)
  have t9 : h >>> 28 = 9 ↔ (h >>> 28).toUInt32 = 9 := by simpa using tag_iff h 9 hh (by decide)
  simp only [ETag.app, ETag.isBind, ETag.lam, ETag.forallE, ETag.bvar, ETag.letE, ETag.proj,
    beq_iff_eq, Bool.or_eq_true] at *
  by_cases g4 : h >>> 28 = 4
  · rw [ilW_app n m h d o l fu hfu hcut g4] at hb
    simp only [show (h >>> 28).toUInt32 = 4 from (t4.mp g4), ↓reduceIte]
    exact arm.1 g4 hb
  have g4' : ¬ (h >>> 28).toUInt32 = 4 := fun e => g4 (t4.mpr e)
  by_cases g5 : h >>> 28 = 5
  · rw [ilW_lam n m h d o l fu hfu hcut g5] at hb
    simp only [g4', show (h >>> 28).toUInt32 = 5 from (t5.mp g5), true_or, ↓reduceIte]
    exact arm.2.1 g5 hb
  have g5' : ¬ (h >>> 28).toUInt32 = 5 := fun e => g5 (t5.mpr e)
  by_cases g6 : h >>> 28 = 6
  · rw [ilW_forall n m h d o l fu hfu hcut g6] at hb
    simp only [g4', g5', show (h >>> 28).toUInt32 = 6 from (t6.mp g6), or_true, ↓reduceIte]
    exact arm.2.2.1 g6 hb
  have g6' : ¬ (h >>> 28).toUInt32 = 6 := fun e => g6 (t6.mpr e)
  simp only [g4', g5', g6', or_self, ↓reduceIte]
  by_cases g7 : h >>> 28 = 7
  · rw [ilW_let n m h d o l fu hfu hcut g7] at hb
    simp only [show (h >>> 28).toUInt32 = 7 from (t7.mp g7), ↓reduceIte]
    exact arm.2.2.2.1 g7 hb
  have g7' : ¬ (h >>> 28).toUInt32 = 7 := fun e => g7 (t7.mpr e)
  simp only [g7', ↓reduceIte]
  by_cases g9 : h >>> 28 = 9
  · rw [ilW_proj n m h d o l fu hfu hcut g9] at hb
    simp only [show (h >>> 28).toUInt32 = 9 from (t9.mp g9), ↓reduceIte]
    exact arm.2.2.2.2.1 g9 hb
  have g9' : ¬ (h >>> 28).toUInt32 = 9 := fun e => g9 (t9.mpr e)
  simp only [g9', ↓reduceIte]
  by_cases g0 : h >>> 28 = 0
  · rw [ilW_bvar n m h d o l fu hfu hcut g0] at hb
    simp only [show (h >>> 28).toUInt32 = 0 from (t0.mp g0), ↓reduceIte]
    exact arm.2.2.2.2.2 g0 hb
  have g0' : ¬ (h >>> 28).toUInt32 = 0 := fun e => g0 (t0.mpr e)
  simp only [g0', ↓reduceIte]
  rw [ilW_leaf n m h d o l fu hfu hcut g0 g4 g5 g6 g7 g9] at hb
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
  exact ⟨a, rfl, hA, by simp⟩

theorem ilggoOK_succ (n : Nat) (ih : ILGArmOK n) (ihl : ILGoOK n) : ILGGoOK (n + 1) := by
  intro m m' a h d o l fu r vs hA hsl hbd hh hb
  have hfu : ¬ fu = 0 := fun hfu => by rw [ilgW] at hb; simp [hfu] at hb
  rw [ctrW_toNat fu hfu, instantiateListGo_succ, StateT.run_bind, instListCutoff_run]
  simp only [except_ok_bind]
  by_cases hcut : ilCut m h d
  · rw [ilgW_cut n m h d o l fu hfu hcut] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    rw [ilcut_iff m a hA h d hh] at hcut
    simp only [hcut, ↓reduceIte]
    exact ⟨a, rfl, hA, by simp⟩
  have hcut' := hcut
  rw [ilcut_iff m a hA h d hh] at hcut'
  simp only [Bool.not_eq_true] at hcut'
  simp only [hcut', Bool.false_eq_true, ↓reduceIte, decE_tag h hh]
  have arm := ih m m' a h d o l (fu - 1) r vs hA hsl hbd hh
  have t4 : h >>> 28 = 4 ↔ (h >>> 28).toUInt32 = 4 := by simpa using tag_iff h 4 hh (by decide)
  have t5 : h >>> 28 = 5 ↔ (h >>> 28).toUInt32 = 5 := by simpa using tag_iff h 5 hh (by decide)
  have t6 : h >>> 28 = 6 ↔ (h >>> 28).toUInt32 = 6 := by simpa using tag_iff h 6 hh (by decide)
  have t0 : h >>> 28 = 0 ↔ (h >>> 28).toUInt32 = 0 := by simpa using tag_iff h 0 hh (by decide)
  have t7 : h >>> 28 = 7 ↔ (h >>> 28).toUInt32 = 7 := by simpa using tag_iff h 7 hh (by decide)
  have t9 : h >>> 28 = 9 ↔ (h >>> 28).toUInt32 = 9 := by simpa using tag_iff h 9 hh (by decide)
  simp only [ETag.app, ETag.isBind, ETag.lam, ETag.forallE, ETag.bvar, ETag.letE, ETag.proj,
    beq_iff_eq, Bool.or_eq_true] at *
  by_cases g4 : h >>> 28 = 4
  · rw [ilgW_app n m h d o l fu hfu hcut g4] at hb
    simp only [show (h >>> 28).toUInt32 = 4 from (t4.mp g4), ↓reduceIte]
    exact arm.1 g4 hb
  have g4' : ¬ (h >>> 28).toUInt32 = 4 := fun e => g4 (t4.mpr e)
  by_cases g5 : h >>> 28 = 5
  · rw [ilgW_lam n m h d o l fu hfu hcut g5] at hb
    simp only [g4', show (h >>> 28).toUInt32 = 5 from (t5.mp g5), true_or, ↓reduceIte]
    exact arm.2.1 g5 hb
  have g5' : ¬ (h >>> 28).toUInt32 = 5 := fun e => g5 (t5.mpr e)
  by_cases g6 : h >>> 28 = 6
  · rw [ilgW_forall n m h d o l fu hfu hcut g6] at hb
    simp only [g4', g5', show (h >>> 28).toUInt32 = 6 from (t6.mp g6), or_true, ↓reduceIte]
    exact arm.2.2.1 g6 hb
  have g6' : ¬ (h >>> 28).toUInt32 = 6 := fun e => g6 (t6.mpr e)
  simp only [g4', g5', g6', or_self, ↓reduceIte]
  by_cases g7 : h >>> 28 = 7
  · rw [ilgW_let n m h d o l fu hfu hcut g7] at hb
    simp only [show (h >>> 28).toUInt32 = 7 from (t7.mp g7), ↓reduceIte]
    exact arm.2.2.2.1 g7 hb
  have g7' : ¬ (h >>> 28).toUInt32 = 7 := fun e => g7 (t7.mpr e)
  simp only [g7', ↓reduceIte]
  by_cases g9 : h >>> 28 = 9
  · rw [ilgW_proj n m h d o l fu hfu hcut g9] at hb
    simp only [show (h >>> 28).toUInt32 = 9 from (t9.mp g9), ↓reduceIte]
    exact arm.2.2.2.2 g9 hb
  have g9' : ¬ (h >>> 28).toUInt32 = 9 := fun e => g9 (t9.mpr e)
  simp only [g9', ↓reduceIte]
  by_cases g0 : h >>> 28 = 0
  · rw [ilgW_bvar n m h d o l fu hfu hcut g0] at hb
    simp only [show (h >>> 28).toUInt32 = 0 from (t0.mp g0), ↓reduceIte]
    exact ihl m m' a h d o l (fu - 1) r vs hA hsl hbd hh hb
  have g0' : ¬ (h >>> 28).toUInt32 = 0 := fun e => g0 (t0.mpr e)
  simp only [g0', ↓reduceIte]
  rw [ilgW_leaf n m h d o l fu hfu hcut g0 g4 g5 g6 g7 g9] at hb
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
  exact ⟨a, rfl, hA, by simp⟩

/-! ## The pure walk's arms -/

section arms
variable (n : Nat) (ih : ILGoOK n) (m m' : Mem) (a : AState) (hA : ArenaL m a)
  (h d o l fu r : Word) (vs : Array EIdx) (hsl : SpineR m o l vs) (hbd : o.toNat + l.toNat < 2 ^ 64)
  (hh : h.toNat < 2 ^ 32)
include ih hA hsl hbd hh

theorem lappArm_ok (hg : h >>> 28 = 4) :
    LArmRef (n + 1) ilAppW (instListArmApp vs fu.toNat (decE h) d.toNat) m m' a h d o l fu r := by
  intro hb
  rw [instListArmApp]
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [ilAppW] at hb; simp only [ne_eq] at hs; simp only [hs, ne_eq, not_false_eq_true, and_self, ↓reduceIte, reduceCtorEq] at hb
  have hv : viewOK m h APP := ⟨hs, UInt64.not_le.mp fun hc => by
    rw [ilAppW] at hb; simp only [ne_eq] at hs; simp only [hs, hc, ↓reduceIte, reduceCtorEq] at hb⟩
  obtain ⟨-, hfw, haw⟩ := view_app m a hA.1.1 h hh hv hg
  rw [ilAppW_miss n m h d o l fu hv] at hb
  rw [StateT.run_bind, viewApp_run, viewApp_ok m a hA.1.1 h hh hv, except_ok_bind]
  dsimp only
  refine SimD.exists (R := SpnR m) (Sim.bindD rfl (fun _ _ => rfl)
    (Sim.ofD fun x m₁ e => ih m m₁ a _ d o l fu x vs hA hsl hbd hfw e) fun x m₁ a₁ hR => ?_) hb
  obtain ⟨hA₁, hs₁⟩ := hR
  refine Sim.bindD (K := lappK₁.lappK₂ x) rfl (fun _ _ => rfl)
    (Sim.ofD fun y m₂ e => ih m₁ m₂ a₁ _ d o l fu y vs hA₁ (hsl.of_spn hs₁) hbd haw e)
        fun y m₂ a₂ hR => ?_
  obtain ⟨hA₂, hs₂⟩ := hR
  refine Sim.ofOk fun r m' hb => ?_
  obtain ⟨hok, hA₃, hres, hs₃⟩ := mkApp_okL m₂ a₂ hA₂ x y r m' hb
  simp only [internAppE]
  exact ⟨hok, hres, hA₃, hs₃.trans (hs₂.trans hs₁)⟩

theorem llamArm_ok (hg : h >>> 28 = 5) :
    LArmRef (n + 1) ilLamW (instListArmBind vs fu.toNat (decE h) d.toNat) m m' a h d o l fu r := by
  intro hb
  have hd1 : ¬ d + 1 = 0 := fun hd1 => by rw [ilLamW] at hb; simp [hd1] at hb
  rw [instListArmBind]
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [ilLamW] at hb; simp only [ne_eq] at hs; simp only [hd1, hs, ne_eq, not_false_eq_true, and_self, ↓reduceIte, reduceCtorEq] at hb
  have hv : viewOK m h LAM := ⟨hs, UInt64.not_le.mp fun hc => by
    rw [ilLamW] at hb; simp only [ne_eq] at hs; simp only [hd1, hs, hc, ↓reduceIte, reduceCtorEq] at hb⟩
  obtain ⟨-, hfw, haw⟩ := view_lam m a hA.1.1 h hh hv hg
  rw [ilLamW_miss n m h d o l fu hd1 hv] at hb
  rw [StateT.run_bind, viewBind_run, viewBind_lam m a hA.1.1 h hh hv hg, except_ok_bind]
  dsimp only
  refine SimD.exists (R := SpnR m) (Sim.bindD rfl (fun _ _ => rfl)
    (Sim.ofD fun x m₁ e => ih m m₁ a _ d o l fu x vs hA hsl hbd hfw e) fun x m₁ a₁ hR => ?_) hb
  obtain ⟨hA₁, hs₁⟩ := hR
  refine Sim.bindD (K := llamK₁.llamK₂ x) rfl (fun _ _ => rfl)
    (Sim.ofD fun y m₂ e => by
      simpa only [succW_toNat d hd1] using ih m₁ m₂ a₁ _ (d + 1) o l fu y vs hA₁
          (hsl.of_spn hs₁) hbd haw e) fun y m₂ a₂ hR => ?_
  obtain ⟨hA₂, hs₂⟩ := hR
  have hbind : ∀ t b, internBindE (decE h).tag t b = internE (.lam t b) := by
    intro t b; simp [internBindE, decE_tag h hh, hg, ETag.lam, internE]
  refine Sim.ofOk fun r m' hb => ?_
  obtain ⟨hok, hA₃, hres, hs₃⟩ := mkLam_okL m₂ a₂ hA₂ x y r m' hb
  simp only [hbind]
  exact ⟨hok, hres, hA₃, hs₃.trans (hs₂.trans hs₁)⟩

theorem lforallArm_ok (hg : h >>> 28 = 6) :
    LArmRef (n + 1) ilForallW (instListArmBind vs fu.toNat (decE h) d.toNat) m m' a h d o l fu r := by
  intro hb
  have hd1 : ¬ d + 1 = 0 := fun hd1 => by rw [ilForallW] at hb; simp [hd1] at hb
  rw [instListArmBind]
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [ilForallW] at hb; simp only [ne_eq] at hs; simp only [hd1, hs, ne_eq, not_false_eq_true, and_self, ↓reduceIte, reduceCtorEq] at hb
  have hv : viewOK m h FORALL := ⟨hs, UInt64.not_le.mp fun hc => by
    rw [ilForallW] at hb; simp only [ne_eq] at hs; simp only [hd1, hs, hc, ↓reduceIte, reduceCtorEq] at hb⟩
  obtain ⟨-, hfw, haw⟩ := view_forall m a hA.1.1 h hh hv hg
  rw [ilForallW_miss n m h d o l fu hd1 hv] at hb
  rw [StateT.run_bind, viewBind_run, viewBind_forall m a hA.1.1 h hh hv hg, except_ok_bind]
  dsimp only
  refine SimD.exists (R := SpnR m) (Sim.bindD rfl (fun _ _ => rfl)
    (Sim.ofD fun x m₁ e => ih m m₁ a _ d o l fu x vs hA hsl hbd hfw e) fun x m₁ a₁ hR => ?_) hb
  obtain ⟨hA₁, hs₁⟩ := hR
  refine Sim.bindD (K := lfaK₁.lfaK₂ x) rfl (fun _ _ => rfl)
    (Sim.ofD fun y m₂ e => by
      simpa only [succW_toNat d hd1] using ih m₁ m₂ a₁ _ (d + 1) o l fu y vs hA₁
          (hsl.of_spn hs₁) hbd haw e) fun y m₂ a₂ hR => ?_
  obtain ⟨hA₂, hs₂⟩ := hR
  have hbind : ∀ t b, internBindE (decE h).tag t b = internE (.forallE t b) := by
    intro t b; simp [internBindE, decE_tag h hh, hg, ETag.lam, internE]
  refine Sim.ofOk fun r m' hb => ?_
  obtain ⟨hok, hA₃, hres, hs₃⟩ := mkForall_okL m₂ a₂ hA₂ x y r m' hb
  simp only [hbind]
  exact ⟨hok, hres, hA₃, hs₃.trans (hs₂.trans hs₁)⟩

theorem lletArm_ok (hg : h >>> 28 = 7) :
    LArmRef (n + 1) ilLetW (instListArmLet vs fu.toNat (decE h) d.toNat) m m' a h d o l fu r := by
  intro hb
  have hd1 : ¬ d + 1 = 0 := fun hd1 => by rw [ilLetW] at hb; simp [hd1] at hb
  rw [instListArmLet]
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [ilLetW] at hb; simp only [ne_eq] at hs; simp only [hd1, hs, ne_eq, not_false_eq_true, and_self, ↓reduceIte, reduceCtorEq] at hb
  have hv : viewOK m h LET := ⟨hs, UInt64.not_le.mp fun hc => by
    rw [ilLetW] at hb; simp only [ne_eq] at hs; simp only [hd1, hs, hc, ↓reduceIte, reduceCtorEq] at hb⟩
  obtain ⟨-, htw, hvw, hbw⟩ := view_let m a hA.1.1 h hh hv hg
  rw [ilLetW_miss n m h d o l fu hd1 hv] at hb
  rw [StateT.run_bind, viewLet_run, viewLet_ok m a hA.1.1 h hh hv, except_ok_bind]
  dsimp only
  refine SimD.exists (R := SpnR m) (Sim.bindD rfl (fun _ _ => rfl)
    (Sim.ofD fun x m₁ e => ih m m₁ a _ d o l fu x vs hA hsl hbd htw e) fun x m₁ a₁ hR => ?_) hb
  obtain ⟨hA₁, hs₁⟩ := hR
  refine Sim.bindD (K := lleK₁.lleK₂ n d o l fu _ x) rfl (fun _ _ => rfl)
    (Sim.ofD fun y m₂ e => ih m₁ m₂ a₁ _ d o l fu y vs hA₁ (hsl.of_spn hs₁) hbd hvw e)
        fun y m₂ a₂ hR => ?_
  obtain ⟨hA₂, hs₂⟩ := hR
  refine Sim.bindD (K := lleK₁.lleK₃ x y) rfl (fun _ _ => rfl)
    (Sim.ofD fun z m₃ e => by
      simpa only [succW_toNat d hd1] using ih m₂ m₃ a₂ _ (d + 1) o l fu z vs hA₂
          ((hsl.of_spn hs₁).of_spn hs₂) hbd hbw e) fun z m₃ a₃ hR => ?_
  obtain ⟨hA₃, hs₃⟩ := hR
  refine Sim.ofOk fun r m' hb => ?_
  obtain ⟨hok, hA₄, hres, hs₄⟩ := mkLet_okL m₃ a₃ hA₃ x y z r m' hb
  simp only [internLetEE]
  exact ⟨hok, hres, hA₄, hs₄.trans (hs₃.trans (hs₂.trans hs₁))⟩

theorem lprojArm_ok (hg : h >>> 28 = 9) :
    LArmRef (n + 1) ilProjW (instListArmProj vs fu.toNat (decE h) d.toNat) m m' a h d o l fu r := by
  intro hb
  rw [instListArmProj]
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [ilProjW] at hb; simp only [ne_eq] at hs; simp only [hs, ne_eq, not_false_eq_true, and_self, ↓reduceIte, reduceCtorEq] at hb
  have hv : viewOK m h PROJ := ⟨hs, UInt64.not_le.mp fun hc => by
    rw [ilProjW] at hb; simp only [ne_eq] at hs; simp only [hs, hc, ↓reduceIte, reduceCtorEq] at hb⟩
  obtain ⟨-, -, hew⟩ := view_proj m a hA.1.1 h hh hv hg
  rw [ilProjW_miss n m h d o l fu hv] at hb
  rw [StateT.run_bind, viewProj_run, viewProj_ok m a hA.1.1 h hh hv, except_ok_bind]
  dsimp only
  refine SimD.exists (R := SpnR m) (Sim.bindD rfl (fun _ _ => rfl)
    (Sim.ofD fun x m₁ e => ih m m₁ a _ d o l fu x vs hA hsl hbd hew e) fun x m₁ a₁ hR => ?_) hb
  obtain ⟨hA₁, hs₁⟩ := hR
  refine Sim.ofOk fun r m' hb => ?_
  obtain ⟨hok, hA₂, hres, hs₂⟩ := mkProj_okL m₁ a₁ hA₁ _ _ x r m' hb
  simp only [internProjE]
  exact ⟨hok, hres, hA₂, hs₂.trans hs₁⟩

theorem lbvarArm_ok (hg : h >>> 28 = 0) :
    LArmRef (n + 1) ilBVarW (instListArmBVar vs fu.toNat (decE h) d.toNat) m m' a h d o l fu r := by
  intro hb
  rw [instListArmBVar]
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [ilBVarW] at hb; simp only [ne_eq] at hs; simp only [hs, ne_eq, not_false_eq_true, and_self, ↓reduceIte, reduceCtorEq] at hb
  have hv : viewOK m h BVAR := ⟨hs, UInt64.not_le.mp fun hc => by
    rw [ilBVarW] at hb; simp only [ne_eq] at hs; simp only [hs, hc, ↓reduceIte, reduceCtorEq] at hb⟩
  rw [StateT.run_bind, viewBVar_run, viewBVar_ok m a hA.1.1 h hh hv, except_ok_bind]
  simp only
  generalize hJ : tfld m BVAR (tierW h) (idxW h) 0 = J at hb ⊢
  by_cases hj : J < d
  · rw [ilBVarW_lt n m h d o l fu hv (hJ ▸ hj)] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    rw [if_pos (UInt64.lt_iff_toNat_lt.mp hj)]
    exact ⟨a, rfl, hA, by simp⟩
  have hj' : ¬ J.toNat < d.toNat := fun e => hj (UInt64.lt_iff_toNat_lt.mpr e)
  rw [if_neg hj']
  have hdJ : d ≤ J := UInt64.not_lt.mp hj
  have hsub : (J - d).toNat = J.toNat - d.toNat := UInt64.toNat_sub_of_le _ _ hdJ
  by_cases hq : J - d < l
  · rw [ilBVarW_in n m h d o l fu hv (hJ ▸ hj) (hJ ▸ hq)] at hb
    rw [hJ] at hb
    have hq' : J.toNat - d.toNat < vs.size := by
      rw [hsl.size, ← hsub]; exact hq
    rw [dif_pos hq']
    obtain ⟨hlt, hvi, hvl⟩ := spineR_entry hsl hbd hq
    simp only [hsub] at hvi hlt
    simp only [hvi]
    rw [StateT.run_bind, instListCutoff_run, except_ok_bind]
    by_cases hcv : ilCut m (slW m (o + (l - 1 - (J - d)))) d
    · rw [ilVW_cut n m _ d _ _ fu hcv] at hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      rw [ilcut_iff m a hA _ d hvl] at hcv
      simp only [hcv, ↓reduceIte]
      exact ⟨a, rfl, hA, by simp⟩
    · rw [ilVW_go n m _ d _ _ fu hcv] at hb
      rw [ilcut_iff m a hA _ d hvl] at hcv
      simp only [Bool.not_eq_true] at hcv
      simp only [hcv, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨hsl', hbd'⟩ := spineR_last hsl hbd hq
      have := ih m m' a _ d _ _ fu r _ hA hsl' hbd' hvl hb
      rw [hsub] at this
      exact this
  · rw [ilBVarW_out n m h d o l fu hv (hJ ▸ hj) (hJ ▸ hq)] at hb
    rw [hJ] at hb
    have hq' : ¬ J.toNat - d.toNat < vs.size := by
      rw [hsl.size, ← hsub]; exact fun e => hq (UInt64.lt_iff_toNat_lt.mpr e)
    rw [dif_neg hq']
    have hlJ : l ≤ J := by
      rw [UInt64.le_iff_toNat_le]; rw [hsl.size] at hq'; omega
    obtain ⟨hok, hA', hres, hs'⟩ := internBVar_L m a hA _ r m' hb
    rw [UInt64.toNat_sub_of_le _ _ hlJ, ← hsl.size] at hok hA' hres
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
    (hb : ilsetK h c mkr = some (r, m')) :
    ∃ a', (do let r ← op; instLSet (decE h, c.toNat) r; pure r : AM EIdx).run a₂ =
      .ok (decE r, a') ∧ ArenaL m' a' ∧ m'.arr64 ILSPN = m₂.arr64 ILSPN := by
  cases h3 : mkr with
  | none => simp [h3, ilsetK] at hb
  | some q =>
    obtain ⟨r₃, m₃⟩ := q
    rw [h3] at hb
    simp only [ilsetK] at hb
    cases h4 : msetG ilSch m₃ h c r₃ with
    | none => simp [h4] at hb
    | some m₄ =>
      simp only [h4, Option.some.injEq, Prod.mk.injEq] at hb
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
  (h d o l fu r : Word) (vs : Array EIdx) (hsl : SpineR m o l vs) (hbd : o.toNat + l.toNat < 2 ^ 64)
  (hh : h.toNat < 2 ^ 32)
include ih hA hsl hbd hh

theorem gappArm_ok (hg : h >>> 28 = 4) :
    LArmRef (n + 1) ilgAppW (instListGoArmApp vs fu.toNat (decE h) d.toNat) m m' a h d o l fu r := by
  intro hb
  rw [instListGoArmApp]
  refine lprobe_ok _ _ m m' a hA h d r hh (ilgAppW_hit n m h d o l fu ) (fun hr => by rw [ilgAppW]; simp [hr]) (fun hr hh0 hb => ?_) hb
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [ilgAppW] at hb; simp only [ne_eq] at hs; simp only [hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, not_false_eq_true, and_self, reduceCtorEq] at hb
  have hv : viewOK m h APP := ⟨hs, UInt64.not_le.mp fun hc => by
    rw [ilgAppW] at hb; simp only [ne_eq] at hs; simp only [hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, hc, not_false_eq_true, and_self, and_true, reduceCtorEq] at hb⟩
  obtain ⟨-, hfw, haw⟩ := view_app m a hA.1.1 h hh hv hg
  rw [ilgAppW_miss n m h d o l fu hr hh0 hv] at hb
  rw [StateT.run_bind, viewApp_run, viewApp_ok m a hA.1.1 h hh hv, except_ok_bind]
  dsimp only
  refine SimD.exists (R := SpnR m) (Sim.bindD rfl (fun _ _ => rfl)
    (Sim.ofD fun x m₁ e => ih m m₁ a _ d o l fu x vs hA hsl hbd hfw e) fun x m₁ a₁ hR => ?_) hb
  obtain ⟨hA1, hs1⟩ := hR
  refine Sim.bindD (K := gappK₁.gappK₂ h d x) rfl (fun _ _ => rfl)
    (Sim.ofD fun y m₂ e => ih m₁ m₂ a₁ _ d o l fu y vs hA1 (hsl.of_spn hs1) hbd haw e)
        fun y m₂ a₂ hR => ?_
  obtain ⟨hA2, hs2⟩ := hR
  refine Sim.ofD fun r m' hb => ?_
  obtain ⟨a', h7, h8, h9⟩ := ltail_ok _ _ a₂ h d r m₂ m' hh (fun r₉ m₉ hr₉ => mkApp_okL m₂ a₂ hA2 x y r₉ m₉ hr₉) hb
  refine ⟨a', ?_, h8, h9.trans (hs2.trans hs1)⟩
  exact h7

theorem glamArm_ok (hg : h >>> 28 = 5) :
    LArmRef (n + 1) ilgLamW (instListGoArmBind vs fu.toNat (decE h) d.toNat) m m' a h d o l fu r := by
  intro hb
  have hd1 : ¬ d + 1 = 0 := fun hd1 => by rw [ilgLamW] at hb; simp [hd1] at hb
  rw [instListGoArmBind]
  refine lprobe_ok _ _ m m' a hA h d r hh (ilgLamW_hit n m h d o l fu hd1 ) (fun hr => by rw [ilgLamW]; simp [hd1, hr]) (fun hr hh0 hb => ?_) hb
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [ilgLamW] at hb; simp only [ne_eq] at hs; simp only [hd1, hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, not_false_eq_true, and_self, reduceCtorEq] at hb
  have hv : viewOK m h LAM := ⟨hs, UInt64.not_le.mp fun hc => by
    rw [ilgLamW] at hb; simp only [ne_eq] at hs; simp only [hd1, hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, hc, not_false_eq_true, and_self, and_true, reduceCtorEq] at hb⟩
  obtain ⟨-, hfw, haw⟩ := view_lam m a hA.1.1 h hh hv hg
  rw [ilgLamW_miss n m h d o l fu hd1 hr hh0 hv] at hb
  rw [StateT.run_bind, viewBind_run, viewBind_lam m a hA.1.1 h hh hv hg, except_ok_bind]
  dsimp only
  refine SimD.exists (R := SpnR m) (Sim.bindD rfl (fun _ _ => rfl)
    (Sim.ofD fun x m₁ e => ih m m₁ a _ d o l fu x vs hA hsl hbd hfw e) fun x m₁ a₁ hR => ?_) hb
  obtain ⟨hA1, hs1⟩ := hR
  refine Sim.bindD (K := glamK₁.glamK₂ h d x) rfl (fun _ _ => rfl)
    (Sim.ofD fun y m₂ e => by
      simpa only [succW_toNat d hd1] using ih m₁ m₂ a₁ _ (d + 1) o l fu y vs hA1
          (hsl.of_spn hs1) hbd haw e) fun y m₂ a₂ hR => ?_
  obtain ⟨hA2, hs2⟩ := hR
  have hbind : ∀ t b, internBindE (decE h).tag t b = internE (.lam t b) := by
    intro t b; simp [internBindE, decE_tag h hh, hg, ETag.lam, internE]
  refine Sim.ofD fun r m' hb => ?_
  obtain ⟨a', h7, h8, h9⟩ := ltail_ok _ _ a₂ h d r m₂ m' hh (fun r₉ m₉ hr₉ => mkLam_okL m₂ a₂ hA2 x y r₉ m₉ hr₉) hb
  refine ⟨a', ?_, h8, h9.trans (hs2.trans hs1)⟩
  simp only [hbind]; exact h7

theorem gforallArm_ok (hg : h >>> 28 = 6) :
    LArmRef (n + 1) ilgForallW (instListGoArmBind vs fu.toNat (decE h) d.toNat) m m' a h d o l fu r := by
  intro hb
  have hd1 : ¬ d + 1 = 0 := fun hd1 => by rw [ilgForallW] at hb; simp [hd1] at hb
  rw [instListGoArmBind]
  refine lprobe_ok _ _ m m' a hA h d r hh (ilgForallW_hit n m h d o l fu hd1 ) (fun hr => by rw [ilgForallW]; simp [hd1, hr]) (fun hr hh0 hb => ?_) hb
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [ilgForallW] at hb; simp only [ne_eq] at hs; simp only [hd1, hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, not_false_eq_true, and_self, reduceCtorEq] at hb
  have hv : viewOK m h FORALL := ⟨hs, UInt64.not_le.mp fun hc => by
    rw [ilgForallW] at hb; simp only [ne_eq] at hs; simp only [hd1, hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, hc, not_false_eq_true, and_self, and_true, reduceCtorEq] at hb⟩
  obtain ⟨-, hfw, haw⟩ := view_forall m a hA.1.1 h hh hv hg
  rw [ilgForallW_miss n m h d o l fu hd1 hr hh0 hv] at hb
  rw [StateT.run_bind, viewBind_run, viewBind_forall m a hA.1.1 h hh hv hg, except_ok_bind]
  dsimp only
  refine SimD.exists (R := SpnR m) (Sim.bindD rfl (fun _ _ => rfl)
    (Sim.ofD fun x m₁ e => ih m m₁ a _ d o l fu x vs hA hsl hbd hfw e) fun x m₁ a₁ hR => ?_) hb
  obtain ⟨hA1, hs1⟩ := hR
  refine Sim.bindD (K := gfaK₁.gfaK₂ h d x) rfl (fun _ _ => rfl)
    (Sim.ofD fun y m₂ e => by
      simpa only [succW_toNat d hd1] using ih m₁ m₂ a₁ _ (d + 1) o l fu y vs hA1
          (hsl.of_spn hs1) hbd haw e) fun y m₂ a₂ hR => ?_
  obtain ⟨hA2, hs2⟩ := hR
  have hbind : ∀ t b, internBindE (decE h).tag t b = internE (.forallE t b) := by
    intro t b; simp [internBindE, decE_tag h hh, hg, ETag.lam, internE]
  refine Sim.ofD fun r m' hb => ?_
  obtain ⟨a', h7, h8, h9⟩ := ltail_ok _ _ a₂ h d r m₂ m' hh (fun r₉ m₉ hr₉ => mkForall_okL m₂ a₂ hA2 x y r₉ m₉ hr₉) hb
  refine ⟨a', ?_, h8, h9.trans (hs2.trans hs1)⟩
  simp only [hbind]; exact h7

theorem gletArm_ok (hg : h >>> 28 = 7) :
    LArmRef (n + 1) ilgLetW (instListGoArmLet vs fu.toNat (decE h) d.toNat) m m' a h d o l fu r := by
  intro hb
  have hd1 : ¬ d + 1 = 0 := fun hd1 => by rw [ilgLetW] at hb; simp [hd1] at hb
  rw [instListGoArmLet]
  refine lprobe_ok _ _ m m' a hA h d r hh (ilgLetW_hit n m h d o l fu hd1 ) (fun hr => by rw [ilgLetW]; simp [hd1, hr]) (fun hr hh0 hb => ?_) hb
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [ilgLetW] at hb; simp only [ne_eq] at hs; simp only [hd1, hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, not_false_eq_true, and_self, reduceCtorEq] at hb
  have hv : viewOK m h LET := ⟨hs, UInt64.not_le.mp fun hc => by
    rw [ilgLetW] at hb; simp only [ne_eq] at hs; simp only [hd1, hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, hc, not_false_eq_true, and_self, and_true, reduceCtorEq] at hb⟩
  obtain ⟨-, htw, hvw, hbw⟩ := view_let m a hA.1.1 h hh hv hg
  rw [ilgLetW_miss n m h d o l fu hd1 hr hh0 hv] at hb
  rw [StateT.run_bind, viewLet_run, viewLet_ok m a hA.1.1 h hh hv, except_ok_bind]
  dsimp only
  refine SimD.exists (R := SpnR m) (Sim.bindD rfl (fun _ _ => rfl)
    (Sim.ofD fun x m₁ e => ih m m₁ a _ d o l fu x vs hA hsl hbd htw e) fun x m₁ a₁ hR => ?_) hb
  obtain ⟨hA1, hs1⟩ := hR
  refine Sim.bindD (K := gleK₁.gleK₂ n h d o l fu _ x) rfl (fun _ _ => rfl)
    (Sim.ofD fun y m₂ e => ih m₁ m₂ a₁ _ d o l fu y vs hA1 (hsl.of_spn hs1) hbd hvw e)
        fun y m₂ a₂ hR => ?_
  obtain ⟨hA2, hs2⟩ := hR
  refine Sim.bindD (K := gleK₁.gleK₃ h d x y) rfl (fun _ _ => rfl)
    (Sim.ofD fun z m₃ e => by
      simpa only [succW_toNat d hd1] using ih m₂ m₃ a₂ _ (d + 1) o l fu z vs hA2
          ((hsl.of_spn hs1).of_spn hs2) hbd hbw e) fun z m₃ a₃ hR => ?_
  obtain ⟨hA3, hs3⟩ := hR
  have hbind : ∀ t b, internBindE (decE h).tag t b = internE (.forallE t b) := by
    intro t b; simp [internBindE, decE_tag h hh, hg, ETag.lam, internE]
  refine Sim.ofD fun r m' hb => ?_
  obtain ⟨a', h7, h8, h9⟩ := ltail_ok _ _ a₃ h d r m₃ m' hh (fun r₉ m₉ hr₉ => mkLet_okL m₃ a₃ hA3 x y z r₉ m₉ hr₉) hb
  refine ⟨a', ?_, h8, h9.trans (hs3.trans (hs2.trans hs1))⟩
  simp only [hbind, internLetEE]; exact h7

theorem gprojArm_ok (hg : h >>> 28 = 9) :
    LArmRef (n + 1) ilgProjW (instListGoArmProj vs fu.toNat (decE h) d.toNat) m m' a h d o l fu r := by
  intro hb
  rw [instListGoArmProj]
  refine lprobe_ok _ _ m m' a hA h d r hh (ilgProjW_hit n m h d o l fu ) (fun hr => by rw [ilgProjW]; simp [hr]) (fun hr hh0 hb => ?_) hb
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [ilgProjW] at hb; simp only [ne_eq] at hs; simp only [hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, not_false_eq_true, and_self, reduceCtorEq] at hb
  have hv : viewOK m h PROJ := ⟨hs, UInt64.not_le.mp fun hc => by
    rw [ilgProjW] at hb; simp only [ne_eq] at hs; simp only [hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, hc, not_false_eq_true, and_self, and_true, reduceCtorEq] at hb⟩
  obtain ⟨-, -, hew⟩ := view_proj m a hA.1.1 h hh hv hg
  rw [ilgProjW_miss n m h d o l fu hr hh0 hv] at hb
  rw [StateT.run_bind, viewProj_run, viewProj_ok m a hA.1.1 h hh hv, except_ok_bind]
  dsimp only
  refine SimD.exists (R := SpnR m) (Sim.bindD rfl (fun _ _ => rfl)
    (Sim.ofD fun x m₁ e => ih m m₁ a _ d o l fu x vs hA hsl hbd hew e) fun x m₁ a₁ hR => ?_) hb
  obtain ⟨hA1, hs1⟩ := hR
  refine Sim.ofD fun r m' hb => ?_
  obtain ⟨a', h7, h8, h9⟩ := ltail_ok _ _ a₁ h d r m₁ m' hh (fun r₉ m₉ hr₉ => mkProj_okL m₁ a₁ hA1 _ _ x r₉ m₉ hr₉) hb
  refine ⟨a', ?_, h8, h9.trans (hs1)⟩
  simp only [internProjE]; exact h7

end garms

theorem ilarmOK_succ (n : Nat) (ih : ILGoOK n) : ILArmOK (n + 1) := by
  intro m m' a h d o l fu r vs hA hsl hbd hh
  exact ⟨lappArm_ok n ih m m' a hA h d o l fu r vs hsl hbd hh,
    llamArm_ok n ih m m' a hA h d o l fu r vs hsl hbd hh,
    lforallArm_ok n ih m m' a hA h d o l fu r vs hsl hbd hh,
    lletArm_ok n ih m m' a hA h d o l fu r vs hsl hbd hh,
    lprojArm_ok n ih m m' a hA h d o l fu r vs hsl hbd hh,
    lbvarArm_ok n ih m m' a hA h d o l fu r vs hsl hbd hh⟩

/-- **The model of `il_go` refines `instantiateList`** at the counter's fuel, at every L fuel. -/
theorem ilOK (n : Nat) : ILGoOK n ∧ ILArmOK n := by
  induction n with
  | zero =>
    refine ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb => by simp [ilW] at hb,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    intro _ hb <;> simp [ilAppW, ilLamW, ilForallW, ilLetW, ilProjW, ilBVarW] at hb
  | succ n ih => exact ⟨ilgoOK_succ n ih.2, ilarmOK_succ n ih.1⟩

theorem ilgarmOK_succ (n : Nat) (ih : ILGGoOK n) : ILGArmOK (n + 1) := by
  intro m m' a h d o l fu r vs hA hsl hbd hh
  exact ⟨gappArm_ok n ih m m' a hA h d o l fu r vs hsl hbd hh,
    glamArm_ok n ih m m' a hA h d o l fu r vs hsl hbd hh,
    gforallArm_ok n ih m m' a hA h d o l fu r vs hsl hbd hh,
    gletArm_ok n ih m m' a hA h d o l fu r vs hsl hbd hh,
    gprojArm_ok n ih m m' a hA h d o l fu r vs hsl hbd hh⟩

/-- **The model of `ilg_go` refines `instantiateListGo`** at the counter's fuel, at every L fuel. -/
theorem ilgOK (n : Nat) : ILGGoOK n ∧ ILGArmOK n := by
  induction n with
  | zero =>
    refine ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb => by simp [ilgW] at hb,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    intro _ hb <;> simp [ilgAppW, ilgLamW, ilgForallW, ilgLetW, ilgProjW] at hb
  | succ n ih => exact ⟨ilggoOK_succ n ih.2 (ilOK n).1, ilgarmOK_succ n ih.1⟩

/-! ## The entry `inst_list` refines `instantiateListFast` -/

theorem instListFast_run (F : Nat) (e : EIdx) (vs : Array EIdx) (d : Nat) (a : AState) :
    (instantiateListFast F e vs d).run a =
      ((instantiateListGo vs F e d).run (withLLC a ∅) >>= fun p => .ok (p.1, withLLC p.2 ∅)) := by
  simp only [instantiateListFast, StateT.run_bind, instLClear_run, except_ok_bind]
  cases (instantiateListGo vs F e d).run (withLLC a ∅) <;> rfl

theorem instListW_correct (n : Nat) (m m' : Mem) (a : AState) (hA : ArenaL m a)
    (e o l d r : Word) (vs : Array EIdx) (hsl : SpineR m o l vs) (hbd : o.toNat + l.toNat < 2 ^ 64)
    (he : e.toNat < 2 ^ 32) (hb : instListW n m e o l d = some (r, m')) :
    ∃ a', (instantiateListFast coreWalkFuel (decE e) vs d.toNat).run a = .ok (decE r, a') ∧ ArenaL m' a' ∧
      m'.arr64 ILSPN = m.arr64 ILSPN ∧ r.toNat < 2 ^ 32 := by
  simp only [instListW] at hb
  have h0 : ¬ rdW (m.arr64 CTL) 50 + 2 = 0 := fun h0 => by simp [h0] at hb
  simp only [h0, ↓reduceIte] at hb
  have hA₀ := ArenaL.lmemo_clear m a hA h0
  have hs₀ : (mclearG ilSch m).arr64 ILSPN = m.arr64 ILSPN :=
    spn_of_frame (mclearG_frame ilSch m) (by decide)
  cases hw : ilgW n (mclearG ilSch m) e d o l 4000000000 with
  | none => simp [hw, ilclrK] at hb
  | some p =>
    obtain ⟨r₁, m₁⟩ := p
    have h1 : ¬ rdW (m₁.arr64 CTL) 50 + 2 = 0 := fun h1 => by simp [hw, ilclrK, h1] at hb
    simp only [hw, ilclrK, h1, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    obtain ⟨a₁, ha₁, hA₁, hs₁⟩ :=
      (ilgOK n).1 _ _ _ e d o l 4000000000 r₁ vs hA₀ (hsl.of_spn hs₀) hbd he hw
    rw [coreWalkFuel_toNat] at ha₁
    exact ⟨_, by rw [instListFast_run, ha₁, decE_and32]; rfl, ArenaL.lmemo_clear m₁ a₁ hA₁ h1,
      (spn_of_frame (mclearG_frame ilSch m₁) (by decide)).trans (hs₁.trans hs₀), and32_lt r₁⟩

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

end L.Arena
