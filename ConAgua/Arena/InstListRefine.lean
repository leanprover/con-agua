import ConAgua.Arena.InstListSpec
import ConAgua.Arena.Abs1Refine
import ConAgua.Arena.WhnfBase
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

/-- What `il_go`'s model at fuel `n` says about `instantiateList vs` at any fuel `F ≥ n`. -/
def ILGoOK (n : Nat) : Prop :=
  ∀ (F : Nat) (m m' : Mem) (a : AState) (h d o l r : Word) (vs : Array EIdx), n ≤ F →
    ArenaL m a → SpineR m o l vs → o.toNat + l.toNat < 2 ^ 64 → h.toNat < 2 ^ 32 →
    ilW n m h d o l = some (r, m') →
    ∃ a', (instantiateList vs F (decE h) d.toNat).run a = .ok (decE r, a') ∧ ArenaL m' a' ∧
      m'.arr64 ILSPN = m.arr64 ILSPN

/-- The same for `ilg_go`'s model and `instantiateListGo vs`. -/
def ILGGoOK (n : Nat) : Prop :=
  ∀ (F : Nat) (m m' : Mem) (a : AState) (h d o l r : Word) (vs : Array EIdx), n ≤ F →
    ArenaL m a → SpineR m o l vs → o.toNat + l.toNat < 2 ^ 64 → h.toNat < 2 ^ 32 →
    ilgW n m h d o l = some (r, m') →
    ∃ a', (instantiateListGo vs F (decE h) d.toNat).run a = .ok (decE r, a') ∧ ArenaL m' a' ∧
      m'.arr64 ILSPN = m.arr64 ILSPN

/-- The arena arm `arm` refines the L arm `armW` at `h`, under `ArenaL`, keeping the stack. -/
def LArmRef (n : Nat) (armW : Nat → Mem → Word → Word → Word → Word → Option (Word × Mem))
    (arm : AM EIdx) (m m' : Mem) (a : AState) (h d o l r : Word) : Prop :=
  armW n m h d o l = some (r, m') →
    ∃ a', arm.run a = .ok (decE r, a') ∧ ArenaL m' a' ∧ m'.arr64 ILSPN = m.arr64 ILSPN

/-- The pure walk's six arms, each at its tag. -/
def ILArmOK (n : Nat) : Prop :=
  ∀ (F : Nat) (m m' : Mem) (a : AState) (h d o l r : Word) (vs : Array EIdx), n ≤ F + 1 →
    ArenaL m a → SpineR m o l vs → o.toNat + l.toNat < 2 ^ 64 → h.toNat < 2 ^ 32 →
    (h >>> 28 = 4 → LArmRef n ilAppW (instListArmApp vs F (decE h) d.toNat) m m' a h d o l r) ∧
    (h >>> 28 = 5 → LArmRef n ilLamW (instListArmBind vs F (decE h) d.toNat) m m' a h d o l r) ∧
    (h >>> 28 = 6 → LArmRef n ilForallW (instListArmBind vs F (decE h) d.toNat) m m' a h d o l r) ∧
    (h >>> 28 = 7 → LArmRef n ilLetW (instListArmLet vs F (decE h) d.toNat) m m' a h d o l r) ∧
    (h >>> 28 = 9 → LArmRef n ilProjW (instListArmProj vs F (decE h) d.toNat) m m' a h d o l r) ∧
    (h >>> 28 = 0 → LArmRef n ilBVarW (instListArmBVar vs F (decE h) d.toNat) m m' a h d o l r)

/-- The memo walk's five arms, each at its tag. -/
def ILGArmOK (n : Nat) : Prop :=
  ∀ (F : Nat) (m m' : Mem) (a : AState) (h d o l r : Word) (vs : Array EIdx), n ≤ F + 1 →
    ArenaL m a → SpineR m o l vs → o.toNat + l.toNat < 2 ^ 64 → h.toNat < 2 ^ 32 →
    (h >>> 28 = 4 → LArmRef n ilgAppW (instListGoArmApp vs F (decE h) d.toNat) m m' a h d o l r) ∧
    (h >>> 28 = 5 → LArmRef n ilgLamW (instListGoArmBind vs F (decE h) d.toNat) m m' a h d o l r) ∧
    (h >>> 28 = 6 →
      LArmRef n ilgForallW (instListGoArmBind vs F (decE h) d.toNat) m m' a h d o l r) ∧
    (h >>> 28 = 7 → LArmRef n ilgLetW (instListGoArmLet vs F (decE h) d.toNat) m m' a h d o l r) ∧
    (h >>> 28 = 9 → LArmRef n ilgProjW (instListGoArmProj vs F (decE h) d.toNat) m m' a h d o l r)

/-! ## The dispatchers -/

theorem ilgoOK_succ (n : Nat) (ih : ILArmOK n) : ILGoOK (n + 1) := by
  intro F m m' a h d o l r vs hF hA hsl hbd hh hb
  obtain ⟨F, rfl⟩ : ∃ G, F = G + 1 := ⟨F - 1, by omega⟩
  rw [instantiateList_succ, StateT.run_bind, instListCutoff_run]
  simp only [except_ok_bind]
  by_cases hcut : ilCut m h d
  · rw [ilW_cut n m h d o l hcut] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    rw [ilcut_iff m a hA h d hh] at hcut
    simp only [hcut, ↓reduceIte]
    exact ⟨a, rfl, hA, by simp⟩
  have hcut' := hcut
  rw [ilcut_iff m a hA h d hh] at hcut'
  simp only [Bool.not_eq_true] at hcut'
  simp only [hcut', Bool.false_eq_true, ↓reduceIte, decE_tag h hh]
  have arm := ih F m m' a h d o l r vs (by omega) hA hsl hbd hh
  have t4 : h >>> 28 = 4 ↔ (h >>> 28).toUInt32 = 4 := by simpa using tag_iff h 4 hh (by decide)
  have t5 : h >>> 28 = 5 ↔ (h >>> 28).toUInt32 = 5 := by simpa using tag_iff h 5 hh (by decide)
  have t6 : h >>> 28 = 6 ↔ (h >>> 28).toUInt32 = 6 := by simpa using tag_iff h 6 hh (by decide)
  have t0 : h >>> 28 = 0 ↔ (h >>> 28).toUInt32 = 0 := by simpa using tag_iff h 0 hh (by decide)
  have t7 : h >>> 28 = 7 ↔ (h >>> 28).toUInt32 = 7 := by simpa using tag_iff h 7 hh (by decide)
  have t9 : h >>> 28 = 9 ↔ (h >>> 28).toUInt32 = 9 := by simpa using tag_iff h 9 hh (by decide)
  simp only [ETag.app, ETag.isBind, ETag.lam, ETag.forallE, ETag.bvar, ETag.letE, ETag.proj,
    beq_iff_eq, Bool.or_eq_true] at *
  by_cases g4 : h >>> 28 = 4
  · rw [ilW_app n m h d o l hcut g4] at hb
    simp only [show (h >>> 28).toUInt32 = 4 from (t4.mp g4), ↓reduceIte]
    exact arm.1 g4 hb
  have g4' : ¬ (h >>> 28).toUInt32 = 4 := fun e => g4 (t4.mpr e)
  by_cases g5 : h >>> 28 = 5
  · rw [ilW_lam n m h d o l hcut g5] at hb
    simp only [g4', show (h >>> 28).toUInt32 = 5 from (t5.mp g5), true_or, ↓reduceIte]
    exact arm.2.1 g5 hb
  have g5' : ¬ (h >>> 28).toUInt32 = 5 := fun e => g5 (t5.mpr e)
  by_cases g6 : h >>> 28 = 6
  · rw [ilW_forall n m h d o l hcut g6] at hb
    simp only [g4', g5', show (h >>> 28).toUInt32 = 6 from (t6.mp g6), or_true, ↓reduceIte]
    exact arm.2.2.1 g6 hb
  have g6' : ¬ (h >>> 28).toUInt32 = 6 := fun e => g6 (t6.mpr e)
  simp only [g4', g5', g6', or_self, ↓reduceIte]
  by_cases g7 : h >>> 28 = 7
  · rw [ilW_let n m h d o l hcut g7] at hb
    simp only [show (h >>> 28).toUInt32 = 7 from (t7.mp g7), ↓reduceIte]
    exact arm.2.2.2.1 g7 hb
  have g7' : ¬ (h >>> 28).toUInt32 = 7 := fun e => g7 (t7.mpr e)
  simp only [g7', ↓reduceIte]
  by_cases g9 : h >>> 28 = 9
  · rw [ilW_proj n m h d o l hcut g9] at hb
    simp only [show (h >>> 28).toUInt32 = 9 from (t9.mp g9), ↓reduceIte]
    exact arm.2.2.2.2.1 g9 hb
  have g9' : ¬ (h >>> 28).toUInt32 = 9 := fun e => g9 (t9.mpr e)
  simp only [g9', ↓reduceIte]
  by_cases g0 : h >>> 28 = 0
  · rw [ilW_bvar n m h d o l hcut g0] at hb
    simp only [show (h >>> 28).toUInt32 = 0 from (t0.mp g0), ↓reduceIte]
    exact arm.2.2.2.2.2 g0 hb
  have g0' : ¬ (h >>> 28).toUInt32 = 0 := fun e => g0 (t0.mpr e)
  simp only [g0', ↓reduceIte]
  rw [ilW_leaf n m h d o l hcut g0 g4 g5 g6 g7 g9] at hb
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
  exact ⟨a, rfl, hA, by simp⟩

theorem ilggoOK_succ (n : Nat) (ih : ILGArmOK n) (ihl : ILGoOK n) : ILGGoOK (n + 1) := by
  intro F m m' a h d o l r vs hF hA hsl hbd hh hb
  obtain ⟨F, rfl⟩ : ∃ G, F = G + 1 := ⟨F - 1, by omega⟩
  rw [instantiateListGo_succ, StateT.run_bind, instListCutoff_run]
  simp only [except_ok_bind]
  by_cases hcut : ilCut m h d
  · rw [ilgW_cut n m h d o l hcut] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    rw [ilcut_iff m a hA h d hh] at hcut
    simp only [hcut, ↓reduceIte]
    exact ⟨a, rfl, hA, by simp⟩
  have hcut' := hcut
  rw [ilcut_iff m a hA h d hh] at hcut'
  simp only [Bool.not_eq_true] at hcut'
  simp only [hcut', Bool.false_eq_true, ↓reduceIte, decE_tag h hh]
  have arm := ih F m m' a h d o l r vs (by omega) hA hsl hbd hh
  have t4 : h >>> 28 = 4 ↔ (h >>> 28).toUInt32 = 4 := by simpa using tag_iff h 4 hh (by decide)
  have t5 : h >>> 28 = 5 ↔ (h >>> 28).toUInt32 = 5 := by simpa using tag_iff h 5 hh (by decide)
  have t6 : h >>> 28 = 6 ↔ (h >>> 28).toUInt32 = 6 := by simpa using tag_iff h 6 hh (by decide)
  have t0 : h >>> 28 = 0 ↔ (h >>> 28).toUInt32 = 0 := by simpa using tag_iff h 0 hh (by decide)
  have t7 : h >>> 28 = 7 ↔ (h >>> 28).toUInt32 = 7 := by simpa using tag_iff h 7 hh (by decide)
  have t9 : h >>> 28 = 9 ↔ (h >>> 28).toUInt32 = 9 := by simpa using tag_iff h 9 hh (by decide)
  simp only [ETag.app, ETag.isBind, ETag.lam, ETag.forallE, ETag.bvar, ETag.letE, ETag.proj,
    beq_iff_eq, Bool.or_eq_true] at *
  by_cases g4 : h >>> 28 = 4
  · rw [ilgW_app n m h d o l hcut g4] at hb
    simp only [show (h >>> 28).toUInt32 = 4 from (t4.mp g4), ↓reduceIte]
    exact arm.1 g4 hb
  have g4' : ¬ (h >>> 28).toUInt32 = 4 := fun e => g4 (t4.mpr e)
  by_cases g5 : h >>> 28 = 5
  · rw [ilgW_lam n m h d o l hcut g5] at hb
    simp only [g4', show (h >>> 28).toUInt32 = 5 from (t5.mp g5), true_or, ↓reduceIte]
    exact arm.2.1 g5 hb
  have g5' : ¬ (h >>> 28).toUInt32 = 5 := fun e => g5 (t5.mpr e)
  by_cases g6 : h >>> 28 = 6
  · rw [ilgW_forall n m h d o l hcut g6] at hb
    simp only [g4', g5', show (h >>> 28).toUInt32 = 6 from (t6.mp g6), or_true, ↓reduceIte]
    exact arm.2.2.1 g6 hb
  have g6' : ¬ (h >>> 28).toUInt32 = 6 := fun e => g6 (t6.mpr e)
  simp only [g4', g5', g6', or_self, ↓reduceIte]
  by_cases g7 : h >>> 28 = 7
  · rw [ilgW_let n m h d o l hcut g7] at hb
    simp only [show (h >>> 28).toUInt32 = 7 from (t7.mp g7), ↓reduceIte]
    exact arm.2.2.2.1 g7 hb
  have g7' : ¬ (h >>> 28).toUInt32 = 7 := fun e => g7 (t7.mpr e)
  simp only [g7', ↓reduceIte]
  by_cases g9 : h >>> 28 = 9
  · rw [ilgW_proj n m h d o l hcut g9] at hb
    simp only [show (h >>> 28).toUInt32 = 9 from (t9.mp g9), ↓reduceIte]
    exact arm.2.2.2.2 g9 hb
  have g9' : ¬ (h >>> 28).toUInt32 = 9 := fun e => g9 (t9.mpr e)
  simp only [g9', ↓reduceIte]
  by_cases g0 : h >>> 28 = 0
  · rw [ilgW_bvar n m h d o l hcut g0] at hb
    simp only [show (h >>> 28).toUInt32 = 0 from (t0.mp g0), ↓reduceIte]
    exact ihl F m m' a h d o l r vs (by omega) hA hsl hbd hh hb
  have g0' : ¬ (h >>> 28).toUInt32 = 0 := fun e => g0 (t0.mpr e)
  simp only [g0', ↓reduceIte]
  rw [ilgW_leaf n m h d o l hcut g0 g4 g5 g6 g7 g9] at hb
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
  exact ⟨a, rfl, hA, by simp⟩

end L.Arena
