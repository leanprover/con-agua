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

end L.Arena
