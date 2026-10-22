import ConAgua.Arena.Abs1Spec
import ConAgua.Arena.Inst1Refine
import ConAgua.Arena.FVarRangeRefine
import ConAgua.Arena.Keeps
import ConAgua.Census.Attr

/-!
# `abs_go` refines the arena's `abstract1Go`

`Inst1Refine.lean`'s proof, with three additions:

* **The memo tier `ArenaA := ArenaD ∧ AbsR`.** `abs1C` lives outside `MemosR` (`Abs1.lean`'s
  module note), so its relation `AbsR` (`MemoRG abSch lfKey decE`) rides next to `ArenaD`, kept
  across the stores by their frames (`mk*W_frameA`, `binternW_frameA`: none writes array 49 or
  `CTL[48]`) and across the twin's interning by `Keeps` (`internE` changes only the store).
* **The cut-off through `fr_memo`** (`fvbW_ok`): `frMemoW_correct` gives `ArenaR`; `DerR` and
  `AbsR` survive by the model's frame (`frW_frame`: only `FRMEMO` and `CTL[46‥47]`) on the L side
  and by `Keeps` of `(store, abs1C)` on the twin's side (`fvarRangeGo` changes only `fvarBC`).
* **The rebuild on change** (`rbAppW_ok` …): the twin compares handles (`decE x == decE f`),
  L compares words; they agree because the children are below `2^32` (the view) and so is a
  result `mk_*` accepted (its own guard).
-/

open ConRon.Arena ConLeche
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

theorem abSch_wf : abSch.WF := ⟨by decide, by decide⟩

/-! ## The `abstract1` memo tier -/

/-- The `abs1C` relation. -/
def AbsR (m : Mem) (a : AState) : Prop := MemoRG abSch lfKey decE m a.memos.abs1C

/-- `ArenaD` and the `abstract1` memo. -/
def ArenaA (m : Mem) (a : AState) : Prop := ArenaD m a ∧ AbsR m a

/-- The arena state with the `abstract1` memo replaced. -/
def withAC (a : AState) (mp : Std.HashMap (EIdx × Nat) EIdx) : AState :=
  { a with memos := { a.memos with abs1C := mp } }

theorem abs1Get_run (x : EIdx × Nat) (a : AState) :
    (abs1Get x).run a = .ok (a.memos.abs1C[x]?, a) := rfl

theorem abs1Set_run (x : EIdx × Nat) (r : EIdx) (a : AState) :
    (abs1Set x r).run a = .ok ((), withAC a (a.memos.abs1C.insert x r)) := rfl

theorem abs1Clear_run (a : AState) : abs1Clear.run a = .ok ((), withAC a ∅) := rfl

theorem not_arenaCtl_48 : (48 : Word) ∉ arenaCtl := by
  simp [arenaCtl, storeCtl, memoCtl]
theorem not_arenaCtl_49 : (49 : Word) ∉ arenaCtl := by
  simp [arenaCtl, storeCtl, memoCtl]

/-- `ArenaR` and `DerR` do not read `abs1C`. -/
theorem ArenaD.withAC {m : Mem} {a : AState} (hD : ArenaD m a) (mp : Std.HashMap (EIdx × Nat) EIdx) :
    ArenaD m (withAC a mp) :=
  ⟨hD.1.with_memos (MemFrame.refl [] [] m) (by simp) (by simp)
    ⟨hD.1.memos.bvar, hD.1.memos.lift, hD.1.memos.inst1, hD.1.memos.fvar⟩,
    DerR.of_store m a _ hD.2 rfl⟩

theorem ArenaA.amemo_set (m m' : Mem) (a : AState) (hA : ArenaA m a) (h c v : Word)
    (hh : h.toNat < 2 ^ 32) (hs : msetG abSch m h c v = some m') :
    ArenaA m' (withAC a (a.memos.abs1C.insert (decE h, c.toNat) (decE v))) := by
  have hf := msetG_frame abSch abSch_wf m m' h c v hs
  refine ⟨ArenaD.withAC ⟨hA.1.1.frame (by decide) (by simpa using not_arenaCtl_49) hf,
    DerR.frameM _ _ m m' hf (by decide) _ hA.1.2⟩ _, ?_⟩
  exact memoRG_set abSch abSch_wf lfKey decE m _ hA.2 h c v hh m' hs

theorem ArenaA.amemo_clear (m : Mem) (a : AState) (hA : ArenaA m a)
    (h0 : rdW (m.arr64 CTL) 48 + 2 ≠ 0) : ArenaA (mclearG abSch m) (withAC a ∅) := by
  have hf := mclearG_frame abSch m
  have hC : ∀ x ∈ [abSch.cs, abSch.cs + 1], x ∉ arenaCtl := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact not_arenaCtl_48
    · exact not_arenaCtl_49
  exact ⟨ArenaD.withAC ⟨hA.1.1.frame (by decide) hC hf, DerR.frameM _ _ m _ hf (by decide) _ hA.1.2⟩ _,
    memoRG_clear abSch abSch_wf lfKey decE m _ hA.2 h0⟩

/-- **`AbsR` survives a writer apart from it, if the twin's memo did not move.** -/
theorem AbsR.across {A : List ArrId} {C : List Word} {m m' : Mem} {a a' : AState}
    (hR : AbsR m a) (hf : MemFrame A C m m') (hA : ABMEMO ∉ A) (hC : (48 : Word) ∉ C)
    (he : a'.memos.abs1C = a.memos.abs1C) : AbsR m' a' := by
  unfold AbsR; rw [he]
  exact memoRG_frame abSch abSch_wf lfKey decE A C hA hC m m' hf _ hR

/-! ## The frames of the stores (L side) -/

theorem mkAppW_frameA (m m' : Mem) (f a r : Word) (hI : mkAppW m f a = some (r, m')) :
    MemFrame [AREC, ASLOT, ADER] [4, 5] m m' := by
  unfold mkAppW at hI
  split at hI
  · cases hI
  cases hI₁ : ainternW m f a with
  | none => simp [hI₁, mkK] at hI
  | some p =>
    obtain ⟨r₁, m₁⟩ := p
    simp only [hI₁, mkK_some] at hI
    split at hI
    · cases hI
    rename_i m₂ hP
    simp only [Option.some.injEq, Prod.mk.injEq] at hI
    obtain ⟨rfl, rfl⟩ := hI
    have hI₂ := hI₁
    rw [ainternW_eq] at hI₂
    have hf1 := internM_frame appSch appSch_wf _ _ _ _ _ _ _ _ hI₂
    have hf2 := derPutW_frame ADER (by decide) _ _ _ _ _ _ hP
    exact (hf1.mono (by simp [appSch, AREC, ASLOT]) (by simp [appSch])).trans
      (hf2.mono (by simp) (by simp))

theorem mkLamW_frameA (m m' : Mem) (f a r : Word) (hI : mkLamW m f a = some (r, m')) :
    MemFrame [LAREC, LASLOT, LADER] [28, 29] m m' := by
  unfold mkLamW at hI
  split at hI
  · cases hI
  cases hI₁ : lainternW m f a with
  | none => simp [hI₁, mkK] at hI
  | some p =>
    obtain ⟨r₁, m₁⟩ := p
    simp only [hI₁, mkK_some] at hI
    split at hI
    · cases hI
    rename_i m₂ hP
    simp only [Option.some.injEq, Prod.mk.injEq] at hI
    obtain ⟨rfl, rfl⟩ := hI
    have hI₂ := hI₁
    rw [lainternW_eq] at hI₂
    have hf1 := internM_frame lamSch lamSch_wf _ _ _ _ _ _ _ _ hI₂
    have hf2 := derPutW_frame LADER (by decide) _ _ _ _ _ _ hP
    exact (hf1.mono (by simp [lamSch, LAREC, LASLOT]) (by simp [lamSch])).trans
      (hf2.mono (by simp) (by simp))

theorem mkForallW_frameA (m m' : Mem) (f a r : Word) (hI : mkForallW m f a = some (r, m')) :
    MemFrame [FAREC, FASLOT, FADER] [30, 31] m m' := by
  unfold mkForallW at hI
  split at hI
  · cases hI
  cases hI₁ : fainternW m f a with
  | none => simp [hI₁, mkK] at hI
  | some p =>
    obtain ⟨r₁, m₁⟩ := p
    simp only [hI₁, mkK_some] at hI
    split at hI
    · cases hI
    rename_i m₂ hP
    simp only [Option.some.injEq, Prod.mk.injEq] at hI
    obtain ⟨rfl, rfl⟩ := hI
    have hI₂ := hI₁
    rw [fainternW_eq] at hI₂
    have hf1 := internM_frame forallSch forallSch_wf _ _ _ _ _ _ _ _ hI₂
    have hf2 := derPutW_frame FADER (by decide) _ _ _ _ _ _ hP
    exact (hf1.mono (by simp [forallSch, FAREC, FASLOT]) (by simp [forallSch])).trans
      (hf2.mono (by simp) (by simp))

theorem mkLetW_frameA (m m' : Mem) (t v b r : Word) (hI : mkLetW m t v b = some (r, m')) :
    MemFrame [LEREC, LESLOT, LEDER] [20, 21] m m' := by
  unfold mkLetW at hI
  split at hI
  · cases hI
  cases hI₁ : leinternW m t v b with
  | none => simp [hI₁, mkK] at hI
  | some p =>
    obtain ⟨r₁, m₁⟩ := p
    simp only [hI₁, mkK_some] at hI
    split at hI
    · cases hI
    rename_i m₂ hP
    simp only [Option.some.injEq, Prod.mk.injEq] at hI
    obtain ⟨rfl, rfl⟩ := hI
    have hI₂ := hI₁
    rw [leinternW_eq] at hI₂
    have hf1 := internM_frame letSch letSch_wf _ _ _ _ _ _ _ _ hI₂
    have hf2 := derPutW_frame LEDER (by decide) _ _ _ _ _ _ hP
    exact (hf1.mono (by simp [letSch, LEREC, LESLOT]) (by simp [letSch])).trans
      (hf2.mono (by simp) (by simp))

theorem mkProjW_frameA (m m' : Mem) (n i e r : Word) (hI : mkProjW m n i e = some (r, m')) :
    MemFrame [PJREC, PJSLOT, PJDER] [32, 33] m m' := by
  unfold mkProjW at hI
  split at hI
  · cases hI
  cases hI₁ : pjinternW m n i e with
  | none => simp [hI₁, mkK] at hI
  | some p =>
    obtain ⟨r₁, m₁⟩ := p
    simp only [hI₁, mkK_some] at hI
    split at hI
    · cases hI
    rename_i m₂ hP
    simp only [Option.some.injEq, Prod.mk.injEq] at hI
    obtain ⟨rfl, rfl⟩ := hI
    have hI₂ := hI₁
    rw [pjinternW_eq] at hI₂
    have hf1 := internM_frame projSch projSch_wf _ _ _ _ _ _ _ _ hI₂
    have hf2 := derPutW_frame PJDER (by decide) _ _ _ _ _ _ hP
    exact (hf1.mono (by simp [projSch, PJREC, PJSLOT]) (by simp [projSch])).trans
      (hf2.mono (by simp) (by simp))

theorem binternW_frameA (m m' : Mem) (u r : Word) (hI : binternW m u = some (r, m')) :
    MemFrame [BREC, BSLOT] [22, 23] m m' := by
  rw [binternW_eq] at hI
  exact (internM_frame bvarSch bvarSch_wf _ _ _ _ _ _ _ _ hI).mono (by simp [bvarSch])
    (by simp [bvarSch])

/-! ## The twin's interning keeps `abs1C` -/

theorem keeps_internNodeE_ab (v : ENodeView) : Keeps (·.memos.abs1C) (internNodeE v) := by
  prim_keeps internNodeE
theorem keeps_internLamE_ab (ty b : EIdx) : Keeps (·.memos.abs1C) (internLamE ty b) := by
  prim_keeps internLamE
theorem keeps_internForallEE_ab (ty b : EIdx) : Keeps (·.memos.abs1C) (internForallEE ty b) := by
  prim_keeps internForallEE
theorem keeps_internE_ab (v : ENodeView) : Keeps (·.memos.abs1C) (internE v) := by
  cases v <;> simp only [internE] <;>
    first | exact keeps_internNodeE_ab _ | exact keeps_internLamE_ab _ _ | exact keeps_internForallEE_ab _ _

theorem internE_abs1C (v : ENodeView) (a : AState) (hok : AM.ok (internE v) a) :
    (AM.st (internE v) a).memos.abs1C = a.memos.abs1C :=
  (keeps_internE_ab v).run (AM.run_of_ok _ _ hok)

/-! ## The `mk_*` and `intern_bvar` under `ArenaA` -/

theorem mkApp_okA (m : Mem) (a : AState) (hA : ArenaA m a) (f x r : Word) (m' : Mem)
    (hI : mkAppW m f x = some (r, m')) :
    AM.ok (internE (.app (decE f) (decE x))) a ∧
    ArenaA m' (AM.st (internE (.app (decE f) (decE x))) a) ∧
    AM.res (internE (.app (decE f) (decE x))) a = decE r := by
  obtain ⟨hok, hD, hres⟩ := mkApp_ok m a hA.1 f x r m' hI
  exact ⟨hok, ⟨hD, hA.2.across (mkAppW_frameA m m' f x r hI) (by decide) (by decide)
    (internE_abs1C _ a hok)⟩, hres⟩

theorem mkLam_okA (m : Mem) (a : AState) (hA : ArenaA m a) (t b r : Word) (m' : Mem)
    (hI : mkLamW m t b = some (r, m')) :
    AM.ok (internE (.lam (decE t) (decE b))) a ∧
    ArenaA m' (AM.st (internE (.lam (decE t) (decE b))) a) ∧
    AM.res (internE (.lam (decE t) (decE b))) a = decE r := by
  obtain ⟨hok, hD, hres⟩ := mkLam_ok m a hA.1 t b r m' hI
  exact ⟨hok, ⟨hD, hA.2.across (mkLamW_frameA m m' t b r hI) (by decide) (by decide)
    (internE_abs1C _ a hok)⟩, hres⟩

theorem mkForall_okA (m : Mem) (a : AState) (hA : ArenaA m a) (t b r : Word) (m' : Mem)
    (hI : mkForallW m t b = some (r, m')) :
    AM.ok (internE (.forallE (decE t) (decE b))) a ∧
    ArenaA m' (AM.st (internE (.forallE (decE t) (decE b))) a) ∧
    AM.res (internE (.forallE (decE t) (decE b))) a = decE r := by
  obtain ⟨hok, hD, hres⟩ := mkForall_ok m a hA.1 t b r m' hI
  exact ⟨hok, ⟨hD, hA.2.across (mkForallW_frameA m m' t b r hI) (by decide) (by decide)
    (internE_abs1C _ a hok)⟩, hres⟩

theorem mkLet_okA (m : Mem) (a : AState) (hA : ArenaA m a) (t v b r : Word) (m' : Mem)
    (hI : mkLetW m t v b = some (r, m')) :
    AM.ok (internE (.letE (decE t) (decE v) (decE b))) a ∧
    ArenaA m' (AM.st (internE (.letE (decE t) (decE v) (decE b))) a) ∧
    AM.res (internE (.letE (decE t) (decE v) (decE b))) a = decE r := by
  obtain ⟨hok, hD, hres⟩ := mkLet_ok m a hA.1 t v b r m' hI
  exact ⟨hok, ⟨hD, hA.2.across (mkLetW_frameA m m' t v b r hI) (by decide) (by decide)
    (internE_abs1C _ a hok)⟩, hres⟩

theorem mkProj_okA (m : Mem) (a : AState) (hA : ArenaA m a) (n i e r : Word) (m' : Mem)
    (hI : mkProjW m n i e = some (r, m')) :
    AM.ok (internE (.proj (decI n) i.toNat (decE e))) a ∧
    ArenaA m' (AM.st (internE (.proj (decI n) i.toNat (decE e))) a) ∧
    AM.res (internE (.proj (decI n) i.toNat (decE e))) a = decE r := by
  obtain ⟨hok, hD, hres⟩ := mkProj_ok m a hA.1 n i e r m' hI
  exact ⟨hok, ⟨hD, hA.2.across (mkProjW_frameA m m' n i e r hI) (by decide) (by decide)
    (internE_abs1C _ a hok)⟩, hres⟩

theorem internBVar_A (m : Mem) (a : AState) (hA : ArenaA m a) (u r : Word) (m' : Mem)
    (hI : binternW m u = some (r, m')) :
    AM.ok (internE (.bvar u.toNat)) a ∧ ArenaA m' (AM.st (internE (.bvar u.toNat)) a) ∧
    AM.res (internE (.bvar u.toNat)) a = decE r := by
  obtain ⟨hok, hD, hres⟩ := internBVar_D m a hA.1 u r m' hI
  exact ⟨hok, ⟨hD, hA.2.across (binternW_frameA m m' u r hI) (by decide) (by decide)
    (internE_abs1C _ a hok)⟩, hres⟩

/-! ## The view of an `fvar`'s index -/

theorem viewFVarIdx_ok (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (hv : viewOK m h 26) :
    a.store.viewFVarIdx (decE h) = some (rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2)).toNat := by
  obtain ⟨k, hk, hi, -⟩ := node_of m a h fvarSch FVRecRel fvhash (·.fvars) _ hR.fvar hv.2
  simp only [EStore.viewFVarIdx, EStore.persGetFVarIdx]
  rw [proj_tier m a hR h hh (fun t i => t.getFVarIdx i) hv.1]
  simp only [ETables.getFVarIdx, Tbl.node?, decE_idx]
  rw [hk]; simp [hi]

/-! ## `fr_memo` writes only its memo (L side) -/

/-- The write set of `fr_go`/`fr_node`/`fr_memo`'s models. -/
abbrev FrFrame (m m' : Mem) : Prop := MemFrame [FRMEMO] [46, 47] m m'

theorem frSet_frame (m m' : Mem) (h r r' : Word) (hb : frSet m h r = some (r', m')) :
    FrFrame m m' := by
  unfold frSet at hb
  split at hb
  · cases hb
  rename_i m₁ hs
  simp only [Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨-, rfl⟩ := hb
  exact (msetG_frame frSch frSch_wf _ _ _ _ _ hs).mono (by simp) (by simp)

/-- A model result whose memory, if any, is a `FrFrame` of `m`. -/
def FrOK (m : Mem) (o : Option (Word × Mem)) : Prop := ∀ r m', o = some (r, m') → FrFrame m m'

theorem FrOK.app {n : Nat} {m : Mem} {y : Word} {o : Option (Word × Mem)} (ho : FrOK m o)
    (hw : ∀ m₁, FrOK m₁ (frW n m₁ y)) : FrOK m (frAppK₁ n y o) := by
  intro r m' hb
  cases o with
  | none => cases hb
  | some p =>
    obtain ⟨x, m₁⟩ := p
    simp only [frAppK₁] at hb
    cases h2 : frW n m₁ y with
    | none => simp [h2, frAppK₁.frAppK₂] at hb
    | some q =>
      obtain ⟨y', m₂⟩ := q
      simp only [h2, frAppK₁.frAppK₂, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨-, rfl⟩ := hb
      exact (ho _ _ rfl).trans (hw m₁ _ _ h2)

theorem FrOK.bind {n : Nat} {m : Mem} {y : Word} {o : Option (Word × Mem)} (ho : FrOK m o)
    (hw : ∀ m₁, FrOK m₁ (frW n m₁ y)) : FrOK m (frBindK₁ n y o) := by
  intro r m' hb
  cases o with
  | none => cases hb
  | some p =>
    obtain ⟨x, m₁⟩ := p
    simp only [frBindK₁] at hb
    cases h2 : frW n m₁ y with
    | none => simp [h2, frBindK₁.frBindK₂] at hb
    | some q =>
      obtain ⟨y', m₂⟩ := q
      simp only [h2, frBindK₁.frBindK₂, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨-, rfl⟩ := hb
      exact (ho _ _ rfl).trans (hw m₁ _ _ h2)

theorem FrOK.letE {n : Nat} {m : Mem} {y z : Word} {o : Option (Word × Mem)} (ho : FrOK m o)
    (hw : ∀ m₁ w, FrOK m₁ (frW n m₁ w)) : FrOK m (frLetK₁ n y z o) := by
  intro r m' hb
  cases o with
  | none => cases hb
  | some p =>
    obtain ⟨x, m₁⟩ := p
    simp only [frLetK₁] at hb
    cases h2 : frW n m₁ y with
    | none => simp [h2, frLetK₁.frLetK₂] at hb
    | some q =>
      obtain ⟨y', m₂⟩ := q
      simp only [h2, frLetK₁.frLetK₂] at hb
      cases h3 : frW n m₂ z with
      | none => simp [h3, frLetK₁.frLetK₃] at hb
      | some o =>
        obtain ⟨z', m₃⟩ := o
        simp only [h3, frLetK₁.frLetK₃, Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨-, rfl⟩ := hb
        exact ((ho _ _ rfl).trans (hw m₁ _ _ _ h2)).trans (hw m₂ _ _ _ h3)

theorem frW_frame (n : Nat) : (∀ m h, FrOK m (frW n m h)) ∧ (∀ m h, FrOK m (frNodeW n m h)) := by
  induction n with
  | zero => exact ⟨fun _ _ _ _ hb => by simp [frW] at hb, fun _ _ _ _ hb => by simp [frNodeW] at hb⟩
  | succ n ih =>
    refine ⟨fun m h r m' hb => ?_, fun m h r m' hb => ?_⟩
    · rw [frW] at hb
      split at hb
      · cases hb
      split at hb
      · simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨-, rfl⟩ := hb
        exact MemFrame.refl _ _ _
      split at hb
      · cases hb
      rename_i r₁ m₁ hn
      exact (ih.2 _ _ _ _ hn).trans (frSet_frame _ _ _ _ _ hb)
    · have dead : ∀ c, ¬ viewOK m h c → rdW (m.arr64 CTL) (c + tierW h) ≤ idxW h ∨
          (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) := by
        intro c hv
        by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
        · exact .inr hs
        · exact .inl (UInt64.not_lt.mp fun hl => hv ⟨hs, hl⟩)
      have leaf : ∀ c, viewOK m h c → frNodeW (n + 1) m h = some (0, m) → FrFrame m m' →
          FrFrame m m' := fun _ _ _ h => h
      clear leaf
      by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
      · rw [frNodeW, if_pos hs] at hb; cases hb
      have tagCase : ∀ (c : Word), (viewOK m h c → FrFrame m m') →
          (rdW (m.arr64 CTL) (c + tierW h) ≤ idxW h → FrFrame m m') → FrFrame m m' := by
        intro c h1 h2
        by_cases hc : rdW (m.arr64 CTL) (c + tierW h) ≤ idxW h
        · exact h2 hc
        · exact h1 ⟨hs, UInt64.not_le.mp hc⟩
      have none_of : ∀ (hn : frNodeW (n + 1) m h = none), False := fun hn => by
        rw [hn] at hb; cases hb
      have done0 : frNodeW (n + 1) m h = some (0, m) → FrFrame m m' := fun e => by
        rw [e] at hb; simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨-, rfl⟩ := hb; exact MemFrame.refl _ _ _
      by_cases g0 : h >>> 28 = 0
      · refine tagCase 22 (fun hv => done0 (frNodeW_bvar n m h g0 hv)) (fun hc => (none_of ?_).elim)
        rw [frNodeW]; simp [hs, g0, hc]
      by_cases g1 : h >>> 28 = 1
      · refine tagCase 26 (fun hv => ?_) (fun hc => (none_of ?_).elim)
        · by_cases h1 : rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2) + 1 = 0
          · exact (none_of (by rw [frNodeW]; simp [hs, g1, h1, UInt64.not_le.mpr hv.2])).elim
          · rw [frNodeW_fvar n m h hv g1 h1] at hb; simp only [Option.some.injEq, Prod.mk.injEq] at hb
            obtain ⟨-, rfl⟩ := hb; exact MemFrame.refl _ _ _
        · rw [frNodeW]; simp [hs, g1, hc]
      by_cases g4 : h >>> 28 = 4
      · refine tagCase 4 (fun hv => ?_) (fun hc => (none_of ?_).elim)
        · rw [frNodeW_app n m h hv g4] at hb
          exact FrOK.app (ih.1 _ _) (fun m₁ => ih.1 m₁ _) _ _ hb
        · rw [frNodeW]; simp [hs, g4, hc]
      by_cases g5 : h >>> 28 = 5
      · refine tagCase 28 (fun hv => ?_) (fun hc => (none_of ?_).elim)
        · rw [frNodeW_lam n m h hv g5] at hb
          exact FrOK.bind (ih.1 _ _) (fun m₁ => ih.1 m₁ _) _ _ hb
        · rw [frNodeW]; simp [hs, g5, hc]
      by_cases g6 : h >>> 28 = 6
      · refine tagCase 30 (fun hv => ?_) (fun hc => (none_of ?_).elim)
        · rw [frNodeW_forall n m h hv g6] at hb
          exact FrOK.bind (ih.1 _ _) (fun m₁ => ih.1 m₁ _) _ _ hb
        · rw [frNodeW]; simp [hs, g6, hc]
      by_cases g9 : h >>> 28 = 9
      · refine tagCase 32 (fun hv => ?_) (fun hc => (none_of ?_).elim)
        · rw [frNodeW_proj n m h hv g9] at hb
          exact ih.1 _ _ _ _ hb
        · rw [frNodeW]; simp [hs, g9, hc]
      by_cases g7 : h >>> 28 = 7
      · refine tagCase 20 (fun hv => ?_) (fun hc => (none_of ?_).elim)
        · rw [frNodeW_let n m h hv g7] at hb
          exact FrOK.letE (ih.1 _ _) (fun m₁ w => ih.1 m₁ w) _ _ hb
        · rw [frNodeW]; simp [hs, g7, hc]
      by_cases g2 : h >>> 28 = 2
      · refine tagCase 16 (fun hv => done0 (frNodeW_sort n m h g2 hv)) (fun hc => (none_of ?_).elim)
        rw [frNodeW]; simp [hs, g2, hc]
      by_cases g3 : h >>> 28 = 3
      · refine tagCase 18 (fun hv => done0 (frNodeW_const n m h g3 hv)) (fun hc => (none_of ?_).elim)
        rw [frNodeW]; simp [hs, g3, hc]
      by_cases g8 : h >>> 28 = 8
      · refine tagCase 2 (fun hv => done0 (frNodeW_lit n m h g8 hv)) (fun hc => (none_of ?_).elim)
        rw [frNodeW]; simp [hs, g8, hc]
      exact (none_of (by rw [frNodeW]; simp [hs, g0, g1, g4, g5, g6, g9, g7, g2, g3, g8])).elim

theorem frMemoW_frame (n : Nat) (m m' : Mem) (h r : Word) (hb : frMemoW n m h = some (r, m')) :
    FrFrame m m' := by
  unfold frMemoW at hb
  split at hb
  · cases hb
  cases hw : frW n (mclearG frSch m) h with
  | none => simp [hw, frClrK] at hb
  | some p =>
    obtain ⟨r₁, m₁⟩ := p
    simp only [hw, frClrK] at hb
    split at hb
    · cases hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨-, rfl⟩ := hb
    exact (((mclearG_frame frSch m).mono (by simp) (by simp)).trans
      ((frW_frame n).1 _ _ _ _ hw)).trans ((mclearG_frame frSch m₁).mono (by simp) (by simp))

/-! ## `fvarRangeMemo` keeps the store and `abs1C` (twin side) -/

/-- What the `fvarBC` walk leaves alone. -/
def fsp (a : AState) : EStore × Std.HashMap (EIdx × Nat) EIdx := (a.store, a.memos.abs1C)

theorem keeps_fvarBSet_fsp (k : EIdx) (v : Nat) : Keeps fsp (fvarBSet k v) := by
  unfold Keeps; intro a r a' h; cases h; rfl
theorem keeps_fvarBClear_fsp : Keeps fsp fvarBClear := by
  unfold Keeps; intro a r a' h; cases h; rfl

theorem keeps_fvarRangeGo_fsp (F : Nat) : ∀ h, Keeps fsp (fvarRangeGo F h) := by
  induction F with
  | zero => intro h; rw [fvarRangeGo_zero]; exact Keeps.fail _
  | succ F ih =>
    intro h; rw [fvarRangeGo_succ]
    repeat' (first
      | exact Keeps.pure _ | exact Keeps.fail _ | exact ih _
      | exact keeps_view _ | exact keeps_fvarBGet _ | exact keeps_fvarBSet_fsp _ _
      | (unfold failDanglingE) | (dsimp only)
      | with_reducible apply Keeps.bind | intro _
      | split | unfold fvarRangeArmApp | unfold fvarRangeArmBind | unfold fvarRangeArmLet)

theorem keeps_fvarRangeMemo_fsp (F : Nat) (e : EIdx) : Keeps fsp (fvarRangeMemo F e) := by
  unfold fvarRangeMemo
  exact Keeps.bind keeps_fvarBClear_fsp fun _ => Keeps.bind (keeps_fvarRangeGo_fsp F e) fun _ =>
    Keeps.bind keeps_fvarBClear_fsp fun _ => Keeps.pure _

/-! ## The cut-off: `ab_fvb` refines `fvarB` -/

theorem fvarB_run (F : Nat) (e : EIdx) (a : AState) :
    (fvarB F e).run a =
      (if (fvarOfData (a.store.derived e)).toNat == satRange then (fvarRangeMemo F e).run a
       else .ok ((fvarOfData (a.store.derived e)).toNat, a)) := by
  simp only [fvarB, StateT.run_bind, derivedE_run, except_ok_bind]
  split <;> rfl

/-- **`ab_fvb`'s model refines `fvarB`** at every arena fuel `F + 1 ≥ n`, under `ArenaA`. -/
theorem fvbW_ok (n F : Nat) (hF : n ≤ F + 1) (m m' : Mem) (a : AState) (hA : ArenaA m a)
    (h x : Word) (hh : h.toNat < 2 ^ 32) (hb : fvbW n m h = some (x, m')) :
    ∃ a', (fvarB F (decE h)).run a = .ok (x.toNat, a') ∧ ArenaA m' a' := by
  obtain ⟨n, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by cases n <;> simp_all [fvbW]⟩
  have hd := derFW_ok m a hA.1.1 hA.1.2 h hh
  rw [fvarB_run, ← hd]
  by_cases hs : derFW m h = 32767
  · rw [fvbW_sat n m h hs] at hb
    have hs' : ((derFW m h).toNat == satRange) = true := by rw [hs]; rfl
    rw [if_pos hs']
    obtain ⟨n, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by cases n <;> simp_all [fvbN]⟩
    rw [fvbN_succ] at hb
    obtain ⟨a', ha', hR'⟩ := frMemoW_correct n F (by omega) m m' a hA.1.1 h x hh hb
    have hk := (keeps_fvarRangeMemo_fsp F (decE h)).run ha'
    simp only [fsp, Prod.mk.injEq] at hk
    have hf := frMemoW_frame n m m' h x hb
    exact ⟨a', ha', ⟨hR', DerR.of_store m' a a' (DerR.frameM _ _ m m' hf (by decide) a hA.1.2) hk.1⟩,
      hA.2.across hf (by decide) (by decide) hk.2⟩
  · rw [fvbW_pk n m h hs] at hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    have hs' : ((derFW m h).toNat == satRange) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro e; apply hs; apply UInt64.toNat_inj.mp; rw [e]; rfl
    rw [if_neg (by simp [hs'])]
    exact ⟨a, rfl, hA⟩

end L.Arena
