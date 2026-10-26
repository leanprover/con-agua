import ConAgua.Arena.Abs1Spec
import ConAgua.Arena.Inst1Refine
import ConAgua.Arena.FVarRangeRefine
import ConAgua.Arena.Keeps
import ConAgua.Arena.SimLib
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
    MemFrame [AREC, ASLOT, ADER, AREC + 256, ASLOT + 256, ADER + 256] [4, 5] m m' := by
  unfold mkAppW at hI; split at hI
  · cases hI
  exact (mkK_frame appCS_wf (by decide) hI).mono (by simp [ConsSch.wset, appCS, appSch, AREC, ASLOT, ADER]) (by simp [appCS, appSch])

theorem mkLamW_frameA (m m' : Mem) (f a r : Word) (hI : mkLamW m f a = some (r, m')) :
    MemFrame [LAREC, LASLOT, LADER, LAREC + 256, LASLOT + 256, LADER + 256] [28, 29] m m' := by
  unfold mkLamW at hI; split at hI
  · cases hI
  exact (mkK_frame lamCS_wf (by decide) hI).mono (by simp [ConsSch.wset, lamCS, lamSch, LAREC, LASLOT, LADER]) (by simp [lamCS, lamSch])

theorem mkForallW_frameA (m m' : Mem) (f a r : Word) (hI : mkForallW m f a = some (r, m')) :
    MemFrame [FAREC, FASLOT, FADER, FAREC + 256, FASLOT + 256, FADER + 256] [30, 31] m m' := by
  unfold mkForallW at hI; split at hI
  · cases hI
  exact (mkK_frame forallCS_wf (by decide) hI).mono (by simp [ConsSch.wset, forallCS, forallSch, FAREC, FASLOT, FADER]) (by simp [forallCS, forallSch])

theorem mkLetW_frameA (m m' : Mem) (t v b r : Word) (hI : mkLetW m t v b = some (r, m')) :
    MemFrame [LEREC, LESLOT, LEDER, LEREC + 256, LESLOT + 256, LEDER + 256] [20, 21] m m' := by
  unfold mkLetW at hI; split at hI
  · cases hI
  exact (mkK_frame letCS_wf (by decide) hI).mono (by simp [ConsSch.wset, letCS, letSch, LEREC, LESLOT, LEDER]) (by simp [letCS, letSch])

theorem mkProjW_frameA (m m' : Mem) (n i e r : Word) (hI : mkProjW m n i e = some (r, m')) :
    MemFrame [PJREC, PJSLOT, PJDER, PJREC + 256, PJSLOT + 256, PJDER + 256] [32, 33] m m' := by
  unfold mkProjW at hI; split at hI
  · cases hI
  exact (mkK_frame projCS_wf (by decide) hI).mono (by simp [ConsSch.wset, projCS, projSch, PJREC, PJSLOT, PJDER]) (by simp [projCS, projSch])

theorem binternW_frameA (m m' : Mem) (u r : Word) (hI : binternW m u = some (r, m')) :
    MemFrame [BREC, BSLOT, BREC + 256, BSLOT + 256] [22, 23] m m' := by
  exact (consInternM_frame bvarCS_wf hI).mono (by simp [ConsSch.wset, bvarCS])
    (by simp [bvarCS, bvarSch])

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
    (hv : viewOK m h FVAR) :
    a.store.viewFVarIdx (decE h) = some (tfld m FVAR (tierW h) (idxW h) 0).toNat := by
  obtain ⟨k, hk, hi, -⟩ := node_of m a h fvarCS FVRecRel (·.fvars) _ hR.fvar hv.2
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
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
  exact (msetG_frame frSch frSch_wf _ _ _ _ _ hs).mono (by simp) (by simp)

/-- A model result whose memory, if any, is a `FrFrame` of `m`. -/
def FrOK (m : Mem) (o : Option (Word × Mem)) : Prop := ∀ r m', o = some (r, m') → FrFrame m m'

theorem FrOK.app {n : Nat} {m : Mem} {c y : Word} {o : Option (Word × Mem)} (ho : FrOK m o)
    (hw : ∀ m₁, FrOK m₁ (frW n m₁ y c)) : FrOK m (frAppK₁ n c y o) :=
  MPost.bindK rfl (fun _ _ => rfl) ho fun _ m₁ h1 =>
    MPost.bindK (K := frAppK₁.frAppK₂ _) rfl (fun _ _ => rfl) (hw m₁)
      fun _ _ h2 => MPost.ret (h1.trans h2)

theorem FrOK.bind {n : Nat} {m : Mem} {c y : Word} {o : Option (Word × Mem)} (ho : FrOK m o)
    (hw : ∀ m₁, FrOK m₁ (frW n m₁ y c)) : FrOK m (frBindK₁ n c y o) :=
  MPost.bindK rfl (fun _ _ => rfl) ho fun _ m₁ h1 =>
    MPost.bindK (K := frBindK₁.frBindK₂ _) rfl (fun _ _ => rfl) (hw m₁)
      fun _ _ h2 => MPost.ret (h1.trans h2)

theorem FrOK.letE {n : Nat} {m : Mem} {c y z : Word} {o : Option (Word × Mem)} (ho : FrOK m o)
    (hw : ∀ m₁ w, FrOK m₁ (frW n m₁ w c)) : FrOK m (frLetK₁ n c y z o) :=
  MPost.bindK rfl (fun _ _ => rfl) ho fun _ m₁ h1 =>
    MPost.bindK (K := frLetK₁.frLetK₂ _ _ _ _) rfl (fun _ _ => rfl) (hw m₁ _) fun _ m₂ h2 =>
    MPost.bindK (K := frLetK₁.frLetK₃ _ _) rfl (fun _ _ => rfl) (hw m₂ _) fun _ _ h3 =>
    MPost.ret ((h1.trans h2).trans h3)

theorem frW_frame (n : Nat) :
    (∀ m h c, FrOK m (frW n m h c)) ∧ (∀ m h c, FrOK m (frNodeW n m h c)) := by
  induction n with
  | zero =>
    exact ⟨fun _ _ _ _ _ hb => by simp [frW] at hb, fun _ _ _ _ _ hb => by simp [frNodeW] at hb⟩
  | succ n ih =>
    refine ⟨fun m h c r m' hb => ?_, fun m h c r m' hb => ?_⟩
    · rw [frW] at hb
      split at hb
      · cases hb
      split at hb
      · cases hb
      split at hb
      · simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨-, rfl⟩ := hb
        exact MemFrame.refl _ _ _
      split at hb
      · cases hb
      rename_i r₁ m₁ hn
      exact (ih.2 _ _ _ _ _ hn).trans (frSet_frame _ _ _ _ _ hb)
    · have dead : ∀ S : TRec, ¬ viewOK m h S → tcnt m S (tierW h) ≤ idxW h ∨
          (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) := by
        intro S hv
        by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
        · exact .inr hs
        · exact .inl (UInt64.not_lt.mp fun hl => hv ⟨hs, hl⟩)
      have leaf : ∀ S, viewOK m h S → frNodeW (n + 1) m h c = some (0, m) → FrFrame m m' →
          FrFrame m m' := fun _ _ _ h => h
      clear leaf
      have hs : ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) := fun hs => by rw [frNodeW, if_pos hs] at hb; cases hb
      have tagCase : ∀ (S : TRec), (viewOK m h S → FrFrame m m') →
          (tcnt m S (tierW h) ≤ idxW h → FrFrame m m') → FrFrame m m' := by
        intro S h1 h2
        by_cases hc : tcnt m S (tierW h) ≤ idxW h
        · exact h2 hc
        · exact h1 ⟨hs, UInt64.not_le.mp hc⟩
      have none_of : ∀ (hn : frNodeW (n + 1) m h c = none), False := fun hn => by
        rw [hn] at hb; cases hb
      have done0 : frNodeW (n + 1) m h c = some (0, m) → FrFrame m m' := fun e => by
        rw [e] at hb; simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨-, rfl⟩ := hb; exact MemFrame.refl _ _ _
      by_cases g0 : h >>> 28 = 0
      · refine tagCase BVAR (fun hv => done0 (frNodeW_bvar n m h c g0 hv)) (fun hc => (none_of ?_).elim)
        rw [frNodeW]; simp [hs, g0, hc]
      by_cases g1 : h >>> 28 = 1
      · refine tagCase FVAR (fun hv => ?_) (fun hc => (none_of ?_).elim)
        · by_cases h1 : tfld m FVAR (tierW h) (idxW h) 0 + 1 = 0
          · exact (none_of (by rw [frNodeW]; simp [hs, g1, h1, UInt64.not_le.mpr hv.2])).elim
          · rw [frNodeW_fvar n m h c hv g1 h1] at hb; simp only [Option.some.injEq, Prod.mk.injEq] at hb
            obtain ⟨-, rfl⟩ := hb; exact MemFrame.refl _ _ _
        · rw [frNodeW]; simp [hs, g1, hc]
      by_cases g4 : h >>> 28 = 4
      · refine tagCase APP (fun hv => ?_) (fun hc => (none_of ?_).elim)
        · rw [frNodeW_app n m h c hv g4] at hb
          exact FrOK.app (ih.1 _ _ _) (fun m₁ => ih.1 m₁ _ _) _ _ hb
        · rw [frNodeW]; simp [hs, g4, hc]
      by_cases g5 : h >>> 28 = 5
      · refine tagCase LAM (fun hv => ?_) (fun hc => (none_of ?_).elim)
        · rw [frNodeW_lam n m h c hv g5] at hb
          exact FrOK.bind (ih.1 _ _ _) (fun m₁ => ih.1 m₁ _ _) _ _ hb
        · rw [frNodeW]; simp [hs, g5, hc]
      by_cases g6 : h >>> 28 = 6
      · refine tagCase FORALL (fun hv => ?_) (fun hc => (none_of ?_).elim)
        · rw [frNodeW_forall n m h c hv g6] at hb
          exact FrOK.bind (ih.1 _ _ _) (fun m₁ => ih.1 m₁ _ _) _ _ hb
        · rw [frNodeW]; simp [hs, g6, hc]
      by_cases g9 : h >>> 28 = 9
      · refine tagCase PROJ (fun hv => ?_) (fun hc => (none_of ?_).elim)
        · rw [frNodeW_proj n m h c hv g9] at hb
          exact ih.1 _ _ _ _ _ hb
        · rw [frNodeW]; simp [hs, g9, hc]
      by_cases g7 : h >>> 28 = 7
      · refine tagCase LET (fun hv => ?_) (fun hc => (none_of ?_).elim)
        · rw [frNodeW_let n m h c hv g7] at hb
          exact FrOK.letE (ih.1 _ _ _) (fun m₁ w => ih.1 m₁ w _) _ _ hb
        · rw [frNodeW]; simp [hs, g7, hc]
      by_cases g2 : h >>> 28 = 2
      · refine tagCase SORT (fun hv => done0 (frNodeW_sort n m h c g2 hv)) (fun hc => (none_of ?_).elim)
        rw [frNodeW]; simp [hs, g2, hc]
      by_cases g3 : h >>> 28 = 3
      · refine tagCase CONST (fun hv => done0 (frNodeW_const n m h c g3 hv)) (fun hc => (none_of ?_).elim)
        rw [frNodeW]; simp [hs, g3, hc]
      by_cases g8 : h >>> 28 = 8
      · refine tagCase LIT (fun hv => done0 (frNodeW_lit n m h c g8 hv)) (fun hc => (none_of ?_).elim)
        rw [frNodeW]; simp [hs, g8, hc]
      exact (none_of (by rw [frNodeW]; simp [hs, g0, g1, g4, g5, g6, g9, g7, g2, g3, g8])).elim

theorem frMemoW_frame (n : Nat) (m m' : Mem) (h c r : Word) (hb : frMemoW n m h c = some (r, m')) :
    FrFrame m m' := by
  unfold frMemoW at hb
  split at hb
  · cases hb
  rcases hw : frW n (mclearG frSch m) h c with _ | ⟨r₁, m₁⟩ <;> simp only [hw, frClrK, reduceCtorEq] at hb
  split at hb
  · cases hb
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
  exact (((mclearG_frame frSch m).mono (by simp) (by simp)).trans
    ((frW_frame n).1 _ _ _ _ _ hw)).trans ((mclearG_frame frSch m₁).mono (by simp) (by simp))

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

/-- **`ab_fvb`'s model refines `fvarB`** at the counter's fuel `f.toNat`, under `ArenaA`. -/
theorem fvbW_ok (n : Nat) (m m' : Mem) (a : AState) (hA : ArenaA m a)
    (h f x : Word) (hh : h.toNat < 2 ^ 32) (hb : fvbW n m h f = some (x, m')) :
    ∃ a', (fvarB f.toNat (decE h)).run a = .ok (x.toNat, a') ∧ ArenaA m' a' := by
  obtain ⟨n, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by cases n <;> simp_all [fvbW]⟩
  have hd := derFW_ok m a hA.1.1 hA.1.2 h hh
  rw [fvarB_run, ← hd]
  by_cases hs : derFW m h = 32767
  · rw [fvbW_sat n m h f hs] at hb
    have hs' : ((derFW m h).toNat == satRange) = true := by rw [hs]; rfl
    rw [if_pos hs']
    obtain ⟨n, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by cases n <;> simp_all [fvbN]⟩
    rw [fvbN_succ] at hb
    obtain ⟨a', ha', hR'⟩ := frMemoW_correct n m m' a hA.1.1 h f x hh hb
    have hk := (keeps_fvarRangeMemo_fsp f.toNat (decE h)).run ha'
    simp only [fsp, Prod.mk.injEq] at hk
    have hf := frMemoW_frame n m m' h f x hb
    exact ⟨a', ha', ⟨hR', DerR.of_store m' a a' (DerR.frameM _ _ m m' hf (by decide) a hA.1.2) hk.1⟩,
      hA.2.across hf (by decide) (by decide) hk.2⟩
  · rw [fvbW_pk n m h f hs] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    have hs' : ((derFW m h).toNat == satRange) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro e; apply hs; apply UInt64.toNat_inj.mp; rw [e]; rfl
    rw [if_neg (by simp [hs'])]
    exact ⟨a, rfl, hA⟩

/-- **`ab_fvb(h, f)` refines the arena's `fvarB f.toNat h` under `ArenaA`.** -/
@[refines ConRon.Arena.fvarB]
theorem abFvb_refines (p : Prog) (hp : AbsProg p) (n : Nat) (s₀ : St)
    (a₀ : AState) (hA : ArenaA s₀.mem a₀) (h f : Word) (hh : h.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "ab_fvb" [h, f]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (fvarB f.toNat (decE h)) a₀ ∧
      ArenaA s'.mem (AM.st (fvarB f.toNat (decE h)) a₀) ∧
      AM.res (fvarB f.toNat (decE h)) a₀ = (r.headD 0).toNat; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun (abFvb_spec p hp n s₀ h f)
  subst hs
  obtain ⟨a', ha', hA'⟩ := fvbW_ok n _ _ a₀ hA h f _ hh hI
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ ha'
  exact ⟨hloc, hok, hst ▸ hA', hres⟩

/-! ## The arms' probe, rebuild and tail -/

theorem decE_inj (x y : Word) (hx : x.toNat < 2 ^ 32) (hy : y.toNat < 2 ^ 32) (e : decE x = decE y) :
    x = y := by
  rw [← word_decE x hx, ← word_decE y hy, e]

theorem atail_ok (op : AM EIdx) (mkr : Option (Word × Mem)) (a₂ : AState) (h c r : Word) (m' : Mem)
    (hh : h.toNat < 2 ^ 32)
    (hmk : ∀ r₃ m₃, mkr = some (r₃, m₃) →
      AM.ok op a₂ ∧ ArenaA m₃ (AM.st op a₂) ∧ AM.res op a₂ = decE r₃)
    (hb : asetK h c mkr = some (r, m')) :
    ∃ a', (do let r ← op; abs1Set (decE h, c.toNat) r; pure r : AM EIdx).run a₂ =
      .ok (decE r, a') ∧ ArenaA m' a' := by
  cases h3 : mkr with
  | none => simp [h3, asetK] at hb
  | some q =>
    obtain ⟨r₃, m₃⟩ := q
    rw [h3] at hb
    simp only [asetK] at hb
    cases h4 : msetG abSch m₃ h c r₃ with
    | none => simp [h4] at hb
    | some m₄ =>
      simp only [h4, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      obtain ⟨hok, hA₃, hres⟩ := hmk r₃ m₃ h3
      refine ⟨_, ?_, ArenaA.amemo_set m₃ m₄ _ hA₃ h c r₃ hh h4⟩
      simp only [StateT.run_bind, AM.run_of_ok _ _ hok, hres, except_ok_bind, abs1Set_run]; rfl

theorem aprobe_ok (armW : Option (Word × Mem)) (miss : AM EIdx) (m m' : Mem) (a : AState)
    (hA : ArenaA m a) (h c r : Word) (hh : h.toNat < 2 ^ 32)
    (hhit : mfindG abSch m h c ≠ [] → (mfindG abSch m h c).headD 0 ≠ 0 →
      armW = some (rdW (m.arr64 ABMEMO) ((mfindG abSch m h c).tail.headD 0 * 4 + 3), m))
    (hnone : mfindG abSch m h c = [] → armW = none)
    (hmiss : mfindG abSch m h c ≠ [] → (mfindG abSch m h c).headD 0 = 0 → armW = some (r, m') →
      ∃ a', miss.run a = .ok (decE r, a') ∧ ArenaA m' a')
    (hb : armW = some (r, m')) :
    ∃ a', (do
        match ← abs1Get (decE h, c.toNat) with
        | some r => pure r
        | none => miss : AM EIdx).run a = .ok (decE r, a') ∧ ArenaA m' a' := by
  rw [StateT.run_bind, abs1Get_run, except_ok_bind]
  have hr : ¬ mfindG abSch m h c = [] := fun hr => by rw [hnone hr] at hb; cases hb
  by_cases hh0 : (mfindG abSch m h c).headD 0 ≠ 0
  · rw [hhit hr hh0] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    rw [show a.memos.abs1C[(decE h, c.toNat)]? = _ from
      memoRG_hit abSch lfKey decE m _ hA.2 h c hr hh0 hh]
    exact ⟨a, rfl, hA⟩
  · simp only [ne_eq, Decidable.not_not] at hh0
    rw [show a.memos.abs1C[(decE h, c.toNat)]? = none from
      memoRG_miss abSch lfKey decE m _ hA.2 h c hh hr hh0]
    exact hmiss hr hh0 hb

/-- **A rebuild on change**: `h` itself when the model's words came back equal (then so did the
twin's handles), else the model's interning, which the twin's `op` refines. -/
theorem rb_ok (op : AM EIdx) (same : Bool) (P : Prop) [Decidable P] (mkr : Option (Word × Mem))
    (m : Mem) (a : AState) (hA : ArenaA m a) (h r : Word) (m' : Mem)
    (hsame : P → same = true)
    (hnew : ¬ P → mkr = some (r, m') →
      same = false ∧ AM.ok op a ∧ ArenaA m' (AM.st op a) ∧ AM.res op a = decE r)
    (hb : (if P then some (h, m) else mkr) = some (r, m')) :
    AM.ok (if same then pure (decE h) else op) a ∧
      ArenaA m' (AM.st (if same then pure (decE h) else op) a) ∧
      AM.res (if same then pure (decE h) else op) a = decE r := by
  by_cases hP : P
  · rw [if_pos hP] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    rw [hsame hP]
    exact ⟨trivial, hA, rfl⟩
  · rw [if_neg hP] at hb
    obtain ⟨hs, hok, hA', hres⟩ := hnew hP hb
    rw [hs]
    exact ⟨hok, hA', hres⟩

theorem mkAppW_lt (m : Mem) (x y r : Word) (m' : Mem) (hI : mkAppW m x y = some (r, m')) :
    x.toNat < 2 ^ 32 ∧ y.toNat < 2 ^ 32 := by
  unfold mkAppW at hI; split at hI
  · cases hI
  · rename_i hg; exact or_shr32 x y (by simpa using hg)
theorem mkLamW_lt (m : Mem) (x y r : Word) (m' : Mem) (hI : mkLamW m x y = some (r, m')) :
    x.toNat < 2 ^ 32 ∧ y.toNat < 2 ^ 32 := by
  unfold mkLamW at hI; split at hI
  · cases hI
  · rename_i hg; exact or_shr32 x y (by simpa using hg)
theorem mkForallW_lt (m : Mem) (x y r : Word) (m' : Mem) (hI : mkForallW m x y = some (r, m')) :
    x.toNat < 2 ^ 32 ∧ y.toNat < 2 ^ 32 := by
  unfold mkForallW at hI; split at hI
  · cases hI
  · rename_i hg; exact or_shr32 x y (by simpa using hg)
theorem mkLetW_lt (m : Mem) (x y z r : Word) (m' : Mem) (hI : mkLetW m x y z = some (r, m')) :
    x.toNat < 2 ^ 32 ∧ y.toNat < 2 ^ 32 ∧ z.toNat < 2 ^ 32 := by
  unfold mkLetW at hI; split at hI
  · cases hI
  · rename_i hg
    obtain ⟨hxy, hz⟩ := or_shr32 (x ||| y) z (by simpa using hg)
    obtain ⟨hx, hy⟩ := or_lt32 x y hxy
    exact ⟨hx, hy, hz⟩
theorem mkProjW_lt (m : Mem) (n i x r : Word) (m' : Mem) (hI : mkProjW m n i x = some (r, m')) :
    x.toNat < 2 ^ 32 := by
  unfold mkProjW at hI; split at hI
  · cases hI
  · rename_i hg; exact (or_shr32 n x (by simpa using hg)).2

/-! ## The twin's dispatcher, named -/

/-- The part of `abstract1Go` after the cut-off: the dispatch on the tag. -/
def absNodeA (d F : Nat) (h : EIdx) (k : Nat) : AM EIdx :=
  let tg := h.tag
  if tg == ETag.app then abstract1ArmApp d F h k
  else if ETag.isBind tg then abstract1ArmBind d F h k
  else if tg == ETag.fvar then abstract1ArmFVar d h k
  else if tg == ETag.letE then abstract1ArmLet d F h k
  else if tg == ETag.proj then abstract1ArmProj d F h k
  else pure h

theorem abstract1Go_succ' (d F : Nat) (h : EIdx) (k : Nat) :
    abstract1Go d (F + 1) h k = (do
      let fb ← fvarB F h
      if fb ≤ d then pure h else absNodeA d F h k) := by
  rw [abstract1Go_succ]; rfl

theorem viewFVarIdx_run (h : EIdx) (a : AState) :
    (viewFVarIdx h).run a = .ok (a.store.viewFVarIdx h, a) := rfl

/-! ## The statements, by fuel -/

/-- What `abs_go`'s model at L fuel `n` and counter `fu` says about the arena walk at the twin
fuel `fu.toNat` (exactly: the counter is the twin's `fuel`, any L fuel). -/
def AGoOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (h k d fu r : Word), ArenaA m a →
    h.toNat < 2 ^ 32 → absW n m h k d fu = some (r, m') →
    ∃ a', (abstract1Go d.toNat fu.toNat (decE h) k.toNat).run a = .ok (decE r, a') ∧ ArenaA m' a'

/-- The same for `ab_node` and the dispatch. -/
def ANodeOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (h k d fu r : Word), ArenaA m a →
    h.toNat < 2 ^ 32 → absNodeW n m h k d fu = some (r, m') →
    ∃ a', (absNodeA d.toNat fu.toNat (decE h) k.toNat).run a = .ok (decE r, a') ∧ ArenaA m' a'

/-- The arena arm `arm` refines the L arm `armW` at `h`, under `ArenaA`. -/
def AArmRef (n : Nat) (armW : Nat → Mem → Word → Word → Word → Word → Option (Word × Mem))
    (arm : AM EIdx) (m m' : Mem) (a : AState) (h k d fu r : Word) : Prop :=
  armW n m h k d fu = some (r, m') → ∃ a', arm.run a = .ok (decE r, a') ∧ ArenaA m' a'

/-- The five arms, each at its tag. -/
def AArmOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (h k d fu r : Word), ArenaA m a →
    h.toNat < 2 ^ 32 →
    (h >>> 28 = 4 → AArmRef n absAppW (abstract1ArmApp d.toNat fu.toNat (decE h) k.toNat) m m' a h k d fu r) ∧
    (h >>> 28 = 5 → AArmRef n absLamW (abstract1ArmBind d.toNat fu.toNat (decE h) k.toNat) m m' a h k d fu r) ∧
    (h >>> 28 = 6 →
      AArmRef n absForallW (abstract1ArmBind d.toNat fu.toNat (decE h) k.toNat) m m' a h k d fu r) ∧
    (h >>> 28 = 7 → AArmRef n absLetW (abstract1ArmLet d.toNat fu.toNat (decE h) k.toNat) m m' a h k d fu r) ∧
    (h >>> 28 = 9 → AArmRef n absProjW (abstract1ArmProj d.toNat fu.toNat (decE h) k.toNat) m m' a h k d fu r)

theorem agoOK_succ (n : Nat) (ih : ANodeOK n) : AGoOK (n + 1) := by
  intro m m' a h k d fu r hA hh hb
  have hfu : ¬ fu = 0 := fun hfu => by rw [absW] at hb; simp [hfu] at hb
  rw [absW_eq n m h k d fu hfu] at hb
  rw [ctrW_toNat fu hfu, abstract1Go_succ']
  refine SimD.exists (Sim.bindD rfl (fun _ _ => rfl)
    (Sim.ofD fun x m₁ e => fvbW_ok n m m₁ a hA h (fu - 1) x hh e) fun x m₁ a₁ hA₁ => ?_) hb
  rw [acutK_some]
  by_cases hc : x ≤ d
  · rw [if_pos hc, if_pos (UInt64.le_iff_toNat_le.mp hc)]; exact Sim.ret ⟨rfl, hA₁⟩
  · rw [if_neg hc, if_neg (fun e => hc (UInt64.le_iff_toNat_le.mpr e))]
    exact Sim.ofD fun r m' hb => ih m₁ m' a₁ h k d (fu - 1) r hA₁ hh hb

theorem anodeOK_succ (n : Nat) (ih : AArmOK n) : ANodeOK (n + 1) := by
  intro m m' a h k d fu r hA hh hb
  have arm := ih m m' a h k d fu r hA hh
  have t4 : h >>> 28 = 4 ↔ (h >>> 28).toUInt32 = 4 := by simpa using tag_iff h 4 hh (by decide)
  have t5 : h >>> 28 = 5 ↔ (h >>> 28).toUInt32 = 5 := by simpa using tag_iff h 5 hh (by decide)
  have t6 : h >>> 28 = 6 ↔ (h >>> 28).toUInt32 = 6 := by simpa using tag_iff h 6 hh (by decide)
  have t1 : h >>> 28 = 1 ↔ (h >>> 28).toUInt32 = 1 := by simpa using tag_iff h 1 hh (by decide)
  have t7 : h >>> 28 = 7 ↔ (h >>> 28).toUInt32 = 7 := by simpa using tag_iff h 7 hh (by decide)
  have t9 : h >>> 28 = 9 ↔ (h >>> 28).toUInt32 = 9 := by simpa using tag_iff h 9 hh (by decide)
  simp only [absNodeA, decE_tag h hh]
  simp only [ETag.app, ETag.isBind, ETag.lam, ETag.forallE, ETag.fvar, ETag.letE, ETag.proj,
    beq_iff_eq, Bool.or_eq_true] at *
  by_cases g4 : h >>> 28 = 4
  · rw [absNodeW_app n m h k d fu g4] at hb
    simp only [show (h >>> 28).toUInt32 = 4 from (t4.mp g4), ↓reduceIte]
    exact arm.1 g4 hb
  have g4' : ¬ (h >>> 28).toUInt32 = 4 := fun e => g4 (t4.mpr e)
  by_cases g5 : h >>> 28 = 5
  · rw [absNodeW_lam n m h k d fu g5] at hb
    simp only [g4', show (h >>> 28).toUInt32 = 5 from (t5.mp g5), true_or, ↓reduceIte]
    exact arm.2.1 g5 hb
  have g5' : ¬ (h >>> 28).toUInt32 = 5 := fun e => g5 (t5.mpr e)
  by_cases g6 : h >>> 28 = 6
  · rw [absNodeW_forall n m h k d fu g6] at hb
    simp only [g4', g5', show (h >>> 28).toUInt32 = 6 from (t6.mp g6), or_true, ↓reduceIte]
    exact arm.2.2.1 g6 hb
  have g6' : ¬ (h >>> 28).toUInt32 = 6 := fun e => g6 (t6.mpr e)
  simp only [g4', g5', g6', or_self, ↓reduceIte]
  by_cases g1 : h >>> 28 = 1
  · simp only [show (h >>> 28).toUInt32 = 1 from (t1.mp g1), ↓reduceIte]
    have hs : ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) := fun hs => by rw [absNodeW] at hb; simp [g4, g5, g6, g1, hs] at hb
    have hv : viewOK m h FVAR := ⟨hs, UInt64.not_le.mp fun hc => by
      rw [absNodeW] at hb; simp [g4, g5, g6, g1, hs, hc] at hb⟩
    rw [abstract1ArmFVar, StateT.run_bind, viewFVarIdx_run, viewFVarIdx_ok m a hA.1.1 h hh hv]
    simp only [except_ok_bind]
    by_cases he : tfld m FVAR (tierW h) (idxW h) 0 = d
    · rw [absNodeW_fvar_eq n m h k d fu hv g1 he] at hb
      obtain ⟨hok, hA', hres⟩ := internBVar_A m a hA _ r m' hb
      simp only [he, ↓reduceIte, internBVarE]
      rw [AM.run_of_ok _ _ hok, hres]; exact ⟨_, rfl, hA'⟩
    · rw [absNodeW_fvar_ne n m h k d fu hv g1 he] at hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      have he' : ¬ (tfld m FVAR (tierW h) (idxW h) 0).toNat = d.toNat :=
        fun e => he (UInt64.toNat_inj.mp e)
      simp only [he', ↓reduceIte]; exact ⟨a, rfl, hA⟩
  have g1' : ¬ (h >>> 28).toUInt32 = 1 := fun e => g1 (t1.mpr e)
  simp only [g1', ↓reduceIte]
  by_cases g7 : h >>> 28 = 7
  · rw [absNodeW_let n m h k d fu g7] at hb
    simp only [show (h >>> 28).toUInt32 = 7 from (t7.mp g7), ↓reduceIte]
    exact arm.2.2.2.1 g7 hb
  have g7' : ¬ (h >>> 28).toUInt32 = 7 := fun e => g7 (t7.mpr e)
  simp only [g7', ↓reduceIte]
  by_cases g9 : h >>> 28 = 9
  · rw [absNodeW_proj n m h k d fu g9] at hb
    simp only [show (h >>> 28).toUInt32 = 9 from (t9.mp g9), ↓reduceIte]
    exact arm.2.2.2.2 g9 hb
  have g9' : ¬ (h >>> 28).toUInt32 = 9 := fun e => g9 (t9.mpr e)
  simp only [g9', ↓reduceIte]
  rw [absNodeW_leaf n m h k d fu g1 g4 g5 g6 g7 g9] at hb
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
  exact ⟨a, rfl, hA⟩

/-! ## The arms -/

section arms
variable (n : Nat) (ih : AGoOK n) (m m' : Mem) (a : AState) (hA : ArenaA m a)
  (h k d fu r : Word) (hh : h.toNat < 2 ^ 32)
include ih hA hh

theorem aappArm_ok (hg : h >>> 28 = 4) :
    AArmRef (n + 1) absAppW (abstract1ArmApp d.toNat fu.toNat (decE h) k.toNat) m m' a h k d fu r := by
  intro hb
  rw [abstract1ArmApp]
  refine aprobe_ok _ _ m m' a hA h k r hh (absAppW_hit n m h k d fu)
    (fun hr => by rw [absAppW]; simp [hr]) (fun hr hh0 hb => ?_) hb
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [absAppW] at hb; simp only [ne_eq] at hs; simp only [hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, not_false_eq_true, and_self, reduceCtorEq] at hb
  have hv : viewOK m h APP := ⟨hs, UInt64.not_le.mp fun hc => by
    rw [absAppW] at hb; simp only [ne_eq] at hs; simp only [hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, hc, not_false_eq_true, and_self, and_true, reduceCtorEq] at hb⟩
  obtain ⟨-, hfw, haw⟩ := view_app m a hA.1.1 h hh hv hg
  rw [absAppW_miss n m h k d fu hr hh0 hv] at hb
  rw [StateT.run_bind, viewApp_run, viewApp_ok m a hA.1.1 h hh hv, except_ok_bind]
  refine SimD.exists (Sim.bindD rfl (fun _ _ => rfl)
    (Sim.ofD fun x m₁ e => ih m m₁ a _ k d fu x hA hfw e) fun x m₁ a₁ hA₁ => ?_) hb
  refine Sim.bindD (K := aappK₁.aappK₂ h k _ _ x) rfl (fun _ _ => rfl)
    (Sim.ofD fun y m₂ e => ih m₁ m₂ a₁ _ k d fu y hA₁ haw e) fun y m₂ a₂ hA₂ => ?_
  refine Sim.ofD fun r m' hb => atail_ok (internRebuiltApp (decE h)
      (decE x == decE (tfld m APP (tierW h) (idxW h) 0) && decE y == decE (tfld m APP (tierW h) (idxW h) 1)) (decE x) (decE y))
      _ a₂ h k r m' hh (fun r₃ m₃ hr₃ => by
    unfold internRebuiltApp
    refine rb_ok _ _ _ _ m₂ a₂ hA₂ h r₃ m₃ (fun ⟨e1, e2⟩ => by simp [e1, e2]) (fun hn hI => ?_) hr₃
    obtain ⟨hx, hy⟩ := mkAppW_lt m₂ x y r₃ m₃ hI
    refine ⟨?_, mkApp_okA m₂ a₂ hA₂ x y r₃ m₃ hI⟩
    rcases Decidable.em (decE x = decE (tfld m APP (tierW h) (idxW h) 0)) with e1 | e1
    · have e2 : decE y ≠ decE (tfld m APP (tierW h) (idxW h) 1) :=
        fun e2 => hn ⟨decE_inj _ _ hx hfw e1, decE_inj _ _ hy haw e2⟩
      simp [e1, e2]
    · simp [e1]) hb

theorem alamArm_ok (hg : h >>> 28 = 5) :
    AArmRef (n + 1) absLamW (abstract1ArmBind d.toNat fu.toNat (decE h) k.toNat) m m' a h k d fu r := by
  intro hb
  have hk1 : ¬ k + 1 = 0 := fun hk1 => by rw [absLamW] at hb; simp [hk1] at hb
  rw [abstract1ArmBind]
  refine aprobe_ok _ _ m m' a hA h k r hh (absLamW_hit n m h k d fu hk1)
    (fun hr => by rw [absLamW]; simp [hk1, hr]) (fun hr hh0 hb => ?_) hb
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [absLamW] at hb; simp only [ne_eq] at hs; simp only [hk1, hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, not_false_eq_true, and_self, reduceCtorEq] at hb
  have hv : viewOK m h LAM := ⟨hs, UInt64.not_le.mp fun hc => by
    rw [absLamW] at hb; simp only [ne_eq] at hs; simp only [hk1, hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, hc, not_false_eq_true, and_self, and_true, reduceCtorEq] at hb⟩
  obtain ⟨-, hfw, haw⟩ := view_lam m a hA.1.1 h hh hv hg
  rw [absLamW_miss n m h k d fu hk1 hr hh0 hv] at hb
  rw [StateT.run_bind, viewBind_run, viewBind_lam m a hA.1.1 h hh hv hg, except_ok_bind]
  refine SimD.exists (Sim.bindD rfl (fun _ _ => rfl)
    (Sim.ofD fun x m₁ e => ih m m₁ a _ k d fu x hA hfw e) fun x m₁ a₁ hA₁ => ?_) hb
  refine Sim.bindD (K := alamK₁.alamK₂ h k _ _ x) rfl (fun _ _ => rfl) (Sim.ofD fun y m₂ e => by
    simpa only [succW_toNat k hk1] using ih m₁ m₂ a₁ _ (k + 1) d fu y hA₁ haw e)
        fun y m₂ a₂ hA₂ => ?_
  have hbind : ∀ t b, internBindE (decE h).tag t b = internE (.lam t b) := by
    intro t b; simp [internBindE, decE_tag h hh, hg, ETag.lam, internE]
  refine Sim.ofD fun r m' hb => atail_ok (internRebuiltBind (decE h)
      (decE x == decE (tfld m LAM (tierW h) (idxW h) 0) && decE y == decE (tfld m LAM (tierW h) (idxW h) 1)) (decE h).tag (decE x) (decE y))
      _ a₂ h k r m' hh (fun r₃ m₃ hr₃ => by
    unfold internRebuiltBind
    rw [hbind]
    refine rb_ok _ _ _ _ m₂ a₂ hA₂ h r₃ m₃ (fun ⟨e1, e2⟩ => by simp [e1, e2]) (fun hn hI => ?_) hr₃
    obtain ⟨hx, hy⟩ := mkLamW_lt m₂ x y r₃ m₃ hI
    refine ⟨?_, mkLam_okA m₂ a₂ hA₂ x y r₃ m₃ hI⟩
    rcases Decidable.em (decE x = decE (tfld m LAM (tierW h) (idxW h) 0)) with e1 | e1
    · have e2 : decE y ≠ decE (tfld m LAM (tierW h) (idxW h) 1) :=
        fun e2 => hn ⟨decE_inj _ _ hx hfw e1, decE_inj _ _ hy haw e2⟩
      simp [e1, e2]
    · simp [e1]) hb

theorem aforallArm_ok (hg : h >>> 28 = 6) :
    AArmRef (n + 1) absForallW (abstract1ArmBind d.toNat fu.toNat (decE h) k.toNat) m m' a h k d fu r := by
  intro hb
  have hk1 : ¬ k + 1 = 0 := fun hk1 => by rw [absForallW] at hb; simp [hk1] at hb
  rw [abstract1ArmBind]
  refine aprobe_ok _ _ m m' a hA h k r hh (absForallW_hit n m h k d fu hk1)
    (fun hr => by rw [absForallW]; simp [hk1, hr]) (fun hr hh0 hb => ?_) hb
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [absForallW] at hb; simp only [ne_eq] at hs; simp only [hk1, hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, not_false_eq_true, and_self, reduceCtorEq] at hb
  have hv : viewOK m h FORALL := ⟨hs, UInt64.not_le.mp fun hc => by
    rw [absForallW] at hb; simp only [ne_eq] at hs; simp only [hk1, hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, hc, not_false_eq_true, and_self, and_true, reduceCtorEq] at hb⟩
  obtain ⟨-, hfw, haw⟩ := view_forall m a hA.1.1 h hh hv hg
  rw [absForallW_miss n m h k d fu hk1 hr hh0 hv] at hb
  rw [StateT.run_bind, viewBind_run, viewBind_forall m a hA.1.1 h hh hv hg, except_ok_bind]
  refine SimD.exists (Sim.bindD rfl (fun _ _ => rfl)
    (Sim.ofD fun x m₁ e => ih m m₁ a _ k d fu x hA hfw e) fun x m₁ a₁ hA₁ => ?_) hb
  refine Sim.bindD (K := afaK₁.afaK₂ h k _ _ x) rfl (fun _ _ => rfl) (Sim.ofD fun y m₂ e => by
    simpa only [succW_toNat k hk1] using ih m₁ m₂ a₁ _ (k + 1) d fu y hA₁ haw e)
        fun y m₂ a₂ hA₂ => ?_
  have hbind : ∀ t b, internBindE (decE h).tag t b = internE (.forallE t b) := by
    intro t b; simp [internBindE, decE_tag h hh, hg, ETag.lam, internE]
  refine Sim.ofD fun r m' hb => atail_ok (internRebuiltBind (decE h)
      (decE x == decE (tfld m FORALL (tierW h) (idxW h) 0) && decE y == decE (tfld m FORALL (tierW h) (idxW h) 1)) (decE h).tag (decE x) (decE y))
      _ a₂ h k r m' hh (fun r₃ m₃ hr₃ => by
    unfold internRebuiltBind
    rw [hbind]
    refine rb_ok _ _ _ _ m₂ a₂ hA₂ h r₃ m₃ (fun ⟨e1, e2⟩ => by simp [e1, e2]) (fun hn hI => ?_) hr₃
    obtain ⟨hx, hy⟩ := mkForallW_lt m₂ x y r₃ m₃ hI
    refine ⟨?_, mkForall_okA m₂ a₂ hA₂ x y r₃ m₃ hI⟩
    rcases Decidable.em (decE x = decE (tfld m FORALL (tierW h) (idxW h) 0)) with e1 | e1
    · have e2 : decE y ≠ decE (tfld m FORALL (tierW h) (idxW h) 1) :=
        fun e2 => hn ⟨decE_inj _ _ hx hfw e1, decE_inj _ _ hy haw e2⟩
      simp [e1, e2]
    · simp [e1]) hb

theorem aletArm_ok (hg : h >>> 28 = 7) :
    AArmRef (n + 1) absLetW (abstract1ArmLet d.toNat fu.toNat (decE h) k.toNat) m m' a h k d fu r := by
  intro hb
  have hk1 : ¬ k + 1 = 0 := fun hk1 => by rw [absLetW] at hb; simp [hk1] at hb
  rw [abstract1ArmLet]
  refine aprobe_ok _ _ m m' a hA h k r hh (absLetW_hit n m h k d fu hk1)
    (fun hr => by rw [absLetW]; simp [hk1, hr]) (fun hr hh0 hb => ?_) hb
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [absLetW] at hb; simp only [ne_eq] at hs; simp only [hk1, hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, not_false_eq_true, and_self, reduceCtorEq] at hb
  have hv : viewOK m h LET := ⟨hs, UInt64.not_le.mp fun hc => by
    rw [absLetW] at hb; simp only [ne_eq] at hs; simp only [hk1, hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, hc, not_false_eq_true, and_self, and_true, reduceCtorEq] at hb⟩
  obtain ⟨-, htw, hvw, hbw⟩ := view_let m a hA.1.1 h hh hv hg
  rw [absLetW_miss n m h k d fu hk1 hr hh0 hv] at hb
  rw [StateT.run_bind, viewLet_run, viewLet_ok m a hA.1.1 h hh hv, except_ok_bind]
  refine SimD.exists (Sim.bindD rfl (fun _ _ => rfl)
    (Sim.ofD fun x m₁ e => ih m m₁ a _ k d fu x hA htw e) fun x m₁ a₁ hA₁ => ?_) hb
  refine Sim.bindD (K := aleK₁.aleK₂ n h k d fu _ _ _ x) rfl (fun _ _ => rfl)
    (Sim.ofD fun y m₂ e => ih m₁ m₂ a₁ _ k d fu y hA₁ hvw e) fun y m₂ a₂ hA₂ => ?_
  refine Sim.bindD (K := aleK₁.aleK₃ h k _ _ _ x y) rfl (fun _ _ => rfl) (Sim.ofD fun z m₃ e => by
    simpa only [succW_toNat k hk1] using ih m₂ m₃ a₂ _ (k + 1) d fu z hA₂ hbw e)
        fun z m₃ a₃ hA₃ => ?_
  refine Sim.ofD fun r m' hb => atail_ok (internRebuiltLetE (decE h)
      (decE x == decE (tfld m LET (tierW h) (idxW h) 0) && decE y == decE (tfld m LET (tierW h) (idxW h) 1) && decE z == decE (tfld m LET (tierW h) (idxW h) 2))
      (decE x) (decE y) (decE z)) _ a₃ h k r m' hh (fun r₄ m₄ hr₄ => by
    unfold internRebuiltLetE internLetEE
    refine rb_ok _ _ _ _ m₃ a₃ hA₃ h r₄ m₄ (fun ⟨e1, e2, e3⟩ => by simp [e1, e2, e3])
      (fun hn hI => ?_) hr₄
    obtain ⟨hx, hy, hz⟩ := mkLetW_lt m₃ x y z r₄ m₄ hI
    refine ⟨?_, mkLet_okA m₃ a₃ hA₃ x y z r₄ m₄ hI⟩
    rcases Decidable.em (decE x = decE (tfld m LET (tierW h) (idxW h) 0)) with e1 | e1
    · rcases Decidable.em (decE y = decE (tfld m LET (tierW h) (idxW h) 1))
        with e2 | e2
      · have e3 : decE z ≠ decE (tfld m LET (tierW h) (idxW h) 2) :=
          fun e3 => hn ⟨decE_inj _ _ hx htw e1, decE_inj _ _ hy hvw e2, decE_inj _ _ hz hbw e3⟩
        simp [e1, e2, e3]
      · simp [e1, e2]
    · simp [e1]) hb

theorem aprojArm_ok (hg : h >>> 28 = 9) :
    AArmRef (n + 1) absProjW (abstract1ArmProj d.toNat fu.toNat (decE h) k.toNat) m m' a h k d fu r := by
  intro hb
  rw [abstract1ArmProj]
  refine aprobe_ok _ _ m m' a hA h k r hh (absProjW_hit n m h k d fu)
    (fun hr => by rw [absProjW]; simp [hr]) (fun hr hh0 hb => ?_) hb
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [absProjW] at hb; simp only [ne_eq] at hs; simp only [hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, not_false_eq_true, and_self, reduceCtorEq] at hb
  have hv : viewOK m h PROJ := ⟨hs, UInt64.not_le.mp fun hc => by
    rw [absProjW] at hb; simp only [ne_eq] at hs; simp only [hr, hh0, ne_eq, not_true_eq_false, ↓reduceIte, hs, hc, not_false_eq_true, and_self, and_true, reduceCtorEq] at hb⟩
  obtain ⟨-, -, hew⟩ := view_proj m a hA.1.1 h hh hv hg
  rw [absProjW_miss n m h k d fu hr hh0 hv] at hb
  rw [StateT.run_bind, viewProj_run, viewProj_ok m a hA.1.1 h hh hv, except_ok_bind]
  refine SimD.exists (Sim.bindD rfl (fun _ _ => rfl)
    (Sim.ofD fun x m₁ e => ih m m₁ a _ k d fu x hA hew e) fun x m₁ a₁ hA₁ => ?_) hb
  refine Sim.ofD fun r m' hb => atail_ok (internRebuiltProj (decE h) (decE x == decE (tfld m PROJ (tierW h) (idxW h) 2))
      (decI (tfld m PROJ (tierW h) (idxW h) 0)) (tfld m PROJ (tierW h) (idxW h) 1).toNat (decE x)) _ a₁ h k r m' hh (fun r₃ m₃ hr₃ => by
    unfold internRebuiltProj internProjE
    refine rb_ok _ _ _ _ m₁ a₁ hA₁ h r₃ m₃ (fun e1 => by simp [e1]) (fun hn hI => ?_) hr₃
    have hx := mkProjW_lt m₁ _ _ x r₃ m₃ hI
    refine ⟨?_, mkProj_okA m₁ a₁ hA₁ _ _ x r₃ m₃ hI⟩
    have e1 : decE x ≠ decE (tfld m PROJ (tierW h) (idxW h) 2) :=
      fun e1 => hn (decE_inj _ _ hx hew e1)
    simp [e1]) hb

end arms

theorem aarmOK_succ (n : Nat) (ih : AGoOK n) : AArmOK (n + 1) := by
  intro m m' a h k d fu r hA hh
  exact ⟨aappArm_ok n ih m m' a hA h k d fu r hh, alamArm_ok n ih m m' a hA h k d fu r hh,
    aforallArm_ok n ih m m' a hA h k d fu r hh, aletArm_ok n ih m m' a hA h k d fu r hh,
    aprojArm_ok n ih m m' a hA h k d fu r hh⟩

/-- **The model of `abs_go` refines `abstract1Go`** at the counter's fuel, at every L fuel. -/
theorem absOK (n : Nat) : AGoOK n ∧ ANodeOK n ∧ AArmOK n := by
  induction n with
  | zero =>
    refine ⟨fun _ _ _ _ _ _ _ _ _ _ hb => by simp [absW] at hb,
      fun _ _ _ _ _ _ _ _ _ _ hb => by simp [absNodeW] at hb,
      fun _ _ _ _ _ _ _ _ _ _ => ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    intro _ hb <;> simp [absAppW, absLamW, absForallW, absLetW, absProjW] at hb
  | succ n ih => exact ⟨agoOK_succ n ih.2.1, anodeOK_succ n ih.2.2, aarmOK_succ n ih.1⟩

/-! ## The entry `abs_entry` refines `abstract1Fast` -/

theorem absFast_run (F : Nat) (e : EIdx) (d k : Nat) (a : AState) :
    (abstract1Fast F e d k).run a =
      ((abstract1Go d F e k).run (withAC a ∅) >>= fun p => .ok (p.1, withAC p.2 ∅)) := by
  simp only [abstract1Fast, StateT.run_bind, abs1Clear_run, except_ok_bind]
  cases (abstract1Go d F e k).run (withAC a ∅) <;> rfl

theorem absEntryW_correct (n : Nat) (m m' : Mem) (a : AState) (hA : ArenaA m a)
    (e d k r : Word) (he : e.toNat < 2 ^ 32) (hb : absEntryW n m e d k = some (r, m')) :
    ∃ a', (abstract1Fast coreWalkFuel (decE e) d.toNat k.toNat).run a = .ok (decE r, a') ∧
      ArenaA m' a' ∧ r.toNat < 2 ^ 32 := by
  simp only [absEntryW] at hb
  have h0 : ¬ rdW (m.arr64 CTL) 48 + 2 = 0 := fun h0 => by simp [h0] at hb
  simp only [h0, ↓reduceIte] at hb
  have hA₀ := ArenaA.amemo_clear m a hA h0
  cases hw : absW n (mclearG abSch m) e k d 4000000000 with
  | none => simp [hw, aclrK] at hb
  | some p =>
    obtain ⟨r₁, m₁⟩ := p
    have h1 : ¬ rdW (m₁.arr64 CTL) 48 + 2 = 0 := fun h1 => by simp [hw, aclrK, h1] at hb
    simp only [hw, aclrK, h1, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    obtain ⟨a₁, ha₁, hA₁⟩ := (absOK n).1 _ _ _ e k d 4000000000 r₁ hA₀ he hw
    rw [coreWalkFuel_toNat] at ha₁
    exact ⟨_, by rw [absFast_run, ha₁, decE_and32]; rfl, ArenaA.amemo_clear m₁ a₁ hA₁ h1,
      and32_lt r₁⟩

/-- **`abs_entry` refines the arena's `abstract1Fast coreWalkFuel` under `ArenaA`**, at every L
fuel (the walk's counter starts at `coreWalkFuel`). -/
@[refines ConRon.Arena.abstract1Fast]
theorem absEntry_refines (p : Prog) (hp : AbsProg p) (hpe : p.lookup "abs_entry" = some absEntry)
    (n : Nat) (s₀ : St) (a₀ : AState) (hA : ArenaA s₀.mem a₀) (e d k : Word)
    (he : e.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "abs_entry" [e, d, k]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (abstract1Fast coreWalkFuel (decE e) d.toNat k.toNat) a₀ ∧
      ArenaA s'.mem (AM.st (abstract1Fast coreWalkFuel (decE e) d.toNat k.toNat) a₀) ∧
      AM.res (abstract1Fast coreWalkFuel (decE e) d.toNat k.toNat) a₀ = decE (r.headD 0) ∧
      (r.headD 0).toNat < 2 ^ 32; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun (absEntry_spec p hp hpe n s₀ e d k)
  subst hs
  obtain ⟨a', ha', hA', hlt⟩ := absEntryW_correct n _ _ a₀ hA e d k _ he hI
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ ha'
  exact ⟨hloc, hok, hst ▸ hA', hres, hlt⟩

end L.Arena
