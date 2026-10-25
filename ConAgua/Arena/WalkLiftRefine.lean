import ConAgua.Arena.WalkLift
import ConAgua.Arena.Abs1Refine
import ConAgua.Arena.BvarBRefine
import ConAgua.Arena.LiftRefine
import ConAgua.Arena.Keeps
import ConAgua.Arena.WriteSets
import ConAgua.Census.Attr

/-!
# `instantiate1_lift_fast` refines the arena's `instantiate1LiftFast` (lane `tails`)

`LiftRefine.lean`'s proof for the walk `i1l_go` (`WalkLift.lean`), with two callees inside:

* **The memo tier `ArenaI := ArenaD ∧ I1R`.** `inst1LC` lives outside `MemosR`, as `abs1C`
  (`Abs1Refine.lean`): its relation `I1R` (`MemoRG i1lSch lfKey decE`, array `ILFM` = 51,
  `CTL[52]`) rides next to `ArenaD`, kept by the callees' L frames (the `mk_*`' and
  `intern_bvar`'s from `Abs1Refine.lean`, `bvar_b`'s `BbFrame`, `lift_entry`'s `liftA`/`liftC` by
  `liftW_frame` below) and on the twin's side by `Keeps` of `inst1LC` (`bvarB` and
  `liftLooseBVarsFast` change other memos only, `internE` only the store).
* **The cut-off through `bvar_b`** (`bvbW_ok`, at the walk's decremented counter, as the twin's
  `bvarB fuel h`), then the **view** per tag (`View.lean`), as `lift_go`'s dispatcher; the `bvar d`
  leaf runs `lift_entry` at the remaining fuel (`liftEntryW_correct`, the twin's
  `liftLooseBVarsFast fuel d 0 v`).

The counter word `fu` is the twin's `fuel` exactly; the statements hold at
every L fuel.
-/

open ConRon.Arena ConLeche
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

theorem i1lSch_wf : i1lSch.WF := ⟨by decide, by decide⟩

/-! ## The `instantiate1Lift` memo tier -/

/-- The `inst1LC` relation. -/
def I1R (m : Mem) (a : AState) : Prop := MemoRG i1lSch lfKey decE m a.memos.inst1LC

/-- `ArenaD` and the `instantiate1Lift` memo. -/
def ArenaI (m : Mem) (a : AState) : Prop := ArenaD m a ∧ I1R m a

/-- The arena state with the `instantiate1Lift` memo replaced. -/
def withI1C (a : AState) (mp : Std.HashMap (EIdx × Nat) EIdx) : AState :=
  { a with memos := { a.memos with inst1LC := mp } }

theorem inst1LGet_run (x : EIdx × Nat) (a : AState) :
    (inst1LGet x).run a = .ok (a.memos.inst1LC[x]?, a) := rfl

theorem inst1LSet_run (x : EIdx × Nat) (r : EIdx) (a : AState) :
    (inst1LSet x r).run a = .ok ((), withI1C a (a.memos.inst1LC.insert x r)) := rfl

theorem inst1LClear_run (a : AState) : inst1LClear.run a = .ok ((), withI1C a ∅) := rfl

theorem not_arenaCtl_52 : (52 : Word) ∉ arenaCtl := by
  simp [arenaCtl, storeCtl, memoCtl]
theorem not_arenaCtl_53 : (53 : Word) ∉ arenaCtl := by
  simp [arenaCtl, storeCtl, memoCtl]

/-- `ArenaR` and `DerR` do not read `inst1LC`. -/
theorem ArenaD.withI1C {m : Mem} {a : AState} (hD : ArenaD m a)
    (mp : Std.HashMap (EIdx × Nat) EIdx) : ArenaD m (withI1C a mp) :=
  ⟨hD.1.with_memos (MemFrame.refl [] [] m) (by simp) (by simp)
    ⟨hD.1.memos.bvar, hD.1.memos.lift, hD.1.memos.inst1, hD.1.memos.fvar⟩,
    DerR.of_store m a _ hD.2 rfl⟩

theorem ArenaI.imemo_set (m m' : Mem) (a : AState) (hA : ArenaI m a) (h c v : Word)
    (hh : h.toNat < 2 ^ 32) (hs : msetG i1lSch m h c v = some m') :
    ArenaI m' (withI1C a (a.memos.inst1LC.insert (decE h, c.toNat) (decE v))) := by
  have hf := msetG_frame i1lSch i1lSch_wf m m' h c v hs
  refine ⟨ArenaD.withI1C ⟨hA.1.1.frame (by decide) (by simpa using not_arenaCtl_53) hf,
    DerR.frameM _ _ m m' hf (by decide) _ hA.1.2⟩ _, ?_⟩
  exact memoRG_set i1lSch i1lSch_wf lfKey decE m _ hA.2 h c v hh m' hs

theorem ArenaI.imemo_clear (m : Mem) (a : AState) (hA : ArenaI m a)
    (h0 : rdW (m.arr64 CTL) 52 + 2 ≠ 0) : ArenaI (mclearG i1lSch m) (withI1C a ∅) := by
  have hf := mclearG_frame i1lSch m
  have hC : ∀ x ∈ [i1lSch.cs, i1lSch.cs + 1], x ∉ arenaCtl := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact not_arenaCtl_52
    · exact not_arenaCtl_53
  exact ⟨ArenaD.withI1C ⟨hA.1.1.frame (by decide) hC hf,
      DerR.frameM _ _ m _ hf (by decide) _ hA.1.2⟩ _,
    memoRG_clear i1lSch i1lSch_wf lfKey decE m _ hA.2 h0⟩

/-- **`I1R` survives a writer apart from it, if the twin's memo did not move.** -/
theorem I1R.across {A : List ArrId} {C : List Word} {m m' : Mem} {a a' : AState}
    (hR : I1R m a) (hf : MemFrame A C m m') (hA : ILFM ∉ A) (hC : (52 : Word) ∉ C)
    (he : a'.memos.inst1LC = a.memos.inst1LC) : I1R m' a' := by
  unfold I1R; rw [he]
  exact memoRG_frame i1lSch i1lSch_wf lfKey decE A C hA hC m m' hf _ hR

/-! ## The twin's callees keep `inst1LC` -/

/-- The projection. -/
abbrev pI1 (a : AState) : Std.HashMap (EIdx × Nat) EIdx := a.memos.inst1LC

theorem keeps_internNodeE_i1 (v : ENodeView) : Keeps pI1 (internNodeE v) := by
  prim_keeps internNodeE
theorem keeps_internLamE_i1 (ty b : EIdx) : Keeps pI1 (internLamE ty b) := by
  prim_keeps internLamE
theorem keeps_internForallEE_i1 (ty b : EIdx) : Keeps pI1 (internForallEE ty b) := by
  prim_keeps internForallEE
theorem keeps_internE_i1 (v : ENodeView) : Keeps pI1 (internE v) := by
  cases v <;> simp only [internE] <;>
    first | exact keeps_internNodeE_i1 _ | exact keeps_internLamE_i1 _ _ |
      exact keeps_internForallEE_i1 _ _

theorem keeps_liftSet_i1 (k : EIdx × Nat) (v : EIdx) : Keeps pI1 (liftSet k v) := by
  unfold Keeps; intro a r a' h; cases h; rfl
theorem keeps_liftClear_i1 : Keeps pI1 liftClear := by
  unfold Keeps; intro a r a' h; cases h; rfl
theorem keeps_bvarBSet_i1 (k : EIdx) (v : Nat) : Keeps pI1 (bvarBSet k v) := by
  unfold Keeps; intro a r a' h; cases h; rfl
theorem keeps_bvarBClear_i1 : Keeps pI1 bvarBClear := by
  unfold Keeps; intro a r a' h; cases h; rfl

/-- `keeps_auto` for `pI1` (the memo writes other than `inst1LC`'s keep it). -/
macro "keeps_auto_i1 " "[" arms:ident,* "]" " using " ih:term : tactic => `(tactic| (
  repeat' (first
    | exact Keeps.pure _ | exact Keeps.fail _ | exact $ih _ _ | exact $ih _
    | exact keeps_internE_i1 _ | exact keeps_internLamE_i1 _ _ | exact keeps_internForallEE_i1 _ _
    | exact keeps_view _ | exact keeps_derivedE _
    | exact keeps_liftGet _ | exact keeps_liftSet_i1 _ _
    | exact keeps_bvarBGet _ | exact keeps_bvarBSet_i1 _ _
    | (unfold failDanglingE) | (unfold internBVarE) | (unfold internBindE) | (dsimp only)
    | with_reducible apply Keeps.bind | intro _ | split $[| unfold $arms:ident]* )))

theorem keeps_liftGo_i1 (amount F : Nat) : ∀ h c, Keeps pI1 (liftLooseBVarsGo amount F h c) := by
  induction F with
  | zero => intro h c; rw [liftLooseBVarsGo_zero]; exact Keeps.fail _
  | succ F ih =>
    intro h c; rw [liftLooseBVarsGo_succ]
    keeps_auto_i1 [liftArmApp, liftArmLam, liftArmForallE, liftArmLet, liftArmProj] using ih

theorem keeps_liftFast_i1 (F amount c : Nat) (e : EIdx) :
    Keeps pI1 (liftLooseBVarsFast F amount c e) := by
  unfold liftLooseBVarsFast
  exact Keeps.bind keeps_liftClear_i1 fun _ => Keeps.bind (keeps_liftGo_i1 amount F e c) fun _ =>
    Keeps.bind keeps_liftClear_i1 fun _ => Keeps.pure _

theorem keeps_bvarBoundGo_i1 (F : Nat) : ∀ h, Keeps pI1 (bvarBoundGo F h) := by
  induction F with
  | zero => intro h; rw [bvarBoundGo_zero]; exact Keeps.fail _
  | succ F ih =>
    intro h; rw [bvarBoundGo_succ]
    keeps_auto_i1 [bvarBoundArmApp, bvarBoundArmBind, bvarBoundArmLet] using ih

theorem keeps_bvarB_i1 (F : Nat) (e : EIdx) : Keeps pI1 (bvarB F e) := by
  unfold bvarB
  refine Keeps.bind (keeps_derivedE _) fun _ => ?_
  dsimp only
  split
  · unfold bvarBoundMemo
    exact Keeps.bind keeps_bvarBClear_i1 fun _ => Keeps.bind (keeps_bvarBoundGo_i1 F e) fun _ =>
      Keeps.bind keeps_bvarBClear_i1 fun _ => Keeps.pure _
  · exact Keeps.pure _

/-! ## `lift_entry`'s model writes only `liftA`, `liftC` -/

/-- The write set of the lift walk's models. -/
abbrev LfFrame (m m' : Mem) : Prop := MemFrame liftA liftC m m'

/-- A model result whose memory, if any, is an `LfFrame` of `m`. -/
def LfOK (m : Mem) (o : Option (Word × Mem)) : Prop := ∀ r m', o = some (r, m') → LfFrame m m'

theorem lfSet_frame (m m' : Mem) (h c v : Word) (hs : msetG lfSch m h c v = some m') :
    LfFrame m m' :=
  (msetG_frame lfSch lfSch_wf m m' h c v hs).mono (by simp [liftA, lfSch, LMEMO])
    (by simp [liftC, lfSch])

/-- The shared tail: the rebuilt node recorded in the lift memo. -/
theorem lfTail_frame {m : Mem} {h c : Word} {o : Option (Word × Mem)}
    (ho : LfOK m o) : LfOK m (liftAppW.k_mk_app h c o) := by
  intro r m' hb
  cases h3 : o with
  | none => simp [h3, liftAppW.k_mk_app] at hb
  | some q =>
    obtain ⟨r₃, m₃⟩ := q
    rw [h3] at hb
    have hr : ¬ mfindG lfSch m₃ h c = [] := fun hr => by simp [liftAppW.k_mk_app, hr] at hb
    rw [liftAppW.k_mk_app.arm1 h c r₃ m₃ hr] at hb
    cases h4 : mputG lfSch m₃ h c r₃ ((mfindG lfSch m₃ h c).headD 0)
        ((mfindG lfSch m₃ h c).tail.headD 0) with
    | none => rw [h4] at hb; simp [liftAppW.k_lf_put] at hb
    | some m₄ =>
      rw [h4, liftAppW.k_lf_put.arm1, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      have hs : msetG lfSch m₃ h c r₃ = some m₄ := by rw [msetG, ite_eq_right hr]; exact h4
      exact (ho r₃ m₃ h3).trans (lfSet_frame m₃ m₄ h c r₃ hs)

theorem LfOK.bind {m : Mem} {o : Option (Word × Mem)} {K : Option (Word × Mem) → Option (Word × Mem)}
    {body : Word → Mem → Option (Word × Mem)} (hK : K none = none)
    (hs : ∀ x m₁, K (some (x, m₁)) = body x m₁) (ho : LfOK m o)
    (hb : ∀ x m₁, LfFrame m m₁ → LfOK m (body x m₁)) : LfOK m (K o) := by
  intro r m' h
  rcases h1 : o with _ | ⟨x, m₁⟩ <;> simp only [h1, hK, hs, reduceCtorEq] at h
  exact hb x m₁ (ho x m₁ h1) r m' h

theorem LfOK.trans {m m₁ : Mem} {o : Option (Word × Mem)} (h1 : LfFrame m m₁) (ho : LfOK m₁ o) :
    LfOK m o := fun r m' h => h1.trans (ho r m' h)

theorem mkAppW_lf (m : Mem) (x y : Word) : LfOK m (mkAppW m x y) := fun r m' h =>
  (mkAppW_frameA m m' x y r h).mono (by simp [liftA, AREC, ASLOT, ADER]) (by simp [liftC])
theorem mkLamW_lf (m : Mem) (x y : Word) : LfOK m (mkLamW m x y) := fun r m' h =>
  (mkLamW_frameA m m' x y r h).mono (by simp [liftA, LAREC, LASLOT, LADER]) (by simp [liftC])
theorem mkForallW_lf (m : Mem) (x y : Word) : LfOK m (mkForallW m x y) := fun r m' h =>
  (mkForallW_frameA m m' x y r h).mono (by simp [liftA, FAREC, FASLOT, FADER]) (by simp [liftC])
theorem mkLetW_lf (m : Mem) (x y z : Word) : LfOK m (mkLetW m x y z) := fun r m' h =>
  (mkLetW_frameA m m' x y z r h).mono (by simp [liftA, LEREC, LESLOT, LEDER]) (by simp [liftC])
theorem mkProjW_lf (m : Mem) (a b x : Word) : LfOK m (mkProjW m a b x) := fun r m' h =>
  (mkProjW_frameA m m' a b x r h).mono (by simp [liftA, PJREC, PJSLOT, PJDER]) (by simp [liftC])
theorem binternW_lf (m : Mem) (u : Word) : LfOK m (binternW m u) := fun r m' h =>
  (binternW_frameA m m' u r h).mono (by simp [liftA, BREC, BSLOT]) (by simp [liftC])

theorem lfRet (m : Mem) (h : Word) : LfOK m (some (h, m)) := fun _ _ e => by
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj e); exact MemFrame.refl _ _ _

theorem LfOK.none (m : Mem) : LfOK m none := fun _ _ h => by cases h

theorem LfOK.ite {m : Mem} {p : Prop} [Decidable p] {a b : Option (Word × Mem)} (ha : LfOK m a)
    (hb : LfOK m b) : LfOK m (if p then a else b) := by
  by_cases hp : p
  · rw [if_pos hp]; exact ha
  · rw [if_neg hp]; exact hb

/-- The six lift models write only `liftA`, `liftC`. -/
def LfAll (n : Nat) : Prop :=
  (∀ m h c k fu, LfOK m (liftW n m h c k fu)) ∧ (∀ m h c k fu, LfOK m (liftAppW n m h c k fu)) ∧
  (∀ m h c k fu, LfOK m (liftLamW n m h c k fu)) ∧ (∀ m h c k fu, LfOK m (liftForallW n m h c k fu)) ∧
  (∀ m h c k fu, LfOK m (liftLetW n m h c k fu)) ∧ (∀ m h c k fu, LfOK m (liftProjW n m h c k fu))

theorem liftW_frame (n : Nat) : LfAll n := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro m h c k fu r m' hb <;>
      simp [liftW, liftAppW, liftLamW, liftForallW, liftLetW, liftProjW] at hb
  | succ n ih =>
    obtain ⟨iG, iA, iL, iF, iE, iP⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro m h c k fu
      rw [liftW.eq_def]
      repeat' (first
        | exact LfOK.none m | exact lfRet m h | exact binternW_lf m _
        | exact iA _ _ _ _ _ | exact iL _ _ _ _ _ | exact iF _ _ _ _ _
        | exact iE _ _ _ _ _ | exact iP _ _ _ _ _ | apply LfOK.ite)
    · intro m h c k fu
      rw [liftAppW.eq_def]
      refine LfOK.ite (LfOK.none m) (LfOK.ite (lfRet m _) ?_)
      · refine LfOK.bind (by simp [liftAppW.k_lift_go]) (fun _ _ => by simp only [liftAppW.k_lift_go]; rfl) (iG _ _ _ _ _)
          fun x m₁ h1 => ?_
        refine LfOK.trans h1 (LfOK.bind (by simp [liftAppW.k_lift_go_2]) (fun _ _ => by simp only [liftAppW.k_lift_go_2]; rfl)
          (iG _ _ _ _ _) fun y m₂ h2 => ?_)
        exact LfOK.trans h2 (lfTail_frame (mkAppW_lf m₂ x y))
    · intro m h c k fu
      rw [liftLamW.eq_def]
      refine LfOK.ite (LfOK.none m) (LfOK.ite (LfOK.none m) (LfOK.ite (lfRet m _) ?_))
      · refine LfOK.bind (by simp [liftLamW.k_lift_go]) (fun _ _ => by simp only [liftLamW.k_lift_go]; rfl) (iG _ _ _ _ _)
          fun x m₁ h1 => ?_
        refine LfOK.trans h1 (LfOK.bind (by simp [liftLamW.k_lift_go_2]) (fun _ _ => by simp only [liftLamW.k_lift_go_2]; rfl)
          (iG _ _ _ _ _) fun y m₂ h2 => ?_)
        exact LfOK.trans h2 (lfTail_frame (mkLamW_lf m₂ x y))
    · intro m h c k fu
      rw [liftForallW.eq_def]
      refine LfOK.ite (LfOK.none m) (LfOK.ite (LfOK.none m) (LfOK.ite (lfRet m _) ?_))
      · refine LfOK.bind (by simp [liftForallW.k_lift_go]) (fun _ _ => by simp only [liftForallW.k_lift_go]; rfl)
          (iG _ _ _ _ _) fun x m₁ h1 => ?_
        refine LfOK.trans h1 (LfOK.bind (by simp [liftForallW.k_lift_go_2])
          (fun _ _ => by simp only [liftForallW.k_lift_go_2]; rfl) (iG _ _ _ _ _) fun y m₂ h2 => ?_)
        exact LfOK.trans h2 (lfTail_frame (mkForallW_lf m₂ x y))
    · intro m h c k fu
      rw [liftLetW.eq_def]
      refine LfOK.ite (LfOK.none m) (LfOK.ite (LfOK.none m) (LfOK.ite (lfRet m _) ?_))
      · refine LfOK.bind (by simp [liftLetW.k_lift_go]) (fun _ _ => by simp only [liftLetW.k_lift_go]; rfl) (iG _ _ _ _ _)
          fun x m₁ h1 => ?_
        refine LfOK.trans h1 (LfOK.bind (by simp [liftLetW.k_lift_go_2]) (fun _ _ => by simp only [liftLetW.k_lift_go_2]; rfl)
          (iG _ _ _ _ _) fun y m₂ h2 => ?_)
        refine LfOK.trans h2 (LfOK.bind (by simp [liftLetW.k_lift_go_3]) (fun _ _ => by simp only [liftLetW.k_lift_go_3]; rfl)
          (iG _ _ _ _ _) fun z m₃ h3 => ?_)
        exact LfOK.trans h3 (lfTail_frame (mkLetW_lf m₃ x y z))
    · intro m h c k fu
      rw [liftProjW.eq_def]
      refine LfOK.ite (LfOK.none m) (LfOK.ite (lfRet m _) ?_)
      · refine LfOK.bind (by simp [liftProjW.k_lift_go]) (fun _ _ => by simp only [liftProjW.k_lift_go]; rfl)
          (iG _ _ _ _ _) fun x m₁ h1 => ?_
        exact LfOK.trans h1 (lfTail_frame (mkProjW_lf m₁ _ _ x))

theorem liftEntryW_frame (n : Nat) (m : Mem) (h k c f : Word) : LfOK m (liftEntryW n m h k c f) := by
  intro r m' hb
  cases n with
  | zero => simp [liftEntryW] at hb
  | succ n =>
  have h0 : ¬ rdW (m.arr64 CTL) lfSch.cs + 2 = 0 := fun h0 => by simp [liftEntryW, h0] at hb
  rw [liftEntryW.arm1 n m h k c f h0] at hb
  have hc0 : LfFrame m (mclearG lfSch m) :=
    (mclearG_frame lfSch m).mono (by simp) (by simp [liftC, lfSch])
  cases hw : liftW n (mclearG lfSch m) h c k f with
  | none => simp [hw, liftEntryW.k_lift_go] at hb
  | some p =>
    obtain ⟨r₁, m₁⟩ := p
    have h1 : ¬ rdW (m₁.arr64 CTL) lfSch.cs + 2 = 0 := fun h1 => by simp [hw, liftEntryW.k_lift_go, h1] at hb
    rw [hw, liftEntryW.k_lift_go.arm1 r₁ m₁ h1, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact (hc0.trans ((liftW_frame n).1 _ _ _ _ _ _ _ hw)).trans
      ((mclearG_frame lfSch m₁).mono (by simp) (by simp [liftC, lfSch]))

/-! ## The callees under `ArenaI` -/

theorem internE_inst1LC (v : ENodeView) (a : AState) (hok : AM.ok (internE v) a) :
    (AM.st (internE v) a).memos.inst1LC = a.memos.inst1LC :=
  (keeps_internE_i1 v).run (AM.run_of_ok _ _ hok)

theorem mkApp_okI (m : Mem) (a : AState) (hA : ArenaI m a) (f x r : Word) (m' : Mem)
    (hI : mkAppW m f x = some (r, m')) :
    AM.ok (internE (.app (decE f) (decE x))) a ∧
    ArenaI m' (AM.st (internE (.app (decE f) (decE x))) a) ∧
    AM.res (internE (.app (decE f) (decE x))) a = decE r := by
  obtain ⟨hok, hD, hres⟩ := mkApp_ok m a hA.1 f x r m' hI
  exact ⟨hok, ⟨hD, hA.2.across (mkAppW_frameA m m' f x r hI) (by decide) (by decide)
    (internE_inst1LC _ a hok)⟩, hres⟩

theorem mkLam_okI (m : Mem) (a : AState) (hA : ArenaI m a) (t b r : Word) (m' : Mem)
    (hI : mkLamW m t b = some (r, m')) :
    AM.ok (internE (.lam (decE t) (decE b))) a ∧
    ArenaI m' (AM.st (internE (.lam (decE t) (decE b))) a) ∧
    AM.res (internE (.lam (decE t) (decE b))) a = decE r := by
  obtain ⟨hok, hD, hres⟩ := mkLam_ok m a hA.1 t b r m' hI
  exact ⟨hok, ⟨hD, hA.2.across (mkLamW_frameA m m' t b r hI) (by decide) (by decide)
    (internE_inst1LC _ a hok)⟩, hres⟩

theorem mkForall_okI (m : Mem) (a : AState) (hA : ArenaI m a) (t b r : Word) (m' : Mem)
    (hI : mkForallW m t b = some (r, m')) :
    AM.ok (internE (.forallE (decE t) (decE b))) a ∧
    ArenaI m' (AM.st (internE (.forallE (decE t) (decE b))) a) ∧
    AM.res (internE (.forallE (decE t) (decE b))) a = decE r := by
  obtain ⟨hok, hD, hres⟩ := mkForall_ok m a hA.1 t b r m' hI
  exact ⟨hok, ⟨hD, hA.2.across (mkForallW_frameA m m' t b r hI) (by decide) (by decide)
    (internE_inst1LC _ a hok)⟩, hres⟩

theorem mkLet_okI (m : Mem) (a : AState) (hA : ArenaI m a) (t v b r : Word) (m' : Mem)
    (hI : mkLetW m t v b = some (r, m')) :
    AM.ok (internE (.letE (decE t) (decE v) (decE b))) a ∧
    ArenaI m' (AM.st (internE (.letE (decE t) (decE v) (decE b))) a) ∧
    AM.res (internE (.letE (decE t) (decE v) (decE b))) a = decE r := by
  obtain ⟨hok, hD, hres⟩ := mkLet_ok m a hA.1 t v b r m' hI
  exact ⟨hok, ⟨hD, hA.2.across (mkLetW_frameA m m' t v b r hI) (by decide) (by decide)
    (internE_inst1LC _ a hok)⟩, hres⟩

theorem mkProj_okI (m : Mem) (a : AState) (hA : ArenaI m a) (n i e r : Word) (m' : Mem)
    (hI : mkProjW m n i e = some (r, m')) :
    AM.ok (internE (.proj (decI n) i.toNat (decE e))) a ∧
    ArenaI m' (AM.st (internE (.proj (decI n) i.toNat (decE e))) a) ∧
    AM.res (internE (.proj (decI n) i.toNat (decE e))) a = decE r := by
  obtain ⟨hok, hD, hres⟩ := mkProj_ok m a hA.1 n i e r m' hI
  exact ⟨hok, ⟨hD, hA.2.across (mkProjW_frameA m m' n i e r hI) (by decide) (by decide)
    (internE_inst1LC _ a hok)⟩, hres⟩

theorem internBVar_I (m : Mem) (a : AState) (hA : ArenaI m a) (u r : Word) (m' : Mem)
    (hI : binternW m u = some (r, m')) :
    AM.ok (internE (.bvar u.toNat)) a ∧ ArenaI m' (AM.st (internE (.bvar u.toNat)) a) ∧
    AM.res (internE (.bvar u.toNat)) a = decE r := by
  obtain ⟨hok, hD, hres⟩ := internBVar_D m a hA.1 u r m' hI
  exact ⟨hok, ⟨hD, hA.2.across (binternW_frameA m m' u r hI) (by decide) (by decide)
    (internE_inst1LC _ a hok)⟩, hres⟩

theorem bvbW_frame (n : Nat) (m m' : Mem) (h f x : Word) (hb : bvbW n m h f = some (x, m')) :
    BbFrame m m' := by
  obtain ⟨n, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by cases n <;> simp_all [bvbW]⟩
  by_cases hs : derBW m h = 32767
  · rw [bvbW_sat n m h f hs] at hb
    obtain ⟨n, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by cases n <;> simp_all [bbN]⟩
    rw [bbN_succ] at hb
    exact bbMemoW_frame n m m' h f x hb
  · rw [bvbW_pk n m h f hs] at hb
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    exact MemFrame.refl _ _ _

/-- **`bvar_b`'s model under `ArenaI`.** -/
theorem bvbW_okI (n : Nat) (m m' : Mem) (a : AState) (hA : ArenaI m a)
    (h f x : Word) (hh : h.toNat < 2 ^ 32) (hb : bvbW n m h f = some (x, m')) :
    ∃ a', (bvarB f.toNat (decE h)).run a = .ok (x.toNat, a') ∧ ArenaI m' a' := by
  obtain ⟨a', ha', hD⟩ := bvbW_ok n m m' a hA.1 h f x hh hb
  exact ⟨a', ha', hD, hA.2.across (bvbW_frame n m m' h f x hb) (by decide) (by decide)
    ((keeps_bvarB_i1 _ _).run ha')⟩

/-- **`lift_entry`'s model under `ArenaI`.** -/
theorem liftEntryW_okI (n : Nat) (m m' : Mem) (a : AState) (hA : ArenaI m a)
    (h k c f r : Word) (hh : h.toNat < 2 ^ 32) (hb : liftEntryW n m h k c f = some (r, m')) :
    ∃ a', (liftLooseBVarsFast f.toNat k.toNat c.toNat (decE h)).run a = .ok (decE r, a') ∧
      ArenaI m' a' := by
  cases n with
  | zero => simp [liftEntryW] at hb
  | succ n =>
  obtain ⟨a', ha', hD⟩ := liftEntryW_correct n m m' a hA.1 h k c f r hh hb
  exact ⟨a', ha', hD, hA.2.across (liftEntryW_frame _ m h k c f r m' hb) (by decide) (by decide)
    ((keeps_liftFast_i1 _ _ _ _).run ha')⟩

/-! ## The statements, by fuel -/

/-- What `i1l_go`'s model at L fuel `n` and counter `fu` says about the arena walk at the twin
fuel `fu.toNat`. -/
def LIGoOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (h d v fu r : Word), ArenaI m a →
    h.toNat < 2 ^ 32 → v.toNat < 2 ^ 32 → i1lW n m h d v fu = some (r, m') →
    ∃ a', (instantiate1LiftGo (decE v) fu.toNat (decE h) d.toNat).run a = .ok (decE r, a') ∧
      ArenaI m' a'

/-- The arena arm `arm` refines the L arm `armW` (with its counter) at `h`. -/
def LIArmRef (n : Nat) (armW : Nat → Mem → Word → Word → Word → Word → Option (Word × Mem))
    (arm : AM EIdx) (m m' : Mem) (a : AState) (h d v fu r : Word) : Prop :=
  armW n m h d v fu = some (r, m') → ∃ a', arm.run a = .ok (decE r, a') ∧ ArenaI m' a'

/-- The five arms, given the view checks of each. -/
def LIArmOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (h d v fu r : Word), ArenaI m a →
    h.toNat < 2 ^ 32 → v.toNat < 2 ^ 32 →
    (viewOK m h APP → h >>> 28 = 4 → LIArmRef n i1lAppW
      (inst1LiftArmApp (decE v) fu.toNat (decE h) d.toNat
        (decE (tfld m APP (tierW h) (idxW h) 0))
        (decE (tfld m APP (tierW h) (idxW h) 1))) m m' a h d v fu r) ∧
    (viewOK m h LAM → h >>> 28 = 5 → LIArmRef n i1lLamW
      (inst1LiftArmLam (decE v) fu.toNat (decE h) d.toNat
        (decE (tfld m LAM (tierW h) (idxW h) 0))
        (decE (tfld m LAM (tierW h) (idxW h) 1))) m m' a h d v fu r) ∧
    (viewOK m h FORALL → h >>> 28 = 6 → LIArmRef n i1lForallW
      (inst1LiftArmForallE (decE v) fu.toNat (decE h) d.toNat
        (decE (tfld m FORALL (tierW h) (idxW h) 0))
        (decE (tfld m FORALL (tierW h) (idxW h) 1))) m m' a h d v fu r) ∧
    (viewOK m h LET → h >>> 28 = 7 → LIArmRef n i1lLetW
      (inst1LiftArmLet (decE v) fu.toNat (decE h) d.toNat
        (decE (tfld m LET (tierW h) (idxW h) 0))
        (decE (tfld m LET (tierW h) (idxW h) 1))
        (decE (tfld m LET (tierW h) (idxW h) 2))) m m' a h d v fu r) ∧
    (viewOK m h PROJ → h >>> 28 = 9 → LIArmRef n i1lProjW
      (inst1LiftArmProj (decE v) fu.toNat (decE h) d.toNat
        (decI (tfld m PROJ (tierW h) (idxW h) 0))
        (tfld m PROJ (tierW h) (idxW h) 1).toNat
        (decE (tfld m PROJ (tierW h) (idxW h) 2))) m m' a h d v fu r)

/-! ## The dispatcher -/

theorem ligoOK_succ (n : Nat) (ih : LIArmOK n) : LIGoOK (n + 1) := by
  intro m m' a h d v fu r hA hh hv hb
  have hfu : ¬ fu = 0 := fun hfu => by rw [i1lW] at hb; simp [hfu] at hb
  rw [i1lW.arm1 n m h d v fu hfu] at hb
  rw [ctrW_toNat fu hfu, instantiate1LiftGo_succ, StateT.run_bind]
  cases hx : bvbW n m h (fu - 1) with
  | none => rw [hx, i1lW.k_bvar_b] at hb; cases hb
  | some p =>
  obtain ⟨x, m₁⟩ := p
  rw [hx] at hb
  obtain ⟨a₁, ha₁, hA₁⟩ := bvbW_okI n m m₁ a hA h (fu - 1) x hh hx
  rw [ha₁, except_ok_bind]
  by_cases hcut : x ≤ d
  · rw [i1lW.k_bvar_b.arm1 n h d v fu x m₁ hcut] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    simp only [UInt64.le_iff_toNat_le.mp hcut, decide_true, ↓reduceIte]
    exact ⟨a₁, rfl, hA₁⟩
  have hcut' : ¬ x.toNat ≤ d.toNat := fun e => hcut (UInt64.le_iff_toNat_le.mpr e)
  simp only [hcut', ↓reduceIte, StateT.run_bind]
  have hR := hA₁.1.1
  by_cases hs : tierW h ≠ 0 ∧ rdW (m₁.arr64 CTL) 1 = 0
  · rw [i1lW.k_bvar_b] at hb; simp [hcut, hs] at hb
  have vok : ∀ c0, ¬ tcnt m₁ c0 (tierW h) ≤ idxW h → viewOK m₁ h c0 :=
    fun c0 hc => ⟨hs, UInt64.not_le.mp hc⟩
  by_cases g0 : h >>> 28 = 0
  · by_cases hc : tcnt m₁ BVAR (tierW h) ≤ idxW h
    · rw [i1lW.k_bvar_b] at hb; simp [hcut, hs, g0, hc] at hb
    rw [view_run _ a₁ _ (view_bvar m₁ a₁ hR h hh (vok BVAR hc) g0)]
    simp only [except_ok_bind]
    by_cases he : tfld m₁ BVAR (tierW h) (idxW h) 0 = d
    · rw [i1lW.k_bvar_b.arm2 n h d v fu x m₁ hcut hs g0 hc he] at hb
      obtain ⟨a', ha', hA'⟩ := liftEntryW_okI n m₁ m' a₁ hA₁ v d 0 (fu - 1) r hv hb
      simp only [he, ↓reduceIte]
      exact ⟨a', by simpa using ha', hA'⟩
    have he' : ¬ (tfld m₁ BVAR (tierW h) (idxW h) 0).toNat = d.toNat :=
      fun e => he (UInt64.toNat_inj.mp e)
    by_cases hl : d < tfld m₁ BVAR (tierW h) (idxW h) 0
    · rw [i1lW.k_bvar_b.arm3 n h d v fu x m₁ hcut hs g0 hc he hl] at hb
      obtain ⟨hok, hA', hres⟩ := internBVar_I m₁ a₁ hA₁ _ r m' hb
      have hl' : (tfld m₁ BVAR (tierW h) (idxW h) 0).toNat > d.toNat := hl
      have hsub : (tfld m₁ BVAR (tierW h) (idxW h) 0 - 1).toNat =
          (tfld m₁ BVAR (tierW h) (idxW h) 0).toNat - 1 := by
        rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega)]; simp
      simp only [he', hl', ↓reduceIte]
      rw [← hsub, AM.run_of_ok _ _ hok, hres]; exact ⟨_, rfl, hA'⟩
    · rw [i1lW.k_bvar_b.arm4 n h d v fu x m₁ hcut hs g0 hc he hl] at hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      have hl' : ¬ (tfld m₁ BVAR (tierW h) (idxW h) 0).toNat > d.toNat := fun e => hl e
      simp only [he', hl', ↓reduceIte]; exact ⟨a₁, rfl, hA₁⟩
  have pure_h : ∀ w, a₁.store.view (decE h) = some w →
      i1lW.k_bvar_b n h d v fu (some (x, m₁)) = some (h, m₁) →
      (∀ y : AState, (match w with
        | .bvar i =>
          if i = d.toNat then liftLooseBVarsFast (fu - 1).toNat d.toNat 0 (decE v)
          else if i > d.toNat then internE (.bvar (i - 1))
          else pure (decE h)
        | .fvar _ _ | .sort _ | .const _ _ | .lit _ => pure (decE h)
        | .app f a => inst1LiftArmApp (decE v) (fu - 1).toNat (decE h) d.toNat f a
        | .lam ty body => inst1LiftArmLam (decE v) (fu - 1).toNat (decE h) d.toNat ty body
        | .forallE ty body => inst1LiftArmForallE (decE v) (fu - 1).toNat (decE h) d.toNat ty body
        | .letE ty val body => inst1LiftArmLet (decE v) (fu - 1).toNat (decE h) d.toNat ty val body
        | .proj n i sub => inst1LiftArmProj (decE v) (fu - 1).toNat (decE h) d.toNat n i sub
        : AM EIdx).run y = .ok (decE h, y)) →
      ∃ a', ((view (decE h)).run a₁ >>= fun p => (match p.1 with
        | .bvar i =>
          if i = d.toNat then liftLooseBVarsFast (fu - 1).toNat d.toNat 0 (decE v)
          else if i > d.toNat then internE (.bvar (i - 1))
          else pure (decE h)
        | .fvar _ _ | .sort _ | .const _ _ | .lit _ => pure (decE h)
        | .app f a => inst1LiftArmApp (decE v) (fu - 1).toNat (decE h) d.toNat f a
        | .lam ty body => inst1LiftArmLam (decE v) (fu - 1).toNat (decE h) d.toNat ty body
        | .forallE ty body => inst1LiftArmForallE (decE v) (fu - 1).toNat (decE h) d.toNat ty body
        | .letE ty val body => inst1LiftArmLet (decE v) (fu - 1).toNat (decE h) d.toNat ty val body
        | .proj n i sub => inst1LiftArmProj (decE v) (fu - 1).toNat (decE h) d.toNat n i sub
        : AM EIdx).run p.2) = Except.ok (decE r, a') ∧ ArenaI m' a' := by
    intro w hw hl hy
    rw [hl] at hb; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    rw [view_run _ a₁ w hw]
    exact ⟨a₁, hy a₁, hA₁⟩
  by_cases g1 : h >>> 28 = 1
  · by_cases hc : tcnt m₁ FVAR (tierW h) ≤ idxW h
    · rw [i1lW.k_bvar_b] at hb; simp [hcut, hs, g0, g1, hc] at hb
    obtain ⟨_, _, hw⟩ := view_fvar m₁ a₁ hR h hh (vok FVAR hc) g1
    exact pure_h _ hw (i1lW.k_bvar_b.arm5 n h d v fu x m₁ hcut hs g0 g1 hc) (fun _ => rfl)
  by_cases g2 : h >>> 28 = 2
  · by_cases hc : tcnt m₁ SORT (tierW h) ≤ idxW h
    · rw [i1lW.k_bvar_b] at hb; simp [hcut, hs, g0, g1, g2, hc] at hb
    obtain ⟨_, hw⟩ := view_sort m₁ a₁ hR h hh (vok SORT hc) g2
    exact pure_h _ hw (i1lW.k_bvar_b.arm6 n h d v fu x m₁ hcut hs g0 g1 g2 hc) (fun _ => rfl)
  by_cases g3 : h >>> 28 = 3
  · by_cases hc : tcnt m₁ CONST (tierW h) ≤ idxW h
    · rw [i1lW.k_bvar_b] at hb; simp [hcut, hs, g0, g1, g2, g3, hc] at hb
    obtain ⟨_, _, hw⟩ := view_const m₁ a₁ hR h hh (vok CONST hc) g3
    exact pure_h _ hw (i1lW.k_bvar_b.arm7 n h d v fu x m₁ hcut hs g0 g1 g2 g3 hc) (fun _ => rfl)
  by_cases g8 : h >>> 28 = 8
  · by_cases hc : tcnt m₁ LIT (tierW h) ≤ idxW h
    · rw [i1lW.k_bvar_b] at hb; simp [hcut, hs, g0, g1, g2, g3, g8, hc] at hb
    obtain ⟨_, hw⟩ := view_lit m₁ a₁ hR h hh (vok LIT hc) g8
    exact pure_h _ hw (i1lW.k_bvar_b.arm8 n h d v fu x m₁ hcut hs g0 g1 g2 g3 g8 hc) (fun _ => rfl)
  have arm := ih m₁ m' a₁ h d v (fu - 1) r hA₁ hh hv
  by_cases g4 : h >>> 28 = 4
  · by_cases hc : tcnt m₁ APP (tierW h) ≤ idxW h
    · rw [i1lW.k_bvar_b] at hb; simp [hcut, hs, g0, g1, g2, g3, g8, g4, hc] at hb
    rw [view_run _ a₁ _ (view_app m₁ a₁ hR h hh (vok APP hc) g4).1]
    rw [i1lW.k_bvar_b.arm9 n h d v fu x m₁ hcut hs g0 g1 g2 g3 g8 g4 hc] at hb
    exact arm.1 (vok APP hc) g4 hb
  by_cases g5 : h >>> 28 = 5
  · by_cases hc : tcnt m₁ LAM (tierW h) ≤ idxW h
    · rw [i1lW.k_bvar_b] at hb; simp [hcut, hs, g0, g1, g2, g3, g8, g4, g5, hc] at hb
    rw [view_run _ a₁ _ (view_lam m₁ a₁ hR h hh (vok LAM hc) g5).1]
    rw [i1lW.k_bvar_b.arm10 n h d v fu x m₁ hcut hs g0 g1 g2 g3 g8 g4 g5 hc] at hb
    exact arm.2.1 (vok LAM hc) g5 hb
  by_cases g6 : h >>> 28 = 6
  · by_cases hc : tcnt m₁ FORALL (tierW h) ≤ idxW h
    · rw [i1lW.k_bvar_b] at hb; simp [hcut, hs, g0, g1, g2, g3, g8, g4, g5, g6, hc] at hb
    rw [view_run _ a₁ _ (view_forall m₁ a₁ hR h hh (vok FORALL hc) g6).1]
    rw [i1lW.k_bvar_b.arm11 n h d v fu x m₁ hcut hs g0 g1 g2 g3 g8 g4 g5 g6 hc] at hb
    exact arm.2.2.1 (vok FORALL hc) g6 hb
  by_cases g7 : h >>> 28 = 7
  · by_cases hc : tcnt m₁ LET (tierW h) ≤ idxW h
    · rw [i1lW.k_bvar_b] at hb; simp [hcut, hs, g0, g1, g2, g3, g8, g4, g5, g6, g7, hc] at hb
    rw [view_run _ a₁ _ (view_let m₁ a₁ hR h hh (vok LET hc) g7).1]
    rw [i1lW.k_bvar_b.arm12 n h d v fu x m₁ hcut hs g0 g1 g2 g3 g8 g4 g5 g6 g7 hc] at hb
    exact arm.2.2.2.1 (vok LET hc) g7 hb
  by_cases g9 : h >>> 28 = 9
  · by_cases hc : tcnt m₁ PROJ (tierW h) ≤ idxW h
    · rw [i1lW.k_bvar_b] at hb; simp [hcut, hs, g0, g1, g2, g3, g8, g4, g5, g6, g7, g9, hc] at hb
    rw [view_run _ a₁ _ (view_proj m₁ a₁ hR h hh (vok PROJ hc) g9).1]
    rw [i1lW.k_bvar_b.arm13 n h d v fu x m₁ hcut hs g0 g1 g2 g3 g8 g4 g5 g6 g7 g9 hc] at hb
    exact arm.2.2.2.2 (vok PROJ hc) g9 hb
  rw [i1lW.k_bvar_b] at hb; simp [hcut, hs, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9] at hb

/-! ## The arms -/

/-- **The tail of every arm**: intern the rebuilt node and record it in the memo. -/
theorem i1lTail_ok (op : AM EIdx) (mkr : Option (Word × Mem)) (a₂ : AState) (h d r : Word)
    (m' : Mem) (hh : h.toNat < 2 ^ 32)
    (hmk : ∀ r₃ m₃, mkr = some (r₃, m₃) →
      AM.ok op a₂ ∧ ArenaI m₃ (AM.st op a₂) ∧ AM.res op a₂ = decE r₃)
    (hb : i1lAppW.k_mk_app h d mkr = some (r, m')) :
    ∃ a', (do let r ← op; inst1LSet (decE h, d.toNat) r; pure r : AM EIdx).run a₂ =
      .ok (decE r, a') ∧ ArenaI m' a' := by
  cases h3 : mkr with
  | none => simp [h3, i1lAppW.k_mk_app] at hb
  | some q =>
    obtain ⟨r₃, m₃⟩ := q
    rw [h3] at hb
    have hr : ¬ mfindG i1lSch m₃ h d = [] := fun hr => by simp [i1lAppW.k_mk_app, hr] at hb
    rw [i1lAppW.k_mk_app.arm1 h d r₃ m₃ hr] at hb
    cases h4 : mputG i1lSch m₃ h d r₃ ((mfindG i1lSch m₃ h d).headD 0)
        ((mfindG i1lSch m₃ h d).tail.headD 0) with
    | none => rw [h4] at hb; simp [i1lAppW.k_i1l_put] at hb
    | some m₄ =>
      rw [h4, i1lAppW.k_i1l_put.arm1, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      have hs : msetG i1lSch m₃ h d r₃ = some m₄ := by rw [msetG, ite_eq_right hr]; exact h4
      obtain ⟨hok, hA₃, hres⟩ := hmk r₃ m₃ h3
      refine ⟨_, ?_, ArenaI.imemo_set m₃ m₄ _ hA₃ h d r₃ hh hs⟩
      simp only [StateT.run_bind, AM.run_of_ok _ _ hok, hres, except_ok_bind, inst1LSet_run]; rfl

/-- **The memo probe of every arm**: a hit is the memo's value; a miss runs `miss`. -/
theorem i1lProbe_ok (armW : Option (Word × Mem)) (miss : AM EIdx) (m m' : Mem) (a : AState)
    (hA : ArenaI m a) (h d r : Word) (hh : h.toNat < 2 ^ 32)
    (hhit : mfindG i1lSch m h d ≠ [] → (mfindG i1lSch m h d).headD 0 ≠ 0 →
      armW = some (rdW (m.arr64 ILFM) ((mfindG i1lSch m h d).tail.headD 0 * 4 + 3), m))
    (hnone : mfindG i1lSch m h d = [] → armW = none)
    (hmiss : mfindG i1lSch m h d ≠ [] → (mfindG i1lSch m h d).headD 0 = 0 → armW = some (r, m') →
      ∃ a', miss.run a = .ok (decE r, a') ∧ ArenaI m' a')
    (hb : armW = some (r, m')) :
    ∃ a', (do
        match ← inst1LGet (decE h, d.toNat) with
        | some r => pure r
        | none => miss : AM EIdx).run a = .ok (decE r, a') ∧ ArenaI m' a' := by
  rw [StateT.run_bind, inst1LGet_run, except_ok_bind]
  have hr : ¬ mfindG i1lSch m h d = [] := fun hr => by rw [hnone hr] at hb; cases hb
  by_cases hh0 : (mfindG i1lSch m h d).headD 0 ≠ 0
  · rw [hhit hr hh0] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    rw [show a.memos.inst1LC[(decE h, d.toNat)]? = _ from
      memoRG_hit i1lSch lfKey decE m _ hA.2 h d hr hh0 hh]
    exact ⟨a, rfl, hA⟩
  · simp only [ne_eq, Decidable.not_not] at hh0
    rw [show a.memos.inst1LC[(decE h, d.toNat)]? = none from
      memoRG_miss i1lSch lfKey decE m _ hA.2 h d hh hr hh0]
    exact hmiss hr hh0 hb

section arms
variable (n : Nat) (ih : LIGoOK n) (m m' : Mem) (a : AState) (hA : ArenaI m a)
  (h d v fu r : Word) (hh : h.toNat < 2 ^ 32) (hv : v.toNat < 2 ^ 32)
include ih hA hh hv

theorem i1lAppArm_ok (hvw : viewOK m h APP) (hg : h >>> 28 = 4) :
    LIArmRef (n + 1) i1lAppW
      (inst1LiftArmApp (decE v) fu.toNat (decE h) d.toNat
        (decE (tfld m APP (tierW h) (idxW h) 0))
        (decE (tfld m APP (tierW h) (idxW h) 1))) m m' a h d v fu r := by
  intro hb
  obtain ⟨-, hfw, haw⟩ := view_app m a hA.1.1 h hh hvw hg
  rw [inst1LiftArmApp]
  refine i1lProbe_ok _ _ m m' a hA h d r hh (i1lAppW.arm1 n m h d v fu)
    (fun hr => by rw [i1lAppW]; simp [hr]) (fun hr hh0 hb => ?_) hb
  rw [i1lAppW.arm2 n m h d v fu hr hh0] at hb
  cases h1 : i1lW n m (tfld m APP (tierW h) (idxW h) 0) d v fu with
  | none => simp [h1, i1lAppW.k_i1l_go] at hb
  | some p =>
  obtain ⟨x, m₁⟩ := p
  rcases h2 : i1lW n m₁ (tfld m APP (tierW h) (idxW h) 1) d v fu with _ | ⟨y, m₂⟩ <;> simp only [h2, h1, i1lAppW.k_i1l_go, i1lAppW.k_i1l_go_2, reduceCtorEq] at hb
  obtain ⟨a₁, ha₁, hA₁⟩ := ih m m₁ a _ d v fu x hA hfw hv h1
  obtain ⟨a₂, ha₂, hA₂⟩ := ih m₁ m₂ a₁ _ d v fu y hA₁ haw hv h2
  obtain ⟨a', h3, h4⟩ := i1lTail_ok _ _ a₂ h d r m' hh
    (fun r₃ m₃ h => mkApp_okI m₂ a₂ hA₂ x y r₃ m₃ h) hb
  exact ⟨a', by simp only [StateT.run_bind, ha₁, ha₂, except_ok_bind]; exact h3, h4⟩

theorem i1lLamArm_ok (hvw : viewOK m h LAM) (hg : h >>> 28 = 5) :
    LIArmRef (n + 1) i1lLamW
      (inst1LiftArmLam (decE v) fu.toNat (decE h) d.toNat
        (decE (tfld m LAM (tierW h) (idxW h) 0))
        (decE (tfld m LAM (tierW h) (idxW h) 1))) m m' a h d v fu r := by
  intro hb
  have hd1 : ¬ d + 1 = 0 := fun hd1 => by rw [i1lLamW] at hb; simp [hd1] at hb
  obtain ⟨-, hfw, haw⟩ := view_lam m a hA.1.1 h hh hvw hg
  rw [inst1LiftArmLam]
  refine i1lProbe_ok _ _ m m' a hA h d r hh (i1lLamW.arm1 n m h d v fu hd1)
    (fun hr => by rw [i1lLamW]; simp [hd1, hr]) (fun hr hh0 hb => ?_) hb
  rw [i1lLamW.arm2 n m h d v fu hd1 hr hh0] at hb
  cases h1 : i1lW n m (tfld m LAM (tierW h) (idxW h) 0) d v fu with
  | none => simp [h1, i1lLamW.k_i1l_go] at hb
  | some p =>
  obtain ⟨x, m₁⟩ := p
  rcases h2 : i1lW n m₁ (tfld m LAM (tierW h) (idxW h) 1) (d + 1) v fu with _ | ⟨y, m₂⟩ <;> simp only [h2, h1, i1lLamW.k_i1l_go, i1lLamW.k_i1l_go_2, reduceCtorEq] at hb
  obtain ⟨a₁, ha₁, hA₁⟩ := ih m m₁ a _ d v fu x hA hfw hv h1
  obtain ⟨a₂, ha₂, hA₂⟩ := ih m₁ m₂ a₁ _ (d + 1) v fu y hA₁ haw hv h2
  rw [succW_toNat d hd1] at ha₂
  obtain ⟨a', h3, h4⟩ := i1lTail_ok _ _ a₂ h d r m' hh
    (fun r₃ m₃ h => mkLam_okI m₂ a₂ hA₂ x y r₃ m₃ h) hb
  exact ⟨a', by simp only [StateT.run_bind, ha₁, ha₂, except_ok_bind]; exact h3, h4⟩

theorem i1lForallArm_ok (hvw : viewOK m h FORALL) (hg : h >>> 28 = 6) :
    LIArmRef (n + 1) i1lForallW
      (inst1LiftArmForallE (decE v) fu.toNat (decE h) d.toNat
        (decE (tfld m FORALL (tierW h) (idxW h) 0))
        (decE (tfld m FORALL (tierW h) (idxW h) 1))) m m' a h d v fu r := by
  intro hb
  have hd1 : ¬ d + 1 = 0 := fun hd1 => by rw [i1lForallW] at hb; simp [hd1] at hb
  obtain ⟨-, hfw, haw⟩ := view_forall m a hA.1.1 h hh hvw hg
  rw [inst1LiftArmForallE]
  refine i1lProbe_ok _ _ m m' a hA h d r hh (i1lForallW.arm1 n m h d v fu hd1)
    (fun hr => by rw [i1lForallW]; simp [hd1, hr]) (fun hr hh0 hb => ?_) hb
  rw [i1lForallW.arm2 n m h d v fu hd1 hr hh0] at hb
  cases h1 : i1lW n m (tfld m FORALL (tierW h) (idxW h) 0) d v fu with
  | none => simp [h1, i1lForallW.k_i1l_go] at hb
  | some p =>
  obtain ⟨x, m₁⟩ := p
  rcases h2 : i1lW n m₁ (tfld m FORALL (tierW h) (idxW h) 1) (d + 1) v fu with _ | ⟨y, m₂⟩ <;> simp only [h2, h1, i1lForallW.k_i1l_go, i1lForallW.k_i1l_go_2, reduceCtorEq] at hb
  obtain ⟨a₁, ha₁, hA₁⟩ := ih m m₁ a _ d v fu x hA hfw hv h1
  obtain ⟨a₂, ha₂, hA₂⟩ := ih m₁ m₂ a₁ _ (d + 1) v fu y hA₁ haw hv h2
  rw [succW_toNat d hd1] at ha₂
  obtain ⟨a', h3, h4⟩ := i1lTail_ok _ _ a₂ h d r m' hh
    (fun r₃ m₃ h => mkForall_okI m₂ a₂ hA₂ x y r₃ m₃ h) hb
  exact ⟨a', by simp only [StateT.run_bind, ha₁, ha₂, except_ok_bind]; exact h3, h4⟩

theorem i1lLetArm_ok (hvw : viewOK m h LET) (hg : h >>> 28 = 7) :
    LIArmRef (n + 1) i1lLetW
      (inst1LiftArmLet (decE v) fu.toNat (decE h) d.toNat
        (decE (tfld m LET (tierW h) (idxW h) 0))
        (decE (tfld m LET (tierW h) (idxW h) 1))
        (decE (tfld m LET (tierW h) (idxW h) 2))) m m' a h d v fu r := by
  intro hb
  have hd1 : ¬ d + 1 = 0 := fun hd1 => by rw [i1lLetW] at hb; simp [hd1] at hb
  obtain ⟨-, htw, hvw', hbw⟩ := view_let m a hA.1.1 h hh hvw hg
  rw [inst1LiftArmLet]
  refine i1lProbe_ok _ _ m m' a hA h d r hh (i1lLetW.arm1 n m h d v fu hd1)
    (fun hr => by rw [i1lLetW]; simp [hd1, hr]) (fun hr hh0 hb => ?_) hb
  rw [i1lLetW.arm2 n m h d v fu hd1 hr hh0] at hb
  cases h1 : i1lW n m (tfld m LET (tierW h) (idxW h) 0) d v fu with
  | none => simp [h1, i1lLetW.k_i1l_go] at hb
  | some p =>
  obtain ⟨x, m₁⟩ := p
  cases h2 : i1lW n m₁ (tfld m LET (tierW h) (idxW h) 1) d v fu with
  | none => simp [h1, h2, i1lLetW.k_i1l_go, i1lLetW.k_i1l_go_2] at hb
  | some q =>
  obtain ⟨y, m₂⟩ := q
  rcases h3 : i1lW n m₂ (tfld m LET (tierW h) (idxW h) 2) (d + 1) v fu with _ | ⟨z, m₃⟩ <;> simp only [h3, h1, h2, i1lLetW.k_i1l_go, i1lLetW.k_i1l_go_2, i1lLetW.k_i1l_go_3, reduceCtorEq] at hb
  obtain ⟨a₁, ha₁, hA₁⟩ := ih m m₁ a _ d v fu x hA htw hv h1
  obtain ⟨a₂, ha₂, hA₂⟩ := ih m₁ m₂ a₁ _ d v fu y hA₁ hvw' hv h2
  obtain ⟨a₃, ha₃, hA₃⟩ := ih m₂ m₃ a₂ _ (d + 1) v fu z hA₂ hbw hv h3
  rw [succW_toNat d hd1] at ha₃
  obtain ⟨a', h4, h5⟩ := i1lTail_ok _ _ a₃ h d r m' hh
    (fun r₄ m₄ h => mkLet_okI m₃ a₃ hA₃ x y z r₄ m₄ h) hb
  exact ⟨a', by simp only [StateT.run_bind, ha₁, ha₂, ha₃, except_ok_bind]; exact h4, h5⟩

theorem i1lProjArm_ok (hvw : viewOK m h PROJ) (hg : h >>> 28 = 9) :
    LIArmRef (n + 1) i1lProjW
      (inst1LiftArmProj (decE v) fu.toNat (decE h) d.toNat
        (decI (tfld m PROJ (tierW h) (idxW h) 0))
        (tfld m PROJ (tierW h) (idxW h) 1).toNat
        (decE (tfld m PROJ (tierW h) (idxW h) 2))) m m' a h d v fu r := by
  intro hb
  obtain ⟨-, -, hew⟩ := view_proj m a hA.1.1 h hh hvw hg
  rw [inst1LiftArmProj]
  refine i1lProbe_ok _ _ m m' a hA h d r hh (i1lProjW.arm1 n m h d v fu)
    (fun hr => by rw [i1lProjW]; simp [hr]) (fun hr hh0 hb => ?_) hb
  rw [i1lProjW.arm2 n m h d v fu hr hh0] at hb
  rcases h1 : i1lW n m (tfld m PROJ (tierW h) (idxW h) 2) d v fu with _ | ⟨x, m₁⟩ <;> simp only [h1, i1lProjW.k_i1l_go, reduceCtorEq] at hb
  obtain ⟨a₁, ha₁, hA₁⟩ := ih m m₁ a _ d v fu x hA hew hv h1
  obtain ⟨a', h3, h4⟩ := i1lTail_ok _ _ a₁ h d r m' hh
    (fun r₃ m₃ h => mkProj_okI m₁ a₁ hA₁ _ _ x r₃ m₃ h) hb
  exact ⟨a', by simp only [StateT.run_bind, ha₁, except_ok_bind]; exact h3, h4⟩

end arms

theorem liarmOK_succ (n : Nat) (ih : LIGoOK n) : LIArmOK (n + 1) := by
  intro m m' a h d v fu r hA hh hv
  exact ⟨i1lAppArm_ok n ih m m' a hA h d v fu r hh hv,
    i1lLamArm_ok n ih m m' a hA h d v fu r hh hv,
    i1lForallArm_ok n ih m m' a hA h d v fu r hh hv,
    i1lLetArm_ok n ih m m' a hA h d v fu r hh hv,
    i1lProjArm_ok n ih m m' a hA h d v fu r hh hv⟩

/-- **The model of `i1l_go` refines `instantiate1LiftGo`** at the counter's fuel, for every L
fuel. -/
theorem i1lOK (n : Nat) : LIGoOK n ∧ LIArmOK n := by
  induction n with
  | zero =>
    refine ⟨fun _ _ _ _ _ _ _ _ _ _ _ hb => by simp [i1lW] at hb,
      fun _ _ _ _ _ _ _ _ _ _ _ => ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    intro _ _ hb <;> simp [i1lAppW, i1lLamW, i1lForallW, i1lLetW, i1lProjW] at hb
  | succ n ih => exact ⟨ligoOK_succ n ih.2, liarmOK_succ n ih.1⟩

/-! ## The entry `instantiate1_lift_fast` refines `instantiate1LiftFast` -/

theorem i1lFast_run (F : Nat) (e v : EIdx) (d : Nat) (a : AState) :
    (instantiate1LiftFast F e v d).run a =
      ((instantiate1LiftGo v F e d).run (withI1C a ∅) >>= fun p => .ok (p.1, withI1C p.2 ∅)) := by
  simp only [instantiate1LiftFast, StateT.run_bind, inst1LClear_run, except_ok_bind]
  cases (instantiate1LiftGo v F e d).run (withI1C a ∅) <;> rfl

theorem i1lFastW_correct (n : Nat) (m m' : Mem) (a : AState) (hA : ArenaI m a)
    (f e v d r : Word) (he : e.toNat < 2 ^ 32) (hv : v.toNat < 2 ^ 32)
    (hb : i1lFastW (n + 1) m f e v d = some (r, m')) :
    ∃ a', (instantiate1LiftFast f.toNat (decE e) (decE v) d.toNat).run a = .ok (decE r, a') ∧
      ArenaI m' a' ∧ r.toNat < 2 ^ 32 := by
  have hcs : i1lSch.cs = 52 := rfl
  have h0 : ¬ rdW (m.arr64 CTL) 52 + 2 = 0 := fun h0 => by simp [i1lFastW, hcs, h0] at hb
  rw [i1lFastW.arm1 n m f e v d (by rw [hcs]; exact h0)] at hb
  have hA₀ := ArenaI.imemo_clear m a hA h0
  cases hw : i1lW n (mclearG i1lSch m) e d v f with
  | none => simp [hw, i1lFastW.k_i1l_go] at hb
  | some p =>
    obtain ⟨r₁, m₁⟩ := p
    have h1 : ¬ rdW (m₁.arr64 CTL) 52 + 2 = 0 := fun h1 => by simp [hw, i1lFastW.k_i1l_go, hcs, h1] at hb
    rw [hw, i1lFastW.k_i1l_go.arm1 r₁ m₁ (by rw [hcs]; exact h1), Option.some.injEq,
      Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    obtain ⟨a₁, ha₁, hA₁⟩ := (i1lOK n).1 _ _ _ e d v f r₁ hA₀ he hv hw
    exact ⟨_, by rw [i1lFast_run, ha₁, decE_and32]; rfl, ArenaI.imemo_clear m₁ a₁ hA₁ h1, and32_lt r₁⟩

/-- **`instantiate1_lift_fast(f, e, v, d)` refines the arena's `instantiate1LiftFast f e v d`**
under `ArenaI` (`ArenaD` and the walk's memo), at the counter's fuel `f.toNat` and every L fuel:
if the L walk returns, the twin's walk succeeds with the same handle, in a related state; the
handle (masked to 32 bits, as `abs_entry`'s and `inst_entry`'s) is below `2^32`. -/
@[refines ConRon.Arena.instantiate1LiftFast]
theorem i1lFast_refines (p : Prog) (hp : I1lProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (hA : ArenaI s₀.mem a₀) (f e v d : Word) (he : e.toNat < 2 ^ 32) (hv : v.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "instantiate1_lift_fast" [f, e, v, d]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (instantiate1LiftFast f.toNat (decE e) (decE v) d.toNat) a₀ ∧
      ArenaI s'.mem (AM.st (instantiate1LiftFast f.toNat (decE e) (decE v) d.toNat) a₀) ∧
      AM.res (instantiate1LiftFast f.toNat (decE e) (decE v) d.toNat) a₀ = decE (r.headD 0) ∧
      (r.headD 0).toNat < 2 ^ 32; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun (i1lFast_spec p hp (n + 1) s₀ f e v d)
  subst hs
  obtain ⟨a', ha', hA', hlt⟩ := i1lFastW_correct n _ _ a₀ hA f e v d _ he hv hI
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ ha'
  exact ⟨hloc, hok, hst ▸ hA', hres, hlt⟩

end L.Arena
