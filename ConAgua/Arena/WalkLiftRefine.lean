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

The counter word `fu` is the twin's `fuel` exactly (ROADMAP §3 (b)); the statements hold at
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
    (ho : LfOK m o) : LfOK m (liftAppW.k2 h c o) := by
  intro r m' hb
  cases h3 : o with
  | none => simp [h3, liftAppW.k2] at hb
  | some q =>
    obtain ⟨r₃, m₃⟩ := q
    rw [h3] at hb
    by_cases hr : mfindG lfSch m₃ h c = []
    · simp [liftAppW.k2, hr] at hb
    rw [liftAppW.k2.arm1 h c r₃ m₃ hr] at hb
    cases h4 : mputG lfSch m₃ h c r₃ ((mfindG lfSch m₃ h c).headD 0)
        ((mfindG lfSch m₃ h c).tail.headD 0) with
    | none => rw [h4] at hb; simp [liftAppW.k1] at hb
    | some m₄ =>
      rw [h4, liftAppW.k1.arm1, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      have hs : msetG lfSch m₃ h c r₃ = some m₄ := by rw [msetG, ite_eq_right hr]; exact h4
      exact (ho r₃ m₃ h3).trans (lfSet_frame m₃ m₄ h c r₃ hs)

theorem LfOK.bind {m : Mem} {o : Option (Word × Mem)} {K : Option (Word × Mem) → Option (Word × Mem)}
    {body : Word → Mem → Option (Word × Mem)} (hK : K none = none)
    (hs : ∀ x m₁, K (some (x, m₁)) = body x m₁) (ho : LfOK m o)
    (hb : ∀ x m₁, LfFrame m m₁ → LfOK m (body x m₁)) : LfOK m (K o) := by
  intro r m' h
  cases h1 : o with
  | none => rw [h1, hK] at h; cases h
  | some q =>
    obtain ⟨x, m₁⟩ := q
    rw [h1, hs] at h
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
      · refine LfOK.bind (by simp [liftAppW.k4]) (fun _ _ => by simp only [liftAppW.k4]; rfl) (iG _ _ _ _ _)
          fun x m₁ h1 => ?_
        refine LfOK.trans h1 (LfOK.bind (by simp [liftAppW.k3]) (fun _ _ => by simp only [liftAppW.k3]; rfl)
          (iG _ _ _ _ _) fun y m₂ h2 => ?_)
        exact LfOK.trans h2 (lfTail_frame (mkAppW_lf m₂ x y))
    · intro m h c k fu
      rw [liftLamW.eq_def]
      refine LfOK.ite (LfOK.none m) (LfOK.ite (LfOK.none m) (LfOK.ite (lfRet m _) ?_))
      · refine LfOK.bind (by simp [liftLamW.k2]) (fun _ _ => by simp only [liftLamW.k2]; rfl) (iG _ _ _ _ _)
          fun x m₁ h1 => ?_
        refine LfOK.trans h1 (LfOK.bind (by simp [liftLamW.k1]) (fun _ _ => by simp only [liftLamW.k1]; rfl)
          (iG _ _ _ _ _) fun y m₂ h2 => ?_)
        exact LfOK.trans h2 (lfTail_frame (mkLamW_lf m₂ x y))
    · intro m h c k fu
      rw [liftForallW.eq_def]
      refine LfOK.ite (LfOK.none m) (LfOK.ite (LfOK.none m) (LfOK.ite (lfRet m _) ?_))
      · refine LfOK.bind (by simp [liftForallW.k2]) (fun _ _ => by simp only [liftForallW.k2]; rfl)
          (iG _ _ _ _ _) fun x m₁ h1 => ?_
        refine LfOK.trans h1 (LfOK.bind (by simp [liftForallW.k1])
          (fun _ _ => by simp only [liftForallW.k1]; rfl) (iG _ _ _ _ _) fun y m₂ h2 => ?_)
        exact LfOK.trans h2 (lfTail_frame (mkForallW_lf m₂ x y))
    · intro m h c k fu
      rw [liftLetW.eq_def]
      refine LfOK.ite (LfOK.none m) (LfOK.ite (LfOK.none m) (LfOK.ite (lfRet m _) ?_))
      · refine LfOK.bind (by simp [liftLetW.k3]) (fun _ _ => by simp only [liftLetW.k3]; rfl) (iG _ _ _ _ _)
          fun x m₁ h1 => ?_
        refine LfOK.trans h1 (LfOK.bind (by simp [liftLetW.k2]) (fun _ _ => by simp only [liftLetW.k2]; rfl)
          (iG _ _ _ _ _) fun y m₂ h2 => ?_)
        refine LfOK.trans h2 (LfOK.bind (by simp [liftLetW.k1]) (fun _ _ => by simp only [liftLetW.k1]; rfl)
          (iG _ _ _ _ _) fun z m₃ h3 => ?_)
        exact LfOK.trans h3 (lfTail_frame (mkLetW_lf m₃ x y z))
    · intro m h c k fu
      rw [liftProjW.eq_def]
      refine LfOK.ite (LfOK.none m) (LfOK.ite (lfRet m _) ?_)
      · refine LfOK.bind (by simp [liftProjW.k1]) (fun _ _ => by simp only [liftProjW.k1]; rfl)
          (iG _ _ _ _ _) fun x m₁ h1 => ?_
        exact LfOK.trans h1 (lfTail_frame (mkProjW_lf m₁ _ _ x))

theorem liftEntryW_frame (n : Nat) (m : Mem) (h k c f : Word) : LfOK m (liftEntryW n m h k c f) := by
  intro r m' hb
  cases n with
  | zero => simp [liftEntryW] at hb
  | succ n =>
  by_cases h0 : rdW (m.arr64 CTL) lfSch.cs + 2 = 0
  · simp [liftEntryW, h0] at hb
  rw [liftEntryW.arm1 n m h k c f h0] at hb
  have hc0 : LfFrame m (mclearG lfSch m) :=
    (mclearG_frame lfSch m).mono (by simp) (by simp [liftC, lfSch])
  cases hw : liftW n (mclearG lfSch m) h c k f with
  | none => simp [hw, liftEntryW.k1] at hb
  | some p =>
    obtain ⟨r₁, m₁⟩ := p
    by_cases h1 : rdW (m₁.arr64 CTL) lfSch.cs + 2 = 0
    · simp [hw, liftEntryW.k1, h1] at hb
    rw [hw, liftEntryW.k1.arm1 r₁ m₁ h1, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact (hc0.trans ((liftW_frame n).1 _ _ _ _ _ _ _ hw)).trans
      ((mclearG_frame lfSch m₁).mono (by simp) (by simp [liftC, lfSch]))

end L.Arena
