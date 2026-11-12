module

public import ConAgua.Arena.WalkLift
public import ConAgua.Arena.Abs1Refine
public import ConAgua.Arena.BvarBRefine
public import ConAgua.Arena.LiftRefine
public import ConAgua.Arena.Keeps
public import ConAgua.Arena.WriteSets
public import ConAgua.Census.Attr
public import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Arena.DerRel
import ConAgua.Arena.FVarRangeRefine
import ConAgua.Arena.View
import ConAgua.L.WordOff

@[expose] public section

/-!
# `instantiate_lift_fast` refines the arena's `instantiateLiftFast` (lanes `tails`, `ronsync3`)

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
* **The values' slice `SlR`** (`IW[o ‥ o + l)`, push order): every callee leaves the `IW` pool as
  it is (`IWEq`, from its write set), so the slice holds at every node.

The counter word `fu` is the twin's `fuel` exactly; the statements hold at
every L fuel.
-/

open ConRon.Arena ConLeche
open Std.WP
open scoped Lean.Order


namespace L.Arena

theorem i1lSch_wf : i1lSch.WF := ⟨by decide, by decide⟩

/-! ## The `instantiateLift` memo tier -/

/-- The `inst1LC` relation. -/
def I1R (m : Mem) (a : AState) : Prop := MemoRG i1lSch lfKey decE m a.memos.inst1LC

/-- `ArenaD` and the `instantiateLift` memo. -/
def ArenaI (m : Mem) (a : AState) : Prop := ArenaD m a ∧ I1R m a

/-- The arena state with the `instantiateLift` memo replaced. -/
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
  ⟨hD.base.with_memos (MemFrame.refl [] [] m) (by simp) (by simp)
    ⟨hD.base.memos.bvar, hD.base.memos.lift, hD.base.memos.inst1, hD.base.memos.fvar⟩,
    DerR.of_store m a _ hD.der rfl⟩

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
theorem I1R.across {A : List TieredArray} {C : List Word} {m m' : Mem} {a a' : AState}
    (hR : I1R m a) (hf : MemFrame A C m m') (hA : (ILFM : TieredArray) ∉ A) (hC : (52 : Word) ∉ C)
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
  (msetG_frame lfSch lfSch_wf m m' h c v hs).mono (by simp [liftA, LMEMO])
    (by simp [liftC])

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
  (L.Arena.mkAppW_frame m m' x y r h).mono (by simp [tier1, liftA, AREC, ASLOT, ADER]) (by simp [liftC])
theorem mkLamW_lf (m : Mem) (x y : Word) : LfOK m (mkLamW m x y) := fun r m' h =>
  (mkLamW_frameA m m' x y r h).mono (by simp [tier1, liftA, LAREC, LASLOT, LADER]) (by simp [liftC])
theorem mkForallW_lf (m : Mem) (x y : Word) : LfOK m (mkForallW m x y) := fun r m' h =>
  (mkForallW_frameA m m' x y r h).mono (by simp [tier1, liftA, FAREC, FASLOT, FADER]) (by simp [liftC])
theorem mkLetW_lf (m : Mem) (x y z : Word) : LfOK m (mkLetW m x y z) := fun r m' h =>
  (mkLetW_frameA m m' x y z r h).mono (by simp [tier1, liftA, LEREC, LESLOT, LEDER]) (by simp [liftC])
theorem mkProjW_lf (m : Mem) (a b x : Word) : LfOK m (mkProjW m a b x) := fun r m' h =>
  (mkProjW_frameA m m' a b x r h).mono (by simp [tier1, liftA, PJREC, PJSLOT, PJDER]) (by simp [liftC])
theorem binternW_lf (m : Mem) (u : Word) : LfOK m (binternW m u) := fun r m' h =>
  (binternW_frameA m m' u r h).mono (by simp [tier1, liftA, BREC, BSLOT]) (by simp [liftC])

theorem lfRet (m : Mem) (h : Word) : LfOK m (some (h, m)) := fun _ _ e => by
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj e); exact MemFrame.refl _ _ _

theorem LfOK.none (m : Mem) : LfOK m none := fun _ _ h => by cases h

theorem LfOK.ite {m : Mem} {p : Prop} [Decidable p] {a b : Option (Word × Mem)} (ha : LfOK m a)
    (hb : LfOK m b) : LfOK m (if p then a else b) := by
  by_cases hp : p
  · rw [ite_eq_left hp]; exact ha
  · rw [ite_eq_right hp]; exact hb

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
    (mclearG_frame lfSch m).mono (by simp) (by simp [liftC])
  cases hw : liftW n (mclearG lfSch m) h c k f with
  | none => simp [hw, liftEntryW.k_lift_go] at hb
  | some p =>
    obtain ⟨r₁, m₁⟩ := p
    have h1 : ¬ rdW (m₁.arr64 CTL) lfSch.cs + 2 = 0 := fun h1 => by simp [hw, liftEntryW.k_lift_go, h1] at hb
    rw [hw, liftEntryW.k_lift_go.arm1 r₁ m₁ h1, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact (hc0.trans ((liftW_frame n).1 _ _ _ _ _ _ _ hw)).trans
      ((mclearG_frame lfSch m₁).mono (by simp) (by simp [liftC]))

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
  exact ⟨hok, ⟨hD, hA.2.across (L.Arena.mkAppW_frame m m' f x r hI) (by decide) (by decide)
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

theorem bvbW_frame (n : Nat) (m m' : Mem) (h f x : Word) (hb : bvbW n m f h = some (x, m')) :
    BbFrame m m' := by
  obtain ⟨n, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by cases n <;> simp_all [bvbW]⟩
  by_cases hs : derBW m h = 32767
  · rw [bvbW.arm1 n m f h hs] at hb
    obtain ⟨n, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by cases n <;> simp_all [bbN]⟩
    rw [bbN_succ] at hb
    exact bbMemoW_frame n m m' h f x hb
  · rw [bvbW.arm2 n m f h hs] at hb
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    exact MemFrame.refl _ _ _

/-- **`bvar_b`'s model under `ArenaI`.** -/
theorem bvbW_okI (n : Nat) (m m' : Mem) (a : AState) (hA : ArenaI m a)
    (h f x : Word) (hh : h.toNat < 2 ^ 32) (hb : bvbW n m f h = some (x, m')) :
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

/-! ## The values' slice, and the walk keeps it -/

/-- The `IW` pool is the same in `m'` as in `m` (the walk writes no `IW` word). -/
abbrev IWEq (m m' : Mem) : Prop := m'.arr64 LPIW = m.arr64 LPIW

/-- **The values' slice**: `IW[o ‥ o + l)` holds the handles of `vs` (push order, entry `q` at
`o + q`), each below `2^32`. -/
def SlR (m : Mem) (o l : Word) (vs : Array EIdx) : Prop :=
  vs.size = l.toNat ∧ ∀ q : Word, q < l →
    (rdW (m.arr64 LPIW) (o + q)).toNat < 2 ^ 32 ∧ vs[q.toNat]? = some (decE (rdW (m.arr64 LPIW) (o + q)))

theorem SlR.of_eq {m m' : Mem} {o l : Word} {vs : Array EIdx} (h : SlR m o l vs) (he : IWEq m m') :
    SlR m' o l vs := by
  unfold SlR; rw [he]; exact h

theorem IWEq.trans {m₁ m₂ m₃ : Mem} (h₁ : IWEq m₁ m₂) (h₂ : IWEq m₂ m₃) : IWEq m₁ m₃ :=
  Eq.trans h₂ h₁

/-- The value index `l - 1 - k` of the variable `k` past the cursor. -/
theorem qidx (l k : Word) (hk : k < l) : l - 1 - k < l ∧ (l - 1 - k).toNat = l.toNat - 1 - k.toNat := by
  have h1 := UInt64.lt_iff_toNat_lt.mp hk
  have e1 : (l - 1).toNat = l.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp
  have e2 : (l - 1 - k).toNat = l.toNat - 1 - k.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), e1]
  exact ⟨UInt64.lt_iff_toNat_lt.mpr (by omega), e2⟩

theorem IWEq.of_frame {A : List TieredArray} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : (LPIW : TieredArray) ∉ A) : IWEq m m' := hf.arr _ hA (by decide)

theorem iw_bvb {n : Nat} {m m' : Mem} {h f x : Word} (hb : bvbW n m f h = some (x, m')) : IWEq m m' :=
  IWEq.of_frame (bvbW_frame n m m' h f x hb) (by decide)
theorem iw_lift {n : Nat} {m m' : Mem} {h k c f r : Word} (hb : liftEntryW n m h k c f = some (r, m')) :
    IWEq m m' := IWEq.of_frame (liftEntryW_frame n m h k c f r m' hb) (by decide)
theorem iw_bintern {m m' : Mem} {u r : Word} (hb : binternW m u = some (r, m')) : IWEq m m' :=
  IWEq.of_frame (binternW_frameA m m' u r hb) (by decide)
theorem iw_mkApp {m m' : Mem} {x y r : Word} (hb : mkAppW m x y = some (r, m')) : IWEq m m' :=
  IWEq.of_frame (L.Arena.mkAppW_frame m m' x y r hb) (by decide)
theorem iw_mkLam {m m' : Mem} {x y r : Word} (hb : mkLamW m x y = some (r, m')) : IWEq m m' :=
  IWEq.of_frame (mkLamW_frameA m m' x y r hb) (by decide)
theorem iw_mkForall {m m' : Mem} {x y r : Word} (hb : mkForallW m x y = some (r, m')) : IWEq m m' :=
  IWEq.of_frame (mkForallW_frameA m m' x y r hb) (by decide)
theorem iw_mkLet {m m' : Mem} {x y z r : Word} (hb : mkLetW m x y z = some (r, m')) : IWEq m m' :=
  IWEq.of_frame (mkLetW_frameA m m' x y z r hb) (by decide)
theorem iw_mkProj {m m' : Mem} {a b x r : Word} (hb : mkProjW m a b x = some (r, m')) : IWEq m m' :=
  IWEq.of_frame (mkProjW_frameA m m' a b x r hb) (by decide)
theorem iw_mset {m m' : Mem} {h c v : Word} (hs : msetG i1lSch m h c v = some m') : IWEq m m' :=
  IWEq.of_frame (msetG_frame i1lSch i1lSch_wf m m' h c v hs) (by decide)
theorem iw_mclear (m : Mem) : IWEq m (mclearG i1lSch m) :=
  IWEq.of_frame (mclearG_frame i1lSch m) (by decide)

/-! ## The twin's dispatcher, named -/

/-- The part of `instantiateLiftGo` after the cut-off: the view's arms. -/
def ilNodeA (vs : Array EIdx) (F : Nat) (h : EIdx) (d : Nat) : ENodeView → AM EIdx
  | .bvar i =>
    if i < d then pure h
    else if hlt : i - d < vs.size then
      liftLooseBVarsFast F d 0 (vs[vs.size - 1 - (i - d)]'(by omega))
    else internE (.bvar (i - vs.size))
  | .fvar _ _ => pure h
  | .sort _ => pure h
  | .const _ _ => pure h
  | .lit _ => pure h
  | .app f a => instLiftArmApp vs F h d f a
  | .lam ty body => instLiftArmLam vs F h d ty body
  | .forallE ty body => instLiftArmForallE vs F h d ty body
  | .letE ty val body => instLiftArmLet vs F h d ty val body
  | .proj n i sub => instLiftArmProj vs F h d n i sub

theorem instantiateLiftGo_succ' (vs : Array EIdx) (F : Nat) (h : EIdx) (d : Nat) :
    instantiateLiftGo vs (F + 1) h d = (do
      let bb ← bvarB F h
      if bb ≤ d then pure h else (view h >>= ilNodeA vs F h d)) := by
  rw [instantiateLiftGo_succ]; rfl

/-! ## The statements, by fuel -/

/-- What `i1l_go`'s model at L fuel `n` and counter `fu` says about the arena walk at the twin
fuel `fu.toNat`, over the values' slice `(o, l)`. -/
def LIGoOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (h d o l fu r : Word) (vs : Array EIdx), ArenaI m a →
    h.toNat < 2 ^ 32 → SlR m o l vs → i1lW n m h d o l fu = some (r, m') →
    ∃ a', (instantiateLiftGo vs fu.toNat (decE h) d.toNat).run a = .ok (decE r, a') ∧
      ArenaI m' a' ∧ IWEq m m'

/-- The arena arm `arm` refines the L arm `armW` (with its counter) at `h`. -/
def LIArmRef (n : Nat) (armW : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem))
    (arm : AM EIdx) (m m' : Mem) (a : AState) (h d o l fu r : Word) : Prop :=
  armW n m h d o l fu = some (r, m') → ∃ a', arm.run a = .ok (decE r, a') ∧ ArenaI m' a' ∧ IWEq m m'

/-- The five arms, given the view checks of each. -/
def LIArmOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (h d o l fu r : Word) (vs : Array EIdx), ArenaI m a →
    h.toNat < 2 ^ 32 → SlR m o l vs →
    (viewOKA m h → tagW h = 4 → LIArmRef n i1lAppW
      (instLiftArmApp vs fu.toNat (decE h) d.toNat
        (decE (tfld m APP (tierW h) (idxA h) 0))
        (decE (tfld m APP (tierW h) (idxA h) 1))) m m' a h d o l fu r) ∧
    (viewOK m h LAM → tagW h = 5 → LIArmRef n i1lLamW
      (instLiftArmLam vs fu.toNat (decE h) d.toNat
        (decE (tfld m LAM (tierW h) (idxW h) 0))
        (decE (tfld m LAM (tierW h) (idxW h) 1))) m m' a h d o l fu r) ∧
    (viewOK m h FORALL → tagW h = 6 → LIArmRef n i1lForallW
      (instLiftArmForallE vs fu.toNat (decE h) d.toNat
        (decE (tfld m FORALL (tierW h) (idxW h) 0))
        (decE (tfld m FORALL (tierW h) (idxW h) 1))) m m' a h d o l fu r) ∧
    (viewOK m h LET → tagW h = 7 → LIArmRef n i1lLetW
      (instLiftArmLet vs fu.toNat (decE h) d.toNat
        (decE (tfld m LET (tierW h) (idxW h) 0))
        (decE (tfld m LET (tierW h) (idxW h) 1))
        (decE (tfld m LET (tierW h) (idxW h) 2))) m m' a h d o l fu r) ∧
    (viewOK m h PROJ → tagW h = 9 → LIArmRef n i1lProjW
      (instLiftArmProj vs fu.toNat (decE h) d.toNat
        (decI (tfld m PROJ (tierW h) (idxW h) 0))
        (tfld m PROJ (tierW h) (idxW h) 1).toNat
        (decE (tfld m PROJ (tierW h) (idxW h) 2))) m m' a h d o l fu r)

/-! ## The dispatcher -/

/-- **The `bvar` arm**: below `d` the node itself, a value lifted past the `d` binders, past the
values the variable lowered by their count. -/
theorem i1lBVar_ok (n : Nat) (m₁ m' : Mem) (a₁ : AState) (hA₁ : ArenaI m₁ a₁) (h d o l fu x r : Word)
    (vs : Array EIdx) (hsl : SlR m₁ o l vs) (hcut : ¬ x ≤ d)
    (hs : ¬ (tierW h ≠ 0 ∧ rdW (m₁.arr64 CTL) 1 = 0)) (g0 : tagW h = 0)
    (hc : ¬ tcnt m₁ BVAR (tierW h) ≤ idxW h)
    (hb : i1lW.k_bvar_b n h d o l fu (some (x, m₁)) = some (r, m')) :
    ∃ a', (ilNodeA vs (fu - 1).toNat (decE h) d.toNat
        (.bvar (tfld m₁ BVAR (tierW h) (idxW h) 0).toNat)).run a₁ = .ok (decE r, a') ∧
      ArenaI m' a' ∧ IWEq m₁ m' := by
  obtain ⟨X, hX⟩ : ∃ X, tfld m₁ BVAR (tierW h) (idxW h) 0 = X := ⟨_, rfl⟩
  rw [hX]
  simp only [ilNodeA]
  by_cases hlt : X < d
  · rw [i1lW.k_bvar_b.arm2 n h d o l fu x m₁ hcut hs g0 hc (hX ▸ hlt)] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    have : X.toNat < d.toNat := hlt
    simp only [this, ↓reduceIte]; exact ⟨a₁, rfl, And.intro hA₁ (by first | rfl | trivial)⟩
  have hge : d.toNat ≤ X.toNat := by have := mt UInt64.lt_iff_toNat_lt.mpr hlt; omega
  have hsub : (X - d).toNat = X.toNat - d.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hge)]
  have hlt' : ¬ X.toNat < d.toNat := by omega
  simp only [hlt', ↓reduceIte]
  by_cases hv : X - d < l
  · rw [i1lW.k_bvar_b.arm3 n h d o l fu x m₁ hcut hs g0 hc (hX ▸ hlt) (hX ▸ hv), hX] at hb
    have hv' : X.toNat - d.toNat < vs.size := by
      have := UInt64.lt_iff_toNat_lt.mp hv; rw [hsl.1]; omega
    obtain ⟨hq, hqn⟩ := qidx l (X - d) hv
    obtain ⟨hw32, hwv⟩ := hsl.2 _ hq
    rw [hqn, hsub, ← hsl.1, Array.getElem?_eq_getElem (by omega)] at hwv
    rw [dite_eq_left hv', Option.some.inj hwv]
    obtain ⟨a', ha', hA'⟩ := liftEntryW_okI n m₁ m' a₁ hA₁ _ d 0 (fu - 1) r hw32 hb
    exact ⟨a', by simpa using ha', And.intro hA' (iw_lift hb)⟩
  · rw [i1lW.k_bvar_b.arm4 n h d o l fu x m₁ hcut hs g0 hc (hX ▸ hlt) (hX ▸ hv), hX] at hb
    have hv' : ¬ X.toNat - d.toNat < vs.size := by
      have := mt UInt64.lt_iff_toNat_lt.mpr hv; rw [hsl.1]; omega
    rw [dite_eq_right hv']
    obtain ⟨hok, hA', hres⟩ := internBVar_I m₁ a₁ hA₁ _ r m' hb
    have hsz : (X - l).toNat = X.toNat - vs.size := by
      have := mt UInt64.lt_iff_toNat_lt.mpr hv
      rw [hsl.1, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))]
    rw [← hsz, AM.run_of_ok _ _ hok, hres]; exact ⟨_, rfl, And.intro hA' (iw_bintern hb)⟩

theorem ligoOK_succ (n : Nat) (ih : LIArmOK n) : LIGoOK (n + 1) := by
  intro m m' a h d o l fu r vs hA hh hsl hb
  have hfu : ¬ fu = 0 := fun hfu => by rw [i1lW] at hb; simp [hfu] at hb
  rw [i1lW.arm1 n m h d o l fu hfu] at hb
  rw [L.toNat_eq_toNat_sub_one_add_one fu hfu, instantiateLiftGo_succ', StateT.run_bind]
  cases hx : bvbW n m (fu - 1) h with
  | none => rw [hx, i1lW.k_bvar_b] at hb; cases hb
  | some p =>
  obtain ⟨x, m₁⟩ := p
  rw [hx] at hb
  obtain ⟨a₁, ha₁, hA₁⟩ := bvbW_okI n m m₁ a hA h (fu - 1) x hh hx
  have hI₁ : IWEq m m₁ := iw_bvb hx
  have hsl₁ := hsl.of_eq hI₁
  rw [ha₁, except_ok_bind]
  by_cases hcut : x ≤ d
  · rw [i1lW.k_bvar_b.arm1 n h d o l fu x m₁ hcut] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    simp only [UInt64.le_iff_toNat_le.mp hcut, ↓reduceIte]
    exact ⟨a₁, rfl, hA₁, hI₁⟩
  have hcut' : ¬ x.toNat ≤ d.toNat := fun e => hcut (UInt64.le_iff_toNat_le.mpr e)
  simp only [hcut', ↓reduceIte, StateT.run_bind]
  have hR := hA₁.1.1
  by_cases hs : tierW h ≠ 0 ∧ rdW (m₁.arr64 CTL) 1 = 0
  · rw [i1lW.k_bvar_b] at hb; simp [hcut, hs] at hb
  have vok : ∀ c0, ¬ tcnt m₁ c0 (tierW h) ≤ idxW h → viewOK m₁ h c0 :=
    fun c0 hc => ⟨hs, UInt64.not_le.mp hc⟩
  have done : ∀ w, a₁.store.view (decE h) = some w →
      (∃ a', (ilNodeA vs (fu - 1).toNat (decE h) d.toNat w).run a₁ = .ok (decE r, a') ∧
        ArenaI m' a' ∧ IWEq m₁ m') →
      ∃ a', ((view (decE h)).run a₁ >>= fun p => (ilNodeA vs (fu - 1).toNat (decE h) d.toNat p.1).run p.2) =
        .ok (decE r, a') ∧ ArenaI m' a' ∧ IWEq m m' := by
    intro w hw ⟨a', h1, h2, h3⟩
    rw [view_run _ a₁ w hw]; exact ⟨a', h1, h2, hI₁.trans h3⟩
  have pure_h : ∀ w, a₁.store.view (decE h) = some w →
      i1lW.k_bvar_b n h d o l fu (some (x, m₁)) = some (h, m₁) →
      (ilNodeA vs (fu - 1).toNat (decE h) d.toNat w).run a₁ = .ok (decE h, a₁) →
      ∃ a', ((view (decE h)).run a₁ >>= fun p => (ilNodeA vs (fu - 1).toNat (decE h) d.toNat p.1).run p.2) =
        .ok (decE r, a') ∧ ArenaI m' a' ∧ IWEq m m' := by
    intro w hw hl hy
    rw [hl] at hb; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    exact done w hw ⟨a₁, hy, hA₁, rfl⟩
  by_cases g0 : tagW h = 0
  · by_cases hc : tcnt m₁ BVAR (tierW h) ≤ idxW h
    · rw [i1lW.k_bvar_b] at hb; simp [hcut, hs, g0, hc] at hb
    exact done _ (view_bvar m₁ a₁ hR h hh (vok BVAR hc) g0)
      (i1lBVar_ok n m₁ m' a₁ hA₁ h d o l fu x r vs hsl₁ hcut hs g0 hc hb)
  by_cases g1 : tagW h = 1
  · by_cases hc : tcnt m₁ FVAR (tierW h) ≤ idxW h
    · rw [i1lW.k_bvar_b] at hb; simp [hcut, hs, g1, hc] at hb
    obtain ⟨_, _, hw⟩ := view_fvar m₁ a₁ hR h hh (vok FVAR hc) g1
    exact pure_h _ hw (i1lW.k_bvar_b.arm5 n h d o l fu x m₁ hcut hs g0 g1 hc) rfl
  by_cases g2 : tagW h = 2
  · by_cases hc : tcnt m₁ SORT (tierW h) ≤ idxW h
    · rw [i1lW.k_bvar_b] at hb; simp [hcut, hs, g2, hc] at hb
    obtain ⟨_, hw⟩ := view_sort m₁ a₁ hR h hh (vok SORT hc) g2
    exact pure_h _ hw (i1lW.k_bvar_b.arm6 n h d o l fu x m₁ hcut hs g0 g1 g2 hc) rfl
  by_cases g3 : tagW h = 3
  · by_cases hc : tcnt m₁ CONST (tierW h) ≤ idxW h
    · rw [i1lW.k_bvar_b] at hb; simp [hcut, hs, g3, hc] at hb
    obtain ⟨_, _, hw⟩ := view_const m₁ a₁ hR h hh (vok CONST hc) g3
    exact pure_h _ hw (i1lW.k_bvar_b.arm7 n h d o l fu x m₁ hcut hs g0 g1 g2 g3 hc) rfl
  by_cases g8 : tagW h = 8
  · by_cases hc : tcnt m₁ LIT (tierW h) ≤ idxW h
    · rw [i1lW.k_bvar_b] at hb; simp [hcut, hs, g8, hc] at hb
    obtain ⟨_, hw⟩ := view_lit m₁ a₁ hR h hh (vok LIT hc) g8
    exact pure_h _ hw (i1lW.k_bvar_b.arm8 n h d o l fu x m₁ hcut hs g0 g1 g2 g3 g8 hc) rfl
  have arm := ih m₁ m' a₁ h d o l (fu - 1) r vs hA₁ hh hsl₁
  by_cases g4 : tagW h = 4
  · by_cases hc : tcnt m₁ APP (tierW h) ≤ idxA h
    · rw [i1lW.k_bvar_b] at hb; simp [hcut, hs, g4, hc] at hb
    rw [i1lW.k_bvar_b.arm9 n h d o l fu x m₁ hcut hs g0 g1 g2 g3 g8 g4 hc] at hb
    exact done _ (view_app m₁ a₁ hR h hh ⟨hs, UInt64.not_le.mp hc⟩ g4).1
      (arm.1 ⟨hs, UInt64.not_le.mp hc⟩ g4 hb)
  by_cases g5 : tagW h = 5
  · by_cases hc : tcnt m₁ LAM (tierW h) ≤ idxW h
    · rw [i1lW.k_bvar_b] at hb; simp [hcut, hs, g5, hc] at hb
    rw [i1lW.k_bvar_b.arm10 n h d o l fu x m₁ hcut hs g0 g1 g2 g3 g8 g4 g5 hc] at hb
    exact done _ (view_lam m₁ a₁ hR h hh (vok LAM hc) g5).1 (arm.2.1 (vok LAM hc) g5 hb)
  by_cases g6 : tagW h = 6
  · by_cases hc : tcnt m₁ FORALL (tierW h) ≤ idxW h
    · rw [i1lW.k_bvar_b] at hb; simp [hcut, hs, g6, hc] at hb
    rw [i1lW.k_bvar_b.arm11 n h d o l fu x m₁ hcut hs g0 g1 g2 g3 g8 g4 g5 g6 hc] at hb
    exact done _ (view_forall m₁ a₁ hR h hh (vok FORALL hc) g6).1 (arm.2.2.1 (vok FORALL hc) g6 hb)
  by_cases g7 : tagW h = 7
  · by_cases hc : tcnt m₁ LET (tierW h) ≤ idxW h
    · rw [i1lW.k_bvar_b] at hb; simp [hcut, hs, g7, hc] at hb
    rw [i1lW.k_bvar_b.arm12 n h d o l fu x m₁ hcut hs g0 g1 g2 g3 g8 g4 g5 g6 g7 hc] at hb
    exact done _ (view_let m₁ a₁ hR h hh (vok LET hc) g7).1 (arm.2.2.2.1 (vok LET hc) g7 hb)
  by_cases g9 : tagW h = 9
  · by_cases hc : tcnt m₁ PROJ (tierW h) ≤ idxW h
    · rw [i1lW.k_bvar_b] at hb; simp [hcut, hs, g9, hc] at hb
    rw [i1lW.k_bvar_b.arm13 n h d o l fu x m₁ hcut hs g0 g1 g2 g3 g8 g4 g5 g6 g7 g9 hc] at hb
    exact done _ (view_proj m₁ a₁ hR h hh (vok PROJ hc) g9).1 (arm.2.2.2.2 (vok PROJ hc) g9 hb)
  rw [i1lW.k_bvar_b] at hb; simp [hcut, hs, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9] at hb

/-! ## The arms -/

/-- **The tail of every arm**: intern the rebuilt node and record it in the memo. -/
theorem i1lTail_ok (op : AM EIdx) (mkr : Option (Word × Mem)) (a₂ : AState) (h d r : Word)
    (m₂ m' : Mem) (hh : h.toNat < 2 ^ 32)
    (hmk : ∀ r₃ m₃, mkr = some (r₃, m₃) →
      AM.ok op a₂ ∧ ArenaI m₃ (AM.st op a₂) ∧ AM.res op a₂ = decE r₃ ∧ IWEq m₂ m₃)
    (hb : i1lAppW.k_mk_app h d mkr = some (r, m')) :
    ∃ a', (do let r ← op; inst1LSet (decE h, d.toNat) r; pure r : AM EIdx).run a₂ =
      .ok (decE r, a') ∧ ArenaI m' a' ∧ IWEq m₂ m' := by
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
      obtain ⟨hok, hA₃, hres, hI₃⟩ := hmk r₃ m₃ h3
      refine ⟨_, ?_, ArenaI.imemo_set m₃ m₄ _ hA₃ h d r₃ hh hs, hI₃.trans (iw_mset hs)⟩
      simp only [StateT.run_bind, AM.run_of_ok _ _ hok, hres, except_ok_bind, inst1LSet_run]; rfl

/-- **The memo probe of every arm**: a hit is the memo's value; a miss runs `miss`. -/
theorem i1lProbe_ok (armW : Option (Word × Mem)) (miss : AM EIdx) (m m' : Mem) (a : AState)
    (hA : ArenaI m a) (h d r : Word) (hh : h.toNat < 2 ^ 32)
    (hhit : mfindG i1lSch m h d ≠ [] → (mfindG i1lSch m h d).headD 0 ≠ 0 →
      armW = some (rdW (m.arr64 ILFM) ((mfindG i1lSch m h d).tail.headD 0 * 4 + 3), m))
    (hnone : mfindG i1lSch m h d = [] → armW = none)
    (hmiss : mfindG i1lSch m h d ≠ [] → (mfindG i1lSch m h d).headD 0 = 0 → armW = some (r, m') →
      ∃ a', miss.run a = .ok (decE r, a') ∧ ArenaI m' a' ∧ IWEq m m')
    (hb : armW = some (r, m')) :
    ∃ a', (do
        match ← inst1LGet (decE h, d.toNat) with
        | some r => pure r
        | none => miss : AM EIdx).run a = .ok (decE r, a') ∧ ArenaI m' a' ∧ IWEq m m' := by
  rw [StateT.run_bind, inst1LGet_run, except_ok_bind]
  have hr : ¬ mfindG i1lSch m h d = [] := fun hr => by rw [hnone hr] at hb; cases hb
  by_cases hh0 : (mfindG i1lSch m h d).headD 0 ≠ 0
  · rw [hhit hr hh0] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    rw [show a.memos.inst1LC[(decE h, d.toNat)]? = _ from
      memoRG_hit i1lSch lfKey decE m _ hA.2 h d hr hh0 hh]
    exact ⟨a, rfl, hA, rfl⟩
  · simp only [ne_eq, Decidable.not_not] at hh0
    rw [show a.memos.inst1LC[(decE h, d.toNat)]? = none from
      memoRG_miss i1lSch lfKey decE m _ hA.2 h d hh hr hh0]
    exact hmiss hr hh0 hb

section arms
variable (n : Nat) (ih : LIGoOK n) (m m' : Mem) (a : AState) (hA : ArenaI m a)
  (h d o l fu r : Word) (vs : Array EIdx) (hh : h.toNat < 2 ^ 32) (hsl : SlR m o l vs)
include ih hA hh hsl

theorem i1lAppArm_ok (hvw : viewOKA m h) (hg : tagW h = 4) :
    LIArmRef (n + 1) i1lAppW
      (instLiftArmApp vs fu.toNat (decE h) d.toNat
        (decE (tfld m APP (tierW h) (idxA h) 0))
        (decE (tfld m APP (tierW h) (idxA h) 1))) m m' a h d o l fu r := by
  intro hb
  obtain ⟨-, hfw, haw⟩ := view_app m a hA.1.1 h hh hvw hg
  rw [instLiftArmApp]
  refine i1lProbe_ok _ _ m m' a hA h d r hh (i1lAppW.arm1 n m h d o l fu)
    (fun hr => by rw [i1lAppW]; simp [hr]) (fun hr hh0 hb => ?_) hb
  rw [i1lAppW.arm2 n m h d o l fu hr hh0] at hb
  cases h1 : i1lW n m (tfld m APP (tierW h) (idxA h) 0) d o l fu with
  | none => simp [h1, i1lAppW.k_i1l_go] at hb
  | some p =>
  obtain ⟨x, m₁⟩ := p
  rcases h2 : i1lW n m₁ (tfld m APP (tierW h) (idxA h) 1) d o l fu with _ | ⟨y, m₂⟩ <;> simp only [h2, h1, i1lAppW.k_i1l_go, i1lAppW.k_i1l_go_2, reduceCtorEq] at hb
  obtain ⟨a₁, ha₁, hA₁, hI₁⟩ := ih m m₁ a _ d o l fu x vs hA hfw hsl h1
  obtain ⟨a₂, ha₂, hA₂, hI₂⟩ := ih m₁ m₂ a₁ _ d o l fu y vs hA₁ haw (hsl.of_eq hI₁) h2
  obtain ⟨a', h3, h4, hI₃⟩ := i1lTail_ok _ _ a₂ h d r m₂ m' hh
    (fun r₃ m₃ h => (mkApp_okI m₂ a₂ hA₂ x y r₃ m₃ h).imp_right fun e => e.imp_right fun e' => ⟨e', iw_mkApp h⟩) hb
  exact ⟨a', by simp only [StateT.run_bind, ha₁, ha₂, except_ok_bind]; exact h3, h4,
    (hI₁.trans hI₂).trans hI₃⟩

theorem i1lLamArm_ok (hvw : viewOK m h LAM) (hg : tagW h = 5) :
    LIArmRef (n + 1) i1lLamW
      (instLiftArmLam vs fu.toNat (decE h) d.toNat
        (decE (tfld m LAM (tierW h) (idxW h) 0))
        (decE (tfld m LAM (tierW h) (idxW h) 1))) m m' a h d o l fu r := by
  intro hb
  have hd1 : ¬ d + 1 = 0 := fun hd1 => by rw [i1lLamW] at hb; simp [hd1] at hb
  obtain ⟨-, hfw, haw⟩ := view_lam m a hA.1.1 h hh hvw hg
  rw [instLiftArmLam]
  refine i1lProbe_ok _ _ m m' a hA h d r hh (i1lLamW.arm1 n m h d o l fu hd1)
    (fun hr => by rw [i1lLamW]; simp [hd1, hr]) (fun hr hh0 hb => ?_) hb
  rw [i1lLamW.arm2 n m h d o l fu hd1 hr hh0] at hb
  cases h1 : i1lW n m (tfld m LAM (tierW h) (idxW h) 0) d o l fu with
  | none => simp [h1, i1lLamW.k_i1l_go] at hb
  | some p =>
  obtain ⟨x, m₁⟩ := p
  rcases h2 : i1lW n m₁ (tfld m LAM (tierW h) (idxW h) 1) (d + 1) o l fu with _ | ⟨y, m₂⟩ <;> simp only [h2, h1, i1lLamW.k_i1l_go, i1lLamW.k_i1l_go_2, reduceCtorEq] at hb
  obtain ⟨a₁, ha₁, hA₁, hI₁⟩ := ih m m₁ a _ d o l fu x vs hA hfw hsl h1
  obtain ⟨a₂, ha₂, hA₂, hI₂⟩ := ih m₁ m₂ a₁ _ (d + 1) o l fu y vs hA₁ haw (hsl.of_eq hI₁) h2
  rw [L.toNat_add_one_of_ne d hd1] at ha₂
  obtain ⟨a', h3, h4, hI₃⟩ := i1lTail_ok _ _ a₂ h d r m₂ m' hh
    (fun r₃ m₃ h => (mkLam_okI m₂ a₂ hA₂ x y r₃ m₃ h).imp_right fun e => e.imp_right fun e' => ⟨e', iw_mkLam h⟩) hb
  exact ⟨a', by simp only [StateT.run_bind, ha₁, ha₂, except_ok_bind]; exact h3, h4,
    (hI₁.trans hI₂).trans hI₃⟩

theorem i1lForallArm_ok (hvw : viewOK m h FORALL) (hg : tagW h = 6) :
    LIArmRef (n + 1) i1lForallW
      (instLiftArmForallE vs fu.toNat (decE h) d.toNat
        (decE (tfld m FORALL (tierW h) (idxW h) 0))
        (decE (tfld m FORALL (tierW h) (idxW h) 1))) m m' a h d o l fu r := by
  intro hb
  have hd1 : ¬ d + 1 = 0 := fun hd1 => by rw [i1lForallW] at hb; simp [hd1] at hb
  obtain ⟨-, hfw, haw⟩ := view_forall m a hA.1.1 h hh hvw hg
  rw [instLiftArmForallE]
  refine i1lProbe_ok _ _ m m' a hA h d r hh (i1lForallW.arm1 n m h d o l fu hd1)
    (fun hr => by rw [i1lForallW]; simp [hd1, hr]) (fun hr hh0 hb => ?_) hb
  rw [i1lForallW.arm2 n m h d o l fu hd1 hr hh0] at hb
  cases h1 : i1lW n m (tfld m FORALL (tierW h) (idxW h) 0) d o l fu with
  | none => simp [h1, i1lForallW.k_i1l_go] at hb
  | some p =>
  obtain ⟨x, m₁⟩ := p
  rcases h2 : i1lW n m₁ (tfld m FORALL (tierW h) (idxW h) 1) (d + 1) o l fu with _ | ⟨y, m₂⟩ <;> simp only [h2, h1, i1lForallW.k_i1l_go, i1lForallW.k_i1l_go_2, reduceCtorEq] at hb
  obtain ⟨a₁, ha₁, hA₁, hI₁⟩ := ih m m₁ a _ d o l fu x vs hA hfw hsl h1
  obtain ⟨a₂, ha₂, hA₂, hI₂⟩ := ih m₁ m₂ a₁ _ (d + 1) o l fu y vs hA₁ haw (hsl.of_eq hI₁) h2
  rw [L.toNat_add_one_of_ne d hd1] at ha₂
  obtain ⟨a', h3, h4, hI₃⟩ := i1lTail_ok _ _ a₂ h d r m₂ m' hh
    (fun r₃ m₃ h => (mkForall_okI m₂ a₂ hA₂ x y r₃ m₃ h).imp_right fun e => e.imp_right fun e' => ⟨e', iw_mkForall h⟩) hb
  exact ⟨a', by simp only [StateT.run_bind, ha₁, ha₂, except_ok_bind]; exact h3, h4,
    (hI₁.trans hI₂).trans hI₃⟩

theorem i1lLetArm_ok (hvw : viewOK m h LET) (hg : tagW h = 7) :
    LIArmRef (n + 1) i1lLetW
      (instLiftArmLet vs fu.toNat (decE h) d.toNat
        (decE (tfld m LET (tierW h) (idxW h) 0))
        (decE (tfld m LET (tierW h) (idxW h) 1))
        (decE (tfld m LET (tierW h) (idxW h) 2))) m m' a h d o l fu r := by
  intro hb
  have hd1 : ¬ d + 1 = 0 := fun hd1 => by rw [i1lLetW] at hb; simp [hd1] at hb
  obtain ⟨-, htw, hvw', hbw⟩ := view_let m a hA.1.1 h hh hvw hg
  rw [instLiftArmLet]
  refine i1lProbe_ok _ _ m m' a hA h d r hh (i1lLetW.arm1 n m h d o l fu hd1)
    (fun hr => by rw [i1lLetW]; simp [hd1, hr]) (fun hr hh0 hb => ?_) hb
  rw [i1lLetW.arm2 n m h d o l fu hd1 hr hh0] at hb
  cases h1 : i1lW n m (tfld m LET (tierW h) (idxW h) 0) d o l fu with
  | none => simp [h1, i1lLetW.k_i1l_go] at hb
  | some p =>
  obtain ⟨x, m₁⟩ := p
  cases h2 : i1lW n m₁ (tfld m LET (tierW h) (idxW h) 1) d o l fu with
  | none => simp [h1, h2, i1lLetW.k_i1l_go, i1lLetW.k_i1l_go_2] at hb
  | some q =>
  obtain ⟨y, m₂⟩ := q
  rcases h3 : i1lW n m₂ (tfld m LET (tierW h) (idxW h) 2) (d + 1) o l fu with _ | ⟨z, m₃⟩ <;> simp only [h3, h1, h2, i1lLetW.k_i1l_go, i1lLetW.k_i1l_go_2, i1lLetW.k_i1l_go_3, reduceCtorEq] at hb
  obtain ⟨a₁, ha₁, hA₁, hI₁⟩ := ih m m₁ a _ d o l fu x vs hA htw hsl h1
  obtain ⟨a₂, ha₂, hA₂, hI₂⟩ := ih m₁ m₂ a₁ _ d o l fu y vs hA₁ hvw' (hsl.of_eq hI₁) h2
  obtain ⟨a₃, ha₃, hA₃, hI₃⟩ := ih m₂ m₃ a₂ _ (d + 1) o l fu z vs hA₂ hbw
    (hsl.of_eq (hI₁.trans hI₂)) h3
  rw [L.toNat_add_one_of_ne d hd1] at ha₃
  obtain ⟨a', h4, h5, hI₄⟩ := i1lTail_ok _ _ a₃ h d r m₃ m' hh
    (fun r₄ m₄ h => (mkLet_okI m₃ a₃ hA₃ x y z r₄ m₄ h).imp_right fun e => e.imp_right fun e' => ⟨e', iw_mkLet h⟩) hb
  exact ⟨a', by simp only [StateT.run_bind, ha₁, ha₂, ha₃, except_ok_bind]; exact h4, h5,
    ((hI₁.trans hI₂).trans hI₃).trans hI₄⟩

theorem i1lProjArm_ok (hvw : viewOK m h PROJ) (hg : tagW h = 9) :
    LIArmRef (n + 1) i1lProjW
      (instLiftArmProj vs fu.toNat (decE h) d.toNat
        (decI (tfld m PROJ (tierW h) (idxW h) 0))
        (tfld m PROJ (tierW h) (idxW h) 1).toNat
        (decE (tfld m PROJ (tierW h) (idxW h) 2))) m m' a h d o l fu r := by
  intro hb
  obtain ⟨-, -, hew⟩ := view_proj m a hA.1.1 h hh hvw hg
  rw [instLiftArmProj]
  refine i1lProbe_ok _ _ m m' a hA h d r hh (i1lProjW.arm1 n m h d o l fu)
    (fun hr => by rw [i1lProjW]; simp [hr]) (fun hr hh0 hb => ?_) hb
  rw [i1lProjW.arm2 n m h d o l fu hr hh0] at hb
  rcases h1 : i1lW n m (tfld m PROJ (tierW h) (idxW h) 2) d o l fu with _ | ⟨x, m₁⟩ <;> simp only [h1, i1lProjW.k_i1l_go, reduceCtorEq] at hb
  obtain ⟨a₁, ha₁, hA₁, hI₁⟩ := ih m m₁ a _ d o l fu x vs hA hew hsl h1
  obtain ⟨a', h3, h4, hI₂⟩ := i1lTail_ok _ _ a₁ h d r m₁ m' hh
    (fun r₃ m₃ h => (mkProj_okI m₁ a₁ hA₁ _ _ x r₃ m₃ h).imp_right fun e => e.imp_right fun e' => ⟨e', iw_mkProj h⟩) hb
  exact ⟨a', by simp only [StateT.run_bind, ha₁, except_ok_bind]; exact h3, h4, hI₁.trans hI₂⟩

end arms

theorem liarmOK_succ (n : Nat) (ih : LIGoOK n) : LIArmOK (n + 1) := by
  intro m m' a h d o l fu r vs hA hh hsl
  exact ⟨i1lAppArm_ok n ih m m' a hA h d o l fu r vs hh hsl,
    i1lLamArm_ok n ih m m' a hA h d o l fu r vs hh hsl,
    i1lForallArm_ok n ih m m' a hA h d o l fu r vs hh hsl,
    i1lLetArm_ok n ih m m' a hA h d o l fu r vs hh hsl,
    i1lProjArm_ok n ih m m' a hA h d o l fu r vs hh hsl⟩

/-- **The model of `i1l_go` refines `instantiateLiftGo`** at the counter's fuel, for every L
fuel. -/
theorem i1lOK (n : Nat) : LIGoOK n ∧ LIArmOK n := by
  induction n with
  | zero =>
    refine ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ hb => by simp [i1lW] at hb,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ => ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    intro _ _ hb <;> simp [i1lAppW, i1lLamW, i1lForallW, i1lLetW, i1lProjW] at hb
  | succ n ih => exact ⟨ligoOK_succ n ih.2, liarmOK_succ n ih.1⟩

/-! ## The entry `instantiate_lift_fast` refines `instantiateLiftFast` -/

theorem i1lFast_run (F : Nat) (e : EIdx) (vs : Array EIdx) (d : Nat) (a : AState) :
    (instantiateLiftFast F e vs d).run a =
      ((instantiateLiftGo vs F e d).run (withI1C a ∅) >>= fun p => .ok (p.1, withI1C p.2 ∅)) := by
  simp only [instantiateLiftFast, StateT.run_bind, inst1LClear_run, except_ok_bind]
  cases (instantiateLiftGo vs F e d).run (withI1C a ∅) <;> rfl

theorem i1lFastW_correct (n : Nat) (m m' : Mem) (a : AState) (hA : ArenaI m a)
    (f e o l d r : Word) (vs : Array EIdx) (he : e.toNat < 2 ^ 32) (hsl : SlR m o l vs)
    (hb : i1lFastW (n + 1) m f e o l d = some (r, m')) :
    ∃ a', (instantiateLiftFast f.toNat (decE e) vs d.toNat).run a = .ok (decE r, a') ∧
      ArenaI m' a' ∧ r.toNat < 2 ^ 32 ∧ IWEq m m' := by
  have hcs : i1lSch.cs = 52 := rfl
  have h0 : ¬ rdW (m.arr64 CTL) 52 + 2 = 0 := fun h0 => by simp [i1lFastW, h0] at hb
  rw [i1lFastW.arm1 n m f e o l d (by rw [hcs]; exact h0)] at hb
  have hA₀ := ArenaI.imemo_clear m a hA h0
  cases hw : i1lW n (mclearG i1lSch m) e d o l f with
  | none => simp [hw, i1lFastW.k_i1l_go] at hb
  | some p =>
    obtain ⟨r₁, m₁⟩ := p
    have h1 : ¬ rdW (m₁.arr64 CTL) 52 + 2 = 0 := fun h1 => by simp [hw, i1lFastW.k_i1l_go, h1] at hb
    rw [hw, i1lFastW.k_i1l_go.arm1 r₁ m₁ (by rw [hcs]; exact h1), Option.some.injEq,
      Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    obtain ⟨a₁, ha₁, hA₁, hI₁⟩ := (i1lOK n).1 _ _ _ e d o l f r₁ vs hA₀ he
      (hsl.of_eq (iw_mclear m)) hw
    exact ⟨_, by rw [i1lFast_run, ha₁, decE_mask]; rfl, ArenaI.imemo_clear m₁ a₁ hA₁ h1, mask_lt r₁,
      ((iw_mclear m).trans hI₁).trans (iw_mclear m₁)⟩

/-- **`instantiate_lift_fast(f, e, o, l, d)` refines the arena's `instantiateLiftFast f e vs d`**
under `ArenaI` (`ArenaD` and the walk's memo), the values `vs` the `IW` slice `(o, l)` (`SlR`), at
the counter's fuel `f.toNat` and every L fuel: if the L walk returns, the twin's walk succeeds with
the same handle, in a related state; the handle (masked to 32 bits) is below `2^32`, and the `IW`
pool is untouched. -/
@[refines ConRon.Arena.instantiateLiftFast]
theorem i1lFast_refines (p : Prog) (hp : I1lProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (hA : ArenaI s₀.mem a₀) (f e o l d : Word) (vs : Array EIdx) (he : e.toNat < 2 ^ 32)
    (hsl : SlR s₀.mem o l vs) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "instantiate_lift_fast" [f, e, o, l, d]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (instantiateLiftFast f.toNat (decE e) vs d.toNat) a₀ ∧
      ArenaI s'.mem (AM.st (instantiateLiftFast f.toNat (decE e) vs d.toNat) a₀) ∧
      AM.res (instantiateLiftFast f.toNat (decE e) vs d.toNat) a₀ = decE (r.headD 0) ∧
      (r.headD 0).toNat < 2 ^ 32 ∧ IWEq s₀.mem s'.mem; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun (i1lFast_spec p hp (n + 1) s₀ f e o l d)
  subst hs
  obtain ⟨a', ha', hA', hlt, hiw⟩ := i1lFastW_correct n _ _ a₀ hA f e o l d _ vs he hsl hI
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ ha'
  exact ⟨hloc, hok, hst ▸ hA', hres, hlt, hiw⟩

end L.Arena
