import ConRon.Arena.Basis
import ConRon.Bridge.Promote.Pers
import ConRon.Bridge.Checker.Basis

/-!
# `andPinOk` keeps the scratch tier's flag (lane `loopt3`)

The step's bracket opens with `enterScratch`, whose `TwinOK` lemma needs the scratch tier off; the
loop head has it off (`TwinFold.off`), and `andPinOk` runs in between. Its only writes are
interning (the pinned `And` block's `internCIList`, canon's numbered names), and interning keeps
the flag (`EStore.scratchOn` is a field only the bracket's `enterScratch`/`dropScratch` set).
Pure twin reasoning.
-/

open ConRon.Arena

set_option linter.deprecated false

namespace L.Arena

/-- `x` keeps the scratch tier's flag on every accepting run. -/
def KeepsScr {α : Type} (x : AM α) : Prop :=
  ∀ s r s', x s = .ok (r, s') → s'.store.scratchOn = s.store.scratchOn

namespace KeepsScr

theorem pure' {α : Type} (a : α) : KeepsScr (pure a : AM α) := by
  intro s r s' h; exact congrArg (·.store.scratchOn) (ConRon.Bridge.AM.pure_ok h).2

theorem bind' {α β : Type} {x : AM α} {f : α → AM β} (hx : KeepsScr x)
    (hf : ∀ a, KeepsScr (f a)) : KeepsScr (x >>= f) := by
  intro s r s' h
  obtain ⟨a, s1, h1, h2⟩ := ConRon.Bridge.AM.bind_ok h
  exact (hf a _ _ _ h2).trans (hx _ _ _ h1)

theorem ite' {α : Type} {c : Prop} [Decidable c] {x y : AM α} (hx : KeepsScr x)
    (hy : KeepsScr y) : KeepsScr (if c then x else y) := by
  split <;> assumption

theorem fail' {α : Type} (e : CheckError) : KeepsScr (fail e : AM α) :=
  fun _ _ _ h => (ConRon.Bridge.AM.fail_ok h).elim

theorem get' : KeepsScr (get : AM AState) := by
  intro s r s' h; rw [(ConRon.Bridge.AM.get_ok h).2]

/-- A block that reads the state first: its continuation at that very state. -/
theorem getBind {β : Type} {f : AState → AM β}
    (hf : ∀ s r s', f s s = .ok (r, s') → s'.store.scratchOn = s.store.scratchOn) :
    KeepsScr (get >>= f) := by
  intro s r s' h
  obtain ⟨a, s1, h1, h2⟩ := ConRon.Bridge.AM.bind_ok h
  obtain ⟨rfl, rfl⟩ := ConRon.Bridge.AM.get_ok h1
  exact hf _ _ _ h2

end KeepsScr

open KeepsScr

theorem view_ks (h : EIdx) : KeepsScr (view h) :=
  bind' get' fun s => by split <;> first | exact pure' _ | exact fail' _

theorem viewL_ks (h : LIdx) : KeepsScr (viewL h) :=
  bind' get' fun s => by split <;> first | exact pure' _ | exact fail' _

theorem viewLs_ks (h : LsIdx) : KeepsScr (viewLs h) :=
  bind' get' fun s => by split <;> first | exact pure' _ | exact fail' _

theorem internNNode_ks (v : NNodeView) : KeepsScr (internNNode v) := by
  unfold internNNode
  refine getBind fun s r s' h => ?_
  dsimp only at h
  cases hf : s.store.ns.find? v with
  | some k => rw [hf] at h; exact (pure' _) _ _ _ h
  | none =>
    rw [hf] at h
    dsimp only at h
    by_cases hc : (if s.store.ns.scratchOn = true then s.store.ns.scr.sizeOf v
        else s.store.ns.pers.sizeOf v) < Idx.idxCap
    · rw [if_pos hc] at h
      generalize hx : s.store.internName v = x at h
      obtain ⟨st', h'⟩ := x
      obtain ⟨_, t1, h1, h2⟩ := ConRon.Bridge.AM.bind_ok h
      rw [(ConRon.Bridge.AM.pure_ok h2).2, ConRon.Bridge.AM.set_ok h1]
      have : st' = (s.store.internName v).1 := by rw [hx]
      rw [this]; rfl
    · rw [if_neg hc] at h
      exact (ConRon.Bridge.AM.fail_ok h).elim

theorem canonNamesGo_ks : ∀ (n i : Nat), KeepsScr (canonNamesGo i n)
  | 0, i => by unfold canonNamesGo; exact pure' _
  | n + 1, i => by
    unfold canonNamesGo
    exact bind' (internNNode_ks _) fun _ => bind' (internNNode_ks _) fun _ =>
      bind' (canonNamesGo_ks n _) fun _ => pure' _

/-- The combinators, tried in turn (a monadic block of reads, tests and recursive calls). -/
macro "ks_step" : tactic => `(tactic| first
  | exact pure' _ | exact fail' _ | exact view_ks _ | exact viewL_ks _ | exact viewLs_ks _
  | refine ite' ?_ ?_ | refine bind' ?_ fun _ => ?_ | split)

theorem canonLevelEq_ks (ps ps' cs : List NIdx) :
    ∀ (fuel : Nat) (u v : LIdx), KeepsScr (canonLevelEq ps ps' cs fuel u v)
  | 0, u, v => by unfold canonLevelEq; exact fail' _
  | fuel + 1, u, v => by
    have ih := canonLevelEq_ks ps ps' cs fuel
    unfold canonLevelEq
    repeat (first | exact ih _ _ | ks_step)

theorem canonLevelListEq_ks (ps ps' cs : List NIdx) (fuel : Nat) :
    ∀ (us vs : List LIdx), KeepsScr (canonLevelListEq ps ps' cs fuel us vs)
  | [], [] => by unfold canonLevelListEq; exact pure' _
  | u :: us, v :: vs => by
    have ih := canonLevelListEq_ks ps ps' cs fuel us vs
    unfold canonLevelListEq
    repeat (first | exact ih | exact canonLevelEq_ks _ _ _ _ _ _ | ks_step)
  | [], _ :: _ => by unfold canonLevelListEq; exact pure' _
  | _ :: _, [] => by unfold canonLevelListEq; exact pure' _

theorem canonLevelsEq_ks (ps ps' cs : List NIdx) (fuel : Nat) (us vs : LsIdx) :
    KeepsScr (canonLevelsEq ps ps' cs fuel us vs) := by
  unfold canonLevelsEq
  exact bind' (viewLs_ks _) fun _ => bind' (viewLs_ks _) fun _ => canonLevelListEq_ks _ _ _ _ _ _

theorem canonExprEq_ks (ps ps' cs : List NIdx) :
    ∀ (fuel : Nat) (a b : EIdx), KeepsScr (canonExprEq ps ps' cs fuel a b)
  | 0, a, b => by unfold canonExprEq; exact fail' _
  | fuel + 1, a, b => by
    have ih := canonExprEq_ks ps ps' cs fuel
    unfold canonExprEq
    repeat (first | exact ih _ _ | exact canonLevelEq_ks _ _ _ _ _ _ | exact canonLevelsEq_ks _ _ _ _ _ _ | ks_step)

theorem canonRulesEq_ks (ps ps' cs : List NIdx) (fuel : Nat) :
    ∀ (rs rs' : List IRecRule), KeepsScr (canonRulesEq ps ps' cs fuel rs rs')
  | [], [] => by unfold canonRulesEq; exact pure' _
  | r :: rs, r' :: rs' => by
    have ih := canonRulesEq_ks ps ps' cs fuel rs rs'
    unfold canonRulesEq
    repeat (first | exact ih | exact canonExprEq_ks _ _ _ _ _ _ | ks_step)
  | [], _ :: _ => by unfold canonRulesEq; exact pure' _
  | _ :: _, [] => by unfold canonRulesEq; exact pure' _

theorem canonEqCV_ks (cv cv' : IConstantVal) : KeepsScr (cv.canonEq cv') := by
  unfold IConstantVal.canonEq
  repeat (first | exact canonExprEq_ks _ _ _ _ _ _ | exact canonNamesGo_ks _ _ | ks_step)

theorem canonEqCI_ks (c c' : IConstantInfo) : KeepsScr (c.canonEq c') := by
  unfold IConstantInfo.canonEq
  repeat (first | exact canonEqCV_ks _ _ | exact canonExprEq_ks _ _ _ _ _ _ | exact canonNamesGo_ks _ _ | exact canonRulesEq_ks _ _ _ _ _ _ | ks_step)

theorem canonEqList_ks : ∀ (cs cs' : List IConstantInfo), KeepsScr (canonEqList cs cs')
  | [], [] => by unfold canonEqList; exact pure' _
  | c :: cs, c' :: cs' => by
    have ih := canonEqList_ks cs cs'
    unfold canonEqList
    repeat (first | exact ih | exact canonEqCI_ks _ _ | ks_step)
  | [], _ :: _ => by unfold canonEqList; exact pure' _
  | _ :: _, [] => by unfold canonEqList; exact pure' _

/-- **`andPinOk` keeps the scratch tier's flag**, from a well-formed state with its pins: the
name tests only read, the pinned block's interning is an `IStepS` (con-ron's
`internCIList_sstep`), canon's comparisons keep it (`canonEqList_ks`). -/
theorem andPinOk_scratch {pd : IDeclaration} {s s' : AState} {b : Bool}
    (hok : ConRon.Bridge.StateOK s) (hp : ConRon.Bridge.PinsOK s)
    (h : andPinOk pd s = .ok (b, s')) : s'.store.scratchOn = s.store.scratchOn := by
  cases pd with
  | indDecl block nP =>
    simp only [andPinOk] at h
    obtain ⟨hs, s₁, g1, k1⟩ := ConRon.Bridge.AM.bind_ok h
    obtain rfl := ConRon.Bridge.andPinNameHs_run hp g1
    rcases ConRon.Bridge.AM.ite_ok k1 with ⟨-, k2⟩ | ⟨-, k2⟩
    · rcases ConRon.Bridge.AM.ite_ok k2 with ⟨-, k3⟩ | ⟨-, k3⟩
      · obtain ⟨pinned, s₂, g2, k4⟩ := ConRon.Bridge.AM.bind_ok k3
        simp only [andPinDecls, internCIList] at g2
        obtain ⟨q, s₃, hgo, hrest⟩ := ConRon.Bridge.AM.bind_ok g2
        obtain ⟨-, rfl⟩ := ConRon.Bridge.AM.pure_ok hrest
        obtain ⟨hstep, -, -⟩ := ConRon.Bridge.Frontend.internCIList_sstep ConLeche.andPin hok
          (ConRon.Bridge.Frontend.EMemoOK.empty _) hgo
        exact (canonEqList_ks _ _ _ _ _ k4).trans hstep.scratch
      · exact congrArg (·.store.scratchOn) (ConRon.Bridge.AM.pure_ok k3).2
    · exact congrArg (·.store.scratchOn) (ConRon.Bridge.AM.pure_ok k2).2
  | basisDecl _ =>
    simp only [andPinOk] at h
    exact congrArg (·.store.scratchOn) (ConRon.Bridge.AM.pure_ok h).2
  | _ => rw [ConRon.Bridge.andPinNameFree_run hp h]

end L.Arena
