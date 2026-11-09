module

public import ConAgua.Arena.DeclBasisRef
public import ConAgua.Arena.LoopT
public import ConAgua.Arena.TwinStep
public import ConAgua.Arena.Verdict
public import ConRon.Arena.DeclCheck
public import ConAgua.Checker.NoVerdictFns
public import ConAgua.Arena.IndArmBridge2
public import ConAgua.Arena.IndPartsSpec.BlockSplitRecs

@[expose] public section

/-!
# `check_basis_block`'s contract (lane `ronsync2`, stage 3)

`check_ind_decl`'s pinned-block arm: `check_basis_block(vis, kind, bo, bl)` (`DeclArms.lean`) on a
block that `basis_name_hit` matched (an `EREC` slice of record pointers, `BlockAt`) refines
`checkBasisBlock fe kind block`, both outcomes, from `StageC` and the arm's memos, back to the
stage at the returned view with the core's and the inductive stage's memos (`CidPost`).

The contract `CbbRef` is stated at the call (`callE`), so that `cid_ref` takes it as it takes
`check_block`'s (`BlockRefS`).
-/

open ConRon.Arena
open Std.WP

namespace L.Ind

open L.Arena

/-- What `check_ind_decl` (and its two returning callees) gives besides the twin's run, a view `w`
and the memory `m'` (from `m`): the stage, the core's memos, the growth, the inductive arm's
memos. -/
structure CidPost (dn : NIdx → Option ConLeche.Name) (m : Mem) (w : Word) (x : IFEnv) (m' : Mem)
    (a' : AState) : Prop where
  stage : StageR w x m' a'
  core : CoreMemos m'
  grow : IWGrow m m'
  ind : IndMemos m'

/-- A later start: the post from `m₁` is the post from `m` once `m` grew to `m₁`. -/
theorem CidPost.pre {dn : NIdx → Option ConLeche.Name} {m m₁ m' : Mem} {w : Word} {x : IFEnv}
    {a' : AState} (h : CidPost dn m₁ w x m' a') (hg : IWGrow m m₁) : CidPost dn m w x m' a' :=
  ⟨h.stage, h.core, hg.trans h.grow, h.ind⟩

/-- A block at an `EREC` slice stays there as the pools grow. -/
theorem blockAt_grow {o l : Word} {b : List IConstantInfo} {m m' : Mem} (h : BlockAt o l b m)
    (hg : IWGrow m m') : BlockAt o l b m' := by
  have hb := (decB_decEBlk_of_decCIs (dn := fun _ => none) h.1).grow (decEBlk_mono _ _ _) hg
  exact ⟨hb.get (decEBlk_mono _ _ _), Nat.le_trans h.2 hg.er⟩

/-- **`check_basis_block`'s contract**: on a block `basis_name_hit` matched at a kind below `4`,
from `StageC` and the arm's memos, the call refines `checkBasisBlock`, both outcomes (its
errors, the pin mismatch and a duplicate install, are the twin's own; `G` is the no-verdict
closure fact the model's spec reads its errors under). -/
def CbbRef (p : Prog) (dn : NIdx → Option ConLeche.Name) : Prop :=
  ∀ (n : Nat) (vis k o l : Word) (fe : IFEnv) (env : ConLeche.Env) (m : Mem) (a : AState)
    (block : List IConstantInfo) (blockP : List ConLeche.ConstantInfo), k.toNat < 4 →
    StageC dn vis fe env m a → BlockAt o l block m →
    Frontend.denoteCIList a.store block = some blockP → IndMemos m → AbsOK m →
    RefE (closedNV p L.Checker.nvFns = true) (callE p n "check_basis_block" [vis, k, o, l] m)
      (checkBasisBlock fe (basisOfW k.toNat) block) a
      (fun rm fe' a' => CidPost dn m (rm.1.headD 0) fe' rm.2 a')

/-- **A unified model's refinement as the call's**: the model's spec (`hs`) and its `RefE` give
the `RefE` of `callE` (the class-`0` errors claim nothing). -/
theorem RefE.ofCallE {α β : Type} {p : Prog} {n : Nat} {f : FnName} {args : List Word} {s₀ : St}
    {G Gs : Prop} {fx : Except Err α} {V : List Word → St → α} {Q : List Word → St → Prop}
    {T : AM β} {a : AState} {R : α → β → AState → Prop}
    (hs : ⦃fun s => s = s₀⦄ invoke p (exec p n) f args
      ⦃fun r s' => Q r s' ∧ fx = .ok (V r s'); fun ε => Gs → ε.cls ≠ 0 → fx = .error ε⦄)
    (hGs : G → Gs) (h : RefE G fx T a R) :
    RefE G (callE p n f args s₀.mem) T a
      (fun rm y a' => ∃ s', s'.mem = rm.2 ∧ Q rm.1 s' ∧ R (V rm.1 s') y a') := by
  rcases c : callE p n f args s₀.mem with e | ⟨r, m'⟩
  · exact fun hG => RefE.run_err hs (hGs hG) hG h c
  obtain ⟨s', hm, hQ, y, a', hr, hR⟩ := RefE.run_ok hs h c
  exact ⟨y, a', hr, s', hm, hQ, hR⟩

end L.Ind
