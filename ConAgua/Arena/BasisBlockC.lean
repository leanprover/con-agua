module

public import ConAgua.Arena.DeclBasisRef
public import ConAgua.Arena.LoopT
public import ConRon.Arena.DeclCheck
public import ConAgua.Arena.IndArmBridge2
public import ConAgua.Arena.IndPartsSpec.BlockSplitRecs

@[expose] public section

/-!
# The inductive arm's post (`CidPost`) and a unified model's refinement as the call's

What `check_ind_decl` and `check_block` give besides the twin's run (`CidPost`: the stage at the
returned view, the core's and the inductive stage's memos), and `RefE.ofCallE`.
-/

open ConRon.Arena
open Std.WP

namespace L.Ind

open L.Arena

/-- What `check_ind_decl` (and its returning callee) gives besides the twin's run, a view `w`
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
