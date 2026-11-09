module

import ConAgua.Arena.IndT.Pass
import ConAgua.Arena.IndInstallSpec.BlockRawRec
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndInstallSpec.IcaW
import ConAgua.Arena.IndInstallSpec.IcvgW
import ConAgua.Arena.IndInstallSpec.PosFreeMfr
import ConAgua.Arena.IndPartsSpec.AllCtors
import ConAgua.Arena.IndPartsSpec.BlockSplitRecs
import ConAgua.Arena.IndPosSpec.FgW
import ConAgua.Arena.IndT.Tail
import ConAgua.Arena.RecGenSpec.FlushStage
import ConAgua.Arena.RefWalk
import ConAgua.Arena.ScratchRefine
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.IndInstallSpec.BpRecBpassR
public import ConAgua.Arena.IndInstallSpec.CbProg
public import ConAgua.Arena.IndInstallSpec.ConsRecsTFSimOf
public import ConAgua.Arena.IndInstallSpec.OfClosed
public import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved
public import ConAgua.Arena.IndInstallSpec.BlockCapsAt
public import ConAgua.Arena.IndMaster
public import ConAgua.Arena.IndT.ArmMemos
public import ConAgua.Arena.IndT.GenRec2
public import ConAgua.Arena.IndT.Sum2
public import ConAgua.Arena.BasisBlockC
public import ConAgua.Arena.IndT.BlockC
public import ConAgua.Arena.IndArmLps
public import ConRon.Bridge.Checker.Inv
import all ConAgua.Arena.IndInstall

@[expose] public section

/-!
# `checkBlock`'s ok half (lane `ronsync2`, stage 3)

`check_block`'s refinement is `IndT/BlockC`'s `cb_ref` (both outcomes, from its callees'
contracts `CbRefs`); `checkBlock_refinesC` is its ok half on a call's run.
-/


noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **`check_block(vis, block.off, block.len, p0)` refines `checkBlock`** (the ok half of
`cb_ref`): from `StageC` at the recogniser's state, the fold's invariant, the shape and the block
decoded and denoted, the arm's memos; the twin's run and `CidPost` after it. -/
@[refines ConRon.Arena.checkBlock]
theorem checkBlock_refinesC {G : Prop} {p : Prog} {dn : NIdx → Option ConLeche.Name}
    (R : CbRefs G p dn) {n : Nat} {vis bO bL p0 : Word} {fe : IFEnv} {env : ConLeche.Env}
    {m m' : Mem} {a a₀ : AState} {r : List Word} {bs : BlockShape} {bsP : ConLeche.BlockShape}
    {block : List IConstantInfo} {blockP : List ConLeche.ConstantInfo}
    (h : callW p n "check_block" [vis, bO, bL, p0] m = some (r, m'))
    (hC : StageC dn vis fe env m a) (hfold : ConRon.Bridge.FoldOK env fe a₀)
    (hx : ConRon.Arena.Ext a₀.store a.store)
    (hq : DecB (fun m => decBS m p0.toNat) m bs) (hsl : ShapeSl m p0)
    (hblk : DecB (fun m => decEBlk dn m bO.toNat bL.toNat) m block) (hbb : bO.toNat + bL.toNat ≤ erTop m)
    (hbP : Frontend.denoteCIList a.store block = some blockP)
    (hdP : ConRon.Bridge.Inductives.dShape a.store bs = some bsP)
    (hd : ∀ ms ∈ bsP.members, ms.declared = ms.cvT) (hlpd : BlockLpsDn dn block)
    (hnPb : bs.nP + 1 < 2 ^ 64) (hIM : IndMemos m) (hA : AbsOK m) :
    ∃ fe' a', (ConRon.Arena.checkBlock V fe block bs).run a = .ok (fe', a') ∧
      CidPost dn m (r.headD 0) fe' m' a' := by
  obtain ⟨s', rfl, -, x, a', hrun, hR⟩ := RefE.run_okW (s₀ := ⟨m, Locals.init []⟩)
    (icbE_spec p R.look n _ vis bO bL p0)
    (cb_ref R hC hfold hx hq hsl hblk hbb hbP hdP hd hlpd hnPb hIM hA (N := n)) h
  exact ⟨x, a', hrun, hR⟩

end L.Ind
