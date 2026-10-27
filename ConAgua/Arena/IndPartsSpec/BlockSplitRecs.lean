import ConAgua.Arena.IndPartsSpec.BsW
import ConAgua.Census.Attr

/-!
# BlockSplitRecs: `ConRon.Arena.blockSplitCtors`, `ConRon.Arena.blockSplitRecs`, `ConRon.Arena.blockSplit`

The refinement theorems `blockSplitRecs_refines`, `blockSplitCtors_refines`, `blockSplit_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The block below the tops -/

theorem partsErNat_mono (i : Nat) : OMono (fun m => nat? (erA m) i) := ⟨fun _ _ _ he h => he.2.nat? h⟩

theorem decEBlk_mono (dn : NIdx → Option ConLeche.Name) (off l : Nat) :
    OMono (fun m => decEBlk dn m off l) :=
  OMono.mapM (fun j => OMono.bind (partsErNat_mono (off + j))
    (fun q => (⟨fun _ _ _ he h => he.2.decCI h⟩ : OMono (fun m => decCI (erA m) dn q)))) _

/-- **`block_split_recs` refines `blockSplitRecs`**: the block an `EREC` slice of constant records
decoded below the tops; the result `(ok, off, len)` is the twin's `Option`, the slice of fresh
`[cv, mI, rP, rules.off, rules.len]` records decoded below the tops. -/
@[refines ConRon.Arena.blockSplitRecs]
theorem blockSplitRecs_refines (p : Prog) (hP : IndPartsProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (off l : Word)
    (blk : List IConstantInfo) (hS : StageR dn vis fe s₀.mem a₀)
    (hblk : DecB (fun m => decEBlk dn m off.toNat l.toNat) s₀.mem blk) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_split_recs" [off, l]
    ⦃fun r s' => LocEq s' s₀ ∧ StageR dn vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem ∧
      RecsR (ConRon.Arena.blockSplitRecs blk) r s'.mem; ⊤⦄ :=
  triple_post (bsr_spec p hP.alloc hP.copy hP.cons hP.rec5 hP.recs n s₀ off l) fun r _ ⟨hl, hm⟩ =>
    ⟨hl, bsrW_ok n _ _ a₀ off l blk r hm hS hblk⟩

/-- **`block_split_ctors` refines `blockSplitCtors`.** -/
@[refines ConRon.Arena.blockSplitCtors]
theorem blockSplitCtors_refines (p : Prog) (hP : IndPartsProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (off l : Word)
    (blk : List IConstantInfo) (hS : StageR dn vis fe s₀.mem a₀)
    (hblk : DecB (fun m => decEBlk dn m off.toNat l.toNat) s₀.mem blk) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_split_ctors" [off, l]
    ⦃fun r s' => LocEq s' s₀ ∧ StageR dn vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem ∧
      CtorsR (ConRon.Arena.blockSplitCtors blk) r s'.mem; ⊤⦄ :=
  triple_post (bsc_spec p hP.alloc hP.copy hP.cons hP.rec5 hP.rec3 hP.recs hP.ctors n s₀ off l)
    fun r _ ⟨hl, hm⟩ => ⟨hl, bscW_ok n _ _ a₀ off l blk r hm hS hblk⟩

/-- **`block_split` refines `blockSplit`**: the result `(ok, q)`, `q` the 6-word record of the
formers', constructors' and recursors' slices (`SplitRec`). -/
@[refines ConRon.Arena.blockSplit]
theorem blockSplit_refines (p : Prog) (hP : IndPartsProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (off l : Word)
    (blk : List IConstantInfo) (hS : StageR dn vis fe s₀.mem a₀)
    (hblk : DecB (fun m => decEBlk dn m off.toNat l.toNat) s₀.mem blk) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_split" [off, l]
    ⦃fun r s' => LocEq s' s₀ ∧ StageR dn vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem ∧
      SplitR (ConRon.Arena.blockSplit blk) r s'.mem; ⊤⦄ :=
  triple_post (bs_spec p hP.alloc hP.copy hP.cons hP.rec5 hP.rec3 hP.rec6 hP.recs hP.ctors hP.split
    n s₀ off l) fun r _ ⟨hl, hm⟩ => ⟨hl, bsW_ok n _ _ a₀ off l blk r hm hS hblk⟩

end L.Ind

end
