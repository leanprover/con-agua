module

public import ConAgua.Arena.IndInstallSpec.PartsShapeFacts
import ConAgua.Arena.IndPartsSpec.PartsSliceCopy
import ConAgua.Arena.IndPartsSpec.PlW
import ConAgua.Arena.IndPartsSpec.PartsPSlCons
public import ConAgua.Arena.IndPosSpec.Pos2CvLpsWStage
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.Arena.IndInstallSpec.PartsAt
import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved
import ConAgua.Arena.IndPartsSpec.IndPartsProg2
import ConAgua.Arena.IndSumSpec.Row
import all ConAgua.Arena.IndInstall

@[expose] public section

/-!
# NestCtx: `ConRon.Arena.BlockShape.nestCtx`

The refinement theorems `blockShapeNestCtx_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

set_option maxHeartbeats 3200000 in
theorem nck_spec (p : Prog) (hP : NckProg p) (n : Nat) (s₀ : St) (q fo fl : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "block_shape_nest_ctx" [q, fo, fl]
    ⦃fun r s' => LocEq s' s₀ ∧ nckW n s₀.mem q fo fl = some (r, s'.mem); ⊤⦄ := by
  sorry

theorem nIdxsW_room {n : Nat} {m m' : Mem} {p : Word} {r : List Word}
    (h : nIdxsW n m p = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    iwTop m + (rdW (m.arr64 IW) (p + 1)).toNat ≤ (m.arr64 IW).size := by
  unfold nIdxsW at h
  cases hal : allocW m (rdW (m.arr64 IW) (p + 1)) with
  | none => rw [hal] at h; cases h
  | some x =>
    obtain ⟨hq, -, hr⟩ := allocW_facts hal hsz
    simp only [iwTop]; rw [hq] at hr; exact hr

/-- **`block_shape_lps`, below the tops** (no global bound on the record pool needed). -/
theorem lpsW_ok' {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m m' : Mem} {q : Word} {r : List Word} {bs : BlockShape} (h : lpsW n m q = some (r, m'))
    (hS : StageR vis fe m a) (hq : DecB (fun m => decBS m q.toNat) m bs) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some bs.lps ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  sorry

/-- The model of `block_shape_nest_ctx` against `BlockShape.nestCtx` (through `param_levels`' stub
`intern_ls_iw`): the shape record decoded below the tops, its members' slice below the top
(`hsrc`), the parameters' free variables a handle slice below the top; the context record decoded
below the tops. -/
theorem nckW_ok (n : Nat) (s₀ s' : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (q fo fl : Word) (bs : BlockShape)
    (fvsP : List EIdx) (hS : StageR vis fe s₀.mem a₀) (hq : DecB (fun m => decBS m q.toNat) s₀.mem bs)
    (hsrc : ∀ o l, iwN s₀.mem q.toNat = some o → iwN s₀.mem (q.toNat + 1) = some l → o + l ≤ iwTop s₀.mem)
    (hf : decHL s₀.mem fo.toNat fl.toNat = some fvsP) (hfb : fo.toNat + fl.toNat ≤ iwTop s₀.mem)
    (r : List Word) (hm : nckW n s₀.mem q fo fl = some (r, s'.mem)) :
    AM.ok (bs.nestCtx fvsP) a₀ ∧
      DecB (fun m => decCtx m (r.headD 0).toNat) s'.mem (AM.res (bs.nestCtx fvsP) a₀) ∧
      StageR vis fe s'.mem (AM.st (bs.nestCtx fvsP) a₀) ∧ IWGrow s₀.mem s'.mem ∧
      CtxIn s'.mem (r.headD 0).toNat (· < iwTop s'.mem) ∧ CtxSl s'.mem (r.headD 0).toNat := by
  sorry

/-- **`block_shape_nest_ctx` refines `BlockShape.nestCtx`** (through `param_levels`' stub
`intern_ls_iw`): the shape record decoded below the tops, its members' slice below the top
(`hsrc`), the parameters' free variables a handle slice below the top; the context record decoded
below the tops. -/
@[refines ConRon.Arena.BlockShape.nestCtx]
theorem blockShapeNestCtx_refines (p : Prog) (hP : NckProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (q fo fl : Word) (bs : BlockShape)
    (fvsP : List EIdx) (hS : StageR vis fe s₀.mem a₀) (hq : DecB (fun m => decBS m q.toNat) s₀.mem bs)
    (hsrc : ∀ o l, iwN s₀.mem q.toNat = some o → iwN s₀.mem (q.toNat + 1) = some l → o + l ≤ iwTop s₀.mem)
    (hf : decHL s₀.mem fo.toNat fl.toNat = some fvsP) (hfb : fo.toNat + fl.toNat ≤ iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "block_shape_nest_ctx" [q, fo, fl]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (bs.nestCtx fvsP) a₀ ∧
      DecB (fun m => decCtx m (r.headD 0).toNat) s'.mem (AM.res (bs.nestCtx fvsP) a₀) ∧
      StageR vis fe s'.mem (AM.st (bs.nestCtx fvsP) a₀) ∧ IWGrow s₀.mem s'.mem ∧
      CtxIn s'.mem (r.headD 0).toNat (· < iwTop s'.mem) ∧ CtxSl s'.mem (r.headD 0).toNat; ⊤⦄ :=
  triple_post (nck_spec p hP n s₀ q fo fl) fun r s' ⟨hl, hm⟩ =>
    ⟨hl, nckW_ok n s₀ s' a₀ dn vis fe q fo fl bs fvsP hS hq hsrc hf hfb r hm⟩

end L.Ind

end
