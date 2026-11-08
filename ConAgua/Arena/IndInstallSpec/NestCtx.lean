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
theorem lpsW_ok' {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m m' : Mem} {q : Word} {r : List Word} {bs : BlockShape} (h : lpsW n m q = some (r, m'))
    (hS : StageR vis fe m a) (hq : DecB (fun m => decBS m q.toNat) m bs) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some bs.lps ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  have hqt : decBS (truncM m) q.toNat = some bs := hq
  obtain ⟨hmem, -, -, -, -, -, hpr⟩ := decBS_some hqt
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hq8 : q.toNat + 8 < iwTop m := by
    simp only [iwB, bool?, Option.map_eq_some_iff] at hpr
    obtain ⟨w, hw, -⟩ := hpr
    exact (truncM_iw_get hw).1
  obtain ⟨o, l, ho, hl, hdm, hb⟩ := partsAt decMS_mono hmem
  obtain ⟨how, -, -⟩ := partsIwRd ho rfl
  obtain ⟨hlw, -, -⟩ := partsIwRd hl (show (q + 1).toNat = q.toNat + 1 by rw [UInt64.toNat_add]; simp; omega)
  rw [ofNat_toNat_word] at how hlw
  rcases n with _ | n
  · simp [lpsW] at h
  by_cases hl0 : l = 0
  · rw [lpsW_nil n m q (by rw [hlw, hl0])] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : bs.members = [] := by have := decPL_length _ (show decPL _ _ _ _ = _ from hdm); rw [hl0] at this; simpa using this
    refine ⟨hS, IWGrow.refl _, ?_, by simp⟩
    simp [BlockShape.lps, this, decHL, hslice?]
  rw [lpsW_cons n m q (by rw [hlw]; exact hl0)] at h
  have hPS : PSlR decMS bs.members o l m := ⟨hdm, hb.resolve_left hl0⟩
  obtain ⟨pc, ms0, ms', hms, hw0, hpb, hm0, -⟩ := partsPSl_cons hPS hl0
  obtain ⟨⟨cvp, hcvp, hcv⟩, -, -⟩ := decMS_some (show decMS (truncM m) pc = some ms0 from hm0)
  obtain ⟨hcw, hcvb, -⟩ := partsIwRd hcvp (UInt64.toNat_ofNat_of_lt' hpb)
  rw [how, hw0, hcw] at h
  obtain ⟨hS', hg, hd, ht⟩ := partsLpsCopy h hS (show DecB (fun m => decCVp m cvp) m ms0.cvT from hcv) hcvb
  refine ⟨hS', hg, ?_, Nat.le_of_eq ht⟩
  rw [hd]; simp [BlockShape.lps, hms]

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
