import ConAgua.Verdict.DefEqSlotE

/-!
# `defeq_tail`'s error claim

`dt_ref`'s error half (`DefEqStuckTail.lean`), in the shape the `defeq` slot's error half reads
(`DefeqTailE`), from `lazy_delta_step`'s claim (`LazyDeltaStepE`, the projection loop's step) and
the whnf family's `reduce_proj_core`, `proof_irrel` and `defeq_lst` claims.
-/

open ConRon.Arena

namespace L.Arena

/-- **`lazy_delta_step`'s error spec** (the error half of `LazyDeltaStepH`). -/
def LazyDeltaStepE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d a b : Word), SlotPre s₀ a₀ dn vis fe M eb mode → HW a → HW b →
    d.toNat < 2 ^ 63 →
    CoreSpecE p (n + 1) "lazy_delta_step" [mode, vis, d, a, b]
      (lazyDeltaStep (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) s₀ a₀

/-- **`defeq_tail`'s error claim** (`DefeqTailE`, `dt_ref`'s error half). -/
theorem defeqTail_refinesE (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (hlsE : LazyDeltaStepE p) (hrpE : ReduceProjCoreE p) (hpi : ProofIrrelWE p)
    (hlst : DefeqLstWE p) (hnv : closedNV p L.Checker.nvFns = true) : DefeqTailE p :=
  fun n hk hkE F s₀ a₀ dn vis fe M eb mode d a1 b1 hF hn hs ha hb hd =>
    RefE.coreSpecE (dtE_spec p hq.defeqTail hq.projPair hq.ldpr hq.defeqStuck hq.stuckStr hq.stuckApp
      hq.stuckAppCong hq.stuckRest hq.stuckIrrel hq.setCert hq.setWith hq.setWtb hq.setGo hq.setTail
      hq.sunit hq.suHead hq.suTail hq.etaCert hq.etaCertBody hq.etaCertTy (n + 1) s₀ mode vis d a1 b1)
      hnv
      ⟨⟨fun j hj F hF hn s₀ a₀ dn vis fe M eb mode d a b hs ha hb hd =>
          hlsE j (hk.mono hj) (hkE.mono hj) F hF hn s₀ a₀ dn vis fe M eb mode d a b hs ha hb hd,
        hkE, hrpE⟩, hpi, hlst⟩
      (dt_ref p hq hi hc n hk F s₀ a₀ dn vis fe M eb mode d a1 b1 hF hn hs ha hb hd)

end L.Arena
