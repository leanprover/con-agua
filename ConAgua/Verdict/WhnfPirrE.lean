import ConAgua.Arena.WhnfIotaRefine4
import ConAgua.Arena.DefEqStuck
/-!
# `proof_irrel`'s verdict claims (lane `verdicts-b`, helper `k2`)

`proof_irrel`'s claims are `pirr_ref`'s error half (`WhnfIotaRefine4.lean`: its halves', the
level comparison out of fuel declines, the rest are the `infer_io` and `whnf` slots');
`proofIrrelE_of`: `ProofIrrelWE`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

theorem whnfPirrE_nv : ∀ f ∈ ["pin_word", "lvl_eq_c"], f ∈ L.Checker.nvFns :=
  _root_.L.Checker.nv_sub (by decide +kernel)

/-- **`ProofIrrelWE`**: `proof_irrel`'s verdicts are its halves' (`pirr_ref`'s error half). -/
theorem proofIrrelE_of (p : Prog) (hp : IotaProg4 p) (hld : LvlDen)
    (hnv : closedNV p L.Checker.nvFns = true) : ProofIrrelWE p :=
  fun n hk hkE F hnF hn62 s₀ a₀ dn vis fe MM eb mode d a b hS hm4 hebm ha hb =>
    RefE.coreSpecE (pirrE_spec p hp.proofIrrel hp.proofIrrelHalf (n + 1) s₀ mode vis d a b) trivial
      ⟨hkE, fun j args m _ h => callE_nv hnv (whnfPirrE_nv "pin_word" (by simp)) j args m h,
        fun j args m _ h => callE_nv hnv (whnfPirrE_nv "lvl_eq_c" (by simp)) j args m h⟩
      (pirr_ref p hp hld n F hk hnF hn62 dn vis fe eb mode d a b hm4 hebm ha hb s₀.mem a₀ MM hS)

end L.Arena
