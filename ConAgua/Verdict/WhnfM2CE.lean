import ConAgua.Verdict.WhnfModels6E
import ConAgua.Verdict.WhnfPrepE
/-!
# `major_to_ctor`'s verdict claims

No verdict site of its own: the claims are the `infer_io`, `whnf` and `defeq` slots'
(`KnotUpToE`) and `proof_irrel`'s (`ProofIrrelWE`), through its pieces' unified refinements
(`m2cHead_ref` and below, `Arena/WhnfM2CRefine*.lean`): `majorToCtorE_of` (`MajorToCtorE`) is
`m2cHead_ref`'s error half.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

section top
variable (p : Prog) (hp : M2CProg' p) (hc : IotaCallees p) (hpi : ProofIrrelOKM p)
  (hE : ErecKeptKnot p) (hcc : ProjCallees p) (hnv : closedNV p L.Checker.nvFns = true)
  (hPI : ProofIrrelWE p)
include hp hc hpi hE hcc hnv hPI

/-- **`MajorToCtorE`**: `major_to_ctor`'s verdicts are `m2c_head`'s (`m2cHead_ref`'s error
half). -/
theorem majorToCtorE_of : MajorToCtorE p := by
  intro n hk hkE F hnF s₀ a₀ dn vis fe MM eb mode d rec ro rc major rules hn62 hS hm4 hebm hmaj hr
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (mtcE_spec p hp.majorToCtor (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d rec ro rc major) hc0 (Err.code_ne_of_cls hk0)
  simp only [mtcE] at hW
  have hW' := err_of_k (by intro q e; simp [mtcE.k_m2c_head]) (fun _ => rfl) hW
  cases n with
  | zero => exact ErrClaim.of_callE_zeroW hW'
  | succ N =>
  rw [majorToCtor_eq]
  exact RefE.run_err (m2cHeadE_spec p hp.toM2CProg (N + 1) ⟨s₀.mem, Locals.init []⟩ mode vis d ro rc
    major) hnv ⟨hkE.mono (Nat.le_succ _), hPI⟩ (m2cHead_ref p hp hc hpi hE hcc N F
      (hk.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb mode d ro rc major hm4 hebm hmaj
      rules s₀.mem a₀ MM hS hr) hW'

end top

end L.Arena
