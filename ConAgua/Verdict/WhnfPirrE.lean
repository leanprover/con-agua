import ConAgua.Verdict.WhnfM2CE
/-!
# `proof_irrel`'s verdict claims (lane `verdicts-b`, helper `k2`)

`proof_irrel_half`'s claims are `pih_ref`'s error half (`WhnfIotaRefine4.lean`: the level
comparison out of fuel declines, the rest are the `infer_io` and `whnf` slots'). The twin's
`proofIrrel` is its two halves (`proofIrrel_eq_halves`, `piHalfT_eq`); `proofIrrelE_of`:
`ProofIrrelWE`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

theorem whnfPirrE_nv : ∀ f ∈ ["pin_word", "lvl_eq_c"], f ∈ L.Checker.nvFns :=
  _root_.L.Checker.nv_sub (by decide +kernel)

/-- **`ProofIrrelWE`**: `proof_irrel`'s verdicts are its halves' (`pih_ref`'s error half). -/
theorem proofIrrelE_of (p : Prog) (hp : IotaProg4 p) (hld : LvlDen)
    (hnv : closedNV p L.Checker.nvFns = true) : ProofIrrelWE p := by
  intro n hk hkE F hnF hn62 s₀ a₀ dn vis fe MM eb mode d a b hS hm4 hebm ha hb
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (pirrE_spec p hp.proofIrrel (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d a b) hc0 (Err.code_ne_of_cls hk0)
  simp only [pirrE] at hW
  rw [proofIrrel_eq_halves, piHalfT_eq]
  cases n with
  | zero =>
    obtain ⟨e', he', h0⟩ := callE_zero p "proof_irrel_half" [mode, vis, d, a] s₀.mem
    rw [he', pirrE.k_proof_irrel_half.none] at hW; cases hW; exact absurd h0 hk0
  | succ n' =>
  have hG : ∀ k, k ≤ n' → PihG p k := fun k hkn =>
    ⟨hkE.mono (by omega),
      fun j args m _ h => callE_nv hnv (whnfPirrE_nv "pin_word" (by simp)) j args m h,
      fun j args m _ h => callE_nv hnv (whnfPirrE_nv "lvl_eq_c" (by simp)) j args m h⟩
  have hr := pih_ref p hp hld n' F (hk.mono (Nat.le_succ n')) (by omega) (by omega) dn vis fe eb mode d
  cases c1 : callE p (n' + 1) "proof_irrel_half" [mode, vis, d, a] s₀.mem with
  | error e1 =>
    rw [c1, pirrE.k_proof_irrel_half.none] at hW; cases hW
    exact ErrClaim.bind_left (RefE.run_err (s₀ := ⟨s₀.mem, Locals.init []⟩)
      (pihE_spec p hp.proofIrrelHalf (n' + 1) _ mode vis d a) trivial (hG n' (Nat.le_refl _))
      (hr a hm4 hebm ha s₀.mem a₀ MM hS) c1)
  | ok q =>
  obtain ⟨ra, m1⟩ := q
  rw [c1] at hW
  simp only [pirrE.k_proof_irrel_half] at hW
  obtain ⟨t1, ht1, -, ya, a1, hA1, hRa⟩ := RefE.run_ok (s₀ := ⟨s₀.mem, Locals.init []⟩)
    (pihE_spec p hp.proofIrrelHalf (n' + 1) _ mode vis d a) (hr a hm4 hebm ha s₀.mem a₀ MM hS) c1
  rw [ht1] at hRa
  have hya : ya = decO (ra.headD 0) := hRa.res
  by_cases hwa : ra.headD 0 = 0
  · rw [ite_eq_left hwa] at hW; cases hW
  rw [ite_eq_right hwa] at hW
  have hW' := err_of_k (by intro q e; simp only [pirrE.k_proof_irrel_half_2]; split <;> simp)
    (fun _ => rfl) hW
  obtain ⟨M1, hS1, -, -⟩ := hRa.after
  have hx : ya = some (decide (ra.headD 0 ≠ 1)) := by
    rw [hya]; unfold decO; by_cases h1 : ra.headD 0 = 1
    · rw [ite_eq_right hwa, ite_eq_left h1, h1]; rfl
    · rw [ite_eq_right hwa, ite_eq_right h1, decide_eq_true h1]
  rw [hx] at hA1
  refine ErrClaim.bind_right hA1 ?_
  show ErrClaim (piHalfT _ _ _ _) _ _
  rw [piHalfT_eq]
  exact ErrClaim.bind_left (RefE.run_err (s₀ := ⟨m1, Locals.init []⟩)
    (pihE_spec p hp.proofIrrelHalf (n' + 1) _ mode vis d b) trivial (hG n' (Nat.le_refl _))
    (hr b hm4 hebm hb m1 a1 M1 hS1) hW')

end L.Arena
