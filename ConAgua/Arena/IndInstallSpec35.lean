import ConAgua.Arena.IndInstallSpec31

/-!
# Refinements of `IndInstall`, part 35 (lane `indproofs4`): `checkBlockTail`

`ictlW_sim` (part 31) took `cons_block_recs_tf` as the hypothesis `ConsRecsTFSim p`; helper
`indproofs3-rec`'s `consBlockRecsTF_refines` (`IndSumSpec/ConsBlockRecsTF`) discharges it (`consRecsTFSim_of`;
the `hb` memo after from the write set, `HbMemo.ofClosed`). With it the tail's triple.
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **`cons_block_recs_tf` as the tail needs it**, from its refinement. -/
theorem consRecsTFSim_of {p : Prog} (L : CbrLook p) {fs : List FnName}
    (hcl : closedA p hbFreeA hbFreeC fs = true) (hf : "cons_block_recs_tf" ∈ fs) :
    ConsRecsTFSim p := by
  intro n dn vis vis2 pp fe m a bs rr outs hS hbs hrr hM hA r m' hc
  obtain ⟨s', hs', -, hok, hS', hg, hA'⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (consBlockRecsTF_refines p L n _ a dn fe vis2 pp 0 (rr.headD 0) (rr.tail.headD 0) vis bs outs
      hS hbs hrr (by simpa using (rr.tail.headD 0).toNat_lt) hA) hc
  subst hs'
  have hrun := AM.run_of_ok _ a hok
  simp only [UInt64.toNat_zero] at hrun hS'
  exact ⟨_, _, hrun, hS', hg, HbMemo.ofClosed hcl hf hc hM, hA'⟩

end L.Ind
