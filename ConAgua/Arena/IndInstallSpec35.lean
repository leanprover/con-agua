import ConAgua.Arena.IndInstallSpec31
import ConAgua.Arena.RecCheckSpec20

/-!
# Refinements of `IndInstall`, part 35 (lane `indproofs4`): `checkBlockTail`

`ictlW_sim` (part 31) took `cons_block_recs_tf` as the hypothesis `ConsRecsTFSim p`; helper
`indproofs3-rec`'s `consBlockRecsTF_refines` (`RecCheckSpec20`) discharges it (`consRecsTFSim_of`;
the `hb` memo after from the write set, `HbMemo.ofClosed`). With it the tail's triple.
-/

set_option linter.deprecated false

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
  intro n dn vis vis2 pp fe m a bs rr outs hS hbs hrr hM r m' hc
  obtain ⟨s', hs', -, hok, hS', hg⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (consBlockRecsTF_refines p L n _ a dn fe vis2 pp 0 (rr.headD 0) (rr.tail.headD 0) vis bs outs
      hS hbs hrr (by simpa using (rr.tail.headD 0).toNat_lt)) hc
  subst hs'
  have hrun := AM.run_of_ok _ a hok
  simp only [UInt64.toNat_zero] at hrun hS'
  exact ⟨_, _, hrun, hS', hg, HbMemo.ofClosed hcl hf hc hM⟩

/-- **`check_block_tail(bO, bL, q)` refines `checkBlockTail`**: from the pass's record (`BPassR`),
the stage relation at its environment, the raw block decoded and the `hb` memo well formed, the
stage relation at the returned view of the twin's environment, the pools grown, the memo kept.
Program facts: the lookups (`TailProg`, `CbrLook`) and the write set of the callees without a memo
lemma (`hcl`, decided for the checker's program). -/
@[refines ConRon.Arena.checkBlockTail]
theorem checkBlockTail_refines {p : Prog} (hP : TailProg p) (L : CbrLook p) {fs : List FnName}
    (hfs : ∀ f ∈ tailCallees, f ∈ fs) (hcl : closedA p hbFreeA hbFreeC fs = true) (n : Nat)
    (hn : 2 ^ 31 + n ≤ coreWalkFuel) (s₀ : St) (a₀ : AState) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {bO bL q : Word} {bp : BlockPass} {block : List IConstantInfo}
    (hS : StageR dn vis fe s₀.mem a₀) (hq : BPassR vis fe s₀.mem q bp)
    (hblk : DecB (fun m => decEBlk dn m bO.toNat bL.toNat) s₀.mem block) (hM : HbMemo s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check_block_tail" [bO, bL, q]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.checkBlockTail V block bp) a₀ ∧
      StageR dn (r.headD 0) (AM.res (ConRon.Arena.checkBlockTail V block bp) a₀) s'.mem
        (AM.st (ConRon.Arena.checkBlockTail V block bp) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ HbMemo s'.mem; ⊤⦄ := by
  refine triple_post (ictl_spec p hP.tail n s₀ bO bL q) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hg, hM'⟩ :=
    ictlW_sim hP (consRecsTFSim_of L hcl (hfs _ (by decide))) hfs hcl n hn hS hq hblk hM r s'.mem hm
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hres, hst]; exact hS', hg, hM'⟩

end L.Ind
