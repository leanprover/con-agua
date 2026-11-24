module

public import ConAgua.Checker.C1ThrQ
public import ConAgua.Arena.JobStartX
public import ConAgua.Checker.CmpSeqW
import ConAgua.Arena.IWFrame

@[expose] public section

/-!
# What the solution's jobs keep, call by call (lane compare2, H7)

The threads' solution phase carries, at the jobs' witness memory `X`, the invariant `c1Q X₀ X`:
the flag-`0` write set's frame from the phase's start `X₀` and the record pool grown from it.

* `c1Q_flush`: the flush (and a change of globals) keeps it (`hQf` of `Checker/C1ThrQ.lean`).
* `c1_recStepQ`: `record_job` calls with the growth (`recCall_stepX`) keep it (`RecStepQ`).
-/

namespace L.Checker

open L L.Arena ConRon.Arena ConRon.Bridge

/-- **The solution phase's invariant** from its start `X₀`. -/
def c1Q (X₀ X : Mem) : Prop := MemFrame cqA cqC X₀ X ∧ ArrExt (erecP X₀) (erecP X)

theorem flushCtl_cqC : ∀ x ∈ flushCtl, x ∈ cqC := by
  intro x hx
  simp only [flushCtl, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact cq_ctl_mem (by decide)

theorem c1Q_flush {X₀ X : Mem} (g : GVar → Word) (h : c1Q X₀ X) :
    c1Q X₀ ⟨(flushMem X).bytes, (flushMem X).words, g⟩ := by
  have f0 : MemFrame [] flushCtl X ⟨(flushMem X).bytes, (flushMem X).words, g⟩ := by
    have f := flushMem_frame X
    generalize flushMem X = F at f ⊢
    exact ⟨f.arr, f.ctl, f.size⟩
  refine ⟨h.1.trans (f0.mono (by simp) flushCtl_cqC), fun i v hv => ?_⟩
  rw [erecP_congr' (f0.arr _ (by simp) (by decide)) (f0.arr _ (by simp) (by decide))
    (f0.ctl 129 (by decide)) (f0.ctl 130 (by decide))]
  exact h.2 i v hv

local notation "VM" => ConLeche.CheckMode.verified

/-- **`record_job` calls keep the solution phase's invariant** (the growth by `recCall_stepX`, the
frame by `cq_recordJobE_frame0`: the flag `CTL[224]` is `0` at the start and outside the frame). -/
theorem c1_recStepQ {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration}
    {p : Prog} {J : Option ISolution} {I : IStreamIndex} {a₀ : AState}
    (hcl : closedA p cqA cqC cqF0 = true) (hrj : p.lookup "record_job" = some recordJobL)
    (X₀ : Mem) (h224 : rdW (X₀.arr64 CTL) 224 = 0)
    (hX : ∀ (k : Nat) (r r' : Mem) (a : AState) (hk : k < ds.size), JobRelX pins dn ds J I a₀ X₀ r a →
      RecCall p k r r' → (∃ env, FoldOK env (I.view k) (AM.st enterScratch a)) →
      ∃ a', recordJob VM pins J I k ds[k] a = .ok ((), a') ∧ JobRelX pins dn ds J I a₀ X₀ r' a') :
    RecStepQ (c1Q X₀) pins dn ds I a₀ p J := by
  intro k r r' a hk hJ ⟨hf, hx⟩ hc hF
  obtain ⟨a', h1, h2, h3⟩ := hX k r r' a hk ⟨hJ, hx⟩ hc hF
  obtain ⟨n, rs, -, hcall⟩ := hc
  obtain ⟨s', hs', -, hE⟩ := triple_of_callE (recordJob_specE p hrj n ⟨r, Locals.init []⟩ _) hcall
  rw [hs'] at hE
  have n224 : (224 : Word) ∉ cqC := cq_not_cqC (.inl (cq_not_cdC (by decide)))
  exact ⟨a', h1, h2, hf.trans (cq_recordJobE_frame0 hcl hE (by rw [hf.ctl 224 n224]; exact h224)), h3⟩

end L.Checker
