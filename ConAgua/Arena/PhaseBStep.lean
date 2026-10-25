import ConAgua.Arena.FreezeRel

/-!
# One pending group from `PhaseBStart` (lane parmode, from lane parallel's `PhaseBEntry`)

The threads' entry 2 checks pending groups one at a time, in any order, each on the state the
previous one left. con-ron's phase-B invariant `TwinPend` is stated over the remaining groups in
order; over all of them it holds again after any one (`TwinPend.dup`: a group of the list may be
checked first), because each check ends in `dropScratch` and grows the persistent tier only
(`TwinPend.step`).

`PhaseBStart.step`: `check_pending(j, v)` from `PhaseBStart … m a v` refines `checkPending` on
group `j` and ends in `PhaseBStart` again, at the twin's state after it.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open ConRon.Bridge (PendRel ListRel)

theorem listRel_mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, ListRel R xs ys → ∀ x ∈ xs, ∃ y, R x y
  | _, _, .nil, _, hx => absurd hx (by simp)
  | _, _, .cons hab hr, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨_, hab⟩
    · exact listRel_mem_left hr x hx

/-- **A pending group of the list may be checked first**: `TwinPend` over `pend` gives it over
`pc :: pend` for every `pc ∈ pend`. -/
theorem TwinPend.dup {fe : IFEnv} {pend : List PendingCheck} {a : AState} {pc : PendingCheck}
    (h : TwinPend fe pend a) (hpc : pc ∈ pend) : TwinPend fe (pc :: pend) a := by
  obtain ⟨env, pendP, hok, hnd, hrel⟩ := h.fold
  obtain ⟨y, hy⟩ := listRel_mem_left hrel pc hpc
  exact ⟨⟨env, y :: pendP, hok, hnd, .cons hy hrel⟩,
    fun _ => h.caches (List.ne_nil_of_mem hpc), h.off, fun _ => h.dropped (List.ne_nil_of_mem hpc)⟩

theorem pdAt_mem (pend : Array PendingCheck) (j : Word) (hj : j.toNat < pend.size) :
    pdAt pend j ∈ pend.toList := by
  simp only [pdAt, Array.getD, hj, dite_true]
  exact Array.getElem_mem_toList hj

section step
variable (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
  (ds : Array IDeclaration) (p : Prog)

/-- **One pending group from `PhaseBStart`**: `check_pending(j, v)` (any `j` below the count)
refines `checkPending` on group `j` and ends in `PhaseBStart` at the twin's state after it. -/
theorem PhaseBStart.step (hm : mode = .verified) (hP : PhaseBProg p) (n : Nat) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (j v : Word) (fe : IFEnv) (pend : Array PendingCheck)
    (hj : j.toNat < pend.size) (h : PhaseBStart pins dn ds fe pend s₀.mem a₀ v) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_pending" [j, v]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (checkPending mode fe (pdAt pend j)) a₀ ∧
      PhaseBStart pins dn ds fe pend s'.mem (AM.st (checkPending mode fe (pdAt pend j)) a₀) v; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  have hT := h.twin.dup (pdAt_mem pend j hj)
  obtain ⟨h0, ho, hL, hcm, hCr'⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (checkPending_refinesT mode pins dn ds p hm hP n hn s₀ a₀ j v fe pend hj _ hT h.loop h.mem
      h.core h.cr)
  obtain ⟨hf, -⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (invoke_memFrame hP.loop n checkPending_loop [j, v] s₀)
  subst hs hm
  have hrun' := AM.run_of_ok _ _ ho
  obtain ⟨hT', hx⟩ := TwinPend.step hT hrun'
  exact ⟨h0, ho, ⟨hL, h.mem.step hf hx, hcm, hT', hCr'⟩⟩

end step

end L.Arena
