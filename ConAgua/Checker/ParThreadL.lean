import ConAgua.Checker.ParDriverL
import ConAgua.Arena.PhaseBOne

/-!
# The threads' entry 2, in L: one pending group per call (lane parmode)

docs/design/parmode.md. A thread calls `check` with the mode word `2` and the range `[j, j + 1)` on
its worker memory, again and again. Its invariant `ThreadInv`: the worker memory agrees, on every
word array phase B's loop names, with a memory `m'` that is `PhaseBStart` at the twin's current
worker state (and holds the pin data, for the substituted program), and the seed is copied
(`INIT = 1`). One call that returns keeps it at the state after `checkPending` on group `j`
(`threadGo_agree`, through `L/Agree.lean` and `PhaseBStart.one`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Checker

open L L.Arena L.Rom

section thread
variable (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
  (ds : Array IDeclaration) (fe : IFEnv) (pend : Array PendingCheck) (bs : List UInt8)

/-- **What a thread's worker memory `w` stands for** at the twin's worker state `a` and phase A's
final view `v`: a memory `m'` with `PhaseBStart` at `a`, the pin data, and `w`'s word arrays
equal to `m'`'s wherever phase B's loop reads. -/
def WorkerRel (v : Word) (w : Mem) (a : AState) : Prop :=
  ∃ m', PhaseBStart pins dn ds fe pend m' a v ∧ m'.arr8 PB = bs.toArray ∧
    ∀ b, phaseBS b = true → w.arr64 b = m'.arr64 b

/-- **Phase B's loop over one group on a worker memory**: `check_pending_go(j, j + 1, v)` from a
state whose memory is `WorkerRel` to `a` returns only if `checkPending` on group `j` accepts, and the
memory it leaves is `WorkerRel` to the state after it. -/
theorem threadGo_agree (hP : PhaseBProg (Prog.subPB bs checkerProg)) (hm : mode = .verified)
    (n : Nat) (hn : n ≤ 2 ^ 62) (a : AState) (v j : Word) (hj : j.toNat < pend.size)
    (hj62 : j.toNat < 2 ^ 62) (x y z : Word) :
    ⦃fun s => x = j ∧ y = j + 1 ∧ z = v ∧ WorkerRel pins dn ds fe pend bs v s.mem a⦄
    invoke checkerProg (exec checkerProg n) "check_pending_go" [x, y, z]
    ⦃fun _ s' => AM.ok (checkPending mode fe (pdAt pend j)) a ∧
      WorkerRel pins dn ds fe pend bs v s'.mem (AM.st (checkPending mode fe (pdAt pend j)) a); ⊤⦄ := by
  apply M.triple_of_run
  rintro s rs s' ⟨hx, hy, hz, m', hS, hPB, hw⟩ hrun
  rw [hx, hy, hz] at hrun
  let m₂ : Mem := { m' with glob := s.mem.glob }
  have hf : MemFrame [] [] m' m₂ := ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl, rfl⟩
  have h₂ := PhaseBStart.frame0 hf hS
  let s₂ : St := ⟨m₂, s.loc⟩
  have hAg : Agree phaseBS (fun _ => false) s.mem s₂.mem :=
    ⟨fun b hb => hw b hb, fun _ hb => absurd hb (by simp), rfl⟩
  obtain ⟨s₂', hrun₂, hAg', -⟩ :=
    invoke_agree_ok checkerProg_phaseBReads check_pending_go_mem_phaseBFns hAg rfl hrun
  -- the pin data survives (no byte store anywhere in the checker)
  have hk := M.of_run (P := fun x => x = s₂) rfl hrun₂
    (Triple.keep checkerProg_noSt8 (Q := fun _ _ => True) (s₀ := s₂) (M.triple_of_run fun _ _ _ _ _ => trivial))
  have hPB₂ : s₂'.mem.arr8 PB = bs.toArray := by rw [hk.2.1.arr8]; exact hPB
  rw [← L.Rom.invoke_subPB (bs := bs) checkerProg_noSt8PB n _ _ (s := s₂) hPB] at hrun₂
  obtain ⟨hok, hS'⟩ := M.of_run (P := fun x => x = s₂) rfl hrun₂
    (PhaseBStart.one mode pins dn ds (Prog.subPB bs checkerProg) hm hP n hn s₂ a j v fe pend hj hj62 h₂)
  exact ⟨hok, s₂'.mem, hS', hPB₂, fun b hb => hAg'.1 b hb⟩

end thread

end L.Checker
