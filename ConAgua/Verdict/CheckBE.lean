import ConAgua.Verdict.PhaseBE
import ConAgua.Checker.ParDriverL

/-!
# Entry 2's `check_b` fails only where phase B on the worker does (lane verdicts-b, calibration)

The error halves of `ParDriverL.lean`'s `checkPendingGo_agree` and `checkB_agree0`: phase B's
loop on a memory that agrees with phase A's on what the loop names (`invoke_agree`, the same
error), the ROM substitution (`invoke_subPB`), the loop's error claim
(`checkPendingGo_refinesE`) and the worker (`checkPendingList_worker_fails`).
-/

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Checker

open L L.Arena

section agree
variable (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
  (ds : Array IDeclaration) (fe : IFEnv) (pend : Array PendingCheck)

/-- **Phase B's loop, error half of `checkPendingGo_agree`**: a failing `check_pending_go(0, k, v)`
from a memory that agrees with phase A's on what the loop names claims phase B's failure on the
worker. -/
theorem checkPendingGo_agreeE (bs : List UInt8) (hP : PhaseBProg (Prog.subPB bs checkerProg))
    (hm : mode = .verified) (hE : CPErrT mode pins dn ds (Prog.subPB bs checkerProg) fe pend)
    (n : Nat) (hn : n ≤ 2 ^ 62) (m : Mem) (a : AState) (v k : Word) (hk : k.toNat = pend.size)
    (hPB : m.arr8 L.Rom.PB = bs.toArray)
    (h : PhaseBStart pins dn ds fe pend m a v) (x y z : Word) :
    ⦃fun s => x = 0 ∧ y = k ∧ z = v ∧ ∀ b, phaseBS b = true → s.mem.arr64 b = m.arr64 b⦄
    invoke checkerProg (exec checkerProg n) "check_pending_go" [x, y, z]
    ⦃fun _ _ => True; ErrClaimV (checkPendingList mode fe pend.toList) a.worker⦄ := by
  apply M.triple_of_run' (fun _ _ _ _ _ => trivial)
  rintro s e ⟨hx, hy, hz, hw⟩ hrun
  rw [hx, hy, hz] at hrun
  let m₂ : Mem := { m with glob := s.mem.glob }
  have hf : MemFrame [] [] m m₂ := ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl, rfl⟩
  have h₂ := PhaseBStart.frame0 hf h
  -- the run from the call's own locals
  have hrun₀ : (invoke checkerProg (exec checkerProg n) "check_pending_go" [0, k, v]).run
      ⟨s.mem, Locals.init []⟩ = .error e := by
    rw [invoke_run_loc'] at hrun
    cases hq : (invoke checkerProg (exec checkerProg n) "check_pending_go" [0, k, v]).run
      ⟨s.mem, Locals.init []⟩ with
    | error e' => rw [hq] at hrun; simp [Except.map] at hrun; rw [hrun]
    | ok q => rw [hq] at hrun; simp [Except.map] at hrun
  have hAg : Agree phaseBS (fun _ => false) s.mem m₂ :=
    ⟨fun b hb => hw b hb, fun _ hb => absurd hb (by simp), rfl⟩
  have hres := invoke_agree checkerProg_phaseBReads check_pending_go_mem_phaseBFns n [0, k, v]
    (s₁ := ⟨s.mem, Locals.init []⟩) (s₂ := ⟨m₂, Locals.init []⟩) hAg rfl
  rw [hrun₀] at hres
  have hrun₂ : (invoke checkerProg (exec checkerProg n) "check_pending_go" [0, k, v]).run
      ⟨m₂, Locals.init []⟩ = .error e := by
    revert hres
    cases (invoke checkerProg (exec checkerProg n) "check_pending_go" [0, k, v]).run
      ⟨m₂, Locals.init []⟩ with
    | ok q => intro h'; exact h'.elim
    | error e' => intro h'; cases h'; rfl
  rw [← L.Rom.invoke_subPB (bs := bs) checkerProg_noSt8PB n _ _ (s := ⟨m₂, Locals.init []⟩) hPB]
    at hrun₂
  have hc : callE (Prog.subPB bs checkerProg) n "check_pending_go" [0, k, v] m₂ = .error e := by
    simp only [callE, hrun₂]
  intro hk0
  have := (checkPendingGo_refinesE mode pins dn ds (Prog.subPB bs checkerProg) fe pend hP hm hE n hn).1
    m₂ a 0 k v (by simp) hk (by simpa using h₂.twin) h₂.loop h₂.mem h₂.core h₂.cr e hc hk0
  simp only [UInt64.toNat_zero, List.drop_zero] at this
  exact checkPendingList_worker_fails h₂.twin.caches this

/-- **Entry 2 in place, `check_b`, error half of `checkB_agree0`**: from a memory that agrees with
phase A's on what phase B's loop names, with the range `[0, k)`, an empty seed `CTLF` and the view
`v` in the header's word 3, a failing run of class `≠ 0` claims phase B's failure on `a.worker`. -/
theorem checkB_agree0E (bs : List UInt8) (hP : PhaseBProg (Prog.subPB bs checkerProg))
    (hm : mode = .verified) (hE : CPErrT mode pins dn ds (Prog.subPB bs checkerProg) fe pend)
    (n : Nat) (hn : n ≤ 2 ^ 62) (m : Mem) (a : AState) (v k : Word) (hk : k.toNat = pend.size)
    (hPB : m.arr8 L.Rom.PB = bs.toArray) (h : PhaseBStart pins dn ds fe pend m a v) (s₀ : St)
    (hw : ∀ b, phaseBS b = true → s₀.mem.arr64 b = m.arr64 b)
    (hlo : s₀.mem.glob PLO = 0) (hhi : s₀.mem.glob PHI = k) (hctlf : (s₀.mem.arr64 CTLF).size = 0)
    (hv : rd64 s₀.mem HDRF 3 = v) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "check_b" []
    ⦃fun _ _ => True; ErrClaimV (checkPendingList mode fe pend.toList) a.worker⦄ := by
  have hl : (UInt64.toNat (s₀.mem.len64 242)) = 0 := by simp [Mem.len64, show (242 : ArrId) = CTLF from rfl, hctlf]
  have hlo' : s₀.mem.glob ⟨9⟩ = 0 := hlo
  have hhi' : s₀.mem.glob ⟨11⟩ = k := hhi
  have hv' : ∀ (hb : (3 : Word).toNat < (s₀.mem.arr64 241).size), (s₀.mem.arr64 241)[(3 : Word).toNat] = v := by
    intro hb; rw [← hv]; unfold rd64; rw [Array.getD, dite_eq_left hb]; rfl
  rw [invoke_eq _ checkerProg_lookup_check_b]
  simp only [callFn, checkBL]
  cases n with
  | zero => vcgen [exec] <;> simp [ErrClaimV.of_cls0]
  | succ n =>
    have hcg' := checkPendingGo_agreeE mode pins dn ds fe pend bs hP hm hE n (by omega) m a v k hk hPB h
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, setG, ld64, warr, (hcg' · · ·)]
    all_goals (try simp only [St.setLoc_mem, St.setLoc_loc, St.setLocs_cons,
      Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval,
      reduceIte, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at *)
    all_goals (try simp only [hl, Mem.copy64_zero] at *)
    all_goals (try simp only [St.setG, Mem.setG, St.setLoc] at *)
    all_goals first
      | exact ErrClaimV.of_cls0 (by decide)
      | (simp_all (config := { decide := true }) [Mem.arr64]; done)
      | exact hv' ‹_›
      | (simp only [Mem.arr64] at *; grind)

/-- `checkB_agree0E` with the memory facts as the precondition. -/
theorem checkB_agreeE (bs : List UInt8) (hP : PhaseBProg (Prog.subPB bs checkerProg))
    (hm : mode = .verified) (hE : CPErrT mode pins dn ds (Prog.subPB bs checkerProg) fe pend)
    (n : Nat) (hn : n ≤ 2 ^ 62) (m : Mem) (a : AState) (v k : Word) (hk : k.toNat = pend.size)
    (hPB : m.arr8 L.Rom.PB = bs.toArray) (h : PhaseBStart pins dn ds fe pend m a v) :
    ⦃fun s => (∀ b, phaseBS b = true → s.mem.arr64 b = m.arr64 b) ∧ s.mem.glob PLO = 0 ∧
      s.mem.glob PHI = k ∧ (s.mem.arr64 CTLF).size = 0 ∧ rd64 s.mem HDRF 3 = v⦄
    invoke checkerProg (exec checkerProg n) "check_b" []
    ⦃fun _ _ => True; ErrClaimV (checkPendingList mode fe pend.toList) a.worker⦄ := by
  apply M.triple_of_run' (fun _ _ _ _ _ => trivial)
  intro s₀ e ⟨hw, hlo, hhi, hctlf, hv⟩ hrun
  exact M.of_run_err (P := fun x => x = s₀) rfl hrun
    (checkB_agree0E mode pins dn ds fe pend bs hP hm hE n hn m a v k hk hPB h s₀ hw hlo hhi hctlf hv)

/-- **Entry 2 in place, `check` with the mode word `2`, error half of `checkMode2_agree`.** -/
theorem checkMode2_agreeE (bs : List UInt8) (hP : PhaseBProg (Prog.subPB bs checkerProg))
    (hm : mode = .verified) (hE : CPErrT mode pins dn ds (Prog.subPB bs checkerProg) fe pend)
    (n : Nat) (hn : n ≤ 2 ^ 62) (m : Mem) (a : AState) (v k : Word) (hk : k.toNat = pend.size)
    (hPB : m.arr8 L.Rom.PB = bs.toArray) (h : PhaseBStart pins dn ds fe pend m a v) (s₀ : St)
    (hw : ∀ b, phaseBS b = true → s₀.mem.arr64 b = m.arr64 b) (hmode : s₀.mem.glob MODE = 2)
    (hlo : s₀.mem.glob PLO = 0) (hhi : s₀.mem.glob PHI = k) (hctlf : (s₀.mem.arr64 CTLF).size = 0)
    (hv : rd64 s₀.mem HDRF 3 = v) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "check" []
    ⦃fun _ _ => True; ErrClaimV (checkPendingList mode fe pend.toList) a.worker⦄ := by
  rw [invoke_eq _ checkerProg_lookup_check']
  simp only [callFn, checkL]
  cases n with
  | zero => vcgen [exec] <;> simp [ErrClaimV.of_cls0]
  | succ n =>
    have hB := checkB_agreeE mode pins dn ds fe pend bs hP hm hE n (by omega) m a v k hk hPB h
    have hmode' : s₀.mem.glob ⟨8⟩ = 2 := hmode
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, hB,
      (callE_spec checkerProg n "check_a" [1] ·), (callE_spec checkerProg n "check_a" [0] ·)]
    all_goals (try simp only [St.setLoc_mem, St.setLoc_loc, St.setLocs_cons, Locals.init_nil,
      Cmp.eval, reduceIte, beq_iff_eq, Sig.retVal, Sig.retOr, St.setLocs_nil, List.headD_cons] at *)
    all_goals first
      | exact ErrClaimV.of_cls0 (by decide)
      | (simp_all (config := { decide := true }); done)
      | (simp_all [St.setLoc]; done)

/-- **Entry 2 in place, as a run, error half of `runMode2_agree`**: `L.run checkerProg n "check" [] w`
failing with class `≠ 0`, from a memory `w` as `checkMode2_agree` asks, claims phase B's failure on
the worker. -/
theorem runMode2_agreeE (bs : List UInt8) (hP : PhaseBProg (Prog.subPB bs checkerProg))
    (hm : mode = .verified) (hE : CPErrT mode pins dn ds (Prog.subPB bs checkerProg) fe pend)
    (n : Nat) (hn : n ≤ 2 ^ 62) (m : Mem) (a : AState) (v k : Word) (hk : k.toNat = pend.size)
    (hPB : m.arr8 L.Rom.PB = bs.toArray) (h : PhaseBStart pins dn ds fe pend m a v) (w : Mem)
    (hw : ∀ b, phaseBS b = true → w.arr64 b = m.arr64 b) (hmode : w.glob MODE = 2)
    (hlo : w.glob PLO = 0) (hhi : w.glob PHI = k) (hctlf : (w.arr64 CTLF).size = 0)
    (hv : rd64 w HDRF 3 = v) {e : Err} (hrun : L.run checkerProg n "check" [] w = .error e) :
    ErrClaimV (checkPendingList mode fe pend.toList) a.worker e := by
  simp only [L.run] at hrun
  cases hq : (invoke checkerProg (exec checkerProg n) "check" []).run ⟨w, Locals.init []⟩ with
  | ok x => rw [hq] at hrun; cases hrun
  | error e' =>
    rw [hq] at hrun
    simp only [Except.map, Except.error.injEq] at hrun
    subst hrun
    exact M.of_run_err (P := fun x => x = ⟨w, Locals.init []⟩) rfl hq
      (checkMode2_agreeE mode pins dn ds fe pend bs hP hm hE n hn m a v k hk hPB h ⟨w, Locals.init []⟩
        hw hmode hlo hhi hctlf hv)

end agree
end L.Checker
