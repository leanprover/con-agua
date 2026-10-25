import ConAgua.Checker.ParThreadL
import ConAgua.Checker.ParThreadReads
import ConAgua.Arena.FreezeBuf

/-!
# The threads' entry 2, one call (lane parmode)

docs/design/parmode.md, "Step 4". A thread calls `check` with the mode word `2` and the range
`[j, j + 1)` on the memory `bufMem B r j` (`Arena/FreezeRel.lean`): the frozen arrays are the
buffer's images, the owned arrays the region's `r`, every other word array empty.

* `ThreadRel`: `WorkerRel` (`ParThreadL.lean`) over `thrS` (the frozen arrays but `HDRF`/`CTLF`,
  and the owned arrays) instead of `phaseBS`: the worker memory has no other array, and phase B's
  loop names no other (`checkerProg_thrReads`).
* `threadGo_thr`: `threadGo_agree` over `thrS`, keeping `INIT`.
* `seedMem w`: the memory after `check_b`'s first block (on the first call, `INIT = 0`: the seed
  `CTLF` copied into `CTL`, `INIT := 1`; later calls: `w`).
* `checkB_thr`, `checkThr`, `runThr`: a call that returns from a memory whose `seedMem` is
  `ThreadRel` to `a` with `INIT = 1` accepts group `j` at `a` and leaves a memory `ThreadRel` to
  the state after it, with `INIT = 1`.
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
equal to `m'`'s on `thrS` (the frozen arrays but the header and the seed, and the owned ones). -/
def ThreadRel (v : Word) (w : Mem) (a : AState) : Prop :=
  ∃ m', PhaseBStart pins dn ds fe pend m' a v ∧ m'.arr8 PB = bs.toArray ∧
    ∀ b, thrS b = true → w.arr64 b = m'.arr64 b

/-- `thrS` lies inside `phaseBS`. -/
theorem phaseBS_of_thrS {a : ArrId} (h : thrS a = true) : phaseBS a = true := by
  obtain ⟨h1, h2, h3⟩ := (thrS_iff a).mp h
  have : a ≠ OUT := by
    rintro rfl; exact absurd h3 (by decide)
  simp only [phaseBS, bne_iff_ne, ne_eq, Bool.and_eq_true]
  exact ⟨⟨this, h1⟩, h2⟩

/-- `WorkerRel` gives `ThreadRel` (`thrS` lies in `phaseBS`). -/
theorem ThreadRel.of_worker {v : Word} {w : Mem} {a : AState}
    (h : WorkerRel pins dn ds fe pend bs v w a) : ThreadRel pins dn ds fe pend bs v w a := by
  obtain ⟨m', hS, hPB, hw⟩ := h
  exact ⟨m', hS, hPB, fun b hb => hw b (phaseBS_of_thrS hb)⟩

/-- **Phase B's loop over one group on a thread's memory** (`threadGo_agree` over `thrS`), keeping
`INIT`. -/
theorem threadGo_thr (hP : PhaseBProg (Prog.subPB bs checkerProg)) (hm : mode = .verified)
    (n : Nat) (hn : n ≤ 2 ^ 62) (a : AState) (v j : Word) (hj : j.toNat < pend.size)
    (hj62 : j.toNat < 2 ^ 62) (x y z : Word) :
    ⦃fun s => x = j ∧ y = j + 1 ∧ z = v ∧ ThreadRel pins dn ds fe pend bs v s.mem a ∧
      s.mem.glob INIT = 1⦄
    invoke checkerProg (exec checkerProg n) "check_pending_go" [x, y, z]
    ⦃fun _ s' => AM.ok (checkPending mode fe (pdAt pend j)) a ∧
      ThreadRel pins dn ds fe pend bs v s'.mem (AM.st (checkPending mode fe (pdAt pend j)) a) ∧
      s'.mem.glob INIT = 1; ⊤⦄ := by
  apply M.triple_of_run
  rintro s rs s' ⟨hx, hy, hz, ⟨m', hS, hPB, hw⟩, hI⟩ hrun
  rw [hx, hy, hz] at hrun
  have hI' : s'.mem.glob INIT = 1 := (check_pending_go_keepsG hrun).1.trans hI
  let m₂ : Mem := { m' with glob := s.mem.glob }
  have hf : MemFrame [] [] m' m₂ := ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl, rfl⟩
  have h₂ := PhaseBStart.frame0 hf hS
  let s₂ : St := ⟨m₂, s.loc⟩
  have hAg : Agree thrS (fun _ => false) s.mem s₂.mem :=
    ⟨fun b hb => hw b hb, fun _ hb => absurd hb (by simp), rfl⟩
  obtain ⟨s₂', hrun₂, hAg', -⟩ :=
    invoke_agree_ok checkerProg_thrReads check_pending_go_mem_phaseBFns hAg rfl hrun
  have hk := M.of_run (P := fun x => x = s₂) rfl hrun₂
    (Triple.keep checkerProg_noSt8 (Q := fun _ _ => True) (s₀ := s₂) (M.triple_of_run fun _ _ _ _ _ => trivial))
  have hPB₂ : s₂'.mem.arr8 PB = bs.toArray := by rw [hk.2.1.arr8]; exact hPB
  rw [← L.Rom.invoke_subPB (bs := bs) checkerProg_noSt8PB n _ _ (s := s₂) hPB] at hrun₂
  obtain ⟨hok, hS'⟩ := M.of_run (P := fun x => x = s₂) rfl hrun₂
    (PhaseBStart.one mode pins dn ds (Prog.subPB bs checkerProg) hm hP n hn s₂ a j v fe pend hj hj62 h₂)
  exact ⟨hok, ⟨s₂'.mem, hS', hPB₂, fun b hb => hAg'.1 b hb⟩, hI'⟩

/-- **`check_b`'s first block**: on the first call (`INIT = 0`) the seed `CTLF` copied into `CTL`
and `INIT := 1`; on later calls nothing. -/
def seedMem (w : Mem) : Mem :=
  if w.glob INIT = 0 then (w.copy64 CTL 0 CTLF 0 (w.len64 CTLF).toNat).setG INIT 1 else w

/-- **`check_b` on a thread's memory**: from a memory whose `seedMem` is `ThreadRel` to `a` with
`INIT = 1`, with the range `[j, j + 1)` and the view `v` in the header's word `3`, a returning call
accepts group `j` at `a`, and leaves a memory `ThreadRel` to the state after it with `INIT = 1`. -/
theorem checkB_thr0 (hP : PhaseBProg (Prog.subPB bs checkerProg)) (hm : mode = .verified)
    (n : Nat) (hn : n ≤ 2 ^ 62) (a : AState) (v j : Word) (hj : j.toNat < pend.size)
    (hj62 : j.toNat < 2 ^ 62) (s₀ : St)
    (hR : ThreadRel pins dn ds fe pend bs v (seedMem s₀.mem) a) (hI : (seedMem s₀.mem).glob INIT = 1)
    (hlo : s₀.mem.glob PLO = j) (hhi : s₀.mem.glob PHI = j + 1)
    (hv : rd64 s₀.mem HDRF 3 = v) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "check_b" []
    ⦃fun _ s' => AM.ok (checkPending mode fe (pdAt pend j)) a ∧
      ThreadRel pins dn ds fe pend bs v s'.mem (AM.st (checkPending mode fe (pdAt pend j)) a) ∧
      s'.mem.glob INIT = 1; ⊤⦄ := by
  have hlo' : s₀.mem.glob ⟨9⟩ = j := hlo
  have hhi' : s₀.mem.glob ⟨11⟩ = j + 1 := hhi
  have hv' : ∀ (hb : (3 : Word).toNat < (s₀.mem.arr64 241).size), (s₀.mem.arr64 241)[(3 : Word).toNat] = v := by
    intro hb; rw [← hv]; unfold rd64; rw [Array.getD, dif_pos hb]; rfl
  have hR0 : s₀.mem.glob ⟨10⟩ = 0 → ThreadRel pins dn ds fe pend bs v
      { bytes := (s₀.mem.copy64 1 0 242 0 (UInt64.toNat (s₀.mem.len64 242))).bytes,
        words := (s₀.mem.copy64 1 0 242 0 (UInt64.toNat (s₀.mem.len64 242))).words,
        glob := fun h => if h = ⟨10⟩ then 1
          else (s₀.mem.copy64 1 0 242 0 (UInt64.toNat (s₀.mem.len64 242))).glob h } a := by
    intro h0; have := hR; simp only [seedMem, if_pos h0] at this; exact this
  have hR1 : ¬ s₀.mem.glob ⟨10⟩ = 0 → ThreadRel pins dn ds fe pend bs v s₀.mem a := by
    intro h0; have := hR; simp only [seedMem, if_neg h0] at this; exact this
  have hI1 : ¬ s₀.mem.glob ⟨10⟩ = 0 → s₀.mem.glob ⟨10⟩ = 1 := by
    intro h0; have := hI; simp only [seedMem, if_neg h0] at this; exact this
  have hv0 : ∀ (hb : (3 : Word).toNat < ((s₀.mem.copy64 1 0 242 0 (UInt64.toNat (s₀.mem.len64 242))).arr64 241).size),
      ((s₀.mem.copy64 1 0 242 0 (UInt64.toNat (s₀.mem.len64 242))).arr64 241)[(3 : Word).toNat] = v := by
    intro hb
    simp only [arr64_copy64_ne _ _ _ _ _ _ (show (241 : ArrId) ≠ 1 by decide)] at hb ⊢
    exact hv' hb
  rw [invoke_eq _ checkerProg_lookup_check_b]
  simp only [callFn, checkBL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hcg' := threadGo_thr mode pins dn ds fe pend bs hP hm n (by omega) a v j hj hj62
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, setG, ld64, warr, (hcg' · · ·)]
    all_goals (try simp only [St.setLoc_mem, St.setLoc_loc, St.setLocs_cons,
      Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval,
      reduceIte, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at *)
    all_goals (try simp only [St.setG, Mem.setG, St.setLoc] at *)
    all_goals first
      | (simp only [Mem.copy64_glob] at *; simp_all (config := { decide := true }); done)
      | exact hR0 ‹_›
      | exact hR1 ‹_›
      | exact hv' ‹_›
      | exact hv0 ‹_›
      | (exact hI1 ‹_›)
      | trace_state; sorry

end thread

end L.Checker
