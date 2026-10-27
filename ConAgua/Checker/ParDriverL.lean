import ConAgua.Checker.PhaseBReads
import ConAgua.Arena.FreezeRel
import ConAgua.Checker.LoopProgTac
import ConAgua.Checker.RomProg0
import ConAgua.Final.Statement

/-!
# Entry 2 of the sequential driver, in L (lane parmode)

docs/design/parmode.md, "Redesign". The driver's entry 2 (`ca_check_seq`) runs `check` with the mode
word `2` on a memory `w` that is phase A's memory `m` except in the arrays phase B's loop never
names (`OUT`, the header `HDRF`, the seed `CTLF`, the byte arrays) and in the globals. Then:

* `PhaseBStart.frame0`: `PhaseBStart` does not see a change that keeps every word array (a frame
  with no array write): the globals, the byte arrays.
* `checkPendingGo_agree`: `check_pending_go(0, k, v)` on such a `w` refines phase B on the worker
  (`checkPendingGo_workerT` on `m` with `w`'s globals, through `L/Agree.lean`'s non-interference
  and `checkerProg_phaseBReads`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Checker

open L L.Arena

-- `check_b` (`checkBL`, `ConAgua/Checker/Entry.lean`) returns the literal `ACCEPT`.
example : (71757147230292 : Word) = ConAgua.Final.ACCEPT := rfl

section frame0
variable {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration}
  {fe : IFEnv} {pend : Array PendingCheck} {m m' : Mem} {a : AState} {v : Word}

/-- **`PhaseBStart` across a frame with no array write** (the globals and the byte arrays). -/
theorem PhaseBStart.frame0 (hf : MemFrame [] [] m m') (h : PhaseBStart pins dn ds fe pend m a v) :
    PhaseBStart pins dn ds fe pend m' a v := by
  have hf' : MemFrame scrArrs [] m m' := hf.mono (by simp) (by simp)
  refine ⟨h.loop.of_lo (CheckR.frame_hi (by simp) (by simp) hf h.loop.check) hf' (by simp), ?_,
    CoreMemos.frame_hi hf (by simp) (by simp) h.core, h.twin, CrOK.frame h.cr hf (by simp) (by simp)⟩
  have hM := h.mem
  exact ⟨by rw [hf.2.2.1]; exact hM.erec, by rw [hf.2.2.1]; exact hM.spn, by rw [hf.2.2.1]; exact hM.bstk,
    by simp only [pinW, hf.1 PINS (by simp) (by decide)]; exact hM.flag, hM.dnP⟩

end frame0

/-- The arrays phase B's loop may name: every word array but `OUT`, `HDRF`, `CTLF`. -/
abbrev phaseBS : ArrId → Bool := fun a => a != 240 && a != 241 && a != 242

section agree
variable (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
  (ds : Array IDeclaration) (fe : IFEnv) (pend : Array PendingCheck)

/-- **Phase B's loop on a memory that agrees with phase A's on what the loop names**: a returning
`check_pending_go(0, k, v)` from a state whose memory has `m`'s word arrays except `OUT`, `HDRF`,
`CTLF` (and any globals and byte arrays) means the twin's phase B on `a.worker` accepts. -/
theorem checkPendingGo_agree (bs : List UInt8) (hP : PhaseBProg (Prog.subPB bs checkerProg))
    (hm : mode = .verified) (n : Nat)
    (hn : n ≤ 2 ^ 62) (m : Mem) (a : AState) (v k : Word) (hk : k.toNat = pend.size)
    (hPB : m.arr8 L.Rom.PB = bs.toArray)
    (h : PhaseBStart pins dn ds fe pend m a v) (x y z : Word) :
    ⦃fun s => x = 0 ∧ y = k ∧ z = v ∧ ∀ b, phaseBS b = true → s.mem.arr64 b = m.arr64 b⦄
    invoke checkerProg (exec checkerProg n) "check_pending_go" [x, y, z]
    ⦃fun _ _ => ∃ s'', checkPendingList mode fe pend.toList a.worker = .ok (.ok (), s''); ⊤⦄ := by
  apply M.triple_of_run
  rintro s rs s' ⟨hx, hy, hz, hw⟩ hrun
  subst hx hy hz
  -- phase A's memory with the worker's globals and byte arrays
  let m₂ : Mem := { m with glob := s.mem.glob }
  have hf : MemFrame [] [] m m₂ := ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl, rfl⟩
  have h₂ := PhaseBStart.frame0 hf h
  let s₂ : St := ⟨m₂, s.loc⟩
  have hAg : Agree phaseBS (fun _ => false) s.mem s₂.mem :=
    ⟨fun b hb => hw b hb, fun _ hb => absurd hb (by simp), rfl⟩
  obtain ⟨s₂', hrun₂, -, -⟩ :=
    invoke_agree_ok checkerProg_phaseBReads check_pending_go_mem_phaseBFns hAg rfl hrun
  rw [← L.Rom.invoke_subPB (bs := bs) checkerProg_noSt8PB n _ _ (s := s₂) hPB] at hrun₂
  have := M.of_run (P := fun x => x = s₂) rfl hrun₂
    (checkPendingGo_workerT mode pins dn ds (Prog.subPB bs checkerProg) fe pend hP hm n hn s₂ a _ _ hk
      h₂.twin h₂.loop h₂.mem h₂.core h₂.cr)
  exact this.2.1

theorem checkerProg_lookup_check_b : checkerProg.lookup "check_b" = some checkBL := by chk_lk
theorem checkerProg_lookup_check' : checkerProg.lookup "check" = some checkL := by chk_lk

/-- **Entry 2 in place, `check_b`**: from a memory that agrees with phase A's on what phase B's
loop names, with the range `[0, k)` (`k` the number of pending groups), an empty seed `CTLF` and the
view `v` in the header's word 3, a run that returns `ACCEPT` means the twin's phase B on
`a.worker` accepts. -/
theorem checkB_agree0 (bs : List UInt8) (hP : PhaseBProg (Prog.subPB bs checkerProg))
    (hm : mode = .verified) (n : Nat)
    (hn : n ≤ 2 ^ 62) (m : Mem) (a : AState) (v k : Word) (hk : k.toNat = pend.size)
    (hPB : m.arr8 L.Rom.PB = bs.toArray) (h : PhaseBStart pins dn ds fe pend m a v) (s₀ : St)
    (hw : ∀ b, phaseBS b = true → s₀.mem.arr64 b = m.arr64 b)
    (hlo : s₀.mem.glob PLO = 0) (hhi : s₀.mem.glob PHI = k) (hctlf : (s₀.mem.arr64 CTLF).size = 0)
    (hv : rd64 s₀.mem HDRF 3 = v) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "check_b" []
    ⦃fun r _ => r.headD 0 = ConAgua.Final.ACCEPT →
      ∃ s'', checkPendingList mode fe pend.toList a.worker = .ok (.ok (), s''); ⊤⦄ := by
  have hl : (UInt64.toNat (s₀.mem.len64 242)) = 0 := by simp [Mem.len64, show (242 : ArrId) = CTLF from rfl, hctlf]
  have hlo' : s₀.mem.glob ⟨9⟩ = 0 := hlo
  have hhi' : s₀.mem.glob ⟨11⟩ = k := hhi
  have hv' : ∀ (hb : (3 : Word).toNat < (s₀.mem.arr64 241).size), (s₀.mem.arr64 241)[(3 : Word).toNat] = v := by
    intro hb; rw [← hv]; unfold rd64; rw [Array.getD, dite_eq_left hb]; rfl
  rw [invoke_eq _ checkerProg_lookup_check_b]
  simp only [callFn, checkBL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hcg' := checkPendingGo_agree mode pins dn ds fe pend bs hP hm n (by omega) m a v k hk hPB h
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, setG, ld64, warr, (hcg' · · ·)]
    all_goals (try simp only [St.setLoc_mem, St.setLoc_loc,
      Locals.init_nil, Cmp.eval,
      reduceIte, beq_iff_eq, decide_eq_true_eq] at *)
    all_goals (try simp only [hl, Mem.copy64_zero] at *)
    all_goals (try simp only [St.setG, Mem.setG, St.setLoc] at *)
    all_goals first
      | (simp_all (config := { decide := true }) [Mem.arr64]; done)
      | exact hv' ‹_›
      | (simp only [Mem.arr64] at *; grind)

/-- `checkB_agree0` with the memory facts as the precondition. -/
theorem checkB_agree (bs : List UInt8) (hP : PhaseBProg (Prog.subPB bs checkerProg))
    (hm : mode = .verified) (n : Nat)
    (hn : n ≤ 2 ^ 62) (m : Mem) (a : AState) (v k : Word) (hk : k.toNat = pend.size)
    (hPB : m.arr8 L.Rom.PB = bs.toArray) (h : PhaseBStart pins dn ds fe pend m a v) :
    ⦃fun s => (∀ b, phaseBS b = true → s.mem.arr64 b = m.arr64 b) ∧ s.mem.glob PLO = 0 ∧
      s.mem.glob PHI = k ∧ (s.mem.arr64 CTLF).size = 0 ∧ rd64 s.mem HDRF 3 = v⦄
    invoke checkerProg (exec checkerProg n) "check_b" []
    ⦃fun r _ => r.headD 0 = ConAgua.Final.ACCEPT →
      ∃ s'', checkPendingList mode fe pend.toList a.worker = .ok (.ok (), s''); ⊤⦄ := by
  apply M.triple_of_run
  intro s₀ rs s' ⟨hw, hlo, hhi, hctlf, hv⟩ hrun
  exact M.of_run (P := fun x => x = s₀) rfl hrun
    (checkB_agree0 mode pins dn ds fe pend bs hP hm n hn m a v k hk hPB h s₀ hw hlo hhi hctlf hv)

/-- **Entry 2 in place, `check` with the mode word `2`**: `check_b` (as `checkB_agree`). -/
theorem checkMode2_agree (bs : List UInt8) (hP : PhaseBProg (Prog.subPB bs checkerProg))
    (hm : mode = .verified) (n : Nat)
    (hn : n ≤ 2 ^ 62) (m : Mem) (a : AState) (v k : Word) (hk : k.toNat = pend.size)
    (hPB : m.arr8 L.Rom.PB = bs.toArray) (h : PhaseBStart pins dn ds fe pend m a v) (s₀ : St)
    (hw : ∀ b, phaseBS b = true → s₀.mem.arr64 b = m.arr64 b) (hmode : s₀.mem.glob MODE = 2)
    (hlo : s₀.mem.glob PLO = 0) (hhi : s₀.mem.glob PHI = k) (hctlf : (s₀.mem.arr64 CTLF).size = 0)
    (hv : rd64 s₀.mem HDRF 3 = v) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "check" []
    ⦃fun r _ => r.headD 0 = ConAgua.Final.ACCEPT →
      ∃ s'', checkPendingList mode fe pend.toList a.worker = .ok (.ok (), s''); ⊤⦄ := by
  rw [invoke_eq _ checkerProg_lookup_check']
  simp only [callFn, checkL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hB := checkB_agree mode pins dn ds fe pend bs hP hm n (by omega) m a v k hk hPB h
    have hmode' : s₀.mem.glob ⟨8⟩ = 2 := hmode
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, hB,
      (L.invoke_loc checkerProg (exec checkerProg n) "check_a" [1] ·),
      (L.invoke_loc checkerProg (exec checkerProg n) "check_a" [0] ·)]
    all_goals (try simp only [St.setLoc_loc, St.setLocs_cons,
      Cmp.eval, reduceIte, beq_iff_eq, Sig.retVal, Sig.retOr, St.setLocs_nil, List.headD_cons] at *)
    all_goals first
      | (simp_all (config := { decide := true }); done)
      | (simp_all [St.setLoc]; done)

/-- **Entry 2 in place, as a run**: `L.run checkerProg n "check" [] w` returning `ACCEPT`, from a
memory `w` as `checkMode2_agree` asks. -/
theorem runMode2_agree (bs : List UInt8) (hP : PhaseBProg (Prog.subPB bs checkerProg))
    (hm : mode = .verified) (n : Nat)
    (hn : n ≤ 2 ^ 62) (m : Mem) (a : AState) (v k : Word) (hk : k.toNat = pend.size)
    (hPB : m.arr8 L.Rom.PB = bs.toArray) (h : PhaseBStart pins dn ds fe pend m a v) (w : Mem)
    (hw : ∀ b, phaseBS b = true → w.arr64 b = m.arr64 b) (hmode : w.glob MODE = 2)
    (hlo : w.glob PLO = 0) (hhi : w.glob PHI = k) (hctlf : (w.arr64 CTLF).size = 0)
    (hv : rd64 w HDRF 3 = v) {rs : List Word} {w' : Mem}
    (hrun : L.run checkerProg n "check" [] w = .ok (rs, w'))
    (hacc : rs.headD 0 = ConAgua.Final.ACCEPT) :
    ∃ s'', checkPendingList mode fe pend.toList a.worker = .ok (.ok (), s'') := by
  simp only [L.run] at hrun
  cases e : (invoke checkerProg (exec checkerProg n) "check" []).run ⟨w, Locals.init []⟩ with
  | error _ => rw [e] at hrun; cases hrun
  | ok x =>
    obtain ⟨r, s⟩ := x
    rw [e] at hrun
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at hrun
    obtain ⟨rfl, -⟩ := hrun
    exact M.of_run (P := fun x => x = ⟨w, Locals.init []⟩) rfl e
      (checkMode2_agree mode pins dn ds fe pend bs hP hm n hn m a v k hk hPB h ⟨w, Locals.init []⟩ hw hmode
        hlo hhi hctlf hv) hacc

end agree

end L.Checker
