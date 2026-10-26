import ConAgua.Verdict.PhaseBE
import ConAgua.Checker.ParThreadTwin
import ConAgua.Final.TwinVerdict

/-!
# A thread's failing call is the twin pool's failure (lane verdicts-b)

The error halves of `ParThreadCall.lean` and `ParThreadTwin.lean`. A thread calls entry 2 once per
group index it claims, on its own region (`ThreadRuns`); when call `j` fails with a class other
than `0`, the twin's worker, from phase A's state, checking the thread's groups in order up to and
including `j`, fails with that class (`checkPendingList` reports it as a value).

* `PhaseBStart.oneE`: `check_pending_go(j, j + 1, v)` from `PhaseBStart` fails only where
  `checkPending` on group `j` does (from `check_pending`'s error claim `CPErrT`);
* `threadGo_thrE`, `checkB_thrE`, `checkThrE`, `runThrE`: the same on a thread's memory
  (`ThreadRel`), through `check_b` and `check`;
* `thrCall_firstE`, `thrCall_nextE`: a thread's first and later call;
* `thread_chainE`, `thread_failsE`: the calls before ran ok (`thrCall_next`), the failing one
  ends the group list (`checkPendingList_fails_tail`, `checkPendingList_fails_head`);
* `threads_twinVerdictPooled`: with entry 1's run, `TwinVerdictPooled [b]` (its second
  disjunct), given `check_pending`'s error claim at the programs `entry2Verdict_of` takes it.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open ConRon.Bridge (ListRel)

theorem listRel_drop {α β : Type} {R : α → β → Prop} :
    ∀ (k : Nat) {xs : List α} {ys : List β}, ListRel R xs ys → ListRel R (xs.drop k) (ys.drop k)
  | 0, _, _, h => h
  | _ + 1, _, _, .nil => .nil
  | k + 1, _, _, .cons _ hr => listRel_drop k hr

/-- `TwinPend` over the groups from `k` on. -/
theorem TwinPend.drop {fe : IFEnv} {l : List PendingCheck} {a : AState} (h : TwinPend fe l a)
    (k : Nat) : TwinPend fe (l.drop k) a := by
  obtain ⟨env, pendP, hok, hnd, hrel⟩ := h.fold
  exact ⟨⟨env, pendP.drop k, hok, hnd, listRel_drop k hrel⟩,
    fun hne => h.caches fun e => hne (by simp [e]), h.off,
    fun hne => h.dropped fun e => hne (by simp [e])⟩

section one
variable (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
  (ds : Array IDeclaration) (p : Prog) (fe : IFEnv) (pend : Array PendingCheck)

/-- `check_pending_go(k, k, v)` fails only with class `0`. -/
theorem checkPendingGo_emptyE (hP : PhaseBProg p) (n : Nat) (m : Mem) (k v : Word) {e : Err}
    (h : callE p n "check_pending_go" [k, k, v] m = .error e) : e.cls = 0 := by
  cases n with
  | zero =>
    obtain ⟨e', he', h0⟩ := callE_zero p "check_pending_go" [k, k, v] m
    rw [h] at he'; cases he'; exact h0
  | succ n =>
    by_cases hk0 : e.cls = 0
    · exact hk0
    exfalso
    have hW := triple_of_callE_err (checkPendingGo_specE p hP.cpg (n + 1) ⟨m, Locals.init []⟩ k k v)
      h (Err.code_ne_of_cls hk0)
    simp only [checkPendingGoE] at hW
    rw [ite_eq_left trivial] at hW
    cases hW

/-- **One group through phase B's loop, error half of `PhaseBStart.one`**: a failing
`check_pending_go(j, j + 1, v)` from `PhaseBStart` claims `checkPending`'s failure on group `j`. -/
theorem PhaseBStart.oneE (hP : PhaseBProg p)
    (hE : CPErrT mode pins dn ds p fe pend) (n : Nat) (hn : n ≤ 2 ^ 62)
    (m : Mem) (a₀ : AState) (j v : Word) (hj : j.toNat < pend.size) (hj62 : j.toNat < 2 ^ 62)
    (h : PhaseBStart pins dn ds fe pend m a₀ v) {e : Err}
    (hc : callE p n "check_pending_go" [j, j + 1, v] m = .error e) :
    ErrClaim (checkPending mode fe (pdAt pend j)) a₀ e := by
  intro hk0
  have h1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  cases n with
  | zero =>
    obtain ⟨e', he', h0⟩ := callE_zero p "check_pending_go" [j, j + 1, v] m
    rw [hc] at he'; cases he'; exact absurd h0 hk0
  | succ n =>
    have hW := triple_of_callE_err (checkPendingGo_specE p hP.cpg (n + 1) ⟨m, Locals.init []⟩ j (j + 1) v)
      hc (Err.code_ne_of_cls hk0)
    simp only [checkPendingGoE] at hW
    have g1 : ¬ j = j + 1 := fun e' => by have := congrArg UInt64.toNat e'; omega
    rw [ite_eq_right g1] at hW
    cases h2 : callE p n "check_pending_next" [j, j + 1, v] m with
    | ok q =>
      obtain ⟨r, m₁⟩ := q
      rw [h2, checkPendingGoE.k_check_pending_next.arm1] at hW
      cases hW
    | error e1 =>
      rw [h2, checkPendingGoE.k_check_pending_next.none] at hW
      cases hW
      cases n with
      | zero =>
        obtain ⟨e', he', h0⟩ := callE_zero p "check_pending_next" [j, j + 1, v] m
        rw [h2] at he'; cases he'; exact absurd h0 hk0
      | succ n =>
        have hn' : n ≤ 2 ^ 62 := by omega
        have hW := triple_of_callE_err
          (checkPendingNext_specE p hP.cpx (n + 1) ⟨m, Locals.init []⟩ j (j + 1) v) h2
          (Err.code_ne_of_cls hk0)
        simp only [checkPendingNextE] at hW
        have g2 : ¬ 4611686018427387904 ≤ j := fun g => by
          have := UInt64.le_iff_toNat_le.mp g; simp at this; omega
        rw [ite_eq_right g2] at hW
        cases hc1 : callE p n "check_pending" [j, v] m with
        | error e2 =>
          rw [hc1, checkPendingNextE.k_check_pending.none] at hW
          cases hW
          have hT := h.twin.drop j.toNat
          exact CoreSpecE.of_callE (hE n hn' ⟨m, Locals.init []⟩ a₀ j v hj hT h.loop h.mem h.core hj62 h.cr)
            hc1 hk0
        | ok q =>
          obtain ⟨r, m₁⟩ := q
          rw [hc1] at hW
          simp only [checkPendingNextE.k_check_pending] at hW
          cases hc2 : callE p n "check_pending_go" [j + 1, j + 1, v] m₁ with
          | error e3 =>
            rw [hc2, checkPendingNextE.k_check_pending_go.none] at hW
            cases hW
            exact absurd (checkPendingGo_emptyE p hP n m₁ (j + 1) v hc2) hk0
          | ok q2 =>
            obtain ⟨r2, m₂⟩ := q2
            rw [hc2, checkPendingNextE.k_check_pending_go.arm1] at hW
            cases hW

end one

end L.Arena

namespace L.Checker

open L L.Arena L.Rom

section thread
variable (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
  (ds : Array IDeclaration) (fe : IFEnv) (pend : Array PendingCheck) (bs : List UInt8)

/-- **Phase B's loop over one group on a thread's memory, error half of `threadGo_thr`.** -/
theorem threadGo_thrE (hP : PhaseBProg (Prog.subPB bs checkerProg))
   
    (hE : CPErrT mode pins dn ds (Prog.subPB bs checkerProg) fe pend)
    (n : Nat) (hn : n ≤ 2 ^ 62) (a : AState) (v j : Word) (hj : j.toNat < pend.size)
    (hj62 : j.toNat < 2 ^ 62) (x y z : Word) :
    ⦃fun s => x = j ∧ y = j + 1 ∧ z = v ∧ ThreadRel pins dn ds fe pend bs v s.mem a⦄
    invoke checkerProg (exec checkerProg n) "check_pending_go" [x, y, z]
    ⦃fun _ _ => True; ErrClaim (checkPending mode fe (pdAt pend j)) a⦄ := by
  apply M.triple_of_run' (fun _ _ _ _ _ => trivial)
  rintro s e ⟨hx, hy, hz, ⟨m', hS, hPB, hw⟩⟩ hrun
  rw [hx, hy, hz] at hrun
  let m₂ : Mem := { m' with glob := s.mem.glob }
  have hf : MemFrame [] [] m' m₂ := ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl, rfl⟩
  have h₂ := PhaseBStart.frame0 hf hS
  have hrun₀ : (invoke checkerProg (exec checkerProg n) "check_pending_go" [j, j + 1, v]).run
      ⟨s.mem, Locals.init []⟩ = .error e := by
    rw [invoke_run_loc'] at hrun
    cases hq : (invoke checkerProg (exec checkerProg n) "check_pending_go" [j, j + 1, v]).run
      ⟨s.mem, Locals.init []⟩ with
    | error e' => rw [hq] at hrun; simp [Except.map] at hrun; rw [hrun]
    | ok q => rw [hq] at hrun; simp [Except.map] at hrun
  have hAg : Agree thrS (fun _ => false) s.mem m₂ :=
    ⟨fun b hb => hw b hb, fun _ hb => absurd hb (by simp), rfl⟩
  have hres := L.invoke_agree checkerProg_thrReads check_pending_go_mem_phaseBFns n [j, j + 1, v]
    (s₁ := ⟨s.mem, Locals.init []⟩) (s₂ := ⟨m₂, Locals.init []⟩) hAg rfl
  rw [hrun₀] at hres
  have hrun₂ : (invoke checkerProg (exec checkerProg n) "check_pending_go" [j, j + 1, v]).run
      ⟨m₂, Locals.init []⟩ = .error e := by
    revert hres
    cases (invoke checkerProg (exec checkerProg n) "check_pending_go" [j, j + 1, v]).run
      ⟨m₂, Locals.init []⟩ with
    | ok q => intro h'; exact h'.elim
    | error e' => intro h'; cases h'; rfl
  rw [← L.Rom.invoke_subPB (bs := bs) checkerProg_noSt8PB n _ _ (s := ⟨m₂, Locals.init []⟩) hPB]
    at hrun₂
  have hc : callE (Prog.subPB bs checkerProg) n "check_pending_go" [j, j + 1, v] m₂ = .error e := by
    simp only [callE, hrun₂]
  exact PhaseBStart.oneE mode pins dn ds (Prog.subPB bs checkerProg) fe pend hP hE n hn m₂ a j v hj
    hj62 h₂ hc

/-- **`check_b` on a thread's memory, error half of `checkB_thr0`.** -/
theorem checkB_thrE (hP : PhaseBProg (Prog.subPB bs checkerProg))
   
    (hE : CPErrT mode pins dn ds (Prog.subPB bs checkerProg) fe pend)
    (n : Nat) (hn : n ≤ 2 ^ 62) (a : AState) (v j : Word) (hj : j.toNat < pend.size)
    (hj62 : j.toNat < 2 ^ 62) (s₀ : St)
    (hR : ThreadRel pins dn ds fe pend bs v (seedMem s₀.mem) a)
    (hlo : s₀.mem.glob PLO = j) (hhi : s₀.mem.glob PHI = j + 1)
    (hv : ∀ hb : 3 < (s₀.mem.arr64 HDRF).size, (s₀.mem.arr64 HDRF)[3] = v) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "check_b" []
    ⦃fun _ _ => True; ErrClaim (checkPending mode fe (pdAt pend j)) a⦄ := by
  have hlo' : s₀.mem.glob ⟨9⟩ = j := hlo
  have hhi' : s₀.mem.glob ⟨11⟩ = j + 1 := hhi
  have hv' : ∀ (hb : (3 : Word).toNat < (s₀.mem.arr64 241).size), (s₀.mem.arr64 241)[(3 : Word).toNat] = v := by
    intro hb; exact hv hb
  have hR0 : s₀.mem.glob ⟨10⟩ = 0 → ThreadRel pins dn ds fe pend bs v
      { bytes := (s₀.mem.copy64 1 0 242 0 (UInt64.toNat (s₀.mem.len64 242))).bytes,
        words := (s₀.mem.copy64 1 0 242 0 (UInt64.toNat (s₀.mem.len64 242))).words,
        glob := fun h => if h = ⟨10⟩ then 1
          else (s₀.mem.copy64 1 0 242 0 (UInt64.toNat (s₀.mem.len64 242))).glob h } a := by
    intro h0; have := hR; simp only [seedMem, ite_eq_left h0] at this; exact this
  have hR1 : ¬ s₀.mem.glob ⟨10⟩ = 0 → ThreadRel pins dn ds fe pend bs v s₀.mem a := by
    intro h0; have := hR; simp only [seedMem, ite_eq_right h0] at this; exact this
  have hv0 : ∀ (hb : (3 : Word).toNat < ((s₀.mem.copy64 1 0 242 0 (UInt64.toNat (s₀.mem.len64 242))).arr64 241).size),
      ((s₀.mem.copy64 1 0 242 0 (UInt64.toNat (s₀.mem.len64 242))).arr64 241)[(3 : Word).toNat] = v := by
    intro hb
    simp only [arr64_copy64_ne _ _ _ _ _ _ (show (241 : ArrId) ≠ 1 by decide)] at hb ⊢
    exact hv' hb
  rw [invoke_eq _ checkerProg_lookup_check_b]
  simp only [callFn, checkBL]
  cases n with
  | zero => vcgen [exec] <;> simp [ErrClaim.of_cls0]
  | succ n =>
    have hcg' := threadGo_thrE mode pins dn ds fe pend bs hP hE n (by omega) a v j hj hj62
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, setG, ld64, warr, (hcg' · · ·)]
    all_goals (try simp only [St.setLoc_mem, St.setLoc_loc,
      Locals.init_nil, Cmp.eval,
      reduceIte, beq_iff_eq, decide_eq_true_eq] at *)
    all_goals (try simp only [St.setG, Mem.setG, St.setLoc] at *)
    all_goals first
      | exact ErrClaim.of_cls0 (by decide)
      | (simp only [Mem.copy64_glob] at *; simp_all (config := { decide := true }); done)
      | exact hR0 ‹_›
      | exact hR1 ‹_›
      | exact hv' ‹_›
      | exact hv0 ‹_›
      | (trace_state; fail "ThreadsE: no closing tactic applies")

/-- **`check` with the mode word `2` on a thread's memory, error half of `checkThr`.** -/
theorem checkThrE (hP : PhaseBProg (Prog.subPB bs checkerProg))
   
    (hE : CPErrT mode pins dn ds (Prog.subPB bs checkerProg) fe pend)
    (n : Nat) (hn : n ≤ 2 ^ 62) (a : AState) (v j : Word) (hj : j.toNat < pend.size)
    (hj62 : j.toNat < 2 ^ 62) (s₀ : St) (hmode : s₀.mem.glob MODE = 2)
    (hR : ThreadRel pins dn ds fe pend bs v (seedMem s₀.mem) a)
    (hlo : s₀.mem.glob PLO = j) (hhi : s₀.mem.glob PHI = j + 1)
    (hv : ∀ hb : 3 < (s₀.mem.arr64 HDRF).size, (s₀.mem.arr64 HDRF)[3] = v) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "check" []
    ⦃fun _ _ => True; ErrClaim (checkPending mode fe (pdAt pend j)) a⦄ := by
  rw [invoke_eq _ checkerProg_lookup_check']
  simp only [callFn, checkL]
  cases n with
  | zero => vcgen [exec] <;> simp [ErrClaim.of_cls0]
  | succ n =>
    have hB : ⦃fun s => s.mem = s₀.mem⦄ invoke checkerProg (exec checkerProg n) "check_b" []
        ⦃fun _ _ => True; ErrClaim (checkPending mode fe (pdAt pend j)) a⦄ := by
      apply M.triple_of_run' (fun _ _ _ _ _ => trivial)
      intro s₁ e hs hrun
      exact M.of_run_err (P := fun x => x = s₁) rfl hrun
        (checkB_thrE mode pins dn ds fe pend bs hP hE n (by omega) a v j hj hj62 s₁ (hs ▸ hR)
          (hs ▸ hlo) (hs ▸ hhi) (hs ▸ hv))
    have hmode' : s₀.mem.glob ⟨8⟩ = 2 := hmode
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, hB,
      (callE_spec checkerProg n "check_a" [1] ·), (callE_spec checkerProg n "check_a" [0] ·)]
    all_goals (try simp only [
      Cmp.eval, beq_iff_eq] at *)
    all_goals first
      | exact ErrClaim.of_cls0 (by decide)
      | (simp_all (config := { decide := true }); done)
      | (simp_all [St.setLoc]; done)

/-- **One call, as a run, error half of `runThr`.** -/
theorem runThrE (hP : PhaseBProg (Prog.subPB bs checkerProg))
   
    (hE : CPErrT mode pins dn ds (Prog.subPB bs checkerProg) fe pend)
    (n : Nat) (hn : n ≤ 2 ^ 62) (a : AState) (v j : Word) (hj : j.toNat < pend.size)
    (hj62 : j.toNat < 2 ^ 62) (w : Mem) (hmode : w.glob MODE = 2)
    (hR : ThreadRel pins dn ds fe pend bs v (seedMem w) a)
    (hlo : w.glob PLO = j) (hhi : w.glob PHI = j + 1)
    (hv : ∀ hb : 3 < (w.arr64 HDRF).size, (w.arr64 HDRF)[3] = v) {e : Err}
    (hrun : L.run checkerProg n "check" [] w = .error e) :
    ErrClaim (checkPending mode fe (pdAt pend j)) a e := by
  simp only [L.run] at hrun
  cases hq : (invoke checkerProg (exec checkerProg n) "check" []).run ⟨w, Locals.init []⟩ with
  | ok x => rw [hq] at hrun; cases hrun
  | error e' =>
    rw [hq] at hrun
    simp only [Except.map, Except.error.injEq] at hrun
    subst hrun
    exact M.of_run_err (P := fun x => x = ⟨w, Locals.init []⟩) rfl hq
      (checkThrE mode pins dn ds fe pend bs hP hE n hn a v j hj hj62 ⟨w, Locals.init []⟩ hmode hR
        hlo hhi hv)

/-- **A thread's first call, error half of `thrCall_first`.** -/
theorem thrCall_firstE (hP : PhaseBProg (Prog.subPB bs checkerProg))
   
    (hE : CPErrT mode pins dn ds (Prog.subPB bs checkerProg) fe pend)
    {m : Mem} {a : AState} {v : Word} (hS : PhaseBStart pins dn ds fe pend m a v)
    (hPB : m.arr8 PB = bs.toArray) (hok : parCompactOK m 1 = true)
    (hlt : (m.arr64 OUT).size < 2 ^ 64)
    (r : Mem) (hr : 388 ≤ r.words.size) (hz : ∀ b ∈ parOwnedL, r.arr64 b = zeros (m.arr64 b).size)
    (hI : r.glob INIT = 0) (j : Word) (hj : j.toNat < pend.size) (hj62 : j.toNat < 2 ^ 62)
    (n : Nat) (hn : n ≤ 2 ^ 62) {e : Err}
    (hrun : L.run checkerProg n "check" [] (bufMem (bufOf m v) r j) = .error e) :
    ErrClaim (checkPending mode fe (pdAt pend j)) a.worker e := by
  obtain ⟨hR, -⟩ := ThreadRel.first hS hPB (by omega) hok hlt r j hr hz hI
  exact runThrE mode pins dn ds fe pend bs hP hE n hn a.worker v j hj hj62 _ rfl hR rfl rfl
    (bufMem_view (bufImg_hdr hok hlt) r j) hrun

/-- **A thread's later call, error half of `thrCall_next`.** -/
theorem thrCall_nextE (hP : PhaseBProg (Prog.subPB bs checkerProg))
   
    (hE : CPErrT mode pins dn ds (Prog.subPB bs checkerProg) fe pend)
    {B : Array Word} {v : Word} (hB : (bufImg B 0).getD 3 0 = v) {r : Mem} {a : AState}
    (hR : ThreadRel pins dn ds fe pend bs v r a) (hI : r.glob INIT = 1)
    (hfz : ∀ k (hk : k < frozen.length), 1 ≤ k → r.arr64 frozen[k].1 = bufImg B (k + 1))
    (j : Word) (hj : j.toNat < pend.size) (hj62 : j.toNat < 2 ^ 62)
    (n : Nat) (hn : n ≤ 2 ^ 62) {e : Err}
    (hrun : L.run checkerProg n "check" [] (bufMem B r j) = .error e) :
    ErrClaim (checkPending mode fe (pdAt pend j)) a e := by
  have hI' : (bufMem B r j).glob INIT ≠ 0 := by rw [bufMem_glob_init, hI]; decide
  have hs := seedMem_of_ne hI'
  refine runThrE mode pins dn ds fe pend bs hP hE n hn a v j hj hj62 _ rfl ?_ rfl rfl
    (bufMem_view hB r j) hrun
  rw [hs]; exact ThreadRel.next B j hR hfz

end thread

/-! ## A thread's calls, the last one failing -/

/-- **A thread's calls ending in a failure**: the calls `cs` from the region memory `r` ran as
`ThreadRuns` says, and the next call, on group `j` with fuel `n ≤ 2^62`, on `bufMem B r' j` (`r'`
the last call's final memory, `r` if there was none), failed with `e`. -/
def ThreadFails (B : Array Word) (j : Word) (n : Nat) (e : Err) : Mem → List (Word × Nat × Mem) → Prop
  | r, [] => n ≤ 2 ^ 62 ∧ L.run checkerProg n "check" [] (bufMem B r j) = .error e
  | r, (j', n', r') :: cs => n' ≤ 2 ^ 62 ∧
      (∃ rs, L.run checkerProg n' "check" [] (bufMem B r j') = .ok (rs, r')) ∧ BufKept B r' ∧
      ThreadFails B j n e r' cs

section chain
variable (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
  (ds : Array IDeclaration) (fe : IFEnv) (pend : Array PendingCheck) (bs : List UInt8)

/-- **A thread's later calls, the last failing** (error half of `thread_chain`): the groups of
the calls that ran, then the failing group, fail in order from `a`. -/
theorem thread_chainE (hP : PhaseBProg (Prog.subPB bs checkerProg)) (hm : mode = .verified)
    (hE : CPErrT mode pins dn ds (Prog.subPB bs checkerProg) fe pend)
    (hpend : pend.size ≤ 2 ^ 62) {B : Array Word} {v : Word} (hB : (bufImg B 0).getD 3 0 = v)
    (j : Word) (hj : j.toNat < pend.size) (n : Nat) (e : Err) (hk0 : e.cls ≠ 0) :
    ∀ (cs : List (Word × Nat × Mem)) (r : Mem) (a : AState),
      ThreadRel pins dn ds fe pend bs v r a → r.glob INIT = 1 → BufKept B r →
      ThreadFails B j n e r cs → (∀ c ∈ cs, c.1.toNat < pend.size) →
      TwinFailsV (checkPendingList mode fe (thrGroups pend cs ++ [pdAt pend j])) a e.cls
  | [], r, a, hR, hI, hk, ⟨hn, hrun⟩, _ =>
    checkPendingList_fails_head
      (thrCall_nextE mode pins dn ds fe pend bs hP hE hB hR hI hk j hj (by omega) n hn hrun hk0)
  | (j', n', r') :: cs, r, a, hR, hI, hk, ⟨hn, ⟨rs, hrun⟩, hk', hrest⟩, hj' => by
    have hj'' : j'.toNat < pend.size := hj' _ List.mem_cons_self
    obtain ⟨hok, hR', hI'⟩ := thrCall_next mode pins dn ds fe pend bs hP hm hB hR hI hk j' hj''
      (by omega) n' hn hrun
    simp only [thrGroups, List.map_cons, List.cons_append]
    exact checkPendingList_fails_tail hok
      (thread_chainE hP hm hE hpend hB j hj n e hk0 cs r' _ hR' hI' hk' hrest
        (fun c hc => hj' c (List.mem_cons_of_mem _ hc)))

/-- **A thread's calls, the last failing, from phase A's worker state** (error half of
`thread_accepts`). -/
theorem thread_failsE (hP : PhaseBProg (Prog.subPB bs checkerProg)) (hm : mode = .verified)
    (hE : CPErrT mode pins dn ds (Prog.subPB bs checkerProg) fe pend)
    {m : Mem} {a : AState} {v : Word} (hS : PhaseBStart pins dn ds fe pend m a v)
    (hPB : m.arr8 PB = bs.toArray) (hok : parCompactOK m 1 = true)
    (hlt : (m.arr64 OUT).size < 2 ^ 64)
    (r₀ : Mem) (hr : 388 ≤ r₀.words.size)
    (hz : ∀ b ∈ parOwnedL, r₀.arr64 b = zeros (m.arr64 b).size) (hI : r₀.glob INIT = 0)
    (j : Word) (hj : j.toNat < pend.size) (n : Nat) (e : Err) (hk0 : e.cls ≠ 0)
    (cs : List (Word × Nat × Mem)) (hruns : ThreadFails (bufOf m v) j n e r₀ cs)
    (hcs : ∀ c ∈ cs, c.1.toNat < pend.size) :
    TwinFailsV (checkPendingList mode fe (thrGroups pend cs ++ [pdAt pend j])) a.worker e.cls := by
  have hpend : pend.size ≤ 2 ^ 62 := by
    have := hS.loop.pend.bound; rw [hS.loop.pend.count] at this; exact this
  match cs, hruns, hcs with
  | [], ⟨hn, hrun⟩, _ =>
    exact checkPendingList_fails_head
      (thrCall_firstE mode pins dn ds fe pend bs hP hE hS hPB hok hlt r₀ hr hz hI j hj (by omega)
        n hn hrun hk0)
  | (j', n', r') :: cs, ⟨hn, ⟨rs, hrun⟩, hk', hrest⟩, hcs =>
    have hj' : j'.toNat < pend.size := hcs _ List.mem_cons_self
    obtain ⟨hok', hR', hI'⟩ := thrCall_first mode pins dn ds fe pend bs hP hm hS hPB hok hlt r₀ hr hz
      hI j' hj' (by omega) n' hn hrun
    simp only [thrGroups, List.map_cons, List.cons_append]
    exact checkPendingList_fails_tail hok'
      (thread_chainE mode pins dn ds fe pend bs hP hm hE hpend (bufImg_hdr hok hlt) j hj n e hk0 cs r' _
        hR' hI' hk' hrest (fun c hc => hcs c (List.mem_cons_of_mem _ hc)))

end chain

/-! ## With entry 1 -/

/-- **`check_pending`'s error claim at the programs phase B runs** (the hypothesis
`entry2Verdict_of` takes): under the program facts `drv_twinAccepts` has. -/
def CPVerdict : Prop :=
  ∀ (bs : List UInt8) (dn : NIdx → Option ConLeche.Name), RomOK bs →
    bs = romData ++ bs.drop romData.length → L.Ind.DnInj dn → QuotDn dn →
    PhaseBProg (Prog.subPB bs checkerProg) → ∀ pins ds fe pend,
    CPErrT .verified pins dn ds (Prog.subPB bs checkerProg) fe pend

open ConAgua.Final in
/-- **A thread's failing call is the twin pool's failure.** Entry 1 (`check` with the mode word
`1`, from the loaded memory) returning `2^63 + k`; the buffer `B` (the first `len` words of `OUT`,
`len` the header's word `1`); a thread with a fresh region memory `r₀` (as in
`threads_twinAcceptsPooled`) whose calls `cs` ran (`ThreadRuns`) and whose next call, on group
`j`, failed with an error `e` of class other than `0` (`ThreadFails`), every group index below `k`.
Then the twin's pool fails with that class (`TwinVerdictPooled`, its second disjunct: the worker
checking the thread's groups up to and including `j`). -/
theorem threads_twinVerdictPooled (hCP : CPVerdict)
    (b pb : ByteArray) (s8 s64 : List Nat) (hin : InputsOK b pb s64)
    (N₁ : Nat) (hN₁ : N₁ < 2 ^ 62) (rs₁ : List Word) (m₁ : Mem)
    (h₁ : L.run checkerProg N₁ "check" [] (loadMemM b pb s8 s64 1) = .ok (rs₁, m₁))
    (hge : 9223372036854775808 ≤ (rs₁.headD 0).toNat)
    (B : Array Word) (hB : B = (m₁.arr64 OUT).extract 0 ((m₁.arr64 OUT).getD 1 0).toNat)
    (r₀ : Mem) (hr : 388 ≤ r₀.words.size) (hz : ∀ b ∈ parOwnedL, r₀.arr64 b = zeros (m₁.arr64 b).size)
    (hI : r₀.glob INIT = 0) (cs : List (Word × Nat × Mem)) (j : Word) (n : Nat) (e : Err)
    (hruns : ThreadFails B j n e r₀ cs)
    (hcs : ∀ c ∈ cs, c.1 < rs₁.headD 0 - 9223372036854775808)
    (hj : j < rs₁.headD 0 - 9223372036854775808) (hk0 : e.cls ≠ 0) :
    TwinVerdictPooled [b] e.cls := by
  have hr' : rs₁.headD 0 ≠ 1 := fun e => by rw [e] at hge; simp at hge
  obtain ⟨PA, m, v, hS, hPB, hpre, hok, hm₁, hres⟩ :=
    checkA_run b pb s8 s64 hin 1 (Or.inl rfl) N₁ hN₁ rs₁ m₁ h₁ hr'
  have hflag : modeFlag 1 = 1 := rfl
  rw [hflag] at hok hm₁
  have hrom : RomOK pb.data.toList := by simpa [RomOK] using hin.2.2.1
  have hT := twinFold_of_prefix PA.pfx
  have hdn : L.Ind.DnInj (dnOf PA.sE.store) := dnOf_inj hT.stateOK.wf
  have hQd : QuotDn (dnOf PA.sE.store) := by
    obtain ⟨k, hk, hd⟩ := prefix_quotU PA.pfx
    exact ⟨k, by simp [dnOf, hk, hd]⟩
  have hLC := checkerProg_loopCalleesPB pb.data.toList hrom hpre (dnOf PA.sE.store) hdn
    (indArmSpec_checker _ hrom hpre _ hdn) hQd
  have hTop := checkerProg_loopTopPB pb.data.toList
  have hPB' : PhaseBProg (Prog.subPB pb.data.toList checkerProg) :=
    ⟨hTop.bracket, hLC.cvg, hLC.knot, hLC.leaf, hLC.loop, hTop.pc, hTop.pcg, hTop.pcx,
      hLC.cd.crp.apd, ⟨hLC.indMemo, hLC.crf⟩⟩
  have hF := parCompactMem_out m v 1
  rw [← hm₁] at hF
  have hlt : (m.arr64 OUT).size < 2 ^ 64 := by
    rw [← hF.size OUT]; exact run_load_size hin.2.2.2 h₁ OUT
  have hBm : B = bufOf m v := by
    rw [hB, bufOf, hm₁, (parCompactMem_hdr hok).2.1]
  have hk : (rs₁.headD 0 - 9223372036854775808).toNat = PA.pend.size := by
    have hc := hS.loop.pend.count
    have hlt' : PA.pend.size < 2 ^ 64 := by rw [← hc]; exact UInt64.toNat_lt_size _
    have e : (9223372036854775808 : Word) + UInt64.ofNat PA.pend.size - 9223372036854775808 =
        UInt64.ofNat PA.pend.size := by rw [UInt64.add_comm, UInt64.add_sub_cancel]
    rw [hres, e, UInt64.toNat_ofNat_of_lt' (by simpa [UInt64.size] using hlt')]
  have hcs' : ∀ c ∈ cs, c.1.toNat < PA.pend.size := fun c hc => by
    have := hcs c hc; rw [UInt64.lt_iff_toNat_lt, hk] at this; exact this
  have hj' : j.toNat < PA.pend.size := by rw [UInt64.lt_iff_toNat_lt, hk] at hj; exact hj
  have hz' : ∀ b ∈ parOwnedL, r₀.arr64 b = zeros (m.arr64 b).size := fun b hb => by
    rw [hz b hb, hF.size]
  have hfail := thread_failsE .verified PA.ipins (dnOf PA.sE.store) PA.ds PA.fe PA.pend pb.data.toList
    hPB' rfl (hCP _ _ hrom hpre hdn hQd hPB' _ _ _ _) hS hPB hok hlt r₀ hr hz' hI j hj' n e hk0 cs
    (hBm ▸ hruns) hcs'
  have hsub : ∀ pc ∈ thrGroups PA.pend cs ++ [pdAt PA.pend j], pc ∈ PA.pend.toList := by
    intro pc hpc
    rcases List.mem_append.mp hpc with hpc | hpc
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hpc
      exact pdAt_mem PA.pend c.1 (hcs' c hc)
    · rw [List.mem_singleton.mp hpc]; exact pdAt_mem PA.pend j hj'
  obtain ⟨hA, hBp, hC, hD, hE⟩ := PA.pfx
  exact .inr ⟨PA.pins, PA.sA, PA.sB, PA.sC, PA.sD, PA.sE, PA.sF, PA.pre, PA.rc, PA.ds, PA.ipins, PA.k,
    PA.fe, PA.pend, _, hA, hBp, hC, hD, hE, PA.fold, hsub, hfail⟩

end L.Checker
