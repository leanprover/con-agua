module

public import ConAgua.Checker.ParThreadTwin
import ConAgua.Arena.FreezeFresh
import ConAgua.Checker.CheckARun
import ConAgua.Checker.NoVerdictClosed
import ConAgua.Checker.RomProgInit
import ConAgua.Checker.LoopStage
import ConAgua.L.Blocks
import ConAgua.Checker.LoopProgTac
meta import ConAgua.Checker.LoopProgTac
public import ConAgua.Final.TwinVerdict
import all ConAgua.Checker.Entry
import ConAgua.Front.FrontRunRef

@[expose] public section

/-!
# A thread's failing call is the twin pool's failure (lane verdicts-b, stage 3 of ronsync2)

The error halves of `ParThreadCall.lean` and `ParThreadTwin.lean`. A thread calls entry 2 once per
record it claims, on its own region (`ThreadRuns`); when call `j` fails with a class other than
`0` and every record below `j` was run, and accepted, by some thread's calls, the twin's worker,
from the index state's worker, running the thread's records in order up to and including `j`,
fails with that class (`checkJobList` reports it as a value).

* `CjStepE`, `cjStepE_of`: `check_jobs(j, j + 1)` failing from the jobs' relation (`JobRel`)
  claims record `j`'s list failure (`checkJobs_ref`'s error half, under `JobG`);
* `checkJobs_thrE`, `checkB_thrE`, `checkThrE`, `runThrE`: the same on a thread's memory
  (`ThrAt`), through `check_b` and `check`;
* `threads_twinVerdictPooled`: with entry 1's run, `TwinVerdictPooled [b]`: the threads' calls
  below `j` give con-ron's fold invariant at every view up to `j` (`pool_prefix`), so the failing
  thread's calls before the failing one ran ok (`runThr`), each from a worker state at a view
  where the invariant holds (`worker_foldOK`), and the failing call is the twin's failure
  (`runThrE`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Checker

open L L.Arena L.Rom ConRon.Bridge

local notation "VM" => ConLeche.CheckMode.verified

universe w

/-! ## Small pieces -/

/-- A failing run from agreeing states fails alike (`invoke_agree`). -/
theorem invoke_agree_err {p : Prog} {S : TieredArray → Bool} {S8 : ArrId → Bool} {fs : List FnName}
    (hp : readsIn p S S8 fs = true) {f : FnName} (hf : f ∈ fs) {n : Nat} {vs : List Word}
    {s₁ s₂ : St} (hm : Agree S S8 s₁.mem s₂.mem) (hl : s₁.loc = s₂.loc) {e : Err}
    (h : (invoke p (exec p n) f vs).run s₁ = .error e) :
    (invoke p (exec p n) f vs).run s₂ = .error e := by
  have := L.invoke_agree hp hf n vs hm hl
  rw [h] at this
  revert this
  cases (invoke p (exec p n) f vs).run s₂ with
  | ok r => intro h'; exact h'.elim
  | error e' => intro h'; cases h'; rfl

/-- `flush_caches` at the checker, error-precise: it fails only with class `0`. -/
theorem flushCaches_specNV (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "flush_caches" []
    ⦃fun _ s' => LocEq s' s₀ ∧ FlushOK s₀.mem ∧ s'.mem = flushMem s₀.mem; fun e => e.cls = 0⦄ := by
  have hm : "flush_caches" ∈ nvFns := nv_mem (by decide +kernel)
  have hS := flushCaches_spec checkerProg L.Checker.checkerProg_flushProg n s₀
  have hN := invoke_nv checkerProg checkerProg_nv n "flush_caches" hm []
  apply M.triple_of_run'
  · intro s r s' hp hr
    exact M.of_run' (P := fun s => s = s₀)
      (Q := fun _ s' => LocEq s' s₀ ∧ FlushOK s₀.mem ∧ s'.mem = flushMem s₀.mem) (E := ⊤) hp hr hS
  · intro s e _ hr
    exact M.of_run_err (P := fun _ => True) trivial hr hN

/-- A job accepted at the head of a list: the list's failure claim is the rest's, from the job's
state. -/
theorem ErrClaimV.cons_ok {pins : List INatOpPinSet} {I : IStreamIndex} {ds : Array IDeclaration} {J : Option ISolution}
    {t : Nat} (ht : t < ds.size) {rest : List Nat} {a a₁ : AState} {e : Err}
    (h : recordJob VM pins J I t ds[t] a = .ok ((), a₁))
    (hr : ErrClaimV (checkJobList VM pins J I ds rest) a₁ e) :
    ErrClaimV (checkJobList VM pins J I ds (t :: rest)) a e := fun hk => by
  have e1 : (checkJobList VM pins J I ds (t :: rest)).run a = (checkJobList VM pins J I ds rest).run a₁ :=
    checkJobList_cons_ok ht h
  unfold TwinFailsV; rw [e1]; exact hr hk

/-! ## `check_jobs(j, j + 1)` failing -/

section step
variable (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)
  (I : IStreamIndex) (a₀ : AState)

/-- **`check_jobs(j, j + 1)` failing claims record `j`'s failure**, from the jobs' relation (up to
the scratch entry) and con-ron's fold invariant at the record's view. -/
def CjStepE (p : Prog) (J : Option ISolution := none) : Prop :=
  ∀ (n : Nat) (m : Mem) (a : AState) (j : Word), n ≤ 2 ^ 62 → j.toNat < ds.size →
    JobRel pins dn ds J I a₀ m a → (∃ env, FoldOK env (I.view j.toNat) (AM.st enterScratch a)) →
    ∀ {e : Err}, callE p n "check_jobs" [j, j + 1] m = .error e →
    ErrClaimV (checkJobList VM pins J I ds [j.toNat]) a e

variable {pins dn ds I a₀} in
/-- `CjStepE` from the jobs' program facts and their error claims (`JobG`), by `checkJobs_ref`. -/
theorem cjStepE_of {pinsP : List ConLeche.NatOpPinSet} {p : Prog}
    (hP : JobProg pins dn ds p) (hFD : FrontDecls ds) (hLD : DeclsLpsDn dn ds) (hdn : DnPers dn)
    (hrec : RecordSpec pins pinsP) (hpp : PersPinSets pins) (hds : ds.size < 2 ^ 63)
    (hden : ∀ x ∈ ds.toList, PersDecl x ∧ ∃ d, Frontend.denoteDecl a₀.store x = some d)
    (hPD : PinsDenote a₀.store pins pinsP) (hG : JobG pins dn ds p) :
    CjStepE pins dn ds I a₀ p := by
  intro n m a j hn hj ⟨a₁, hJP, hS⟩ hF e hc
  rw [← hS.st] at hF
  have e1 : (j + 1).toNat = j.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  have h := checkJobs_ref (J := none) (I := I) hP hFD hLD hdn hpp hden hPD hrec (fun h => absurd h (by simp)) (hi := j + 1) (j := j) (by rw [e1]; omega) hn hJP
    (fun t a' h1 h2 h3 => by
      obtain rfl : t = j.toNat := by omega
      rw [Nat.sub_self, List.range'_zero] at h3
      cases h3
      exact hF)
  have h' := RefC.run_err (checkJobs_specE p hP.check_jobs n ⟨m, Locals.init []⟩ j (j + 1))
    (fun e h0 => ErrClaimV.of_cls0 h0) trivial (JobGJ.none hG) h hc
  rw [e1, Nat.add_sub_cancel_left, List.range'_one] at h'
  exact fun hk => twinFailsV_of_sameEnter hS (h' hk)

end step

/-! ## On a thread's memory -/

section thread
variable {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration}
  {I : IStreamIndex} {a₀ : AState} {bs : List UInt8} {J : Option ISolution}

/-- **`check_jobs(j, j + 1)` on a thread's memory, after the flush, error half of
`checkJobs_thrT`.** -/
theorem checkJobs_thrE (hE : CjStepE pins dn ds I a₀ (Prog.subPB bs checkerProg) J)
    (n : Nat) (hn : n ≤ 2 ^ 62) (a : AState) (j : Word) (hj : j.toNat < ds.size)
    (hF : ∃ env, FoldOK env (I.view j.toNat) (AM.st enterScratch a)) (x y : Word) :
    ⦃fun s => x = j ∧ y = j + 1 ∧ ∃ Y, FlushOK Y ∧ s.mem = flushMem Y ∧
      ThrAt pins dn ds I a₀ bs Y a J⦄
    invoke checkerProg (exec checkerProg n) "check_jobs" [x, y]
    ⦃fun _ _ => True; ErrClaimV (checkJobList VM pins J I ds [j.toNat]) a⦄ := by
  apply M.triple_of_run' (fun _ _ _ _ _ => trivial)
  rintro s e ⟨hxj, hyj, Y, hfy, hsY, X, hJ, hPB, hYX⟩ hrun
  rw [hxj, hyj] at hrun
  have hc : thrS CTL = true := by decide
  let X₂ : Mem := ⟨X.bytes, X.words, Y.glob⟩
  have hAg0 : Agree thrS (fun _ => false) Y X₂ :=
    ⟨fun t ht => hYX t ht, fun _ h => absurd h (by simp), rfl⟩
  have hfx : FlushOK X := by
    rw [flushOK_eq] at hfy ⊢
    exact clearsOK_words _ (m₁ := X₂) (m₂ := X) rfl (clearsOK_agree hc _ hAg0 hfy)
  obtain ⟨a₁, ⟨hJR, hx, hp⟩, hSE⟩ := hJ
  have hA2 := flushMem_agree hAg0 hc
  have hw2 : (flushMem X₂).words = (flushMem X).words := flushMem_words rfl
  let s₂ : St := ⟨⟨(flushMem X).bytes, (flushMem X).words, s.mem.glob⟩, s.loc⟩
  have hAg : Agree thrS (fun _ => false) s.mem s₂.mem :=
    ⟨fun t ht => by
      rw [hsY, hA2.1 t ht]; show (flushMem X₂).words t = (flushMem X).words t; rw [hw2],
     fun _ h => absurd h (by simp), rfl⟩
  have hrun₂ := invoke_agree_err checkerProg_thrReads check_jobs_mem_phaseBJobFns hAg rfl hrun
  have hPB₂ : s₂.mem.arr8 L.Rom.PB = bs.toArray := by
    show (flushMem X).bytes L.Rom.PB = _
    rw [flushMem_bytes]; exact hPB
  rw [← L.Rom.invoke_subPB (bs := bs) checkerProg_noSt8PB n _ _ (s := s₂) hPB₂] at hrun₂
  have hJ2 : JobRel pins dn ds J I a₀ s₂.mem a := ⟨a₁, ⟨(hJR.flush hfx).setGlob _, hx, hp⟩, hSE⟩
  exact hE n s₂.mem a j hn hj hJ2 hF (L.Front.callE_of_run_err hrun₂)

theorem seedReread_specNV (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "seed_reread" []
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = rereadMem s₀.mem ∧ r = [0]; fun e => e.cls = 0⦄ := by
  have hm : "seed_reread" ∈ nvFns := nv_mem (by decide +kernel)
  have hS := seedReread_spec checkerProg (by chk_lk) n s₀
  have hN := invoke_nv checkerProg checkerProg_nv n "seed_reread" hm []
  apply M.triple_of_run'
  · intro s r s' hp hr
    exact M.of_run' (P := fun s => s = s₀)
      (Q := fun r s' => LocEq s' s₀ ∧ s'.mem = rereadMem s₀.mem ∧ r = [0]) (E := ⊤) hp hr hS
  · intro s e _ hr
    exact M.of_run_err (P := fun _ => True) trivial hr hN

/-- **`check_b` on a thread's memory, error half of `checkB_thr`.** -/
theorem checkB_thrE (hE : CjStepE pins dn ds I a₀ (Prog.subPB bs checkerProg) J)
    (n : Nat) (hn : n ≤ 2 ^ 62) (a : AState) (j : Word) (hj : j.toNat < ds.size)
    (hF : ∃ env, FoldOK env (I.view j.toNat) (AM.st enterScratch a)) (s₀ : St)
    (hR : ThrAt pins dn ds I a₀ bs (seedMem s₀.mem) a J)
    (hlo : s₀.mem.glob PLO = j) (hhi : s₀.mem.glob PHI = j + 1) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "check_b" []
    ⦃fun _ _ => True; ErrClaimV (checkJobList VM pins J I ds [j.toNat]) a⦄ := by
  have hlo' : s₀.mem.glob ⟨9⟩ = j := hlo
  have hhi' : s₀.mem.glob ⟨11⟩ = j + 1 := hhi
  have hR0 : s₀.mem.glob ⟨10⟩ = 0 → ThrAt (J := J) pins dn ds I a₀ bs (rereadMem
      { bytes := (s₀.mem.copy64 CTL 0 CTLF 0 (UInt64.toNat (s₀.mem.len64 CTLF))).bytes,
        words := (s₀.mem.copy64 CTL 0 CTLF 0 (UInt64.toNat (s₀.mem.len64 CTLF))).words,
        glob := fun h => if h = ⟨10⟩ then 1
          else (s₀.mem.copy64 CTL 0 CTLF 0 (UInt64.toNat (s₀.mem.len64 CTLF))).glob h }) a := by
    intro h0; have := hR; simp only [seedMem, ite_eq_left h0] at this; exact this
  have hR1 : ¬ s₀.mem.glob ⟨10⟩ = 0 → ThrAt pins dn ds I a₀ bs (rereadMem s₀.mem) a J := by
    intro h0; have := hR; simp only [seedMem, ite_eq_right h0] at this; exact this
  rw [invoke_eq _ checkerProg_lookup_check_b]
  simp only [callFn, checkBL]
  cases n with
  | zero => vcgen [exec] <;> simp [ErrClaimV.of_cls0]
  | succ n =>
    have hJ := checkJobs_thrE hE n (by omega) a j hj hF
    have hFl := flushCaches_specNV n
    have hRR := seedReread_specNV n
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, setG, ld64, warr, (hJ · ·), (hFl ·), (hRR ·)]
    all_goals (try simp only [L.St.setLoc_mem, St.setLoc_loc,
      L.Locals.init_nil, Cmp.eval,
      reduceIte, beq_iff_eq, decide_eq_true_eq] at *)
    all_goals (try simp only [St.setG, Mem.setG, St.setLoc] at *)
    all_goals first
      | exact ErrClaimV.of_cls0 (by decide)
      | exact ErrClaimV.of_cls0 ‹_›
      | (simp_all (config := { decide := true }) [Mem.arr64]; done)
      | skip
    all_goals first
      | (obtain ⟨-, hfx, hm⟩ := ‹LocEq _ _ ∧ FlushOK _ ∧ _›
         first
          | exact ⟨_, hfx, by rw [L.St.setLocs_mem]; exact hm, hR0 (by simp_all)⟩
          | exact ⟨_, hfx, by rw [L.St.setLocs_mem]; exact hm, hR1 (by simp_all)⟩
          | (rw [L.St.setLocs_mem, hm, flushMem_glob]; simp_all; done)
          | (rw [L.St.setLocs_mem, hm, flushMem_glob]; simp only [Mem.copy64_glob, rereadMem_glob] at *; simp_all; done)
          | exact ⟨_, hfx, by rw [L.St.setLocs_mem]; exact hm,
              by rw [L.St.setLocs_mem, ‹St.mem _ = rereadMem _›]; exact hR0 (by simp_all)⟩
          | exact ⟨_, hfx, by rw [L.St.setLocs_mem]; exact hm,
              by rw [L.St.setLocs_mem, ‹St.mem _ = rereadMem _›]; exact hR1 (by simp_all)⟩
          | (simp only [flushMem_glob, rereadMem_glob, Mem.copy64_glob] at *; simp_all; done)
          | (rw [L.St.setLocs_mem, hm, flushMem_glob, L.St.setLocs_mem, ‹St.mem _ = rereadMem _›,
              rereadMem_glob]; simp_all; done))
      | (rw [L.St.setLocs_mem]; simp_all; done)
      | (rw [L.St.setLocs_mem]; simp_all [flushMem_glob, rereadMem_glob, Mem.copy64_glob]; done)
      | (trace_state; fail "ThreadsE.checkB_thrE: no closing tactic applies")

/-- **`check` with the mode word `2` on a thread's memory, error half of `checkThr`.** -/
theorem checkThrE (hE : CjStepE pins dn ds I a₀ (Prog.subPB bs checkerProg) J)
    (n : Nat) (hn : n ≤ 2 ^ 62) (a : AState) (j : Word) (hj : j.toNat < ds.size)
    (hF : ∃ env, FoldOK env (I.view j.toNat) (AM.st enterScratch a)) (s₀ : St)
    (hmode : s₀.mem.glob MODE = 2) (hR : ThrAt pins dn ds I a₀ bs (seedMem s₀.mem) a J)
    (hlo : s₀.mem.glob PLO = j) (hhi : s₀.mem.glob PHI = j + 1) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "check" []
    ⦃fun _ _ => True; ErrClaimV (checkJobList VM pins J I ds [j.toNat]) a⦄ := by
  rw [invoke_eq _ checkerProg_lookup_check']
  simp only [callFn, checkL]
  cases n with
  | zero => vcgen [exec] <;> simp [ErrClaimV.of_cls0]
  | succ n =>
    have hB : ⦃fun s => s.mem = s₀.mem⦄ invoke checkerProg (exec checkerProg n) "check_b" []
        ⦃fun _ _ => True; ErrClaimV (checkJobList VM pins J I ds [j.toNat]) a⦄ := by
      apply M.triple_of_run' (fun _ _ _ _ _ => trivial)
      intro s₁ e hs hrun
      exact M.of_run_err (P := fun x => x = s₁) rfl hrun
        (checkB_thrE hE n (by omega) a j hj hF s₁ (hs ▸ hR) (hs ▸ hlo) (hs ▸ hhi))
    have hmode' : s₀.mem.glob ⟨8⟩ = 2 := hmode
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, hB,
      (callE_spec checkerProg n "check_a" [1] ·), (callE_spec checkerProg n "check_a" [0] ·),
      (callE_spec checkerProg n "check_bs" [] ·), (callE_spec checkerProg n "check_bc" [] ·),
      (callE_spec checkerProg n "check_c1" [] ·), (callE_spec checkerProg n "check_c2" [] ·),
      (callE_spec checkerProg n "check_c3" [·] ·)]
    all_goals (try simp only [Cmp.eval, beq_iff_eq] at *)
    all_goals first
      | exact ErrClaimV.of_cls0 (by decide)
      | (simp_all (config := { decide := true }); done)
      | (simp_all [St.setLoc]; done)
      | (trace_state; fail "ThreadsE.checkThrE: no closing tactic applies")

/-- **One call, as a run, error half of `runThr`.** -/
theorem runThrE (hE : CjStepE pins dn ds I a₀ (Prog.subPB bs checkerProg) J)
    (n : Nat) (hn : n ≤ 2 ^ 62) (a : AState) (j : Word) (hj : j.toNat < ds.size)
    (hF : ∃ env, FoldOK env (I.view j.toNat) (AM.st enterScratch a)) (w : Mem)
    (hmode : w.glob MODE = 2) (hR : ThrAt pins dn ds I a₀ bs (seedMem w) a J)
    (hlo : w.glob PLO = j) (hhi : w.glob PHI = j + 1) {e : Err}
    (hrun : L.run checkerProg n "check" [] w = .error e) :
    ErrClaimV (checkJobList VM pins J I ds [j.toNat]) a e := by
  simp only [L.run] at hrun
  cases hq : (invoke checkerProg (exec checkerProg n) "check" []).run ⟨w, Locals.init []⟩ with
  | ok x => rw [hq] at hrun; cases hrun
  | error e' =>
    rw [hq] at hrun
    simp only [Except.map, Except.error.injEq] at hrun
    subst hrun
    exact M.of_run_err (P := fun x => x = ⟨w, Locals.init []⟩) rfl hq
      (checkThrE hE n hn a j hj hF ⟨w, Locals.init []⟩ hmode hR hlo hhi)

end thread

/-! ## A thread's calls, the last one failing -/

/-- **A thread's calls ending in a failure**: the calls `cs` from the region memory `r` ran as
`ThreadRuns` says, and the next call, on record `j` with fuel `n ≤ 2^62`, on `bufMem B r' j` (`r'`
the last call's final memory, `r` if there was none), failed with `e`. -/
def ThreadFails (B : Array Word) (j : Word) (n : Nat) (e : Err) : Mem → List (Word × Nat × Mem) → Prop
  | r, [] => n ≤ 2 ^ 62 ∧ L.run checkerProg n "check" [] (bufMem B r j) = .error e
  | r, (j', n', r') :: cs => n' ≤ 2 ^ 62 ∧
      (∃ rs, L.run checkerProg n' "check" [] (bufMem B r j') = .ok (rs, r')) ∧ BufKept B r' ∧
      ThreadFails B j n e r' cs

/-! ## With entry 1 -/

open ConAgua.Final in
/-- **A thread's failing call is the twin pool's failure.** Entry 1 (`check` with the mode word
`1`, from the loaded memory) returning `2^63 + k`; the buffer `B` (the first `len` words of `OUT`,
`len` the header's word `1`); a thread with a fresh region memory `r₀` (as in
`threads_twinAcceptsPooled`) whose calls `cs`, each on a record below `j`, ran and whose next call,
on record `j < k`, failed with an error `e` of class other than `0` (`ThreadFails`); and threads
`ths` (each a fresh region memory with its calls, as in `threads_twinAcceptsPooled`, every claim
below `k`, each thread's claims increasing) whose calls ran every record below `j`. Then the twin's
pool fails with that class (`TwinVerdictPooled`), given `check_decl`'s program facts (`CheckerCd`)
and the jobs' error claims (`JobG`) at every phase A. -/
theorem threads_twinVerdictPooled (hCd : CheckerCd)
    (hJG : ∀ (b pb : ByteArray) (PA : PhaseA b), pb.size < 2 ^ 63 → PbPre pb →
      JobG PA.ipins (dnOf PA.sE.store) PA.ds (Prog.subPB pb.data.toList checkerProg))
    (b pb : ByteArray) (sz : TieredArray → Nat) (hin : InputsOK b pb sz)
    (N₁ : Nat) (hN₁ : N₁ < 2 ^ 62) (rs₁ : List Word) (m₁ : Mem)
    (h₁ : L.run checkerProg N₁ "check" [] (loadMemM b pb sz 1) = .ok (rs₁, m₁))
    (hge : 9223372036854775808 ≤ (rs₁.headD 0).toNat)
    (B : Array Word) (hB : B = (m₁.arr64 OUT).extract 0 ((m₁.arr64 OUT).getD 1 0).toNat)
    (r₀ : Mem) (hz : ∀ b ∈ parOwnedL, r₀.arr64 b = zeros (m₁.arr64 b).size)
    (hI : r₀.glob INIT = 0) (j : Word) (cs : List (Word × Nat × Mem)) (n : Nat) (e : Err)
    (hruns : ThreadFails B j n e r₀ cs) (hcs : ∀ c ∈ cs, c.1 < j)
    (hj : j < rs₁.headD 0 - 9223372036854775808) (hk0 : e.cls ≠ 0)
    (ths : List (Mem × List (Word × Nat × Mem)))
    (hth : ∀ t ∈ ths, (∀ b ∈ parOwnedL, t.1.arr64 b = zeros (m₁.arr64 b).size) ∧
      t.1.glob INIT = 0 ∧ ThreadRuns B t.1 t.2 ∧ ∀ c ∈ t.2, c.1 < rs₁.headD 0 - 9223372036854775808)
    (hinc : ∀ t ∈ ths, (t.2.map (·.1)).Pairwise (· < ·))
    (hbelow : ∀ i : Word, i < j → ∃ t ∈ ths, ∃ c ∈ t.2, c.1 = i) :
    TwinVerdictPooled [b] e.cls := by
  have hr : rs₁.headD 0 ≠ 1 := fun e => by rw [e] at hge; simp at hge
  obtain ⟨PA, m₇, m, hF, hok, hm₁, hres⟩ := checkA_run b pb sz hin 1 (Or.inl rfl) N₁ hN₁ rs₁ m₁ h₁ hr
  have hflag : modeFlag 1 = 1 := rfl
  rw [hflag] at hok hm₁
  have hpb := hin.2.2.1
  have hJP := jobProg_of_cd hCd PA hpb hF.r7.since.pbpre
  have hJG' := hJG b pb PA hpb hF.r7.since.pbpre
  let bs := pb.data.toList
  let p := Prog.subPB bs checkerProg
  -- the buffer and the sizes
  have hO := parCompactMem_out m 1
  rw [← hm₁] at hO
  have hlt : (m.arr64 OUT).size < 2 ^ 64 := by
    rw [← hO.size OUT]; exact run_load_size hin.2.2.2 h₁ OUT
  have hBm : B = bufOf m := by
    rw [hB, bufOf, hm₁, (parCompactMem_hdr hok).2.1]
  have hsz : PA.ds.size < 2 ^ 63 := by
    have := hF.build.decls.room; have := hF.build.decls.dsize; omega
  have hk : (rs₁.headD 0 - 9223372036854775808).toNat = PA.ds.size := by
    have e : (9223372036854775808 : Word) + UInt64.ofNat PA.ds.size - 9223372036854775808 =
        UInt64.ofNat PA.ds.size := by rw [UInt64.add_comm, UInt64.add_sub_cancel]
    rw [hres, e, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
  have hjN : j.toNat < PA.ds.size := by rw [← hk]; exact UInt64.lt_iff_toNat_lt.mp hj
  have hcN : ∀ c ∈ cs, c.1.toNat < PA.ds.size := fun c hc => by
    have := UInt64.lt_iff_toNat_lt.mp (hcs c hc); omega
  -- the twin's side
  let a₀ : AState := { PA.sF with caches := Caches.empty }
  let Rel : Mem → AState → Prop := fun r a =>
    ∀ j, ThrAt PA.ipins (dnOf PA.sE.store) PA.ds PA.I a₀ bs (seedMem (bufMem B r j)) a
  let Call : Nat → Mem → Mem → Prop := fun k r r' => ∃ n rs, n ≤ 2 ^ 62 ∧
    L.run checkerProg n "check" [] (bufMem B r (UInt64.ofNat k)) = .ok (rs, r') ∧ BufKept B r'
  obtain ⟨pinsP, dsP, hst, hrec, hpp, hden, hPD, hH⟩ := poolHyps_of_phaseA PA Rel Call
  obtain ⟨hA, hBp, hC, hD, hE⟩ := PA.pfx
  obtain ⟨-, -, -, -, -, hpd, _rc, _preC, -, hden0⟩ :=
    ConRon.Bridge.stages_frame (chunks := [b]) hA hBp hC hD hE
  have hFD : FrontDecls PA.ds := frontDecls_of_prefix PA.pfx
  have hLD : DeclsLpsDn (dnOf PA.sE.store) PA.ds := declsLpsDn_dnOf hpd ⟨_, hden0⟩
  have hdn : DnPers (dnOf PA.sE.store) := fun k x hk => by
    simp only [dnOf] at hk; split at hk
    · assumption
    · cases hk
  have hRS : RecStep PA.ipins (dnOf PA.sE.store) PA.ds PA.I a₀ p :=
    recCall_stepE (J := none) hJP hFD hLD hdn hpp (by omega) hden hPD hrec (fun h => absurd h (by simp))
  have hCE : CjStepE PA.ipins (dnOf PA.sE.store) PA.ds PA.I a₀ p :=
    cjStepE_of hJP hFD hLD hdn hrec hpp hsz hden hPD hJG'
  have hstep : ∀ (k : Nat) (r r' : Mem) (a : AState) (hk : k < PA.ds.size), Rel r a → Call k r r' →
      (∃ env, FoldOK env (PA.I.view k) (AM.st enterScratch a)) →
      ∃ a', recordJob .verified PA.ipins none PA.I k PA.ds[k] a = .ok ((), a') ∧ Rel r' a' := by
    intro k r r' a hk hR ⟨n, rs, hn, hrun, hkept⟩ hfo
    have hk' : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
    obtain ⟨⟨a', hrj, X, hJ, hPB, hX⟩, hI⟩ := runThr hJP.check_jobs hRS hsz n hn a (UInt64.ofNat k)
      (by rw [hk']; exact hk) (by rw [hk']; exact hfo) _ rfl (hR _) rfl rfl hrun
    refine ⟨a', ?_, fun j => ⟨X, hJ, hPB, fun t ht => (thr_next B j hI hkept (thr_ctl_next hrun) t ht).trans (hX t ht)⟩⟩
    have e : PA.ds[(UInt64.ofNat k).toNat]'(by rw [hk']; exact hk) = PA.ds[k] := by simp only [hk']
    rw [← e]; simp only [hk'] at hrj ⊢; exact hrj
  have H := hH hstep
  -- the threads' runs below `j`: the fold's prefixes up to `j`
  have hstart : ∀ r : Mem, (∀ b ∈ parOwnedL, r.arr64 b = zeros (m₁.arr64 b).size) → r.glob INIT = 0 →
      Rel r PA.sF.worker := by
    intro r hz hI j
    have hoff := hF.build.off
    have hw := hF.build.drv.state.wf
    have hKI := indexKeysIn_of hF.jobM.arena.base H.hI H.hpI
    have hJR := JobM.fresh (hF.jobM.trunc hoff hKI) hw hoff
    refine ⟨freshMem m, ⟨_, ⟨hJR, PExt.of_ext (Ext.refl _), rfl⟩, ?_⟩, ?_, ?_⟩
    · exact ⟨by simp [AState.worker, enableScratch_dropScratch], rfl, rfl⟩
    · rw [freshMem_arr8]
      show m.bytes L.Rom.PB = _
      rw [hF.bytes, ← Mem.arr8, hF.r7.since.keep.arr8]; exact loadMem_pb b pb sz
    · rw [hBm]
      exact thr_first hok hlt r j (fun b hb => by rw [hz b hb, hO.size]) hI
  let ths' : List (Mem × List Nat) := ths.map fun t => (t.1, t.2.map (·.1.toNat))
  have hinc' : ∀ t ∈ ths', t.2.Pairwise (· < ·) := by
    intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
    have := hinc t₀ ht₀
    rw [List.pairwise_map] at this ⊢
    exact this.imp fun h => UInt64.lt_iff_toNat_lt.mp h
  have hpre := pool_prefix H hst ths'
    (fun t ht => by
      obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
      exact hstart t₀.1 (hth t₀ ht₀).1 (hth t₀ ht₀).2.1)
    (fun t ht => by
      obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
      exact threadRuns_chain B _ _ (hth t₀ ht₀).2.2.1)
    hinc' j.toNat (by omega) (fun i hi => by
      have hi64 : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
      obtain ⟨t, ht, c, hc, hci⟩ := hbelow (UInt64.ofNat i) (by rw [UInt64.lt_iff_toNat_lt, hi64]; exact hi)
      exact ⟨_, List.mem_map_of_mem ht, List.mem_map.mpr ⟨c, hc, by rw [hci, hi64]⟩⟩)
  have hfold : ∀ x a, x < PA.ds.size → x ≤ j.toNat → WorkerOK PA.sF a →
      ∃ env, FoldOK env (PA.I.view x) (AM.st enterScratch a) := fun x a hx hxj hw => by
    obtain ⟨hP, hnd⟩ := hpre x hxj
    obtain ⟨hx', -⟩ := H.hden x hx
    exact worker_foldOK H.hpinsOK H.hpersPins H.hI H.hpI hx' hP hnd hw
  -- the thread's walk
  have walk : ∀ (cs : List (Word × Nat × Mem)) (r : Mem) (a : AState), Rel r a → WorkerOK PA.sF a →
      ThreadFails B j n e r cs →
      (∀ c ∈ cs, c.1 < j) →
      ErrClaimV (checkJobList VM PA.ipins none PA.I PA.ds (cs.map (·.1.toNat) ++ [j.toNat])) a e := by
    intro cs
    induction cs with
    | nil =>
      intro r a hR hw ⟨hn, hrun⟩ _
      exact runThrE hCE n hn a j hjN (hfold _ a hjN (Nat.le_refl _) hw) _ rfl (hR j) rfl rfl hrun
    | cons c cs ih =>
      intro r a hR hw h hc
      obtain ⟨j', n', r'⟩ := c
      obtain ⟨hn', ⟨rs, hrun⟩, hkept, hrest⟩ := h
      have hjj : j'.toNat < j.toNat := UInt64.lt_iff_toNat_lt.mp (hc _ List.mem_cons_self)
      have hj' : j'.toNat < PA.ds.size := by omega
      obtain ⟨⟨a', hrj, X, hJ, hPB, hX⟩, hI'⟩ := runThr hJP.check_jobs hRS hsz n' hn' a j' hj'
        (hfold _ a hj' (by omega) hw) _ rfl (hR _) rfl rfl hrun
      have hR' : Rel r' a' := fun j => ⟨X, hJ, hPB, fun t ht => (thr_next B j hI' hkept (thr_ctl_next hrun) t ht).trans (hX t ht)⟩
      obtain ⟨hP, hnd⟩ := hpre j'.toNat (by omega)
      obtain ⟨hx', hdk⟩ := H.hden _ hj'
      obtain ⟨hw', -⟩ := job_spec H.hrec H.hpp H.hpinsOK H.hpersPins H.hpins H.hpd H.hI
        H.hpI hw hj' hx' hdk hP.envWF hnd hrj
      exact ErrClaimV.cons_ok hj' hrj
        (ih r' a' hR' hw' hrest fun c hc' => hc c (List.mem_cons_of_mem _ hc'))
  have hW := walk cs r₀ PA.sF.worker (hstart r₀ hz hI) (WorkerOK.start hst) hruns hcs
  refine .inr ⟨PA.pins, PA.sA, PA.sB, PA.sC, PA.sD, PA.sE, PA.sF, PA.pre, PA.rc, PA.ds, PA.ipins,
    PA.I, cs.map (·.1.toNat) ++ [j.toNat], hA, hBp, hC, hD, hE, PA.idx, fun t ht => ?_, hW hk0⟩
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
    exact hcN c hc
  · rw [List.mem_singleton.mp ht]; exact hjN

end L.Checker
