module

public import ConAgua.Checker.ParThreadTwin
import ConAgua.Arena.FreezeFresh
import ConAgua.Checker.CheckARun
import ConAgua.Checker.NoVerdictClosed
import ConAgua.Checker.NoVerdictTree
import ConAgua.Checker.RomProgInit
import ConAgua.Checker.IndArm
import ConAgua.Checker.LoopProg
import ConAgua.Checker.LoopStage
import ConAgua.Checker.TwinShapeQuot
import ConAgua.Checker.RomProg0
import ConAgua.L.Blocks
public import ConAgua.Final.TwinVerdict
import all ConAgua.Checker.Entry

@[expose] public section

/-!
# A thread's failing call is the twin pool's failure (lane verdicts-b, stage 3 of ronsync2)

The error halves of `ParThreadCall.lean` and `ParThreadTwin.lean`. A thread calls entry 2 once per
record it claims, on its own region (`ThreadRuns`); when call `j` fails with a class other than
`0`, the twin's worker, from the index state's worker, running the thread's records in order up to
and including `j`, fails with that class (`checkJobList` reports it as a value), unless some
record below one of them does not pass on its own (the weakened `TwinVerdictPooled`).

* `CjStepE`, `cjStepE_of`: `check_jobs(j, j + 1)` failing from the jobs' relation (`JobRel`)
  claims record `j`'s list failure (`checkJobs_ref`'s error half, under `JobG`);
* `checkJobs_thrE`, `checkB_thrE`, `checkThrE`, `runThrE`: the same on a thread's memory
  (`ThrAt`), through `check_b` and `check`;
* `threads_twinVerdictPooled`: with entry 1's run, `TwinVerdictPooled [b]`: the thread's calls
  before the failing one ran ok (`runThr`), each from a worker state at a view where con-ron's fold
  invariant holds (`worker_foldOK`, the records below passing: `prefixOK_of_passes`).
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
  have := invoke_agree hp hf n vs hm hl
  rw [h] at this
  revert this
  cases (invoke p (exec p n) f vs).run s₂ with
  | ok r => intro h'; exact h'.elim
  | error e' => intro h'; cases h'; rfl

/-- A failing run is a failing `callE`. -/
theorem callE_of_run_err {p : Prog} {n : Nat} {f : FnName} {vs : List Word} {s : St} {e : Err}
    (h : (invoke p (exec p n) f vs).run s = .error e) : callE p n f vs s.mem = .error e := by
  rw [invoke_run_loc'] at h
  simp only [callE]
  revert h
  cases (invoke p (exec p n) f vs).run ⟨s.mem, Locals.init []⟩ with
  | ok q => intro h; simp [Except.map] at h
  | error e' => intro h; simp only [Except.map, Except.error.injEq] at h; rw [h]

/-- `flush_caches` at the checker, error-precise: it fails only with class `0`. -/
theorem flushCaches_specNV (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "flush_caches" []
    ⦃fun _ s' => LocEq s' s₀ ∧ FlushOK s₀.mem ∧ s'.mem = flushMem s₀.mem; fun e => e.cls = 0⦄ := by
  have hm : "flush_caches" ∈ nvFns := nv_mem (by decide +kernel)
  have hS := flushCaches_spec checkerProg checkerProg_flushProg' n s₀
  have hN := invoke_nv checkerProg checkerProg_nv n "flush_caches" hm []
  apply M.triple_of_run'
  · intro s r s' hp hr
    exact M.of_run' (P := fun s => s = s₀)
      (Q := fun _ s' => LocEq s' s₀ ∧ FlushOK s₀.mem ∧ s'.mem = flushMem s₀.mem) (E := ⊤) hp hr hS
  · intro s e _ hr
    exact M.of_run_err (P := fun _ => True) trivial hr hN

/-- A job accepted at the head of a list: the list's failure claim is the rest's, from the job's
state. -/
theorem ErrClaimV.cons_ok {pins : List INatOpPinSet} {I : IStreamIndex} {ds : Array IDeclaration}
    {t : Nat} (ht : t < ds.size) {rest : List Nat} {a a₁ : AState} {e : Err}
    (h : recordJob VM pins I t ds[t] a = .ok ((), a₁))
    (hr : ErrClaimV (checkJobList VM pins I ds rest) a₁ e) :
    ErrClaimV (checkJobList VM pins I ds (t :: rest)) a e := fun hk => by
  have e1 : (checkJobList VM pins I ds (t :: rest)).run a = (checkJobList VM pins I ds rest).run a₁ :=
    checkJobList_cons_ok ht h
  unfold TwinFailsV; rw [e1]; exact hr hk

/-! ## `check_jobs(j, j + 1)` failing -/

section step
variable (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)
  (I : IStreamIndex) (a₀ : AState)

/-- **`check_jobs(j, j + 1)` failing claims record `j`'s failure**, from the jobs' relation (up to
the scratch entry) and con-ron's fold invariant at the record's view. -/
def CjStepE (p : Prog) : Prop :=
  ∀ (n : Nat) (m : Mem) (a : AState) (j : Word), n ≤ 2 ^ 62 → j.toNat < ds.size →
    JobRel pins dn ds I a₀ m a → (∃ env, FoldOK env (I.view j.toNat) (AM.st enterScratch a)) →
    ∀ {e : Err}, callE p n "check_jobs" [j, j + 1] m = .error e →
    ErrClaimV (checkJobList VM pins I ds [j.toNat]) a e

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
  have h := checkJobs_ref (I := I) hP hFD hLD hdn hrec hpp hden hPD (hi := j + 1) (j := j) (by rw [e1]; omega) hn hJP
    (fun t a' h1 h2 h3 => by
      obtain rfl : t = j.toNat := by omega
      rw [Nat.sub_self, List.range'_zero] at h3
      cases h3
      exact hF)
  have h' := RefC.run_err (checkJobs_specE p hP.check_jobs n ⟨m, Locals.init []⟩ j (j + 1))
    (fun e h0 => ErrClaimV.of_cls0 h0) trivial hG h hc
  rw [e1, Nat.add_sub_cancel_left, List.range'_one] at h'
  exact fun hk => twinFailsV_of_sameEnter hS (h' hk)

end step

/-! ## On a thread's memory -/

section thread
variable {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration}
  {I : IStreamIndex} {a₀ : AState} {bs : List UInt8}

/-- **`check_jobs(j, j + 1)` on a thread's memory, after the flush, error half of
`checkJobs_thrT`.** -/
theorem checkJobs_thrE (hE : CjStepE pins dn ds I a₀ (Prog.subPB bs checkerProg))
    (n : Nat) (hn : n ≤ 2 ^ 62) (a : AState) (j : Word) (hj : j.toNat < ds.size)
    (hF : ∃ env, FoldOK env (I.view j.toNat) (AM.st enterScratch a)) (x y : Word) :
    ⦃fun s => x = j ∧ y = j + 1 ∧ ∃ Y, FlushOK Y ∧ s.mem = flushMem Y ∧
      ThrAt pins dn ds I a₀ bs Y a⦄
    invoke checkerProg (exec checkerProg n) "check_jobs" [x, y]
    ⦃fun _ _ => True; ErrClaimV (checkJobList VM pins I ds [j.toNat]) a⦄ := by
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
  have hJ2 : JobRel pins dn ds I a₀ s₂.mem a := ⟨a₁, ⟨(hJR.flush hfx).setGlob _, hx, hp⟩, hSE⟩
  exact hE n s₂.mem a j hn hj hJ2 hF (callE_of_run_err hrun₂)

/-- **`check_b` on a thread's memory, error half of `checkB_thr`.** -/
theorem checkB_thrE (hE : CjStepE pins dn ds I a₀ (Prog.subPB bs checkerProg))
    (n : Nat) (hn : n ≤ 2 ^ 62) (a : AState) (j : Word) (hj : j.toNat < ds.size)
    (hF : ∃ env, FoldOK env (I.view j.toNat) (AM.st enterScratch a)) (s₀ : St)
    (hR : ThrAt pins dn ds I a₀ bs (seedMem s₀.mem) a)
    (hlo : s₀.mem.glob PLO = j) (hhi : s₀.mem.glob PHI = j + 1) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "check_b" []
    ⦃fun _ _ => True; ErrClaimV (checkJobList VM pins I ds [j.toNat]) a⦄ := by
  have hlo' : s₀.mem.glob ⟨9⟩ = j := hlo
  have hhi' : s₀.mem.glob ⟨11⟩ = j + 1 := hhi
  have hR0 : s₀.mem.glob ⟨10⟩ = 0 → ThrAt pins dn ds I a₀ bs
      { bytes := (s₀.mem.copy64 CTL 0 CTLF 0 (UInt64.toNat (s₀.mem.len64 CTLF))).bytes,
        words := (s₀.mem.copy64 CTL 0 CTLF 0 (UInt64.toNat (s₀.mem.len64 CTLF))).words,
        glob := fun h => if h = ⟨10⟩ then 1
          else (s₀.mem.copy64 CTL 0 CTLF 0 (UInt64.toNat (s₀.mem.len64 CTLF))).glob h } a := by
    intro h0; have := hR; simp only [seedMem, ite_eq_left h0] at this; exact this
  have hR1 : ¬ s₀.mem.glob ⟨10⟩ = 0 → ThrAt pins dn ds I a₀ bs s₀.mem a := by
    intro h0; have := hR; simp only [seedMem, ite_eq_right h0] at this; exact this
  rw [invoke_eq _ checkerProg_lookup_check_b]
  simp only [callFn, checkBL]
  cases n with
  | zero => vcgen [exec] <;> simp [ErrClaimV.of_cls0]
  | succ n =>
    have hJ := checkJobs_thrE hE n (by omega) a j hj hF
    have hFl := flushCaches_specNV n
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, setG, ld64, warr, (hJ · ·), (hFl ·)]
    all_goals (try simp only [St.setLoc_mem, St.setLoc_loc,
      Locals.init_nil, Cmp.eval,
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
          | exact ⟨_, hfx, by rw [St.setLocs_mem']; exact hm, hR0 (by simp_all)⟩
          | exact ⟨_, hfx, by rw [St.setLocs_mem']; exact hm, hR1 (by simp_all)⟩
          | (rw [St.setLocs_mem', hm, flushMem_glob]; simp_all; done)
          | (rw [St.setLocs_mem', hm, flushMem_glob]; simp only [Mem.copy64_glob] at *; simp_all; done))
      | (rw [St.setLocs_mem']; simp_all; done)
      | (trace_state; fail "ThreadsE.checkB_thrE: no closing tactic applies")

/-- **`check` with the mode word `2` on a thread's memory, error half of `checkThr`.** -/
theorem checkThrE (hE : CjStepE pins dn ds I a₀ (Prog.subPB bs checkerProg))
    (n : Nat) (hn : n ≤ 2 ^ 62) (a : AState) (j : Word) (hj : j.toNat < ds.size)
    (hF : ∃ env, FoldOK env (I.view j.toNat) (AM.st enterScratch a)) (s₀ : St)
    (hmode : s₀.mem.glob MODE = 2) (hR : ThrAt pins dn ds I a₀ bs (seedMem s₀.mem) a)
    (hlo : s₀.mem.glob PLO = j) (hhi : s₀.mem.glob PHI = j + 1) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "check" []
    ⦃fun _ _ => True; ErrClaimV (checkJobList VM pins I ds [j.toNat]) a⦄ := by
  rw [invoke_eq _ checkerProg_lookup_check']
  simp only [callFn, checkL]
  cases n with
  | zero => vcgen [exec] <;> simp [ErrClaimV.of_cls0]
  | succ n =>
    have hB : ⦃fun s => s.mem = s₀.mem⦄ invoke checkerProg (exec checkerProg n) "check_b" []
        ⦃fun _ _ => True; ErrClaimV (checkJobList VM pins I ds [j.toNat]) a⦄ := by
      apply M.triple_of_run' (fun _ _ _ _ _ => trivial)
      intro s₁ e hs hrun
      exact M.of_run_err (P := fun x => x = s₁) rfl hrun
        (checkB_thrE hE n (by omega) a j hj hF s₁ (hs ▸ hR) (hs ▸ hlo) (hs ▸ hhi))
    have hmode' : s₀.mem.glob ⟨8⟩ = 2 := hmode
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, hB,
      (callE_spec checkerProg n "check_a" [1] ·), (callE_spec checkerProg n "check_a" [0] ·)]
    all_goals (try simp only [Cmp.eval, beq_iff_eq] at *)
    all_goals first
      | exact ErrClaimV.of_cls0 (by decide)
      | (simp_all (config := { decide := true }); done)
      | (simp_all [St.setLoc]; done)
      | (trace_state; fail "ThreadsE.checkThrE: no closing tactic applies")

/-- **One call, as a run, error half of `runThr`.** -/
theorem runThrE (hE : CjStepE pins dn ds I a₀ (Prog.subPB bs checkerProg))
    (n : Nat) (hn : n ≤ 2 ^ 62) (a : AState) (j : Word) (hj : j.toNat < ds.size)
    (hF : ∃ env, FoldOK env (I.view j.toNat) (AM.st enterScratch a)) (w : Mem)
    (hmode : w.glob MODE = 2) (hR : ThrAt pins dn ds I a₀ bs (seedMem w) a)
    (hlo : w.glob PLO = j) (hhi : w.glob PHI = j + 1) {e : Err}
    (hrun : L.run checkerProg n "check" [] w = .error e) :
    ErrClaimV (checkJobList VM pins I ds [j.toNat]) a e := by
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
`threads_twinAcceptsPooled`) whose calls `cs` ran and whose next call, on record `j`, failed with an
error `e` of class other than `0` (`ThreadFails`), every claimed index below `k`, every record
below `j` passing on its own. Then the twin's pool fails with that class (`TwinVerdictPooled`),
given `check_decl`'s program facts (`CheckerCd`) and the jobs' error claims (`JobG`) at every
phase A. -/
theorem threads_twinVerdictPooled (Vt : Type w) [ConLeche.SetTheory Vt] (hCd : CheckerCd)
    (hJG : ∀ (b pb : ByteArray) (PA : PhaseA b), pb.size < 2 ^ 63 → PbPre pb →
      JobG PA.ipins (dnOf PA.sE.store) PA.ds (Prog.subPB pb.data.toList checkerProg))
    (b pb : ByteArray) (sz : TieredArray → Nat) (hin : InputsOK b pb sz)
    (N₁ : Nat) (hN₁ : N₁ < 2 ^ 62) (rs₁ : List Word) (m₁ : Mem)
    (h₁ : L.run checkerProg N₁ "check" [] (loadMemM b pb sz 1) = .ok (rs₁, m₁))
    (hge : 9223372036854775808 ≤ (rs₁.headD 0).toNat)
    (B : Array Word) (hB : B = (m₁.arr64 OUT).extract 0 ((m₁.arr64 OUT).getD 1 0).toNat)
    (r₀ : Mem) (hz : ∀ b ∈ parOwnedL, r₀.arr64 b = zeros (m₁.arr64 b).size)
    (hI : r₀.glob INIT = 0) (j : Word) (cs : List (Word × Nat × Mem)) (n : Nat) (e : Err)
    (hruns : ThreadFails B j n e r₀ cs)
    (hcs : ∀ c ∈ cs, c.1 < rs₁.headD 0 - 9223372036854775808)
    (hj : j < rs₁.headD 0 - 9223372036854775808) (hk0 : e.cls ≠ 0)
    (hpass : ∀ i < j.toNat, TwinJobPasses [b] i) :
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
    rw [← hk]; exact UInt64.lt_iff_toNat_lt.mp (hcs c hc)
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
    recCall_stepE hJP hFD hLD hdn hrec hpp (by omega) hden hPD
  have hCE : CjStepE PA.ipins (dnOf PA.sE.store) PA.ds PA.I a₀ p :=
    cjStepE_of hJP hFD hLD hdn hrec hpp hsz hden hPD hJG'
  have hstep : ∀ (k : Nat) (r r' : Mem) (a : AState) (hk : k < PA.ds.size), Rel r a → Call k r r' →
      (∃ env, FoldOK env (PA.I.view k) (AM.st enterScratch a)) →
      ∃ a', recordJob .verified PA.ipins PA.I k PA.ds[k] a = .ok ((), a') ∧ Rel r' a' := by
    intro k r r' a hk hR ⟨n, rs, hn, hrun, hkept⟩ hfo
    have hk' : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
    obtain ⟨⟨a', hrj, X, hJ, hPB, hX⟩, hI⟩ := runThr hJP.check_jobs hRS hsz n hn a (UInt64.ofNat k)
      (by rw [hk']; exact hk) (by rw [hk']; exact hfo) _ rfl (hR _) rfl rfl hrun
    refine ⟨a', ?_, fun j => ⟨X, hJ, hPB, fun t ht => (thr_next B j hI hkept t ht).trans (hX t ht)⟩⟩
    have e : PA.ds[(UInt64.ofNat k).toNat]'(by rw [hk']; exact hk) = PA.ds[k] := by simp only [hk']
    rw [← e]; simp only [hk'] at hrj ⊢; exact hrj
  have H := hH hstep
  -- a call with a record below it that does not pass: the weakened verdict
  by_cases hbad : ∃ c ∈ cs, ∃ i < c.1.toNat, ¬ TwinJobPasses [b] i
  · obtain ⟨c, hc, i, hi, hn⟩ := hbad
    refine TwinVerdictPooled.of_not_passes (j := c.1.toNat) ?_ hi hn
    intro pins sA sB sC sD sE sF pre r ds ipins I hA' hB' hC' hD' _ _
    rw [hA] at hA'; injection hA' with hA'; obtain ⟨-, rfl⟩ := Prod.mk.inj hA'
    rw [hBp] at hB'; injection hB' with hB'; obtain ⟨hB1, rfl⟩ := Prod.mk.inj hB'
    injection hB1 with hB1; subst hB1
    rw [hC] at hC'; injection hC' with hC'; obtain ⟨hC1, rfl⟩ := Prod.mk.inj hC'
    injection hC1 with hC1; subst hC1
    rw [hD] at hD'; injection hD' with hD'; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hD'
    exact hcN c hc
  simp only [not_exists, not_and, Classical.not_not] at hbad
  -- a passing record's job accepts from the index state's worker
  have hjob : ∀ i (hi : i < PA.ds.size), TwinJobPasses [b] i →
      ∃ a', recordJob VM PA.ipins PA.I i PA.ds[i] PA.sF.worker = .ok ((), a') := by
    intro i hi hp
    obtain ⟨s', hs'⟩ := hp PA.pins PA.sA PA.sB PA.sC PA.sD PA.sE PA.sF PA.pre PA.rc PA.ds PA.ipins
      PA.I hA hBp hC hD hE PA.idx
    cases hrj : recordJob VM PA.ipins PA.I i PA.ds[i] PA.sF.worker with
    | ok v => exact ⟨v.2, by cases v; rfl⟩
    | error ce =>
      have e1 : (checkJobList VM PA.ipins PA.I PA.ds [i]) PA.sF.worker = .ok (.error (ce, i), AState.abandoned) := by
        simp only [checkJobList, runJob, Array.getElem?_eq_getElem hi, hrj]
      rw [show (checkJobList VM PA.ipins PA.I PA.ds [i]) PA.sF.worker = _ from hs'] at e1
      cases e1
  -- the fold's prefixes below passing records
  have hpre : ∀ x, x ≤ PA.ds.size → (∀ i < x, TwinJobPasses [b] i) → PrefixOK pinsP dsP x ∧
      ((ConLeche.Cached.recsConsts (dsP.take x)).map (·.name)).Nodup := by
    intro x
    induction x with
    | zero =>
      intro _ _
      have h0 : (ConLeche.Cached.recsConsts ([] : List ConLeche.Declaration)).length = 0 := by
        have := (ConLeche.Cached.buildIndex_spec (#[] : Array ConLeche.Declaration)).next
        simpa [ConLeche.Cached.buildIndex] using this.symm
      refine ⟨⟨0, fun _ _ => rfl⟩, ?_⟩
      rw [List.take_zero, List.eq_nil_of_length_eq_zero h0]
      exact List.nodup_nil
    | succ x ih =>
      intro hx hp
      obtain ⟨hPx, hndx⟩ := ih (by omega) fun i hi => hp i (by omega)
      obtain ⟨a', hj'⟩ := hjob x (by omega) (hp x (by omega))
      obtain ⟨hx', hdk⟩ := H.hden x (by omega)
      obtain ⟨-, env', F, hd⟩ := job_spec Vt H.hrec H.hpp H.hpinsOK H.hpersPins H.hpins H.hpd H.hI
        H.hpI (WorkerOK.start hst) (by omega) hx' hdk hPx hndx hj'
      exact PrefixOK.step H.hpush hx' hPx hd hndx
  have hfold : ∀ x a, x < PA.ds.size → (∀ i < x, TwinJobPasses [b] i) → WorkerOK PA.sF a →
      ∃ env, FoldOK env (PA.I.view x) (AM.st enterScratch a) := fun x a hx hp hw => by
    obtain ⟨hP, hnd⟩ := hpre x (by omega) hp
    obtain ⟨hx', -⟩ := H.hden x hx
    exact worker_foldOK Vt H.hpinsOK H.hpersPins H.hI H.hpI hx' hP hnd hw
  -- the thread's walk
  have walk : ∀ (cs : List (Word × Nat × Mem)) (r : Mem) (a : AState), Rel r a → WorkerOK PA.sF a →
      ThreadFails B j n e r cs →
      (∀ c ∈ cs, c.1.toNat < PA.ds.size ∧ ∀ i < c.1.toNat, TwinJobPasses [b] i) →
      ErrClaimV (checkJobList VM PA.ipins PA.I PA.ds (cs.map (·.1.toNat) ++ [j.toNat])) a e := by
    intro cs
    induction cs with
    | nil =>
      intro r a hR hw ⟨hn, hrun⟩ _
      exact runThrE hCE n hn a j hjN (hfold _ a hjN hpass hw) _ rfl (hR j) rfl rfl hrun
    | cons c cs ih =>
      intro r a hR hw h hc
      obtain ⟨j', n', r'⟩ := c
      obtain ⟨hn', ⟨rs, hrun⟩, hkept, hrest⟩ := h
      obtain ⟨hj', hp'⟩ := hc _ List.mem_cons_self
      obtain ⟨⟨a', hrj, X, hJ, hPB, hX⟩, hI'⟩ := runThr hJP.check_jobs hRS hsz n' hn' a j' hj'
        (hfold _ a hj' hp' hw) _ rfl (hR _) rfl rfl hrun
      have hR' : Rel r' a' := fun j => ⟨X, hJ, hPB, fun t ht => (thr_next B j hI' hkept t ht).trans (hX t ht)⟩
      obtain ⟨hP, hnd⟩ := hpre _ (by omega) hp'
      obtain ⟨hx', hdk⟩ := H.hden _ hj'
      obtain ⟨hw', -⟩ := job_spec Vt H.hrec H.hpp H.hpinsOK H.hpersPins H.hpins H.hpd H.hI
        H.hpI hw hj' hx' hdk hP hnd hrj
      exact ErrClaimV.cons_ok hj' hrj
        (ih r' a' hR' hw' hrest fun c hc' => hc c (List.mem_cons_of_mem _ hc'))
  -- the thread's start
  have hstart : Rel r₀ PA.sF.worker := by
    intro j
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
      exact thr_first hok hlt r₀ j (fun b hb => by rw [hz b hb, hO.size]) hI
  have hW := walk cs r₀ PA.sF.worker hstart (WorkerOK.start hst) hruns
    fun c hc => ⟨hcN c hc, hbad c hc⟩
  refine .inr ⟨PA.pins, PA.sA, PA.sB, PA.sC, PA.sD, PA.sE, PA.sF, PA.pre, PA.rc, PA.ds, PA.ipins,
    PA.I, cs.map (·.1.toNat) ++ [j.toNat], hA, hBp, hC, hD, hE, PA.idx, fun t ht => ?_, .inl (hW hk0)⟩
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
    exact hcN c hc
  · rw [List.mem_singleton.mp ht]; exact hjN

end L.Checker
