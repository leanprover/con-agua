module

public import ConAgua.Checker.ParThreadCall
import ConAgua.Checker.CheckARun
import ConAgua.L.Blocks
import ConAgua.Checker.LoopProgTac
meta import ConAgua.Checker.LoopProgTac
import all ConAgua.Checker.Entry
import ConAgua.Checker.ParDriverL
import ConAgua.Checker.JobsStart

@[expose] public section

/-!
# The threads' entry 2, one call, with an invariant of the witness (lane compare2, H7)

`Checker/ParThreadCall.lean`'s `checkJobs_thrT`, `checkB_thr`, `checkThr`, `runThr` with a
predicate `Q` on the witness memory carried along (`ThrAtQ`, `RecStepQ`): kept by the flush
(`hQf`) and by every `record_job` call. The threaded compared run needs it for what the
solution's jobs keep of the challenge's view (the walks' memos, the record pool's growth).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Checker

open L L.Arena L.Rom ConRon.Bridge

local notation "VM" => ConLeche.CheckMode.verified

section thread
variable (Q : Mem → Prop) {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration}
  {I : IStreamIndex} {a₀ : AState} {bs : List UInt8} {J : Option ISolution}

variable (pins dn ds I a₀ bs) in
/-- **`ThrAt` with `Q` at the witness.** -/
def ThrAtQ (w : Mem) (a : AState) (J : Option ISolution := none) : Prop :=
  ∃ X, JobRel pins dn ds J I a₀ X a ∧ Q X ∧ X.arr8 PB = bs.toArray ∧ ∀ t, thrS t = true → w.arr64 t = X.arr64 t

variable (pins dn ds I a₀) in
/-- **`RecStep` keeping `Q`.** -/
def RecStepQ (p : Prog) (J : Option ISolution := none) : Prop :=
  ∀ (k : Nat) (r r' : Mem) (a : AState) (hk : k < ds.size), JobRel pins dn ds J I a₀ r a → Q r →
    RecCall p k r r' → (∃ env, FoldOK env (I.view k) (AM.st enterScratch a)) →
    ∃ a', recordJob VM pins J I k ds[k] a = .ok ((), a') ∧ JobRel pins dn ds J I a₀ r' a' ∧ Q r'

variable {Q}

/-- **`check_jobs(j, j + 1)` on a thread's memory, after the flush**: from the flush of a memory
`ThrAt a`, a returning call runs record `j`'s job at `a` and leaves a memory `ThrAt` the state
after it, keeping `INIT`. -/
theorem checkJobs_thrTQ (hck : (Prog.subPB bs checkerProg).lookup "check_jobs" = some checkJobsL)
    (hS : RecStepQ Q pins dn ds I a₀ (Prog.subPB bs checkerProg) J)
    (hQf : ∀ (X : Mem) g, Q X → FlushOK X → Q ⟨(flushMem X).bytes, (flushMem X).words, g⟩) (hds : ds.size < 2 ^ 63)
    (n : Nat) (hn : n ≤ 2 ^ 62) (a : AState) (j : Word) (hj : j.toNat < ds.size)
    (hF : ∃ env, FoldOK env (I.view j.toNat) (AM.st enterScratch a)) (x y : Word) :
    ⦃fun s => x = j ∧ y = j + 1 ∧ s.mem.glob INIT ≠ 0 ∧ ∃ Y, FlushOK Y ∧ s.mem = flushMem Y ∧
      ThrAtQ Q pins dn ds I a₀ bs Y a J⦄
    invoke checkerProg (exec checkerProg n) "check_jobs" [x, y]
    ⦃fun _ s' => (∃ a', recordJob VM pins J I j.toNat ds[j.toNat] a = .ok ((), a') ∧
      ThrAtQ Q pins dn ds I a₀ bs s'.mem a' J) ∧ s'.mem.glob INIT ≠ 0; ⊤⦄ := by
  apply M.triple_of_run
  rintro s rs s' ⟨hxj, hyj, hg, Y, hfy, hsY, X, hJ, hQ, hPB, hYX⟩ hrun
  rw [hxj, hyj] at hrun
  refine ⟨?_, by rw [invoke_keepsG checkerProg_phaseBGlobs check_jobs_mem_phaseBJobFns hrun (g := INIT) (by decide)]; exact hg⟩
  have hc : thrS CTL = true := by decide
  let X₂ : Mem := ⟨X.bytes, X.words, Y.glob⟩
  have hAg0 : Agree thrS (fun _ => false) Y X₂ :=
    ⟨fun t ht => hYX t ht, fun _ h => absurd h (by simp), rfl⟩
  have hfx : FlushOK X := by
    rw [flushOK_eq] at hfy ⊢
    exact clearsOK_words _ (m₁ := X₂) (m₂ := X) rfl (clearsOK_agree hc _ hAg0 hfy)
  obtain ⟨a₁, ⟨hJR, hx, hp⟩, hSE⟩ := hJ
  have hJF : JobRel pins dn ds J I a₀ (flushMem X) a := ⟨a₁, ⟨hJR.flush hfx, hx, hp⟩, hSE⟩
  have hA2 := flushMem_agree hAg0 hc
  have hw2 : (flushMem X₂).words = (flushMem X).words := flushMem_words rfl
  let s₂ : St := ⟨⟨(flushMem X).bytes, (flushMem X).words, s.mem.glob⟩, s.loc⟩
  have hAg : Agree thrS (fun _ => false) s.mem s₂.mem :=
    ⟨fun t ht => by
      rw [hsY, hA2.1 t ht]; show (flushMem X₂).words t = (flushMem X).words t; rw [hw2],
     fun _ h => absurd h (by simp), rfl⟩
  obtain ⟨s₂', hrun₂, hAg', -⟩ :=
    invoke_agree_ok checkerProg_thrReads check_jobs_mem_phaseBJobFns hAg rfl hrun
  have hPB₂ : s₂.mem.arr8 L.Rom.PB = bs.toArray := by
    show (flushMem X).bytes L.Rom.PB = _
    rw [flushMem_bytes]; exact hPB
  have hk := M.of_run (P := fun x => x = s₂) rfl hrun₂
    (Triple.keep checkerProg_noSt8 (Q := fun _ _ => True) (s₀ := s₂) (M.triple_of_run fun _ _ _ _ _ => trivial))
  have hPB' : s₂'.mem.arr8 L.Rom.PB = bs.toArray := by rw [hk.2.1.arr8]; exact hPB₂
  rw [← L.Rom.invoke_subPB (bs := bs) checkerProg_noSt8PB n _ _ (s := s₂) hPB₂] at hrun₂
  have hcE := callE_of_run hrun₂
  obtain ⟨_s3, hm3, -, hx'⟩ := triple_of_callE
    (checkJobs_specE (Prog.subPB bs checkerProg) hck n ⟨s₂.mem, Locals.init []⟩ j (j + 1)) hcE
  rcases n with _ | n
  · obtain ⟨e, he, -⟩ := callE_zero (Prog.subPB bs checkerProg) "check_jobs" [j, j + 1] s₂.mem
    rw [hcE] at he; cases he
  have hx'' : checkJobsE.k_loop1 (Prog.subPB bs checkerProg) (checkJobsE.loop1 (Prog.subPB bs checkerProg) (n + 1) s₂.mem j (j + 1)) = _ := hx'
  cases hl : checkJobsE.loop1 (Prog.subPB bs checkerProg) (n + 1) s₂.mem j (j + 1) with
  | error ε => rw [hl] at hx''; cases hx''
  | ok q =>
  rw [hl] at hx''
  have hq : q = s₂'.mem := by
    rw [← hm3]; revert hx''; simp [checkJobsE.k_loop1]
  subst hq
  have hj1 : j.toNat + 1 < 2 ^ 64 := by omega
  obtain ⟨r1, hr1⟩ := checkJobsLoop_one hj1 hl
  have hcall : RecCall (Prog.subPB bs checkerProg) j.toNat s₂.mem s₂'.mem :=
    ⟨n, r1, by omega, by rw [UInt64.ofNat_toNat]; exact hr1⟩
  have hJ2 : JobRel pins dn ds J I a₀ s₂.mem a := ⟨a₁, ⟨(hJR.flush hfx).setGlob _, hx, hp⟩, hSE⟩
  obtain ⟨a', hrec, hJ', hQ'⟩ := hS j.toNat s₂.mem s₂'.mem a hj hJ2 (hQf X _ hQ hfx) hcall hF
  exact ⟨a', hrec, s₂'.mem, hJ', hQ', hPB', fun t ht => hAg'.1 t ht⟩

/-- **`check_b` on a thread's memory**: from a memory whose `seedMem` is `ThrAt a`, with the range
`[j, j + 1)`, a returning call runs record `j`'s job at `a` and leaves a memory `ThrAt` the state
after it, with `INIT` nonzero. -/
theorem checkB_thrQ (hck : (Prog.subPB bs checkerProg).lookup "check_jobs" = some checkJobsL)
    (hS : RecStepQ Q pins dn ds I a₀ (Prog.subPB bs checkerProg) J)
    (hQf : ∀ (X : Mem) g, Q X → FlushOK X → Q ⟨(flushMem X).bytes, (flushMem X).words, g⟩) (hds : ds.size < 2 ^ 63)
    (n : Nat) (hn : n ≤ 2 ^ 62) (a : AState) (j : Word) (hj : j.toNat < ds.size)
    (hF : ∃ env, FoldOK env (I.view j.toNat) (AM.st enterScratch a)) (s₀ : St)
    (hR : ThrAtQ Q pins dn ds I a₀ bs (seedMem s₀.mem) a J)
    (hlo : s₀.mem.glob PLO = j) (hhi : s₀.mem.glob PHI = j + 1) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "check_b" []
    ⦃fun _ s' => (∃ a', recordJob VM pins J I j.toNat ds[j.toNat] a = .ok ((), a') ∧
      ThrAtQ Q pins dn ds I a₀ bs s'.mem a' J) ∧ s'.mem.glob INIT ≠ 0; ⊤⦄ := by
  have hlo' : s₀.mem.glob ⟨9⟩ = j := hlo
  have hhi' : s₀.mem.glob ⟨11⟩ = j + 1 := hhi
  have hR0 : s₀.mem.glob ⟨10⟩ = 0 → ThrAtQ Q pins dn ds I a₀ bs (rereadMem
      { bytes := (s₀.mem.copy64 CTL 0 CTLF 0 (UInt64.toNat (s₀.mem.len64 CTLF))).bytes,
        words := (s₀.mem.copy64 CTL 0 CTLF 0 (UInt64.toNat (s₀.mem.len64 CTLF))).words,
        glob := fun h => if h = ⟨10⟩ then 1
          else (s₀.mem.copy64 CTL 0 CTLF 0 (UInt64.toNat (s₀.mem.len64 CTLF))).glob h }) a J := by
    intro h0; have := hR; simp only [seedMem, ite_eq_left h0] at this; exact this
  have hR1 : ¬ s₀.mem.glob ⟨10⟩ = 0 → ThrAtQ Q pins dn ds I a₀ bs (rereadMem s₀.mem) a J := by
    intro h0; have := hR; simp only [seedMem, ite_eq_right h0] at this; exact this
  rw [invoke_eq _ checkerProg_lookup_check_b]
  simp only [callFn, checkBL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hJ := checkJobs_thrTQ hck hS hQf hds n (by omega) a j hj hF
    have hFl := flushCaches_spec checkerProg L.Checker.checkerProg_flushProg n
    have hRR := seedReread_spec checkerProg (by chk_lk) n
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, setG, ld64, warr, (hJ · ·), (hFl ·), (hRR ·)]
    all_goals (try simp only [L.St.setLoc_mem, St.setLoc_loc,
      L.Locals.init_nil, Cmp.eval,
      reduceIte, beq_iff_eq, decide_eq_true_eq] at *)
    all_goals (try simp only [St.setG, Mem.setG, St.setLoc] at *)
    all_goals first
      | (simp_all (config := { decide := true }) [Mem.arr64]; done)
      | skip
    all_goals first
      | (obtain ⟨-, hfx, hm⟩ := ‹LocEq _ _ ∧ FlushOK _ ∧ _›
         first
          | exact ⟨_, hfx, by rw [L.St.setLocs_mem]; exact hm, hR0 (by simp_all)⟩
          | exact ⟨_, hfx, by rw [L.St.setLocs_mem]; exact hm, hR1 (by simp_all)⟩
          | (rw [L.St.setLocs_mem, hm, flushMem_glob]; simp_all; done)
          | (rw [L.St.setLocs_mem, hm, flushMem_glob]; simp only [Mem.copy64_glob] at *; simp_all; done)
          | exact ⟨_, hfx, by rw [L.St.setLocs_mem]; exact hm,
              by rw [L.St.setLocs_mem, ‹St.mem _ = rereadMem _›]; exact hR0 (by simp_all)⟩
          | exact ⟨_, hfx, by rw [L.St.setLocs_mem]; exact hm,
              by rw [L.St.setLocs_mem, ‹St.mem _ = rereadMem _›]; exact hR1 (by simp_all)⟩
          | (simp only [Mem.copy64_glob] at *; simp_all; done)
          | (rw [L.St.setLocs_mem, hm, flushMem_glob, L.St.setLocs_mem, ‹St.mem _ = rereadMem _›,
              rereadMem_glob]; simp_all; done))
      | (rw [L.St.setLocs_mem]; simp_all; done)
      | (rw [L.St.setLocs_mem]; simp_all [flushMem_glob, rereadMem_glob, Mem.copy64_glob]; done)

/-- **`check` with the mode word `2` on a thread's memory**: `check_b` (as `checkB_thr`). -/
theorem checkThrQ (hck : (Prog.subPB bs checkerProg).lookup "check_jobs" = some checkJobsL)
    (hS : RecStepQ Q pins dn ds I a₀ (Prog.subPB bs checkerProg) J)
    (hQf : ∀ (X : Mem) g, Q X → FlushOK X → Q ⟨(flushMem X).bytes, (flushMem X).words, g⟩) (hds : ds.size < 2 ^ 63)
    (n : Nat) (hn : n ≤ 2 ^ 62) (a : AState) (j : Word) (hj : j.toNat < ds.size)
    (hF : ∃ env, FoldOK env (I.view j.toNat) (AM.st enterScratch a)) (s₀ : St)
    (hmode : s₀.mem.glob MODE = 2) (hR : ThrAtQ Q pins dn ds I a₀ bs (seedMem s₀.mem) a J)
    (hlo : s₀.mem.glob PLO = j) (hhi : s₀.mem.glob PHI = j + 1) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "check" []
    ⦃fun _ s' => (∃ a', recordJob VM pins J I j.toNat ds[j.toNat] a = .ok ((), a') ∧
      ThrAtQ Q pins dn ds I a₀ bs s'.mem a' J) ∧ s'.mem.glob INIT ≠ 0; ⊤⦄ := by
  rw [invoke_eq _ checkerProg_lookup_check']
  simp only [callFn, checkL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hB := checkB_thrQ hck hS hQf hds n (by omega) a j hj hF
    have hmode' : s₀.mem.glob ⟨8⟩ = 2 := hmode
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, (hB · · · ·),
      (L.invoke_loc checkerProg (exec checkerProg n) "check_a" [1] ·), (L.invoke_loc checkerProg (exec checkerProg n) "check_bs" [] ·), (L.invoke_loc checkerProg (exec checkerProg n) "check_bc" [] ·),
      (L.invoke_loc checkerProg (exec checkerProg n) "check_a" [0] ·),
      (L.invoke_loc checkerProg (exec checkerProg n) "check_c1" [] ·),
      (L.invoke_loc checkerProg (exec checkerProg n) "check_c2" [] ·),
      (L.invoke_loc checkerProg (exec checkerProg n) "check_c3" [·] ·)]
    all_goals (try simp only [L.St.setLoc_mem, St.setLocs_cons,
      Cmp.eval, beq_iff_eq, St.setLocs_nil] at *)
    all_goals first
      | (simp_all (config := { decide := true }); done)
      | (simp_all [St.setLoc]; done)

/-- **One call, as a run** (`checkThr`). -/
theorem runThrQ (hck : (Prog.subPB bs checkerProg).lookup "check_jobs" = some checkJobsL)
    (hS : RecStepQ Q pins dn ds I a₀ (Prog.subPB bs checkerProg) J)
    (hQf : ∀ (X : Mem) g, Q X → FlushOK X → Q ⟨(flushMem X).bytes, (flushMem X).words, g⟩) (hds : ds.size < 2 ^ 63)
    (n : Nat) (hn : n ≤ 2 ^ 62) (a : AState) (j : Word) (hj : j.toNat < ds.size)
    (hF : ∃ env, FoldOK env (I.view j.toNat) (AM.st enterScratch a)) (w : Mem)
    (hmode : w.glob MODE = 2) (hR : ThrAtQ Q pins dn ds I a₀ bs (seedMem w) a J)
    (hlo : w.glob PLO = j) (hhi : w.glob PHI = j + 1) {rs : List Word} {w' : Mem}
    (hrun : L.run checkerProg n "check" [] w = .ok (rs, w')) :
    (∃ a', recordJob VM pins J I j.toNat ds[j.toNat] a = .ok ((), a') ∧
      ThrAtQ Q pins dn ds I a₀ bs w' a' J) ∧ w'.glob INIT ≠ 0 :=
  run_post (Q := fun _ m => (∃ a', recordJob VM pins J I j.toNat ds[j.toNat] a = .ok ((), a') ∧
      ThrAtQ Q pins dn ds I a₀ bs m a' J) ∧ m.glob INIT ≠ 0) hrun
    (checkThrQ hck hS hQf hds n hn a j hj hF _ hmode hR hlo hhi)

end thread

end L.Checker
