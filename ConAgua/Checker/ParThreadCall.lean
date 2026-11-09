module

public import ConAgua.Checker.ParThreadL
public import ConAgua.Checker.ParThreadReads
public import ConAgua.Arena.FreezeBuf
import ConAgua.Checker.CheckARun
import ConAgua.Arena.FreezeFresh
import ConAgua.Checker.RomProg0
import ConAgua.L.Blocks
import all ConAgua.Checker.Entry

@[expose] public section

/-!
# The threads' entry 2, one call (lane parmode)

docs/design/parmode.md, "Step 4". A thread calls `check` with the mode word `2` and the range
`[j, j + 1)` on the memory `bufMem B r j` (`Arena/FreezeRel.lean`): the frozen arrays are the
buffer's images, the owned arrays the region's `r`, every other word array empty.

* `ThrAt w a`: the thread's memory `w` agrees on `thrS` (the frozen arrays but `HDRF`/`CTLF`, and
  the owned arrays) with a memory where the jobs' relation (`JobRel`) holds at the twin's `a`: the
  worker memory has no other array, and the jobs name no other (`checkerProg_thrReads`).
* `seedMem w`: the memory after `check_b`'s first block (on the first call, `INIT = 0`: the seed
  `CTLF` copied into `CTL`, `INIT := 1`; later calls: `w`).
* `checkJobs_thrT`, `checkB_thr`, `checkThr`, `runThr`: a call that returns from a memory whose
  `seedMem` is `ThrAt a`, with the range `[j, j + 1)`, runs record `j`'s job at `a` (`recordJob`)
  and leaves a memory `ThrAt` the state after it, with `INIT` nonzero.
* `ThrAt.first`: a thread's first call (a fresh region) is `ThrAt` the index state's worker, through
  `freshMem` (`JobM.trunc`, `JobM.fresh`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Checker

open L L.Arena L.Rom ConRon.Bridge

local notation "VM" => ConLeche.CheckMode.verified

/-! ## The jobs' relation across the flush, and before it -/

/-- **`JobR` across the core caches' flush.** -/
theorem _root_.L.Arena.JobR.flush {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}
    {ds : Array IDeclaration} {I : IStreamIndex} {M : Mem} {a : AState}
    (h : JobR pins dn ds I M a) (hfok : FlushOK M) : JobR pins dn ds I (flushMem M) a := by
  have hF := flushMem_frame M
  have hA : LoArr [] := loArr_nil
  have hC : LoCtl flushCtl := loCtl_flush
  refine ⟨⟨⟨ArenaR.frame_ext [] _ (by simp) flushCtl_ge _ _ hF _ h.arena.base,
      DerR.frameM [] _ _ _ hF (by simp) _ h.arena.der⟩, ?_,
    h.pinsR.frame (fun _ h => absurd h (by simp)) hF, h.mode.frame hF (by decide) (by decide),
    h.idx.frameLo hA hC hF, h.below.frameLo hA hC hF,
    by rw [stampW_frameLo hC hF]; exact h.stamp, declsF_frameLo hA hF h.decls, iwOK_frameLo hA hC hF h.iw,
    by rw [hC.ctl hF (by decide)]; exact h.top1, pinSetsR_frameLo hA hC hF h.pinsets,
    h.mem.frameLo hA hC hF fun k x e => h.mem.dnN k x e, by rw [pinW_frame hF (by simp)]; exact h.flag,
    h.memos.frameLo hA hC hF, h.fsize⟩, h.state, h.off, h.caches⟩
  have := h.core.flush hfok
  rw [h.caches]; exact this

/-! ## The thread's memory -/

section thread
variable {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration}
  {I : IStreamIndex} {a₀ : AState} {bs : List UInt8}

variable (pins dn ds I a₀ bs) in
/-- **What a thread's memory `w` stands for** at the twin's state `a`: a memory `X` with the jobs'
relation at `a` (from `a₀`) and the ROM, whose arrays of `thrS` are `w`'s. -/
def ThrAt (w : Mem) (a : AState) : Prop :=
  ∃ X, JobRel pins dn ds I a₀ X a ∧ X.arr8 PB = bs.toArray ∧ ∀ t, thrS t = true → w.arr64 t = X.arr64 t

variable (pins dn ds I a₀) in
/-- **`record_job` calls as the pool's step** (`recCall_stepE`'s conclusion). -/
def RecStep (p : Prog) : Prop :=
  ∀ (k : Nat) (r r' : Mem) (a : AState) (hk : k < ds.size), JobRel pins dn ds I a₀ r a →
    RecCall p k r r' → (∃ env, FoldOK env (I.view k) (AM.st enterScratch a)) →
    ∃ a', recordJob VM pins I k ds[k] a = .ok ((), a') ∧ JobRel pins dn ds I a₀ r' a'

/-- A `check_jobs(j, j + 1)` loop that returns is one `record_job(j)` call. -/
theorem checkJobsLoop_one {p : Prog} {n : Nat} {m q : Mem} {j : Word} (hj : j.toNat + 1 < 2 ^ 64)
    (h : checkJobsE.loop1 p (n + 1) m j (j + 1) = .ok q) :
    ∃ r, callE p n "record_job" [j] m = .ok (r, q) := by
  have g : j < j + 1 := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add]; simp; omega
  rw [checkJobsE.loop1.arm1 _ _ _ _ _ g] at h
  cases hc : callE p n "record_job" [j] m with
  | error e => rw [hc, checkJobsE.k_record_job.none] at h; cases h
  | ok q1 =>
    obtain ⟨r, m₁⟩ := q1
    rw [hc, checkJobsE.k_record_job.arm1] at h
    refine ⟨r, ?_⟩
    cases n with
    | zero => rw [checkJobsE.loop1.eq_1] at h; cases h
    | succ n =>
      rw [checkJobsE.loop1.arm2 _ _ _ _ _ (UInt64.lt_irrefl _)] at h
      cases h; rfl

/-- **`check_jobs(j, j + 1)` on a thread's memory, after the flush**: from the flush of a memory
`ThrAt a`, a returning call runs record `j`'s job at `a` and leaves a memory `ThrAt` the state
after it, keeping `INIT`. -/
theorem checkJobs_thrT (hck : (Prog.subPB bs checkerProg).lookup "check_jobs" = some checkJobsL)
    (hS : RecStep pins dn ds I a₀ (Prog.subPB bs checkerProg)) (hds : ds.size < 2 ^ 63)
    (n : Nat) (hn : n ≤ 2 ^ 62) (a : AState) (j : Word) (hj : j.toNat < ds.size)
    (hF : ∃ env, FoldOK env (I.view j.toNat) (AM.st enterScratch a)) (g x y : Word) :
    ⦃fun s => x = j ∧ y = j + 1 ∧ s.mem.glob INIT = g ∧ ∃ Y, FlushOK Y ∧ s.mem = flushMem Y ∧
      ThrAt pins dn ds I a₀ bs Y a⦄
    invoke checkerProg (exec checkerProg n) "check_jobs" [x, y]
    ⦃fun _ s' => (∃ a', recordJob VM pins I j.toNat ds[j.toNat] a = .ok ((), a') ∧
      ThrAt pins dn ds I a₀ bs s'.mem a') ∧ s'.mem.glob INIT = g; ⊤⦄ := by
  apply M.triple_of_run
  rintro s rs s' ⟨hxj, hyj, hg, Y, hfy, hsY, X, hJ, hPB, hYX⟩ hrun
  rw [hxj, hyj] at hrun
  refine ⟨?_, by rw [← hg]; exact invoke_keepsG checkerProg_phaseBGlobs check_jobs_mem_phaseBJobFns hrun (g := INIT) (by decide)⟩
  have hc : thrS CTL = true := by decide
  let X₂ : Mem := ⟨X.bytes, X.words, Y.glob⟩
  have hAg0 : Agree thrS (fun _ => false) Y X₂ :=
    ⟨fun t ht => hYX t ht, fun _ h => absurd h (by simp), rfl⟩
  have hfx : FlushOK X := by
    rw [flushOK_eq] at hfy ⊢
    exact clearsOK_words _ (m₁ := X₂) (m₂ := X) rfl (clearsOK_agree hc _ hAg0 hfy)
  obtain ⟨a₁, ⟨hJR, hx, hp⟩, hSE⟩ := hJ
  have hJF : JobRel pins dn ds I a₀ (flushMem X) a := ⟨a₁, ⟨hJR.flush hfx, hx, hp⟩, hSE⟩
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
  have hJ2 : JobRel pins dn ds I a₀ s₂.mem a := ⟨a₁, ⟨(hJR.flush hfx).setGlob _, hx, hp⟩, hSE⟩
  obtain ⟨a', hrec, hJ'⟩ := hS j.toNat s₂.mem s₂'.mem a hj hJ2 hcall hF
  exact ⟨a', hrec, s₂'.mem, hJ', hPB', fun t ht => hAg'.1 t ht⟩

end thread

end L.Checker
