module

public import ConAgua.Checker.ParDriverL
public import ConAgua.Checker.ParThreadReads
public import ConAgua.Arena.FreezeBuf
import ConAgua.Checker.CheckARun
import ConAgua.L.Blocks
import all ConAgua.Checker.Entry
import ConAgua.Arena.FreezeFreshBase
public import ConAgua.Arena.JobStart

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
    {ds : Array IDeclaration} {J : Option ISolution} {I : IStreamIndex} {M : Mem} {a : AState}
    (h : JobR pins dn ds J I M a) (hfok : FlushOK M) : JobR pins dn ds J I (flushMem M) a := by
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
    h.memos.frameLo hA hC hF, h.fsize, h.frozen.frameLo hC hF, h.jsol.frameLo hA hC hF⟩, h.state, h.off,
    h.caches⟩
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
  ∃ X, JobRel pins dn ds none I a₀ X a ∧ X.arr8 PB = bs.toArray ∧ ∀ t, thrS t = true → w.arr64 t = X.arr64 t

variable (pins dn ds I a₀) in
/-- **`record_job` calls as the pool's step** (`recCall_stepE`'s conclusion). -/
def RecStep (p : Prog) : Prop :=
  ∀ (k : Nat) (r r' : Mem) (a : AState) (hk : k < ds.size), JobRel pins dn ds none I a₀ r a →
    RecCall p k r r' → (∃ env, FoldOK env (I.view k) (AM.st enterScratch a)) →
    ∃ a', recordJob VM pins none I k ds[k] a = .ok ((), a') ∧ JobRel pins dn ds none I a₀ r' a'

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
    (hF : ∃ env, FoldOK env (I.view j.toNat) (AM.st enterScratch a)) (x y : Word) :
    ⦃fun s => x = j ∧ y = j + 1 ∧ s.mem.glob INIT ≠ 0 ∧ ∃ Y, FlushOK Y ∧ s.mem = flushMem Y ∧
      ThrAt pins dn ds I a₀ bs Y a⦄
    invoke checkerProg (exec checkerProg n) "check_jobs" [x, y]
    ⦃fun _ s' => (∃ a', recordJob VM pins none I j.toNat ds[j.toNat] a = .ok ((), a') ∧
      ThrAt pins dn ds I a₀ bs s'.mem a') ∧ s'.mem.glob INIT ≠ 0; ⊤⦄ := by
  apply M.triple_of_run
  rintro s rs s' ⟨hxj, hyj, hg, Y, hfy, hsY, X, hJ, hPB, hYX⟩ hrun
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
  have hJF : JobRel pins dn ds none I a₀ (flushMem X) a := ⟨a₁, ⟨hJR.flush hfx, hx, hp⟩, hSE⟩
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
  have hJ2 : JobRel pins dn ds none I a₀ s₂.mem a := ⟨a₁, ⟨(hJR.flush hfx).setGlob _, hx, hp⟩, hSE⟩
  obtain ⟨a', hrec, hJ'⟩ := hS j.toNat s₂.mem s₂'.mem a hj hJ2 hcall hF
  exact ⟨a', hrec, s₂'.mem, hJ', hPB', fun t ht => hAg'.1 t ht⟩

/-- **`check_b`'s first block**: on the first call (`INIT = 0`) the seed `CTLF` copied into `CTL`
and `INIT := 1`; on later calls nothing. -/
def seedMem (w : Mem) : Mem :=
  if w.glob INIT = 0 then (w.copy64 CTL 0 CTLF 0 (w.len64 CTLF).toNat).setG INIT 1 else w

/-- **`check_b` on a thread's memory**: from a memory whose `seedMem` is `ThrAt a`, with the range
`[j, j + 1)`, a returning call runs record `j`'s job at `a` and leaves a memory `ThrAt` the state
after it, with `INIT` nonzero. -/
theorem checkB_thr (hck : (Prog.subPB bs checkerProg).lookup "check_jobs" = some checkJobsL)
    (hS : RecStep pins dn ds I a₀ (Prog.subPB bs checkerProg)) (hds : ds.size < 2 ^ 63)
    (n : Nat) (hn : n ≤ 2 ^ 62) (a : AState) (j : Word) (hj : j.toNat < ds.size)
    (hF : ∃ env, FoldOK env (I.view j.toNat) (AM.st enterScratch a)) (s₀ : St)
    (hR : ThrAt pins dn ds I a₀ bs (seedMem s₀.mem) a)
    (hlo : s₀.mem.glob PLO = j) (hhi : s₀.mem.glob PHI = j + 1) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "check_b" []
    ⦃fun _ s' => (∃ a', recordJob VM pins none I j.toNat ds[j.toNat] a = .ok ((), a') ∧
      ThrAt pins dn ds I a₀ bs s'.mem a') ∧ s'.mem.glob INIT ≠ 0; ⊤⦄ := by
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
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hJ := checkJobs_thrT hck hS hds n (by omega) a j hj hF
    have hFl := flushCaches_spec checkerProg L.Checker.checkerProg_flushProg n
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, setG, ld64, warr, (hJ · ·), (hFl ·)]
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
          | (rw [L.St.setLocs_mem, hm, flushMem_glob]; simp only [Mem.copy64_glob] at *; simp_all; done))
      | (rw [L.St.setLocs_mem]; simp_all; done)

/-- **`check` with the mode word `2` on a thread's memory**: `check_b` (as `checkB_thr`). -/
theorem checkThr (hck : (Prog.subPB bs checkerProg).lookup "check_jobs" = some checkJobsL)
    (hS : RecStep pins dn ds I a₀ (Prog.subPB bs checkerProg)) (hds : ds.size < 2 ^ 63)
    (n : Nat) (hn : n ≤ 2 ^ 62) (a : AState) (j : Word) (hj : j.toNat < ds.size)
    (hF : ∃ env, FoldOK env (I.view j.toNat) (AM.st enterScratch a)) (s₀ : St)
    (hmode : s₀.mem.glob MODE = 2) (hR : ThrAt pins dn ds I a₀ bs (seedMem s₀.mem) a)
    (hlo : s₀.mem.glob PLO = j) (hhi : s₀.mem.glob PHI = j + 1) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "check" []
    ⦃fun _ s' => (∃ a', recordJob VM pins none I j.toNat ds[j.toNat] a = .ok ((), a') ∧
      ThrAt pins dn ds I a₀ bs s'.mem a') ∧ s'.mem.glob INIT ≠ 0; ⊤⦄ := by
  rw [invoke_eq _ checkerProg_lookup_check']
  simp only [callFn, checkL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hB := checkB_thr hck hS hds n (by omega) a j hj hF
    have hmode' : s₀.mem.glob ⟨8⟩ = 2 := hmode
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, (hB · · · ·),
      (L.invoke_loc checkerProg (exec checkerProg n) "check_a" [1] ·),
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
theorem runThr (hck : (Prog.subPB bs checkerProg).lookup "check_jobs" = some checkJobsL)
    (hS : RecStep pins dn ds I a₀ (Prog.subPB bs checkerProg)) (hds : ds.size < 2 ^ 63)
    (n : Nat) (hn : n ≤ 2 ^ 62) (a : AState) (j : Word) (hj : j.toNat < ds.size)
    (hF : ∃ env, FoldOK env (I.view j.toNat) (AM.st enterScratch a)) (w : Mem)
    (hmode : w.glob MODE = 2) (hR : ThrAt pins dn ds I a₀ bs (seedMem w) a)
    (hlo : w.glob PLO = j) (hhi : w.glob PHI = j + 1) {rs : List Word} {w' : Mem}
    (hrun : L.run checkerProg n "check" [] w = .ok (rs, w')) :
    (∃ a', recordJob VM pins none I j.toNat ds[j.toNat] a = .ok ((), a') ∧
      ThrAt pins dn ds I a₀ bs w' a') ∧ w'.glob INIT ≠ 0 :=
  run_post (Q := fun _ m => (∃ a', recordJob VM pins none I j.toNat ds[j.toNat] a = .ok ((), a') ∧
      ThrAt pins dn ds I a₀ bs m a') ∧ m.glob INIT ≠ 0) hrun
    (checkThr hck hS hds n hn a j hj hF _ hmode hR hlo hhi)

end thread

/-! ## The thread's memory at a call -/

/-- **An array of `thrS`** is a frozen one (not the header or the seed) or an owned one. -/
theorem thrS_cases {b : TieredArray} (h : thrS b = true) :
    (∃ k, ∃ hk : k < frozen.length, 1 ≤ k ∧ b = frozen[k].1) ∨ b ∈ parOwnedL := by
  obtain ⟨h1, h2, h3 | h3⟩ := (thrS_iff b).mp h
  · left
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem h3
    subst e
    have hL : frozenIdsL.length = frozen.length + 1 := by rw [frozenIdsL_eq]; simp
    rcases i with _ | _ | k
    · exact absurd rfl h1
    · exact absurd (by rw [frozenIdsL_get (by omega)]; rfl) h2
    · exact ⟨k + 1, by omega, by omega, frozenIdsL_get (by omega)⟩
  · exact Or.inr h3

theorem seedMem_of_ne {w : Mem} (h : w.glob INIT ≠ 0) : seedMem w = w := by
  simp only [seedMem, ite_eq_right h]

theorem truncList_bytes (m₀ : Mem) : ∀ (zs : List (ArrId × Fz)) (m : Mem),
    (truncList m₀ m zs).bytes = m.bytes
  | [], _ => rfl
  | (_, _) :: zs, m => by rw [truncList, truncList_bytes m₀ zs]

theorem freshMem_arr8 (m : Mem) (b : ArrId) : (freshMem m).arr8 b = m.arr8 b := by
  show (truncFrozen m).bytes b = m.bytes b
  rw [truncFrozen, truncList_bytes]

/-- **A later call**: the previous call's final memory `r`, with `INIT` nonzero and its frozen
arrays (but the header and the seed) the buffer's images, and the next call's memory
`bufMem B r j` agree on `thrS`. -/
theorem thr_next {r : Mem} (B : Array Word) (j : Word) (hI : r.glob INIT ≠ 0)
    (hfz : ∀ k (hk : k < frozen.length), 1 ≤ k → r.arr64 frozen[k].1 = bufImg B (k + 1)) :
    ∀ t, thrS t = true → (seedMem (bufMem B r j)).arr64 t = r.arr64 t := by
  intro t ht
  rw [seedMem_of_ne (by rw [bufMem_glob_init]; exact hI)]
  rcases thrS_cases ht with ⟨k, hk, h1, rfl⟩ | ho
  · rw [bufMem_frozen B r j hk h1, hfz k hk h1]
  · exact bufMem_owned B r j ho

/-- **The first call**: from entry 1's memory `m` (the buffer `bufOf m`) and a region memory `r`
with `INIT = 0` and every owned array zero (at its size in `m`), the memory after `check_b`'s seed
copy on `bufMem (bufOf m) r j` agrees with `freshMem m` on `thrS`. -/
theorem thr_first {m : Mem} (hok : parCompactOK m 1 = true) (hlt : (m.arr64 OUT).size < 2 ^ 64)
    (r : Mem) (j : Word) (hz : ∀ b ∈ parOwnedL, r.arr64 b = zeros (m.arr64 b).size)
    (hI : r.glob INIT = 0) :
    ∀ t, thrS t = true → (seedMem (bufMem (bufOf m) r j)).arr64 t = (freshMem m).arr64 t := by
  have hI' : (bufMem (bufOf m) r j).glob INIT = 0 := hI
  simp only [seedMem, ite_eq_left hI']
  generalize hW : bufMem (bufOf m) r j = W
  obtain ⟨hseed, h256⟩ := bufImg_seed hok hlt
  have hctlf : W.arr64 CTLF = (m.arr64 CTL).extract 0 256 := by
    rw [← hW, bufMem_ctlf, hseed]
  have hlen : (W.len64 CTLF).toNat = 256 := by
    simp only [Mem.len64, hctlf, size_extract0, Nat.min_eq_left h256]; rfl
  have hctl : W.arr64 CTL = zeros (m.arr64 CTL).size := by
    rw [← hW, bufMem_ctl]; exact hz CTL (by decide)
  rw [hlen]
  intro b hb
  rw [show ∀ M : Mem, (M.setG INIT 1).arr64 b = M.arr64 b from fun _ => rfl]
  by_cases hbc : b = CTL
  · subst hbc
    rw [freshMem_arr, ite_eq_left rfl, truncFrozen_ctl]
    apply arr_eq_of_getD
    · rw [size_copy64, hctl, freshCtl_size]; simp [zeros]
    · intro k hk
      rw [size_copy64, hctl] at hk
      simp only [zeros, Array.size_replicate] at hk
      rw [getD_copy64 (by decide) 256 W 0 0 (by simp) (by simp) k, getD_freshCtl, hctl, hctlf]
      simp only [UInt64.toNat_zero, Nat.zero_le, true_and, Nat.zero_add, Nat.sub_zero, zeros,
        Array.size_replicate]
      by_cases h1 : k < 256
      · rw [ite_eq_left ⟨h1, hk⟩, ite_eq_left h1, getD_extract_lt _ _ _ _ (by rw [size_extract0]; omega),
          Nat.zero_add]
      · rw [ite_eq_right (by omega), ite_eq_right h1]
        simp [Array.getD_eq_getD_getElem?, hk]
  · rw [arr64_copy64_ne _ _ _ _ _ _ hbc, ← hW]
    rcases thrS_cases hb with ⟨k, hk, h1, rfl⟩ | ho
    · obtain ⟨-, hz', hc⟩ := frozen_facts hk h1
      rw [bufMem_frozen _ r j hk h1, bufImg_trunc hok hlt hk h1, freshMem_arr,
        ite_eq_right (TieredArray.t0_ne hc), ite_eq_right hz']
    · obtain ⟨-, hsrc⟩ := owned_facts ho
      rw [bufMem_owned _ r j ho, hz b ho, freshMem_arr, ite_eq_right hbc,
        ite_eq_left (show b ∈ freshZ from List.mem_cons_of_mem _ ho), truncFrozen_other m b hsrc]

end L.Checker
