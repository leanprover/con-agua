import ConAgua.Checker.ParThreadL
import ConAgua.Checker.ParThreadReads
import ConAgua.Arena.FreezeBuf
import ConAgua.Checker.CheckARun
import ConAgua.Arena.FreezeFresh

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
set_option linter.unusedSimpArgs false

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
    (hv : ∀ hb : 3 < (s₀.mem.arr64 HDRF).size, (s₀.mem.arr64 HDRF)[3] = v) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "check_b" []
    ⦃fun _ s' => AM.ok (checkPending mode fe (pdAt pend j)) a ∧
      ThreadRel pins dn ds fe pend bs v s'.mem (AM.st (checkPending mode fe (pdAt pend j)) a) ∧
      s'.mem.glob INIT = 1; ⊤⦄ := by
  have hlo' : s₀.mem.glob ⟨9⟩ = j := hlo
  have hhi' : s₀.mem.glob ⟨11⟩ = j + 1 := hhi
  have hv' : ∀ (hb : (3 : Word).toNat < (s₀.mem.arr64 241).size), (s₀.mem.arr64 241)[(3 : Word).toNat] = v := by
    intro hb; exact hv hb
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

/-- **`check` with the mode word `2` on a thread's memory**: `check_b` (as `checkB_thr0`). -/
theorem checkThr (hP : PhaseBProg (Prog.subPB bs checkerProg)) (hm : mode = .verified)
    (n : Nat) (hn : n ≤ 2 ^ 62) (a : AState) (v j : Word) (hj : j.toNat < pend.size)
    (hj62 : j.toNat < 2 ^ 62) (s₀ : St) (hmode : s₀.mem.glob MODE = 2)
    (hR : ThreadRel pins dn ds fe pend bs v (seedMem s₀.mem) a) (hI : (seedMem s₀.mem).glob INIT = 1)
    (hlo : s₀.mem.glob PLO = j) (hhi : s₀.mem.glob PHI = j + 1)
    (hv : ∀ hb : 3 < (s₀.mem.arr64 HDRF).size, (s₀.mem.arr64 HDRF)[3] = v) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "check" []
    ⦃fun _ s' => AM.ok (checkPending mode fe (pdAt pend j)) a ∧
      ThreadRel pins dn ds fe pend bs v s'.mem (AM.st (checkPending mode fe (pdAt pend j)) a) ∧
      s'.mem.glob INIT = 1; ⊤⦄ := by
  rw [invoke_eq _ checkerProg_lookup_check']
  simp only [callFn, checkL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hB := checkB_thr0 mode pins dn ds fe pend bs hP hm n (by omega) a v j hj hj62
    have hmode' : s₀.mem.glob ⟨8⟩ = 2 := hmode
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      (hB · · · · · ·),
      (L.invoke_loc checkerProg (exec checkerProg n) "check_a" [1] ·),
      (L.invoke_loc checkerProg (exec checkerProg n) "check_a" [0] ·),
      (L.invoke_loc checkerProg (exec checkerProg n) "cap_check" [] ·),
      (L.invoke_loc checkerProg (exec checkerProg n) "pb_check" [] ·),
      (L.invoke_loc checkerProg (exec checkerProg n) "intern_reserved_pins" [] ·),
      (L.invoke_loc checkerProg (exec checkerProg n) "builtin_prelude" [] ·),
      (L.invoke_loc checkerProg (exec checkerProg n) "front_run" [] ·),
      (L.invoke_loc checkerProg (exec checkerProg n) "prepare_prelude" [] ·),
      (L.invoke_loc checkerProg (exec checkerProg n) "intern_all_pins" [] ·),
      (L.invoke_loc checkerProg (exec checkerProg n) "install_then_check" [] ·)]
    all_goals (try simp only [St.setLoc_mem, St.setLoc_loc, St.setLocs_cons, Locals.init_nil,
      Cmp.eval, reduceIte, beq_iff_eq, Sig.retVal, Sig.retOr, St.setLocs_nil, List.headD_cons] at *)
    all_goals first
      | (simp_all (config := { decide := true }); done)
      | (simp_all [St.setLoc]; done)
      | trace_state; sorry

/-- **One call, as a run**: `L.run checkerProg n "check" [] w` that returns, from a memory `w`
with the mode word `2`, the range `[j, j + 1)`, the view in the header's word `3`, and `seedMem w`
`ThreadRel` to `a` with `INIT = 1`: group `j` accepts at `a`, and the final memory is
`ThreadRel` to the state after it, with `INIT = 1`. -/
theorem runThr (hP : PhaseBProg (Prog.subPB bs checkerProg)) (hm : mode = .verified)
    (n : Nat) (hn : n ≤ 2 ^ 62) (a : AState) (v j : Word) (hj : j.toNat < pend.size)
    (hj62 : j.toNat < 2 ^ 62) (w : Mem) (hmode : w.glob MODE = 2)
    (hR : ThreadRel pins dn ds fe pend bs v (seedMem w) a) (hI : (seedMem w).glob INIT = 1)
    (hlo : w.glob PLO = j) (hhi : w.glob PHI = j + 1)
    (hv : ∀ hb : 3 < (w.arr64 HDRF).size, (w.arr64 HDRF)[3] = v) {rs : List Word} {w' : Mem}
    (hrun : L.run checkerProg n "check" [] w = .ok (rs, w')) :
    AM.ok (checkPending mode fe (pdAt pend j)) a ∧
      ThreadRel pins dn ds fe pend bs v w' (AM.st (checkPending mode fe (pdAt pend j)) a) ∧
      w'.glob INIT = 1 :=
  run_post (Q := fun _ m => AM.ok (checkPending mode fe (pdAt pend j)) a ∧
      ThreadRel pins dn ds fe pend bs v m (AM.st (checkPending mode fe (pdAt pend j)) a) ∧
      m.glob INIT = 1) hrun (checkThr mode pins dn ds fe pend bs hP hm n hn a v j hj hj62 _ hmode hR hI hlo hhi hv)

end thread

/-! ## The thread's memory at a call -/

/-- **An array of `thrS`** is a frozen one (not the header or the seed) or an owned one. -/
theorem thrS_cases {b : ArrId} (h : thrS b = true) :
    (∃ k, ∃ hk : k < frozen.length, 1 ≤ k ∧ b = frozen[k].1) ∨ b ∈ parOwnedL := by
  obtain ⟨h1, h2, h3 | h3⟩ := (thrS_iff b).mp h
  · left
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h3
    have hL : frozenIdsL.length = 62 := rfl
    have hF : frozen.length = 61 := frozen_length
    rcases i with _ | _ | k
    · exact absurd rfl h1
    · exact absurd rfl h2
    · exact ⟨k + 1, by omega, by omega, frozenIdsL_get (by omega)⟩
  · exact Or.inr h3

theorem seedMem_of_ne {w : Mem} (h : w.glob INIT ≠ 0) : seedMem w = w := by
  simp only [seedMem, if_neg h]

theorem truncList_bytes (m₀ : Mem) : ∀ (zs : List (ArrId × Fz)) (m : Mem),
    (truncList m₀ m zs).bytes = m.bytes
  | [], _ => rfl
  | (_, _) :: zs, m => by rw [truncList, truncList_bytes m₀ zs]

theorem freshMem_arr8 (m : Mem) (b : ArrId) : (freshMem m).arr8 b = m.arr8 b := by
  show (truncFrozen m).bytes.getD b #[] = m.bytes.getD b #[]
  rw [truncFrozen, truncList_bytes]

section start
variable {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}
  {ds : Array IDeclaration} {fe : IFEnv} {pend : Array PendingCheck} {bs : List UInt8}

/-- **A later call**: the final memory `r` of the previous call `ThreadRel` to `a`, with its frozen
arrays (but the header and the seed) the buffer's images (the buffer is unchanged), gives the next
call's memory `bufMem B r j` `ThreadRel` to `a` (it takes the frozen arrays from `B`, the owned ones
from `r`). -/
theorem ThreadRel.next {v : Word} {r : Mem} {a : AState} (B : Array Word) (j : Word)
    (h : ThreadRel pins dn ds fe pend bs v r a)
    (hfz : ∀ k (hk : k < frozen.length), 1 ≤ k → r.arr64 frozen[k].1 = bufImg B (k + 1)) :
    ThreadRel pins dn ds fe pend bs v (bufMem B r j) a := by
  obtain ⟨m', hS, hPB, hw⟩ := h
  refine ⟨m', hS, hPB, fun b hb => ?_⟩
  rw [← hw b hb]
  rcases thrS_cases hb with ⟨k, hk, h1, rfl⟩ | ho
  · rw [bufMem_frozen B r j hk h1]
    split
    · rw [hfz k hk h1]
    · rename_i hs; rw [Mem.arr64_oob _ _ hs]
  · exact bufMem_owned B r j ho

/-- **The first call**: from entry 1's `PhaseBStart m a v` (with a pending group) and a region
memory `r` with `INIT = 0` and every owned array zero (at its size in `m`), the memory after
`check_b`'s seed copy on `bufMem (bufOf m v) r j` is `ThreadRel` to the worker state `a.worker`
(the witness is `freshMem m`, `PhaseBStart.fresh`), with `INIT = 1`. -/
theorem ThreadRel.first {m : Mem} {a : AState} {v : Word}
    (hS : PhaseBStart pins dn ds fe pend m a v) (hPB : m.arr8 PB = bs.toArray)
    (hne : pend.size ≠ 0) (hok : parCompactOK m 1 = true) (hlt : (m.arr64 OUT).size < 2 ^ 64)
    (r : Mem) (j : Word) (hr : 388 ≤ r.words.size)
    (hz : ∀ b ∈ parOwnedL, r.arr64 b = zeros (m.arr64 b).size) (hI : r.glob INIT = 0) :
    ThreadRel pins dn ds fe pend bs v (seedMem (bufMem (bufOf m v) r j)) a.worker ∧
      (seedMem (bufMem (bufOf m v) r j)).glob INIT = 1 := by
  have hI' : (bufMem (bufOf m v) r j).glob INIT = 0 := hI
  simp only [seedMem, if_pos hI']
  generalize hW : bufMem (bufOf m v) r j = W
  obtain ⟨hseed, h256⟩ := bufImg_seed (v := v) hok hlt
  have hctlf : W.arr64 CTLF = (m.arr64 CTL).extract 0 256 := by
    rw [← hW, bufMem_ctlf, if_pos (show 242 < r.words.size by omega), hseed]
  have hlen : (W.len64 CTLF).toNat = 256 := by
    simp only [Mem.len64, hctlf, size_extract0, Nat.min_eq_left h256]; rfl
  have hctl : W.arr64 CTL = zeros (m.arr64 CTL).size := by
    rw [← hW, bufMem_ctl]; exact hz CTL (by decide)
  rw [hlen]
  refine ⟨⟨freshMem m, hS.fresh hne, by rw [freshMem_arr8]; exact hPB, fun b hb => ?_⟩, ?_⟩
  · rw [show ∀ M : Mem, (M.setG INIT 1).arr64 b = M.arr64 b from fun _ => rfl]
    by_cases hbc : b = CTL
    · subst hbc
      rw [freshMem_arr, if_pos rfl, truncFrozen_ctl]
      apply arr_eq_of_getD
      · rw [size_copy64, hctl, freshCtl_size]; simp [zeros]
      · intro k hk
        rw [size_copy64, hctl] at hk
        simp only [zeros, Array.size_replicate] at hk
        rw [getD_copy64 (by decide) 256 W 0 0 (by simp) (by simp) k, getD_freshCtl, hctl, hctlf]
        simp only [UInt64.toNat_zero, Nat.zero_le, true_and, Nat.zero_add, Nat.sub_zero, zeros,
          Array.size_replicate]
        by_cases h1 : k < 256
        · rw [if_pos ⟨h1, hk⟩, if_pos h1, getD_extract_lt _ _ _ _ (by rw [size_extract0]; omega),
            Nat.zero_add]
        · rw [if_neg (by omega), if_neg h1]
          simp [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, hk]
    · rw [arr64_copy64_ne _ _ _ _ _ _ hbc, ← hW]
      rcases thrS_cases hb with ⟨k, hk, h1, rfl⟩ | ho
      · obtain ⟨-, hz', hc, h388⟩ := frozen_facts hk h1
        rw [bufMem_frozen _ r j hk h1, if_pos (Nat.lt_of_lt_of_le h388 hr), bufImg_trunc hok hlt hk h1, freshMem_arr,
          if_neg hc, if_neg hz']
      · obtain ⟨-, hsrc⟩ := owned_facts ho
        rw [bufMem_owned _ r j ho, hz b ho, freshMem_arr, if_neg hbc,
          if_pos (show b ∈ freshZ from List.mem_cons_of_mem _ ho), truncFrozen_other m b hsrc]
  · simp [Mem.setG]

end start

/-! ## One call -/

section onecall
variable (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
  (ds : Array IDeclaration) (fe : IFEnv) (pend : Array PendingCheck) (bs : List UInt8)

theorem bufMem_view {B : Array Word} {v : Word} (hB : (bufImg B 0).getD 3 0 = v) (r : Mem)
    (j : Word) : ∀ hb : 3 < ((bufMem B r j).arr64 HDRF).size, ((bufMem B r j).arr64 HDRF)[3] = v := by
  intro hb
  have e := bufMem_hdr B r j
  split at e
  · simp only [e] at hb ⊢
    rw [← hB, Array.getD, dif_pos hb]; rfl
  · rw [e] at hb; simp at hb

/-- **A thread's first call** (`ca_check_b(buf, len, j, region, …)` on a fresh region): from
entry 1's `PhaseBStart m a v` (with the pin data, in bounds), the buffer `bufOf m v`, a region
memory `r` with `INIT = 0`, every owned array zero (at its size in `m`) and at least `388` arrays (`checkerTab.nw`), a
run of `check` on `bufMem (bufOf m v) r j` that returns accepts group `j` at `a.worker`, and
leaves `r'` `ThreadRel` to the state after it, with `INIT = 1`. -/
theorem thrCall_first (hP : PhaseBProg (Prog.subPB bs checkerProg)) (hm : mode = .verified)
    {m : Mem} {a : AState} {v : Word} (hS : PhaseBStart pins dn ds fe pend m a v)
    (hPB : m.arr8 PB = bs.toArray) (hok : parCompactOK m 1 = true)
    (hlt : (m.arr64 OUT).size < 2 ^ 64)
    (r : Mem) (hr : 388 ≤ r.words.size) (hz : ∀ b ∈ parOwnedL, r.arr64 b = zeros (m.arr64 b).size)
    (hI : r.glob INIT = 0) (j : Word) (hj : j.toNat < pend.size) (hj62 : j.toNat < 2 ^ 62)
    (n : Nat) (hn : n ≤ 2 ^ 62) {rs : List Word} {r' : Mem}
    (hrun : L.run checkerProg n "check" [] (bufMem (bufOf m v) r j) = .ok (rs, r')) :
    AM.ok (checkPending mode fe (pdAt pend j)) a.worker ∧
      ThreadRel pins dn ds fe pend bs v r' (AM.st (checkPending mode fe (pdAt pend j)) a.worker) ∧
      r'.glob INIT = 1 := by
  obtain ⟨hR, hI'⟩ := ThreadRel.first hS hPB (by omega) hok hlt r j hr hz hI
  exact runThr mode pins dn ds fe pend bs hP hm n hn a.worker v j hj hj62 _ rfl hR hI' rfl rfl
    (bufMem_view (bufImg_hdr hok hlt) r j) hrun

/-- **A thread's later call**: the previous call's final memory `r` `ThreadRel` to `a` with
`INIT = 1`, and its frozen arrays (but the header and the seed) the buffer's images (the buffer is
unchanged), with the view in the buffer's header word `3`: a run of `check` on `bufMem B r j` that
returns accepts group `j` at `a`, and leaves `r'` `ThreadRel` to the state after it, with
`INIT = 1`. -/
theorem thrCall_next (hP : PhaseBProg (Prog.subPB bs checkerProg)) (hm : mode = .verified)
    {B : Array Word} {v : Word} (hB : (bufImg B 0).getD 3 0 = v) {r : Mem} {a : AState}
    (hR : ThreadRel pins dn ds fe pend bs v r a) (hI : r.glob INIT = 1)
    (hfz : ∀ k (hk : k < frozen.length), 1 ≤ k → r.arr64 frozen[k].1 = bufImg B (k + 1))
    (j : Word) (hj : j.toNat < pend.size) (hj62 : j.toNat < 2 ^ 62)
    (n : Nat) (hn : n ≤ 2 ^ 62) {rs : List Word} {r' : Mem}
    (hrun : L.run checkerProg n "check" [] (bufMem B r j) = .ok (rs, r')) :
    AM.ok (checkPending mode fe (pdAt pend j)) a ∧
      ThreadRel pins dn ds fe pend bs v r' (AM.st (checkPending mode fe (pdAt pend j)) a) ∧
      r'.glob INIT = 1 := by
  have hI' : (bufMem B r j).glob INIT ≠ 0 := by rw [bufMem_glob_init, hI]; decide
  have hs := seedMem_of_ne hI'
  refine runThr mode pins dn ds fe pend bs hP hm n hn a v j hj hj62 _ rfl ?_ ?_ rfl rfl
    (bufMem_view hB r j) hrun
  · rw [hs]; exact ThreadRel.next B j hR hfz
  · rw [hs, bufMem_glob_init, hI]

end onecall

end L.Checker
