module

public import ConAgua.Verdict.FrontStageE
public import ConAgua.Checker.CompareChain5
public import ConAgua.Final.CompareTwinVerdict
public import ConAgua.Final.CmpAbi
public import ConAgua.Checker.ProgTab
import ConAgua.Verdict.FrontSafeE
import ConAgua.Compiler.Abi
import ConAgua.Final.DrvFinal
import ConAgua.Checker.AsmFinal
import ConAgua.Checker.CheckARun
import ConAgua.Checker.LoopProgTac
import ConAgua.Checker.NoVerdictClosed
import ConAgua.Checker.PreludeRef
import ConAgua.Checker.RomProgInit
import ConAgua.Front.ChunkBridge
import ConAgua.Front.FrontRunRef
import ConAgua.Final.CmpChain
import all ConAgua.Checker.Entry
import all ConAgua.Checker.CompareEntry

@[expose] public section

/-!
# The compared run's modes `4`, `5`, `6` fail only where the twin does (lane compare2, helper
compare2-verdict)

Mode `4` (`check_c1`) and mode `5` (`check_c2`) run the stages of entry 1: of their callees only
`builtin_prelude` and `front_run` can fail with a class other than `0` (the others are in `nvFns`,
`checkerProg_nv`), and their error halves (`FrontStageE.lean`) claim the twin's prelude or parse
failing, the challenge's (`TwinCompareVerdict.prelude`, `.frontC`) or the solution's (`.frontS`,
at `CmpAt4`'s twin prefix). Mode `6` (`check_c3`) is in `nvFns` itself: it claims nothing.

* `cmpV_a4`: a failing mode-`4` run of class other than `0` is `TwinCompareVerdict`;
* `cmpV_a5`: so is a failing mode-`5` run after mode `4` returned `2^63`;
* `cmpV_a6`: a failing mode-`6` run has class `0`.
-/

namespace L.Checker

open L L.Arena L.Front L.Rom L.Compiler ConAgua.Final
open ConRon.Arena ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

/-! ## The stages' error specs at the compared run -/

/-- `builtin_prelude`'s error half, claiming the compared run's prelude failing. -/
theorem cmpV_preludeStageE (bC bS pb : ByteArray) (sz : TieredArray → Nat) (hin : InputsOK bC pb sz) :
    StageSpecE checkerProg "builtin_prelude" [] (Q3 bC (checkerRels bC pb sz))
      (TwinCompareVerdict bC bS) := by
  intro n _hn s₀
  refine M.triple_of_run' (fun _ _ _ _ _ => trivial) fun s e hs hr hQ hk => ?_
  subst hs
  obtain ⟨sA, hA, h3⟩ := hQ
  have h3 : R3 (loadMem bC pb sz) s.mem pb sA := h3
  have hc := CapsOK.keep h3.since.keep h3.since.caps
  exact TwinCompareVerdict.prelude hA (RefC.run_err (builtinPrelude_specE checkerProg checkerProg_builtin n
      ⟨s.mem, Locals.init []⟩) (fun _ h0 h => absurd h0 h) checkerProg_nv trivial
    (builtinPrelude_ref hin.1 sA n
      ⟨h3.arena, h3.sdr, h3.twin, Nat.lt_of_lt_of_le (by decide) hc.2.1, h3.mode⟩)
    (L.Front.callE_of_run_err (s := s) hr) hk)

/-- `front_run`'s error half at the `R4` of the bytes `b`: the twin's parse of `[b]` from `sB`
fails at that class. -/
theorem cmpV_frontRunE {b pb : ByteArray} {sz : TieredArray → Nat} (h64 : System.Platform.numBits = 64)
    (hb : b.size < 2 ^ 63) {pre : PreludeIx} {sB : AState} {n : Nat} {s : St} {e : Err}
    (h4 : R4 (loadMem b pb sz) s.mem pb pre sB)
    (hr : (invoke checkerProg (exec checkerProg n) "front_run" []).run s = .error e) (hk : e.cls ≠ 0) :
    TwinFailsV (parseChunks [b]) sB e.cls := by
  have hm : s.mem.arr8 IN = b.data := by rw [h4.since.keep.arr8]; exact loadMem_in b pb sz
  have hf := frontRun_errClaim pre.decls b h64 hb (safeLink h64 b hb) n s.mem sB
    ⟨hm, h4.arena, h4.sdr, h4.twin.ok, h4.twin.off, h4.twin.pins, h4.rok, h4.mode⟩
    (L.Front.callE_of_run_err hr) hk
  have hu : b.size < USize.size := by
    rw [show USize.size = 2 ^ 64 by simp [USize.size, h64]]; omega
  rw [ConAgua.Front.ChunkBridge.parseChunks_single b hu]
  exact hf

/-- The challenge's `front_run`'s error half. -/
theorem cmpV_frontCStageE (bC bS pb : ByteArray) (sz : TieredArray → Nat) (hin : InputsOK bC pb sz) :
    StageSpecE checkerProg "front_run" [] (Q4 bC (checkerRels bC pb sz)) (TwinCompareVerdict bC bS) := by
  intro n _hn s₀
  refine M.triple_of_run' (fun _ _ _ _ _ => trivial) fun s e hs hr hQ hk => ?_
  subst hs
  obtain ⟨sA, pre, sB, hA, hB, h4⟩ := hQ
  exact TwinCompareVerdict.frontC hA hB (cmpV_frontRunE hin.1 hin.2.1 h4 hr hk)

/-- The solution's `front_run`'s error half, before it (`QS4`). -/
theorem cmpV_frontSStageE (bC bS pb : ByteArray) (sz : TieredArray → Nat)
    (h64 : System.Platform.numBits = 64) (hb : bS.size < 2 ^ 63) :
    StageSpecE checkerProg "front_run" [] (QS4 bC bS pb sz) (TwinCompareVerdict bC bS) := by
  intro n _hn s₀
  refine M.triple_of_run' (fun _ _ _ _ _ => trivial) fun s e hs hr hQ hk => ?_
  subst hs
  obtain ⟨sA, pre, sB, rC, sC, ⟨hA, hB, hC⟩, h4, -⟩ := hQ
  exact TwinCompareVerdict.frontS hA hB hC (cmpV_frontRunE h64 hb h4 hr hk)

/-! ## The entries' errors from their stages -/

/-- **`check_c1()`'s error from its stages.** -/
theorem checkC1_err_of_stages {p : Prog} (hp : p.lookup "check_c1" = some checkC1L)
    {fs : List FnName} (hnv : closedNV p fs = true)
    (hm1 : "cap_check" ∈ fs) (hm2 : "pb_check" ∈ fs) (hm2p : "presize_tables" ∈ fs)
    (hm3 : "intern_reserved_pins" ∈ fs) (hm6 : "cmp_stash" ∈ fs)
    {Q0 Q1 Q2 Q2p Q3 Q4 : Mem → Prop} {V : Word → Prop}
    (h1 : StageSpec p "cap_check" Q0 fun _ => Q1)
    (h2 : StageSpec p "pb_check" Q1 fun _ => Q2)
    (h2p : StageSpec p "presize_tables" Q2 fun _ => Q2p)
    (h3 : StageSpec p "intern_reserved_pins" Q2p fun _ => Q3)
    (h4 : StageSpec p "builtin_prelude" Q3 fun _ => Q4)
    (e4 : StageSpecE p "builtin_prelude" [] Q3 V)
    (e5 : StageSpecE p "front_run" [] Q4 V)
    (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_c1" []
    ⦃fun _ _ => True; fun e => Q0 s₀.mem → e.cls ≠ 0 → V e.cls⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkC1L]
  cases n with
  | zero => vcgen [exec] <;> simp_all
  | succ n =>
    have hn' : n ≤ 2 ^ 62 := by omega
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      (fun s => Triple.and_err (h1 n hn' s) (nv_at hnv hm1 n [] s)),
      (fun s => Triple.and_err (h2 n hn' s) (nv_at hnv hm2 n [] s)),
      (fun s => Triple.and_err (h2p n hn' s) (nv_at hnv hm2p n [] s)),
      (fun s => Triple.and_err (h3 n hn' s) (nv_at hnv hm3 n [] s)),
      (fun s => Triple.and_err (h4 n hn' s) (e4 n hn' s)),
      (e5 n hn' ·), (nv_at hnv hm6 n [] ·)]
    all_goals (try simp only [L.St.setLoc_mem,
      St.setLocs_cons, St.setLocs_nil, St.setLoc_loc, Cmp.eval, ite_true,
      bne_iff_ne, ne_eq, Decidable.not_not] at *)
    all_goals clear h1 h2 h2p h3 h4 e4 e5 hp
    all_goals grind (gen := 30) (ematch := 40) [lang_grind, Locals.init_cons_zero]

/-- **`check_c2()`'s error from its stages**: only the solution's `front_run` claims. -/
theorem checkC2_err_of_stages {p : Prog} (hp : p.lookup "check_c2" = some checkC2L)
    {fs : List FnName} (hnv : closedNV p fs = true)
    (hm6 : "prepare_prelude" ∈ fs) (hm7 : "intern_all_pins" ∈ fs) (hm8 : "par_compact" ∈ fs)
    (hm9 : "build_index" ∈ fs) {Q4 : Mem → Prop} {V : Word → Prop}
    (e5 : StageSpecE p "front_run" [] Q4 V)
    (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_c2" []
    ⦃fun _ _ => True; fun e => Q4 s₀.mem → e.cls ≠ 0 → V e.cls⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkC2L]
  cases n with
  | zero => vcgen [exec] <;> simp_all
  | succ n =>
    have hn' : n ≤ 2 ^ 62 := by omega
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      (e5 n hn' ·), (nv_at hnv hm6 n [] ·), (nv_at hnv hm7 n [] ·),
      (fun v s => nv_at hnv hm9 n [v] s), (fun v s => nv_at hnv hm8 n [v] s)]
    all_goals (try simp only [L.St.setLoc_mem,
      St.setLocs_cons, St.setLocs_nil, St.setLoc_loc, Cmp.eval, ite_true,
      UInt64.toNat_zero, bne_iff_ne, ne_eq, Decidable.not_not] at *)
    all_goals clear e5 hp
    all_goals grind (gen := 30) (ematch := 40) [lang_grind, Locals.init_cons_zero]

/-- **`check` fails only as the compared entry its mode word names does**: with the mode word
`4`, `5` or `6`, as `check_c1`, `check_c2`, `check_c3(0)`. -/
theorem check_err_dispatchC {p : Prog} (hp : p.lookup "check" = some checkL) (n : Nat) (s₀ : St)
    (E : Err → Prop)
    (h1 : ∀ s₁ : St, ⦃fun s => s = s₁⦄ invoke p (exec p n) "check_c1" []
      ⦃fun _ _ => True; fun e => s₁.mem = s₀.mem → s₀.mem.glob MODE = 4 → E e⦄)
    (h2 : ∀ s₁ : St, ⦃fun s => s = s₁⦄ invoke p (exec p n) "check_c2" []
      ⦃fun _ _ => True; fun e => s₁.mem = s₀.mem → s₀.mem.glob MODE = 5 → E e⦄)
    (h3 : ∀ s₁ : St, ⦃fun s => s = s₁⦄ invoke p (exec p n) "check_c3" [0]
      ⦃fun _ _ => True; fun e => s₁.mem = s₀.mem → s₀.mem.glob MODE = 6 → E e⦄)
    (hE : E (.abort 0)) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check" []
    ⦃fun _ _ => True; fun e => (s₀.mem.glob MODE = 4 ∨ s₀.mem.glob MODE = 5 ∨
      s₀.mem.glob MODE = 6) → E e⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, (h1 ·), (h2 ·), (h3 ·),
    (L.invoke_loc p (exec p n) "check_a" [·] ·), (L.invoke_loc p (exec p n) "check_b" [] ·),
    (L.invoke_loc p (exec p n) "check_c3" [1] ·)]
  all_goals (try simp only at *)
  all_goals grind [lang_grind]

/-! ## The modes' claims -/

/-- **Mode `4`'s verdict claim**: a failing run of `check` from mode `4`'s memory with a class
other than `0` is the twin's compared run failing with that class. -/
theorem cmpV_a4 (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64) (hbC : bC.size < 2 ^ 63)
    (hpb : pb.size < 2 ^ 63) (e : Err)
    (hrun : cmpRun checkerProg (cmpM4 checkerTab MODE bC pb) = .error e) (hk : e.cls ≠ 0) :
    TwinCompareVerdict bC bS e.cls := by
  have hsz : ∀ s, abiSz checkerTab s < 2 ^ 64 := fun s => by
    have := abiSz_le checkerTab_abiOk s; simp only [abiWords] at this; omega
  generalize hsz' : abiSz checkerTab = sz at hsz
  have hin : InputsOK bC pb sz := ⟨h64, hbC, hpb, hsz⟩
  obtain ⟨-, -, -, s4, -, -, -⟩ := stageSpecs_of_rels checkerRels checker_capStage
    checker_pbStage checker_irpStage checker_preludeStage checker_frontStage checker_prepareStage
    checker_pinsStage bC pb sz hin
  have s1 := StageSpec.of_rel (X := Unit) (fun _ => _) (fun _ => _)
    (fun _ => capStage_setG bC pb sz hin.2.2.2 4) fun m hm => ⟨(), hm, fun _ _ h => h⟩
  have s2 := StageSpec.of_rel (X := Unit) (fun _ => _) (fun _ => _)
    (fun _ => pbStage_setG bC pb sz hin.2.2.1 4) fun m hm => ⟨(), hm, fun _ _ h => h⟩
  have s2p := presizeStage bC pb sz 4 (p := checkerProg) (by chk_lk) (by chk_lk) (by chk_lk)
    (by chk_lk) (by chk_lk)
  have s3 : StageSpec checkerProg "intern_reserved_pins" (PsPre bC pb sz 4)
      (fun _ => Q3 bC (checkerRels bC pb sz)) := StageSpec.of_rel (X := Unit) (fun _ => _) (fun _ => _)
    (fun _ => irpStage_ps bC pb sz 4 hin.2.2.1) fun m hm => ⟨(), hm, fun _ _ h => h⟩
  have hc1 : checkerProg.lookup "check_c1" = some checkC1L := by chk_lk
  have hlc : checkerProg.lookup "check" = some checkL := by chk_lk
  have hmode : (cmpM4 checkerTab MODE bC pb).glob MODE = 4 := by simp [cmpM4, Mem.setG]
  have hr := run_err hrun
  have hN : abiFuel = (abiFuel - 1) + 1 := by simp [abiFuel]
  rw [hN] at hr
  let n := abiFuel - 1
  have hn : n ≤ 2 ^ 62 := by simp [n, abiFuel]
  let s₀ : St := { mem := cmpM4 checkerTab MODE bC pb, loc := Locals.init [] }
  have H := M.of_run_err (P := fun s => s = s₀) rfl hr
    (check_err_dispatchC hlc n s₀ (fun e => e.cls ≠ 0 → TwinCompareVerdict bC bS e.cls)
      (fun s₁ => M.triple_of_run' (fun _ _ _ _ _ => trivial) fun s e' hs hr' hm _ => by
        subst hs
        exact M.of_run_err (P := fun t => t = s) rfl hr'
          (checkC1_err_of_stages (Q0 := (· = loadMemM bC pb sz 4)) hc1 checkerProg_nv
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) s1 s2 s2p s3 s4 (cmpV_preludeStageE bC bS pb sz hin)
            (cmpV_frontCStageE bC bS pb sz hin) n hn s) (by rw [hm, ← hsz']; rfl))
      (fun s₁ => M.triple_of_run' (fun _ _ _ _ _ => trivial) fun _ _ _ _ _ h5 => by
        rw [hmode] at h5; exact absurd h5 (by decide))
      (fun s₁ => M.triple_of_run' (fun _ _ _ _ _ => trivial) fun _ _ _ _ _ h6 => by
        rw [hmode] at h6; exact absurd h6 (by decide))
      (fun h0 => absurd (by decide) h0))
  exact H (.inl hmode) hk

/-- **Mode `5`'s verdict claim**: after mode `4` returned `2^63`, a failing run of `check` from
mode `5`'s memory with a class other than `0` is the twin's compared run failing with that class. -/
theorem cmpV_a5 (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64) (hbC : bC.size < 2 ^ 63)
    (hbS : bS.size < 2 ^ 63) (hpb : pb.size < 2 ^ 63) (rs4 : List Word) (m4 : Mem)
    (h4 : cmpRun checkerProg (cmpM4 checkerTab MODE bC pb) = .ok (rs4, m4))
    (hge4 : 2 ^ 63 ≤ (rs4.getD 0 0).toNat) (e : Err)
    (hrun : cmpRun checkerProg (cmpM5 MODE m4 bS) = .error e) (hk : e.cls ≠ 0) :
    TwinCompareVerdict bC bS e.cls := by
  have hsz : ∀ s, abiSz checkerTab s < 2 ^ 64 := fun s => by
    have := abiSz_le checkerTab_abiOk s; simp only [abiWords] at this; omega
  have hN : abiFuel < 2 ^ 62 := by simp [abiFuel]
  have hr4 : rs4.headD 0 ≠ 1 := fun e => by rw [L.getD_zero, e] at hge4; simp at hge4
  obtain ⟨-, hA4⟩ := checkC1_run bC bS pb _ ⟨h64, hbC, hpb, hsz⟩ abiFuel hN rs4 m4 h4 hr4
  have hQ4 : QS4 bC bS pb (abiSz checkerTab) (cmpM5 MODE m4 bS) := by
    obtain ⟨sA, pre, sB, rC, sC, hpx, hR4, hst⟩ := hA4
    exact ⟨sA, pre, sB, rC, sC, hpx, hR4.frame0 (memFrame_setG _ _ _) rfl, ⟨hst.decls, hst.rok⟩⟩
  have hc2 : checkerProg.lookup "check_c2" = some checkC2L := by chk_lk
  have hlc : checkerProg.lookup "check" = some checkL := by chk_lk
  have hmode : (cmpM5 MODE m4 bS).glob MODE = 5 := by simp [cmpM5, Mem.setG]
  have hr := run_err hrun
  have hN' : abiFuel = (abiFuel - 1) + 1 := by simp [abiFuel]
  rw [hN'] at hr
  let n := abiFuel - 1
  have hn : n ≤ 2 ^ 62 := by simp [n, abiFuel]
  let s₀ : St := { mem := cmpM5 MODE m4 bS, loc := Locals.init [] }
  have H := M.of_run_err (P := fun s => s = s₀) rfl hr
    (check_err_dispatchC hlc n s₀ (fun e => e.cls ≠ 0 → TwinCompareVerdict bC bS e.cls)
      (fun s₁ => M.triple_of_run' (fun _ _ _ _ _ => trivial) fun _ _ _ _ _ h4' => by
        rw [hmode] at h4'; exact absurd h4' (by decide))
      (fun s₁ => M.triple_of_run' (fun _ _ _ _ _ => trivial) fun s e' hs hr' hm _ => by
        subst hs
        exact M.of_run_err (P := fun t => t = s) rfl hr'
          (checkC2_err_of_stages hc2 checkerProg_nv (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel)
            (cmpV_frontSStageE bC bS pb (abiSz checkerTab) h64 hbS) n hn s) (by rw [hm]; exact hQ4))
      (fun s₁ => M.triple_of_run' (fun _ _ _ _ _ => trivial) fun _ _ _ _ _ h6 => by
        rw [hmode] at h6; exact absurd h6 (by decide))
      (fun h0 => absurd (by decide) h0))
  exact H (.inr (.inl hmode)) hk

/-- **Mode `6` claims nothing**: `check_c3` is outside the verdict closure, so a failing run of
`check` with the mode word `6` fails with class `0`. -/
theorem cmpV_a6 {m : Mem} (hmode : m.glob MODE = 6) {e : Err}
    (hrun : cmpRun checkerProg m = .error e) : e.cls = 0 := by
  have hlc : checkerProg.lookup "check" = some checkL := by chk_lk
  have hr := run_err hrun
  have hN' : abiFuel = (abiFuel - 1) + 1 := by simp [abiFuel]
  rw [hN'] at hr
  let n := abiFuel - 1
  let s₀ : St := { mem := m, loc := Locals.init [] }
  have H := M.of_run_err (P := fun s => s = s₀) rfl hr
    (check_err_dispatchC hlc n s₀ (fun e => e.cls = 0)
      (fun s₁ => M.triple_of_run' (fun _ _ _ _ _ => trivial) fun _ _ _ _ _ h4' => by
        rw [hmode] at h4'; exact absurd h4' (by decide))
      (fun s₁ => M.triple_of_run' (fun _ _ _ _ _ => trivial) fun _ _ _ _ _ h5 => by
        rw [hmode] at h5; exact absurd h5 (by decide))
      (fun s₁ => M.triple_of_run' (fun _ _ _ _ _ => trivial) fun s e' hs hr' _ _ =>
        M.of_run_err (P := fun t => t = s₁) hs hr' (nv_at checkerProg_nv (f := "check_c3")
          (by decide +kernel) n [0] s₁))
      rfl)
  exact H (.inr (.inr hmode))

end L.Checker
