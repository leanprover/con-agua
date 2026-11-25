module

public import ConAgua.Checker.ParEntryA
public import ConAgua.Checker.PresizeStage
meta import ConAgua.Checker.ParEntryA
meta import ConAgua.Checker.IndArm
meta import ConAgua.Checker.LoopStage
meta import ConAgua.Checker.PipeFinal
meta import ConAgua.Checker.TwinShapeQuot
meta import ConAgua.Checker.PresizeStage
import all Init.Data.Repr
import ConAgua.Checker.LoopProgTac
import ConAgua.Checker.RomProg
import ConAgua.Checker.RomProgInit
public import ConAgua.Checker.BuildStage

@[expose] public section

/-!
# Entry 1 at the checker's program: `checkA_run` (lane parmode)

docs/design/parmode.md, "Step 4" (a). A run of `check` from the loaded memory with the mode word
`MODE` set to `1` or `3` (`loadMemM b pb sz w`, what the stubs `ca_start_a`/`ca_start_a0`
hand it) that returns anything but `1` (a line that did not scan):

* the twin's stages before the jobs ran and built the stream index (`PhaseA b`: `TwinPrefix` and
  `buildIndex ds sE = .ok (.ok I, sF)`);
* the memory after the index build, `m`, is `FoldAt … m` (`Checker/BuildStage.lean`: `BuildR` at
  `I`, `R7` before the build, the build's write set), and the final memory is the frozen
  buffer's, `parCompactMem m (modeFlag w)`;
* the result is `2^63 + |ds|`.

The stages are `stageSpecs_of_rels` at `checkerRels`, except the
first four, which start from the loaded memory with the mode word set: no relation reads a global
(`R1`‥`R3` name the loaded memory only through its arrays), so the proofs of `cap_check` and
`pb_check` are those of `capStage_checker`, `pbStage_checker` at `loadMemM`; the tables' presize
and `intern_reserved_pins` after it are `presizeStage` and `irpStage_ps` (`PresizeStage.lean`). The
index build is `buildStage_checker` (`BuildStage.lean`).
-/

open ConRon.Arena ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Checker

open L L.Arena L.Front L.Rom L.Compiler ConAgua.Final

/-! ## The first two stages from the loaded memory with the mode word set -/

theorem capStage_setG (b pb : ByteArray) (sz : TieredArray → Nat) (hs : ∀ s, sz s < 2 ^ 64) (w : Word) :
    RelSpec checkerProg "cap_check" (· = loadMemM b pb sz w)
      fun _ m => m = loadMemM b pb sz w ∧ CapsOK (loadMem b pb sz) := by
  intro n _hn s₀ hm
  refine triple_post (capCheck_spec checkerProg checkerProg_capCheck n s₀
    (hm ▸ loadMem_wordsFit b pb sz hs)) fun _ s' ⟨h1, h2, h3⟩ => ⟨h1, ?_, ?_⟩
  · rw [h2, hm]
  · rw [hm] at h3; exact h3

theorem pbStage_setG (b pb : ByteArray) (sz : TieredArray → Nat) (hpb : pb.size < 2 ^ 63) (w : Word) :
    RelSpec checkerProg "pb_check" (fun m => m = loadMemM b pb sz w ∧ CapsOK (loadMem b pb sz))
      fun _ m => m = loadMemM b pb sz w ∧ CapsOK (loadMem b pb sz) ∧ PbPre pb := by
  intro n _hn s₀ ⟨hm, hc⟩
  refine triple_post (checkerProg_pbCheck_PB pb.data.toList (by simpa [RomOK] using hpb) n s₀
    (by rw [hm]; exact loadMem_pb b pb sz)) fun _ s' ⟨h1, h2, h3⟩ => ⟨h1, ?_, hc, h3⟩
  rw [h2, hm]

/-! ## The lookups -/

theorem checkerProg_fz : ∀ i < frozen.length, checkerProg.lookup (fzName i) = some (fzF i) := by
  rw [frozen_length]
  intro i hi
  match i, hi with
  | 0, _ => show checkerProg.lookup "fz_0" = some (fzF 0); chk_lk
  | 1, _ => show checkerProg.lookup "fz_1" = some (fzF 1); chk_lk
  | 2, _ => show checkerProg.lookup "fz_2" = some (fzF 2); chk_lk
  | 3, _ => show checkerProg.lookup "fz_3" = some (fzF 3); chk_lk
  | 4, _ => show checkerProg.lookup "fz_4" = some (fzF 4); chk_lk
  | 5, _ => show checkerProg.lookup "fz_5" = some (fzF 5); chk_lk
  | 6, _ => show checkerProg.lookup "fz_6" = some (fzF 6); chk_lk
  | 7, _ => show checkerProg.lookup "fz_7" = some (fzF 7); chk_lk
  | 8, _ => show checkerProg.lookup "fz_8" = some (fzF 8); chk_lk
  | 9, _ => show checkerProg.lookup "fz_9" = some (fzF 9); chk_lk
  | 10, _ => show checkerProg.lookup "fz_10" = some (fzF 10); chk_lk
  | 11, _ => show checkerProg.lookup "fz_11" = some (fzF 11); chk_lk
  | 12, _ => show checkerProg.lookup "fz_12" = some (fzF 12); chk_lk
  | 13, _ => show checkerProg.lookup "fz_13" = some (fzF 13); chk_lk
  | 14, _ => show checkerProg.lookup "fz_14" = some (fzF 14); chk_lk
  | 15, _ => show checkerProg.lookup "fz_15" = some (fzF 15); chk_lk
  | 16, _ => show checkerProg.lookup "fz_16" = some (fzF 16); chk_lk
  | 17, _ => show checkerProg.lookup "fz_17" = some (fzF 17); chk_lk
  | 18, _ => show checkerProg.lookup "fz_18" = some (fzF 18); chk_lk
  | 19, _ => show checkerProg.lookup "fz_19" = some (fzF 19); chk_lk
  | 20, _ => show checkerProg.lookup "fz_20" = some (fzF 20); chk_lk
  | 21, _ => show checkerProg.lookup "fz_21" = some (fzF 21); chk_lk
  | 22, _ => show checkerProg.lookup "fz_22" = some (fzF 22); chk_lk
  | 23, _ => show checkerProg.lookup "fz_23" = some (fzF 23); chk_lk
  | 24, _ => show checkerProg.lookup "fz_24" = some (fzF 24); chk_lk
  | 25, _ => show checkerProg.lookup "fz_25" = some (fzF 25); chk_lk
  | 26, _ => show checkerProg.lookup "fz_26" = some (fzF 26); chk_lk
  | 27, _ => show checkerProg.lookup "fz_27" = some (fzF 27); chk_lk
  | 28, _ => show checkerProg.lookup "fz_28" = some (fzF 28); chk_lk
  | 29, _ => show checkerProg.lookup "fz_29" = some (fzF 29); chk_lk
  | 30, _ => show checkerProg.lookup "fz_30" = some (fzF 30); chk_lk
  | 31, _ => show checkerProg.lookup "fz_31" = some (fzF 31); chk_lk
  | 32, _ => show checkerProg.lookup "fz_32" = some (fzF 32); chk_lk
  | 33, _ => show checkerProg.lookup "fz_33" = some (fzF 33); chk_lk
  | 34, _ => show checkerProg.lookup "fz_34" = some (fzF 34); chk_lk
  | 35, _ => show checkerProg.lookup "fz_35" = some (fzF 35); chk_lk
  | 36, _ => show checkerProg.lookup "fz_36" = some (fzF 36); chk_lk
  | 37, _ => show checkerProg.lookup "fz_37" = some (fzF 37); chk_lk
  | 38, _ => show checkerProg.lookup "fz_38" = some (fzF 38); chk_lk
  | 39, _ => show checkerProg.lookup "fz_39" = some (fzF 39); chk_lk
  | 40, _ => show checkerProg.lookup "fz_40" = some (fzF 40); chk_lk
  | 41, _ => show checkerProg.lookup "fz_41" = some (fzF 41); chk_lk
  | 42, _ => show checkerProg.lookup "fz_42" = some (fzF 42); chk_lk
  | 43, _ => show checkerProg.lookup "fz_43" = some (fzF 43); chk_lk
  | 44, _ => show checkerProg.lookup "fz_44" = some (fzF 44); chk_lk
  | 45, _ => show checkerProg.lookup "fz_45" = some (fzF 45); chk_lk
  | 46, _ => show checkerProg.lookup "fz_46" = some (fzF 46); chk_lk
  | 47, _ => show checkerProg.lookup "fz_47" = some (fzF 47); chk_lk
  | 48, _ => show checkerProg.lookup "fz_48" = some (fzF 48); chk_lk
  | 49, _ => show checkerProg.lookup "fz_49" = some (fzF 49); chk_lk
  | 50, _ => show checkerProg.lookup "fz_50" = some (fzF 50); chk_lk
  | 51, _ => show checkerProg.lookup "fz_51" = some (fzF 51); chk_lk
  | 52, _ => show checkerProg.lookup "fz_52" = some (fzF 52); chk_lk
  | 53, _ => show checkerProg.lookup "fz_53" = some (fzF 53); chk_lk
  | 54, _ => show checkerProg.lookup "fz_54" = some (fzF 54); chk_lk
  | 55, _ => show checkerProg.lookup "fz_55" = some (fzF 55); chk_lk
  | 56, _ => show checkerProg.lookup "fz_56" = some (fzF 56); chk_lk
  | 57, _ => show checkerProg.lookup "fz_57" = some (fzF 57); chk_lk
  | 58, _ => show checkerProg.lookup "fz_58" = some (fzF 58); chk_lk
  | 59, _ => show checkerProg.lookup "fz_59" = some (fzF 59); chk_lk
  | 60, _ => show checkerProg.lookup "fz_60" = some (fzF 60); chk_lk
  | 61, _ => show checkerProg.lookup "fz_61" = some (fzF 61); chk_lk
  | 62, _ => show checkerProg.lookup "fz_62" = some (fzF 62); chk_lk
  | 63, _ => show checkerProg.lookup "fz_63" = some (fzF 63); chk_lk
  | 64, _ => show checkerProg.lookup "fz_64" = some (fzF 64); chk_lk
  | 65, _ => show checkerProg.lookup "fz_65" = some (fzF 65); chk_lk
  | 66, _ => show checkerProg.lookup "fz_66" = some (fzF 66); chk_lk
  | 67, _ => show checkerProg.lookup "fz_67" = some (fzF 67); chk_lk
  | 68, _ => show checkerProg.lookup "fz_68" = some (fzF 68); chk_lk
  | 69, _ => show checkerProg.lookup "fz_69" = some (fzF 69); chk_lk
  | 70, _ => show checkerProg.lookup "fz_70" = some (fzF 70); chk_lk
  | 71, _ => show checkerProg.lookup "fz_71" = some (fzF 71); chk_lk
  | _ + 72, h => exact absurd h (by omega)

/-! ## Entry 1 -/

/-- A run as a triple (lane parallel's). -/
theorem run_post {p : Prog} {N : Nat} {f : FnName} {m m' : Mem} {rs : List Word}
    {Q : List Word → Mem → Prop} (hrun : L.run p N f [] m = .ok (rs, m'))
    (h : ⦃fun s => s = { mem := m, loc := Locals.init [] }⦄ invoke p (exec p N) f []
      ⦃fun r s => Q r s.mem; ⊤⦄) : Q rs m' := by
  simp only [L.run] at hrun
  cases hr : (invoke p (exec p N) f []).run { mem := m, loc := Locals.init [] } with
  | error e => rw [hr] at hrun; cases hrun
  | ok v =>
    rw [hr] at hrun
    obtain ⟨rs', s'⟩ := v
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact M.of_run (P := fun s => s = _) rfl hr h

/-- **Entry 1 in L**: a run of `check` from the loaded memory with the mode word `w = 1` (images
and header) or `w = 3` (the header only) that returns anything but `1` is an accepting twin
phase A (`PhaseA b`: the stages and the stream index) whose relations hold at the memory `m`
after the index build (`FoldAt`); the final memory is the frozen buffer's,
`parCompactMem m (modeFlag w)` (in bounds), and the result is `2^63 + |ds|`. -/
theorem checkA_run (b pb : ByteArray) (sz : TieredArray → Nat) (hin : InputsOK b pb sz) (w : Word)
    (hw : w = 1 ∨ w = 3) (N : Nat) (hN : N < 2 ^ 62) (rs : List Word) (m' : Mem)
    (hrun : L.run checkerProg N "check" [] (loadMemM b pb sz w) = .ok (rs, m'))
    (hr : rs.headD 0 ≠ 1) :
    ∃ (PA : PhaseA b) (m₇ m : Mem), FoldAt b pb sz PA m₇ m ∧
      parCompactOK m (modeFlag w) = true ∧ m' = parCompactMem m (modeFlag w) ∧
      rs.headD 0 = 9223372036854775808 + UInt64.ofNat PA.ds.size := by
  let r := checkerRels b pb sz
  obtain ⟨-, -, -, s4, s5, s6, s7⟩ := stageSpecs_of_rels checkerRels checker_capStage
    checker_pbStage checker_irpStage checker_preludeStage checker_frontStage checker_prepareStage
    checker_pinsStage b pb sz hin
  have s1 := StageSpec.of_rel (X := Unit) (fun _ => _) (fun _ => _)
    (fun _ => capStage_setG b pb sz hin.2.2.2 w) fun m hm => ⟨(), hm, fun _ _ h => h⟩
  have s2 := StageSpec.of_rel (X := Unit) (fun _ => _) (fun _ => _)
    (fun _ => pbStage_setG b pb sz hin.2.2.1 w) fun m hm => ⟨(), hm, fun _ _ h => h⟩
  have s2p := presizeStage b pb sz w (p := checkerProg) (by chk_lk) (by chk_lk) (by chk_lk)
    (by chk_lk) (by chk_lk)
  have s3 : StageSpec checkerProg "intern_reserved_pins" (PsPre b pb sz w)
      (fun _ => Q3 b r) := StageSpec.of_rel (X := Unit) (fun _ => _) (fun _ => _)
    (fun _ => irpStage_ps b pb sz w hin.2.2.1) fun m hm => ⟨(), hm, fun _ _ h => h⟩
  have hla : checkerProg.lookup "check_a" = some checkAL := by chk_lk
  have hlc : checkerProg.lookup "check" = some checkL := by chk_lk
  have hpc : checkerProg.lookup "par_compact" = some parCompactL := by chk_lk
  have hmode : (loadMemM b pb sz w).glob MODE = w := by simp [loadMemM, Mem.setG]
  let P : Word → Mem → Prop := fun x m'' => x ≠ 1 → PostPC (modeFlag w) (FoldA b pb sz) m'' ∧
    ∀ h : 0 < (m''.arr64 L.Front.DECL).size, x = (9223372036854775808 : Word) + (m''.arr64 L.Front.DECL)[0]
  cases N with
  | zero =>
    exfalso
    refine run_post (Q := fun _ _ => False) hrun ?_
    rw [invoke_eq _ hlc]
    simp only [callFn]
    vcgen [exec] <;> grind
  | succ n =>
    have hn : n ≤ 2 ^ 62 := by omega
    let s₀ : St := { mem := loadMemM b pb sz w, loc := Locals.init [] }
    have hA : ∀ (s₁ : St) (c : Word), ⦃fun s => s = s₁⦄
        invoke checkerProg (exec checkerProg n) "check_a" [c]
        ⦃fun r s' => s₁.mem = s₀.mem → c = modeFlag (s₀.mem.glob MODE) → P (r.headD 0) s'.mem; ⊤⦄ := by
      intro s₁ c
      refine triple_post (checkA_of_stages (Q0 := (· = loadMemM b pb sz w)) hla hpc checkerProg_fz
        s1 s2 s2p s3 s4 s5 s6 s7 (buildStage_checker b pb sz hin.2.2.1 hin.2.2.2) c n hn s₁) ?_
      intro x s' h e ec
      have ec' : c = modeFlag w := by rw [ec, hmode]
      subst ec'
      exact h e
    have H := run_post (Q := fun x m'' => (s₀.mem.glob MODE = 1 ∨ s₀.mem.glob MODE = 3) →
      P (x.headD 0) m'') hrun (check_dispatchA hlc n s₀ P hA)
    obtain ⟨⟨m, ⟨PA, m₇, hF⟩, hok, rfl⟩, hval⟩ := H (by rw [hmode]; exact hw) hr
    refine ⟨PA, m₇, m, hF, hok, rfl, ?_⟩
    have hFo := parCompactMem_out m (modeFlag w)
    have hD0 : 0 < (m.arr64 L.Front.DECL).size := by have := hF.build.decls.room; omega
    have eD : (parCompactMem m (modeFlag w)).arr64 L.Front.DECL = m.arr64 L.Front.DECL :=
      hFo.arr _ (by decide)
    have hD0' : 0 < ((parCompactMem m (modeFlag w)).arr64 L.Front.DECL).size := by rw [eD]; exact hD0
    have hc := hF.build.decls.count
    rw [Array.getElem?_eq_getElem hD0, Option.getD_some] at hc
    have e0 : ((parCompactMem m (modeFlag w)).arr64 L.Front.DECL)[0]'hD0' = (m.arr64 L.Front.DECL)[0] := by
      simp only [eD]
    rw [hval hD0', e0, ← hc, UInt64.ofNat_toNat]

end L.Checker
