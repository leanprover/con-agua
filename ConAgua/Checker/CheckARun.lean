import ConAgua.Checker.ParEntryA
import ConAgua.Checker.IndArm
import ConAgua.Arena.PhaseAEntry
import ConAgua.Checker.LoopStage
import ConAgua.Checker.PipeFinal
import ConAgua.Checker.TwinShapeQuot

/-!
# Entry 1 at the checker's program: `checkA_run` (lane parmode)

docs/design/parmode.md, "Step 4" (a). A run of `check` from the loaded memory with the mode word
`MODE` set to `1` or `3` (`loadMemM b pb s8 s64 w`, what the stubs `ca_start_a`/`ca_start_a0`
hand it) that returns anything but `1` (a line that did not scan):

* the twin's stages before the loop ran and its phase A accepted (`PhaseA b`: `TwinPrefix` and
  `installFold … = .ok (.ok (k, fe, pend), sF)`);
* the memory after the fold, `m`, is `PhaseBStart … m sF v` at the fold's result `v` (the final
  view), and the final memory is the frozen buffer's, `parCompactMem m v (modeFlag w)`;
* the result is `2^63 + |pend|`.

The stages are `stageSpecs_of_rels` at `checkerRels`, except the
first three, which start from the loaded memory with the mode word set: no relation reads a global
(`R1`‥`R3` name the loaded memory only through its arrays), so their proofs are those of
`capStage_checker`, `pbStage_checker`, `irpStage_checker` at `loadMemM`. The fold at the
substituted program (`triple_subPB`: the ROM readers read the pin-data buffer), from
`installFoldGo_start`.
-/

open ConRon.Arena ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Checker

open L L.Arena L.Front L.Rom L.Compiler ConAgua.Final

/-- The memory an entry-1 stub hands to `check`: the loaded memory with the mode word `w`. -/
def loadMemM (b pb : ByteArray) (s8 s64 : List Nat) (w : Word) : Mem := (loadMem b pb s8 s64).setG MODE w

/-! ## The first three stages from the loaded memory with the mode word set -/

/-- A global write is a frame with no array write. -/
theorem memFrame_setG (m : Mem) (g : GVar) (w : Word) : MemFrame [] [] m (m.setG g w) :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl, rfl⟩

theorem capStage_setG (b pb : ByteArray) (s8 s64 : List Nat) (hs : ∀ n ∈ s64, n < 2 ^ 64) (w : Word) :
    RelSpec checkerProg "cap_check" (· = loadMemM b pb s8 s64 w)
      fun _ m => m = loadMemM b pb s8 s64 w ∧ CapsOK (loadMem b pb s8 s64) := by
  intro n _hn s₀ hm
  refine triple_post (capCheck_spec checkerProg checkerProg_capCheck n s₀
    (hm ▸ loadMem_wordsFit b pb s8 s64 hs)) fun _ s' ⟨h1, h2, h3⟩ => ⟨h1, ?_, ?_⟩
  · rw [h2, hm]
  · rw [hm] at h3; exact h3

theorem pbStage_setG (b pb : ByteArray) (s8 s64 : List Nat) (hpb : pb.size < 2 ^ 63) (w : Word) :
    RelSpec checkerProg "pb_check" (fun m => m = loadMemM b pb s8 s64 w ∧ CapsOK (loadMem b pb s8 s64))
      fun _ m => m = loadMemM b pb s8 s64 w ∧ CapsOK (loadMem b pb s8 s64) ∧ PbPre pb := by
  intro n _hn s₀ ⟨hm, hc⟩
  refine triple_post (checkerProg_pbCheck_PB pb.data.toList (by simpa [RomOK] using hpb) n s₀
    (by rw [hm]; exact loadMem_pb b pb s8 s64)) fun _ s' ⟨h1, h2, h3⟩ => ⟨h1, ?_, hc, h3⟩
  rw [h2, hm]

theorem irpStage_setG (b pb : ByteArray) (s8 s64 : List Nat) (hpb : pb.size < 2 ^ 63) (w : Word) :
    RelSpec checkerProg "intern_reserved_pins"
      (fun m => m = loadMemM b pb s8 s64 w ∧ CapsOK (loadMem b pb s8 s64) ∧ PbPre pb)
      fun _ m => ∃ a', internReservedPins (AState.init EStore.empty) = .ok ((), a') ∧
        R3 (loadMem b pb s8 s64) m pb a' := by
  intro n _hn s₀ ⟨hm, hc, hpre⟩
  have hirp := checkerProg_internReservedPins_PB pb.data.toList (by simpa [RomOK] using hpb) hpre n
    s₀ (AState.init EStore.empty) (by rw [hm]; exact loadMem_pb b pb s8 s64)
    (by rw [hm, loadMemM]; exact ArenaD.frameHi (memFrame_setG _ MODE w) (by simp) (by simp) (arenaD_loadMem b pb s8 s64 hc))
    (by rw [hm]; exact Or.inr (by show (rdW ((loadMem b pb s8 s64).arr64 CTL) 0).toNat < 2 ^ 40
                                  rw [loadMem_rd]; decide))
  refine triple_post (triple_and hirp (stage_since n (preLoop_mem "intern_reserved_pins"
    (by decide +kernel)) s₀)) fun _ s' ⟨⟨hl, hok, hA, hfull, hp0, hfr, hmo⟩, _, hk, hpf⟩ => ⟨hl, ?_⟩
  have hrun := AM.run_of_ok _ _ hok
  have hrun' : internReservedPins (AState.init EStore.empty) =
      .ok ((), AM.st internReservedPins (AState.init EStore.empty)) := hrun
  obtain ⟨hokA, -, hpinsA, hppA, hoffA, -, hcachesA⟩ :=
    ConRon.Bridge.internReservedPins_run ⟨EStore.empty_wf⟩ rfl hrun'
  refine ⟨_, hrun', ?_⟩
  rw [hm] at hk hpf hfr
  have hk' : L.Keep (loadMem b pb s8 s64) s'.mem := hk
  have hpf' : MemFrame preLoopA preLoopC (loadMem b pb s8 s64) s'.mem := hpf
  have hfr' : MemFrame PinA StoreC (loadMem b pb s8 s64) s'.mem := hfr
  refine ⟨⟨hk', hc, by simpa [PbPre] using hpre, hpf'⟩, hA, ?_, ?_, ?_, hfull, hp0,
    ⟨hokA, hoffA, hpinsA, hppA, hfull.names_size⟩, hcachesA, ?_, hmo⟩
  · exact (stateDR_loadMem b pb s8 s64 hc).frame hfr' (pinA_not (by decide) (by decide))
      (pinA_not (by decide) (by decide)) (pinA_not (by decide) (by decide))
      (pinA_not (by decide) (by decide)) (pinA_not (by decide) (by decide)) pinA_idArrs storeC_idCtl
  · exact (rsetR_loadMem b pb s8 s64 hc).frame hfr' (pinA_not (by decide) (by decide))
      (pinA_not (by decide) (by decide)) (not_mem_storeC _ (by decide)) (not_mem_storeC _ (by decide))
  · have := hfr'.2.1 131 (not_mem_storeC _ (by decide))
    simp only [stkTop] at this ⊢
    rw [this]; exact stkTop_loadMem b pb s8 s64
  · have z := loadMem_rd b pb s8 s64
    exact HZ.frame ⟨z _ _, z _ _, z _ _, z _ _, z _, z _⟩ hfr' (pinA_not (by decide) (by decide))
      (pinA_not (by decide) (by decide)) (not_mem_storeC _ (by decide)) (not_mem_storeC _ (by decide))
      (not_mem_storeC _ (by decide)) (not_mem_storeC _ (by decide))

/-! ## Phase A's fold at the checker's program -/

/-- **The twin's side of entry 1**: the stages before the loop and phase A, with `k` records
installed, the environment `fe` and the pending groups `pend`, ending in `sF` (lane parallel's
structure). -/
structure PhaseA (b : ByteArray) where
  pins : List ConLeche.NatOpPinSet
  sA : AState
  pre : PreludeIx
  sB : AState
  rc : ParseResultD
  sC : AState
  ds : Array IDeclaration
  sD : AState
  ipins : List INatOpPinSet
  sE : AState
  k : Nat
  fe : IFEnv
  pend : Array PendingCheck
  sF : AState
  pfx : TwinPrefix b sA pre sB rc sC ds sD pins ipins sE
  fold : installFold .verified ipins (0, mkIFEnv IEnv.empty, #[]) ds.toList sE =
    .ok (.ok (k, fe, pend), sF)

/-- **What phase A's fold leaves at its result `v`**: an accepting twin phase A whose state the
memory `m` is `PhaseBStart` to, the pin data in place. -/
def FoldA (b pb : ByteArray) (v : Word) (m : Mem) : Prop :=
  ∃ PA : PhaseA b, PhaseBStart PA.ipins (dnOf PA.sE.store) PA.ds PA.fe PA.pend m PA.sF v ∧
    m.arr8 PB = pb.data.toList.toArray ∧ PbPre pb

/-- **The fold from `R7`** (and the twin's stages before the loop), with `cnt` the count
`DECL[0]`: at the substituted program (`installFoldGo_start`). -/
theorem foldStage_checker (b pb : ByteArray) (s8 s64 : List Nat) (hin : InputsOK b pb s64)
    {sA : AState} {pre : PreludeIx} {sB : AState} {rc : ParseResultD} {sC : AState}
    {ds : Array IDeclaration} {sD : AState} {pins : List ConLeche.NatOpPinSet}
    {ipins : List INatOpPinSet} {sE : AState} (hpx : TwinPrefix b sA pre sB rc sC ds sD pins ipins sE)
    (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (cnt : Word)
    (h7 : R7 (loadMem b pb s8 s64) s₀.mem pb ds ipins sE)
    (hcnt : ∀ h : 0 < (s₀.mem.arr64 DECL).size, cnt = (s₀.mem.arr64 DECL)[0]) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "install_fold_go" [0, cnt, 0]
    ⦃fun r s' => LocEq s' s₀ ∧ ∃ (fe : IFEnv) (pend : Array PendingCheck) (sF : AState),
      installFold .verified ipins (0, mkIFEnv IEnv.empty, #[]) ds.toList sE = .ok (.ok (ds.size, fe, pend), sF) ∧
      PhaseBStart ipins (dnOf sE.store) ds fe pend s'.mem sF (r.headD 0) ∧
      s'.mem.arr8 PB = pb.data.toList.toArray; ⊤⦄ := by
  have hr : RomOK pb.data.toList := by simpa [RomOK] using hin.2.2.1
  have hT := twinFold_of_prefix hpx
  have hcore := core_of_R7 hpx h7
  have hcaps := CapsOK.keep h7.since.keep h7.since.caps
  have hdn : L.Ind.DnInj (dnOf sE.store) := dnOf_inj hT.stateOK.wf
  have hQd : QuotDn (dnOf sE.store) := by
    obtain ⟨k, hk, hd⟩ := prefix_quotU hpx
    exact ⟨k, by simp [dnOf, hk, hd]⟩
  have hLC := checkerProg_loopCalleesPB pb.data.toList hr h7.since.pbpre (dnOf sE.store) hdn
    (indArmSpec_checker _ hr h7.since.pbpre _ hdn) hQd
  have hpb : s₀.mem.arr8 PB = pb.data.toList.toArray := by
    rw [h7.since.keep.arr8]; exact loadMem_pb b pb s8 s64
  have hD0 : 0 < (s₀.mem.arr64 DECL).size := by have := hcaps.2.2.1; simp only [DECL] at this ⊢; omega
  have hcnt' : cnt.toNat = ds.size := by
    rw [hcnt hD0]; have := h7.decls.count; simpa [hD0] using this
  refine triple_post (Triple.keep checkerProg_noSt8 (triple_subPB (bs := pb.data.toList)
    checkerProg_noSt8PB (fun s hs => hs ▸ hpb)
    (installFoldGo_start (checkerProg_loopTopPB _) hLC (frontDecls_of_prefix hpx)
    n hn s₀ cnt hcnt' hT h7.arena hcore h7.pinsFull h7.decls h7.pinSets h7.iw (loopZero_of_since h7.since)
    h7.pin0 (by have := hcaps.1 EREC (by decide); omega) (by have := hcaps.1 SPN (by decide); omega)
    (by have := hcaps.1 145 (by decide); omega) h7.mode))) ?_
  rintro r s' ⟨⟨hl, fe, pend, a', h1, h2⟩, hk, -⟩
  exact ⟨hl, fe, pend, a', h1, h2, by rw [hk.arr8]; exact hpb⟩

/-- The fold's spec at the stages' end `Q7`, in the form `checkA_of_stages` takes. -/
theorem foldSpec_checker (b pb : ByteArray) (s8 s64 : List Nat) (hin : InputsOK b pb s64) :
    ∀ n, n ≤ 2 ^ 62 → ∀ (s₀ : St) (cnt : Word),
      ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "install_fold_go" [0, cnt, 0]
      ⦃fun r s' => LocEq s' s₀ ∧ (Q7 b (checkerRels b pb s8 s64) s₀.mem →
        (∀ h : 0 < (s₀.mem.arr64 L.Front.DECL).size, cnt = (s₀.mem.arr64 L.Front.DECL)[0]) →
        FoldA b pb (r.headD 0) s'.mem); ⊤⦄ := by
  intro n hn s₀ cnt
  apply M.triple_of_run
  intro s r s' hs hrun
  have hl : LocEq s' s₀ := M.of_run (P := fun s => s = s₀) (Q := fun _ s => LocEq s s₀) hs hrun
    (L.invoke_loc checkerProg (exec checkerProg n) "install_fold_go" [0, cnt, 0] s₀)
  refine ⟨hl, fun hQ hcnt => ?_⟩
  obtain ⟨sA, pre, sB, rc, sC, ds, sD, pins, ipins, sE, hA, hB, hC, hD, hE, hR⟩ := hQ
  obtain ⟨-, fe, pend, sF, h1, h2, h3⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (foldStage_checker b pb s8 s64 hin ⟨hA, hB, hC, hD, hE⟩ n hn s₀ cnt hR hcnt)
  exact ⟨⟨pins, sA, pre, sB, rc, sC, ds, sD, ipins, sE, ds.size, fe, pend, sF, ⟨hA, hB, hC, hD, hE⟩, h1⟩,
    h2, h3, hR.since.pbpre⟩

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
  | _ + 61, h => exact absurd h (by omega)

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
phase A (`PhaseA b`) whose state the memory `m` after the fold is `PhaseBStart` to, at the fold's
result `v`; the final memory is the frozen buffer's, `parCompactMem m v (modeFlag w)` (in bounds),
and the result is `2^63 + |pend|`. -/
theorem checkA_run (b pb : ByteArray) (s8 s64 : List Nat) (hin : InputsOK b pb s64) (w : Word)
    (hw : w = 1 ∨ w = 3) (N : Nat) (hN : N < 2 ^ 62) (rs : List Word) (m' : Mem)
    (hrun : L.run checkerProg N "check" [] (loadMemM b pb s8 s64 w) = .ok (rs, m'))
    (hr : rs.headD 0 ≠ 1) :
    ∃ (PA : PhaseA b) (m : Mem) (v : Word),
      PhaseBStart PA.ipins (dnOf PA.sE.store) PA.ds PA.fe PA.pend m PA.sF v ∧
      m.arr8 PB = pb.data.toList.toArray ∧ PbPre pb ∧
      parCompactOK m (modeFlag w) = true ∧ m' = parCompactMem m v (modeFlag w) ∧
      rs.headD 0 = 9223372036854775808 + UInt64.ofNat PA.pend.size := by
  let r := checkerRels b pb s8 s64
  obtain ⟨-, -, -, s4, s5, s6, s7⟩ := stageSpecs_of_rels checkerRels checker_capStage
    checker_pbStage checker_irpStage checker_preludeStage checker_frontStage checker_prepareStage
    checker_pinsStage b pb s8 s64 hin
  have s1 := StageSpec.of_rel (X := Unit) (fun _ => _) (fun _ => _)
    (fun _ => capStage_setG b pb s8 s64 hin.2.2.2 w) fun m hm => ⟨(), hm, fun _ _ h => h⟩
  have s2 := StageSpec.of_rel (X := Unit) (fun _ => _) (fun _ => _)
    (fun _ => pbStage_setG b pb s8 s64 hin.2.2.1 w) fun m hm => ⟨(), hm, fun _ _ h => h⟩
  have s3 : StageSpec checkerProg "intern_reserved_pins"
      (fun m => m = loadMemM b pb s8 s64 w ∧ CapsOK (loadMem b pb s8 s64) ∧ PbPre pb)
      (fun _ => Q3 b r) := StageSpec.of_rel (X := Unit) (fun _ => _) (fun _ => _)
    (fun _ => irpStage_setG b pb s8 s64 hin.2.2.1 w) fun m hm => ⟨(), hm, fun _ _ h => h⟩
  have hla : checkerProg.lookup "check_a" = some checkAL := by chk_lk
  have hlc : checkerProg.lookup "check" = some checkL := by chk_lk
  have hpc : checkerProg.lookup "par_compact" = some parCompactL := by chk_lk
  have hmode : (loadMemM b pb s8 s64 w).glob MODE = w := by simp [loadMemM, Mem.setG]
  let P : Word → Mem → Prop := fun x m'' => x ≠ 1 → PostPC (modeFlag w) (FoldA b pb) m'' ∧
    ∀ h : 130 < (m''.arr64 CTL).size, x = (9223372036854775808 : Word) + (m''.arr64 CTL)[130]
  cases N with
  | zero =>
    exfalso
    refine run_post (Q := fun _ _ => False) hrun ?_
    rw [invoke_eq _ hlc]
    simp only [callFn]
    vcgen [exec] <;> grind
  | succ n =>
    have hn : n ≤ 2 ^ 62 := by omega
    let s₀ : St := { mem := loadMemM b pb s8 s64 w, loc := Locals.init [] }
    have hA : ∀ (s₁ : St) (c : Word), ⦃fun s => s = s₁⦄
        invoke checkerProg (exec checkerProg n) "check_a" [c]
        ⦃fun r s' => s₁.mem = s₀.mem → c = modeFlag (s₀.mem.glob MODE) → P (r.headD 0) s'.mem; ⊤⦄ := by
      intro s₁ c
      refine triple_post (checkA_of_stages (Q0 := (· = loadMemM b pb s8 s64 w)) hla hpc checkerProg_fz
        s1 s2 s3 s4 s5 s6 s7 (foldSpec_checker b pb s8 s64 hin) c n hn s₁) ?_
      intro x s' h e ec
      have ec' : c = modeFlag w := by rw [ec, hmode]
      subst ec'
      exact h e
    have H := run_post (Q := fun x m'' => (s₀.mem.glob MODE = 1 ∨ s₀.mem.glob MODE = 3) →
      P (x.headD 0) m'') hrun (check_dispatchA hlc n s₀ P hA)
    obtain ⟨⟨m, v, ⟨PA, hS, hpb, hpre⟩, hok, rfl⟩, hval⟩ := H (by rw [hmode]; exact hw) hr
    refine ⟨PA, m, v, hS, hpb, hpre, hok, rfl, ?_⟩
    have hF := parCompactMem_out m v (modeFlag w)
    have h130 : 130 < (m.arr64 CTL).size := by
      simp only [parCompactOK, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.2
    rw [hval (by rw [hF.size]; exact h130)]
    have hc := pendCount_eq hS.loop h130
    have e : ((parCompactMem m v (modeFlag w)).arr64 CTL)[130]'(by rw [hF.size]; exact h130) =
        (m.arr64 CTL)[130] := by simp only [hF.arr CTL (by decide)]
    rw [e, ← hc, UInt64.ofNat_toNat]

end L.Checker
