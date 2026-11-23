module

public import ConAgua.Checker.CompareStash
public import ConAgua.Checker.PipeRest
public import ConAgua.Checker.PreLoopWSStages
import ConAgua.Checker.PrepProgHoist
import ConAgua.Front.ChunkBridge
import ConAgua.Front.FrontRunRef
import ConRon.Bridge.Checker.Pins
import ConRon.Bridge.Frontend.Chunks
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr

@[expose] public section

/-!
# The compared run at the L level, mode `4` (lane compare)

`check` with the mode word `4` runs `check_c1()` (`Checker/CompareEntry.lean`): the stages of
entry 1 up to the challenge's parse, then `cmp_stash()`. Here: what the stash leaves
(`stash_R4`): the relation `R4` that the solution's `front_run` starts from (as entry 1's
`front_run` starts from `builtin_prelude`'s), at the loaded memory of the solution's bytes
(the stub replaces the input), and the challenge's records in `CDECL` (`Stash`).
-/

namespace L.Checker

open L L.Arena L.Front L.Rom ConAgua.Final
open ConRon.Arena ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order

/-! ## The input replaced -/

theorem setIn_arr64 (m : Mem) (x : Array UInt8) (a : TieredArray) : (m.setIn x).arr64 a = m.arr64 a := rfl

theorem memFrame_setIn (m : Mem) (x : Array UInt8) : MemFrame [] [] m (m.setIn x) :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

/-- **What holds since the loaded memory of `b` holds since that of `b'`** once the input is
replaced by `b'`: the two loaded memories differ in the input only. -/
theorem Since.setIn {b b' pb : ByteArray} {sz : TieredArray → Nat} {m : Mem}
    (h : Since (loadMem b pb sz) m pb) : Since (loadMem b' pb sz) (m.setIn b'.data) pb := by
  refine ⟨⟨?_, fun a => h.keep.2 a⟩, h.caps, h.pbpre, ⟨fun a ha hc => h.frame.arr a ha hc,
    fun x hx => h.frame.ctl x hx, fun a => h.frame.size a⟩⟩
  funext a
  have e := congrFun h.keep.1 a
  simp only [Mem.setIn, loadMem] at e ⊢
  by_cases ha : a = IN
  · simp [ha]
  · simp only [ha, if_false] at e ⊢; exact e

/-! ## The stash's memory -/

theorem memFrame_copy64 (m : Mem) (d : ArrId) (hd : (d : TieredArray) ≠ CTL) (di : Word) (s : TieredArray)
    (si : Word) (n : Nat) : MemFrame [d] [] m (m.copy64 d di s si n) :=
  ⟨fun b hb _ => arr64_copy64_ne _ _ _ _ _ _ (by simpa using hb),
    fun x _ => by rw [arr64_copy64_ne _ _ _ _ _ _ (Ne.symm hd)], fun b => size_copy64 _ _ _ _ _ _ _⟩

theorem stashM0_frame (m : Mem) : MemFrame [CDECL, DECL] [] m (stashM0 m) :=
  ((memFrame_copy64 m CDECL (by decide) 0 DECL 0 _).mono (by simp) (by simp)).trans
    ((MemFrame.set64 _ DECL (by decide) 0 _).mono (by simp) (by simp))

theorem stashM0_decl (m : Mem) :
    (stashM0 m).arr64 DECL = (m.arr64 DECL).set! 0 (rdW (m.arr64 CTL) 240) := by
  simp only [stashM0, Mem.arr64_set64_same, arr64_copy64_ne _ _ _ _ _ _ (show (DECL : TieredArray) ≠ CDECL by decide)]
  rfl

theorem stashM0_cdecl (m : Mem) :
    (stashM0 m).arr64 CDECL = (m.copy64 CDECL 0 DECL 0 (stashN m).toNat).arr64 CDECL := by
  simp only [stashM0]
  exact Mem.arr64_set64_ne _ _ _ _ _ (by decide)

theorem stashM_decl (m : Mem) : (stashM m).arr64 DECL = (stashM0 m).arr64 DECL :=
  (resetM_frame _).arr _ (by simp) (by decide)

theorem stashM_cdecl (m : Mem) : (stashM m).arr64 CDECL = (stashM0 m).arr64 CDECL :=
  (resetM_frame _).arr _ (by simp) (by decide)

theorem stashM_dlp (m : Mem) : (stashM m).arr64 DLP = m.arr64 DLP := by
  simp only [stashM]
  rw [(resetM_frame _).arr _ (by simp) (by decide), (stashM0_frame m).arr _ (by decide) (by decide)]

/-! ## The challenge's records in `CDECL` -/

/-- **The challenge's records kept for mode `6`**: `CDECL` holds the prelude's records and the
challenge's (`pre.decls ++ rC.decls`) over the pool `DLP`, each `RecOK`. -/
structure Stash (m : Mem) (pre : PreludeIx) (rC : ParseResultD) : Prop where
  decls : DeclsF (m.arr64 CDECL) (m.arr64 DLP) (pre.decls ++ rC.decls)
  rok : ∀ x < (pre.decls ++ rC.decls).size, RecOK (m.arr64 CDECL) (m.arr64 DLP) x

theorem stash_of {m : Mem} {ds : Array IDeclaration} (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds)
    (hR : ∀ x < ds.size, RecOK (m.arr64 DECL) (m.arr64 DLP) x) (hok : StashOK m)
    (hcs : (m.arr64 CDECL).size < 2 ^ 63) :
    DeclsF ((stashM m).arr64 CDECL) ((stashM m).arr64 DLP) ds ∧
      ∀ x < ds.size, RecOK ((stashM m).arr64 CDECL) ((stashM m).arr64 DLP) x := by
  have hc := hD.count
  have hc' : (rdW (m.arr64 DECL) 0).toNat = ds.size := hc
  have h59 := hok.1
  rw [hc'] at h59
  have hn : (stashN m).toNat = 1 + 8 * ds.size := by
    simp only [stashN]
    rw [UInt64.toNat_add, UInt64.toNat_mul, hc']
    simp only [UInt64.toNat_one, UInt64.reduceToNat]
    omega
  have hcp : ∀ j, j < 1 + 8 * ds.size →
      ((stashM m).arr64 CDECL)[j]? = (m.arr64 DECL)[j]? := fun j hj => by
    rw [stashM_cdecl, stashM0_cdecl]
    exact get?_copy64 (by decide) m _ (by rw [hn]; omega) hok.2.1 hok.2.2.1 j (by rw [hn]; exact hj)
  have hroom := hD.room
  have hsz : ((stashM m).arr64 CDECL).size = (m.arr64 CDECL).size := by
    rw [stashM_cdecl, stashM0_cdecl, size_copy64]
  rw [stashM_dlp]
  refine ⟨hD.congr (by rw [hsz]; exact hcs) (by rw [hsz, ← hn]; exact hok.2.1) rfl hcp
    (fun _ _ _ => rfl) (Nat.le_refl _) hD.ptop, fun x hx => recOK_congr (hR x hx) fun j _ hj => hcp j (by omega)⟩


/-! ## The parse state after the stash -/

/-- **`cmp_stash` leaves the parse state of the prelude's records**: the id tables emptied, `DECL`
cut back to the prelude's records (`CTL[240]` of them). -/
theorem stash_stateDR {m : Mem} {st : StateD} {pre : Array IDeclaration}
    (h : StateDR m (st.pre pre)) (hnp : (rdW (m.arr64 CTL) 240).toNat = pre.size) (hok : StashOK m) :
    StateDR (stashM m) (StateD.blank.pre pre) := by
  have hf := stashM0_frame m
  have hA : ∀ x ∈ [(CDECL : TieredArray), DECL], x ∉ idArrs := by decide
  have hC : ∀ x ∈ ([] : List Word), x ∉ idCtl := by simp
  have h0 : StateDR (stashM0 m) ({ st with decls := #[] }.pre pre) := by
    refine ⟨h.names.frame hf (.inl rfl) hA hC, h.levels.frame hf (.inr (.inl rfl)) hA hC,
      h.exprs.frame hf (.inr (.inr rfl)) hA hC, ?_, by rw [hf.size, hf.size]; exact h.ifs⟩
    have hd := h.decls
    simp only [StateD.pre] at hd ⊢
    rw [stashM0_decl, hf.arr DLP (by decide) (by decide), Array.append_empty]
    have e : rdW (m.arr64 CTL) 240 = UInt64.ofNat pre.size := by rw [← hnp, UInt64.ofNat_toNat]
    rw [e]
    exact hd.prefix
  have := frontReset_stateDR h0 hok.2.2.2
  simpa [StateD.pre, stashM] using this

/-! ## The challenge's `front_run`, with its parse state -/

/-- **`front_run` from `R4`, keeping the parse state**: `frontStage_checker`'s statement with the
parse state's relation (`StateDR`, at the twin's final parse state `st` after the prelude's
records), which `cmp_stash` needs to empty the id tables. -/
theorem frontStageS_checker (h64 : System.Platform.numBits = 64) (b pb : ByteArray)
    (hb : b.size < 2 ^ 63) (sz : TieredArray → Nat) (pre : PreludeIx) (a : AState) :
    RelSpec checkerProg "front_run" (fun m => R4 (loadMem b pb sz) m pb pre a) fun r m =>
      r.headD 0 = 0 → ∃ (rc : ParseResultD) (a' : AState) (st : StateD), parseChunks [b] a = .ok (.ok rc, a') ∧
        R5 (loadMem b pb sz) m pb pre rc a' ∧ StateDR m (st.pre pre.decls) ∧ rc.decls = st.decls := by
  intro n _hn s₀ h4
  have hm : s₀.mem.arr8 IN = b.data := by rw [h4.since.keep.arr8]; exact loadMem_in b pb sz
  refine triple_post (triple_and (triple_and (L.Front.frontRunOK_checker pre.decls b h64 hb n s₀ hm
    a h4.arena h4.sdr h4.twin.ok h4.twin.off h4.twin.pins h4.rok h4.mode)
    (stage_since n (preLoop_mem "front_run" (by decide +kernel)) s₀))
    (stageFrame_front_run n s₀)) fun r s' ⟨⟨hpost, hl, hk, hpf⟩, hsf⟩ => ⟨hl, fun h0 => ?_⟩
  obtain ⟨st, a', hp, hA, hD, hto, hM, hR⟩ := hpost h0
  have hu : b.size < USize.size := by
    rw [show USize.size = 2 ^ 64 by simp [USize.size, h64]]; omega
  have hcp : parseChunks [b] a = .ok (.ok (.ofState st), a') := by
    have := ConAgua.Front.ChunkBridge.parseChunks_single b hu
    rw [this]; exact hp
  obtain ⟨hstep, -, -⟩ := ConRon.Bridge.Frontend.parseChunks_run h4.twin.ok h4.twin.off h4.twin.pins hcp
  refine ⟨_, a', st, hcp, ⟨h4.since.step hk hpf, hA, hD.decls, ?_, ?_, ?_, ?_, ?_, hM⟩, hD, rfl⟩
  · rw [hsf.ctl 240 (stageC_front_run_off _ (by decide))]; exact h4.np
  · rw [hstep.pins]
    exact h4.pf.frame hsf stageA_front_run_pins (by decide +kernel) (by decide +kernel)
      (stageC_front_run_off _ (by decide)) (stageC_front_run_off _ (by decide))
      (stageC_front_run_off _ (by decide))
  · exact ⟨hto.1, hto.2.1, hto.2.2.1, h4.twin.pers.mono hstep.pins,
      by simp only [PinsReadyP, hstep.pins]; exact h4.twin.ready⟩
  · exact h4.hz.frame hsf (by decide +kernel) (by decide +kernel)
      (not_mem_of_toNat (Z := [73, 75, 129, 200, 130]) (by decide +kernel) _ (by decide))
      (not_mem_of_toNat (Z := [73, 75, 129, 200, 130]) (by decide +kernel) _ (by decide))
      (not_mem_of_toNat (Z := [73, 75, 129, 200, 130]) (by decide +kernel) _ (by decide))
      (not_mem_of_toNat (Z := [73, 75, 129, 200, 130]) (by decide +kernel) _ (by decide))
      (not_mem_of_toNat (Z := [73, 75, 129, 200, 130]) (by decide +kernel) _ (by decide))
  · exact fun x hx => hR x (by simpa [ParseResultD.ofState] using hx)

/-! ## Mode `4`'s end -/

/-- **What `cmp_stash` leaves after the challenge's parse**: from `R5` after `front_run` on the
challenge's bytes `bC` (with the parse state, `StateDR` at the challenge's state `st` after the
prelude's records), a returning `cmp_stash` (memory `m'`) leaves the relation `R4` that the
solution's `front_run` starts from, at the loaded memory of the solution's bytes `bS` once the
input is replaced by them, and the challenge's records in `CDECL`. -/
theorem stash_R4 {bC bS pb : ByteArray} {sz : TieredArray → Nat} {m m' : Mem} {pre : PreludeIx}
    {rC : ParseResultD} {sC : AState} {st : StateD}
    (h5 : R5 (loadMem bC pb sz) m pb pre rC sC) (hsd : StateDR m (st.pre pre.decls))
    (hok : StashOK m) (hk : L.Keep m m') (hf : MemFrame preLoopA preLoopC m m')
    (hsf : MemFrame stageA_cmp_stash stageC_cmp_stash m m') (hm : m' = stashM m) :
    R4 (loadMem bS pb sz) (m'.setIn bS.data) pb pre sC ∧ Stash m' pre rC := by
  have hS := h5.since.step hk hf
  have hcs : (m.arr64 CDECL).size < 2 ^ 63 := by
    rw [h5.since.frame.size]; have := (h5.since.caps.1 CDECL (by decide)).1; omega
  obtain ⟨hD', hR'⟩ := stash_of h5.decls h5.rok hok hcs
  refine ⟨⟨hS.setIn, ?_, ?_, ?_, ?_, h5.twin, ?_, ?_, ?_⟩, ⟨hm ▸ hD', hm ▸ hR'⟩⟩
  · exact (h5.arena.frameHi hsf (by simp [stageA_cmp_stash, tier0s]; decide) (by simp [stageC_cmp_stash])).frameHi (memFrame_setIn _ _)
      (by simp) (by simp)
  · subst hm
    exact (stash_stateDR hsd h5.np hok).frame (memFrame_setIn _ _) (by simp) (by simp)
  · rw [setIn_arr64, hsf.ctl 240 (stageC_cmp_stash_off _ (by decide))]; exact h5.np
  · exact (h5.pf.frame hsf (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (stageC_cmp_stash_off _ (by decide)) (stageC_cmp_stash_off _ (by decide))
      (stageC_cmp_stash_off _ (by decide))).frame (memFrame_setIn _ _) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp)
  · exact (h5.hz.frame hsf (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)).frame (memFrame_setIn _ _) (by simp)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  · intro x hx
    simp only [setIn_arr64, hm, stashM_decl, stashM_dlp, stashM0_decl]
    exact recOK_congr (h5.rok x (by simp; omega)) fun j hj _ => by
      simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]; split <;> first | omega | rfl
  · exact (h5.mode.frame hsf (by decide +kernel) (by decide +kernel)).frame (memFrame_setIn _ _)
      (by simp) (by simp)

end L.Checker
