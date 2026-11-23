module

public import ConAgua.Checker.CompareStash
public import ConAgua.Checker.PipeRest
public import ConAgua.Front.FrontPreOK1
public import ConAgua.Checker.PresizeStage
import ConAgua.Checker.CheckARun
meta import ConAgua.Checker.LoopProgTac
import all ConAgua.Checker.Entry
import all ConAgua.Checker.CompareEntry
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

set_option experimental.vcgen true

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
  · simp only [ha, ite_false] at e ⊢; exact e

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
    (fun _ _ _ => rfl) (Nat.le_refl _) hD.ptop, fun x hx => recOK_congr_rows (hR x hx) fun j _ hj => hcp j (by omega)⟩


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

/-- **`DLP` kept up to the top of `m₀`**: its words `1 ‥ dtop m₀` are `m₀`'s, its top is at least
`m₀`'s (what the solution's parse leaves of the challenge's records' pool). -/
def DLPKeep (m₀ m : Mem) : Prop :=
  (∀ j, 0 < j → j ≤ dtop m₀ → (m.arr64 DLP)[j]? = (m₀.arr64 DLP)[j]?) ∧ dtop m₀ ≤ dtop m

theorem DLPKeep.refl (m : Mem) : DLPKeep m m := ⟨fun _ _ _ => rfl, Nat.le_refl _⟩

theorem DLPKeep.grow {m₀ m m' : Mem} (h : DLPKeep m₀ m) (hg : DGrow m m') : DLPKeep m₀ m' :=
  ⟨fun j h0 hj => (hg.dlp j h0 (Nat.le_trans hj h.2)).trans (h.1 j h0 hj), Nat.le_trans h.2 hg.top⟩

/-- **`front_run` from `R4` at the memory `m₀`, keeping the parse state and `DLP`**: `frontStage_checker`'s
statement with the parse state's relation (`StateDR`, at the twin's final parse state `st` after
the prelude's records), which `cmp_stash` needs to empty the id tables, and what the run keeps
of `m₀` (`DLPKeep`, the bytes and sizes, the stage's write set). -/
theorem frontStageD_checker (h64 : System.Platform.numBits = 64) (b pb : ByteArray)
    (hb : b.size < 2 ^ 63) (sz : TieredArray → Nat) (pre : PreludeIx) (a : AState) (m₀ : Mem) :
    RelSpec checkerProg "front_run" (fun m => m = m₀ ∧ R4 (loadMem b pb sz) m pb pre a) fun r m =>
      r.headD 0 = 0 → ∃ (rc : ParseResultD) (a' : AState) (st : StateD), parseChunks [b] a = .ok (.ok rc, a') ∧
        R5 (loadMem b pb sz) m pb pre rc a' ∧ StateDR m (st.pre pre.decls) ∧ rc.decls = st.decls ∧
        DLPKeep m₀ m ∧ L.Keep m₀ m ∧ MemFrame stageA_front_run stageC_front_run m₀ m := by
  intro n _hn s₀ ⟨hm₀, h4⟩
  have hm : s₀.mem.arr8 IN = b.data := by rw [h4.since.keep.arr8]; exact loadMem_in b pb sz
  refine triple_post (triple_and (triple_and (L.Front.frontRunOKK_checker (DLPKeep s₀.mem)
    (fun _ _ h hg => h.grow hg) pre.decls b h64 hb n s₀ hm
    a h4.arena h4.sdr h4.twin.ok h4.twin.off h4.twin.pins h4.rok h4.mode (DLPKeep.refl _))
    (stage_since n (preLoop_mem "front_run" (by decide +kernel)) s₀))
    (stageFrame_front_run n s₀)) fun r s' ⟨⟨hpost, hl, hk, hpf⟩, hsf⟩ => ⟨hl, fun h0 => ?_⟩
  obtain ⟨st, a', hp, hA, hD, hto, hM, hR, hKp⟩ := hpost h0
  subst hm₀
  have hu : b.size < USize.size := by
    rw [show USize.size = 2 ^ 64 by simp [USize.size, h64]]; omega
  have hcp : parseChunks [b] a = .ok (.ok (.ofState st), a') := by
    have := ConAgua.Front.ChunkBridge.parseChunks_single b hu
    rw [this]; exact hp
  obtain ⟨hstep, -, -⟩ := ConRon.Bridge.Frontend.parseChunks_run h4.twin.ok h4.twin.off h4.twin.pins hcp
  refine ⟨_, a', st, hcp, ⟨h4.since.step hk hpf, hA, hD.decls, ?_, ?_, ?_, ?_, ?_, hM⟩, hD, rfl, hKp, hk, hsf⟩
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

/-- **`front_run` from `R4`, keeping the parse state** (`frontStageD_checker`). -/
theorem frontStageS_checker (h64 : System.Platform.numBits = 64) (b pb : ByteArray)
    (hb : b.size < 2 ^ 63) (sz : TieredArray → Nat) (pre : PreludeIx) (a : AState) :
    RelSpec checkerProg "front_run" (fun m => R4 (loadMem b pb sz) m pb pre a) fun r m =>
      r.headD 0 = 0 → ∃ (rc : ParseResultD) (a' : AState) (st : StateD), parseChunks [b] a = .ok (.ok rc, a') ∧
        R5 (loadMem b pb sz) m pb pre rc a' ∧ StateDR m (st.pre pre.decls) ∧ rc.decls = st.decls :=
  fun n hn s₀ h4 => triple_post (frontStageD_checker h64 b pb hb sz pre a s₀.mem n hn s₀ ⟨rfl, h4⟩)
    fun _ _ ⟨hl, h⟩ => ⟨hl, fun h0 => by
      obtain ⟨rc, a', st, h1, h2, h3, h4, -⟩ := h h0
      exact ⟨rc, a', st, h1, h2, h3, h4⟩⟩

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
    exact recOK_congr_rows (h5.rok x (by simp; omega)) fun j hj _ => by
      simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]; split <;> first | omega | rfl
  · exact (h5.mode.frame hsf (by decide +kernel) (by decide +kernel)).frame (memFrame_setIn _ _)
      (by simp) (by simp)

/-! ## `check` in mode `4` -/

set_option experimental.vcgen true in
/-- **`check`'s dispatch to mode `4`**: with the mode word `4`, `check` is `check_c1()` from the
same memory. -/
theorem check_dispatch4 {p : Prog} (hp : p.lookup "check" = some checkL) (n : Nat) (s₀ : St)
    (P : Word → Mem → Prop)
    (hC : ∀ s₁ : St, ⦃fun s => s = s₁⦄ invoke p (exec p n) "check_c1" []
      ⦃fun r s' => s₁.mem = s₀.mem → P (r.headD 0) s'.mem; ⊤⦄) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check" []
    ⦃fun r s' => s₀.mem.glob MODE = 4 → P (r.headD 0) s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, (hC ·),
    (L.invoke_loc p (exec p n) "check_a" [·] ·), (L.invoke_loc p (exec p n) "check_b" [] ·),
    (L.invoke_loc p (exec p n) "check_c2" [] ·), (L.invoke_loc p (exec p n) "check_c3" [] ·)]
  all_goals (try simp only [Sig.retVal, Sig.retOr, L.St.setLoc_mem, List.headD_cons,
    St.setLocs_cons, St.setLocs_nil, St.setLoc_loc] at *)
  all_goals grind [lang_grind]

set_option experimental.vcgen true in
/-- **`check_c1()` from its stages**: the six stage specs of entry 1 up to `front_run` and
`cmp_stash`'s; on a result other than `1` (a line that did not scan), the memory after satisfies
`cmp_stash`'s postcondition and the result is `2^63`. -/
theorem checkC1_of_stages {p : Prog} (hp : p.lookup "check_c1" = some checkC1L)
    {Q0 Q1 Q2 Q2p Q3 Q4 Q5 Q6 : Mem → Prop}
    (h1 : StageSpec p "cap_check" Q0 fun _ => Q1)
    (h2 : StageSpec p "pb_check" Q1 fun _ => Q2)
    (h2p : StageSpec p "presize_tables" Q2 fun _ => Q2p)
    (h3 : StageSpec p "intern_reserved_pins" Q2p fun _ => Q3)
    (h4 : StageSpec p "builtin_prelude" Q3 fun _ => Q4)
    (h5 : StageSpec p "front_run" Q4 fun r m => r.headD 0 = 0 → Q5 m)
    (h6 : StageSpec p "cmp_stash" Q5 fun _ => Q6)
    (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_c1" []
    ⦃fun r s' => Q0 s₀.mem → r.headD 0 ≠ 1 → Q6 s'.mem ∧ r.headD 0 = 9223372036854775808; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkC1L]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hn' : n ≤ 2 ^ 62 := by omega
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      (h1 n hn' ·), (h2 n hn' ·), (h2p n hn' ·), (h3 n hn' ·), (h4 n hn' ·), (h5 n hn' ·), (h6 n hn' ·)]
    all_goals (try simp only [Sig.retVal, Sig.retOr, L.St.setLoc_mem, List.headD_cons,
      St.setLocs_cons, St.setLocs_nil, St.setLoc_loc, Cmp.eval, ite_true,
      bne_iff_ne, ne_eq, Decidable.not_not] at *)
    all_goals clear h1 h2 h2p h3 h4 h5 h6 hp
    all_goals grind (gen := 30) (ematch := 40) [lang_grind, Locals.init_cons_zero]

/-- **The twin's compared run up to the challenge's parse**, from the driver's start state. -/
def CmpPfx1 (bC : ByteArray) (sA : AState) (pre : PreludeIx) (sB : AState) (rC : ParseResultD)
    (sC : AState) : Prop :=
  internReservedPins (AState.init EStore.empty) = .ok ((), sA) ∧
    builtinPreludeE sA = .ok (.ok pre, sB) ∧ parseChunks [bC] sB = .ok (.ok rC, sC)

/-- After the challenge's `front_run`: the twin's stages so far, `R5` and the parse state. -/
def Q5S (bC pb : ByteArray) (sz : TieredArray → Nat) (m : Mem) : Prop :=
  ∃ sA pre sB rC sC, CmpPfx1 bC sA pre sB rC sC ∧ R5 (loadMem bC pb sz) m pb pre rC sC ∧
    ∃ st : StateD, StateDR m (st.pre pre.decls) ∧ rC.decls = st.decls

/-- **Mode `4`'s end** at the memory `m` it leaves: the twin's stages up to the challenge's parse
ran, `R4` holds at the loaded memory of the solution's bytes `bS` once the input is `bS`, and
`CDECL` holds the challenge's records. -/
def CmpAt4 (bC bS pb : ByteArray) (sz : TieredArray → Nat) (m : Mem) : Prop :=
  ∃ sA pre sB rC sC, CmpPfx1 bC sA pre sB rC sC ∧ R4 (loadMem bS pb sz) (m.setIn bS.data) pb pre sC ∧
    Stash m pre rC

/-- `cmp_stash` as a stage of mode `4`. -/
theorem stashStage_checker (bC bS pb : ByteArray) (sz : TieredArray → Nat) :
    StageSpec checkerProg "cmp_stash" (Q5S bC pb sz) fun _ => CmpAt4 bC bS pb sz := by
  intro n _ s₀
  refine triple_post (triple_and (triple_and (cmpStash_spec checkerProg (by chk_lk)
    checkerProg_prepProg n s₀) (stage_since n (preLoop_mem "cmp_stash" (by decide +kernel)) s₀))
    (stageFrame_cmp_stash n s₀)) fun _ s' ⟨⟨⟨hl, hok, hm⟩, _, hk, hpf⟩, hsf⟩ => ⟨hl, ?_⟩
  rintro ⟨sA, pre, sB, rC, sC, hpx, h5, st, hsd, hrc⟩
  obtain ⟨h4, hst⟩ := stash_R4 (bS := bS) h5 hsd hok hk hpf hsf hm
  exact ⟨sA, pre, sB, rC, sC, hpx, h4, hst⟩

/-- **Mode `4` in L**: a run of `check` from the loaded memory of the challenge's bytes `bC` with
the mode word `4` that returns anything but `1` (a line that did not scan) returns `2^63`, and its
final memory is mode `4`'s end (`CmpAt4`) for any solution bytes `bS`. -/
theorem checkC1_run (bC bS pb : ByteArray) (sz : TieredArray → Nat) (hin : InputsOK bC pb sz)
    (N : Nat) (hN : N < 2 ^ 62) (rs : List Word) (m' : Mem)
    (hrun : L.run checkerProg N "check" [] (loadMemM bC pb sz 4) = .ok (rs, m'))
    (hr : rs.headD 0 ≠ 1) :
    rs.headD 0 = 9223372036854775808 ∧ CmpAt4 bC bS pb sz m' := by
  let r := checkerRels bC pb sz
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
      (fun _ => Q3 bC r) := StageSpec.of_rel (X := Unit) (fun _ => _) (fun _ => _)
    (fun _ => irpStage_ps bC pb sz 4 hin.2.2.1) fun m hm => ⟨(), hm, fun _ _ h => h⟩
  have s5 : StageSpec checkerProg "front_run" (Q4 bC r) (fun r m => r.headD 0 = 0 → Q5S bC pb sz m) :=
    StageSpec.of_rel (fun x : AState × PreludeIx × AState => (R4 (loadMem bC pb sz) · pb x.2.1 x.2.2)) _
      (fun x => frontStageS_checker hin.1 bC pb hin.2.1 sz x.2.1 x.2.2)
      fun m ⟨sA, pre, sB, hA, hB, hR⟩ => ⟨(sA, pre, sB), hR, fun _ _ h h0 => by
        obtain ⟨rc, sC, st, hC, hR', hsd, hrc⟩ := h h0
        exact ⟨sA, pre, sB, rc, sC, ⟨hA, hB, hC⟩, hR', st, hsd, hrc⟩⟩
  have s6 := stashStage_checker bC bS pb sz
  have hc1 : checkerProg.lookup "check_c1" = some checkC1L := by chk_lk
  have hlc : checkerProg.lookup "check" = some checkL := by chk_lk
  have hmode : (loadMemM bC pb sz 4).glob MODE = 4 := by simp [loadMemM, Mem.setG]
  let P : Word → Mem → Prop := fun x m'' => x ≠ 1 → CmpAt4 bC bS pb sz m'' ∧ x = 9223372036854775808
  cases N with
  | zero =>
    exfalso
    refine run_post (Q := fun _ _ => False) hrun ?_
    rw [invoke_eq _ hlc]
    simp only [callFn]
    vcgen [exec] <;> grind
  | succ n =>
    have hn : n ≤ 2 ^ 62 := by omega
    let s₀ : St := { mem := loadMemM bC pb sz 4, loc := Locals.init [] }
    have hC : ∀ s₁ : St, ⦃fun s => s = s₁⦄ invoke checkerProg (exec checkerProg n) "check_c1" []
        ⦃fun r s' => s₁.mem = s₀.mem → P (r.headD 0) s'.mem; ⊤⦄ := fun s₁ =>
      triple_post (checkC1_of_stages (Q0 := (· = loadMemM bC pb sz 4)) hc1 s1 s2 s2p s3 s4 s5 s6 n hn s₁)
        fun _ _ h e => h e
    have H := run_post (Q := fun x m'' => s₀.mem.glob MODE = 4 → P (x.headD 0) m'') hrun
      (check_dispatch4 hlc n s₀ P hC)
    obtain ⟨h4, hv⟩ := H hmode hr
    exact ⟨hv, h4⟩

end L.Checker
