import ConAgua.Checker.ParEntryA
import ConAgua.Checker.IndArm
import ConAgua.Arena.PhaseAEntry
import ConAgua.Checker.LoopStage
import ConAgua.Checker.PipeFinal
import ConAgua.Checker.TwinShapeQuot
import ConAgua.Checker.Presize

/-!
# The presize stage of entry 1 (lane presize)

`check_a` runs `presize_tables()` (`Checker/Presize.lean`) between `pb_check` and
`intern_reserved_pins`. From the loaded memory with the mode word set (`loadMemM`), it leaves
`psAllM`: the loaded memory with the `app`, `lam` and `forallE` tables' tier-0 count words
written by `X_presize` (`presizeStage`). That memory is still the twin's initial state to the arena
relation (`arenaD_ps`): every table is empty, three of them with more slots, all zero
(`consR_initM`). So `intern_reserved_pins` runs from it as from the loaded memory
(`irpStage_ps`, `irpStage_setG`'s proof), and what it leaves is `R3` of the loaded memory: the
presize writes only slot arrays of the store tier (`StoreA`, `preLoopA`).
-/

open ConRon.Arena ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Checker

open L L.Arena L.Front L.Rom L.Compiler ConAgua.Final

/-- The memory an entry-1 stub hands to `check`: the loaded memory with the mode word `w`. -/
def loadMemM (b pb : ByteArray) (sz : TieredArray → Nat) (w : Word) : Mem := (loadMem b pb sz).setG MODE w

/-- A global write is a frame with no array write. -/
theorem memFrame_setG (m : Mem) (g : GVar) (w : Word) : MemFrame [] [] m (m.setG g w) :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

/-! ## `presize_tables()` -/

/-- `pow2_at_least(q)` writes nothing. -/
theorem pow2AtLeast_spec (p : Prog) (hp : p.lookup "pow2_at_least" = some pow2AtLeastL) (k : Nat)
    (s₀ : St) (q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "pow2_at_least" [q]
    ⦃fun _ s' => LocEq s' s₀ ∧ s'.mem = s₀.mem; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, pow2AtLeastL]
  cases k with
  | zero => vcgen [exec] <;> grind
  | succ k =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs]
    all_goals simp only [St.setLoc_mem, LocEq]

/-- **`presize_tables()`**: a returning call keeps the caller's locals and writes the three
tables' presizes, at some slot counts. -/
theorem presizeTables_spec (p : Prog) (hp : p.lookup "presize_tables" = some presizeTablesL)
    (h2 : p.lookup "pow2_at_least" = some pow2AtLeastL)
    (ha : p.lookup "app_presize" = some appPresizeL) (hl : p.lookup "lam_presize" = some lamPresizeL)
    (hf : p.lookup "forall_presize" = some forallPresizeL) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "presize_tables" []
    ⦃fun _ s' => LocEq s' s₀ ∧
      ∃ a l f, s'.mem = psMem forallCS f (psMem lamCS l (psMem appCS a s₀.mem)); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, presizeTablesL]
  cases k with
  | zero => vcgen [exec] <;> grind
  | succ k =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      (pow2AtLeast_spec p h2 k · ·),
      (consPresize_spec p appCS "app_presize" ha k · ·),
      (consPresize_spec p lamCS "lam_presize" hl k · ·),
      (consPresize_spec p forallCS "forall_presize" hf k · ·)]
    all_goals (simp only [St.setLocs_mem', LocEq] at *)
    rename_i h4 h3 h2 h1 h0
    rw [h0.2, h1.2, h2.2, h3.2, h4.2]
    exact ⟨_, _, _, by congr 3; exact (‹_ ∧ _ = s₀.mem› : _ ∧ _).2⟩

/-! ## The memory after the presize -/

/-- `m` after `presize_tables()` at the slot counts `a`, `l`, `f`. -/
def psAllM (m : Mem) (a l f : Word) : Mem := psMem forallCS f (psMem lamCS l (psMem appCS a m))

section ps
variable (m : Mem) (a l f : Word)

theorem psAllM_arr_ne {b : TieredArray} (h1 : b ≠ ↑ASLOT) (h2 : b ≠ ↑LASLOT) (h3 : b ≠ ↑FASLOT) :
    (psAllM m a l f).arr64 b = m.arr64 b := by
  unfold psAllM
  rw [psMem_arr_ne _ _ _ h3, psMem_arr_ne _ _ _ h2, psMem_arr_ne _ _ _ h1]

theorem psAllM_size (b : TieredArray) : ((psAllM m a l f).arr64 b).size = (m.arr64 b).size := by
  simp only [psAllM, psMem_size]

theorem psAllM_bytes : (psAllM m a l f).bytes = m.bytes := by simp [psAllM]

theorem psAllM_setG (g : GVar) (w : Word) : psAllM (m.setG g w) a l f = (psAllM m a l f).setG g w := by
  simp only [psAllM, psMem_setG]

/-- The presize writes only the three slot arrays. -/
theorem psAllM_frame : MemFrame [↑ASLOT, ↑LASLOT, ↑FASLOT] [] m (psAllM m a l f) :=
  ⟨fun b hb _ => psAllM_arr_ne m a l f (fun e => hb (by simp [e])) (fun e => hb (by simp [e]))
      (fun e => hb (by simp [e])),
    fun x _ => by rw [psAllM_arr_ne m a l f (by decide) (by decide) (by decide)],
    psAllM_size m a l f⟩

theorem psAllM_keep : L.Keep m (psAllM m a l f) := ⟨psAllM_bytes m a l f, psAllM_size m a l f⟩

end ps

section
variable (b pb : ByteArray) (sz : TieredArray → Nat)

/-- **`ArenaR` after the presize**, on the loaded memory: the twin's initial state, every table
empty, the three presized ones at their new slot counts (`consR_initM`), the rest by the frame. -/
theorem arenaR_ps (hc : CapsOK (loadMem b pb sz)) (a l f : Word) :
    ArenaR (psAllM (loadMem b pb sz) a l f) (AState.init EStore.empty) := by
  have hR := arenaR_loadMem b pb sz hc
  have hf := psAllM_frame (loadMem b pb sz) a l f
  have hz := loadMem_rd b pb sz
  have hsl : ∀ a ∈ slotArrs, a ∈ checkerArrays.wordSlots := by decide
  have hs : ∀ x : ArrId, (x : TieredArray) ∈ slotArrs → tier1 x ∈ slotArrs → ∀ t,
      consMinWords ≤ ((psAllM (loadMem b pb sz) a l f).arr64 (tierA x t)).size ∧
      ((psAllM (loadMem b pb sz) a l f).arr64 (tierA x t)).size < 2 ^ 61 := fun x h0 h1 t => by
    rw [psAllM_size]
    rcases tierA_eq_or x t with e | e <;> rw [e]
    · exact (hc.1 x (hsl x h0)).2 h0
    · exact (hc.1 _ (hsl _ h1)).2 h1
  have hctl : 64 ≤ ((psAllM (loadMem b pb sz) a l f).arr64 CTL).size := by
    rw [psAllM_size]; have := hc.2.1; simp [ctlMin] at this; omega
  have hzc : ∀ x, rdW ((psAllM (loadMem b pb sz) a l f).arr64 CTL) x = 0 := fun x => by
    rw [psAllM_arr_ne _ _ _ _ (by decide) (by decide) (by decide)]; exact hz _ x
  have hApp : AppR (psAllM (loadMem b pb sz) a l f) (AState.init EStore.empty) :=
    consR_initM (m := loadMem b pb sz) a
      (by simp only [psAllM]; rw [psMem_arr_ne _ _ _ (by decide), psMem_arr_ne _ _ _ (by decide)])
      hzc (fun x => by rw [psAllM_arr_ne _ _ _ _ (by decide) (by decide) (by decide)]; exact hz _ x)
      (hz _) (by simp only [appCS, UInt64.reduceToNat]; omega) (hs ASLOT (by decide) (by decide))
  have hLam : LamR (psAllM (loadMem b pb sz) a l f) (AState.init EStore.empty) :=
    consR_initM (m := psMem appCS a (loadMem b pb sz)) l
      (by simp only [psAllM]; rw [psMem_arr_ne _ _ _ (by decide)])
      hzc (fun x => by rw [psAllM_arr_ne _ _ _ _ (by decide) (by decide) (by decide)]; exact hz _ x)
      (fun x => by rw [psMem_arr_ne _ _ _ (by decide)]; exact hz _ x)
      (by simp only [lamCS, UInt64.reduceToNat]; omega) (hs LASLOT (by decide) (by decide))
  have hFa : ForallR (psAllM (loadMem b pb sz) a l f) (AState.init EStore.empty) :=
    consR_initM (m := psMem lamCS l (psMem appCS a (loadMem b pb sz))) f rfl
      hzc (fun x => by rw [psAllM_arr_ne _ _ _ _ (by decide) (by decide) (by decide)]; exact hz _ x)
      (fun x => by rw [psMem_arr_ne _ _ _ (by decide), psMem_arr_ne _ _ _ (by decide)]; exact hz _ x)
      (by simp only [forallCS, UInt64.reduceToNat]; omega) (hs FASLOT (by decide) (by decide))
  arena_build hR, hf with first | exact hApp | exact hLam | exact hFa

/-- **`ArenaD` after the presize**, with the mode word set. -/
theorem arenaD_ps (hc : CapsOK (loadMem b pb sz)) (a l f w : Word) :
    ArenaD (psAllM (loadMemM b pb sz w) a l f) (AState.init EStore.empty) := by
  rw [loadMemM, psAllM_setG]
  exact ArenaD.frameHi (memFrame_setG _ MODE w) (by simp) (by simp)
    ⟨arenaR_ps b pb sz hc a l f, derR_init _⟩

end

/-! ## The stages around it -/

section
variable (b pb : ByteArray) (sz : TieredArray → Nat) (w : Word)

/-- What `presize_tables()` leaves (from `pb_check`'s post). -/
def PsPre (m : Mem) : Prop :=
  (∃ a l f, m = psAllM (loadMemM b pb sz w) a l f) ∧ CapsOK (loadMem b pb sz) ∧ PbPre pb

/-- **Stage `presize_tables`**, from `pb_check`'s post (`pbStage_setG`). -/
theorem presizeStage {p : Prog} (hp : p.lookup "presize_tables" = some presizeTablesL)
    (h2 : p.lookup "pow2_at_least" = some pow2AtLeastL)
    (ha : p.lookup "app_presize" = some appPresizeL) (hl : p.lookup "lam_presize" = some lamPresizeL)
    (hf : p.lookup "forall_presize" = some forallPresizeL) :
    StageSpec p "presize_tables" (fun m => m = loadMemM b pb sz w ∧ CapsOK (loadMem b pb sz) ∧ PbPre pb)
      (fun _ => PsPre b pb sz w) := fun n _ s₀ =>
  triple_post (presizeTables_spec p hp h2 ha hl hf n s₀) fun _ _ ⟨hl', a, l, f, e⟩ =>
    ⟨hl', fun ⟨hm, hc, hpre⟩ => ⟨⟨a, l, f, by rw [e, hm]; rfl⟩, hc, hpre⟩⟩

theorem psAllM_arr8 (a l f : Word) (x : ArrId) :
    (psAllM (loadMemM b pb sz w) a l f).arr8 x = (loadMem b pb sz).arr8 x := by
  simp only [Mem.arr8, psAllM_bytes]; rfl

/-- **Stage `intern_reserved_pins` after the presize**: `irpStage_setG`'s proof from `psAllM`
(`arenaD_ps`), its frames composed with the presize's (`psAllM_frame`, slot arrays of the store
tier). -/
theorem irpStage_ps (hpb : pb.size < 2 ^ 63) :
    RelSpec checkerProg "intern_reserved_pins" (PsPre b pb sz w)
      fun _ m => ∃ a', internReservedPins (AState.init EStore.empty) = .ok ((), a') ∧
        R3 (loadMem b pb sz) m pb a' := by
  intro n _hn s₀ ⟨⟨a, l, f, hm⟩, hc, hpre⟩
  have hirp := checkerProg_internReservedPins_PB pb.data.toList (by simpa [RomOK] using hpb) hpre n
    s₀ (AState.init EStore.empty) (by rw [hm, psAllM_arr8]; exact loadMem_pb b pb sz)
    (by rw [hm]; exact arenaD_ps b pb sz hc a l f w)
    (by rw [hm]; exact Or.inr (by
          show (rdW ((psAllM (loadMemM b pb sz w) a l f).arr64 CTL) 0).toNat < 2 ^ 40
          rw [psAllM_arr_ne _ _ _ _ (by decide) (by decide) (by decide)]
          show (rdW ((loadMem b pb sz).arr64 CTL) 0).toNat < 2 ^ 40
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
  have hk0 : L.Keep (loadMem b pb sz) (psAllM (loadMemM b pb sz w) a l f) :=
    psAllM_keep (loadMemM b pb sz w) a l f
  have hf0 : MemFrame [↑ASLOT, ↑LASLOT, ↑FASLOT] [] (loadMem b pb sz)
      (psAllM (loadMemM b pb sz w) a l f) :=
    have h := psAllM_frame (loadMemM b pb sz w) a l f
    ⟨h.arr, h.ctl, h.size⟩
  have hk' : L.Keep (loadMem b pb sz) s'.mem := hk0.trans hk
  have hpf' : MemFrame preLoopA preLoopC (loadMem b pb sz) s'.mem :=
    (hf0.mono (by decide) (by simp)).trans ⟨hpf.arr, hpf.ctl, hpf.size⟩
  have hfr' : MemFrame PinA StoreC (loadMem b pb sz) s'.mem :=
    (hf0.mono (by decide) (by simp)).trans ⟨hfr.arr, hfr.ctl, hfr.size⟩
  refine ⟨⟨hk', hc, by simpa [PbPre] using hpre, hpf'⟩, hA, ?_, ?_, ?_, hfull, hp0,
    ⟨hokA, hoffA, hpinsA, hppA, hfull.names_size⟩, hcachesA, ?_, hmo⟩
  · exact (stateDR_loadMem b pb sz hc).frame hfr' (pinA_not (by decide) (by decide))
      (pinA_not (by decide) (by decide)) (pinA_not (by decide) (by decide))
      (pinA_not (by decide) (by decide)) (pinA_not (by decide) (by decide)) pinA_idArrs storeC_idCtl
  · exact (rsetR_loadMem b pb sz hc).frame hfr' (pinA_not (by decide) (by decide))
      (pinA_not (by decide) (by decide)) (not_mem_storeC _ (by decide)) (not_mem_storeC _ (by decide))
  · have := hfr'.ctl 131 (not_mem_storeC _ (by decide))
    simp only [stkTop] at this ⊢
    rw [this]; exact stkTop_loadMem b pb sz
  · have z := loadMem_rd b pb sz
    exact HZ.frame ⟨z _ _, z _ _, z _ _, z _ _, z _, z _⟩ hfr' (pinA_not (by decide) (by decide))
      (pinA_not (by decide) (by decide)) (not_mem_storeC _ (by decide)) (not_mem_storeC _ (by decide))
      (not_mem_storeC _ (by decide)) (not_mem_storeC _ (by decide))

end

end L.Checker
