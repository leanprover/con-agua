import ConAgua.Arena.DeclLvlStage
import ConAgua.Arena.CoreErec
import ConAgua.Arena.KnotSlot
import ConAgua.Arena.WhnfEntry
import ConAgua.Arena.InferLeaves
import ConAgua.Arena.InferBodyIntern
import ConAgua.Arena.CoreLevels
import ConAgua.Arena.WhnfIotaRefine4
import ConAgua.Arena.LevelEquivRel
import ConAgua.Arena.LevelEquiv
import ConAgua.Arena.InstLPLevel
import ConAgua.Arena.IndInstallSpec8

/-!
# The stage relation with the twin's invariants: `StageT` (lane `indproofs3`)

The inductive stage runs on `StageR = CheckR ∧ IWOK`. The core functions it calls (`whnf`,
`infer_type_core`, `is_def_eq_core`, `ensure_sort_core`, `lvl_eq_c`, …) are refined under `CoreS`,
which adds the twin's invariants `TwinOK` (`DeclLvlStage.lean`: the readback caches, the name store's
well-formedness, the stored levels' readbacks, the walk memos, three capacities) and a filled pin
table. `StageT` is the stage relation with those parts, **by named components** (so
that a lemma names the part it keeps): `stage` (what every stage lemma keeps), `twin` (what only the core's posts and a few frames
keep), `flag` (the pin table's flag word, kept by every writer that leaves `PINS` alone).

What is here:
* `StageT.core`: `StageT` is `CoreS` (at the empty mode maps' existential).
* The core's write set **from the program text** (`CoreStageClosed p`: no function the core reaches
  writes `IW`, `EREC`, `PINS`, `CTL[129]`, `CTL[200]`; decided for the checker's program in
  `ConAgua/Checker/IndCore.lean`), and `StageT.of_core`: a core run's `CoreAfter` is `StageT` after,
  with the pools unchanged (`IWGrow`).
* The entry points as `Sim` facts under `StageT` (the "whnf adapters"): `whnf_top`,
  `infer_type_core`, `is_def_eq_core`, `ensure_sort_core`, from the knot (`KnotOK p n` at every `n`,
  `knot_all`). They replace the `IndStubs` contracts of the same names wherever the caller carries
  `StageT`.
-/

set_option experimental.vcgen true
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **The stage relation with the twin's invariants**, by named components. -/
structure StageT (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m : Mem) (a : AState) :
    Prop where
  /-- The stage relation (`CheckR ∧ IWOK`). -/
  stage : StageR dn vis fe m a
  /-- The twin's invariants `CoreS` has beyond `CheckR`. -/
  twin : TwinOK dn m a fe
  /-- The pin table is filled (its flag word). -/
  flag : pinW m 0 ≠ 0

section
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- `StageT` is `CoreS` at the eager bit `0`. -/
theorem StageT.core {m : Mem} {a : AState} (h : StageT dn vis fe m a) : ∃ M, CoreS dn m a vis fe M 0 :=
  StageR.coreS h.stage h.twin h.flag

/-! ## The core's write set -/

/-- The arrays a core function may write: every array but the pools, the pins, the walk memos `AbsOK`
holds beyond `CoreMemos` (51, 155) and the stage memos (201‥208). -/
def coreStageA : List ArrId := (List.range 388).filter fun b => b ≠ EREC ∧ b ≠ IW ∧ b ≠ PINS ∧
  b ≠ 51 ∧ b ≠ 155 ∧ (b < 201 ∨ 208 < b)

/-- The `CTL` words a core function may write: all but the pools' tops, the epochs of the walk memos
`AbsOK` holds beyond `CoreMemos` (52, 158) and the stage memos' control words (202‥219). -/
def coreStageC : List Word := ((List.range 256).filter fun x => x ≠ 129 ∧ x ≠ 200 ∧ x ≠ 52 ∧
  x ≠ 158 ∧ (x < 202 ∨ 219 < x)).map Nat.toUInt64

/-- The entry points the stage calls, and everything the core reaches. -/
def stageCoreFns : List FnName :=
  ["whnf_top", "infer_type_core", "is_def_eq_core", "ensure_sort_core", "lvl_eq_c"] ++ coreFns

/-- **The program hypothesis**: no function the stage's core entry points reach writes the pools,
their tops or the pins (decided for the checker's program, `ConAgua/Checker/IndCore.lean`). -/
def CoreStageClosed (p : Prog) : Prop := closedA p coreStageA coreStageC stageCoreFns = true

theorem coreStageA_iw : IW ∉ coreStageA := by simp [coreStageA]
theorem coreStageA_erec : EREC ∉ coreStageA := by simp [coreStageA]
theorem coreStageA_pins : PINS ∉ coreStageA := by simp [coreStageA]
theorem coreStageA_51 : (51 : ArrId) ∉ coreStageA := by simp [coreStageA]
theorem coreStageA_155 : (155 : ArrId) ∉ coreStageA := by simp [coreStageA]
/-- The core leaves the stage memos alone. -/
theorem coreStageA_stage : ∀ b ∈ coreStageA, b < 201 ∨ 208 < b := by
  intro b hb; simp only [coreStageA, List.mem_filter, List.mem_range, decide_eq_true_eq] at hb
  exact hb.2.2.2.2.2.2
theorem coreStageC_52 : (52 : Word) ∉ coreStageC := by decide
theorem coreStageC_158 : (158 : Word) ∉ coreStageC := by decide
/-- The core leaves the stage memos' control words alone. -/
theorem coreStageC_stage : ∀ x ∈ coreStageC, x.toNat < 202 ∨ 219 < x.toNat := by
  intro x hx
  simp only [coreStageC, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hx
  obtain ⟨c, ⟨hc, -, -, -, -, h⟩, rfl⟩ := hx
  have : (Nat.toUInt64 c).toNat = c := UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)
  rw [this]; exact h
theorem coreStageC_not {w : Word} (hw : w.toNat < 256) (h1 : w = 129 ∨ w = 200) : w ∉ coreStageC := by
  simp only [coreStageC, List.mem_map, List.mem_filter, List.mem_range, not_exists, not_and]
  intro x hx heq
  obtain ⟨hx, hd⟩ := hx
  have e : x = w.toNat := by rw [← heq]; simp [Nat.toUInt64]; omega
  subst e
  rcases h1 with rfl | rfl <;> simp at hd
theorem coreStageC_129 : (129 : Word) ∉ coreStageC := coreStageC_not (by decide) (.inl rfl)
theorem coreStageC_200 : (200 : Word) ∉ coreStageC := coreStageC_not (by decide) (.inr rfl)

/-- **After a core call**: the core's own post (`CoreS` at the state after) and the write set give
`StageT`, with the pools unchanged. -/
theorem StageT.of_core {p : Prog} (hcl : CoreStageClosed p) {f : FnName} (hf : f ∈ stageCoreFns)
    {n : Nat} {vs : List Word} {m m' : Mem} {r : List Word} {a a' : AState} {M : ModeMaps}
    (h : callW p n f vs m = some (r, m')) (hS : StageT dn vis fe m a)
    (hC : CoreS dn m' a' vis fe M 0) : StageT dn vis fe m' a' ∧ IWGrow m m' := by
  obtain ⟨hfr, -⟩ := run_memFrame hcl hf (run_of_callW h)
  have hI : m'.arr64 IW = m.arr64 IW := hfr.1 _ coreStageA_iw (by decide)
  have hE : m'.arr64 EREC = m.arr64 EREC := hfr.1 _ coreStageA_erec (by decide)
  have hP : m'.arr64 PINS = m.arr64 PINS := hfr.1 _ coreStageA_pins (by decide)
  have h129 : rdW (m'.arr64 CTL) 129 = rdW (m.arr64 CTL) 129 := hfr.2.1 _ coreStageC_129
  have h200 : rdW (m'.arr64 CTL) 200 = rdW (m.arr64 CTL) 200 := hfr.2.1 _ coreStageC_200
  obtain ⟨hCR, hT⟩ := hC.checkR
  refine ⟨⟨⟨hCR, IWOK.frame hfr coreStageA_iw coreStageA_erec coreStageC_129 coreStageC_200
    hS.stage.2⟩, hT, by simp only [pinW, hP]; exact hS.flag⟩, ?_⟩
  exact ⟨by simp [iwTop, h200], by simp [erTop, h129], fun i _ => by rw [hI], fun i _ => by rw [hE]⟩

/-- **A core entry point's refinement as a `Sim` under `StageT`**: a `CoreSpec` at every state in
`CoreS` turns a run of the call into the twin's run, `StageT` after, the pools unchanged. -/
theorem StageT.sim_core {α : Type} [Inhabited α] {p : Prog} (hcl : CoreStageClosed p) {f : FnName}
    (hf : f ∈ stageCoreFns) {n : Nat} {args : List Word} {T : AM α} {dec : List Word → α}
    {m : Mem} {a : AState} (hS : StageT dn vis fe m a)
    (hspec : ∀ (s₀ : St) (M : ModeMaps), CoreS dn s₀.mem a vis fe M 0 →
      CoreSpec p n f args T dec s₀ a dn vis fe M 0) :
    Sim (callW p n f args m) T a (fun r x m' a' => StageT dn vis fe m' a' ∧ IWGrow m m' ∧
      dec r = x ∧ ResH r) := by
  intro r m' e
  obtain ⟨M, hC⟩ := hS.core
  obtain ⟨s', rfl, -, hok, ⟨M', hC', -, -⟩, hres, hrh⟩ :=
    triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (hspec ⟨m, Locals.init []⟩ M hC) e
  obtain ⟨hT', hg⟩ := StageT.of_core hcl hf e hS hC'
  exact ⟨_, _, partsRunOfOk hok, hT', hg, hres.symm, hrh⟩

/-! ## Keeping `StageT` across the stage's own writers -/

/-- **`TwinOK` across a pool writer** (`iw_alloc`, `sl_cons`, `rec*`, `iw_copy`: `MemFrame [IW]
[200]`): none of its parts reads `IW` or `CTL[200]`. -/
theorem _root_.L.Arena.TwinOK.frame_iw {m m' : Mem} {a : AState} (hf : MemFrame [IW] [200] m m')
    (h : TwinOK dn m a fe) : TwinOK dn m' a fe := by
  have hE : m'.arr64 EREC = m.arr64 EREC := hf.1 EREC (by simp [EREC, IW]) (by decide)
  have hSp : m'.arr64 SPN = m.arr64 SPN := hf.1 SPN (by simp [SPN, IW]) (by decide)
  have hB : m'.arr64 145 = m.arr64 145 := hf.1 145 (by simp [IW]) (by decide)
  exact ⟨h.readL, h.readLs, h.nwf, by rw [hE]; exact h.erec, by rw [hSp]; exact h.spn,
    h.memos.frame hf (by simp [IW]) (by simp) (by simp [IW]) (by simp), by rw [hB]; exact h.bstk,
    h.den.frameE hE⟩

/-- **`StageT` across a pool writer**: the writer's `StageR` lemma (`allocW_stage`, `consW_stage`,
`recW_stage`, …) and its frame. -/
theorem StageT.of_iw {m m' : Mem} {a : AState} (hT : StageT dn vis fe m a)
    (hS : StageR dn vis fe m' a) (hf : MemFrame [IW] [200] m m') : StageT dn vis fe m' a :=
  ⟨hS, hT.twin.frame_iw hf, by
    have hP : m'.arr64 PINS = m.arr64 PINS := hf.1 PINS (by simp [PINS, IW]) (by decide)
    simp only [pinW, hP]; exact hT.flag⟩

end

/-! ## The entry points -/

section entry
variable (p : Prog) (hp : KnotEntryProg p) (hw : p.lookup "whnf_top" = some whnfTopL)
  (hK : ∀ n, KnotOK p n) (hcl : CoreStageClosed p)
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

include hw in
theorem whnfTop_spec (n : Nat) (s₀ : St) (vis dep e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "whnf_top" [vis, dep, e]
    ⦃fun r s' => LocEq s' s₀ ∧ call1W p n "whnf" [0, vis, dep, e] s₀.mem = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hw]
  simp only [callFn, whnfTopL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "whnf"] <;>
    finish [call1W_some]

theorem stage_fuel {n : Nat} (hn : n + 1 ≤ 2 ^ 62) : n ≤ checkFuel := by
  unfold checkFuel; omega

include hw hK in
/-- `whnf_top(vis, dep, e)` refines `whnf .verified fe checkFuel dep e` under `CoreS`. -/
theorem whnfTop_core (n : Nat) (hn : n + 1 ≤ 2 ^ 62) (F : Nat) (hF : n ≤ F) (s₀ : St) (a₀ : AState)
    (M : ModeMaps) (dep e : Word) (hS : CoreS dn s₀.mem a₀ vis fe M 0) (he : HW e) :
    CoreSpec p (n + 1) "whnf_top" [vis, dep, e] (whnf V fe F dep.toNat (decE e)) decH
      s₀ a₀ dn vis fe M 0 := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (whnfTop_spec p hw n s₀ vis dep e)
  subst hs0
  exact ⟨hloc, CoreSpec.of_call1W ((hK n).whnf F s a₀ dn vis fe M 0 0 dep e hF
    (by omega) (slotPre_zero hS) he) (fun r r' h => by simp only [decH, h]) hW⟩

/-- `H` and `HW` are one bound. -/
theorem hw_of_h {e : Word} (he : H e) : HW e := he

include hw hK hcl in
/-- **`whnf_top` under `StageT`** (replaces `IndStubs.whnf_spec` for a caller carrying `StageT`). -/
theorem whnfTop_simT (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState} (hS : StageT dn vis fe m a)
    (dep e : Word) (he : H e) :
    Sim (callW p n "whnf_top" [vis, dep, e] m) (whnf V fe checkFuel dep.toNat (decI e)) a
      (fun r x m' a' => StageT dn vis fe m' a' ∧ IWGrow m m' ∧ decW0E m' r x) := by
  rcases n with _ | k
  · intro r m' h; rw [callW_zero] at h; cases h
  refine Sim.mono (StageT.sim_core hcl (by simp [stageCoreFns]) hS
    (fun s₀ M hC => whnfTop_core p hw hK k hn checkFuel (stage_fuel hn) s₀ a M dep e hC (hw_of_h he))) ?_
  rintro r x m' a' ⟨hT, hg, hd, hr⟩
  exact ⟨hT, hg, hr, by rw [← hd]; rfl⟩

include hp hK in
theorem inferTypeCore_core (n : Nat) (hn : n + 1 ≤ 2 ^ 62) (F : Nat) (hF : n ≤ F) (s₀ : St)
    (a₀ : AState) (M : ModeMaps) (dep e : Word) (hS : CoreS dn s₀.mem a₀ vis fe M 0) (he : HW e) :
    CoreSpec p (n + 1) "infer_type_core" [vis, dep, e]
      (inferTypeCore V fe F dep.toNat (decE e)) decH s₀ a₀ dn vis fe M 0 :=
  inferTypeCore_refines p hp n (hK n).infer F s₀ a₀ dn vis fe M dep e hF (by omega) hS he

include hp hK hcl in
/-- **`infer_type_core` under `StageT`** (replaces `IndStubs.inferTypeCore_spec`). -/
theorem inferTypeCore_simT (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    (hS : StageT dn vis fe m a) (dep e : Word) (he : H e) :
    Sim (callW p n "infer_type_core" [vis, dep, e] m) (inferTypeCore V fe checkFuel dep.toNat (decI e)) a
      (fun r x m' a' => StageT dn vis fe m' a' ∧ IWGrow m m' ∧ decW0E m' r x) := by
  rcases n with _ | k
  · intro r m' h; rw [callW_zero] at h; cases h
  refine Sim.mono (StageT.sim_core hcl (by simp [stageCoreFns]) hS
    (fun s₀ M hC => inferTypeCore_core p hp hK k hn checkFuel (stage_fuel hn) s₀ a M dep e hC (hw_of_h he))) ?_
  rintro r x m' a' ⟨hT, hg, hd, hr⟩
  exact ⟨hT, hg, hr, by rw [← hd]; rfl⟩

include hp hK hcl in
/-- **`is_def_eq_core` under `StageT`** (replaces `IndStubs.isDefEqCore_spec`). -/
theorem isDefEqCore_simT (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    (hS : StageT dn vis fe m a) (dep x y : Word) (hx : H x) (hy : H y) :
    Sim (callW p n "is_def_eq_core" [vis, dep, x, y] m)
      (isDefEqCore V fe checkFuel dep.toNat (decI x) (decI y)) a
      (fun r b m' a' => StageT dn vis fe m' a' ∧ IWGrow m m' ∧ decBool r = b) := by
  rcases n with _ | k
  · intro r m' h; rw [callW_zero] at h; cases h
  refine Sim.mono (StageT.sim_core (dec := decBool) hcl (by simp [stageCoreFns]) hS
    (fun s₀ M hC => ?_)) ?_
  · have := isDefEqCore_refines p hp k (hK k).defeq checkFuel s₀ a dn vis fe M dep x y (stage_fuel hn)
      (by omega) hC (hw_of_h hx) (hw_of_h hy)
    exact this
  rintro r b m' a' ⟨hT, hg, hd, -⟩
  exact ⟨hT, hg, hd⟩

include hp hK hcl in
/-- **`ensure_sort_core` under `StageT`** (replaces `IndStubs.ensureSortCore_spec`), from
`InferLeaves`' `ensureSortCore_refines` (the knot below the call). -/
theorem ensureSortCore_simT (hl : InferLeafProg p) (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    (hS : StageT dn vis fe m a) (dep t : Word) (ht : H t) :
    Sim (callW p n "ensure_sort_core" [vis, dep, t] m) (ensureSortCore V fe checkFuel dep.toNat (decI t)) a
      (fun r x m' a' => StageT dn vis fe m' a' ∧ IWGrow m m' ∧ decW0L m' r x) := by
  rcases n with _ | _ | k
  · intro r m' h; rw [callW_zero] at h; cases h
  · intro r m' h
    obtain ⟨s', -, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (L.Arena.ensureSortCore_spec p hp 0 _ vis dep t) h
    simp [call1W, callW_zero] at hW
  refine Sim.mono (StageT.sim_core hcl (by simp [stageCoreFns]) hS
    (fun s₀ M hC => ensureSortCore_refines p hl hp k (fun j _ => hK j) checkFuel s₀ a dn vis fe M dep t
      (stage_fuel (by omega)) (by omega) hC (hw_of_h ht))) ?_
  rintro r x m' a' ⟨hT, hg, hd, hr⟩
  exact ⟨hT, hg, hr, by rw [← hd]; rfl⟩

include hcl in
/-- **`lvl_eq_c` under `StageT`** (replaces `IndStubs.lvlEqStub_spec`), from lane `whnf`'s
`lvlEqC_refines`: the two handles' readbacks are the caller's (`StoreDen.lvlAll` gives them for a
handle the twin's level store holds; `StoreDen.zero` for the pinned zero). -/
theorem lvlEqC_simT (hL : LvlCacheProg p) (hpc : p.lookup "lvl_eq_c" = some lvlEqCL) (n : Nat)
    {m : Mem} {a : AState} (hS : StageT dn vis fe m a) (u v : Word) (hu : H u) (hv : H v)
    (lu lv : ConLeche.Level) (hdu : denoteL a.store.ls (decI u) = some lu)
    (hdv : denoteL a.store.ls (decI v) = some lv) :
    Sim (callW p n "lvl_eq_c" [u, v] m) (lvlEq? (decI u) (decI v)) a
      (fun r x m' a' => StageT dn vis fe m' a' ∧ IWGrow m m' ∧ decO (r.headD 0) = x ∧ H (r.headD 0)) := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · intro r m' h; rw [lvlEqC_small p hpc n hn] at h; cases h
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  exact Sim.mono (StageT.sim_core hcl (by simp [stageCoreFns]) hS
    (fun s₀ M hC => lvlEqC_refines p hL k s₀ a dn vis fe M 0 hC u v hu hv lu lv hdu hdv))
    fun r x m' a' ⟨hT, hg, hd, hr⟩ => ⟨hT, hg, hd, hr⟩

end entry

/-! ## `lv_leq_top` under `StageT` -/

section leq
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- **`StageT` from `CoreS` after a heap-only run** (the level programs write only `LH` and
`CTL[192]`): the pools and the pins are untouched. -/
theorem StageT.of_heap {m m' : Mem} {a a' : AState} {M : ModeMaps} (hT : StageT dn vis fe m a)
    (hC : CoreS dn m a' vis fe M 0) (hf : MemFrame [LH] [192] m m') : StageT dn vis fe m' a' ∧ IWGrow m m' := by
  have hC' := hC.frameSM hf
    (by intro b hb; simp only [List.mem_singleton] at hb; subst hb; decide)
    (by intro x hx; simp only [List.mem_singleton] at hx; subst hx; decide)
    (hC.memos.frame hf (by decide) (by decide) (by decide) (by decide))
  have hI : m'.arr64 IW = m.arr64 IW := hf.1 IW (by decide) (by decide)
  have hE : m'.arr64 EREC = m.arr64 EREC := hf.1 EREC (by decide) (by decide)
  have hP : m'.arr64 PINS = m.arr64 PINS := hf.1 PINS (by decide) (by decide)
  have h129 : rdW (m'.arr64 CTL) 129 = rdW (m.arr64 CTL) 129 := hf.2.1 129 (by decide)
  have h200 : rdW (m'.arr64 CTL) 200 = rdW (m.arr64 CTL) 200 := hf.2.1 200 (by decide)
  obtain ⟨hCR, hTw⟩ := hC'.checkR
  refine ⟨⟨⟨hCR, IWOK.frame hf (by decide) (by decide) (by decide) (by decide) hT.stage.2⟩, hTw,
    by simp only [pinW, hP]; exact hT.flag⟩, ?_⟩
  exact ⟨by simp [iwTop, h200], by simp [erTop, h129], fun i _ => by rw [hI], fun i _ => by rw [hE]⟩

/-- The twin side of `lv_leq_top`: the two readbacks, then `Level.leq`. -/
def leqTopAM (u v : LIdx) : AM (Option Bool) := do
  let lu ← readLevelM u
  let lv ← readLevelM v
  pure (ConLeche.Level.leq lu lv)

end leq

end L.Ind
