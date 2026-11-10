module

public import ConAgua.Arena.DeclLvlStage
import ConAgua.Arena.IndInstallSpec.NhW
public import ConAgua.Arena.InferLeaves
import ConAgua.Arena.WhnfIotaRefine4
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
public import ConAgua.Arena.CoreErec
import all ConAgua.Arena.WhnfEntry
public import ConAgua.Arena.LeafFrame
public import ConAgua.Arena.IndPosSpec.NoGoStep
public import ConAgua.Arena.IndRealOpfLeaf
public import ConAgua.Arena.IndSumSpec.StructUsedFrame

@[expose] public section

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
* The core's write set **from the program text, with two leaves** (`CoreStageClosed p`: no
  function the core reaches writes `IW`, `EREC`, `PINS`, `CTL[129]`, `CTL[200]`, except the leaves
  `struct_used_later` and `open_pis_at_fvars_f`, which only grow the pool; decided for the
  checker's program in `ConAgua/Checker/IndCore.lean`). `CoreFr m m'`: a core call's frame
  (`run_coreFrame`): the core's writes and the leaves' (`coreFrA`, `coreFrC`), the pool grown.
  `StageT.of_core`: a core run's `CoreAfter` is `StageT` after, the pools grown (`IWGrow`).
* The entry points as `Sim` facts under `StageT` (the "whnf adapters"): `whnf_top`,
  `infer_type_core`, `is_def_eq_core`, `ensure_sort_core`, from the knot (`KnotOK p n` at every `n`,
  `knot_all`). They replace the `IndStubs` contracts of the same names wherever the caller carries
  `StageT`.
-/

set_option experimental.vcgen true

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
  stage : StageR vis fe m a
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
def coreStageA : List TieredArray := checkerWordArrays.filter fun b => b ≠ EREC ∧ b ≠ IW ∧ b ≠ PINS ∧
  b ≠ ILFM ∧ b ≠ Stubs.CRM ∧ (b.arr < 201 ∨ 208 < b.arr) ∧ b ≠ tier1 EREC

/-- The `CTL` words a core function may write: all but the pools' tops, the epochs of the walk memos
`AbsOK` holds beyond `CoreMemos` (52, 158) and the stage memos' control words (202‥219). -/
def coreStageC : List Word := ((List.range 256).filter fun x => x ≠ 129 ∧ x ≠ 200 ∧ x ≠ 52 ∧
  x ≠ 158 ∧ (x < 202 ∨ 219 < x) ∧ x ≠ 130).map Nat.toUInt64

/-- **The core's leaves**: reached by the core (`infer_proj`), they write the pool; each has its
own lemma (`ustW_grow`, `opfF_grow`) instead of the write-set check. -/
def coreLeaves : List FnName := ["struct_used_later", "open_pis_at_fvars_f"]

/-- What only the leaves reach (and the leaves): left out of the checked set. -/
def coreLeafOnly : List FnName := ["struct_used_later", "has_loose_b_var_b_fast",
  "has_loose_b_var_b_go", "has_loose_b_var_b_ins", "hb_find", "hb_clear", "hb_put", "strip_pis",
  "open_pis_at_fvars_f", "iw_alloc", "spn_to_iw"]

/-- The entry points the stage calls, and everything the core reaches but the leaves' own
functions. -/
def stageCoreFns : List FnName :=
  (["whnf_top", "infer_type_core", "is_def_eq_core", "ensure_sort_core", "lvl_eq_c"] ++ coreFns).filter
    fun f => !coreLeafOnly.contains f

theorem mem_stageCoreFns {f : FnName}
    (h1 : f ∈ ["whnf_top", "infer_type_core", "is_def_eq_core", "ensure_sort_core", "lvl_eq_c"] ++ coreFns)
    (h2 : coreLeafOnly.contains f = false) : f ∈ stageCoreFns :=
  List.mem_filter.mpr ⟨h1, by rw [h2]; rfl⟩

/-- `lvl_eq_c`'s call closure (it reaches no leaf). -/
def lvlCoreFns : List FnName :=
  ["lvl_eq_c", "lq_find", "lvl_eq_rec", "lvl_eq", "lv_equiv", "lv_eq", "lv_node", "lv_simp", "lh_mk",
   "lv_comb", "lv_leq", "lv_rest", "lv_imax", "lv_cases", "lv_cases_at", "lv_subsimp", "lv_subst",
   "lv_imax_l", "lv_dist1", "lv_dist2", "lv_imax_r", "lq_put"]

/-- **The program hypothesis**: no function the stage's core entry points reach writes the pools,
their tops or the pins, but the two leaves (decided for the checker's program,
`ConAgua/Checker/IndCore.lean`), whose programs are the bundles `UsF`, `OpfF`; `lvl_eq_c` without
leaves (`lvl`: its frame is the core's own, `MemFrame coreStageA coreStageC`). -/
structure CoreStageClosed (p : Prog) : Prop where
  closed : closedAL p coreStageA coreStageC stageCoreFns coreLeaves = true
  us : UsF p
  opf : OpfF p
  lvl : closedA p coreStageA coreStageC lvlCoreFns = true

theorem coreStageA_iw : (IW : TieredArray) ∉ coreStageA := by simp [coreStageA]
theorem coreStageA_erec : (EREC : TieredArray) ∉ coreStageA := by simp [coreStageA]
theorem coreStageA_pins : (PINS : TieredArray) ∉ coreStageA := by simp [coreStageA]
theorem coreStageA_51 : (ILFM : TieredArray) ∉ coreStageA := by simp [coreStageA]
theorem coreStageA_155 : (Stubs.CRM : TieredArray) ∉ coreStageA := by simp [coreStageA]
/-- The core leaves the stage memos alone. -/
theorem coreStageA_stage : ∀ b ∈ coreStageA, b.arr < 201 ∨ 208 < b.arr := by
  intro b hb; simp only [coreStageA, List.mem_filter, decide_eq_true_eq] at hb
  exact hb.2.2.2.2.2.2.1
theorem coreStageC_52 : (52 : Word) ∉ coreStageC := by decide
theorem coreStageC_158 : (158 : Word) ∉ coreStageC := by decide
/-- The core leaves the stage memos' control words alone. -/
theorem coreStageC_stage : ∀ x ∈ coreStageC, x.toNat < 202 ∨ 219 < x.toNat := by
  intro x hx
  simp only [coreStageC, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hx
  obtain ⟨c, ⟨hc, -, -, -, -, h, -⟩, rfl⟩ := hx
  have : (Nat.toUInt64 c).toNat = c := UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)
  rw [this]; exact h
theorem coreStageC_not {w : Word} (hw : w.toNat < 256) (h1 : w = 129 ∨ w = 200 ∨ w = 130) :
    w ∉ coreStageC := by
  simp only [coreStageC, List.mem_map, List.mem_filter, List.mem_range, not_exists, not_and]
  intro x hx heq
  obtain ⟨hx, hd⟩ := hx
  have e : x = w.toNat := by rw [← heq]; simp [Nat.toUInt64]; omega
  subst e
  rcases h1 with rfl | rfl | rfl <;> simp at hd
theorem coreStageC_129 : (129 : Word) ∉ coreStageC := coreStageC_not (by decide) (.inl rfl)
theorem coreStageC_200 : (200 : Word) ∉ coreStageC := coreStageC_not (by decide) (.inr (.inl rfl))
theorem coreStageC_130 : (130 : Word) ∉ coreStageC := coreStageC_not (by decide) (.inr (.inr rfl))
theorem coreStageA_erec1 : (tier1 EREC : TieredArray) ∉ coreStageA := by simp [coreStageA]

/-! ## The frame of a core call -/

/-- The arrays a core call writes: the core's, and the leaves'. -/
def coreFrA : List TieredArray := coreStageA ++ usA ++ opfA
/-- The `CTL` words a core call writes. -/
def coreFrC : List Word := coreStageC ++ usC ++ opfC

/-- **A core call's frame**: only `coreFrA`/`coreFrC` change, and the pools only grow. -/
def CoreFr (m₀ m : Mem) : Prop :=
  MemFrame coreFrA coreFrC m₀ m ∧ (IWOK m₀ → IWOK m ∧ IWGrow m₀ m)

theorem coreFrA_of {b : TieredArray} (h : b ∈ coreStageA) : b ∈ coreFrA := by
  simp [coreFrA, h]
theorem coreFrC_of {x : Word} (h : x ∈ coreStageC) : x ∈ coreFrC := by
  simp [coreFrC, h]

theorem coreFr_wframe : WFrame CTL coreStageA coreStageC CoreFr where
  refl m := ⟨MemFrame.refl _ _ _, fun h => ⟨h, IWGrow.refl m⟩⟩
  st64 m₀ m a i v h ha := by
    rcases ha with ⟨hc, ha⟩ | ⟨rfl, hi⟩
    · refine ⟨h.1.trans ((MemFrame.set64 m a hc i v).mono (by simpa using coreFrA_of ha) (by simp)),
        fun h0 => ?_⟩
      obtain ⟨hI, hg⟩ := h.2 h0
      have hA : (IW : TieredArray) ∉ [a] ∧ (EREC : TieredArray) ∉ [a] ∧ tier1 EREC ∉ [a] := by
        simp only [List.mem_singleton]
        exact ⟨fun e => coreStageA_iw (e ▸ ha), fun e => coreStageA_erec (e ▸ ha),
          fun e => coreStageA_erec1 (e ▸ ha)⟩
      obtain ⟨hI', hg'⟩ := iwKeep (MemFrame.set64 m a hc i v) hA (by simp) hI
      exact ⟨hI', hg.trans hg'⟩
    · refine ⟨h.1.trans ((MemFrame.setCtl m i v).mono (by simp) (by simpa using coreFrC_of hi)),
        fun h0 => ?_⟩
      obtain ⟨hI, hg⟩ := h.2 h0
      have hC : (129 : Word) ∉ [i] ∧ (130 : Word) ∉ [i] ∧ (200 : Word) ∉ [i] := by
        simp only [List.mem_singleton]
        exact ⟨fun e => coreStageC_129 (e ▸ hi), fun e => coreStageC_130 (e ▸ hi),
          fun e => coreStageC_200 (e ▸ hi)⟩
      obtain ⟨hI', hg'⟩ := iwKeep (MemFrame.setCtl m i v) (by simp) hC hI
      exact ⟨hI', hg.trans hg'⟩
  setG m₀ m g v h := by
    have hf : MemFrame [] [] m (m.setG g v) := ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩
    refine ⟨h.1.trans (hf.mono (by simp) (by simp)), fun h0 => ?_⟩
    obtain ⟨hI, hg⟩ := h.2 h0
    obtain ⟨hI', hg'⟩ := iwKeep hf (by simp) (by simp) hI
    exact ⟨hI', hg.trans hg'⟩

/-- **`struct_used_later` keeps the core frame**, at any arguments and fuel. -/
theorem coreFr_us {p : Prog} (hp : UsF p) (n : Nat) (m₀ : Mem) (vs : List Word) :
    ⦃fun s => CoreFr m₀ s.mem⦄ invoke p (exec p n) "struct_used_later" vs
    ⦃fun _ s => CoreFr m₀ s.mem; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨-, hc⟩ := M.of_run (P := fun t => t = s) rfl hrun (callW_spec p n "struct_used_later" vs s)
  have hfr := (run_memFrame hp.closed (by decide) (run_of_callW hc)).1
  obtain ⟨s'', hm, -, hu⟩ := triple_of_callW (s₀ := ⟨s.mem, Locals.init []⟩)
    (structUsedLater_specV hp n _ vs) (callW_mono hc (Nat.le_add_right n 2))
  rw [hm] at hu
  refine ⟨hs.1.trans (hfr.mono (fun b hb => by simp [coreFrA, hb]) (fun x hx => by simp [coreFrC, hx])),
    fun h0 => ?_⟩
  obtain ⟨hI, hg⟩ := hs.2 h0
  obtain ⟨hI', hg'⟩ := ustW_grow hu hI
  exact ⟨hI', hg.trans hg'⟩

/-- **`open_pis_at_fvars_f` keeps the core frame**, at any arguments and fuel. -/
theorem coreFr_opf {p : Prog} (hp : OpfF p) (n : Nat) (m₀ : Mem) (vs : List Word) :
    ⦃fun s => CoreFr m₀ s.mem⦄ invoke p (exec p n) "open_pis_at_fvars_f" vs
    ⦃fun _ s => CoreFr m₀ s.mem; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨-, hc⟩ := M.of_run (P := fun t => t = s) rfl hrun (opfF_spec p hp n s vs)
  refine ⟨hs.1.trans ((opfF_frame hc).mono (fun b hb => by simp [coreFrA, hb])
    (fun x hx => by simp [coreFrC, hx])), fun h0 => ?_⟩
  obtain ⟨hI, hg⟩ := hs.2 h0
  obtain ⟨hI', hg'⟩ := opfF_grow hc hI
  exact ⟨hI', hg.trans hg'⟩

theorem coreLeaves_keep {p : Prog} (hcl : CoreStageClosed p) : ∀ g ∈ coreLeaves, ∀ n m₀ vs,
    ⦃fun s => CoreFr m₀ s.mem⦄ invoke p (exec p n) g vs ⦃fun _ s => CoreFr m₀ s.mem; ⊤⦄ := by
  intro g hg n m₀ vs
  simp only [coreLeaves, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact coreFr_us hcl.us n m₀ vs
  · exact coreFr_opf hcl.opf n m₀ vs

/-- **A core call's frame**, as a triple. -/
theorem invoke_coreFrame {p : Prog} (hcl : CoreStageClosed p) (n : Nat) {f : FnName}
    (hf : f ∈ stageCoreFns) (vs : List Word) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) f vs ⦃fun _ s => CoreFr s₀.mem s.mem; ⊤⦄ :=
  invoke_frameL p hcl.closed coreFr_wframe (coreLeaves_keep hcl) n f hf vs s₀

/-- **Every run of a core function is a core frame.** -/
theorem run_coreFrame {p : Prog} (hcl : CoreStageClosed p) {f : FnName} (hf : f ∈ stageCoreFns)
    {n : Nat} {vs : List Word} {m : Mem} {rs : List Word} {m' : Mem}
    (h : run p n f vs m = .ok (rs, m')) : CoreFr m m' := by
  simp only [run] at h
  cases hr : (invoke p (exec p n) f vs).run { mem := m, loc := Locals.init [] } with
  | error e => simp [hr, Except.map] at h
  | ok r =>
    obtain ⟨r, s'⟩ := r
    simp only [hr, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact M.of_run (P := fun s => s = ⟨m, Locals.init []⟩) rfl hr
      (invoke_coreFrame hcl n hf vs ⟨m, Locals.init []⟩)

/-- The same through `callW`. -/
theorem callW_coreFrame {p : Prog} (hcl : CoreStageClosed p) {f : FnName} (hf : f ∈ stageCoreFns)
    {n : Nat} {vs : List Word} {m m' : Mem} {r : List Word} (h : callW p n f vs m = some (r, m')) :
    CoreFr m m' :=
  run_coreFrame hcl hf (run_of_callW h)

theorem coreFrA_not {b : TieredArray} (h1 : b ∉ coreStageA) (h2 : b ∉ usA ++ opfA) : b ∉ coreFrA := by
  simp only [coreFrA, List.append_assoc, List.mem_append, not_or] at h2 ⊢
  exact ⟨h1, h2⟩
theorem coreFrC_not {x : Word} (h1 : x ∉ coreStageC) (h2 : x ∉ usC ++ opfC) : x ∉ coreFrC := by
  simp only [coreFrC, List.append_assoc, List.mem_append, not_or] at h2 ⊢
  exact ⟨h1, h2⟩

theorem coreFrA_erec : (EREC : TieredArray) ∉ coreFrA := coreFrA_not coreStageA_erec (by decide)
theorem coreFrA_erec1 : (tier1 EREC : TieredArray) ∉ coreFrA := coreFrA_not coreStageA_erec1 (by decide)
theorem coreFrA_pins : (PINS : TieredArray) ∉ coreFrA := coreFrA_not coreStageA_pins (by decide)
theorem coreFrA_51 : (ILFM : TieredArray) ∉ coreFrA := coreFrA_not coreStageA_51 (by decide)
theorem coreFrA_155 : (Stubs.CRM : TieredArray) ∉ coreFrA := coreFrA_not coreStageA_155 (by decide)
theorem coreFrC_129 : (129 : Word) ∉ coreFrC := coreFrC_not coreStageC_129 (by decide)
theorem coreFrC_130 : (130 : Word) ∉ coreFrC := coreFrC_not coreStageC_130 (by decide)
theorem coreFrC_52 : (52 : Word) ∉ coreFrC := coreFrC_not coreStageC_52 (by decide)
theorem coreFrC_158 : (158 : Word) ∉ coreFrC := coreFrC_not coreStageC_158 (by decide)

/-- A core call leaves the stage memos alone but the `hb` memo (`struct_used_later`'s). -/
theorem coreFrA_stage : ∀ b ∈ coreFrA, b.arr < 201 ∨ 208 < b.arr ∨ b ∈ [(HBM : TieredArray)] := by
  intro b hb
  simp only [coreFrA, List.append_assoc, List.mem_append] at hb
  rcases hb with hb | hb | hb
  · rcases coreStageA_stage b hb with h | h
    · exact .inl h
    · exact .inr (.inl h)
  · revert b hb; exact (by decide +kernel : ∀ b ∈ usA, b.arr < 201 ∨ 208 < b.arr ∨ b ∈ [(HBM : TieredArray)])
  · revert b hb; exact (by decide +kernel : ∀ b ∈ opfA, b.arr < 201 ∨ 208 < b.arr ∨ b ∈ [(HBM : TieredArray)])
/-- The same for the `CTL` words: the `hb` memo's two. -/
theorem coreFrC_stage : ∀ x ∈ coreFrC, x.toNat < 202 ∨ 219 < x.toNat ∨ x ∈ [(214 : Word), 215] := by
  intro x hx
  simp only [coreFrC, List.append_assoc, List.mem_append] at hx
  rcases hx with hx | hx | hx
  · rcases coreStageC_stage x hx with h | h
    · exact .inl h
    · exact .inr (.inl h)
  · have h := List.all_eq_true.mp (show usC.all (fun x : Word => x.toNat < 202 || 219 < x.toNat ||
      x == 214 || x == 215) = true by decide +kernel) x hx
    simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rcases h with ((h | h) | h) | h <;> simp [h]
  · have h := List.all_eq_true.mp (show opfC.all (fun x : Word => x.toNat < 202 || 219 < x.toNat ||
      x == 214 || x == 215) = true by decide +kernel) x hx
    simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rcases h with ((h | h) | h) | h <;> simp [h]

/-- **A core call's memo frame**: the stage memos stand but the `hb` memo. -/
theorem CoreFr.mfr {m m' : Mem} (h : CoreFr m m') : MFr [HBM] [214, 215] m m' :=
  ⟨coreFrA, coreFrC, h.1, coreFrA_stage, coreFrC_stage⟩

/-- **After a core call**: the core's own post (`CoreS` at the state after) and the write set give
`StageT`, with the pools unchanged. -/
theorem StageT.of_core {p : Prog} (hcl : CoreStageClosed p) {f : FnName} (hf : f ∈ stageCoreFns)
    {n : Nat} {vs : List Word} {m m' : Mem} {r : List Word} {a a' : AState} {M : ModeMaps}
    (h : callW p n f vs m = some (r, m')) (hS : StageT dn vis fe m a)
    (hC : CoreS dn m' a' vis fe M 0) : StageT dn vis fe m' a' ∧ IWGrow m m' := by
  obtain ⟨hfr, hg⟩ := callW_coreFrame hcl hf h
  obtain ⟨hI, hG⟩ := hg hS.stage.iw
  have hP : m'.arr64 PINS = m.arr64 PINS := hfr.1 _ coreFrA_pins (by decide)
  obtain ⟨hCR, hT⟩ := hC.checkR
  exact ⟨⟨⟨hCR, hI⟩, hT, by simp only [pinW, hP]; exact hS.flag⟩, hG⟩

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
  exact ⟨_, _, L.Arena.AM.run_of_ok _ _ hok, hT', hg, hres.symm, hrh⟩

/-! ## Keeping `StageT` across the stage's own writers -/

/-- **`TwinOK` across a pool writer** (`iw_alloc`, `sl_cons`, `rec*`, `iw_copy`: `MemFrame [IW]
[200]`): none of its parts reads `IW` or `CTL[200]`. -/
theorem _root_.L.Arena.TwinOK.frame_iw {m m' : Mem} {a : AState} (hf : MemFrame [IW] [200] m m')
    (h : TwinOK dn m a fe) : TwinOK dn m' a fe := by
  have hE : m'.arr64 EREC = m.arr64 EREC := hf.arr EREC (by simp [EREC, IW]) (by decide)
  have hSp : m'.arr64 SPN = m.arr64 SPN := hf.arr SPN (by simp [SPN, IW]) (by decide)
  have hB : m'.arr64 BSTK = m.arr64 BSTK := hf.arr BSTK (by simp [BSTK, IW]) (by decide)
  exact ⟨h.readL, h.readLs, h.nwf, by rw [hE]; exact h.erec, by rw [hSp]; exact h.spn,
    h.memos.frame hf (by decide) (by simp) (by decide) (by simp), by rw [hB]; exact h.bstk,
    h.den.frameE hE⟩

/-- **`StageT` across a pool writer**: the writer's `StageR` lemma (`allocW_stage`, `consW_stage`,
`recW_stage`, …) and its frame. -/
theorem StageT.of_iw {m m' : Mem} {a : AState} (hT : StageT dn vis fe m a)
    (hS : StageR vis fe m' a) (hf : MemFrame [IW] [200] m m') : StageT dn vis fe m' a :=
  ⟨hS, hT.twin.frame_iw hf, by
    have hP : m'.arr64 PINS = m.arr64 PINS := hf.arr PINS (by simp [PINS, IW]) (by decide)
    simp only [pinW, hP]; exact hT.flag⟩

end

/-! ## The entry points -/

/-- **`whnf_top`'s model, both outcomes**: the `whnf` slot (verified mode) through its run. -/
l_model wtopE_spec (p : Prog) (hf : p.lookup "whnf_top" = some whnfTopL)
  fns [hf ↦ wtopE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified


section entry
variable (p : Prog) (hp : KnotEntryProg p) (hw : p.lookup "whnf_top" = some whnfTopL)
  (hK : ∀ n, KnotOK p n) (hcl : CoreStageClosed p)
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

theorem stage_fuel {n : Nat} (hn : n + 1 ≤ 2 ^ 62) : n ≤ checkFuel := by
  unfold checkFuel; omega

include hK in
/-- **`whnf_top(vis, dep, e)` refines `whnf .verified fe F dep e`, both outcomes**: the `whnf`
slot's (`KnotOK`, `KnotUpToE`). -/
theorem whnfTop_ref (n : Nat) (hn : n + 1 ≤ 2 ^ 62) (F : Nat) (hF : n ≤ F) (s₀ : St) (a₀ : AState)
    (M : ModeMaps) (dep e : Word) (hS : CoreS dn s₀.mem a₀ vis fe M 0) (he : HW e) :
    RefE (KnotUpToE p n) (wtopE p (n + 1) s₀.mem vis dep e) (whnf V fe F dep.toNat (decE e)) a₀
      (fun v y a' => CorePost decH dn s₀.mem vis fe M 0 ResH v y a') := by
  simp only [wtopE]
  rcases h : callE p n "whnf" [0, vis, dep, e] s₀.mem with e1 | ⟨r, m₁⟩
  · exact fun hG => CoreSpecE.of_callE ((hG n (Nat.le_refl _)).whnf F s₀ a₀ dn vis fe M 0 0 dep e
      hF (by omega) (slotPre_zero hS) he) h
  obtain ⟨hrun, hR⟩ := (CoreSpec.of_callW ((hK n).whnf F s₀ a₀ dn vis fe M 0 0 dep e hF (by omega)
    (slotPre_zero hS) he) (callW_of_callE h)).post
  exact RefE.ret hrun ⟨hR.after, by simpa [decH] using hR.res, by simpa [ResH] using hR.valid⟩

include hw hK in
/-- `whnf_top(vis, dep, e)` refines `whnf .verified fe checkFuel dep e` under `CoreS`
(`whnfTop_ref`'s ok half). -/
theorem whnfTop_core (n : Nat) (hn : n + 1 ≤ 2 ^ 62) (F : Nat) (hF : n ≤ F) (s₀ : St) (a₀ : AState)
    (M : ModeMaps) (dep e : Word) (hS : CoreS dn s₀.mem a₀ vis fe M 0) (he : HW e) :
    CoreSpec p (n + 1) "whnf_top" [vis, dep, e] (whnf V fe F dep.toNat (decE e)) decH
      s₀ a₀ dn vis fe M 0 :=
  CoreSpec.of_refE (w := id) (wtopE_spec p hw (n + 1) s₀ vis dep e)
    (whnfTop_ref p hK n hn F hF s₀ a₀ M dep e hS he) fun _ _ => ⟨rfl, rfl, id⟩

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
  refine Sim.mono (StageT.sim_core hcl (mem_stageCoreFns (by simp) (by simp [coreLeafOnly])) hS
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
  refine Sim.mono (StageT.sim_core hcl (mem_stageCoreFns (by simp) (by simp [coreLeafOnly])) hS
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
  refine Sim.mono (StageT.sim_core (dec := decBool) hcl (mem_stageCoreFns (by simp) (by simp [coreLeafOnly])) hS
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
    obtain ⟨s', -, -, hW⟩ := triple_of_callE (s₀ := ⟨m, Locals.init []⟩)
      (escE_spec p hp.ensureSortCore 1 _ vis dep t) (callE_of_callW h)
    obtain ⟨e', he', -⟩ := callE_zero p "ensure_sort" [0, vis, dep, t] m
    simp [escE, he', escE.k_ensure_sort] at hW
  refine Sim.mono (StageT.sim_core hcl (mem_stageCoreFns (by simp) (by simp [coreLeafOnly])) hS
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
  exact Sim.mono (StageT.sim_core hcl (mem_stageCoreFns (by simp) (by simp [coreLeafOnly])) hS
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
  have hP : m'.arr64 PINS = m.arr64 PINS := hf.arr PINS (by decide) (by decide)
  obtain ⟨hCR, hTw⟩ := hC'.checkR
  exact ⟨⟨⟨hCR, IWOK.frame hf (by decide) (by decide) (by decide) (by decide) hT.stage.iw⟩, hTw,
    by simp only [pinW, hP]; exact hT.flag⟩, IWGrow.of_keep hf (by decide) (by decide)⟩

/-- The twin side of `lv_leq_top`: the two readbacks, then `Level.leq`. -/
def leqTopAM (u v : LIdx) : AM (Option Bool) := do
  let lu ← readLevelM u
  let lv ← readLevelM v
  pure (ConLeche.Level.leq lu lv)

end leq

end L.Ind
