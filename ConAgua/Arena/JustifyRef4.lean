module

public import ConAgua.Arena.JustifyRef3
public import ConAgua.Arena.NeedsRef3
import ConAgua.Arena.RecLayout.CIDec
import ConAgua.Arena.RecLayout.CapsDec
import ConRon.Bridge.Checker.Canon
import ConRon.Bridge.Checker.Basis
import ConRon.Bridge.Checker.Inv
import all ConAgua.Arena.Justify

@[expose] public section

/-!
# The cone's context and `entry_needs` (lane compare, helper compare-cone)

**The context** `ConeT dn vis fe J m a`: the job's stage with the twin's invariants (`StageT`),
the twin's store well formed and read back (`StateOK`, `ReadOK`), the solution in memory (`SolR`),
and the constants of both indices denoting (`FindDen`: what the comparisons `copy_b`/`refines_b`
ask of their arguments).

**The frames.** The comparisons (`refines_b`, `same_cv_up_to_levels`) give no frame of their own
(`CmpPost`); their call closure `cmpFns` writes outside the solution's rows, the walks' memos and
stacks (`cmpKeep`) by a program hypothesis decided on the concrete program (`ConeProg.cmpClosed`).
`entry_needs` writes the needs walk's state, the work pool, the record pool and `name_rec`'s
(`enA`, `enC`). A step of the cone is a frame of `coneA = cmpA ++ enA`, `coneC = cmpC ++ enC`.
-/

noncomputable section

open ConRon.Arena

namespace L.Arena

open L.Ind L.Stubs

/-! ## Frames -/

/-- What the comparisons keep: the solution's rows, the walks' memos and stacks. -/
def cmpKeep : List TieredArray := solArrs ++ [(CSM : TieredArray), CWK, NDM, NACC]

/-- The arrays the comparisons may write. -/
def cmpA : List TieredArray := checkerWordArrays.filter fun b => b ∉ cmpKeep

/-- The control words the comparisons may write: all but the walks' and the solution's
(`220‥228`). -/
def cmpC : List Word := ((List.range 1024).filter fun x => x < 220 ∨ 228 < x).map UInt64.ofNat

/-- The call closure of `refines_b` and `same_cv_up_to_levels` in `checkerProg`, a literal list
(127 functions; `scripts/core_fns.lean` with these roots prints it). -/
def cmpFns : List FnName := [
  "app_find", "app_push", "b_eq", "caps_eq", "caps_eq_a", "caps_eq_b", "caps_eq_c", "ci_at_lps",
  "ci_eq", "ci_eq_rest", "const_find", "const_push", "copy_b", "cv_at_lps", "cv_eq", "cv_lps",
  "der_b", "ek_copy", "er_copy", "er_copy_er", "er_sl_at", "er_sl_eq", "er_to_iw", "erec_alloc",
  "erec_put", "fire_levels_at", "forall_find", "forall_push", "fvar_find", "fvar_push", "hint_eq",
  "ilp_clear", "ilp_find", "ilp_put", "ilpl_clear", "ilpl_find", "ilpl_put", "ilpls_clear",
  "ilpls_find", "ilpls_put", "imax_find", "imax_push", "inst_lp", "inst_lp_core", "intern_app",
  "intern_const", "intern_forall", "intern_fvar", "intern_imax", "intern_lam", "intern_letE",
  "intern_ls", "intern_ls_iw", "intern_max", "intern_param", "intern_proj", "intern_sort",
  "intern_succ", "intern_zero", "is_stmt_kind", "iw_alloc", "iw_copy", "iw_pool", "keys_ok",
  "keys_push", "lam_find", "lam_push", "letE_find", "letE_push", "levels_renaming", "lh_mk",
  "limbs_eq", "lit_hash", "lp_app", "lp_forall", "lp_fvar", "lp_go", "lp_lam", "lp_let",
  "lp_let_tail", "lp_lookup", "lp_proj", "lp_rb_let", "lp_substl", "ls_find", "ls_match",
  "ls_node", "ls_push", "lv_intern", "lv_node", "lv_sub_int", "max_find", "max_push", "mk_app",
  "mk_forall", "mk_lam", "mk_let", "mk_proj", "param_find", "param_levels", "param_levels_go",
  "param_push", "pin_at", "pool_room", "proj_find", "proj_push", "refines_b", "reserved_contains",
  "reserved_from", "rule_eq_a", "rule_eq_b", "rule_eq_but_rhs", "rules_at_lps_go", "rules_eq",
  "same_cv_up_to_levels", "sl_cons", "sl_contains", "sl_get", "sl_memo", "sl_nodup", "sle_go",
  "sls_go", "sls_memo", "sort_find", "sort_push", "spn_ls", "spn_pool", "spn_to_er", "succ_find",
  "succ_push", "zero_find", "zero_push"]

/-- What `entry_needs` writes: the needs walk's state, the work pool, the record pool, `name_rec`'s. -/
def enA : List TieredArray := [(NDM : TieredArray), NACC, IW, EREC, tier1 EREC] ++ nrA

/-- The control words `entry_needs` writes. -/
def enC : List Word := [220, 221, NTOPC, 200, 129, 130] ++ nrC

/-- A step of the cone's write set. -/
def coneA : List TieredArray := cmpA ++ enA

/-- A step of the cone's control words. -/
def coneC : List Word := cmpC ++ enC

theorem not_mem_cmpA {b : TieredArray} (h : b ∈ cmpKeep) : b ∉ cmpA := by
  simp only [cmpA, List.mem_filter, decide_eq_true_eq, not_and, Classical.not_not]
  exact fun _ => h

theorem not_mem_cmpC {x : Word} (h : 220 ≤ x.toNat ∧ x.toNat ≤ 228) : x ∉ cmpC := by
  simp only [cmpC, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq, not_exists,
    not_and]
  intro i hi e
  subst e
  have : (UInt64.ofNat i).toNat = i := by simp; omega
  rw [this] at h; omega

/-- The solution's rows are no step's. -/
theorem coneA_sol : ∀ b ∈ coneA, b ∉ solArrs := by
  intro b hb hs
  rcases List.mem_append.mp hb with h | h
  · exact not_mem_cmpA (List.mem_append.mpr (.inl hs)) h
  · exact (by decide : ∀ b ∈ enA, b ∉ solArrs) b h hs

theorem coneC_sol : ∀ x ∈ coneC, x ∉ solCtl := by
  intro x hx hs
  rcases List.mem_append.mp hx with h | h
  · simp only [solCtl, SOLC, SNEXTC, SCNTC, List.mem_cons, List.not_mem_nil, or_false] at hs
    exact not_mem_cmpC (by rcases hs with rfl | rfl | rfl <;> decide) h
  · simp only [enC, nrC, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
    simp only [solCtl, SOLC, SNEXTC, SCNTC, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases h with (rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl) <;>
      rcases hs with h | h | h <;> exact absurd h (by decide)

theorem coneA_csm : (CSM : TieredArray) ∉ coneA := by
  intro h
  rcases List.mem_append.mp h with h | h
  · exact not_mem_cmpA (by decide) h
  · exact (by decide : (CSM : TieredArray) ∉ enA) h

theorem coneA_cwk : (CWK : TieredArray) ∉ coneA := by
  intro h
  rcases List.mem_append.mp h with h | h
  · exact not_mem_cmpA (by decide) h
  · exact (by decide : (CWK : TieredArray) ∉ enA) h

theorem coneC_cs : (222 : Word) ∉ coneC ∧ CTOPC ∉ coneC := by
  constructor <;> intro h <;> rcases List.mem_append.mp h with h | h
  · exact not_mem_cmpC (by decide) h
  · exact (by decide : (222 : Word) ∉ enC) h
  · exact not_mem_cmpC (by decide) h
  · exact (by decide : CTOPC ∉ enC) h

/-- **The cone's state across a step.** -/
theorem CnR.coneFrame {m m' : Mem} {seen : Std.HashMap NIdx Bool} {work : List NIdx}
    (hf : MemFrame coneA coneC m m') (h : CnR m seen work) : CnR m' seen work := by
  have hW : m'.arr64 CWK = m.arr64 CWK := hf.arr _ coneA_cwk (by decide)
  have hT : ctlW m' CTOPC = ctlW m CTOPC := hf.ctl _ coneC_cs.2
  refine ⟨⟨memoRG_frame csSch csSch_wf nmKey _ coneA coneC coneA_csm coneC_cs.1 m m' hf _ h.rel.seen,
    ?_, ?_, ?_⟩, ?_⟩
  · rw [← h.rel.work]; simp only [cwkList, hW, hT]
  · intro i hi; rw [hW]; exact h.rel.words i (by rw [← hT]; exact hi)
  · rw [hW, hT]; exact h.rel.room
  · rw [hf.size]; exact h.ctl

/-! ## The context -/

/-- The constants a lookup finds denote. -/
def FindDen (st : EStore) (f : NIdx → Option IConstantInfo) : Prop :=
  ∀ n ci, f n = some ci → ∃ C, Frontend.denoteCI st ci = some C

theorem FindDen.ext {st st' : EStore} {f : NIdx → Option IConstantInfo} (h : FindDen st f)
    (hx : Ext st st') : FindDen st' f := fun n ci e => by
  obtain ⟨C, hC⟩ := h n ci e
  exact ⟨C, ConRon.Bridge.denoteCI_ext hC hx⟩

/-- **The cone's context**: the stage with the twin's invariants, the twin's store well formed and
read back, the solution in memory, both indices' constants denoting. -/
structure ConeT (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (J : ISolution)
    (m : Mem) (a : AState) : Prop where
  T : StageT dn vis fe m a
  ok : ConRon.Bridge.StateOK a
  rd : ConRon.Bridge.ReadOK a
  sol : SolR m J
  fden : FindDen a.store fe.find?
  sden : FindDen a.store J.find?

/-- The context from the twin's invariants: `FoldOK`'s index denoting (the solution's lookups
denoting, `hsden`: from `IFEnvOK envS (SolView J)` by `ISolution.find?_view`). -/
theorem ConeT.of_twin {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {J : ISolution} {m : Mem} {a : AState} {env : ConLeche.Env}
    (hT : StageT dn vis fe m a) (hF : ConRon.Bridge.FoldOK env fe a)
    (hsden : FindDen a.store J.find?) (hJ : SolR m J) :
    ConeT dn vis fe J m a := by
  refine ⟨hT, hF.check.state, hF.check.readOK, hJ, fun n ci e => ?_, hsden⟩
  obtain ⟨-, c, -, hc, -⟩ := hF.check.ienv.hit n ci e; exact ⟨c, hc⟩

/-! ## The program -/

/-- **What the cone's refinements need of a program.** -/
structure ConeProg (p : Prog) : Prop where
  cmp : JfCmpProg p
  nd : NeedsFpProg p
  ft : FindTableProg p
  rn : RnProg p
  en : p.lookup "entry_needs" = some entryNeedsL
  ce : p.lookup "cone_entry" = some coneEntryL
  cp : p.lookup "cone_push" = some conePushL
  cg : p.lookup "cone_go" = some coneGoL
  srg : p.lookup "sol_row_get" = some solRowGetL
  sf : p.lookup "sol_find" = some solFindL
  stg : p.lookup "sol_tbl_get" = some solTblGetL
  sft : p.lookup "sol_find_table" = some solFindTableL
  mg : p.lookup "mates_get" = some matesGetL
  csf : p.lookup "cs_find" = some (memoFindG csSch)
  csp : p.lookup "cs_put" = some (memoPutG csSch)
  csc : p.lookup "cs_clear" = some (memoClearG csSch)
  /-- The comparisons write outside `cmpKeep` (decided on the concrete program). -/
  cmpClosed : closedA p cmpA cmpC cmpFns = true

/-! ## Small frames -/

/-- The record pool's words across a frame that writes neither of its tiers nor their tops. -/
theorem erecP_frameAC {A : List TieredArray} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : (EREC : TieredArray) ∉ A ∧ tier1 EREC ∉ A) (hC : (129 : Word) ∉ C ∧ (130 : Word) ∉ C) :
    erecP m' = erecP m := by
  have h0 : m'.arr64 EREC = m.arr64 EREC := hf.arr _ hA.1 (by decide)
  have h1 : m'.arr64 (tier1 EREC) = m.arr64 (tier1 EREC) := hf.arr _ hA.2 (by decide)
  have t0 : erTop m' = erTop m := by simp only [erTop]; rw [hf.ctl _ hC.1]
  have t1 : erecTop1 m' = erecTop1 m := by simp only [erecTop1]; rw [hf.ctl _ hC.2]
  funext i; simp only [erecP, h0, h1, t0, t1]

/-- The pools' growth across a frame that writes neither the work pool, the record pool, nor
their tops. -/
theorem iwGrow_frame {A : List TieredArray} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : (IW : TieredArray) ∉ A ∧ (EREC : TieredArray) ∉ A ∧ tier1 EREC ∉ A)
    (hC : (200 : Word) ∉ C ∧ (129 : Word) ∉ C ∧ (130 : Word) ∉ C) : IWGrow m m' := by
  have hI : m'.arr64 IW = m.arr64 IW := hf.arr _ hA.1 (by decide)
  have h0 : m'.arr64 EREC = m.arr64 EREC := hf.arr _ hA.2.1 (by decide)
  have h1 : m'.arr64 (tier1 EREC) = m.arr64 (tier1 EREC) := hf.arr _ hA.2.2 (by decide)
  exact { iw := by simp only [iwTop]; rw [hf.ctl _ hC.1]; exact Nat.le_refl _
          er := by simp only [erTop]; rw [hf.ctl _ hC.2.1]; exact Nat.le_refl _
          iwGet := fun i _ => by rw [hI]
          erGet := fun i _ => by rw [h0]
          er1 := by simp only [erecTop1]; rw [hf.ctl _ hC.2.2]; exact Nat.le_refl _
          er1Get := fun i _ => by rw [h1] }

/-- **`StageT` across a needs walk** (its `StageR` post, the walk's frame with the work pool). -/
theorem StageT.of_ndw {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m' : Mem}
    {a : AState} (hT : StageT dn vis fe m a) (hS : StageR vis fe m' a)
    (hf : MemFrame ndAW ndCW m m') : StageT dn vis fe m' a :=
  ⟨hS, hT.twin.frame hf ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
    ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
    ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩ (by decide) (by decide),
    by simp only [pinW, hf.arr PINS (by decide) (by decide)]; exact hT.flag⟩

/-! ## `entry_needs` -/

section en
variable {p : Prog} (P : ConeProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
include P

/-- **`entry_needs(c, vis)` refines `entryNeeds`**: from any needs walk's state, the names the
twin's `entryNeeds` lists left on `NACC` (`needs_reset`, `needs_const`, an inductive's
constructors and its block's recursors' names (`rec_names` into a fresh slice), the mates of
its name, its table's names); the stage with the twin's invariants kept across the twin's
interning of the recursors' names. -/
@[refines ConRon.Arena.entryNeeds]
theorem entryNeeds_ok {n : Nat} {m m' : Mem} {a : AState} {c : Word} {r : List Word}
    {ci : IConstantInfo} {x : NeedsSt} {J : ISolution}
    (h : callW p n "entry_needs" [c, vis] m = some (r, m'))
    (hT : StageT dn vis fe m a) (hok : ConRon.Bridge.StateOK a) (hrd : ConRon.Bridge.ReadOK a)
    (hJ : SolR m J) (hci : decCI (erecP m) c.toNat = some ci)
    (hden : ∃ C, Frontend.denoteCI a.store ci = some C) (hx : NdR m x) :
    ∃ ns a', (ConRon.Arena.entryNeeds J.mates fe ci).run a = .ok (ns, a') ∧
      StageT dn vis fe m' a' ∧ ConRon.Bridge.RStep a a' ∧ IWGrow m m' ∧
      (∃ seen, NdR m' ⟨seen, ns⟩) ∧ MemFrame enA enC m m' := by
  sorry

end en

end L.Arena
