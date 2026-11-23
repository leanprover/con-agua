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


theorem not_solCtl {x : Word} (h : x.toNat < 224 ∨ 226 < x.toNat) : x ∉ solCtl := by
  simp only [solCtl, SOLC, SNEXTC, SCNTC, List.mem_cons, List.not_mem_nil, or_false]
  rintro (rfl | rfl | rfl) <;> simp at h

theorem ndC_sol : ∀ x ∈ ndC, x ∉ solCtl := by
  intro x hx; simp only [ndC, NTOPC, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> exact not_solCtl (by simp)

theorem ndCW_sol : ∀ x ∈ ndCW, x ∉ solCtl := by
  intro x hx; simp only [ndCW, NTOPC, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> exact not_solCtl (by simp)

theorem rnC_sol : ∀ x ∈ nrC ++ [129, 130], x ∉ solCtl := by
  intro x hx; simp only [nrC, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (rfl | rfl | rfl) | (rfl | rfl) <;> exact not_solCtl (by simp)

/-! ## `entry_needs` -/

/-- The twin's `entryNeeds` past the kind's arms: the mates, then the table. -/
def enTail (mates : Std.HashMap NIdx (List NIdx)) (fe : IFEnv) (ci : IConstantInfo)
    (x2 : NeedsSt) : AM (List NIdx) :=
  let x3 := match mates[ci.name]? with
    | some ms => x2.names ms
    | none => x2
  match fe.findTable? ci.name with
  | some t => do
    let x4 ← x3.table t
    pure x4.acc
  | none => pure x3.acc

theorem entryNeeds_eq (mates : Std.HashMap NIdx (List NIdx)) (fe : IFEnv) (ci : IConstantInfo) :
    ConRon.Arena.entryNeeds mates fe ci = (do
      let x0 ← NeedsSt.empty.const ci
      let x2 ← match ci with
        | .indInfo _ caps => do
          let x1 := x0.names caps.ctors
          let rn ← ConRon.Arena.recNames [] caps.all
          pure (x1.names rn)
        | _ => pure x0
      enTail mates fe ci x2) := rfl

section en
variable {p : Prog} (P : ConeProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
include P

/-- **`entry_needs`' tail** (`j1`): the mates of the name (`mates_get`, `needs_names`), then its
table's names (`find_table`, `needs_table`). -/
theorem enTail_ok {n : Nat} {m m' : Mem} {a : AState} {c : Word} {r : List Word}
    {ci : IConstantInfo} {x : NeedsSt} {J : ISolution}
    (h : entryNeedsW.j1 p n c vis m = some (r, m'))
    (hT : StageT dn vis fe m a) (hJ : SolR m J) (hci : decCI (erecP m) c.toNat = some ci)
    (hx : NdR m x) :
    ∃ ns, (enTail J.mates fe ci x).run a = .ok (ns, a) ∧ StageT dn vis fe m' a ∧
      (∃ seen, NdR m' ⟨seen, ns⟩) ∧ MemFrame ndA ndC m m' := by
  have Q := P.nd.toNeedsProg
  rw [entryNeedsW.j1.arm1] at h
  obtain ⟨hnw, hname, -⟩ := decCV_rd_ci (erRdOK m) (decCI_cv hci)
  generalize hwn : erRd m (c + (CI.cv + CV.name)) = wn at h hnw hname
  have hcn : ci.name = decI wn := by rw [ci_name_cv]; exact hname
  -- the mates' row
  replace h := opt_some h (entryNeedsW.k_mates_get.eq_1 ..)
  obtain ⟨⟨r1, m1⟩, c1, h⟩ := h
  obtain ⟨s1, hs1, hm1, -, hr1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (matesGet_spec p P.mg n _ wn) c1
  have e1 : m1 = m := hs1 ▸ hm1
  rw [e1] at h
  subst hr1
  have hmates : J.mates[ci.name]? = matList m wn := by
    rw [hcn, hJ.mates, decI_word_self wn hnw]
  -- the table, from a state `x3` of the mates
  have tbl : ∀ (x3 : NeedsSt) (m3 : Mem), NdR m3 x3 → StageT dn vis fe m3 a → MemFrame ndA ndC m m3 →
      entryNeedsW.j2 p n vis wn m3 = some (r, m') →
      ∃ ns, (match fe.findTable? ci.name with
        | some t => do
          let x4 ← x3.table t
          pure x4.acc
        | none => pure x3.acc : AM (List NIdx)).run a = .ok (ns, a) ∧ StageT dn vis fe m' a ∧
        (∃ seen, NdR m' ⟨seen, ns⟩) ∧ MemFrame ndA ndC m m' := by
    intro x3 m3 hx3 hT3 f3 h
    rw [entryNeedsW.j2.arm1] at h
    replace h := opt_some h (entryNeedsW.k_find_table.none ..)
    obtain ⟨⟨r4, m4⟩, c4, h⟩ := h
    obtain ⟨s4, hs4, hm4, -, hft, hdec⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
      (findTable_refines p P.ft n _ vis wn hT3.stage.check.env hnw) c4
    simp only at hm4 hft hdec
    rw [← hs4, hm4] at h
    rw [hcn, hft]
    by_cases h0 : r4.headD 0 = 0
    · rw [entryNeedsW.k_find_table.arm2 _ _ _ _ h0, entryNeedsW.j3.arm1] at h
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hnone : tblFound m3 (r4.headD 0) = none := by unfold tblFound; rw [ite_eq_left h0]
      refine ⟨x3.acc, by rw [hnone]; rfl, hT3, ⟨x3.seen, hx3⟩, f3⟩
    · rw [entryNeedsW.k_find_table.arm1 _ _ _ _ h0] at h
      replace h := opt_some h (entryNeedsW.k_needs_table.none ..)
      obtain ⟨⟨r5, m5⟩, c5, h⟩ := h
      rw [entryNeedsW.k_needs_table.arm1, entryNeedsW.j3.arm1] at h
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨tb, htb⟩ := hdec h0
      obtain ⟨y, ey, hy, hS5, f5⟩ := needsTable_ref Q c5 hT3.stage hx3
        (by rw [sub1_toNat h0]; exact htb)
      have hfound : tblFound m3 (r4.headD 0) = some tb := by unfold tblFound; rw [ite_eq_right h0, htb]
      refine ⟨y.acc, ?_, StageT.of_ndw hT3 hS5 (ndFrame_w f5), ⟨y.seen, hy⟩, f3.trans f5⟩
      rw [hfound]
      show (NeedsSt.acc <$> x3.table tb).run a = _
      simp only [StateT.run_map, ey]; rfl
  by_cases h0 : (matRow m wn).1 = 0
  · rw [entryNeedsW.k_mates_get.arm2 _ _ _ _ _ _ (by simpa using h0)] at h
    obtain ⟨ns, e, hT', hN', f'⟩ := tbl x m hx hT (MemFrame.refl _ _ _) h
    refine ⟨ns, ?_, hT', hN', f'⟩
    have hn : J.mates[ci.name]? = none := by rw [hmates, matList, ite_eq_left h0]
    simp only [enTail, hn]; exact e
  · rw [entryNeedsW.k_mates_get.arm1 _ _ _ _ _ _ (by simpa using h0)] at h
    obtain ⟨ms, hms⟩ := Option.isSome_iff_exists.mp (hJ.mates_dec wn h0)
    have hsl : hslice? (erecP m) ((matRow m wn).1 - 1).toNat (matRow m wn).2.toNat = some ms := by
      rw [sub1_toNat h0]; unfold matList at hms; rwa [ite_eq_right h0] at hms
    replace h := opt_some h (entryNeedsW.k_needs_names.none ..)
    obtain ⟨⟨r2, m2⟩, c2, h⟩ := h
    rw [entryNeedsW.k_needs_names.arm1] at h
    simp only [List.headD_cons, List.tail_cons] at c2
    obtain ⟨hx2, f2⟩ := needsNames_step Q c2 hx hsl
    have hS2 := (hT.stage.ndFrame f2).1
    obtain ⟨ns, e, hT', hN', f'⟩ := tbl _ m2 hx2 (StageT.of_ndw hT hS2 (ndFrame_w f2)) f2 h
    refine ⟨ns, ?_, hT', hN', f'⟩
    have hn : J.mates[ci.name]? = some ms := by rw [hmates, hms]
    simp only [enTail, hn]; exact e

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
  have Q := P.nd.toNeedsProg
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (entryNeeds_specW p P.en n _ c vis) h
  rcases n with _ | n
  · rw [entryNeedsW.eq_1] at hW; cases hW
  rw [entryNeedsW.arm1] at hW
  -- `needs_reset`, `needs_const`
  replace hW := opt_some hW (entryNeedsW.k_needs_reset.none ..)
  obtain ⟨⟨r1, m1⟩, c1, hW⟩ := hW
  rw [entryNeedsW.k_needs_reset.arm1] at hW
  obtain ⟨hy1, f1⟩ := needsReset_ref Q c1 hx.rel.seen hx.ctl
  have hS1 := (hT.stage.ndFrame f1).1
  have hT1 := StageT.of_ndw hT hS1 (ndFrame_w f1)
  have hci1 : decCI (erecP m1) c.toNat = some ci := by rw [erecP_nd f1]; exact hci
  replace hW := opt_some hW (entryNeedsW.k_needs_const.eq_1 ..)
  obtain ⟨⟨r2, m2⟩, c2, hW⟩ := hW
  obtain ⟨y0, e0, hy0, hS2, hg2, f2⟩ := needsConst_ref P.nd c2 hS1 hy1 hci1
  have hT2 := StageT.of_ndw hT1 hS2 f2
  have hE2 : erecP m2 = erecP m1 := erecP_frameAC f2 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
  have hci2 : decCI (erecP m2) c.toNat = some ci := by rw [hE2]; exact hci1
  have hg1 : IWGrow m m1 := iwGrow_frame f1 ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
  have hJ2 : SolR m2 J :=
    (hJ.growF f1 (by decide) ndC_sol hg1.erecGrow).growF f2 (by decide) ndCW_sol hg2.erecGrow
  have hk := kindW hci2
  rw [entryNeeds_eq]
  simp only [StateT.run_bind, e0, except_ok_bind]
  by_cases hk3 : erRd m2 c = 3
  · ------ an inductive: its constructors, its block's recursors
    rw [hk3] at hk
    obtain ⟨v, cap, rfl⟩ : ∃ v cap, ci = .indInfo v cap := by
      cases ci <;> first | (simp [ciKindQ] at hk; done) | exact ⟨_, _, rfl⟩
    rw [entryNeedsW.k_needs_const.arm1 _ _ _ _ _ _ hk3] at hW
    obtain ⟨-, -, -, -, hall, hctors⟩ := decCI_indInfo_rd (erRdOK m2) hci2
    replace hW := opt_some hW (entryNeedsW.k_needs_names_2.eq_1 ..)
    obtain ⟨⟨r3, m3⟩, c3, hW⟩ := hW
    obtain ⟨hy3, f3⟩ := needsNames_step Q c3 hy0 hctors
    have hS3 := (hS2.ndFrame f3).1
    have hT3 := StageT.of_ndw hT2 hS3 (ndFrame_w f3)
    rw [entryNeedsW.k_needs_names_2.arm1, erRd_nd f3] at hW
    generalize hl : erRd m2 (c + (CI.indCaps + Caps.allLen)) = l at hW hall
    replace hW := opt_some hW (entryNeedsW.k_erec_alloc.eq_1 ..)
    obtain ⟨⟨r4, m4⟩, c4, hW⟩ := hW
    have ha := callW_erecAlloc P.cmp.rcp.alloc c4
    generalize hd : r4.headD 0 = d at ha hW
    obtain ⟨hT4, hg4, hoff, htop, hd41⟩ := erAlloc_stageT ha hT3
    obtain ⟨-, hf4, -, -, -, -, -, -⟩ := erAllocW_spec ha hT3.stage.iw
    rw [entryNeedsW.k_erec_alloc.arm1, hd] at hW
    have hrd4 : erRd m4 = erRd m3 := by
      funext z; simp only [erRd]; rw [hf4.tier _ (by decide) (by decide) (by decide)]
    rw [hrd4, erRd_nd f3] at hW
    generalize ho : erRd m2 (c + (CI.indCaps + Caps.allOff)) = o at hW hall
    replace hW := opt_some hW (entryNeedsW.k_rec_names.eq_1 ..)
    obtain ⟨⟨r5, m5⟩, c5, hW⟩ := hW
    obtain ⟨s5, hs5, -, hW5⟩ := triple_of_callW (s₀ := ⟨m4, Locals.init []⟩)
      (recNames_specW p P.rn.rn n _ d o l) c5
    simp only at hW5
    rw [hs5] at hW5
    obtain ⟨C, hC⟩ := hden
    obtain ⟨cv, dd, -, -, hdc⟩ := ConRon.Bridge.denoteCI_ind_inv hC
    simp only [Frontend.denoteCaps] at hdc
    cases hA : Frontend.denoteNList a.store.ns cap.all with
    | none => simp [hA] at hdc
    | some all =>
    have hall' := hA
    have hall3 : hslice? (erecP m3) o.toNat l.toNat = some cap.all := by
      rw [erecP_nd f3]; exact hall
    have hol : o.toNat + l.toNat ≤ 2 ^ 64 := by
      rcases Nat.eq_zero_or_pos l.toNat with h0 | h0
      · rw [h0]; exact Nat.le_of_lt (UInt64.toNat_lt _)
      · obtain ⟨w, hw, -⟩ := hslice?_atR hall3 (l.toNat - 1) (by omega)
        have := erecP_lt64 hw; omega
    obtain ⟨htsz, hcap⟩ := hT4.stage.iw.topOf d
    have hdl : d.toNat + l.toNat < 2 ^ 41 := by
      have e : erOff d = d.toNat % 2 ^ 40 := rfl
      omega
    obtain ⟨rn, a5, hrun5, hT5, st5, hg5, -, hfr5, -, hsl5, -⟩ :=
      recNames_loop P.rn hT3.stage n m4 m5 a d o l r5 cap.all all [] hW5 hT4 hok
        (hf4.mono (by simp) (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact ctl_quotC.1
          · exact ctl_quotC.2)) hg4 hall3 hall' (by rw [hoff]; exact Nat.le_refl _) (by rw [htop, hoff]; exact Nat.le_refl _) hdl hol
    rw [entryNeedsW.k_rec_names.arm1] at hW
    have hy4 : NdR m4 (y0.names cap.ctors) := NdR.frame hf4 (by decide) (by decide) hy3
    have hy5 : NdR m5 (y0.names cap.ctors) := NdR.frame hfr5 (by decide) (by decide) hy4
    replace hW := opt_some hW (entryNeedsW.k_needs_names_3.eq_1 ..)
    obtain ⟨⟨r6, m6⟩, c6, hW⟩ := hW
    rw [entryNeedsW.k_needs_names_3.arm1] at hW
    obtain ⟨hy6, f6⟩ := needsNames_step Q c6 hy5 hsl5
    have hS6 := (hT5.stage.ndFrame f6).1
    have hT6 := StageT.of_ndw hT5 hS6 (ndFrame_w f6)
    have hg3 : IWGrow m2 m3 := iwGrow_frame f3 ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
    have hg6 : IWGrow m5 m6 := iwGrow_frame f6 ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
    have f45 : MemFrame rnA (nrC ++ [129, 130]) m3 m5 :=
      (hf4.mono (by simp) (by simp)).trans (hfr5.mono (fun _ h => h) (fun x hx => List.mem_append_left _ hx))
    have hJ6 : SolR m6 J :=
      (((hJ2.growF f3 (by decide) ndC_sol hg3.erecGrow).growF f45 (by decide) rnC_sol
        hg5.erecGrow).growF f6 (by decide) ndC_sol hg6.erecGrow)
    have hci6 : decCI (erecP m6) c.toNat = some (.indInfo v cap) := by
      rw [erecP_nd f6]; exact ArrExt.decCI hg5.ext (by rw [erecP_nd f3]; exact hci2)
    obtain ⟨ns, e, hT', hN', f'⟩ := enTail_ok P hW hT6 hJ6 hci6 hy6
    have hg' : IWGrow m6 s'.mem :=
      iwGrow_frame f' ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
    refine ⟨ns, a5, ?_, hT', ConRon.Bridge.RStep.of_istep st5 hrd,
      hg1.trans (hg2.trans (hg3.trans (hg5.trans (hg6.trans hg')))), hN', ?_⟩
    · simp only [StateT.run_bind, hrun5, except_ok_bind, List.nil_append]
      exact e
    · exact (f1.mono (by simp [ndA, enA]) (by simp [ndC, enC])).trans
        ((f2.mono (by simp [ndAW, enA]) (by simp [ndCW, enC])).trans
        ((f3.mono (by simp [ndA, enA]) (by simp [ndC, enC])).trans
        ((f45.mono (A' := enA) (C' := enC)
          (fun b hb => by
            simp only [rnA, List.mem_cons] at hb
            simp only [enA, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
            rcases hb with rfl | rfl | hb <;> simp_all)
          (fun x hx => by
            simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
            simp only [enC, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
            rcases hx with hx | rfl | rfl <;> simp_all)).trans
        ((f6.mono (by simp [ndA, enA]) (by simp [ndC, enC])).trans
        (f'.mono (by simp [ndA, enA]) (by simp [ndC, enC]))))))
  · rw [entryNeedsW.k_needs_const.arm2 _ _ _ _ _ _ hk3] at hW
    obtain ⟨ns, e, hT', hN', f'⟩ := enTail_ok P hW hT2 hJ2 hci2 hy0
    have hg' : IWGrow m2 s'.mem :=
      iwGrow_frame f' ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
    have hfr : MemFrame enA enC m s'.mem :=
      (f1.mono (by simp [ndA, enA]) (by simp [ndC, enC])).trans
        ((f2.mono (by simp [ndAW, enA]) (by simp [ndCW, enC])).trans
        (f'.mono (by simp [ndA, enA]) (by simp [ndC, enC])))
    have hgg : IWGrow m s'.mem := hg1.trans (hg2.trans hg')
    cases ci
    case indInfo v cap => exact absurd (UInt64.toNat_inj.mp (by rw [hk]; rfl)) hk3
    all_goals exact ⟨ns, a, e, hT', ConRon.Bridge.RStep.refl hok hrd, hgg, hN', hfr⟩

end en

end L.Arena
