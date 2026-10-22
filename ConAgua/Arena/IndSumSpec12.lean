import ConAgua.Arena.IndSumSpec11
import ConAgua.Arena.IndSumSpec4
import ConAgua.Arena.IndSumSpec2A
import ConAgua.Arena.RecGenSpec4
import ConAgua.Arena.RecClassSpecB

/-!
# `check_sum_ctor` refines `checkSumCtor` (lane `indproofs2`)

One constructor's type. L splits the twin's body in two: `check_sum_ctor` (the constant check, the
result shape, the parameter pins) and `check_sum_ctor_tail` (the opened residual, the pre-block
resolution, the field sorts); `cscTailT` is the twin's tail verbatim, so `checkSumCtor` is its head
followed by `cscTailT` (`checkSumCtor_eq`). The callees: stubs (`open_pis_at_fvars_f`,
`get_app_fn_f`, `get_app_args_f`, `check_constant_val`, `strip_pis`, `fvar_type_ds`, and those of the
proved callees), `param_levels`, `intern_const` (guarded below `2^32`, as elsewhere),
`field_doms_resolve`/`idx_args_resolve` at the pre-block view `vis0` (the stage relation there is
the restriction of the one at `vis`: `fe₀ = fe.restrictTo vis0`), `check_struct_field_sorts_i`,
`struct_ctor_resid_ok`, `check_struct_doms_at`.

`SumProg p`: the program lookups of this file and the next, bundled (DESIGN.md, lane `indproofs2`
landing 2: a bundle per module instead of 20 hypotheses per statement).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The program lookups of `check_sum_ctor(s)` and their callees. -/
structure SumProg (p : Prog) : Prop where
  ha : p.lookup "iw_alloc" = some iwAlloc
  hc : p.lookup "iw_copy" = some iwCopy
  hsc : p.lookup "sl_cons" = some slCons
  hg : p.lookup "sl_get" = some slGet
  hpf : p.lookup "param_find" = some paramFind
  hpp : p.lookup "param_push" = some paramPush
  hip : p.lookup "intern_param" = some internParam
  hplg : p.lookup "param_levels_go" = some paramLevelsGoL
  hpl : p.lookup "param_levels" = some paramLevelsL
  hcf : p.lookup "const_find" = some constFind
  hcp : p.lookup "const_push" = some constPush
  hic : p.lookup "intern_const" = some internConst
  heq : p.lookup "sl_eq" = some slEq
  hfdr : p.lookup "field_doms_resolve" = some fieldDomsResolveL
  hiar : p.lookup "idx_args_resolve" = some idxArgsResolveL
  hpw : p.lookup "pin_word" = some pinWordL
  het : p.lookup "lvl_eq_true" = some lvlEqTrue
  hcn : p.lookup "sl_contains" = some slContains
  hfsb : p.lookup "check_field_sort_bound" = some checkFieldSortBoundL
  hcfg : p.lookup "check_struct_field_sorts_i_go" = some checkStructFieldSortsIGoL
  hcfs : p.lookup "check_struct_field_sorts_i" = some checkStructFieldSortsIL
  htail : p.lookup "check_sum_ctor_tail" = some checkSumCtorTailL
  hbf : p.lookup "bvar_find" = some bvarFind
  hbp : p.lookup "bvar_push" = some bvarPush
  hib : p.lookup "intern_bvar" = some internBVar
  hpg : p.lookup "struct_ps_at_go" = some structPsAtGoL
  hps : p.lookup "struct_ps_at" = some structPsAtL
  hsr : p.lookup "struct_ctor_resid_ok" = some structCtorResidOkL
  hsd : p.lookup "check_struct_doms_at" = some checkStructDomsAtL
  hctor : p.lookup "check_sum_ctor" = some checkSumCtorL
  hrec2 : p.lookup "rec2" = some rec2
  hcsg : p.lookup "check_sum_ctors_go" = some checkSumCtorsGoL
  hcs : p.lookup "check_sum_ctors" = some checkSumCtorsL

/-! ## `check_sum_ctor_tail`: the word model -/

/-- After the field sorts. -/
def ctlK9 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, r.tail.headD 0], m)
/-- After `idx_args_resolve`: the field sorts. -/
def ctlK8 (n : Nat) (vis isP lg rs nP nF xo xl ao al : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none
    else ctlK9 (fsortsW n m vis isP lg rs nP xo xl (ao + nP) (al - nP) nF)
/-- After `field_doms_resolve`: the index arguments. -/
def ctlK7 (n : Nat) (vis0 vis isP lg rs nP nF xo xl ao al : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none
    else ctlK8 n vis isP lg rs nP nF xo xl ao al (iarW (n + 1) m vis0 (ao + nP) (al - nP))
/-- After `sl_eq` (or its skip): the residual's shape. -/
def ctlK6 (n : Nat) (vis0 vis nP nIdx rs isP lg nF xo xl hd xfn ao al : Word) (m : Mem) : Option Word → Option (List Word × Mem)
  | none => none
  | some e => if xfn ≠ hd ∨ al ≠ nP + nIdx ∨ e = 0 then none
    else ctlK7 n vis0 vis isP lg rs nP nF xo xl ao al (fdrW (n + 1) m vis0 xo xl)
/-- After `get_app_args_f`: the parameter prefix. -/
def ctlK5 (n : Nat) (vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl hd xfn : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ra, m) => ctlK6 n vis0 vis nP nIdx rs isP lg nF xo xl hd xfn (ra.headD 0) (ra.tail.headD 0) m
      (if nP ≤ ra.tail.headD 0 then eqW (n + 1) m (ra.headD 0) nP cqO cqL else some 0)
/-- After `get_app_fn_f`. -/
def ctlK4 (n : Nat) (vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb hd : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rf, m) => ctlK5 n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl hd (rf.headD 0)
      (stubM "get_app_args_f" m [CWF, xb])
/-- After `intern_const`: the guard, `get_app_fn_f`. -/
def ctlK3 (n : Nat) (vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (hd, m) => if 4294967296 ≤ hd then none
    else ctlK4 n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb hd (stubM "get_app_fn_f" m [CWF, xb])
/-- After `param_levels`: the family's head. -/
def ctlK2 (n : Nat) (vis0 vis T nP nIdx rs isP lg nF cqO cqL xo xl xb : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ru, m) => ctlK3 n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb (ceinternW m T (ru.headD 0))
/-- After `open_pis_at_fvars_f`. -/
def ctlK1 (n : Nat) (vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rx, m) => if rx.headD 0 = 0 then none
    else ctlK2 n vis0 vis T nP nIdx rs isP lg nF cqO cqL (rx.tail.headD 0) (rx.tail.tail.headD 0)
      (rx.tail.tail.tail.headD 0) (plW (n + 1) m lo ll)

/-- **The model of `check_sum_ctor_tail(vis0, vis, T, lo, ll, nP, nIdx, rs, isP, lg, nF, cqO, cqL,
cqB)`** (its callees at exec fuel `n + 1`). -/
def ctlW (n : Nat) (m : Mem) (vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL cqB : Word) :
    Option (List Word × Mem) :=
  ctlK1 n vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL (stubM "open_pis_at_fvars_f" m [nF, cqB, nP])

section arms
variable (n : Nat) (m : Mem) (vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL xo xl xb hd xfn ao al e : Word)
  (r : List Word)
theorem ctlK9_some : ctlK9 (some (r, m)) = some ([r.headD 0, r.tail.headD 0], m) := rfl
theorem ctlK8_no (h : r.headD 0 = 0) : ctlK8 n vis isP lg rs nP nF xo xl ao al (some (r, m)) = none := by
  simp only [ctlK8]; rw [if_pos h]
theorem ctlK8_yes (h : r.headD 0 ≠ 0) : ctlK8 n vis isP lg rs nP nF xo xl ao al (some (r, m)) =
    ctlK9 (fsortsW n m vis isP lg rs nP xo xl (ao + nP) (al - nP) nF) := by simp only [ctlK8]; rw [if_neg h]
theorem ctlK7_no (h : r.headD 0 = 0) :
    ctlK7 n vis0 vis isP lg rs nP nF xo xl ao al (some (r, m)) = none := by simp only [ctlK7]; rw [if_pos h]
theorem ctlK7_yes (h : r.headD 0 ≠ 0) : ctlK7 n vis0 vis isP lg rs nP nF xo xl ao al (some (r, m)) =
    ctlK8 n vis isP lg rs nP nF xo xl ao al (iarW (n + 1) m vis0 (ao + nP) (al - nP)) := by
  simp only [ctlK7]; rw [if_neg h]
theorem ctlK6_no (h : xfn ≠ hd ∨ al ≠ nP + nIdx ∨ e = 0) :
    ctlK6 n vis0 vis nP nIdx rs isP lg nF xo xl hd xfn ao al m (some e) = none := by
  simp only [ctlK6]; rw [if_pos h]
theorem ctlK6_yes (h : ¬ (xfn ≠ hd ∨ al ≠ nP + nIdx ∨ e = 0)) :
    ctlK6 n vis0 vis nP nIdx rs isP lg nF xo xl hd xfn ao al m (some e) =
      ctlK7 n vis0 vis isP lg rs nP nF xo xl ao al (fdrW (n + 1) m vis0 xo xl) := by
  simp only [ctlK6]; rw [if_neg h]
theorem ctlK5_some : ctlK5 n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl hd xfn (some (r, m)) =
    ctlK6 n vis0 vis nP nIdx rs isP lg nF xo xl hd xfn (r.headD 0) (r.tail.headD 0) m
      (if nP ≤ r.tail.headD 0 then eqW (n + 1) m (r.headD 0) nP cqO cqL else some 0) := rfl
theorem ctlK4_some : ctlK4 n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb hd (some (r, m)) =
    ctlK5 n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl hd (r.headD 0)
      (stubM "get_app_args_f" m [CWF, xb]) := rfl
theorem ctlK3_big (h : 4294967296 ≤ hd) :
    ctlK3 n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb (some (hd, m)) = none := by simp only [ctlK3]; rw [if_pos h]
theorem ctlK3_ok (h : ¬ 4294967296 ≤ hd) :
    ctlK3 n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb (some (hd, m)) =
      ctlK4 n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb hd (stubM "get_app_fn_f" m [CWF, xb]) := by
  simp only [ctlK3]; rw [if_neg h]
theorem ctlK2_some : ctlK2 n vis0 vis T nP nIdx rs isP lg nF cqO cqL xo xl xb (some (r, m)) =
    ctlK3 n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb (ceinternW m T (r.headD 0)) := rfl
theorem ctlK1_no (h : r.headD 0 = 0) :
    ctlK1 n vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL (some (r, m)) = none := by simp only [ctlK1]; rw [if_pos h]
theorem ctlK1_yes (h : r.headD 0 ≠ 0) :
    ctlK1 n vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL (some (r, m)) =
      ctlK2 n vis0 vis T nP nIdx rs isP lg nF cqO cqL (r.tail.headD 0) (r.tail.tail.headD 0)
        (r.tail.tail.tail.headD 0) (plW (n + 1) m lo ll) := by simp only [ctlK1]; rw [if_neg h]
end arms
attribute [ind_grind] ctlK9_some ctlK8_no ctlK8_yes ctlK7_no ctlK7_yes ctlK6_no ctlK6_yes ctlK5_some
  ctlK4_some ctlK3_big ctlK3_ok ctlK2_some ctlK1_no ctlK1_yes

set_option maxHeartbeats 2000000 in
theorem ctlW_spec (p : Prog) (hP : SumProg p) (n : Nat) (s₀ : St)
    (vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL cqB : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 2)) "check_sum_ctor_tail"
      [vis0, vis, T, lo, ll, nP, nIdx, rs, isP, lg, nF, cqO, cqL, cqB]
    ⦃fun r s' => LocEq s' s₀ ∧
      ctlW n s₀.mem vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL cqB = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.htail]
  simp only [callFn, checkSumCtorTailL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      stubM_spec p "open_pis_at_fvars_f" (n + 1),
      plW_spec p hP.ha hP.hc hP.hsc hP.hg hP.hpf hP.hpp hP.hip hP.hplg hP.hpl (n + 1),
      internConst_spec p hP.hcf hP.hcp hP.hic (n + 1),
      stubM_spec p "get_app_fn_f" (n + 1), stubM_spec p "get_app_args_f" (n + 1),
      slEq_spec p hP.heq (n + 1), fdrW_spec p hP.hfdr (n + 1), iarW_spec p hP.hiar (n + 1),
      fsortsW_spec p hP.hg hP.hpw hP.het hP.hcn hP.hfsb hP.hcfg hP.ha hP.hcfs n] <;>
    finish (gen := 30) (instances := 5000) [ctlW]

/-! ## The relation to the twin: pieces -/

/-- The twin's tail of `checkSumCtor` (from the opened field telescope on), verbatim. -/
def cscTailT (fe₀ fe : IFEnv) (T : NIdx) (lps : List NIdx) (nP nIdx : Nat) (resSort : LIdx)
    (isProp large : Bool) (cvCa : IConstantVal) (nF : Nat) (cq : List EIdx × EIdx) :
    AM (IConstantVal × List LIdx) := do
  let xq ← unwrapOr (← openPisAtFvarsF nF cq.2 nP)
    (.notImplemented "direct sum: constructor field telescope")
  let us ← paramLevels lps
  let hd ← internE (.const T us)
  let xfn ← getAppFn coreWalkFuel xq.2
  let xargs ← getAppArgs coreWalkFuel xq.2
  unless xfn == hd && xargs.take nP == cq.1 && xargs.length == nP + nIdx do
    fail (.notImplemented "direct sum: opened constructor residual")
  let idxArgs := xargs.drop nP
  unless ← fieldDomsResolve fe₀ xq.1 do
    fail (.notImplemented "direct sum: field domain after the block")
  unless ← idxArgsResolve fe₀ idxArgs do
    fail (.invalid "direct sum: index expression mentions the block")
  let sorts ← checkStructFieldSortsI .verified fe isProp large resSort nP xq.1
    idxArgs nF
  pure (cvCa, sorts)

theorem sumGetD1 (r : List Word) : r.getD 1 0 = r.tail.headD 0 := by
  rcases r with _ | ⟨a, _ | ⟨b, r⟩⟩ <;> rfl
theorem sumGetD2 (r : List Word) : r.getD 2 0 = r.tail.tail.headD 0 := by
  rcases r with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩ <;> rfl
theorem sumGetD0 (r : List Word) : r.getD 0 0 = r.headD 0 := by
  rcases r with _ | ⟨a, r⟩ <;> rfl

/-- `param_levels` as a `Sim`. -/
theorem plSim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (k : Nat) (m : Mem)
    (a : AState) (o l : Word) (lps : List NIdx) (hS : StageR dn vis fe m a)
    (hd : decHL m o.toNat l.toNat = some lps) (hb : o.toNat + l.toNat ≤ iwTop m) :
    Sim (plW k m o l) (paramLevels lps) a (fun r x m' a' => StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      H (r.headD 0) ∧ decI (r.headD 0) = x) := fun r m' e => by
  obtain ⟨x, a', h1, h2⟩ := plW_ok dn vis fe k m m' a o l lps r e hS hd (hS.lt64 hb) hb
  exact ⟨x, a', h1, h2⟩

/-- `intern_const` as a `Sim`. -/
theorem ceSim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (m : Mem) (a : AState)
    (f x : Word) (hS : StageR dn vis fe m a) (hf : H f) (hx : H x) :
    Sim (ceinternW m f x) (internE (.const (decI (k := .name) f) (decI (k := .levels) x))) a
      (fun r e m' a' => e = decI r ∧ StageR dn vis fe m' a' ∧ IWGrow m m') := fun r m' e => by
  obtain ⟨a', h1, h2, h3⟩ := internConst_stage hS f x hf hx e
  exact ⟨_, a', h1, rfl, h2, h3⟩

/-- `field_doms_resolve` as a `Sim`. -/
theorem fdrSim {dn : NIdx → Option ConLeche.Name} {v : Word} {fe : IFEnv} (n : Nat) (m : Mem)
    (a : AState) (o l : Word) (xs : List EIdx) (hS : StageR dn v fe m a)
    (hd : decHL m o.toNat l.toNat = some xs) (hb : o.toNat + l.toNat ≤ iwTop m) :
    Sim (fdrW n m v o l) (fieldDomsResolve fe xs) a
      (fun r b m' a' => KeepPost dn v fe decW0B m m' a' r b) := fun r m' e => by
  obtain ⟨x, a', h1, h2⟩ := fdrW_ok dn fe n m m' a v o l xs r e hS hd (hS.lt64 hb) hb
  exact ⟨x, a', h1, h2⟩

/-- `idx_args_resolve` as a `Sim`. -/
theorem iarSim {dn : NIdx → Option ConLeche.Name} {v : Word} {fe : IFEnv} (n : Nat) (m : Mem)
    (a : AState) (o l : Word) (xs : List EIdx) (hS : StageR dn v fe m a)
    (hd : decHL m o.toNat l.toNat = some xs) (hb : o.toNat + l.toNat ≤ iwTop m) :
    Sim (iarW n m v o l) (idxArgsResolve fe xs) a
      (fun r b m' a' => KeepPost dn v fe decW0B m m' a' r b) := fun r m' e => by
  obtain ⟨x, a', h1, h2⟩ := iarW_ok dn fe n m m' a v o l xs r e hS hd (hS.lt64 hb) hb
  exact ⟨x, a', h1, h2⟩

/-- A callee run at the pre-block view `vis0` (the restriction), back at `vis`. -/
theorem sumKeep_restrict {dn : NIdx → Option ConLeche.Name} {vis vis0 : Word} {fe : IFEnv}
    {m m' : Mem} {a' : AState} {r : List Word} {b : Bool} (hv : fe.visibleBelow = vis.toNat)
    (h : KeepPost dn vis0 (fe.restrictTo vis0.toNat) decW0B m m' a' r b) :
    StageR dn vis fe m' a' ∧ IWGrow m m' ∧ (r.headD 0 != 0) = b :=
  ⟨h.1.unrestrict hv, h.2.1, h.2.2.1⟩

/-- The `unless` of a passed test. -/
theorem sumUnless_true {α : Type} {c : Bool} (hc : c = true) (e : CheckError) (k : AM α) :
    ((unless c do fail e) >>= fun _ => k) = k := by subst hc; rfl

/-- **`check_sum_ctor_tail`'s model refines `cscTailT`** (the twin's tail of `checkSumCtor`), the
pre-block environment the restriction of `fe` to `vis0`. -/
theorem ctlW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) (m : Mem)
    (a : AState) (vis0 T lo ll nP nIdx rs isP lg nF cqO cqL cqB : Word) (lps : List NIdx)
    (cq1 : List EIdx) (cvCa : IConstantVal) (hS : StageR dn vis fe m a) (hT : H T)
    (hlps : decHL m lo.toNat ll.toNat = some lps) (hlb : lo.toNat + ll.toNat ≤ iwTop m)
    (hcq : decHL m cqO.toNat cqL.toNat = some cq1) (hcqb : cqO.toNat + cqL.toNat ≤ iwTop m)
    (hcqB : H cqB) (hrs : H rs) (hni : nP.toNat + nIdx.toNat < 2 ^ 64)
    (hnf : nP.toNat + nF.toNat < 2 ^ 64) :
    Sim (ctlW n m vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL cqB)
      (cscTailT (fe.restrictTo vis0.toNat) fe (decI T) lps nP.toNat nIdx.toNat (decI rs) (isP != 0)
        (lg != 0) cvCa nF.toNat (cq1, decI cqB)) a
      (fun r x m' a' => StageR dn vis fe m' a' ∧ IWGrow m m' ∧ x.1 = cvCa ∧
        decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some x.2 ∧
        (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m') := by
  have hv := hS.1.env.vis
  unfold ctlW cscTailT
  refine Sim.bindK (K := ctlK1 n vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL) rfl (fun _ _ => rfl)
    (sumSim_of_relAM (openPisAtFvarsF_spec dn vis fe nF cqB nP hcqB) hS) fun rx ox m1 a1 hQ => ?_
  obtain ⟨hS1, hg1, hdec1⟩ := hQ
  by_cases h0 : rx.headD 0 = 0
  · rw [ctlK1_no n m1 vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL rx h0]; exact Sim.of_none
  rw [ctlK1_yes n m1 vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL rx h0]
  cases ox with
  | none => exact absurd hdec1 h0
  | some xq =>
  obtain ⟨xl1, xb⟩ := xq
  obtain ⟨-, ⟨hxl, hxlb⟩, hxb, hxbd⟩ := hdec1
  rw [sumGetD1, sumGetD2] at hxl hxlb
  rw [drop3_eq] at hxb hxbd
  refine Sim.bind_twin (x := (xl1, xb)) (a₁ := a1) rfl ?_
  generalize hxo : rx.tail.headD 0 = xo at hxl hxlb
  generalize hxlw : rx.tail.tail.headD 0 = xlw at hxl hxlb
  generalize hxbw : rx.tail.tail.tail.headD 0 = xbw at hxb hxbd
  -- `param_levels`
  refine Sim.bindK (K := ctlK2 n vis0 vis T nP nIdx rs isP lg nF cqO cqL xo xlw xbw) rfl
    (fun _ _ => rfl) (plSim (n + 1) m1 a1 lo ll lps hS1 (by rw [decHL_grow hg1 hlb]; exact hlps)
      (by have := hg1.1; omega)) fun ru us m2 a2 hQ => ?_
  obtain ⟨hS2, hg2, hu, hus⟩ := hQ
  subst hus
  rw [ctlK2_some]
  -- `intern_const`
  refine Sim.bindK (K := ctlK3 n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xlw xbw) rfl
    (fun _ _ => rfl) (ceSim m2 a2 T (ru.headD 0) hS2 hT hu) fun hd e m3 a3 hQ => ?_
  obtain ⟨he, hS3, hg3⟩ := hQ
  subst he
  by_cases hbig : 4294967296 ≤ hd
  · rw [ctlK3_big n m3 vis0 vis nP nIdx rs isP lg nF cqO cqL xo xlw xbw hd hbig]; exact Sim.of_none
  rw [ctlK3_ok n m3 vis0 vis nP nIdx rs isP lg nF cqO cqL xo xlw xbw hd hbig]
  have hd32 : H hd := by have : ¬ (4294967296 : Nat) ≤ hd.toNat := hbig; show hd.toNat < 2 ^ 32; omega
  -- `get_app_fn_f`
  have h4 := getAppFn_spec dn vis fe CWF xbw hxb
  rw [CWF_eq, hxbd] at h4
  refine Sim.bindK (K := ctlK4 n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xlw xbw hd) rfl
    (fun _ _ => rfl) (sumSim_of_relAM h4 hS3) fun rf xfn m4 a4 hQ => ?_
  obtain ⟨hS4, hg4, hf32, hfd⟩ := hQ
  rw [ctlK4_some]
  -- `get_app_args_f`
  have h5 := getAppArgs_spec dn vis fe CWF xbw hxb
  rw [CWF_eq, hxbd] at h5
  refine Sim.bindK (K := ctlK5 n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xlw hd (rf.headD 0)) rfl
    (fun _ _ => rfl) (sumSim_of_relAM h5 hS4) fun ra args m5 a5 hQ => ?_
  obtain ⟨hS5, hg5, hargs, hab⟩ := hQ
  rw [sumGetD0, sumGetD1] at hargs hab
  rw [ctlK5_some]
  subst hfd
  generalize hao : ra.headD 0 = ao at hargs hab
  generalize hal : ra.tail.headD 0 = al at hargs hab
  have hlen : args.length = al.toNat := decHL_length m5 hargs
  have hg15 := ((hg2.trans hg3).trans hg4).trans hg5
  have hg05 := hg1.trans hg15
  cases heo : (if nP ≤ al then eqW (n + 1) m5 ao nP cqO cqL else some 0) with
  | none => exact Sim.of_none
  | some e =>
  by_cases hfail : rf.headD 0 ≠ hd ∨ al ≠ nP + nIdx ∨ e = 0
  · rw [ctlK6_no n m5 vis0 vis nP nIdx rs isP lg nF xo xlw hd (rf.headD 0) ao al e hfail]; exact Sim.of_none
  rw [ctlK6_yes n m5 vis0 vis nP nIdx rs isP lg nF xo xlw hd (rf.headD 0) ao al e hfail]
  have hfn : rf.headD 0 = hd := by
    by_cases h : rf.headD 0 = hd
    · exact h
    · exact absurd (Or.inl h) hfail
  have hln : al = nP + nIdx := by
    by_cases h : al = nP + nIdx
    · exact h
    · exact absurd (Or.inr (Or.inl h)) hfail
  have he0 : e ≠ 0 := fun h => hfail (Or.inr (Or.inr h))
  have hle : nP ≤ al := by
    by_cases h : nP ≤ al
    · exact h
    · rw [if_neg h] at heo; cases heo; exact absurd rfl he0
  rw [if_pos hle] at heo
  have hle' : nP.toNat ≤ al.toNat := UInt64.le_iff_toNat_le.mp hle
  have hcq5 : decHL m5 cqO.toNat cqL.toNat = some cq1 := by rw [decHL_grow hg05 hcqb]; exact hcq
  have htk := decHL_take hargs nP.toNat hle'
  obtain ⟨ws1, hs1, hm1, hb1⟩ := slR_of_decHL m5 _ _ _ htk (hS5.lt64 (by omega))
  obtain ⟨ws2, hs2, hm2, hb2⟩ := slR_of_decHL m5 _ _ _ hcq5 (hS5.lt64 (by have := hg05.1; omega))
  simp only [UInt64.ofNat_toNat] at hs1 hs2
  have heq := eqW_ok (n + 1) m5 _ _ _ _ e ws1 ws2 hs1 hs2 heo
  have hws : ws1 = ws2 := by
    by_cases h : ws1 = ws2
    · exact h
    · rw [heq, if_neg h] at he0; exact absurd rfl he0
  have htake : args.take nP.toNat = cq1 := by rw [hm1, hm2, hws]
  have hc : (decI (rf.headD 0) == (decI hd : EIdx) && args.take nP.toNat == cq1 &&
      args.length == nP.toNat + nIdx.toNat) = true := by
    rw [hfn, htake, hlen, hln, sum_toNat_add hni]; simp
  simp only [hc, ite_true]
  have hT5 : ao.toNat + al.toNat < 2 ^ 64 := hS5.lt64 hab
  have hxl5 : decHL m5 xo.toNat xlw.toNat = some xl1 := by rw [decHL_grow hg15 hxlb]; exact hxl
  have hxlb5 : xo.toNat + xlw.toNat ≤ iwTop m5 := by have := hg15.1; omega
  -- `field_doms_resolve`, at the pre-block view
  refine Sim.bindK (K := ctlK7 n vis0 vis isP lg rs nP nF xo xlw ao al) rfl (fun _ _ => rfl)
    (fdrSim (n + 1) m5 a5 xo xlw xl1 (hS5.restrict vis0) hxl5 hxlb5) fun r1 b1 m6 a6 hQ => ?_
  obtain ⟨hS6, hg6, hb1⟩ := sumKeep_restrict hv hQ
  by_cases h1 : r1.headD 0 = 0
  · rw [ctlK7_no (h := h1)]; exact Sim.of_none
  rw [ctlK7_yes (h := h1)]
  have hb1' : b1 = true := by rw [← hb1]; simpa using h1
  subst hb1'
  simp only [ite_true]
  -- `idx_args_resolve`
  have hao : (ao + nP).toNat = ao.toNat + nP.toNat := sum_toNat_add (by omega)
  have halp : (al - nP).toNat = al.toNat - nP.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ hle]
  have hdrop6 : decHL m6 (ao + nP).toNat (al - nP).toNat = some (args.drop nP.toNat) := by
    rw [hao, halp]
    exact decHL_drop nP.toNat (by rw [decHL_grow hg6 hab]; exact hargs) hle'
  have hdb6 : (ao + nP).toNat + (al - nP).toNat ≤ iwTop m6 := by
    rw [hao, halp]; have := hg6.1; omega
  refine Sim.bindK (K := ctlK8 n vis isP lg rs nP nF xo xlw ao al) rfl (fun _ _ => rfl)
    (iarSim (n + 1) m6 a6 (ao + nP) (al - nP) (args.drop nP.toNat) (hS6.restrict vis0) hdrop6 hdb6)
    fun r2 b2 m7 a7 hQ => ?_
  obtain ⟨hS7, hg7, hb2⟩ := sumKeep_restrict hv hQ
  by_cases h2 : r2.headD 0 = 0
  · rw [ctlK8_no (h := h2)]; exact Sim.of_none
  rw [ctlK8_yes (h := h2)]
  have hb2' : b2 = true := by rw [← hb2]; simpa using h2
  subst hb2'
  simp only [ite_true]
  -- the field sorts
  have hg67 := hg6.trans hg7
  refine Sim.bindK (K := ctlK9) rfl (fun _ _ => rfl)
    (fsortsW_ok n m7 a7 isP lg rs nP xo xlw (ao + nP) (al - nP) nF xl1 (args.drop nP.toNat) hS7
      (by rw [decHL_grow hg67 hxlb5]; exact hxl5) (by have := hg67.1; omega)
      (by rw [decHL_grow hg7 hdb6]; exact hdrop6) (by have := hg7.1; omega) hrs hnf)
    fun r9 sorts m8 a8 hQ => ?_
  obtain ⟨hS8, hg8, hd8, hb8⟩ := hQ
  exact Sim.ret ⟨hS8, (((hg1.trans hg15).trans hg67).trans hg8), rfl, by simpa using hd8,
    by simpa using hb8⟩

/-! ## `check_sum_ctor`: the word model -/

/-- After the tail. -/
def ctorK9 (cvC : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([cvC, r.headD 0, r.tail.headD 0], m)
/-- After `check_struct_doms_at`: the tail. -/
def ctorK8 (n : Nat) (vis0 vis T lo ll nP nIdx rs isP lg nF cvC cqO cqL cqB : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => ctorK9 cvC (ctlW n m vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL cqB)
/-- After `fvar_type_ds`: the binder domains. -/
def ctorK7 (n : Nat) (vis0 vis T lo ll nP nIdx rs isP lg nF cvC cqO cqL cqB : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rt, m) => ctorK8 n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cqO cqL cqB
      (sdomsW (n + 2) m vis 0 cqO cqL (rt.headD 0) (rt.tail.headD 0) nP)
/-- After the type former's opened telescope. -/
def ctorK6 (n : Nat) (vis0 vis T lo ll nP nIdx rs isP lg nF cvC cqO cqL cqB : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rq, m) => if rq.headD 0 = 0 then none
    else ctorK7 n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cqO cqL cqB
      (stubM "fvar_type_ds" m [rq.tail.headD 0, rq.tail.tail.headD 0])
/-- After the constructor's opened telescope. -/
def ctorK5 (n : Nat) (vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rc, m) => if rc.headD 0 = 0 then none
    else ctorK6 n vis0 vis T lo ll nP nIdx rs isP lg nF cvC (rc.tail.headD 0) (rc.tail.tail.headD 0)
      (rc.tail.tail.tail.headD 0) (stubM "open_pis_at_fvars_f" m [nP, rdW (m.arr64 EREC) (cvTa + 3), 0])
/-- After `struct_ctor_resid_ok`. -/
def ctorK4 (n : Nat) (vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rr, m) => if rr.headD 0 = 0 then none
    else ctorK5 n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa
      (stubM "open_pis_at_fvars_f" m [nP, rdW (m.arr64 EREC) (cvC + 3), 0])
/-- After `strip_pis`. -/
def ctorK3 (n : Nat) (vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rs', m) => if rs'.headD 0 = 0 then none
    else ctorK4 n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa
      (srW (n + 2) m T lo ll nP nF nIdx (rs'.tail.tail.tail.headD 0))
/-- After `check_constant_val`. -/
def ctorK2 (n : Nat) (vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => ctorK3 n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa
      (stubM "strip_pis" m [nP + nF, rdW (m.arr64 EREC) (cvC + 3)])

/-- **The model of `check_sum_ctor(vis0, vis, T, lo, ll, nP, nIdx, rs, isP, lg, cvC, nF, cvTa)`**
(its callees at exec fuel `n + 2`). -/
def ctorW (n : Nat) (m : Mem) (vis0 vis T lo ll nP nIdx rs isP lg cvC nF cvTa : Word) :
    Option (List Word × Mem) :=
  ctorK2 n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa (stubM "check_constant_val" m [vis, cvC])

section arms
variable (n : Nat) (m : Mem) (vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa cqO cqL cqB : Word)
  (r : List Word)
theorem ctorK9_some : ctorK9 cvC (some (r, m)) = some ([cvC, r.headD 0, r.tail.headD 0], m) := rfl
theorem ctorK8_some : ctorK8 n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cqO cqL cqB (some (r, m)) =
    ctorK9 cvC (ctlW n m vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL cqB) := rfl
theorem ctorK7_some : ctorK7 n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cqO cqL cqB (some (r, m)) =
    ctorK8 n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cqO cqL cqB
      (sdomsW (n + 2) m vis 0 cqO cqL (r.headD 0) (r.tail.headD 0) nP) := rfl
theorem ctorK6_no (h : r.headD 0 = 0) :
    ctorK6 n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cqO cqL cqB (some (r, m)) = none := by
  simp only [ctorK6]; rw [if_pos h]
theorem ctorK6_yes (h : r.headD 0 ≠ 0) :
    ctorK6 n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cqO cqL cqB (some (r, m)) =
      ctorK7 n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cqO cqL cqB
        (stubM "fvar_type_ds" m [r.tail.headD 0, r.tail.tail.headD 0]) := by
  simp only [ctorK6]; rw [if_neg h]
theorem ctorK5_no (h : r.headD 0 = 0) :
    ctorK5 n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa (some (r, m)) = none := by
  simp only [ctorK5]; rw [if_pos h]
theorem ctorK5_yes (h : r.headD 0 ≠ 0) :
    ctorK5 n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa (some (r, m)) =
      ctorK6 n vis0 vis T lo ll nP nIdx rs isP lg nF cvC (r.tail.headD 0) (r.tail.tail.headD 0)
        (r.tail.tail.tail.headD 0)
        (stubM "open_pis_at_fvars_f" m [nP, rdW (m.arr64 EREC) (cvTa + 3), 0]) := by
  simp only [ctorK5]; rw [if_neg h]
theorem ctorK4_no (h : r.headD 0 = 0) :
    ctorK4 n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa (some (r, m)) = none := by
  simp only [ctorK4]; rw [if_pos h]
theorem ctorK4_yes (h : r.headD 0 ≠ 0) :
    ctorK4 n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa (some (r, m)) =
      ctorK5 n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa
        (stubM "open_pis_at_fvars_f" m [nP, rdW (m.arr64 EREC) (cvC + 3), 0]) := by
  simp only [ctorK4]; rw [if_neg h]
theorem ctorK3_no (h : r.headD 0 = 0) :
    ctorK3 n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa (some (r, m)) = none := by
  simp only [ctorK3]; rw [if_pos h]
theorem ctorK3_yes (h : r.headD 0 ≠ 0) :
    ctorK3 n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa (some (r, m)) =
      ctorK4 n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa
        (srW (n + 2) m T lo ll nP nF nIdx (r.tail.tail.tail.headD 0)) := by
  simp only [ctorK3]; rw [if_neg h]
theorem ctorK2_some : ctorK2 n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa (some (r, m)) =
    ctorK3 n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa
      (stubM "strip_pis" m [nP + nF, rdW (m.arr64 EREC) (cvC + 3)]) := rfl
end arms
attribute [ind_grind] ctorK9_some ctorK8_some ctorK7_some ctorK6_no ctorK6_yes ctorK5_no ctorK5_yes
  ctorK4_no ctorK4_yes ctorK3_no ctorK3_yes ctorK2_some

set_option maxHeartbeats 4000000 in
theorem ctorW_spec (p : Prog) (hP : SumProg p) (n : Nat) (s₀ : St)
    (vis0 vis T lo ll nP nIdx rs isP lg cvC nF cvTa : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 3)) "check_sum_ctor"
      [vis0, vis, T, lo, ll, nP, nIdx, rs, isP, lg, cvC, nF, cvTa]
    ⦃fun r s' => LocEq s' s₀ ∧
      ctorW n s₀.mem vis0 vis T lo ll nP nIdx rs isP lg cvC nF cvTa = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.hctor]
  simp only [callFn, checkSumCtorL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      stubM_spec p "check_constant_val" (n + 2), stubM_spec p "strip_pis" (n + 2),
      srW_spec p hP.ha hP.hc hP.hsc hP.hg hP.hpf hP.hpp hP.hip hP.hplg hP.hpl hP.hcf hP.hcp hP.hic
        hP.hbf hP.hbp hP.hib hP.hpg hP.hps hP.heq hP.hsr (n + 2),
      stubM_spec p "open_pis_at_fvars_f" (n + 2), stubM_spec p "fvar_type_ds" (n + 2),
      sdomsW_spec p hP.hg hP.hsd (n + 2), ctlW_spec p hP n] <;>
    finish (gen := 30) (instances := 5000) [ctorW, rdW_eq]

end L.Ind
