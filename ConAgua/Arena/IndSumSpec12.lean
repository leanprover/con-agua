import ConAgua.Arena.IndSumSpec11
import ConAgua.Arena.IndSumSpec4
import ConAgua.Arena.RecGenSpec4
import ConAgua.Arena.IndSumSpec2C
import ConAgua.Arena.IndSim

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

noncomputable section

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
  ad : AdF p
  hip : p.lookup "intern_param" = some internParam
  hplg : p.lookup "param_levels_go" = some paramLevelsGoL
  hpl : p.lookup "param_levels" = some paramLevelsL
  hil : IlF p
  hcf : p.lookup "const_find" = some constFind
  hcp : p.lookup "const_push" = some constPush
  hic : p.lookup "intern_const" = some internConst
  heq : p.lookup "sl_eq" = some slEq
  hfdr : p.lookup "field_doms_resolve" = some fieldDomsResolveL
  hiar : p.lookup "idx_args_resolve" = some idxArgsResolveL
  hcr : CrfF p
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
  hcs : p.lookup "check_sum_ctors" = some checkSumCtorsL
  strip : StripProg p

/-! ## `check_sum_ctor_tail`: the word model -/

/-- After the field sorts. -/
def ctlK9 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, r.tail.headD 0], m)
/-- After `idx_args_resolve`: the field sorts. -/
def ctlK8 (cR : CallM) (n : Nat) (vis isP lg rs nP nF xo xl ao al : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none
    else ctlK9 (fsortsW cR n m vis isP lg rs nP xo xl (ao + nP) (al - nP) nF)
/-- After `field_doms_resolve`: the index arguments. -/
def ctlK7 (cR : CallM) (n : Nat) (vis0 vis isP lg rs nP nF xo xl ao al : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none
    else ctlK8 cR n vis isP lg rs nP nF xo xl ao al (iarW (n + 1) m vis0 (ao + nP) (al - nP))
/-- After `sl_eq` (or its skip): the residual's shape. -/
def ctlK6 (cR : CallM) (n : Nat) (vis0 vis nP nIdx rs isP lg nF xo xl hd xfn ao al : Word) (m : Mem) : Option Word → Option (List Word × Mem)
  | none => none
  | some e => if xfn ≠ hd ∨ al ≠ nP + nIdx ∨ e = 0 then none
    else ctlK7 cR n vis0 vis isP lg rs nP nF xo xl ao al (fdrW (n + 1) m vis0 xo xl)
/-- After `get_app_args_f`: the parameter prefix. -/
def ctlK5 (cR : CallM) (n : Nat) (vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl hd xfn : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ra, m) => ctlK6 cR n vis0 vis nP nIdx rs isP lg nF xo xl hd xfn (ra.headD 0) (ra.tail.headD 0) m
      (if nP ≤ ra.tail.headD 0 then eqW (n + 1) m (ra.headD 0) nP cqO cqL else some 0)
/-- After `get_app_fn_f`. -/
def ctlK4 (cR : CallM) (n : Nat) (vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb hd : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rf, m) => ctlK5 cR n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl hd (rf.headD 0)
      (gaaF m [CWF, xb])
/-- After `intern_const`: the guard, `get_app_fn_f`. -/
def ctlK3 (cR : CallM) (n : Nat) (vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (hd, m) => if 4294967296 ≤ hd then none
    else ctlK4 cR n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb hd (gafF m [CWF, xb])
/-- After `param_levels`: the family's head. -/
def ctlK2 (cR : CallM) (n : Nat) (vis0 vis T nP nIdx rs isP lg nF cqO cqL xo xl xb : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ru, m) => ctlK3 cR n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb (ceinternW m T (ru.headD 0))
/-- After `open_pis_at_fvars_f`. -/
def ctlK1 (cR : CallM) (n : Nat) (vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rx, m) => if rx.headD 0 = 0 then none
    else ctlK2 cR n vis0 vis T nP nIdx rs isP lg nF cqO cqL (rx.tail.headD 0) (rx.tail.tail.headD 0)
      (rx.tail.tail.tail.headD 0) (plW (n + 1) m lo ll)

/-- **The model of `check_sum_ctor_tail(vis0, vis, T, lo, ll, nP, nIdx, rs, isP, lg, nF, cqO, cqL,
cqB)`** (its callees at exec fuel `n + 1`). -/
def ctlW (cR : CallM) (n : Nat) (m : Mem) (vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL cqB : Word) :
    Option (List Word × Mem) :=
  ctlK1 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL (cR (n + 1) "open_pis_at_fvars_f" [nF, cqB, nP] m)

section arms
variable (cR : CallM) (n : Nat) (m : Mem) (vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL xo xl xb hd xfn ao al e : Word)
  (r : List Word)
theorem ctlK9_some : ctlK9 (some (r, m)) = some ([r.headD 0, r.tail.headD 0], m) := rfl
theorem ctlK8_no (h : r.headD 0 = 0) : ctlK8 cR n vis isP lg rs nP nF xo xl ao al (some (r, m)) = none := by
  simp only [ctlK8]; rw [ite_eq_left h]
theorem ctlK8_yes (h : r.headD 0 ≠ 0) : ctlK8 cR n vis isP lg rs nP nF xo xl ao al (some (r, m)) =
    ctlK9 (fsortsW cR n m vis isP lg rs nP xo xl (ao + nP) (al - nP) nF) := by simp only [ctlK8]; rw [ite_eq_right h]
theorem ctlK7_no (h : r.headD 0 = 0) :
    ctlK7 cR n vis0 vis isP lg rs nP nF xo xl ao al (some (r, m)) = none := by simp only [ctlK7]; rw [ite_eq_left h]
theorem ctlK7_yes (h : r.headD 0 ≠ 0) : ctlK7 cR n vis0 vis isP lg rs nP nF xo xl ao al (some (r, m)) =
    ctlK8 cR n vis isP lg rs nP nF xo xl ao al (iarW (n + 1) m vis0 (ao + nP) (al - nP)) := by
  simp only [ctlK7]; rw [ite_eq_right h]
theorem ctlK6_no (h : xfn ≠ hd ∨ al ≠ nP + nIdx ∨ e = 0) :
    ctlK6 cR n vis0 vis nP nIdx rs isP lg nF xo xl hd xfn ao al m (some e) = none := by
  simp only [ctlK6]; rw [ite_eq_left h]
theorem ctlK6_yes (h : ¬ (xfn ≠ hd ∨ al ≠ nP + nIdx ∨ e = 0)) :
    ctlK6 cR n vis0 vis nP nIdx rs isP lg nF xo xl hd xfn ao al m (some e) =
      ctlK7 cR n vis0 vis isP lg rs nP nF xo xl ao al (fdrW (n + 1) m vis0 xo xl) := by
  simp only [ctlK6]; rw [ite_eq_right h]
theorem ctlK5_some : ctlK5 cR n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl hd xfn (some (r, m)) =
    ctlK6 cR n vis0 vis nP nIdx rs isP lg nF xo xl hd xfn (r.headD 0) (r.tail.headD 0) m
      (if nP ≤ r.tail.headD 0 then eqW (n + 1) m (r.headD 0) nP cqO cqL else some 0) := rfl
theorem ctlK4_some : ctlK4 cR n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb hd (some (r, m)) =
    ctlK5 cR n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl hd (r.headD 0)
      (gaaF m [CWF, xb]) := rfl
theorem ctlK3_big (h : 4294967296 ≤ hd) :
    ctlK3 cR n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb (some (hd, m)) = none := by simp only [ctlK3]; rw [ite_eq_left h]
theorem ctlK3_ok (h : ¬ 4294967296 ≤ hd) :
    ctlK3 cR n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb (some (hd, m)) =
      ctlK4 cR n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb hd (gafF m [CWF, xb]) := by
  simp only [ctlK3]; rw [ite_eq_right h]
theorem ctlK2_some : ctlK2 cR n vis0 vis T nP nIdx rs isP lg nF cqO cqL xo xl xb (some (r, m)) =
    ctlK3 cR n vis0 vis nP nIdx rs isP lg nF cqO cqL xo xl xb (ceinternW m T (r.headD 0)) := rfl
theorem ctlK1_no (h : r.headD 0 = 0) :
    ctlK1 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL (some (r, m)) = none := by simp only [ctlK1]; rw [ite_eq_left h]
theorem ctlK1_yes (h : r.headD 0 ≠ 0) :
    ctlK1 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL (some (r, m)) =
      ctlK2 cR n vis0 vis T nP nIdx rs isP lg nF cqO cqL (r.tail.headD 0) (r.tail.tail.headD 0)
        (r.tail.tail.tail.headD 0) (plW (n + 1) m lo ll) := by simp only [ctlK1]; rw [ite_eq_right h]
end arms
attribute [ind_grind] ctlK9_some ctlK8_no ctlK8_yes ctlK7_no ctlK7_yes ctlK6_no ctlK6_yes ctlK5_some
  ctlK4_some ctlK3_big ctlK3_ok ctlK2_some ctlK1_no ctlK1_yes

set_option maxHeartbeats 2000000 in
theorem ctlW_spec (p : Prog) (hP : SumProg p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) (s₀ : St)
    (vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL cqB : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 2)) "check_sum_ctor_tail"
      [vis0, vis, T, lo, ll, nP, nIdx, rs, isP, lg, nF, cqO, cqL, cqB]
    ⦃fun r s' => LocEq s' s₀ ∧
      ctlW cR n s₀.mem vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL cqB = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.htail]
  simp only [callFn, checkSumCtorTailL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
    hcR (n + 1) "open_pis_at_fvars_f",
    plW_spec p hP.ha hP.hc hP.hsc hP.hg hP.hpf hP.hpp hP.hip hP.hplg hP.hpl hP.hil (n + 1),
    internConst_spec p hP.hcf hP.hcp hP.hic (n + 1),
    gafF_spec p hP.ad (n + 1), gaaF_spec p hP.ad (n + 1),
    slEq_spec p hP.heq (n + 1), fdrW_spec p hP.hfdr hP.ad.ftd hP.hcr (n + 1), iarW_spec p hP.hiar hP.hcr (n + 1),
    fsortsW_spec p hP.hg hP.hpw hP.het hP.hcn hP.hfsb hP.hcfg hP.ha hP.hcfs hP.ad.ftd cR hcR n]
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Locals.init, List.getD_cons_zero, List.getD_cons_succ, Cmp.eval,
    BinOp.eval, Nat.reduceEqDiff, reduceIte, beq_iff_eq,
    decide_eq_true_eq] at *)
  all_goals grind (gen := 30) (instances := 5000) [lang_grind, arena_grind, ind_grind, ctlW]

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
    (hd : decHL m o.toNat l.toNat = some xs) (hb : o.toNat + l.toNat ≤ iwTop m) (hA : AbsOK m) :
    Sim (fdrW n m v o l) (fieldDomsResolve fe xs) a
      (fun r b m' a' => KeepPost dn v fe decW0B m m' a' r b ∧ AbsOK m') := fun r m' e => by
  obtain ⟨x, a', h1, h2⟩ := fdrW_ok dn fe n m m' a v o l xs r e hS hd (hS.lt64 hb) hb hA
  exact ⟨x, a', h1, h2⟩

/-- `idx_args_resolve` as a `Sim`. -/
theorem iarSim {dn : NIdx → Option ConLeche.Name} {v : Word} {fe : IFEnv} (n : Nat) (m : Mem)
    (a : AState) (o l : Word) (xs : List EIdx) (hS : StageR dn v fe m a)
    (hd : decHL m o.toNat l.toNat = some xs) (hb : o.toNat + l.toNat ≤ iwTop m) (hA : AbsOK m) :
    Sim (iarW n m v o l) (idxArgsResolve fe xs) a
      (fun r b m' a' => KeepPost dn v fe decW0B m m' a' r b ∧ AbsOK m') := fun r m' e => by
  obtain ⟨x, a', h1, h2⟩ := iarW_ok dn fe n m m' a v o l xs r e hS hd (hS.lt64 hb) hb hA
  exact ⟨x, a', h1, h2⟩

/-- A callee run at the pre-block view `vis0` (the restriction), back at `vis`. -/
theorem sumKeep_restrict {dn : NIdx → Option ConLeche.Name} {vis vis0 : Word} {fe : IFEnv}
    {m m' : Mem} {a' : AState} {r : List Word} {b : Bool} (hv : fe.visibleBelow = vis.toNat)
    (h : KeepPost dn vis0 (fe.restrictTo vis0.toNat) decW0B m m' a' r b) :
    StageR dn vis fe m' a' ∧ IWGrow m m' ∧ (r.headD 0 != 0) = b :=
  ⟨h.1.unrestrict hv, h.2.1, h.2.2.1⟩

/-! ## `check_sum_ctor`: the word model -/

/-- After the tail. -/
def ctorK9 (cvC : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([cvC, r.headD 0, r.tail.headD 0], m)
/-- After `check_struct_doms_at`: the tail. -/
def ctorK8 (cR : CallM) (n : Nat) (vis0 vis T lo ll nP nIdx rs isP lg nF cvC cqO cqL cqB : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => ctorK9 cvC (ctlW cR n m vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL cqB)
/-- After `fvar_type_ds`: the binder domains. -/
def ctorK7 (cR : CallM) (n : Nat) (vis0 vis T lo ll nP nIdx rs isP lg nF cvC cqO cqL cqB : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rt, m) => ctorK8 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cqO cqL cqB
      (sdomsW cR (n + 2) m vis 0 cqO cqL (rt.headD 0) (rt.tail.headD 0) nP)
/-- After the type former's opened telescope. -/
def ctorK6 (cR : CallM) (n : Nat) (vis0 vis T lo ll nP nIdx rs isP lg nF cvC cqO cqL cqB : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rq, m) => if rq.headD 0 = 0 then none
    else ctorK7 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cqO cqL cqB
      (ftdsF m [rq.tail.headD 0, rq.tail.tail.headD 0])
/-- After the constructor's opened telescope. -/
def ctorK5 (cR : CallM) (n : Nat) (vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rc, m) => if rc.headD 0 = 0 then none
    else ctorK6 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC (rc.tail.headD 0) (rc.tail.tail.headD 0)
      (rc.tail.tail.tail.headD 0) (cR (n + 2) "open_pis_at_fvars_f" [nP, rdW (m.arr64 EREC) (cvTa + 3), 0] m)
/-- After `struct_ctor_resid_ok`. -/
def ctorK4 (cR : CallM) (n : Nat) (vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rr, m) => if rr.headD 0 = 0 then none
    else ctorK5 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa
      (cR (n + 2) "open_pis_at_fvars_f" [nP, rdW (m.arr64 EREC) (cvC + 3), 0] m)
/-- After `strip_pis`. -/
def ctorK3 (cR : CallM) (n : Nat) (vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rs', m) => if rs'.headD 0 = 0 then none
    else ctorK4 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa
      (srW (n + 2) m T lo ll nP nF nIdx (rs'.tail.tail.tail.headD 0))
/-- After `check_constant_val`. -/
def ctorK2 (cR : CallM) (n : Nat) (vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => ctorK3 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa
      (stripF 6 m [nP + nF, rdW (m.arr64 EREC) (cvC + 3)])

/-- **The model of `check_sum_ctor(vis0, vis, T, lo, ll, nP, nIdx, rs, isP, lg, cvC, nF, cvTa)`**
(its callees at exec fuel `n + 2`). -/
def ctorW (cR : CallM) (n : Nat) (m : Mem) (vis0 vis T lo ll nP nIdx rs isP lg cvC nF cvTa : Word) :
    Option (List Word × Mem) :=
  ctorK2 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa (cR (n + 2) "check_constant_val" [vis, cvC] m)

section arms
variable (cR : CallM) (n : Nat) (m : Mem) (vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa cqO cqL cqB : Word)
  (r : List Word)
theorem ctorK9_some : ctorK9 cvC (some (r, m)) = some ([cvC, r.headD 0, r.tail.headD 0], m) := rfl
theorem ctorK8_some : ctorK8 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cqO cqL cqB (some (r, m)) =
    ctorK9 cvC (ctlW cR n m vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL cqB) := rfl
theorem ctorK7_some : ctorK7 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cqO cqL cqB (some (r, m)) =
    ctorK8 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cqO cqL cqB
      (sdomsW cR (n + 2) m vis 0 cqO cqL (r.headD 0) (r.tail.headD 0) nP) := rfl
theorem ctorK6_no (h : r.headD 0 = 0) :
    ctorK6 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cqO cqL cqB (some (r, m)) = none := by
  simp only [ctorK6]; rw [ite_eq_left h]
theorem ctorK6_yes (h : r.headD 0 ≠ 0) :
    ctorK6 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cqO cqL cqB (some (r, m)) =
      ctorK7 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cqO cqL cqB
        (ftdsF m [r.tail.headD 0, r.tail.tail.headD 0]) := by
  simp only [ctorK6]; rw [ite_eq_right h]
theorem ctorK5_no (h : r.headD 0 = 0) :
    ctorK5 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa (some (r, m)) = none := by
  simp only [ctorK5]; rw [ite_eq_left h]
theorem ctorK5_yes (h : r.headD 0 ≠ 0) :
    ctorK5 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa (some (r, m)) =
      ctorK6 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC (r.tail.headD 0) (r.tail.tail.headD 0)
        (r.tail.tail.tail.headD 0)
        (cR (n + 2) "open_pis_at_fvars_f" [nP, rdW (m.arr64 EREC) (cvTa + 3), 0] m) := by
  simp only [ctorK5]; rw [ite_eq_right h]
theorem ctorK4_no (h : r.headD 0 = 0) :
    ctorK4 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa (some (r, m)) = none := by
  simp only [ctorK4]; rw [ite_eq_left h]
theorem ctorK4_yes (h : r.headD 0 ≠ 0) :
    ctorK4 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa (some (r, m)) =
      ctorK5 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa
        (cR (n + 2) "open_pis_at_fvars_f" [nP, rdW (m.arr64 EREC) (cvC + 3), 0] m) := by
  simp only [ctorK4]; rw [ite_eq_right h]
theorem ctorK3_no (h : r.headD 0 = 0) :
    ctorK3 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa (some (r, m)) = none := by
  simp only [ctorK3]; rw [ite_eq_left h]
theorem ctorK3_yes (h : r.headD 0 ≠ 0) :
    ctorK3 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa (some (r, m)) =
      ctorK4 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa
        (srW (n + 2) m T lo ll nP nF nIdx (r.tail.tail.tail.headD 0)) := by
  simp only [ctorK3]; rw [ite_eq_right h]
theorem ctorK2_some : ctorK2 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa (some (r, m)) =
    ctorK3 cR n vis0 vis T lo ll nP nIdx rs isP lg nF cvC cvTa
      (stripF 6 m [nP + nF, rdW (m.arr64 EREC) (cvC + 3)]) := rfl
end arms
attribute [ind_grind] ctorK9_some ctorK8_some ctorK7_some ctorK6_no ctorK6_yes ctorK5_no ctorK5_yes
  ctorK4_no ctorK4_yes ctorK3_no ctorK3_yes ctorK2_some

set_option maxHeartbeats 4000000 in
theorem ctorW_spec (p : Prog) (hP : SumProg p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) (s₀ : St)
    (vis0 vis T lo ll nP nIdx rs isP lg cvC nF cvTa : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 3)) "check_sum_ctor"
      [vis0, vis, T, lo, ll, nP, nIdx, rs, isP, lg, cvC, nF, cvTa]
    ⦃fun r s' => LocEq s' s₀ ∧
      ctorW cR n s₀.mem vis0 vis T lo ll nP nIdx rs isP lg cvC nF cvTa = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.hctor]
  simp only [callFn, checkSumCtorL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
    hcR (n + 2) "check_constant_val", stripPis_specF p hP.strip (n + 2),
    srW_spec p hP.ha hP.hc hP.hsc hP.hg hP.hpf hP.hpp hP.hip hP.hplg hP.hpl hP.hil hP.hcf hP.hcp hP.hic
      hP.hbf hP.hbp hP.hib hP.hpg hP.hps hP.heq hP.hsr hP.ad (n + 2),
    hcR (n + 2) "open_pis_at_fvars_f", ftdsF_spec p hP.ad (n + 2),
    sdomsW_spec p hP.hg hP.hsd hP.ad.ftd cR hcR (n + 2), ctlW_spec p hP cR hcR n]
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Locals.init, List.getD_cons_zero, List.getD_cons_succ, Cmp.eval,
    BinOp.eval, Nat.reduceEqDiff, reduceIte, beq_iff_eq] at *)
  all_goals grind (gen := 30) (instances := 5000) [lang_grind, arena_grind, ind_grind, ctorW, rdW_eq]

/-! ## `check_sum_ctor`: the relation to the twin -/

/-- **`checkSumCtor` is its head followed by `cscTailT`** (definitionally). -/
theorem checkSumCtor_eq (fe₀ fe : IFEnv) (T : NIdx) (lps : List NIdx) (nP nIdx : Nat) (resSort : LIdx)
    (isProp large : Bool) (cvC : IConstantVal) (nF : Nat) (cvTa : IConstantVal) :
    checkSumCtor V fe₀ fe T lps nP nIdx resSort isProp large cvC nF cvTa = (do
      checkConstantVal V fe cvC
      let (_, cbody) ← unwrapOr (← stripPis (nP + nF) cvC.type)
        (.notImplemented "direct sum: constructor telescope")
      unless ← structCtorResidOk T lps nP nF nIdx cbody do
        fail (.invalid "direct sum: invalid constructor return type")
      let cq ← unwrapOr (← openPisAtFvarsF nP cvC.type 0)
        (.notImplemented "direct sum: constructor telescope")
      let tq ← unwrapOr (← openPisAtFvarsF nP cvTa.type 0)
        (.notImplemented "direct sum: type former telescope")
      let tdoms ← fvarTypeDs tq.1
      checkStructDomsAt V fe 0 cq.1 tdoms nP
      cscTailT fe₀ fe T lps nP nIdx resSort isProp large cvC nF cq) := by
  rfl

/-- A constant's type word, read where the model reads it. -/
theorem sumTypeWord {m : Mem} {q : Word} {cv : IConstantVal} (h : decCVp m q.toNat = some cv)
    (hsz : (m.arr64 EREC).size < 2 ^ 64) :
    ∃ w, rdW (m.arr64 EREC) (q + 3) = w ∧ H w ∧ decI w = cv.type := by
  have ht := decCV_type h
  simp only [hd?, Option.bind_eq_bind, Option.bind_eq_some_iff] at ht
  obtain ⟨w, hw, hx⟩ := ht
  split at hx
  · have hx' := Option.some.inj hx
    have hlt : q.toNat + 3 < (m.arr64 EREC).size := (Array.getElem?_eq_some_iff.mp hw).1
    refine ⟨w, rdW_of_get? ?_ hw, by assumption, hx'⟩
    rw [sum_toNat_add (by simp; omega)]; rfl
  · cases hx

end L.Ind
