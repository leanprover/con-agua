module

import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.IndRealOpf3
public import ConAgua.Verdict.VCtx
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndRealAbs
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
import ConAgua.L.ModelGen
public import ConAgua.Arena.IndRealOpf
public import ConAgua.Arena.KnotEntry
public import ConAgua.Arena.TwinStep
public import ConRon.Bridge.Checker.Hyp
public import ConRon.Bridge.Inductives.Run
import all ConAgua.Arena.IndInstall
import all ConAgua.Arena.IndSum

@[expose] public section

/-!
# `check_block_doms_at`, `check_struct_doms_at`: one model and one refinement each

The two binder-domain walks (the block's member agreement, the direct structure's constructor)
compare binder `j - 1`'s domain with the expected one, then recurse to `j - 1`. Their unified models
`cbdaE`, `sdomsE` (`l_model … unified`: `fvar_type_d` and `sl_get`, outside the verdict closure,
lifted; `is_def_eq_core` through its run) and their refinements `cbda_ref`, `sds_ref` against
`checkBlockDomsAt`/`checkStructDomsAt`, both outcomes, under `StageC` and con-ron's preconditions
of `checkBlockDomsAt_specF` (the opened variables and the expected domains denote; their scoping at
the comparison's depth): `fvarTypeD` (`fvarTypeD_run`: the twin's state unchanged), `isDefEqCore`
(`isDefEqC_rsim`; its errors by the core stubs' claims, `CoreStubsE`), a `false` comparison the
twin's reject, the recursion at the extended store (`denoteEList_ext`). The two bodies differ (the
block reads the slices directly and returns a word, the structure walk reads them by `sl_get`; the
reject messages differ), so the proofs are two.
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `open_pis_at_fvars_f`, the real call (replacing the stub contract) -/

/-- A call of `open_pis_at_fvars_f` in a program with `opfP` is its model `opfF`. -/
theorem callW_opfF {p : Prog} (hOpf : OpfF p) {n : Nat} {args r : List Word} {m m' : Mem}
    (h : callW p n "open_pis_at_fvars_f" args m = some (r, m')) : opfF m args = some (r, m') := by
  obtain ⟨s', hs, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (opfF_spec p hOpf n _ args) h
  rw [← hs]; exact hW

/-- **`open_pis_at_fvars_f`, the real call, as a `Sim`** (the stub contract's `KeepPost`, the
twin's run, and `AbsOK` after: `opfF_ok`). -/
theorem opfSimRA {p : Prog} (hOpf : OpfF p) {n : Nat} {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {k e i : Word} (he : H e) {m : Mem} {a : AState} (hS : StageR vis fe m a)
    (hA : AbsOK m) :
    Sim (callW p n "open_pis_at_fvars_f" [k, e, i] m) (openPisAtFvarsF k.toNat (decI e) i.toNat) a
      (fun r x m' a' => ((StageR vis fe m' a' ∧ IWGrow m m' ∧ decOLE m' r x) ∧
        (openPisAtFvarsF k.toNat (decI e) i.toNat).run a = .ok (x, a')) ∧ AbsOK m') := by
  sorry

/-- The same, from the model's run. -/
theorem opfF_okRA {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {k e i : Word}
    (he : H e) {m m' : Mem} {a : AState} {r : List Word} (h : opfF m [k, e, i] = some (r, m'))
    (hS : StageR vis fe m a) (hA : AbsOK m) :
    ∃ x a', (openPisAtFvarsF k.toNat (decI e) i.toNat).run a = .ok (x, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ decOLE m' r x ∧ AbsOK m' := by
  sorry

set_option experimental.vcgen true in
/-- **`check_block_doms_at`'s model, both outcomes**: `fvar_type_d` (outside the verdict closure)
lifted, `is_def_eq_core` through its run. -/
l_model cbdaE_spec (p : Prog) (hf : p.lookup "check_block_doms_at" = some checkBlockDomsAt)
  fns [hf ↦ cbdaE] specs [callW_spec p n "fvar_type_d"] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

set_option experimental.vcgen true in
/-- **`check_struct_doms_at`'s model, both outcomes**: `sl_get` and `fvar_type_d` (outside the
verdict closure) lifted, `is_def_eq_core` through its run. -/
l_model sdomsE_spec (p : Prog) (hf : p.lookup "check_struct_doms_at" = some checkStructDomsAtL)
  fns [hf ↦ sdomsE] specs [callW_spec p n "sl_get", callW_spec p n "fvar_type_d"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-! ## The install family's invariant package and its steps -/

/-- **The walk's package from `(m₀, a₀)` to `(m, a)`** (the install and sum families,
docs/design/refgen.md §6): the stage, `AbsOK`, the `IW` growth and the twin's core step. -/
structure InsAt (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m₀ : Mem) (a₀ : AState) (m : Mem) (a : AState) : Prop where
  stage : StageC dn vis fe env m a
  abs : AbsOK m
  grow : IWGrow m₀ m

namespace InsAt
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {m₀ m₁ m : Mem} {a₀ a₁ a : AState}

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem refl (h : StageC dn vis fe env m a) (hA : AbsOK m) : InsAt dn vis fe env m a m a :=
  ⟨h, hA, IWGrow.refl _, ConRon.Bridge.CoreStep.refl h.check⟩
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem trans (h₁ : InsAt dn vis fe env m₀ a₀ m₁ a₁) (h₂ : InsAt dn vis fe env m₁ a₁ m a) :
    InsAt dn vis fe env m₀ a₀ m a :=
  ⟨h₂.stage, h₂.abs, h₁.grow.trans h₂.grow, h₁.core.trans h₂.core⟩
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- A step that con-ron calls a `PStep`. -/
theorem pstep (h : StageC dn vis fe env m₀ a₀) (hS : StageR vis fe m a) (hA : AbsOK m)
    (hg : IWGrow m₀ m) (hp : PStep a₀ a) : InsAt dn vis fe env m₀ a₀ m a :=
  ⟨h.of_pstep hS hA hp, hA, hg, hp.toCore h.check⟩
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- A core step. -/
theorem cstep (h : StageC dn vis fe env m₀ a₀) (hS : StageR vis fe m a) (hA : AbsOK m)
    (hg : IWGrow m₀ m) (hc : ConRon.Bridge.CoreStep V env fe a₀ a) : InsAt dn vis fe env m₀ a₀ m a :=
  ⟨h.of_check hS hA hc.ok hc.ext, hA, hg, hc⟩
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem decHL {k : IdxKind} (h : InsAt dn vis fe env m₀ a₀ m a) {o l : Nat} {xs : List (Idx k)}
    (hd : _root_.L.Ind.decHL m₀ o l = some xs) (hb : o + l ≤ iwTop m₀) :
    _root_.L.Ind.decHL m o l = some xs := by
  rw [decHL_grow h.grow hb]; exact hd
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem top (h : InsAt dn vis fe env m₀ a₀ m a) {x : Nat} (hb : x ≤ iwTop m₀) : x ≤ iwTop m :=
  Nat.le_trans hb h.grow.iw
-/

end InsAt

/-- What the binder-domain walks leave: the stage relation, the growth, no stale records. -/
structure DomsPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m m' : Mem) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  abs : AbsOK m'

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env) {m₀ m : Mem} {a₀ a : AState}

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`fvar_type_d`'s step** (the twin state unchanged): the opened variable's annotation. -/
theorem ftd_step (hftd : FtdF p) {n : Nat} (hk : InsAt dn vis fe env m₀ a₀ m a) {w : Word} (hw : H w)
    {xP : ConLeche.Expr} (hxP : denoteE a.store (decI w) = some xP) :
    Sim (callW p n "fvar_type_d" [w] m) (fvarTypeD (decI w)) a
      fun r x m' a' => InsAt dn vis fe env m a m' a' ∧ H (r.headD 0) ∧ decI (r.headD 0) = x ∧
        denoteE a'.store x = some xP.fvarTypeD :=
  fun r m' hc => by
    obtain ⟨s', hs, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (ftdF_spec0 p hftd n _ [w]) hc
    subst hs
    obtain ⟨x, a', hr, hS, hg, hlt, heq⟩ := ftdF_ok dn vis fe w hw m s'.mem a r hW hk.stage.stage
    obtain ⟨rfl, hx⟩ := ConRon.Bridge.Inductives.fvarTypeD_run hk.stage.check.state hxP hr
    exact ⟨x, a', hr, InsAt.pstep hk.stage hS (ftdF_afr hW hk.abs) hg (PStep.refl hk.stage.check.state),
      hlt, heq, hx⟩
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
include hq henv in
/-- **`is_def_eq_core`'s step** (a unified callee: its errors by the core stubs' claims). -/
theorem idc_ref {n : Nat} (hn : n ≤ 2 ^ 62) (hk : InsAt dn vis fe env m₀ a₀ m a) {dep x y : Word}
    {d : Nat} (hd : dep.toNat = d) {xi : EIdx} (hxi : decI x = xi) (hx : H x) (hy : H y)
    {xP yP : ConLeche.Expr} (hdx : denoteE a.store xi = some xP)
    (hdy : denoteE a.store (decI y) = some yP) (hwx : ConLeche.Expr.WScoped d xP)
    (hwy : ConLeche.Expr.WScoped d yP) :
    RefE (CoreStubsE p) (callE p n "is_def_eq_core" [vis, dep, x, y] m)
      (isDefEqCore V fe checkFuel d xi (decI y)) a
      (fun v c a' => InsAt dn vis fe env m a v.2 a' ∧ (v.1.headD 0 = 0 ↔ c = false)) := by
  subst hd hxi
  rcases h : callE p n "is_def_eq_core" [vis, dep, x, y] m with e | ⟨r, m'⟩
  · exact fun hcE => hcE.isDefEqCore n hn hk.stage.stageT dep x y hx hy e h
  obtain ⟨c, a', hr, hC, hg, hd, hA, hcs⟩ :=
    isDefEqC_rsim hq henv n hn hk.stage hk.abs dep x y hx hy hdx hdy hwx hwy (r, m') (callW_of_callE h)
  exact ⟨c, a', hr, ⟨hC, hA, hg, hcs⟩, by rw [← hd]; simp [decBool]⟩
-/

/-- **`sl_get`** (an L helper, no twin step) on a decoded slice: the memory unchanged, the index in
range, the word read the element. -/
theorem slGet_step (hg : p.lookup "sl_get" = some slGet) {n : Nat} {o l i : Word} {xs : List EIdx}
    (hd : decHL m o.toNat l.toNat = some xs) (hb : o.toNat + l.toNat < 2 ^ 64) :
    ∀ r m', callW p n "sl_get" [o, l, i] m = some (r, m') →
      m = m' ∧ i.toNat < l.toNat ∧ H (r.headD 0) ∧ xs[i.toNat]? = some (decI (r.headD 0)) :=
  fun r m' hc => by
    obtain ⟨s, hs, -, hm, hgw⟩ := triple_of_callW (slGet_specW p hg n ⟨m, Locals.init []⟩ o l i) hc
    have hl : ¬ l ≤ i := fun hl' => by simp [getW, hl'] at hgw
    have hi : i.toNat < l.toNat := Nat.lt_of_not_le fun e => hl (UInt64.le_iff_toNat_le.mpr e)
    simp only [getW, hl, ite_false, Option.some.injEq] at hgw
    obtain ⟨w, hw, hwlt, hwd⟩ := decHL_get' hd i.toNat hi hb
    have hoi : o + i = UInt64.ofNat (o.toNat + i.toNat) := by
      apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
    rw [hoi, hw] at hgw
    refine ⟨by rw [← hs, hm], hi, hgw ▸ hwlt, ?_⟩
    rw [← hgw, List.getElem?_eq_getElem (by rw [decHL_length m hd]; exact hi)]
    exact congrArg some hwd

include hq henv in
/-- **`check_block_doms_at` refines `checkBlockDomsAt`**, both outcomes (con-ron's
`checkBlockDomsAt_specF`'s preconditions; the scoping below the count `j`). -/
theorem cbda_ref (hftd : FtdF p) (n : Nat) (hn : n ≤ 2 ^ 62) : ∀ (m : Mem) (a : AState)
    (off fo fl dO dl j : Word) (fvs doms : List EIdx) (fvsP domsP : List ConLeche.Expr),
    StageC dn vis fe env m a → AbsOK m →
    decHL m fo.toNat fl.toNat = some fvs → decHL m dO.toNat dl.toNat = some doms →
    fo.toNat + fl.toNat < 2 ^ 64 → dO.toNat + dl.toNat < 2 ^ 64 → fo.toNat + fl.toNat ≤ iwTop m →
    dO.toNat + dl.toNat ≤ iwTop m → off.toNat + fl.toNat < 2 ^ 64 →
    Frontend.denoteEList a.store fvs = some fvsP → Frontend.denoteEList a.store doms = some domsP →
    (∀ i, i < j.toNat → ∀ x y, fvsP[i]? = some x → domsP[i]? = some y →
      ConLeche.Expr.WScoped (off.toNat + i) x.fvarTypeD ∧ ConLeche.Expr.WScoped (off.toNat + i) y) →
    RefE (CoreStubsE p) (cbdaE p n m vis off fo fl dO dl j)
      (ConRon.Arena.checkBlockDomsAt V fe off.toNat fvs doms j.toNat) a
      (fun v _ a' => DomsPost dn vis fe env m v.2 a') := by
  sorry

include hq henv in
/-- **`check_struct_doms_at` refines `checkStructDomsAt`**, both outcomes (as `cbda_ref`; the
indices read by `sl_get`, a binder mismatch the twin's decline). -/
theorem sds_ref (hg : p.lookup "sl_get" = some slGet) (hftd : FtdF p) (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (off fo fl dO dl j : Word) (fvs doms : List EIdx)
    (fvsP domsP : List ConLeche.Expr),
    StageC dn vis fe env m a → AbsOK m →
    decHL m fo.toNat fl.toNat = some fvs → decHL m dO.toNat dl.toNat = some doms →
    fo.toNat + fl.toNat < 2 ^ 64 → dO.toNat + dl.toNat < 2 ^ 64 → fo.toNat + fl.toNat ≤ iwTop m →
    dO.toNat + dl.toNat ≤ iwTop m → off.toNat + fl.toNat < 2 ^ 64 →
    Frontend.denoteEList a.store fvs = some fvsP → Frontend.denoteEList a.store doms = some domsP →
    (∀ i, i < j.toNat → ∀ x y, fvsP[i]? = some x → domsP[i]? = some y →
      ConLeche.Expr.WScoped (off.toNat + i) x.fvarTypeD ∧ ConLeche.Expr.WScoped (off.toNat + i) y) →
    RefE (CoreStubsE p) (sdomsE p n m vis off fo fl dO dl j)
      (ConRon.Arena.checkStructDomsAt V fe off.toNat fvs doms j.toNat) a
      (fun v _ a' => DomsPost dn vis fe env m v.2 a') := by
  sorry

include hq henv in
/-- **`check_block_doms_at` refines `checkBlockDomsAt .verified`** under `StageC` (`cbda_ref`'s ok
half). -/
@[refines ConRon.Arena.checkBlockDomsAt]
theorem checkBlockDomsAt_refinesC (hp : p.lookup "check_block_doms_at" = some checkBlockDomsAt)
    (hftd : FtdF p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (off fo fl dO dl j : Word)
    (fvs doms : List EIdx) (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hfvs : decHL s₀.mem fo.toNat fl.toNat = some fvs)
    (hdoms : decHL s₀.mem dO.toNat dl.toNat = some doms)
    (hfob : fo.toNat + fl.toNat < 2 ^ 64) (hdob : dO.toNat + dl.toNat < 2 ^ 64)
    (hfot : fo.toNat + fl.toNat ≤ iwTop s₀.mem) (hdot : dO.toNat + dl.toNat ≤ iwTop s₀.mem)
    (hoob : off.toNat + fl.toNat < 2 ^ 64)
    {fvsP domsP : List ConLeche.Expr} (hfP : Frontend.denoteEList a₀.store fvs = some fvsP)
    (hdP : Frontend.denoteEList a₀.store doms = some domsP)
    (hc : ∀ (i : Nat) (x : ConLeche.Expr), fvsP[i]? = some x →
      ConLeche.Expr.WScoped (off.toNat + i) x.fvarTypeD)
    (ht : ∀ (i : Nat) (x : ConLeche.Expr), domsP[i]? = some x →
      ConLeche.Expr.WScoped (off.toNat + i) x) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_block_doms_at" [vis, off, fo, fl, dO, dl, j]
    ⦃fun _r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.checkBlockDomsAt V fe off.toNat fvs doms j.toNat) a₀ ∧
      StageC dn vis fe env s'.mem
        (AM.st (ConRon.Arena.checkBlockDomsAt V fe off.toNat fvs doms j.toNat) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (RefE.triple (cbdaE_spec p hp n s₀ vis off fo fl dO dl j)
    (cbda_ref hq henv hftd n hn _ a₀ off fo fl dO dl j fvs doms fvsP domsP hC hA hfvs hdoms hfob hdob hfot
      hdot hoob hfP hdP fun i _ x y hx hy => ⟨hc i x hx, ht i y hy⟩))
    fun _ _ ⟨hl, _, _, hrun, hR⟩ =>
      let ⟨hok, hst, _⟩ := AM.of_run_ok _ _ _ _ hrun
      ⟨hl, hok, hst ▸ hR.stage, hR.grow, hR.abs⟩

include hq henv in
/-- **`check_struct_doms_at` refines `checkStructDomsAt .verified`** under `StageC` (`sds_ref`'s ok
half). -/
@[refines ConRon.Arena.checkStructDomsAt]
theorem checkStructDomsAt_refinesC (hg : p.lookup "sl_get" = some slGet)
    (hp : p.lookup "check_struct_doms_at" = some checkStructDomsAtL) (hftd : FtdF p) (n : Nat)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (off fo fl dO dl j : Word) (fvs doms : List EIdx)
    (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hfvs : decHL s₀.mem fo.toNat fl.toNat = some fvs)
    (hdoms : decHL s₀.mem dO.toNat dl.toNat = some doms)
    (hfob : fo.toNat + fl.toNat < 2 ^ 64) (hdob : dO.toNat + dl.toNat < 2 ^ 64)
    (hfot : fo.toNat + fl.toNat ≤ iwTop s₀.mem) (hdot : dO.toNat + dl.toNat ≤ iwTop s₀.mem)
    (hoob : off.toNat + fl.toNat < 2 ^ 64)
    {fvsP domsP : List ConLeche.Expr} (hfP : Frontend.denoteEList a₀.store fvs = some fvsP)
    (hdP : Frontend.denoteEList a₀.store doms = some domsP)
    (hws : ∀ i, i < j.toNat → ∀ x y, fvsP[i]? = some x → domsP[i]? = some y →
      ConLeche.Expr.WScoped (off.toNat + i) x.fvarTypeD ∧ ConLeche.Expr.WScoped (off.toNat + i) y) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_struct_doms_at" [vis, off, fo, fl, dO, dl, j]
    ⦃fun _r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.checkStructDomsAt V fe off.toNat fvs doms j.toNat) a₀ ∧
      StageC dn vis fe env s'.mem
        (AM.st (ConRon.Arena.checkStructDomsAt V fe off.toNat fvs doms j.toNat) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (RefE.triple (sdomsE_spec p hp n s₀ vis off fo fl dO dl j)
    (sds_ref hq henv hg hftd n hn _ a₀ off fo fl dO dl j fvs doms fvsP domsP hC hA hfvs hdoms hfob hdob
      hfot hdot hoob hfP hdP hws))
    fun _ _ ⟨hl, _, _, hrun, hR⟩ =>
      let ⟨hok, hst, _⟩ := AM.of_run_ok _ _ _ _ hrun
      ⟨hl, hok, hst ▸ hR.stage, hR.grow, hR.abs⟩

end sims

end L.Ind
