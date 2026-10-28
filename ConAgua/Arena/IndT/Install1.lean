import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.IndRealOpf3
import ConAgua.Verdict.VCtx

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
    {fe : IFEnv} {k e i : Word} (he : H e) {m : Mem} {a : AState} (hS : StageR dn vis fe m a)
    (hA : AbsOK m) :
    Sim (callW p n "open_pis_at_fvars_f" [k, e, i] m) (openPisAtFvarsF k.toNat (decI e) i.toNat) a
      (fun r x m' a' => ((StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decOLE m' r x) ∧
        (openPisAtFvarsF k.toNat (decI e) i.toNat).run a = .ok (x, a')) ∧ AbsOK m') := by
  intro r m' h
  obtain ⟨x, a', hrun, ⟨hS', hg, hd⟩, hA'⟩ :=
    opfF_ok dn vis fe k e i he m m' a r (callW_opfF hOpf h) ⟨hS, hA⟩
  exact ⟨x, a', hrun, ⟨⟨hS', hg, hd⟩, hrun⟩, hA'⟩

/-- The same, from the model's run. -/
theorem opfF_okRA {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {k e i : Word}
    (he : H e) {m m' : Mem} {a : AState} {r : List Word} (h : opfF m [k, e, i] = some (r, m'))
    (hS : StageR dn vis fe m a) (hA : AbsOK m) :
    ∃ x a', (openPisAtFvarsF k.toNat (decI e) i.toNat).run a = .ok (x, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decOLE m' r x ∧ AbsOK m' := by
  obtain ⟨x, a', hrun, ⟨hS', hg, hd⟩, hA'⟩ := opfF_ok dn vis fe k e i he m m' a r h ⟨hS, hA⟩
  exact ⟨x, a', hrun, hS', hg, hd, hA'⟩

/-- A `RSim` of a word model is a `Sim` of it. -/
theorem RSim.toSim {α : Type} {mo : Option (List Word × Mem)} {op : AM α} {a : AState}
    {Q : List Word × Mem → AState → α → Prop} (h : RSim mo op a Q) :
    Sim mo op a (fun r x m' a' => Q (r, m') a' x) := fun r m' e => h (r, m') e

/-- A `Sim` also records the twin's run. -/
theorem _root_.L.Arena.Sim.withRunC {β α : Type} {mo : Option (β × Mem)} {op : AM α} {a : AState}
    {Q : β → α → Mem → AState → Prop} (h : Sim mo op a Q) :
    Sim mo op a (fun r x m' a' => Q r x m' a' ∧ op.run a = .ok (x, a')) := by
  intro r m' e; obtain ⟨x, a', h1, h2⟩ := h r m' e; exact ⟨x, a', h1, h2, h1⟩

set_option experimental.vcgen true in
/-- **`check_block_doms_at`'s model, both outcomes**: `fvar_type_d` (outside the verdict closure)
lifted, `is_def_eq_core` through its run. -/
l_model cbdaE_spec (p : Prog) (hf : p.lookup "check_block_doms_at" = some checkBlockDomsAt)
  fns [hf ↦ cbdaE] specs [callW_spec p n "fvar_type_d"] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

set_option experimental.vcgen true in
/-- **`check_struct_doms_at`'s model, both outcomes**: `sl_get` and `fvar_type_d` (outside the
verdict closure) lifted, `is_def_eq_core` through its run. -/
l_model sdomsE_spec (p : Prog) (hf : p.lookup "check_struct_doms_at" = some checkStructDomsAtL)
  fns [hf ↦ sdomsE] specs [callW_spec p n "sl_get", callW_spec p n "fvar_type_d"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What the binder-domain walks leave: the stage relation, the growth, no stale records. -/
structure DomsPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m m' : Mem) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  abs : AbsOK m'

/-- A lifted `fvar_type_d` call is its model `ftdF`. -/
theorem callW_ftdF {p : Prog} (hftd : FtdF p) {n : Nat} {args r : List Word} {m m' : Mem}
    (h : callW p n "fvar_type_d" args m = some (r, m')) : ftdF m args = some (r, m') := by
  obtain ⟨s', hs, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (ftdF_spec0 p hftd n _ args) h
  rw [← hs]; exact hW

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

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
  induction n with
  | zero => intros; rw [cbdaE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
    intro m a off fo fl dO dl j fvs doms fvsP domsP hC hA hfvs hdoms hfob hdob hfot hdot hoob hfP hdP hws
    have hStage := hC.stage
    have hfvl := decHL_length m hfvs
    have hdol := decHL_length m hdoms
    by_cases hj : j = 0
    · subst hj
      rw [cbdaE.arm1 p n m vis off fo fl dO dl 0 rfl]
      exact RefE.ret rfl ⟨hC, IWGrow.refl m, hA⟩
    have hjpos : 1 ≤ j.toNat := Nat.pos_of_ne_zero fun h0 => hj (UInt64.toNat_inj.mp (by simpa using h0))
    have hj1 : (j - 1).toNat = j.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hjpos))]
      simp
    by_cases hfl : fl ≤ j - 1
    · rw [cbdaE.abort1 p n m vis off fo fl dO dl j hj hfl]; exact RefE.of_cls0 rfl
    by_cases hdl : dl ≤ j - 1
    · rw [cbdaE.abort2 p n m vis off fo fl dO dl j hj hfl hdl]; exact RefE.of_cls0 rfl
    rw [cbdaE.arm2 p n m vis off fo fl dO dl j hj hfl hdl]
    have hjm1f : j.toNat - 1 < fl.toNat := by
      have : ¬ fl.toNat ≤ (j - 1).toNat := by rw [← UInt64.le_iff_toNat_le]; exact hfl
      omega
    have hjm1d : j.toNat - 1 < dl.toNat := by
      have : ¬ dl.toNat ≤ (j - 1).toNat := by rw [← UInt64.le_iff_toNat_le]; exact hdl
      omega
    have hfoeq : fo + (j - 1) = UInt64.ofNat (fo.toNat + (j.toNat - 1)) := by
      apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add, hj1]; simp
    have hdoeq : dO + (j - 1) = UInt64.ofNat (dO.toNat + (j.toNat - 1)) := by
      apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add, hj1]; simp
    obtain ⟨wa, hwa_eq, hwa_lt, hwa_dec⟩ := decHL_get' hfvs (j.toNat - 1) hjm1f hfob
    obtain ⟨wb, hwb_eq, hwb_lt, hwb_dec⟩ := decHL_get' hdoms (j.toNat - 1) hjm1d hdob
    rw [hfoeq, hdoeq, hwa_eq, hwb_eq]
    have hfvsij : fvs[j.toNat - 1]? = some (decI wa) := by
      rw [List.getElem?_eq_getElem (by omega : j.toNat - 1 < fvs.length)]
      exact congrArg some hwa_dec
    have hdomsij : doms[j.toNat - 1]? = some (decI wb) := by
      rw [List.getElem?_eq_getElem (by omega : j.toNat - 1 < doms.length)]
      exact congrArg some hwb_dec
    obtain ⟨aP, haP, hda⟩ := ConRon.Bridge.ExprOps.denoteEList_getElem? fvs fvsP hfP _ _ hfvsij
    obtain ⟨bP, hbP, hdb⟩ := ConRon.Bridge.ExprOps.denoteEList_getElem? doms domsP hdP _ _ hdomsij
    obtain ⟨hwx, hwy⟩ := hws (j.toNat - 1) (by omega) aP bP haP hbP
    -- `fvar_type_d`
    rcases h1 : callW p n "fvar_type_d" [wa] m with _ | ⟨ra, m1⟩
    · rw [liftE_none, cbdaE.k_fvar_type_d.none]; exact RefE.of_cls0 (by simp)
    rw [liftE_some, cbdaE.k_fvar_type_d.arm1]
    have hra := callW_ftdF hftd h1
    obtain ⟨x1, a1, hrun1, hStage1, hg1, hw1lt, hw1eq⟩ :=
      ftdF_ok dn vis fe wa hwa_lt m m1 a ra hra hStage
    -- the twin's `fvarTypeD`: its state unchanged, the answer the opened variable's annotation
    obtain ⟨ha1, hx1d⟩ := ConRon.Bridge.Inductives.fvarTypeD_run hC.check.state hda hrun1
    rw [ha1] at hrun1 hStage1
    have hA1 := ftdF_afr hra hA
    have hC1 : StageC dn vis fe env m1 a := hC.of_pstep hStage1 hA1 (PStep.refl hC.check.state)
    have hdep : (off + (j - 1)).toNat = off.toNat + (j.toNat - 1) := by
      rw [UInt64.toNat_add, hj1]; exact Nat.mod_eq_of_lt (by omega)
    have hdx : denoteE a.store (decI (ra.headD 0)) = some aP.fvarTypeD := by rw [hw1eq]; exact hx1d
    have hjeq : j.toNat = (j.toNat - 1) + 1 := by omega
    have htw : (ConRon.Arena.checkBlockDomsAt V fe off.toNat fvs doms j.toNat).run a =
        ((isDefEqCore V fe checkFuel (off.toNat + (j.toNat - 1)) (decI (ra.headD 0)) (decI wb)) >>= fun c =>
          (do
            unless c do
              ConRon.Arena.fail (.invalid "parameters of all inductive datatypes must match")
            ConRon.Arena.checkBlockDomsAt V fe off.toNat fvs doms (j.toNat - 1) : AM Unit)).run a := by
      rw [hjeq]
      simp only [ConRon.Arena.checkBlockDomsAt, Nat.add_sub_cancel, unwrapOr, hfvsij, hdomsij, pure_bind,
        StateT.run_bind]
      rw [hrun1]
      simp only [bind, Except.bind]
      rw [← hw1eq]
    refine RefE.of_run_eq htw ?_
    -- `is_def_eq_core`
    rcases h2 : callE p n "is_def_eq_core" [vis, off + (j - 1), ra.headD 0, wb] m1 with e2 | ⟨rb, m2⟩
    · rw [cbdaE.k_is_def_eq_core.none]
      refine RefE.bind_left fun hcE => ?_
      have hcl := hcE.isDefEqCore n (by omega) hC1.stageT (off + (j - 1)) (ra.headD 0) wb hw1lt hwb_lt e2 h2
      rwa [hdep] at hcl
    obtain ⟨x2, a2, hrun2, hC2, hg2, hb2eq, hA2, hcs2⟩ :=
      isDefEqC_rsim hq henv n (by omega) hC1 hA1 (off + (j - 1)) (ra.headD 0) wb hw1lt hwb_lt hdx hdb
        (by rw [hdep]; exact hwx) (by rw [hdep]; exact hwy) _ (callW_of_callE h2)
    dsimp only at hC2 hg2 hb2eq hA2
    rw [hdep] at hrun2
    refine RefE.bind_right hrun2 ?_
    by_cases heq0 : rb.headD 0 = 0
    · rw [cbdaE.k_is_def_eq_core.abort1 p n vis off fo fl dO dl (j - 1) rb m2 heq0, RefE_error]
      have hv2 : x2 = false := by rw [← hb2eq, decBool, heq0]; rfl
      subst hv2
      exact fun _ => ErrClaim.bind_left (ErrClaim.fail _ _ (by decide))
    rw [cbdaE.k_is_def_eq_core.arm1 p n vis off fo fl dO dl (j - 1) rb m2 heq0]
    have hv2 : x2 = true := by rw [← hb2eq]; simpa [decBool] using heq0
    subst hv2
    have hg12 := hg1.trans hg2
    have hrec := ih (by omega) m2 a2 off fo fl dO dl (j - 1) fvs doms fvsP domsP hC2 hA2
      (by rw [decHL_grow hg12]; exact hfvs; omega) (by rw [decHL_grow hg12]; exact hdoms; omega)
      hfob hdob (by have := hg12.1; omega) (by have := hg12.1; omega) hoob
      (ConRon.Bridge.denoteEList_ext hcs2.ext _ _ hfP) (ConRon.Bridge.denoteEList_ext hcs2.ext _ _ hdP)
      (fun i hi => hws i (by omega))
    rw [hj1] at hrec
    exact (RefE.of_run_eq (by simp) hrec).mono fun _ _ _ h => ⟨h.stage, hg12.trans h.grow, h.abs⟩

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
  induction n with
  | zero => intros; rw [sdomsE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a off fo fl dO dl j fvs doms fvsP domsP hC hA hfvs hdoms hfob hdob hfot hdot hoob hfP hdP hws
  have hStage := hC.stage
  by_cases hj : j = 0
  · subst hj
    rw [sdomsE.arm2 p n m vis off fo fl dO dl 0 rfl]
    exact RefE.ret rfl ⟨hC, IWGrow.refl m, hA⟩
  rw [sdomsE.arm1 p n m vis off fo fl dO dl j hj]
  have hfvl := decHL_length m hfvs
  have hdol := decHL_length m hdoms
  have hjpos : 1 ≤ j.toNat := Nat.pos_of_ne_zero fun h0 => hj (UInt64.toNat_inj.mp (by simpa using h0))
  have hj1 : (j - 1).toNat = j.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hjpos))]
    simp
  -- the two `sl_get`s
  rcases h1 : callW p n "sl_get" [fo, fl, j - 1] m with _ | ⟨r1, m1⟩
  · rw [liftE_none, sdomsE.k_sl_get.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, sdomsE.k_sl_get.arm1]
  obtain ⟨s1, hs1, -, hm1, hgw1⟩ := triple_of_callW (slGet_specW p hg n ⟨m, Locals.init []⟩ fo fl (j - 1)) h1
  have hl1 : ¬ fl ≤ j - 1 := by
    intro hl'; simp [getW, hl'] at hgw1
  obtain rfl : m = m1 := by rw [← hs1, hm1]
  rcases h2 : callW p n "sl_get" [dO, dl, j - 1] m with _ | ⟨r2, m2⟩
  · rw [liftE_none, sdomsE.k_sl_get_2.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, sdomsE.k_sl_get_2.arm1]
  obtain ⟨s2, hs2, -, hm2, hgw2⟩ := triple_of_callW (slGet_specW p hg n ⟨m, Locals.init []⟩ dO dl (j - 1)) h2
  have hl2 : ¬ dl ≤ j - 1 := by
    intro hl'; simp [getW, hl'] at hgw2
  obtain rfl : m = m2 := by rw [← hs2, hm2]
  have hjm1f : j.toNat - 1 < fl.toNat := by
    have : ¬ fl.toNat ≤ (j - 1).toNat := fun e => hl1 (UInt64.le_iff_toNat_le.mpr e)
    omega
  have hjm1d : j.toNat - 1 < dl.toNat := by
    have : ¬ dl.toNat ≤ (j - 1).toNat := fun e => hl2 (UInt64.le_iff_toNat_le.mpr e)
    omega
  have hfoeq : fo + (j - 1) = UInt64.ofNat (fo.toNat + (j.toNat - 1)) := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add, hj1]; simp
  have hdoeq : dO + (j - 1) = UInt64.ofNat (dO.toNat + (j.toNat - 1)) := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add, hj1]; simp
  obtain ⟨wa, hwa_eq, hwa_lt, hwa_dec⟩ := decHL_get' hfvs (j.toNat - 1) hjm1f hfob
  obtain ⟨wb, hwb_eq, hwb_lt, hwb_dec⟩ := decHL_get' hdoms (j.toNat - 1) hjm1d hdob
  have hfvsij : fvs[j.toNat - 1]? = some (decI wa) := by
    rw [List.getElem?_eq_getElem (by omega : j.toNat - 1 < fvs.length)]
    exact congrArg some hwa_dec
  have hdomsij : doms[j.toNat - 1]? = some (decI wb) := by
    rw [List.getElem?_eq_getElem (by omega : j.toNat - 1 < doms.length)]
    exact congrArg some hwb_dec
  obtain ⟨aP, haP, hda⟩ := ConRon.Bridge.ExprOps.denoteEList_getElem? fvs fvsP hfP _ _ hfvsij
  obtain ⟨bP, hbP, hdb⟩ := ConRon.Bridge.ExprOps.denoteEList_getElem? doms domsP hdP _ _ hdomsij
  obtain ⟨hwx, hwy⟩ := hws (j.toNat - 1) (by omega) aP bP haP hbP
  have hr1 : r1.headD 0 = wa := by
    simp only [getW, hl1, ite_false, Option.some.injEq] at hgw1
    rw [← hgw1, hfoeq, hwa_eq]
  have hr2 : r2.headD 0 = wb := by
    simp only [getW, hl2, ite_false, Option.some.injEq] at hgw2
    rw [← hgw2, hdoeq, hwb_eq]
  rw [hr1, hr2]
  have hjeq : j.toNat = (j.toNat - 1) + 1 := by omega
  rw [hjeq]
  simp only [ConRon.Arena.checkStructDomsAt, unwrapOr, hfvsij, hdomsij, pure_bind]
  -- `fvar_type_d`
  rcases h3 : callW p n "fvar_type_d" [wa] m with _ | ⟨ra, m3⟩
  · rw [liftE_none, sdomsE.k_fvar_type_d.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, sdomsE.k_fvar_type_d.arm1]
  have hm3 := callW_ftdF hftd h3
  obtain ⟨x1, a1, hrun1, hStage1, hg1, hw1lt, hw1eq⟩ := ftdF_ok dn vis fe wa hwa_lt m m3 a ra hm3 hStage
  obtain ⟨ha1, hx1d⟩ := ConRon.Bridge.Inductives.fvarTypeD_run hC.check.state hda hrun1
  rw [ha1] at hrun1 hStage1
  have hA1 := ftdF_afr hm3 hA
  have hC1 : StageC dn vis fe env m3 a := hC.of_pstep hStage1 hA1 (PStep.refl hC.check.state)
  refine RefE.bind_right hrun1 ?_
  have hdep : (off + (j - 1)).toNat = off.toNat + (j.toNat - 1) := by
    rw [UInt64.toNat_add, hj1]; exact Nat.mod_eq_of_lt (by omega)
  have hdx : denoteE a.store (decI (ra.headD 0)) = some aP.fvarTypeD := by rw [hw1eq]; exact hx1d
  -- `is_def_eq_core`
  rcases h4 : callE p n "is_def_eq_core" [vis, off + (j - 1), ra.headD 0, wb] m3 with e4 | ⟨rb, m4⟩
  · rw [sdomsE.k_is_def_eq_core.none]
    refine RefE.bind_left fun hcE => ?_
    have := hcE.isDefEqCore n (by omega) hC1.stageT (off + (j - 1)) (ra.headD 0) wb hw1lt hwb_lt _ h4
    rwa [hdep, hw1eq] at this
  obtain ⟨x2, a2, hrun2, hC2, hg2, hb2eq, hA2, hcs2⟩ :=
    isDefEqC_rsim hq henv n (by omega) hC1 hA1 (off + (j - 1)) (ra.headD 0) wb hw1lt hwb_lt hdx hdb
      (by rw [hdep]; exact hwx) (by rw [hdep]; exact hwy) (rb, m4) (callW_of_callE h4)
  dsimp only at hC2 hg2 hb2eq hA2
  rw [hdep, hw1eq] at hrun2
  refine RefE.bind_right hrun2 ?_
  by_cases heq0 : rb.headD 0 = 0
  · rw [sdomsE.k_is_def_eq_core.abort1 p n vis off fo fl dO dl j _ _ heq0, RefE_error]
    have hv2 : x2 = false := by
      rw [← hb2eq]; simp [decBool]; simpa using heq0
    subst hv2
    simp only [Bool.false_eq_true, ite_false]
    exact fun _ => ErrClaim.bind_left (ErrClaim.fail _ _ (by decide))
  rw [sdomsE.k_is_def_eq_core.arm1 p n vis off fo fl dO dl j _ _ heq0]
  have hv2 : x2 = true := by
    rw [← hb2eq]; simpa [decBool] using heq0
  subst hv2
  simp only [ite_true]
  have hg12 := hg1.trans hg2
  have hrec := ih (by omega) m4 a2 off fo fl dO dl (j - 1) fvs doms fvsP domsP hC2 hA2
    (by rw [decHL_grow hg12 (by omega)]; exact hfvs) (by rw [decHL_grow hg12 (by omega)]; exact hdoms)
    hfob hdob (by have := hg12.1; omega) (by have := hg12.1; omega) hoob
    (ConRon.Bridge.denoteEList_ext hcs2.ext _ _ hfP) (ConRon.Bridge.denoteEList_ext hcs2.ext _ _ hdP)
    (fun i hi => hws i (by omega))
  rw [hj1] at hrec
  rcases h5 : sdomsE p n m4 vis off fo fl dO dl (j - 1) with e5 | ⟨z5, m5⟩
  · rw [h5] at hrec
    rw [sdomsE.k_check_struct_doms_at.none]
    exact hrec
  rw [h5] at hrec
  rw [sdomsE.k_check_struct_doms_at.arm1]
  obtain ⟨u, a5, hrun5, hR5⟩ := hrec
  exact RefE.ret hrun5 ⟨hR5.stage, hg12.trans hR5.grow, hR5.abs⟩

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
