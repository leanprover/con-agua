module

import ConRon.Bridge.Core.Walks.Cached
import ConAgua.Arena.IndSumSpec.SumRules
public import ConAgua.Verdict.VCtx
import ConAgua.Arena.IndRealLvlC
public import ConAgua.Arena.IndSumSpec.CheckStructFieldSortsISucc
import ConAgua.L.ModelGen
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndSim
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.KnotEntry
public import ConAgua.Arena.TwinStep
public import ConRon.Bridge.Checker.Hyp
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.IndSum
import ConAgua.L.WordOff

@[expose] public section

/-!
# `checkStructFieldSortsI` under `StageC` (lane `indstaget`)

`check_struct_field_sorts_i`'s model at `realCall p`, from `StageC` and con-ron's preconditions of
`checkStructFieldSortsI_spec` (the opened fields denote; each inferred field type scoped at its
depth), its twin side transcribed from that spec's proof: `fvarTypeD` (`fvarTypeD_run`: the state
unchanged), `inferTypeCore` (`inferC_rsim`), `ensureSortCore` (`ensureSortC_rsim`), the universe
bound `sfbT` (`sfbT_cstep`: `readLevelM_pstep` twice, or the zero pin and `lvlEq?_spec`), the
write (twin side none), the recursion at the extended store.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

open ConRon.Bridge ConRon.Bridge.Inductives in
/-- **The twin's universe bound for one field is a core step** (con-ron's
`checkStructFieldSortsI_spec`, its middle: `readLevelM_pstep` twice; or nothing; or the zero pin
and `lvlEq?_spec`). -/
theorem sfbT_cstep {env : ConLeche.Env} {fe : IFEnv} {isProp large : Bool} {s : LIdx}
    {idxArgs : List EIdx} {fv : EIdx} {u : LIdx} {a a' : AState} (hok : CheckOK false env fe a)
    (h : (sfbT isProp large s idxArgs fv u).run a = .ok ((), a')) : CoreStep env fe a a' := by
  have h' : sfbT isProp large s idxArgs fv u a = .ok ((), a') := h
  unfold sfbT at h'
  cases isProp with
  | false =>
    simp only [Bool.not_false, ite_true] at h'
    obtain ⟨lu, s5, k5, z5⟩ := AM.bind_ok h'
    have c5 : CoreStep env fe a s5 := (readLevelM_pstep hok.state k5).toCore hok
    obtain ⟨ls, s6, k6, z6⟩ := AM.bind_ok z5
    have c6 : CoreStep env fe s5 s6 := (readLevelM_pstep c5.ok.state k6).toCore c5.ok
    obtain ⟨b, s7, k7, z7⟩ := AM.bind_ok z6
    cases hleq : ConLeche.Level.leq lu ls with
    | none =>
      rw [hleq] at k7; simp only [ConRon.Arena.liftFueled] at k7
      exact absurd k7 (fun h => AM.fail_ok h)
    | some bb =>
    rw [hleq] at k7; simp only [ConRon.Arena.liftFueled] at k7
    obtain ⟨rfl, rfl⟩ := AM.pure_ok k7
    cases b with
    | false =>
      simp only [Bool.false_eq_true, ite_false] at z7
      first
        | exact absurd z7 (fun h => AM.fail_ok h)
        | (obtain ⟨_, _, k, _⟩ := AM.bind_ok z7; exact absurd k (fun h => AM.fail_ok h))
    | true =>
      simp only [ite_true] at z7
      obtain ⟨-, rfl⟩ := AM.pure_ok z7
      exact c5.trans c6
  | true =>
    cases large with
    | false =>
      simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h'
      obtain ⟨-, rfl⟩ := AM.pure_ok h'
      exact CoreStep.refl hok
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true] at h'
      obtain ⟨z, s5, k5, z5⟩ := AM.bind_ok h'
      obtain ⟨hs5, -⟩ := zeroLevel_run hok.pins k5
      rw [hs5] at z5
      obtain ⟨vv, s6, k6, z6⟩ := AM.bind_ok z5
      obtain ⟨hok6, hst6, hp6, -⟩ :=
        AM.of_run (P := fun t => t = a) rfl k6 (Core.lvlEq?_spec a u z hok)
      have c6 : CoreStep env fe a s6 := ⟨hok6, by rw [hst6]; exact Ext.refl _, hp6⟩
      split at z6
      · first
          | (obtain ⟨-, rfl⟩ := AM.pure_ok z6; exact c6)
          | exact absurd z6 (fun h => AM.fail_ok h)
          | (obtain ⟨_, _, k, _⟩ := AM.bind_ok z6; exact absurd k (fun h => AM.fail_ok h))
      · first
          | (obtain ⟨-, rfl⟩ := AM.pure_ok z6; exact c6)
          | exact absurd z6 (fun h => AM.fail_ok h)
          | (obtain ⟨_, _, k, _⟩ := AM.bind_ok z6; exact absurd k (fun h => AM.fail_ok h))

/-- **The model of `check_field_sort_bound`, both outcomes**: its four callees (outside the
verdict closure) through their runs, lifted. -/
l_model cfbE_spec (p : Prog) (hf : p.lookup "check_field_sort_bound" = some checkFieldSortBoundL)
  fns [hf ↦ cfbE]
  specs [callW_spec p n "lv_leq_top", callW_spec p n "pin_word", callW_spec p n "lvl_eq_true",
    callW_spec p n "sl_contains"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `check_field_sort_bound` gives besides the twin's run (from `m`): the stage relation,
growth, `AbsOK`. -/
structure CfbPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem)
    (a' : AState) : Prop where
  stage : StageR vis fe m' a'
  grow : IWGrow m m'
  abs : AbsOK m'

/-- **`check_field_sort_bound` refines the twin's universe bound `sfbT`, both outcomes**: its
callees (`lv_leq_top`, `pin_word`, `lvl_eq_true`, `sl_contains`) are outside the verdict closure,
so its errors are its own rejects (`G` is `True`); `lvLeqTop_simC`, `lvlEqC_simC` for the stub
contracts. -/
theorem cfb_ref {p : Prog} (hcl : CoreStageClosed p) (hLC : LvlCacheProg p)
    (hLT : p.lookup "lv_leq_top" = some lvLeqTop) (hpw : p.lookup "pin_word" = some pinWordL)
    (het : p.lookup "lvl_eq_true" = some lvlEqTrue) (hc : p.lookup "sl_contains" = some slContains)
    {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {env : ConLeche.Env} (n : Nat) (m : Mem)
    (a : AState) (isProp large s io il fv u : Word) (idxArgs : List EIdx)
    (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hu : H u) (hs : H s) (hfv : H fv) (hidx : decHL m io.toNat il.toNat = some idxArgs)
    (hib : io.toNat + il.toNat ≤ iwTop m) {lu sP : ConLeche.Level}
    (hdu : denoteL a.store.ls (decI u) = some lu) (hsP : denoteL a.store.ls (decI s) = some sP) :
    RefE True (cfbE p n m isProp large s io il fv u)
      (sfbT (isProp != 0) (large != 0) (decI s) idxArgs (decI fv) (decI u)) a
      (fun v _ a' => CfbPost dn vis fe m v.2 a') := by
  have hS := hC.stage
  cases n with
  | zero => rw [cfbE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n =>
  by_cases hp : isProp = 0
  · rw [cfbE.arm1 p n m isProp large s io il fv u hp]
    simp only [sfbT, hp, bne_self_eq_false, Bool.not_false, ite_true]
    rw [sfb_leq_eq]
    refine RefE.bindSim (fun _ => rfl) (lvLeqTop_simC p hLC.lev hLT n hC hA u s hu hs lu sP hdu hsP)
      fun r x m1 a' _ _ ⟨hC1, hg1, hx, hA1, _⟩ => ?_
    dsimp only [cfbE.k_lv_leq_top]
    rcases x with _ | _ | _ <;> simp only [decLvlEq] at hx
    · exact RefE.abortAt hx fun _ => ErrClaim.bind_left (ErrClaim.fail _ _ (by decide))
    · refine RefE.pass (by rw [hx]; decide) (RefE.abortAt (by rw [hx]; decide) fun _ => ?_)
      exact ErrClaim.congr (T' := ConRon.Arena.fail (.invalid "direct sum: field universe too large"))
        rfl (ErrClaim.fail _ _ (by decide))
    · refine RefE.pass (by rw [hx]; decide) (RefE.pass (by rw [hx]; decide) ?_)
      rw [cfbE.j1.arm1]
      exact RefE.ret rfl ⟨hC1.stage, hg1, hA1⟩
  have hp' : (isProp != 0) = true := by simpa using hp
  by_cases hl : large = 0
  · rw [cfbE.arm3 p n m isProp large s io il fv u hp hl, cfbE.j1.arm1]
    simp only [sfbT, hp', hl, bne_self_eq_false, Bool.not_true, Bool.false_eq_true, ite_false]
    exact RefE.ret rfl ⟨hS, IWGrow.refl _, hA⟩
  have hl' : (large != 0) = true := by simpa using hl
  rw [cfbE.arm2 p n m isProp large s io il fv u hp hl]
  simp only [sfbT, hp', hl', Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
  -- `pin_word`
  refine RefE.bindLift (fun _ => rfl) fun rz m1 h1 => ?_
  obtain ⟨s', hs', -, hmm, hz'⟩ := triple_of_callW (pinWord_specV p hpw n ⟨m, Locals.init []⟩ 53) h1
  simp only at hmm hz'
  subst hs'
  have hpne : rdW (m.arr64 PINS) 0 ≠ 0 := by
    intro h0; simp [pinWordV, h0] at hz'
  obtain ⟨hrun0, hz⟩ := pinZero_stage hS hz'
  have hzp : rz.headD 0 = pinW m 53 := by
    simp only [pinWordV, hpne, ite_false, Option.some.injEq] at hz'
    rw [← hz']; rfl
  obtain ⟨lz, hdz⟩ : ∃ l, denoteL _ _ = some l := ⟨_, hC.stageT.twin.den.zero⟩
  rw [(hS.check.pins.full hpne).zeroLevel, ← hzp] at hdz
  refine ⟨_, _, hrun0, ?_⟩
  dsimp only [cfbE.k_pin_word]
  rw [hmm]
  -- `lvl_eq_true`
  refine RefE.bindLift (fun _ => rfl) fun rq mq h2 => ?_
  obtain ⟨s2, hs2, -, hW2⟩ := triple_of_callW (eqTrue_specC p het (realCall p) (realCall_spec p) n
    ⟨m, Locals.init []⟩ u (rz.headD 0)) h2
  simp only at hW2
  cases n with
  | zero => simp [eqTrueC] at hW2
  | succ n' =>
  rw [eqTrueC_succ] at hW2
  rcases he' : realCall p n' "lvl_eq_c" [u, rz.headD 0] m with _ | ⟨r1, m1⟩
  · rw [he'] at hW2; simp [eqTrueK] at hW2
  rw [he', eqTrueK_some] at hW2
  simp only [Option.some.injEq, Prod.mk.injEq] at hW2
  obtain ⟨hreq, hm2⟩ := hW2
  obtain ⟨x, a1, hrun1, hC1, hg1, hx, hA1, -⟩ :=
    lvlEqC_simC p hcl hLC n' hC hA u (rz.headD 0) hu hz lu lz hdu hdz r1 m1 he'
  refine ⟨_, _, hrun1, ?_⟩
  have hmq : mq = m1 := by rw [← hs2, ← hm2]
  subst hmq
  dsimp only [cfbE.k_lvl_eq_true]
  have hS1 := hC1.stage
  have hidx1 : decHL mq io.toNat il.toNat = some idxArgs := by
    rw [decHL_grow hg1 hib]; exact hidx
  -- `sl_contains` (L only)
  refine RefE.onlySim (fun _ => rfl) (fun r3 m3 h3 => triple_of_callW
    (slContains_spec p hc (n' + 1) ⟨mq, Locals.init []⟩ io il fv) h3) fun r3 m3 ⟨s3, hs3, _, hm3, hW3⟩ => ?_
  simp only at hW3 hm3
  obtain ⟨ws, hws, hwsd, hwlt⟩ := slR_of_decHL mq _ _ idxArgs hidx1 (hS1.lt64 (by have := hg1.iw; omega))
  simp only [UInt64.ofNat_toNat] at hws
  have hct := containsW_ok (n' + 1) _ _ _ _ _ _ hws hW3
  have hm3' : m3 = mq := by rw [← hs3, hm3]
  subst hm3'
  dsimp only [cfbE.k_sl_contains, cfbE.j1]
  have hq3 : rq.headD 0 = 0 ↔ x ≠ some true := by
    simp only [decLvlEq] at hx; rw [← hreq, hx]; rcases x with _ | _ | _ <;> simp
  have hr3 : r3.headD 0 = 0 ↔ ws.contains fv = false := by rw [hct]; cases ws.contains fv <;> simp
  rw [hwsd, contains_map_decI fv hfv ws hwlt]
  refine RefE.guardIf (by decide) (fun hg => ?_) (fun hb => ?_) fun _ _ => RefE.ret rfl ⟨hS1, hg1, hA1⟩
  · rw [hq3, hr3] at hg; rw [hg.2, Bool.or_false]; simpa using hg.1
  · rw [hq3, hr3]; simpa using hb

/-- **The model of `check_struct_field_sorts_i`, both outcomes**: `sl_get` and `fvar_type_d`
(outside the verdict closure) through their `Option` models, the core stubs and
`check_field_sort_bound` through their runs, the recursion (field `j - 1`, then the fields below)
through the model itself. -/
l_model fsortsE_spec (p : Prog) (hf : p.lookup "check_struct_field_sorts_i" = some checkStructFieldSortsIL)
    (hftd : FtdF p) (hb : p.lookup "check_field_sort_bound" = some checkFieldSortBoundL)
  fns [hf ↦ fsortsE]
  specs [callW_spec p n "sl_get", ftdF_spec0 p hftd n, cfbE_spec p hb n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `check_struct_field_sorts_i` gives (from `m0`, the memory its slices decode in): the stage
relation, growth, `AbsOK`. -/
structure FsortsPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m0 m' : Mem) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m0 m'
  abs : AbsOK m'

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hLC : LvlCacheProg p) (hLT : p.lookup "lv_leq_top" = some lvLeqTop)

include hq henv hLC hLT in
/-- **`check_struct_field_sorts_i_go` refines `checkStructFieldSortsI .verified` at `j`, both
outcomes** (twin side: con-ron's `checkStructFieldSortsI_spec`'s proof): the field (`sl_get`, L
only), `fvarTypeD` (`fvarTypeD_run`: the state unchanged), `inferTypeCore` (`inferC_rsim`; its
error by `CoreStubsE`), `ensureSortCore` (`ensureSortC_rsim`; likewise), the universe bound `sfbT`
(`cfb_ref`, `sfbT_cstep`), the write (L only), the recursion at the
extended store. -/
theorem fsorts_ref (hg : p.lookup "sl_get" = some slGet) (hpw : p.lookup "pin_word" = some pinWordL)
    (het : p.lookup "lvl_eq_true" = some lvlEqTrue) (hc : p.lookup "sl_contains" = some slContains) (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (isProp large s nP fo fl io il j : Word) (m0 : Mem)
      (fvs idxArgs : List EIdx) (fvsP : List ConLeche.Expr),
    StageC dn vis fe env m a → AbsOK m → IWGrow m0 m →
    decHL m0 fo.toNat fl.toNat = some fvs → fo.toNat + fl.toNat ≤ iwTop m0 →
    decHL m0 io.toNat il.toNat = some idxArgs → io.toNat + il.toNat ≤ iwTop m0 →
    H s → (∃ sP, denoteL a.store.ls (decI s) = some sP) → nP.toNat + j.toNat < 2 ^ 64 →
    Frontend.denoteEList a.store fvs = some fvsP →
    (∀ i, i < j.toNat → ∀ x, fvsP[i]? = some x →
      ConLeche.Expr.WScoped (nP.toNat + i) x.fvarTypeD) →
    RefE (VerdictCtx p) (fsortsE p n m vis isProp large s nP fo fl io il j)
      (checkStructFieldSortsI V fe (isProp != 0) (large != 0) (decI s) nP.toNat fvs idxArgs j.toNat) a
      (fun v _ a' => FsortsPost dn vis fe env m0 v.2 a') := by
  induction n with
  | zero => intros; rw [fsortsE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a isProp large s nP fo fl io il j m0 fvs idxArgs fvsP hC hA hg0
    hfvs hfb hidx hib hs hsP hnj hfP hws
  have hS := hC.stage
  by_cases hj : j = 0
  · subst hj
    rw [fsortsE.arm1 p n m vis isProp large s nP fo fl io il 0 rfl]
    exact RefE.ret rfl ⟨hC, hg0, hA⟩
  rw [fsortsE.arm2 p n m vis isProp large s nP fo fl io il j hj]
  obtain ⟨J, hjJ⟩ : ∃ J, j.toNat = J + 1 :=
    ⟨j.toNat - 1, by have : j.toNat ≠ 0 := fun e => hj (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  have hJ : (j - 1).toNat = J := by rw [L.toNat_sub_one_of_ne hj]; omega
  rw [hjJ, checkStructFieldSortsI_succ]
  -- the field (`sl_get`, L only)
  refine RefE.onlySim (fun _ => fsortsE.k_sl_get.none ..) (fun r1 m1 h1 =>
    triple_of_callW (slGet_specW p hg n ⟨m, Locals.init []⟩ fo fl (j - 1)) h1)
    fun r1 m1 ⟨s1, hs1, _, hm1, hgw⟩ => ?_
  have hl : ¬ fl ≤ j - 1 := by
    intro hl'; simp [getW, hl'] at hgw
  have hJl : J < fl.toNat := by
    have : ¬ fl.toNat ≤ (j - 1).toNat := fun e => hl (UInt64.le_iff_toNat_le.mpr e)
    omega
  have hT := hS.lt64 (x := iwTop m) (Nat.le_refl _)
  have hgT := hg0.iw
  have hfvs' : decHL m fo.toNat fl.toNat = some fvs := by rw [decHL_grow hg0 hfb]; exact hfvs
  obtain ⟨w, hw, hwl, hwd⟩ := decHL_get' hfvs' J hJl (by omega)
  have efo : fo + (j - 1) = UInt64.ofNat (fo.toNat + J) := by
    apply UInt64.toNat_inj.mp; rw [L.toNat_add_of_lt _ _ (by omega), hJ]; simp; omega
  have hr1 : r1.headD 0 = w := by
    simp only [getW, hl, ite_false, Option.some.injEq] at hgw
    rw [← hgw, efo, hw]
  have hm1' : m = m1 := by rw [← hs1, hm1]
  subst hm1'
  rw [fsortsE.k_sl_get.arm1]
  rw [hr1]
  have hget : fvs[J]? = some (decI w) := by
    rw [List.getElem?_eq_getElem (by rw [decHL_length m hfvs']; exact hJl), hwd]
  obtain ⟨aP, haP, hda⟩ := ConRon.Bridge.ExprOps.denoteEList_getElem? fvs fvsP hfP J (decI w) hget
  have hwsa := hws J (by omega) aP haP
  refine RefE.bind_right (v := decI w) (a₁ := a) (by rw [hget]; rfl) ?_
  have hdep : (nP + (j - 1)).toNat = nP.toNat + J := by rw [L.toNat_add_of_lt _ _ (by omega), hJ]
  rw [← hdep]
  -- `fvar_type_d` (outside the verdict closure)
  refine RefE.bindSim (fun _ => fsortsE.k_fvar_type_d.none ..) (sumSim_of_relW (ftdF_ok dn vis fe w hwl) hS)
    fun rt t m1 a1 h2 hrun1 ⟨hS1, hg1, ht1, ht⟩ => ?_
  rw [fsortsE.k_fvar_type_d.arm1]
  have hA1 : AbsOK m1 := ftdF_afr h2 hA
  obtain ⟨ha1, htd⟩ := ConRon.Bridge.Inductives.fvarTypeD_run hC.check.state hda hrun1
  subst a1 ht
  have hC1 : StageC dn vis fe env m1 a := hC.of_pstep hS1 hA1 (PStep.refl hC.check.state)
  -- `infer_type_core`
  refine RefE.bindCall (fun _ => fsortsE.k_infer_type_core.none ..)
    (fun hV e h3 => hV.core.inferTypeCore n (by omega) hC1.stageT _ _ ht1 e h3)
    (inferC_rsim hq henv n (by omega) hC1 hA1 _ _ ht1 htd (by rw [hdep]; exact hwsa))
    fun ry m2 ty a2 _ hrun2 ⟨hC2, hg2, ⟨hy1, hy⟩, hA2, c2, tyP, htyP, hwty⟩ => ?_
  dsimp only at hC2 hg2 hy1 hy hA2
  rw [fsortsE.k_infer_type_core.arm1]
  subst hy
  -- `ensure_sort_core`
  refine RefE.bindCall (fun _ => fsortsE.k_ensure_sort_core.none ..)
    (fun hV e h4 => hV.core.ensureSortCore n (by omega) hC2.stageT _ _ hy1 e h4)
    (ensureSortC_rsim hq henv n (by omega) hC2 hA2 _ _ hy1 htyP hwty)
    fun ru m3 u a3 _ hrun3 ⟨hC3, hg3, ⟨hu1, hu⟩, hA3, c3, lu, hdu⟩ => ?_
  dsimp only at hC3 hg3 hu1 hu hA3
  rw [fsortsE.k_ensure_sort_core.arm1]
  subst hu
  have hg03 := ((hg0.trans hg1).trans hg2).trans hg3
  have hidx3 : decHL m3 io.toNat il.toNat = some idxArgs := by rw [decHL_grow hg03 hib]; exact hidx
  obtain ⟨sP, hsP0⟩ := hsP
  -- `check_field_sort_bound`
  refine RefE.bindE (fun _ => fsortsE.k_check_field_sort_bound.none ..) (fun _ => trivial) (cfb_ref hq.closed hLC hLT hpw het hc n m3 a3 isProp
    large s io il w (ru.headD 0) idxArgs hC3 hA3 hu1 hs hwl hidx3 (by have := hg03.iw; omega) hdu
    (ConRon.Bridge.denoteL_ext hsP0 (c2.ext.trans c3.ext))) fun ⟨r5, m4⟩ x4 a4 hrun4 ⟨hS4, hg4, hA4⟩ => ?_
  dsimp only at hS4 hg4 hA4
  rw [fsortsE.k_check_field_sort_bound.arm1]
  have c4 := sfbT_cstep hC3.check hrun4
  have hC4 : StageC dn vis fe env m4 a4 := hC3.of_check hS4 hA4 c4.ok c4.ext
  have hx14 := c2.ext.trans (c3.ext.trans c4.ext)
  -- the fields below
  have hrec := ih (by omega) m4 a4 isProp large s nP fo fl io il (j - 1) m0 fvs idxArgs fvsP hC4 hA4
    (hg03.trans hg4) hfvs hfb hidx hib hs ⟨sP, ConRon.Bridge.denoteL_ext hsP0 hx14⟩ (by omega)
    (ConRon.Bridge.denoteEList_ext hx14 _ _ hfP) (fun i hi => hws i (by omega))
  rw [hJ] at hrec
  rw [← bind_pure (checkStructFieldSortsI V fe _ _ _ _ _ _ _)]
  refine RefE.bindE (fun _ => fsortsE.k_check_struct_field_sorts_i.none ..) id hrec
    fun ⟨w6, m6⟩ _ a5 _ hR5 => ?_
  rw [fsortsE.k_check_struct_field_sorts_i.arm1]
  exact RefE.ret rfl hR5

include hq henv hLC hLT in
/-- **`check_struct_field_sorts_i` refines `checkStructFieldSortsI .verified`** under `StageC`
(`fsorts_ref`'s ok half; the fields' denotations and scoping as con-ron's
`checkStructFieldSortsI_spec` asks): the sorts in a fresh `IW` slice. -/
@[refines ConRon.Arena.checkStructFieldSortsI]
theorem checkStructFieldSortsI_refinesC (hg : p.lookup "sl_get" = some slGet)
    (hpw : p.lookup "pin_word" = some pinWordL)
    (het : p.lookup "lvl_eq_true" = some lvlEqTrue) (hc : p.lookup "sl_contains" = some slContains)
    (hb : p.lookup "check_field_sort_bound" = some checkFieldSortBoundL)
    (hp : p.lookup "check_struct_field_sorts_i" = some checkStructFieldSortsIL) (hftd : FtdF p)
    (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (isProp large s nP fo fl io il nW : Word)
    (fvs idxArgs : List EIdx) (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hfvs : decHL s₀.mem fo.toNat fl.toNat = some fvs) (hfb : fo.toNat + fl.toNat ≤ iwTop s₀.mem)
    (hidx : decHL s₀.mem io.toNat il.toNat = some idxArgs) (hib : io.toNat + il.toNat ≤ iwTop s₀.mem)
    (hs : H s) {sP : ConLeche.Level} (hsP : denoteL a₀.store.ls (decI s) = some sP)
    (hnj : nP.toNat + nW.toNat < 2 ^ 64) {fvsP : List ConLeche.Expr}
    (hfP : Frontend.denoteEList a₀.store fvs = some fvsP)
    (hws : ∀ i, i < nW.toNat → ∀ x, fvsP[i]? = some x →
      ConLeche.Expr.WScoped (nP.toNat + i) x.fvarTypeD) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_struct_field_sorts_i"
      [vis, isProp, large, s, nP, fo, fl, io, il, nW]
    ⦃fun _ s' => LocEq s' s₀ ∧
      AM.ok (checkStructFieldSortsI V fe (isProp != 0) (large != 0) (decI s) nP.toNat fvs idxArgs
        nW.toNat) a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (checkStructFieldSortsI V fe (isProp != 0) (large != 0)
        (decI s) nP.toNat fvs idxArgs nW.toNat) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (RefE.triple (fsortsE_spec p hp hftd hb n s₀ vis isProp large s nP fo fl io il nW)
      (fsorts_ref hq henv hLC hLT hg hpw het hc n hn _ a₀ isProp large s nP fo fl io il nW s₀.mem fvs
        idxArgs fvsP hC hA (IWGrow.refl _) hfvs hfb hidx hib hs ⟨sP, hsP⟩ hnj hfP hws))
      fun _ _ ⟨hl, _, _, hrun, hR⟩ => by
    obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ hrun
    exact ⟨hl, hok, by rw [hst]; exact hR.stage, hR.grow, hR.abs⟩

end sims

end L.Ind
