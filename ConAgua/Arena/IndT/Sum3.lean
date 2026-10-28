import ConAgua.Arena.IndSumSpec.SumRules
import ConAgua.Verdict.VCtx
import ConAgua.Verdict.IndE
import ConAgua.L.ModelGen
import ConAgua.Arena.IndSumSpec.SumProg

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
    {idxArgs : List EIdx} {fv : EIdx} {u : LIdx} {a a' : AState} (hok : CheckOK V env fe a)
    (h : (sfbT isProp large s idxArgs fv u).run a = .ok ((), a')) : CoreStep V env fe a a' := by
  have h' : sfbT isProp large s idxArgs fv u a = .ok ((), a') := h
  unfold sfbT at h'
  cases isProp with
  | false =>
    simp only [Bool.not_false, ite_true] at h'
    obtain ⟨lu, s5, k5, z5⟩ := AM.bind_ok h'
    have c5 : CoreStep V env fe a s5 := (readLevelM_pstep hok.state k5).toCore hok
    obtain ⟨ls, s6, k6, z6⟩ := AM.bind_ok z5
    have c6 : CoreStep V env fe s5 s6 := (readLevelM_pstep c5.ok.state k6).toCore c5.ok
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
      have c6 : CoreStep V env fe a s6 := ⟨hok6, by rw [hst6]; exact Ext.refl _, hp6⟩
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
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `check_field_sort_bound` gives besides the twin's run (from `m`): the stage relation,
growth, `AbsOK`. -/
structure CfbPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem)
    (a' : AState) : Prop where
  stage : StageR dn vis fe m' a'
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
    rcases h1 : callW p n "lv_leq_top" [u, s] m with _ | ⟨r, m1⟩
    · rw [liftE_none, cfbE.k_lv_leq_top.none]; exact RefE.of_cls0 (by simp)
    rw [liftE_some]
    obtain ⟨x, a', hrun, hC1, hg1, hx, hA1, -⟩ :=
      lvLeqTop_simC p hLC.lev hLT n hC hA u s hu hs lu sP hdu hsP r m1 h1
    refine RefE.bind_right hrun ?_
    simp only [decLvlEq] at hx
    by_cases h0 : r.headD 0 = 0
    · rw [cfbE.k_lv_leq_top.abort1 p r m1 h0]
      refine RefE.bind_left fun _ => ?_
      cases x with
      | none => exact ErrClaim.fail _ _ (by decide)
      | some b => cases b <;> (rw [h0] at hx; exact absurd hx (by simp))
    by_cases h2 : r.headD 0 = 2
    · rw [cfbE.k_lv_leq_top.arm1 p r m1 h0 h2, cfbE.j1.arm1]
      have : x = some true := by
        rw [h2] at hx
        rcases x with _ | _ | _
        · exact absurd hx (by decide)
        · exact absurd hx (by decide)
        · rfl
      subst this
      exact RefE.ret rfl ⟨hC1.stage, hg1, hA1⟩
    · rw [cfbE.k_lv_leq_top.abort2 p r m1 h0 h2]
      cases x with
      | none => exact absurd hx h0
      | some b =>
        cases b with
        | true => exact absurd hx h2
        | false =>
          exact fun _ => ErrClaim.congr
            (T' := ConRon.Arena.fail (.invalid "direct sum: field universe too large"))
            rfl (ErrClaim.fail _ _ (by decide))
  have hp' : (isProp != 0) = true := by simpa using hp
  by_cases hl : large = 0
  · rw [cfbE.arm3 p n m isProp large s io il fv u hp hl, cfbE.j1.arm1]
    simp only [sfbT, hp', hl, bne_self_eq_false, Bool.not_true, Bool.false_eq_true, ite_false]
    exact RefE.ret rfl ⟨hS, IWGrow.refl _, hA⟩
  have hl' : (large != 0) = true := by simpa using hl
  rw [cfbE.arm2 p n m isProp large s io il fv u hp hl]
  simp only [sfbT, hp', hl', Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
  rcases h1 : callW p n "pin_word" [53] m with _ | ⟨rz, m1⟩
  · rw [liftE_none, cfbE.k_pin_word.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨s', hs', -, hmm, hz'⟩ := triple_of_callW (pinWord_specV p hpw n ⟨m, Locals.init []⟩ 53) h1
  simp only at hmm
  subst hs'
  rw [cfbE.k_pin_word.arm1, hmm]
  simp only at hz'
  have hpne : rdW (m.arr64 PINS) 0 ≠ 0 := by
    intro h0; simp [pinWordV, h0] at hz'
  obtain ⟨hrun0, hz⟩ := pinZero_stage hS hz'
  have hzp : rz.headD 0 = pinW m 53 := by
    simp only [pinWordV, hpne, ite_false, Option.some.injEq] at hz'
    rw [← hz']; rfl
  have hF := hS.1.pins.full hpne
  obtain ⟨lz, hdz⟩ := hC.stageT.twin.den.zero
  rw [hF.zeroLevel, ← hzp] at hdz
  refine RefE.bind_right hrun0 ?_
  rcases h2 : callW p n "lvl_eq_true" [u, rz.headD 0] m with _ | ⟨rq, mq⟩
  · rw [liftE_none, cfbE.k_lvl_eq_true.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, cfbE.k_lvl_eq_true.arm1]
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
  refine RefE.bind_right hrun1 ?_
  have hmq : mq = m1 := by rw [← hs2, ← hm2]
  subst hmq
  have hS1 := hC1.stage
  have hidx1 : decHL mq io.toNat il.toNat = some idxArgs := by
    rw [decHL_grow hg1 hib]; exact hidx
  rcases h3 : callW p (n' + 1) "sl_contains" [io, il, fv] mq with _ | ⟨r3, m3⟩
  · rw [liftE_none, cfbE.k_sl_contains.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨s3, hs3, -, hm3, hW3⟩ := triple_of_callW (slContains_spec p hc (n' + 1) ⟨mq, Locals.init []⟩ io il fv) h3
  simp only at hW3 hm3
  obtain ⟨ws, hws, hwsd, hwlt⟩ := slR_of_decHL mq _ _ idxArgs hidx1 (hS1.lt64 (by have := hg1.1; omega))
  simp only [UInt64.ofNat_toNat] at hws
  have hct := containsW_ok (n' + 1) _ _ _ _ _ _ hws hW3
  have hm3' : m3 = mq := by rw [← hs3, hm3]
  subst hm3'
  by_cases hg : (rq.headD 0) = 0 ∧ r3.headD 0 = 0
  · rw [cfbE.k_sl_contains.abort1 p _ r3 m3 hg]
    have hr1 : r1.headD 0 ≠ 2 := by
      intro h2; rw [ite_eq_left h2] at hreq; rw [hg.1] at hreq; exact absurd hreq (by decide)
    have hxn : x ≠ some true := by
      intro hxt; subst hxt; simp only [decLvlEq] at hx; exact hr1 hx
    have hnin : ws.contains fv = false := by
      cases hcw : ws.contains fv
      · rfl
      · rw [hcw, hg.2] at hct; exact absurd hct (by decide)
    have hcond : (x == some true || idxArgs.contains (decI fv)) = false := by
      rw [hwsd, contains_map_decI fv hfv ws hwlt, hnin]
      cases x with
      | none => rfl
      | some b => cases b with
        | false => rfl
        | true => exact absurd rfl hxn
    refine fun _ => ErrClaim.congr (T' := ConRon.Arena.fail (.invalid "direct sum: large eliminator with a \
        non-propositional field outside the indices")) ?_ (ErrClaim.fail _ _ (by decide))
    simp only [hcond]; rfl
  rw [cfbE.k_sl_contains.arm1 p _ r3 m3 hg, cfbE.j1.arm1]
  have hcond : (x == some true || idxArgs.contains (decI fv)) = true := by
    by_cases h2 : r1.headD 0 = 2
    · have : x = some true := by
        simp only [decLvlEq] at hx; rw [h2] at hx
        rcases x with _ | _ | _
        · exact absurd hx (by decide)
        · exact absurd hx (by decide)
        · rfl
      rw [this]; rfl
    · have hct1 : r3.headD 0 ≠ 0 := fun e => hg ⟨by rw [← hreq, ite_eq_right h2], e⟩
      have hin : ws.contains fv = true := by
        rw [hct] at hct1
        cases hcw : ws.contains fv
        · rw [hcw] at hct1; exact absurd rfl hct1
        · rfl
      rw [hwsd, contains_map_decI fv hfv ws hwlt, hin, Bool.or_true]
  exact RefE.ret (by simp only [hcond]; rfl) ⟨hS1, hg1, hA1⟩

/-- **The model of `check_struct_field_sorts_i_go`, both outcomes**: `sl_get` and `fvar_type_d`
(outside the verdict closure) through their `Option` models, the core stubs and
`check_field_sort_bound` through their runs, the recursion through the model itself. -/
l_model csfGoE_spec (p : Prog) (hf : p.lookup "check_struct_field_sorts_i_go" = some checkStructFieldSortsIGoL)
    (hftd : FtdF p) (hb : p.lookup "check_field_sort_bound" = some checkFieldSortBoundL)
  fns [hf ↦ csfGoE]
  specs [callW_spec p n "sl_get", ftdF_spec0 p hftd n, cfbE_spec p hb n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **The model of `check_struct_field_sorts_i`, both outcomes**: `iw_alloc` through its `Option`
model, the fields through `csfGoE`. -/
l_model fsortsE_spec (p : Prog) (hf : p.lookup "check_struct_field_sorts_i" = some checkStructFieldSortsIL)
    (hgo : p.lookup "check_struct_field_sorts_i_go" = some checkStructFieldSortsIGoL)
    (hia : p.lookup "iw_alloc" = some iwAlloc) (hftd : FtdF p)
    (hb : p.lookup "check_field_sort_bound" = some checkFieldSortBoundL)
  fns [hf ↦ fsortsE]
  specs [iwAlloc_specW p hia n, csfGoE_spec p hgo hftd hb n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `check_struct_field_sorts_i_go` at `j` gives besides the twin's sorts `xs` of the fields
below `j` (the result slice `res` pre-sized, `acc` the `k` sorts above `j` already written): the
stage relation, growth from `m0`, the sorts written in front of `acc`. -/
structure CsfGoPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m0 : Mem) (res j : Word) (k : Nat) (acc : List LIdx) (m' : Mem) (xs : List LIdx) (a' : AState) :
    Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m0 m'
  sorts : decHL m' res.toNat (j.toNat + k) = some (xs ++ acc)
  top : res.toNat + j.toNat + k ≤ iwTop m'
  abs : AbsOK m'

/-- What `check_struct_field_sorts_i` gives besides the twin's sorts `xs`: the stage relation,
growth, the sorts as the `IW` slice `[r₀, r₁]`. -/
structure FsortsPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (r : List Word) (m' : Mem) (xs : List LIdx) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  sorts : decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some xs
  top : (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m'
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
theorem csfGo_ref (hg : p.lookup "sl_get" = some slGet) (hpw : p.lookup "pin_word" = some pinWordL)
    (het : p.lookup "lvl_eq_true" = some lvlEqTrue) (hc : p.lookup "sl_contains" = some slContains) (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (isProp large s nP fo fl io il res j : Word) (m0 : Mem) (k : Nat)
      (acc : List LIdx) (fvs idxArgs : List EIdx) (fvsP : List ConLeche.Expr),
    StageC dn vis fe env m a → AbsOK m → IWGrow m0 m → iwTop m0 ≤ res.toNat →
    res.toNat + j.toNat + k ≤ iwTop m →
    decHL m (res.toNat + j.toNat) k = some acc →
    decHL m0 fo.toNat fl.toNat = some fvs → fo.toNat + fl.toNat ≤ iwTop m0 →
    decHL m0 io.toNat il.toNat = some idxArgs → io.toNat + il.toNat ≤ iwTop m0 →
    H s → (∃ sP, denoteL a.store.ls (decI s) = some sP) → nP.toNat + j.toNat < 2 ^ 64 →
    Frontend.denoteEList a.store fvs = some fvsP →
    (∀ i, i < j.toNat → ∀ x, fvsP[i]? = some x →
      ConLeche.Expr.WScoped (nP.toNat + i) x.fvarTypeD) →
    RefE (VerdictCtx p) (csfGoE p n m vis isProp large s nP fo fl io il res j)
      (checkStructFieldSortsI V fe (isProp != 0) (large != 0) (decI s) nP.toNat fvs idxArgs j.toNat) a
      (fun v xs a' => CsfGoPost dn vis fe env m0 res j k acc v.2 xs a') := by
  induction n with
  | zero => intros; rw [csfGoE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a isProp large s nP fo fl io il res j m0 k acc fvs idxArgs fvsP hC hA hg0 hr0 hroom hacc
    hfvs hfb hidx hib hs hsP hnj hfP hws
  have hS := hC.stage
  by_cases hj : j = 0
  · subst hj
    rw [csfGoE.arm1 p n m vis isProp large s nP fo fl io il res 0 rfl]
    simp only [UInt64.toNat_zero, Nat.add_zero] at hacc hroom
    exact RefE.ret rfl ⟨hC, hg0, by simpa using hacc, by simpa using hroom, hA⟩
  rw [csfGoE.arm2 p n m vis isProp large s nP fo fl io il res j hj]
  obtain ⟨J, hjJ⟩ : ∃ J, j.toNat = J + 1 :=
    ⟨j.toNat - 1, by have : j.toNat ≠ 0 := fun e => hj (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  have hJ : (j - 1).toNat = J := by rw [sumToNat_pred hj]; omega
  rw [hjJ, checkStructFieldSortsI_succ]
  -- the field (`sl_get`, L only)
  rcases h1 : callW p n "sl_get" [fo, fl, j - 1] m with _ | ⟨r1, m1⟩
  · rw [liftE_none, csfGoE.k_sl_get.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, csfGoE.k_sl_get.arm1]
  obtain ⟨s1, hs1, -, hm1, hgw⟩ := triple_of_callW (slGet_specW p hg n ⟨m, Locals.init []⟩ fo fl (j - 1)) h1
  have hl : ¬ fl ≤ j - 1 := by
    intro hl'; simp [getW, hl'] at hgw
  have hJl : J < fl.toNat := by
    have : ¬ fl.toNat ≤ (j - 1).toNat := fun e => hl (UInt64.le_iff_toNat_le.mpr e)
    omega
  have hT := hS.lt64 (x := iwTop m) (Nat.le_refl _)
  have hgT := hg0.1
  have hfvs' : decHL m fo.toNat fl.toNat = some fvs := by rw [decHL_grow hg0 hfb]; exact hfvs
  obtain ⟨w, hw, hwl, hwd⟩ := decHL_get' hfvs' J hJl (by omega)
  have efo : fo + (j - 1) = UInt64.ofNat (fo.toNat + J) := by
    apply UInt64.toNat_inj.mp; rw [sum_toNat_add (by omega), hJ]; simp; omega
  have hr1 : r1.headD 0 = w := by
    simp only [getW, hl, ite_false, Option.some.injEq] at hgw
    rw [← hgw, efo, hw]
  have hm1' : m = m1 := by rw [← hs1, hm1]
  subst hm1'
  rw [hr1]
  have hget : fvs[J]? = some (decI w) := by
    rw [List.getElem?_eq_getElem (by rw [decHL_length m hfvs']; exact hJl), hwd]
  obtain ⟨aP, haP, hda⟩ := ConRon.Bridge.ExprOps.denoteEList_getElem? fvs fvsP hfP J (decI w) hget
  have hwsa := hws J (by omega) aP haP
  refine RefE.bind_right (v := decI w) (a₁ := a) (by rw [hget]; rfl) ?_
  have hdep : (nP + (j - 1)).toNat = nP.toNat + J := by rw [sum_toNat_add (by omega), hJ]
  -- `fvar_type_d` (outside the verdict closure)
  rcases h2 : ftdF m [w] with _ | ⟨rt, m1⟩
  · rw [liftE_none, csfGoE.k_fvar_type_d.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, csfGoE.k_fvar_type_d.arm1]
  obtain ⟨t, a1, hrun1, hS1, hg1, ht1, ht⟩ := (sumSim_of_relW (ftdF_ok dn vis fe w hwl) hS) rt m1 h2
  have hA1 : AbsOK m1 := ftdF_afr h2 hA
  obtain ⟨ha1, htd⟩ := ConRon.Bridge.Inductives.fvarTypeD_run hC.check.state hda hrun1
  rw [ha1] at hS1 hrun1
  have hC1 : StageC dn vis fe env m1 a := hC.of_pstep hS1 hA1 (PStep.refl hC.check.state)
  refine RefE.bind_right hrun1 ?_
  have hdt : denoteE a.store (decI (rt.headD 0)) = some aP.fvarTypeD := by rw [ht]; exact htd
  -- `infer_type_core`
  rcases h3 : callE p n "infer_type_core" [vis, nP + (j - 1), rt.headD 0] m1 with e3 | ⟨ry, m2⟩
  · rw [csfGoE.k_infer_type_core.none]
    refine RefE.bind_left fun hV => ?_
    have := hV.core.inferTypeCore n (by omega) hC1.stageT (nP + (j - 1)) (rt.headD 0) ht1 _ h3
    rwa [hdep, ht] at this
  rw [csfGoE.k_infer_type_core.arm1]
  have h2' := inferC_rsim hq henv n (by omega) hC1 hA1 (nP + (j - 1)) (rt.headD 0) ht1 hdt
    (by rw [hdep]; exact hwsa)
  rw [hdep, ht] at h2'
  obtain ⟨ty, a2, hrun2, hC2, hg2, ⟨hy1, hy⟩, hA2, c2, tyP, htyP, hwty⟩ := h2' (ry, m2) (callW_of_callE h3)
  dsimp only at hC2 hg2 hy1 hy hA2
  refine RefE.bind_right hrun2 ?_
  -- `ensure_sort_core`
  rcases h4 : callE p n "ensure_sort_core" [vis, nP + (j - 1), ry.headD 0] m2 with e4 | ⟨ru, m3⟩
  · rw [csfGoE.k_ensure_sort_core.none]
    refine RefE.bind_left fun hV => ?_
    have := hV.core.ensureSortCore n (by omega) hC2.stageT (nP + (j - 1)) (ry.headD 0) hy1 _ h4
    rwa [hdep, hy] at this
  rw [csfGoE.k_ensure_sort_core.arm1]
  have h3' := ensureSortC_rsim hq henv n (by omega) hC2 hA2 (nP + (j - 1)) (ry.headD 0) hy1
    (by rw [hy]; exact htyP) (by rw [hdep]; exact hwty)
  rw [hdep, hy] at h3'
  obtain ⟨u, a3, hrun3, hC3, hg3, ⟨hu1, hu⟩, hA3, c3, lu, hdu⟩ := h3' (ru, m3) (callW_of_callE h4)
  dsimp only at hC3 hg3 hu1 hu hA3
  refine RefE.bind_right hrun3 ?_
  have hg03 := ((hg0.trans hg1).trans hg2).trans hg3
  have hidx3 : decHL m3 io.toNat il.toNat = some idxArgs := by rw [decHL_grow hg03 hib]; exact hidx
  obtain ⟨sP, hsP0⟩ := hsP
  rw [← hu] at hdu
  -- `check_field_sort_bound`
  have h4' := cfb_ref hq.closed hLC hLT hpw het hc n m3 a3 isProp large s io il w (ru.headD 0) idxArgs hC3 hA3
    hu1 hs hwl hidx3 (by have := hg03.1; omega) hdu (ConRon.Bridge.denoteL_ext hsP0 (c2.ext.trans c3.ext))
  rw [hu] at h4'
  rcases h5 : cfbE p n m3 isProp large s io il w (ru.headD 0) with e5 | ⟨r5, m4⟩
  · rw [csfGoE.k_check_field_sort_bound.none]
    rw [h5] at h4'
    exact RefE.bind_left fun _ => h4' trivial
  rw [csfGoE.k_check_field_sort_bound.arm1]
  rw [h5] at h4'
  obtain ⟨x4, a4, hrun4, ⟨hS4, hg4, hA4⟩⟩ := h4'
  dsimp only at hS4 hg4 hA4
  refine RefE.bind_right hrun4 ?_
  have c4 := sfbT_cstep hC3.check hrun4
  have hC4 : StageC dn vis fe env m4 a4 := hC3.of_check hS4 hA4 c4.ok c4.ext
  -- the write (L only)
  have hg14 := ((hg1.trans hg2).trans hg3).trans hg4
  have hres1 : (res + (j - 1)).toNat = res.toNat + J := by rw [sum_toNat_add (by omega), hJ]
  have hsz4 : res.toNat + J < (m4.arr64 IW).size := by
    obtain ⟨h1, -, -, -, -⟩ := hS4.2; have := hg14.1; omega
  have hacc4 : decHL m4 (res.toNat + J + 1) k = some acc := by
    rw [decHL_grow hg14 (by omega)]; rw [show res.toNat + J + 1 = res.toNat + j.toNat by omega]; exact hacc
  have hacc' := sumDecHL_write_front m4 _ k _ (ru.headD 0) acc hres1 hsz4 hu1 hacc4
  rw [hu] at hacc'
  have htop' : iwTop (m4.set64 IW (res + (j - 1)) (ru.headD 0)) = iwTop m4 := by
    simp only [iwTop]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have hAw := set64IW_afr m4 (res + (j - 1)) (ru.headD 0) hA4
  have hCw : StageC dn vis fe env (m4.set64 IW (res + (j - 1)) (ru.headD 0)) a4 :=
    hC4.of_pstep (hS4.set_iw _ _) hAw (PStep.refl hC4.check.state)
  have hx14 := c2.ext.trans (c3.ext.trans c4.ext)
  -- the fields below
  have hrec := ih (by omega) (m4.set64 IW (res + (j - 1)) (ru.headD 0)) a4 isProp large s nP fo fl io il
    res (j - 1) m0 (k + 1) (u :: acc) fvs idxArgs fvsP hCw hAw
    ((hg03.trans hg4).set_iw _ _ (by omega)) hr0 (by rw [htop', hJ]; have := hg14.1; omega)
    (by rw [hJ]; exact hacc') hfvs hfb hidx hib hs ⟨sP, ConRon.Bridge.denoteL_ext hsP0 hx14⟩ (by omega)
    (ConRon.Bridge.denoteEList_ext hx14 _ _ hfP) (fun i hi => hws i (by omega))
  rw [hJ] at hrec
  rcases h6 : csfGoE p n (m4.set64 IW (res + (j - 1)) (ru.headD 0)) vis isProp large s nP fo fl io il res
      (j - 1) with e6 | ⟨w6, m6⟩
  · rw [csfGoE.k_check_struct_field_sorts_i_go.none]
    rw [h6] at hrec
    exact RefE.bind_left hrec
  rw [csfGoE.k_check_struct_field_sorts_i_go.arm1]
  rw [h6] at hrec
  obtain ⟨xs, a5, hrun5, hR5⟩ := hrec
  have hd5 := hR5.sorts
  have ht5 := hR5.top
  dsimp only at hd5 ht5
  rw [hJ] at hd5 ht5
  refine RefE.bind_right hrun5 (RefE.ret rfl ⟨hR5.stage, hR5.grow, ?_, by dsimp only; omega, hR5.abs⟩)
  dsimp only
  rw [hjJ, show J + 1 + k = J + (k + 1) by omega, hd5]; simp

include hq henv hLC hLT in
/-- **`check_struct_field_sorts_i` refines `checkStructFieldSortsI .verified`, both outcomes**: the
allocation (L only), then `csfGo_ref` from the top field. -/
theorem fsorts_ref (hg : p.lookup "sl_get" = some slGet) (hpw : p.lookup "pin_word" = some pinWordL)
    (het : p.lookup "lvl_eq_true" = some lvlEqTrue) (hc : p.lookup "sl_contains" = some slContains) (n : Nat) (hn : n ≤ 2 ^ 62)
    (m : Mem) (a : AState) (isProp large s nP fo fl io il nW : Word) (fvs idxArgs : List EIdx)
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) (hfvs : decHL m fo.toNat fl.toNat = some fvs)
    (hfb : fo.toNat + fl.toNat ≤ iwTop m) (hidx : decHL m io.toNat il.toNat = some idxArgs)
    (hib : io.toNat + il.toNat ≤ iwTop m) (hs : H s) {sP : ConLeche.Level}
    (hsP : denoteL a.store.ls (decI s) = some sP) (hnj : nP.toNat + nW.toNat < 2 ^ 64)
    {fvsP : List ConLeche.Expr} (hfP : Frontend.denoteEList a.store fvs = some fvsP)
    (hws : ∀ i, i < nW.toNat → ∀ x, fvsP[i]? = some x →
      ConLeche.Expr.WScoped (nP.toNat + i) x.fvarTypeD) :
    RefE (VerdictCtx p) (fsortsE p (n + 1) m vis isProp large s nP fo fl io il nW)
      (checkStructFieldSortsI V fe (isProp != 0) (large != 0) (decI s) nP.toNat fvs idxArgs nW.toNat) a
      (fun v xs a' => FsortsPost dn vis fe env m v.1 v.2 xs a') := by
  rw [fsortsE.arm1]
  rcases hal : allocW m nW with _ | ⟨res, m1⟩
  · rw [liftE_none, fsortsE.k_iw_alloc.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, fsortsE.k_iw_alloc.arm1]
  obtain ⟨hS1, hg1, hrt, ht1⟩ := allocW_stage hal hC.stage
  have hA1 := allocW_afr hal hA
  have hC1 : StageC dn vis fe env m1 a := hC.of_pstep hS1 hA1 (PStep.refl hC.check.state)
  have h := csfGo_ref hq henv hLC hLT hg hpw het hc n hn m1 a isProp large s nP fo fl io il res nW m 0 []
    fvs idxArgs fvsP hC1 hA1 hg1 (by omega) (by omega) (by simp [decHL, hslice?]) hfvs hfb hidx hib hs
    ⟨sP, hsP⟩ hnj hfP hws
  rcases h2 : csfGoE p n m1 vis isProp large s nP fo fl io il res nW with e2 | ⟨z, m2⟩
  · rw [fsortsE.k_check_struct_field_sorts_i_go.none]; rw [h2] at h; exact h
  rw [fsortsE.k_check_struct_field_sorts_i_go.arm1]
  rw [h2] at h
  obtain ⟨xs, a', hrun, hR⟩ := h
  exact RefE.ret hrun ⟨hR.stage, hR.grow, by simpa using hR.sorts, by simpa using hR.top, hR.abs⟩

include hq henv hLC hLT in
/-- `check_struct_field_sorts_i` under `StageC` as a `Sim` of its call (`fsorts_ref`'s ok half,
from the run). -/
theorem installSimFsortsC (hP : SumProg p) (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    (isP large s nP fo fl io il j : Word) (hs : H s) (fvs idx : List EIdx) {sP : ConLeche.Level}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) (hsP : denoteL a.store.ls (decI s) = some sP)
    (hfd : decHL m fo.toNat fl.toNat = some fvs) (hfb : fo.toNat + fl.toNat ≤ iwTop m)
    (hid : decHL m io.toNat il.toNat = some idx) (hib : io.toNat + il.toNat ≤ iwTop m)
    (hnj : nP.toNat + j.toNat < 2 ^ 64) {fvsP : List ConLeche.Expr}
    (hfP : Frontend.denoteEList a.store fvs = some fvsP)
    (hws : ∀ i, i < j.toNat → ∀ x, fvsP[i]? = some x →
      ConLeche.Expr.WScoped (nP.toNat + i) x.fvarTypeD) :
    Sim (callW p n "check_struct_field_sorts_i" [vis, isP, large, s, nP, fo, fl, io, il, j] m)
      (checkStructFieldSortsI V fe (isP != 0) (large != 0) (decI s) nP.toNat fvs idx j.toNat) a
      (fun r x m' a' => StageC dn vis fe env m' a' ∧ IWGrow m m' ∧
        decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some x ∧
        (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ AbsOK m') := by
  rcases n with _ | k
  · intro r m' e; rw [callW_zero] at e; cases e
  intro r m' e
  obtain ⟨s', rfl, -, x, a', hrun, hR⟩ := RefE.run_okW
    (fsortsE_spec p hP.hcfs hP.hcfg hP.ha hP.ad.ftd hP.hfsb (k + 1) ⟨m, Locals.init []⟩ vis isP large s nP fo fl io il j)
    (fsorts_ref hq henv hLC hLT hP.hg hP.hpw hP.het hP.hcn k (by omega) m a isP large s nP fo fl io il j
      fvs idx hC hA hfd hfb hid hib hs hsP hnj hfP hws) e
  exact ⟨x, a', hrun, hR.stage, hR.grow, hR.sorts, hR.top, hR.abs⟩

include hq henv hLC hLT in
/-- **`check_struct_field_sorts_i` refines `checkStructFieldSortsI .verified`** under `StageC`
(`fsorts_ref`'s ok half; the fields' denotations and scoping as con-ron's
`checkStructFieldSortsI_spec` asks): the sorts in a fresh `IW` slice. -/
@[refines ConRon.Arena.checkStructFieldSortsI]
theorem checkStructFieldSortsI_refinesC (hg : p.lookup "sl_get" = some slGet)
    (hpw : p.lookup "pin_word" = some pinWordL)
    (het : p.lookup "lvl_eq_true" = some lvlEqTrue) (hc : p.lookup "sl_contains" = some slContains)
    (hb : p.lookup "check_field_sort_bound" = some checkFieldSortBoundL)
    (hgo : p.lookup "check_struct_field_sorts_i_go" = some checkStructFieldSortsIGoL)
    (hia : p.lookup "iw_alloc" = some iwAlloc)
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
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check_struct_field_sorts_i"
      [vis, isProp, large, s, nP, fo, fl, io, il, nW]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (checkStructFieldSortsI V fe (isProp != 0) (large != 0) (decI s) nP.toNat fvs idxArgs
        nW.toNat) a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (checkStructFieldSortsI V fe (isProp != 0) (large != 0)
        (decI s) nP.toNat fvs idxArgs nW.toNat) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decHL s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat =
        some (AM.res (checkStructFieldSortsI V fe (isProp != 0) (large != 0) (decI s) nP.toNat fvs
          idxArgs nW.toNat) a₀) ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (RefE.triple (fsortsE_spec p hp hgo hia hftd hb (n + 1) s₀ vis isProp large s nP fo fl io il nW)
      (fsorts_ref hq henv hLC hLT hg hpw het hc n hn _ a₀ isProp large s nP fo fl io il nW fvs idxArgs hC hA
        hfvs hfb hidx hib hs hsP hnj hfP hws)) fun _ _ ⟨hl, _, _, hrun, hR⟩ => by
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
    exact ⟨hl, hok, by rw [hst]; exact hR.stage, hR.grow, by rw [hres]; exact hR.sorts, hR.abs⟩

end sims

end L.Ind
