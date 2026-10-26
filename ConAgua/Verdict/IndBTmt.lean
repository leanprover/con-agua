import ConAgua.Verdict.IndBToi

/-!
# Error refinement of `target_major_of_outside_tail` (lane `verdicts-b`, helper `ib`)

Mirrors `tmtW_simC` (`IndT/RecGenTmf`): `target_outside_inst` (`targetOutsideInst_claim`), then the
level comparison (`lvl_eq_c`, `closedNV`), whose two rejects are the twin's `liftFueled` decline
(code `0`'s result) and the universe fail.
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dMajor)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model tmtE_spec (p : Prog) (hf : p.lookup "target_major_of_outside_tail" = some targetMajorOfOutsideTail)
  fns [hf ↦ tmtE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors

section sims
variable {p : Prog} (hP : TmtProg p) (hIlpf : IlpfF p) (hcore : CoreStageClosed p)
  (hLC : LvlCacheProg p) (hnv : closedNV p _root_.L.Checker.nvFns = true) {env : ConLeche.Env}
  {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

include hP hIlpf hcore hLC hnv in
/-- **`target_major_of_outside_tail`'s model error claim** (`tmtW_simC`'s hypotheses). -/
theorem tmtE_claim (n : Nat) {m : Mem} {a : AState} {pp pfo pfl I us dso dsl cso csl : Word}
    {bs : BlockShape} {pfvs ds : List EIdx} {ctors : List (IConstantVal × Nat)}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hq : DecB (fun m => decBS m pp.toNat) m bs) (hq9 : pp.toNat + 9 ≤ iwTop m)
    (hI : H I) (hus : H us) (hds : DecB (fun m => decHL m dso.toNat dsl.toNat) m ds)
    (hdsb : dso.toNat + dsl.toNat < 2 ^ 64)
    (hct : DecB (fun m => decPL m (decCN m) cso.toNat csl.toNat) m ctors)
    (hpf : DecB (fun m => decHL m pfo.toNat pfl.toNat) m pfvs) (hPm : PosMR m)
    {IP : ConLeche.Name} (hIP : denoteN a.store.ns (decI I) = some IP)
    {usP : List ConLeche.Level} (husP : denoteLs a.store.lss (decI us) = some usP)
    {dsP : List ConLeche.Expr} (hdsP : Frontend.denoteEList a.store ds = some dsP)
    {lr : ConLeche.Level} (hres : denoteL a.store.ls bs.resSort = some lr) :
    ∀ e, tmtE p (n + 1) m vis pp pfo pfl I us dso dsl cso csl = .error e →
      ErrClaim (tmoTailT fe bs pfvs ds dsl.toNat ctors (decI I) (decI us)) a e := by
  intro e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hS := hC.stage
  rw [tmtE.arm1] at he
  unfold tmoTailT
  cases h1 : callE p n "target_outside_inst" [vis, I, us, dso, dsl] m with
  | error e1 =>
    rw [h1, tmtE.k_target_outside_inst.none] at he
    cases he
    exact ErrClaim.bind_left (CoreSpecE.of_callE (targetOutsideInst_claim hP.toi hIlpf hnv n ⟨m, Locals.init []⟩ a I us
      dso dsl ds hC hI hus hds hdsb) h1)
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, tmtE.k_target_outside_inst.arm1] at he
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (targetOutsideInst_spec p hP.toi (realCall p) (realCall_spec p) n _ vis I us dso dsl) (callW_of_callE h1)
  subst hs1
  obtain ⟨x, a', hrun, hS1, hg1, hT1, hAF⟩ := toiW_ok (IlpRd.realC hIlpf hC) hW1 hS hI hus hds hdsb
  have hA1 := hAF toiAfr hA
  obtain ⟨c1, v, ⟨-, hlP⟩, -⟩ := ConRon.Bridge.Inductives.targetOutsideInst_spec fe (decI I) IP
    (decI us) usP ds dsP a a' x hC.check ⟨hIP, husP, hdsP⟩ hrun
  obtain ⟨hr1, hn1, hsH, hsd⟩ := hT1
  refine ErrClaim.bind_right hrun ?_
  obtain ⟨-, -, hrsH, hrsd⟩ := partsShapeWords hg1 hq hq9
  have hC1 : StageC dn vis fe env s1.mem a' := hC.of_check hS1 hA1 c1.ok c1.ext
  have hdu : denoteL a'.store.ls (decI (r1.tail.headD 0)) = some v.2 := by rw [hsd]; exact hlP
  have hdv : denoteL a'.store.ls (decI (rdW (s1.mem.arr64 IW) (pp + 6))) = some lr := by
    rw [hrsd]; exact ConRon.Bridge.denoteL_ext hres c1.ext
  cases h2 : callE p n "lvl_eq_c" [r1.tail.headD 0, rdW (s1.mem.arr64 IW) (pp + 6)] s1.mem with
  | error e2 =>
    rw [h2, tmtE.k_lvl_eq_c.none] at he
    cases he
    exact ErrClaim.bind_left (ErrClaim.of_callE_nv hnv (by decide +kernel) h2)
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  obtain ⟨xl, al, hrunl, hC2, hg2, hx, hA2, -⟩ := lvlEqC_simC p hcore hLC n hC1 hA1 _ _ hsH hrsH v.2 lr hdu hdv r2 m2
    (callW_of_callE h2)
  rw [hsd, hrsd] at hrunl
  refine ErrClaim.bind_right hrunl ?_
  by_cases h0 : r2.headD 0 = 0
  · rw [h2, tmtE.k_lvl_eq_c.abort1 p n pfo pfl I us dso dsl cso csl _ r2 m2 h0] at he
    cases he
    have hn : xl = none := by
      rcases xl with _ | b
      · rfl
      · cases b <;> simp only [decLvlEq] at hx <;> rw [hx] at h0 <;> exact absurd h0 (by decide)
    subst hn
    exact ErrClaim.bind_left (ErrClaim.fail _ _ (by decide))
  by_cases h2' : r2.headD 0 = 2
  · rw [h2, tmtE.k_lvl_eq_c.arm1 p n pfo pfl I us dso dsl cso csl _ r2 m2 h0 h2'] at he
    cases h3 : callE p n "mk_target_major" [I, us, dso, dsl, dsl, r1.headD 0, cso, csl, 0, 0, 0, pfo, pfl] m2 with
    | error e3 =>
      rw [h3, tmtE.k_mk_target_major.none] at he
      cases he
      exact ErrClaim.of_callE_nv hnv (by decide +kernel) h3
    | ok q3 =>
      rw [h3, tmtE.k_mk_target_major.arm1] at he
      cases he
  rw [h2, tmtE.k_lvl_eq_c.abort2 p n pfo pfl I us dso dsl cso csl _ r2 m2 h0 h2'] at he
  cases he
  have hf : xl = some false := by
    rcases xl with _ | b
    · simp only [decLvlEq] at hx; exact absurd hx h0
    · cases b
      · rfl
      · simp only [decLvlEq] at hx; exact absurd hx h2'
  subst hf
  simp only [liftFueled, pure_bind, Bool.false_eq_true, ite_false]
  exact ErrClaim.bind_left (ErrClaim.fail _ _ (by decide))

include hP hIlpf hcore hLC hnv in
/-- **`target_major_of_outside_tail`'s error claim** (every fuel). -/
theorem tmoTail_claim (N : Nat) (s₀ : St) (a₀ : AState) (pp pfo pfl I us dso dsl cso csl : Word)
    (bs : BlockShape) (pfvs ds : List EIdx) (ctors : List (IConstantVal × Nat))
    (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hq : DecB (fun m => decBS m pp.toNat) s₀.mem bs) (hq9 : pp.toNat + 9 ≤ iwTop s₀.mem)
    (hI : H I) (hus : H us) (hds : DecB (fun m => decHL m dso.toNat dsl.toNat) s₀.mem ds)
    (hdsb : dso.toNat + dsl.toNat < 2 ^ 64)
    (hct : DecB (fun m => decPL m (decCN m) cso.toNat csl.toNat) s₀.mem ctors)
    (hpf : DecB (fun m => decHL m pfo.toNat pfl.toNat) s₀.mem pfvs) (hPm : PosMR s₀.mem)
    {IP : ConLeche.Name} (hIP : denoteN a₀.store.ns (decI I) = some IP)
    {usP : List ConLeche.Level} (husP : denoteLs a₀.store.lss (decI us) = some usP)
    {dsP : List ConLeche.Expr} (hdsP : Frontend.denoteEList a₀.store ds = some dsP)
    {lr : ConLeche.Level} (hres : denoteL a₀.store.ls bs.resSort = some lr) :
    CoreSpecE p N "target_major_of_outside_tail" [vis, pp, pfo, pfl, I, us, dso, dsl, cso, csl]
      (tmoTailT fe bs pfvs ds dsl.toNat ctors (decI I) (decI us)) s₀ a₀ := by
  cases N with
  | zero => exact CoreSpecE.zero _ _ _ _ _ _
  | succ n =>
    refine CoreSpecE.of_runs fun e hc => ?_
    by_cases hk0 : e.cls = 0
    · exact ErrClaim.of_cls0 hk0
    exact tmtE_claim hP hIlpf hcore hLC hnv n hC hA hq hq9 hI hus hds hdsb hct hpf hPm hIP husP hdsP hres e
      (triple_of_callE_err (tmtE_spec p hP.tail (n + 1) s₀ vis pp pfo pfl I us dso dsl cso csl) hc
        (Err.code_ne_of_cls hk0))

end sims

end L.Ind
