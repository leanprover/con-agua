import ConAgua.Arena.DeclValT
import ConAgua.Arena.Verdict
import ConAgua.Arena.IndRealLvlT

/-!
# The verdict claims of `check_thm_val` and `check_value_group` (lane `verdicts-b`)

The error models (`l_model … errors`) of `check_thm_val`, `lvl_eq_fueled` and
`check_value_group`, and their error refinements: a failing call of class `1`/`2` claims the
twin's `checkThmVal`/`checkValueGroup` fails with an error of that class, under the hypotheses of
the ok refinements (`tvW_okT`, `cvgW_okT`) and the callees' error claims.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind

l_model lvlEqFueled_specE (p : Prog) (hf : p.lookup "lvl_eq_fueled" = some lvlEqFueled)
  fns [hf ↦ lvlEqFueledE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] finish [tierW, idxW] errors

/-- A bounded read is the defaulting one (for `grind`, in `check_value_group`'s error model:
the run's loads are bounded, the model's are `rdW`). -/
theorem getElem_eq_getD_W (a : Array Word) (i : Nat) (h : i < a.size) : a[i] = a[i]?.getD 0 := by
  simp [h]
theorem rdW_def_W (a : Array Word) (x : Word) : rdW a x = a[x.toNat]?.getD 0 := rfl

section cvg
attribute [local grind =] getElem_eq_getD_W rdW_def_W

/- `finish` with `gen 20`, `instances 4000` (the default `1000` is reached: the injectivity of
the calls' argument lists); `simp []` fails here (its `simp_all` unfolds the continuations). -/
l_model checkValueGroup_specE (p : Prog) (hf : p.lookup "check_value_group" = some checkValueGroupL)
  fns [hf ↦ checkValueGroupE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] finish [tierW, idxW] gen 20
  heartbeats 4000000 instances 4000 errors

end cvg

l_model checkThmVal_specE (p : Prog) (hf : p.lookup "check_thm_val" = some checkThmValL)
  fns [hf ↦ checkThmValE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] heartbeats 400000 simp [] errors

local notation "V" => ConLeche.CheckMode.verified

/-! ## The callees' error claims (hypotheses, discharged bottom-up) -/

/-- A callee outside the verdict closure: its errors are of class `0` (`callE_nv`). -/
def NVAt (p : Prog) (f : FnName) : Prop :=
  ∀ n args m e, callE p n f args m = .error e → e.cls = 0

/-- **The core stubs' error claims under `StageT`**: the error halves of `KnotStageProg`'s
`inferTypeCore_sim`, `ensureSortCore_sim`, `isDefEqCore_sim`. -/
structure CoreStubsE (p : Prog) : Prop where
  inferTypeCore : ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {m : Mem} {a : AState}, StageT dn vis fe m a → ∀ (dep t : Word), H t →
    ∀ e, callE p n "infer_type_core" [vis, dep, t] m = .error e →
      ErrClaim (inferTypeCore V fe checkFuel dep.toNat (decI t)) a e
  ensureSortCore : ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {m : Mem} {a : AState}, StageT dn vis fe m a → ∀ (dep t : Word), H t →
    ∀ e, callE p n "ensure_sort_core" [vis, dep, t] m = .error e →
      ErrClaim (ensureSortCore V fe checkFuel dep.toNat (decI t)) a e
  isDefEqCore : ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {m : Mem} {a : AState}, StageT dn vis fe m a → ∀ (dep x y : Word), H x → H y →
    ∀ e, callE p n "is_def_eq_core" [vis, dep, x, y] m = .error e →
      ErrClaim (isDefEqCore V fe checkFuel dep.toNat (decI x) (decI y)) a e

/-- **`install_value_guards`' error claim under `StageT`** (the error half of `IvgT`). -/
def IvgE (p : Prog) : Prop :=
  ∀ {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m : Mem} {q v : Word} {cv : IConstantVal} {e : Err},
    callE p n "install_value_guards" [vis, q, v] m = .error e → StageT dn vis fe m a →
    decCV (erA m) q.toNat = some cv → q.toNat + 3 < 2 ^ 64 → v.toNat < 2 ^ 32 →
    (∃ ks, cv.levelParams.mapM (denoteN a.store.ns) = some ks) → L.Stubs.CrOK m →
    ErrClaim (installValueGuards fe cv (decI v)) a e

/-! ## `lvl_eq_fueled` -/

/-- **`lvl_eq_fueled` under `StageT`, the answer exact**: `lvl_eq_c`'s word is `0`, `1` or `2`
(`lvlEqC_simTE`), so `0` is the twin's `some false`, `1` its `some true`. -/
theorem lfW_okTE {p : Prog} (hq : KnotStageProg p) (hL : LvlCacheProg p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {n : Nat} {m m' : Mem} {a : AState} {u v : Word} {r : List Word}
    (h : lfW (realCall p) n m u v = some (r, m')) (hS : StageT dn vis fe m a) (hu : H u) (hv : H v)
    (lu lv : ConLeche.Level) (hdu : denoteL a.store.ls (decI u) = some lu)
    (hdv : denoteL a.store.ls (decI v) = some lv) :
    ∃ x a', (lvlEq? (decI u) (decI v)).run a = .ok (x, a') ∧ StageT dn vis fe m' a' ∧
      IWGrow m m' ∧ x = some (r.headD 0 != 0) := by
  cases n with
  | zero => simp [lfW] at h
  | succ n =>
  simp only [lfW] at h
  cases hs : realCall p n "lvl_eq_c" [u, v] m with
  | none => simp [hs] at h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  simp only [hs] at h
  by_cases h0 : r1.headD 0 = 0
  · rw [ite_eq_left h0] at h; exact absurd h (by simp)
  rw [ite_eq_right h0] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨x, a1, hrun, hSt, hg, hdec⟩ :=
    lvlEqC_simTE p hq.closed hL n hS u v hu hv lu lv hdu hdv r1 m1 hs
  refine ⟨x, a1, hrun, hSt, hg, ?_⟩
  unfold decLvlEq at hdec
  rcases x with _ | _ | _ <;> simp_all

/-- **`lvl_eq_fueled`'s verdict claim**: its decline (`lvl_eq_c` answers `0`) is the twin's
`liftFueled` on `none`; `lvl_eq_c` claims nothing. -/
theorem lvlEqFueled_errT {p : Prog} (hq : KnotStageProg p) (hL : LvlCacheProg p)
    (hf : p.lookup "lvl_eq_fueled" = some lvlEqFueled) (hnv : NVAt p "lvl_eq_c")
    {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {n : Nat} {m : Mem} {a : AState} {u v : Word} {β : Type} (k : Bool → AM β)
    (hS : StageT dn vis fe m a) (hu : H u) (hv : H v)
    (lu lv : ConLeche.Level) (hdu : denoteL a.store.ls (decI u) = some lu)
    (hdv : denoteL a.store.ls (decI v) = some lv) {e : Err}
    (hc : callE p n "lvl_eq_fueled" [u, v] m = .error e) :
    ErrClaim (lvlEq? (decI u) (decI v) >>= fun x => liftFueled "level comparison" x >>= k) a e := by
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (lvlEqFueled_specE p hf n ⟨m, Locals.init []⟩ u v) hc
    (Err.code_ne_of_cls hk0)
  cases n with
  | zero => rw [lvlEqFueledE.eq_1] at hW; cases hW; exact absurd rfl hk0
  | succ n =>
  rw [lvlEqFueledE.arm1] at hW
  cases h1 : callE p n "lvl_eq_c" [u, v] m with
  | error e1 =>
    rw [h1, lvlEqFueledE.k_lvl_eq_c.none] at hW; cases hW; exact ErrClaim.of_cls0 (hnv _ _ _ _ h1)
  | ok q =>
  obtain ⟨r1, m1⟩ := q
  rw [h1] at hW
  by_cases h0 : r1.headD 0 = 0
  · rw [lvlEqFueledE.k_lvl_eq_c.abort1 p r1 m1 h0] at hW
    cases hW
    obtain ⟨x, a1, hrun, -, -, hdec⟩ :=
      lvlEqC_simTE p hq.closed hL n hS u v hu hv lu lv hdu hdv r1 m1 (callW_of_callE h1)
    have hx : x = none := by
      unfold decLvlEq at hdec; rw [h0] at hdec
      rcases x with _ | _ | _ <;> first | rfl | exact absurd hdec (by decide)
    subst hx
    exact ErrClaim.bind_right hrun (ErrClaim.bind_left (ErrClaim.fail _ _ rfl))
  · rw [lvlEqFueledE.k_lvl_eq_c.arm1 p r1 m1 h0] at hW; cases hW

/-! ## `check_thm_val(vis, c)` -/

/-- **`check_thm_val`'s verdict claim under `StageT`** (`tvW_okT`'s hypotheses): the type not a
proposition and the type mismatch are the twin's `invalid`, the level comparison out of fuel its
`notImplemented` (`lvlEqFueled_errT`); the core stubs and `install_value_guards` by their claims. -/
theorem tvE_okT {p : Prog} (hq : KnotStageProg p) (hV : ValProg p) (hL : LvlCacheProg p)
    (hap : ApdF p) (hkp : CrKeep p) (hcE : CoreStubsE p) (hivE : IvgE p)
    (hnvP : NVAt p "pin_word") (hnvL : NVAt p "lvl_eq_c") (hnvE : NVAt p "env_push")
    {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem} {c : Word}
    {cv : IConstantVal} {v : EIdx} (hS : StageT dn vis fe m a)
    (hcv : decCV (erecP m) (c.toNat + 1) = some cv)
    (hv : hd? (erecP m) (c.toNat + 5) = some v)
    (hpre : ∃ env cP, ConLeche.EnvWF env ∧ ConRon.Bridge.CheckOK V env fe a ∧
      Frontend.denoteCV a.store cv = some cP ∧ ConLeche.Expr.WScoped 0 cP.type)
    (hCr : L.Stubs.CrOK m) {e : Err} (hc : callE p n "check_thm_val" [vis, c] m = .error e) :
    ErrClaim (checkThmVal V fe cv v) a e := by
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (checkThmVal_specE p hV.tv n ⟨m, Locals.init []⟩ vis c) hc
    (Err.code_ne_of_cls hk0)
  obtain ⟨wv, hwv, hwvl, rfl⟩ := hd?_some hv
  obtain ⟨wt, hwt, hwtl, hty⟩ := decCV_typeW hcv
  have hcb : c.toNat + 5 < 2 ^ 64 := erecP_bound hwv hS.stage.2
  have ev : rdW (m.arr64 EREC) (c + 5) = wv :=
    rdW_of_get? (toNat_add_small c 5 (by omega)).symm (erecP_get hwv)
  have et : rdW (m.arr64 EREC) (c + 4) = wt :=
    rdW_of_get? (toNat_add_small c 4 (by omega)).symm (erecP_get (by simpa [Nat.add_assoc] using hwt))
  have hc1 : (c + 1).toNat = c.toNat + 1 := toNat_add_small c 1 (by omega)
  have h00 : (0 : Word).toNat = 0 := rfl
  cases n with
  | zero => rw [checkThmValE.eq_1] at hW; cases hW; exact absurd rfl hk0
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [checkThmValE.arm1, ev, et] at hW
  rw [checkThmVal_eq]
  -- the type's type
  cases h1 : callE p n "infer_type_core" [vis, 0, wt] m with
  | error e1 =>
    rw [h1, checkThmValE.k_infer_type_core.none] at hW; cases hW
    have := hcE.inferTypeCore n hn' hS 0 wt hwtl _ h1
    rw [h00, ← hty] at this
    exact ErrClaim.bind_left this
  | ok q =>
  obtain ⟨r1, m1⟩ := q
  rw [h1, checkThmValE.k_infer_type_core.arm1] at hW
  have h1' := callW_of_callE h1
  have hCr1 := hkp.call (im_mem _ rfl) h1' hCr
  obtain ⟨x1, a1, hrun1, hS1, hg1, hx1l, hx1⟩ := hq.inferTypeCore_sim n hn' hS 0 wt hwtl r1 m1 h1'
  have hrun1' := hrun1
  rw [h00, ← hty] at hrun1'
  refine ErrClaim.bind_right hrun1' ?_
  -- its sort
  cases h2 : callE p n "ensure_sort_core" [vis, 0, r1.headD 0] m1 with
  | error e2 =>
    rw [h2, checkThmValE.k_ensure_sort_core.none] at hW; cases hW
    have := hcE.ensureSortCore n hn' hS1 0 (r1.headD 0) hx1l _ h2
    rw [h00, hx1] at this
    exact ErrClaim.bind_left this
  | ok q =>
  obtain ⟨r2, m2⟩ := q
  rw [h2, checkThmValE.k_ensure_sort_core.arm1] at hW
  have h2' := callW_of_callE h2
  have hCr2 := hkp.call (im_mem _ rfl) h2' hCr1
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2l, hx2⟩ :=
    hq.ensureSortCore_sim n hn' hS1 0 (r1.headD 0) hx1l r2 m2 h2'
  have hrun2' := hrun2
  rw [h00, hx1] at hrun2'
  refine ErrClaim.bind_right hrun2' ?_
  -- the zero level
  cases h3 : callE p n "pin_word" [53] m2 with
  | error e3 =>
    rw [h3, checkThmValE.k_pin_word.none] at hW; cases hW; exact ErrClaim.of_cls0 (hnvP _ _ _ _ h3)
  | ok q =>
  obtain ⟨r3, m3⟩ := q
  rw [h3, checkThmValE.k_pin_word.arm1] at hW
  obtain ⟨s3, hs3, -, hW3⟩ :=
    triple_of_callE (pinWord_specW p hV.cvg.pin n ⟨m2, Locals.init []⟩ 53) h3
  subst hs3
  have hflag : pinW m2 0 ≠ 0 := hS2.flag
  simp only [pinWordW, hflag, ite_false, Option.some.injEq, Prod.mk.injEq] at hW3
  obtain ⟨rfl, hm3⟩ := hW3
  rw [← hm3] at hW
  have hF := hS2.stage.1.pins.full hflag
  have hz : rdW (m2.arr64 PINS) 53 = pinW m2 53 := by simp [rdW, pinW]
  simp only [List.headD_cons, hz] at hW
  refine ErrClaim.bind_right (pinZeroLevel_run hF) ?_
  -- the two levels read back
  obtain ⟨xs, hxs⟩ := ensureSort_view (r := pureFnsA V fe checkFuel) (fe := fe)
    (d := (0 : Word).toNat) (e := decI (r1.headD 0)) hrun2
  obtain ⟨lu, hdu⟩ := hS2.twin.den.sort _ _ hxs
  rw [← hx2] at hdu
  obtain ⟨lz, hdz⟩ := hS2.twin.den.zero
  rw [hF.zeroLevel] at hdz
  -- the comparison
  cases h4 : callE p n "lvl_eq_fueled" [r2.headD 0, pinW m2 53] m2 with
  | error e4 =>
    rw [h4, checkThmValE.k_lvl_eq_fueled.none] at hW; cases hW
    rw [← hx2]
    exact lvlEqFueled_errT hq hL hV.lef hnvL _ hS2 hx2l hF.lv_lt.2.1 lu lz hdu hdz h4
  | ok q =>
  obtain ⟨r4, m4⟩ := q
  rw [h4] at hW
  obtain ⟨s4, hs4, -, hW4⟩ := triple_of_callE
    (lvlEqFueled_specc p hV.lef (realCall p) (realCall_spec p) n ⟨m2, Locals.init []⟩
      (r2.headD 0) (pinW m2 53)) h4
  subst hs4
  have hCr4 := lfW_crOK hkp hW4 hCr2
  obtain ⟨x4, a4, hrun4, hS4, hg4, hx4⟩ :=
    lfW_okTE hq hL hW4 hS2 hx2l hF.lv_lt.2.1 lu lz hdu hdz
  have hrun4' := hrun4
  rw [hx2] at hrun4'
  refine ErrClaim.bind_right hrun4' ?_
  by_cases hb4 : r4.headD 0 = 0
  · -- the type is not a proposition
    rw [checkThmValE.k_lvl_eq_fueled.abort1 p n vis c wv wt r4 _ hb4] at hW
    cases hW
    rw [hx4, hb4]
    exact ErrClaim.bind_right (a₁ := a4) rfl (ErrClaim.bind_left (ErrClaim.fail _ _ rfl))
  rw [checkThmValE.k_lvl_eq_fueled.arm1 p n vis c wv wt r4 _ hb4] at hW
  have ex4 : x4 = some true := by rw [hx4]; simpa using hb4
  rw [ex4]
  refine ErrClaim.bind_right (a₁ := a4) rfl ?_
  show ErrClaim (dvT fe cv (decI wv) (.thmInfo cv) "type mismatch in theorem") a4 e
  unfold dvT
  -- the parameters' names read back at the guards: the prefix extends the store
  have hlps4 : ∃ ks, cv.levelParams.mapM (denoteN a4.store.ns) = some ks := by
    obtain ⟨env, cP, henv, hck, hcvd, hws⟩ := hpre
    obtain ⟨hck2, hx02⟩ := thmPrefix_ext henv hck hcvd hws hrun1' hrun2'
    obtain ⟨-, hst4, -⟩ := ConRon.Bridge.AM.of_run (P := fun t => t = a2) rfl hrun4'
      (ConRon.Bridge.Core.lvlEq?_spec a2 _ _ hck2)
    rw [hst4]
    exact denoteCV_lps (ConRon.Bridge.denoteCV_ext hcvd hx02)
  have hg14 := hg1.trans (hg2.trans hg4)
  have hcv4 : decCV (erA s4.mem) (c + 1).toNat = some cv := by
    rw [hc1]; exact ArrExt.decCV (IWGrow.erecExt hg14) hcv
  -- the value's guards
  cases h5 : callE p n "install_value_guards" [vis, c + 1, wv] s4.mem with
  | error e5 =>
    rw [h5, checkThmValE.k_install_value_guards.none] at hW; cases hW
    exact ErrClaim.bind_left (hivE h5 hS4 hcv4 (by rw [hc1]; omega) hwvl hlps4 hCr4)
  | ok q =>
  obtain ⟨r5, m5⟩ := q
  rw [h5, checkThmValE.k_install_value_guards.arm1] at hW
  obtain ⟨s5, hs5, -, hW5⟩ := triple_of_callE
    (ivg_specW p hV.cvg (realCall p) (realCall_spec p) n ⟨s4.mem, Locals.init []⟩ vis (c + 1) wv) h5
  subst hs5
  obtain ⟨a5, hrun5, hS5, hg5, -⟩ := ivgW_okT hap hkp hW5 hS4 hcv4 (by rw [hc1]; omega) hwvl hlps4 hCr4
  refine ErrClaim.bind_right hrun5 ?_
  -- the value's type
  cases h7 : callE p n "infer_type_core" [vis, 0, wv] s5.mem with
  | error e7 =>
    rw [h7, checkThmValE.k_infer_type_core_2.none] at hW; cases hW
    have := hcE.inferTypeCore n hn' hS5 0 wv hwvl _ h7
    rw [h00] at this
    exact ErrClaim.bind_left this
  | ok q =>
  obtain ⟨r7, m7⟩ := q
  rw [h7, checkThmValE.k_infer_type_core_2.arm1] at hW
  obtain ⟨x7, a7, hrun7, hS7, hg7, hx7l, hx7⟩ :=
    hq.inferTypeCore_sim n hn' hS5 0 wv hwvl r7 m7 (callW_of_callE h7)
  rw [h00] at hrun7
  refine ErrClaim.bind_right hrun7 ?_
  -- the comparison with the declared type
  cases h8 : callE p n "is_def_eq_core" [vis, 0, r7.headD 0, wt] m7 with
  | error e8 =>
    rw [h8, checkThmValE.k_is_def_eq_core.none] at hW; cases hW
    have := hcE.isDefEqCore n hn' hS7 0 (r7.headD 0) wt hx7l hwtl _ h8
    rw [h00, hx7, ← hty] at this
    exact ErrClaim.bind_left this
  | ok q =>
  obtain ⟨r8, m8⟩ := q
  rw [h8] at hW
  obtain ⟨x8, a8, hrun8, hS8, hg8, hx8⟩ :=
    hq.isDefEqCore_sim n hn' hS7 0 (r7.headD 0) wt hx7l hwtl r8 m8 (callW_of_callE h8)
  rw [h00, hx7, ← hty] at hrun8
  refine ErrClaim.bind_right hrun8 ?_
  by_cases hb8 : r8.headD 0 = 0
  · -- the type mismatch
    rw [checkThmValE.k_is_def_eq_core.abort1 p n vis c r8 m8 hb8] at hW
    cases hW
    have ex8 : x8 = false := by rw [← hx8, decBool, hb8]; rfl
    rw [ex8]
    exact ErrClaim.bind_left (ErrClaim.fail _ _ rfl)
  rw [checkThmValE.k_is_def_eq_core.arm1 p n vis c r8 m8 hb8] at hW
  -- the push
  cases h9 : callE p n "env_push" [vis, c] m8 with
  | error e9 =>
    rw [h9, checkThmValE.k_env_push.none] at hW; cases hW; exact ErrClaim.of_cls0 (hnvE _ _ _ _ h9)
  | ok q =>
    obtain ⟨r9, m9⟩ := q
    rw [h9, checkThmValE.k_env_push.arm1] at hW; cases hW

/-! ## `check_value_group(vis, g)` -/

/-- **`check_value_group`'s verdict claim under `StageT`** (`cvgW_okT`'s hypotheses): for a
theorem, the level comparison's decline (`lvl_eq_c` answers `0`: the twin's `liftFueled` on
`none`), the type not a proposition (`1`: `some false`), and the type mismatch (the three kinds'
codes, all the twin's `invalid`); the core stubs and `install_value_guards` by their claims. -/
theorem cvgE_okT {p : Prog} (hq : KnotStageProg p) (hP : CvgProg p) (hL : LvlCacheProg p)
    (hap : ApdF p) (hkp : CrKeep p) (hcE : CoreStubsE p) (hivE : IvgE p)
    (hnvR : NVAt p "iw_reset") (hnvP : NVAt p "pin_word") (hnvL : NVAt p "lvl_eq_c")
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem} {g : Word} {vg : ValueGroup}
    (hS : StageT dn vis fe m a) (hg : decVG (erecP m) g.toNat = some vg) (hCr : L.Stubs.CrOK m)
    (hthm : vg.kind = .thm → ∃ env cP, ConLeche.EnvWF env ∧ ConRon.Bridge.CheckOK V env fe a ∧
      Frontend.denoteCV a.store vg.cv = some cP ∧ ConLeche.Expr.WScoped 0 cP.type)
    {e : Err} (hc : callE p n "check_value_group" [vis, g] m = .error e) :
    ErrClaim (checkValueGroup V fe vg) a e := by
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (checkValueGroup_specE p hP.cvg n ⟨m, Locals.init []⟩ vis g) hc
    (Err.code_ne_of_cls hk0)
  cases n with
  | zero => rw [checkValueGroupE.eq_1] at hW; cases hW; exact absurd rfl hk0
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [checkValueGroupE.arm1] at hW
  -- `iw_reset()`
  cases h0 : callE p n "iw_reset" [] m with
  | error e0 =>
    rw [h0, checkValueGroupE.k_iw_reset.none] at hW; cases hW
    exact ErrClaim.of_cls0 (hnvR _ _ _ _ h0)
  | ok q =>
  obtain ⟨r0, m0⟩ := q
  rw [h0, checkValueGroupE.k_iw_reset.arm1] at hW
  obtain ⟨s0, hs0, -, hW0⟩ := triple_of_callE (iwReset_specW p hP.reset n ⟨m, Locals.init []⟩) h0
  subst hs0
  rw [show iwResetW m = some ([], m.set64 CTL 200 0) from rfl] at hW0
  simp only [Option.some.injEq, Prod.mk.injEq] at hW0
  obtain ⟨-, hm0⟩ := hW0
  have hCr0 : L.Stubs.CrOK s0.mem := by
    rw [← hm0]; exact CrOK.frame hCr (MemFrame.setCtl m 200 0) (by simp) (by decide)
  have hS0 : StageT dn vis fe s0.mem a := by rw [← hm0]; exact iwReset_stageT hS
  have hP0 : erecP s0.mem = erecP m := by rw [← hm0]; exact erecP_reset m
  generalize s0.mem = m0 at hW hCr0 hS0 hP0
  rw [← hP0] at hg
  have hEs := hS0.stage.2.2.2.2.1
  obtain ⟨⟨wk, hwk, hvk⟩, hcv, wj, hwj, hwjl, hjv⟩ := decVG_words hg
  obtain ⟨wt, hwt, hwtl, hty⟩ := decCV_typeW hcv
  have hb5 : g.toNat + 5 < (m0.arr64 EREC).size := by
    have := (Array.getElem?_eq_some_iff.mp (erecP_get hwj)).1; exact this
  have et : rdW (m0.arr64 EREC) (g + 4) = wt :=
    rdW_of_get? (k := g.toNat + 4) (by rw [UInt64.toNat_add]; simp; omega)
      (erecP_get (by simpa [Nat.add_assoc] using hwt))
  have ev : rdW (m0.arr64 EREC) (g + 5) = wj :=
    rdW_of_get? (k := g.toNat + 5) (by rw [UInt64.toNat_add]; simp; omega) (erecP_get hwj)
  rw [et, ev] at hW
  have h00 : (0 : Word).toNat = 0 := rfl
  unfold checkValueGroup
  -- `infer_type_core(vis, 0, t)`
  cases h1 : callE p n "infer_type_core" [vis, 0, wt] m0 with
  | error e1 =>
    rw [h1, checkValueGroupE.k_infer_type_core.none] at hW; cases hW
    have := hcE.inferTypeCore n hn' hS0 0 wt hwtl _ h1
    rw [h00, ← hty] at this
    exact ErrClaim.bind_left this
  | ok q =>
  obtain ⟨r1, m1⟩ := q
  rw [h1, checkValueGroupE.k_infer_type_core.arm1] at hW
  have h1' := callW_of_callE h1
  have hCr1 := hkp.call (im_mem _ rfl) h1' hCr0
  obtain ⟨x1, a1, hrun1, hS1, hg1, hx1l, hx1⟩ := hq.inferTypeCore_sim n hn' hS0 0 wt hwtl r1 m1 h1'
  rw [h00, ← hty] at hrun1
  refine ErrClaim.bind_right hrun1 ?_
  -- `ensure_sort_core(vis, 0, st)`
  cases h2 : callE p n "ensure_sort_core" [vis, 0, r1.headD 0] m1 with
  | error e2 =>
    rw [h2, checkValueGroupE.k_ensure_sort_core.none] at hW; cases hW
    have := hcE.ensureSortCore n hn' hS1 0 (r1.headD 0) hx1l _ h2
    rw [h00, hx1] at this
    exact ErrClaim.bind_left this
  | ok q =>
  obtain ⟨r2, m2⟩ := q
  rw [h2] at hW
  have h2' := callW_of_callE h2
  have hCr2 := hkp.call (im_mem _ rfl) h2' hCr1
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2l, hx2⟩ :=
    hq.ensureSortCore_sim n hn' hS1 0 (r1.headD 0) hx1l r2 m2 h2'
  rw [h00, hx1] at hrun2
  refine ErrClaim.bind_right hrun2 ?_
  have hext2 : ArrExt (erecP m0) (erA m2) := IWGrow.erecExt (hg1.trans hg2)
  have ek : rdW (m2.arr64 EREC) g = wk := rdW_of_get? rfl (hext2 _ _ hwk)
  -- the tail: `infer_type_core(vis, 0, v)`, `is_def_eq_core(vis, 0, vt, t)`, the mismatch
  have tail : ∀ (m5 : Mem) (a5 : AState), StageT dn vis fe m5 a5 →
      checkValueGroupE.j1 p n vis g wt wj m5 = .error e →
      ErrClaim (do
          let vtype ← inferTypeCore V fe checkFuel 0 vg.jv
          let b ← isDefEqCore V fe checkFuel 0 vtype vg.cv.type
          if b = true then pure ()
            else fail (CheckError.invalid (toString "type mismatch in " ++ toString vg.kind.word)) :
          AM Unit) a5 e := by
    intro m5 a5 hS5 hW
    rw [checkValueGroupE.j1.arm1] at hW
    cases h7 : callE p n "infer_type_core" [vis, 0, wj] m5 with
    | error e7 =>
      rw [h7, checkValueGroupE.k_infer_type_core_2.none] at hW; cases hW
      have := hcE.inferTypeCore n hn' hS5 0 wj hwjl _ h7
      rw [h00, ← hjv] at this
      exact ErrClaim.bind_left this
    | ok q =>
    obtain ⟨r7, m7⟩ := q
    rw [h7, checkValueGroupE.k_infer_type_core_2.arm1] at hW
    obtain ⟨x7, a7, hrun7, hS7, -, hx7l, hx7⟩ :=
      hq.inferTypeCore_sim n hn' hS5 0 wj hwjl r7 m7 (callW_of_callE h7)
    rw [h00, ← hjv] at hrun7
    refine ErrClaim.bind_right hrun7 ?_
    cases h8 : callE p n "is_def_eq_core" [vis, 0, r7.headD 0, wt] m7 with
    | error e8 =>
      rw [h8, checkValueGroupE.k_is_def_eq_core.none] at hW; cases hW
      have := hcE.isDefEqCore n hn' hS7 0 (r7.headD 0) wt hx7l hwtl _ h8
      rw [h00, hx7, ← hty] at this
      exact ErrClaim.bind_left this
    | ok q =>
    obtain ⟨r8, m8⟩ := q
    rw [h8] at hW
    obtain ⟨x8, a8, hrun8, -, -, hx8⟩ :=
      hq.isDefEqCore_sim n hn' hS7 0 (r7.headD 0) wt hx7l hwtl r8 m8 (callW_of_callE h8)
    rw [h00, hx7, ← hty] at hrun8
    refine ErrClaim.bind_right hrun8 ?_
    by_cases hb8 : r8.headD 0 = 0
    · have ex8 : x8 = false := by rw [← hx8, decBool, hb8]; rfl
      rw [ex8]
      refine ErrClaim.ite_neg (by decide) (ErrClaim.fail _ _ ?_)
      by_cases k1 : rdW (m8.arr64 EREC) g = 1
      · rw [checkValueGroupE.k_is_def_eq_core.abort1 p g r8 m8 hb8 k1] at hW; cases hW; rfl
      by_cases k2 : rdW (m8.arr64 EREC) g = 2
      · rw [checkValueGroupE.k_is_def_eq_core.abort2 p g r8 m8 hb8 k1 k2] at hW; cases hW; rfl
      · rw [checkValueGroupE.k_is_def_eq_core.abort3 p g r8 m8 hb8 k1 k2] at hW; cases hW; rfl
    · rw [checkValueGroupE.k_is_def_eq_core.arm1 p g r8 m8 hb8] at hW; cases hW
  by_cases hk1 : wk = 1
  · -- a theorem: the proposition test and the value's guards
    subst hk1
    have hkind : vg.kind = .thm := by simpa [decVK] using hvk.symm
    rw [checkValueGroupE.k_ensure_sort_core.arm1 p n vis g wt wj r2 m2 ek] at hW
    have hb : (vg.kind == ValueKind.thm) = true := by rw [hkind]; rfl
    refine ErrClaim.ite_pos hb ?_
    cases h3 : callE p n "pin_word" [53] m2 with
    | error e3 =>
      rw [h3, checkValueGroupE.k_pin_word.none] at hW; cases hW
      exact ErrClaim.of_cls0 (hnvP _ _ _ _ h3)
    | ok q =>
    obtain ⟨r3, m3⟩ := q
    rw [h3, checkValueGroupE.k_pin_word.arm1] at hW
    obtain ⟨s3, hs3, -, hW3⟩ :=
      triple_of_callE (pinWord_specW p hP.pin n ⟨m2, Locals.init []⟩ 53) h3
    subst hs3
    have hflag : pinW m2 0 ≠ 0 := hS2.flag
    simp only [pinWordW, hflag, ite_false, Option.some.injEq, Prod.mk.injEq] at hW3
    obtain ⟨rfl, hm3⟩ := hW3
    rw [← hm3] at hW
    have hF := hS2.stage.1.pins.full hflag
    have hz : rdW (m2.arr64 PINS) 53 = pinW m2 53 := by simp [rdW, pinW]
    simp only [List.headD_cons, hz] at hW
    refine ErrClaim.bind_right (pinZeroLevel_run hF) ?_
    -- the two levels read back: the sort's level, the pinned zero
    obtain ⟨xs, hxs⟩ := ensureSort_view (r := pureFnsA V fe checkFuel) (fe := fe) (d := 0)
      (e := x1) hrun2
    obtain ⟨lu, hdu⟩ := hS2.twin.den.sort _ _ hxs
    rw [← hx2] at hdu
    obtain ⟨lz, hdz⟩ := hS2.twin.den.zero
    rw [hF.zeroLevel] at hdz
    -- `lvl_eq_c(u, zr)`
    cases h4 : callE p n "lvl_eq_c" [r2.headD 0, pinW m2 53] m2 with
    | error e4 =>
      rw [h4, checkValueGroupE.k_lvl_eq_c.none] at hW; cases hW
      exact ErrClaim.of_cls0 (hnvL _ _ _ _ h4)
    | ok q =>
    obtain ⟨r4, m4⟩ := q
    rw [h4] at hW
    have h4' := callW_of_callE h4
    have hCr4 := hkp.call (im_mem _ rfl) h4' hCr2
    obtain ⟨x4, a4, hrun4, hS4, hg4, hdec4⟩ :=
      lvlEqC_simTE p hq.closed hL n hS2 (r2.headD 0) (pinW m2 53) hx2l hF.lv_lt.2.1 lu lz hdu hdz
        r4 m4 h4'
    have hrun4' := hrun4
    rw [hx2] at hrun4'
    refine ErrClaim.bind_right hrun4' ?_
    unfold decLvlEq at hdec4
    by_cases c0 : r4.headD 0 = 0
    · -- out of fuel: the twin's `liftFueled` on `none`
      rw [checkValueGroupE.k_lvl_eq_c.abort1 p n vis g wt wj r4 m4 c0] at hW; cases hW
      have hx : x4 = none := by
        rw [c0] at hdec4
        rcases x4 with _ | _ | _ <;> first | rfl | exact absurd hdec4 (by decide)
      subst hx
      exact ErrClaim.bind_left (ErrClaim.fail _ _ rfl)
    by_cases c1 : r4.headD 0 = 1
    · -- not a proposition
      rw [checkValueGroupE.k_lvl_eq_c.abort2 p n vis g wt wj r4 m4 c0 c1] at hW; cases hW
      have hx : x4 = some false := by
        rw [c1] at hdec4
        rcases x4 with _ | _ | _ <;> first | rfl | exact absurd hdec4 (by decide)
      subst hx
      exact ErrClaim.bind_right (a₁ := a4) rfl
        (ErrClaim.ite_neg (by decide) (ErrClaim.bind_left (ErrClaim.fail _ _ rfl)))
    by_cases c2' : r4.headD 0 ≠ 2
    · rw [checkValueGroupE.k_lvl_eq_c.abort3 p n vis g wt wj r4 m4 c0 c1 c2'] at hW; cases hW
      exact ErrClaim.of_cls0 rfl
    have c2 : r4.headD 0 = 2 := Classical.not_not.mp c2'
    rw [checkValueGroupE.k_lvl_eq_c.arm1 p n vis g wt wj r4 m4 c0 c1 c2] at hW
    have hx : x4 = some true := by
      rw [c2] at hdec4
      rcases x4 with _ | _ | _ <;> first | rfl | exact absurd hdec4 (by decide)
    subst hx
    refine ErrClaim.bind_right (a₁ := a4) rfl (ErrClaim.ite_pos rfl ?_)
    -- the parameters' names read back at the guards: the prefix extends the store
    have hlps4 : ∃ ks, vg.cv.levelParams.mapM (denoteN a4.store.ns) = some ks := by
      obtain ⟨env, cP, henv, hck, hcvd, hws⟩ := hthm hkind
      obtain ⟨hck2, hx02⟩ := thmPrefix_ext henv hck hcvd hws hrun1 hrun2
      obtain ⟨-, hst4, -⟩ := ConRon.Bridge.AM.of_run (P := fun t => t = a2) rfl hrun4'
        (ConRon.Bridge.Core.lvlEq?_spec a2 _ _ hck2)
      rw [hst4]
      exact denoteCV_lps (ConRon.Bridge.denoteCV_ext hcvd hx02)
    have hg1' : (g + 1).toNat = g.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hcv4 : decCV (erA m4) (g + 1).toNat = some vg.cv := by
      rw [hg1']
      exact ArrExt.decCV (IWGrow.erecExt (hg1.trans (hg2.trans hg4))) hcv
    -- `install_value_guards(vis, g + 1, v)`
    cases h5 : callE p n "install_value_guards" [vis, g + 1, wj] m4 with
    | error e5 =>
      rw [h5, checkValueGroupE.k_install_value_guards.none] at hW; cases hW
      rw [hjv]
      exact ErrClaim.bind_left (hivE h5 hS4 hcv4 (by rw [hg1']; omega) hwjl hlps4 hCr4)
    | ok q =>
    obtain ⟨r5, m5⟩ := q
    rw [h5, checkValueGroupE.k_install_value_guards.arm1] at hW
    obtain ⟨s5, hs5, -, hW5⟩ := triple_of_callE
      (ivg_specW p hP (realCall p) (realCall_spec p) n ⟨m4, Locals.init []⟩ vis (g + 1) wj) h5
    subst hs5
    obtain ⟨a5, hrun5, hS5, -, -⟩ :=
      ivgW_okT hap hkp hW5 hS4 hcv4 (by rw [hg1']; omega) hwjl hlps4 hCr4
    rw [← hjv] at hrun5
    exact ErrClaim.bind_right hrun5 (tail _ _ hS5 hW)
  · rw [checkValueGroupE.k_ensure_sort_core.arm2 p n vis g wt wj r2 m2 (by rw [ek]; exact hk1)] at hW
    have hkind : vg.kind ≠ .thm := by
      intro hk; rw [hk] at hvk
      have : wk.toNat = 1 := by
        unfold decVK at hvk; split at hvk <;> simp_all
      exact hk1 (UInt64.toNat_inj.mp (by simpa using this))
    have hb : (vg.kind == ValueKind.thm) = false := by
      revert hkind; cases vg.kind <;> decide
    refine ErrClaim.ite_neg (by rw [hb]; decide) ?_
    exact tail m2 a2 hS2 hW


end L.Arena
