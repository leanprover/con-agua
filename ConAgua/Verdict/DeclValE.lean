import ConAgua.L.ModelGen
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
set_option linter.deprecated false

namespace L.Arena

open L.Ind

l_model lvlEqFueled_specE (p : Prog) (hf : p.lookup "lvl_eq_fueled" = some lvlEqFueled)
  fns [hf ↦ lvlEqFueledE] grind [arena_grind] fold [tierW, idxW]
  extra [evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] finish [tierW, idxW] errors

l_model checkThmVal_specE (p : Prog) (hf : p.lookup "check_thm_val" = some checkThmValL)
  fns [hf ↦ checkThmValE] grind [arena_grind] fold [tierW, idxW]
  extra [evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] heartbeats 400000 simp [] errors

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
  · rw [if_pos h0] at h; exact absurd h (by simp)
  rw [if_neg h0] at h
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

end L.Arena
