import ConAgua.Arena.InferProj2
import ConAgua.Arena.InferLeaves
import ConAgua.Arena.KnotE
import ConAgua.Checker.NoVerdictClosed
import ConAgua.Arena.DefEqStuckCert
import ConAgua.Arena.DefEqStuckShape

/-!
# Error refinements of `infer_const`, `infer_proj` (lane `verdicts-b`, helper `c1`)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

open Lean Elab Command in
elab "#prefixx " id:ident : command => do
  let env ← getEnv
  for (n, ci) in env.constants.map₂.toList do
    if id.getId.isPrefixOf n && !n.isInternal then logInfo m!"{n} : {ci.type}"

namespace L.Arena

l_model inferConst_specE (p : Prog) (hf : p.lookup "infer_const" = some inferConstL)
  fns [hf ↦ inferConstE] grind [arena_grind] fold [tierW, idxW]
  extra [evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] finish [tierW, idxW] errors

#print inferConstE
#prefixx L.Arena.inferConstE

/-! ## `infer_const` -/

/-- The callees of `infer_const`, `infer_proj` outside the verdict closure. -/
theorem inferLeavesE_nv : ∀ f ∈ ["env_find", "pin_at", "ls_node", "const_ty_at", "find_table",
    "find_proj", "get_app_fn", "get_app_args"], f ∈ L.Checker.nvFns := by
  decide +kernel

/-- **`infer_const(vis, n, us)`'s verdicts**: an unknown name rejects, `sorryAx` declines
(`unknownConstError`), a level count mismatch rejects; every callee claims nothing (`nvFns`). -/
theorem inferConst_refinesE (p : Prog) (hp : InferLeafProg p)
    (hnv : closedNV p L.Checker.nvFns = true) (n : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb nm us : Word) (hS : CoreS dn s₀.mem a₀ vis fe M eb) (hnm : HW nm)
    (hus : HW us) :
    CoreSpecE p (n + 1) "infer_const" [vis, nm, us] (inferConstT fe (decI nm) (decI us)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (inferConst_specE p hp.inferConst (n + 1) ⟨s₀.mem, Locals.init []⟩
    vis nm us) hc (Err.code_ne_of_cls hk0)
  simp only [inferConstE] at hW
  cases h1 : callE p n "env_find" [nm, vis] s₀.mem with
  | error e1 =>
    rw [h1, inferConstE.k_env_find.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (inferLeavesE_nv "env_find" (by simp)) h1
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [h1] at hW
  obtain ⟨t₁, ht₁, hm₁, -, hfind⟩ := triple_of_callE
    (envFind_refines p hp.envix hp.envrow hp.envfind n ⟨s₀.mem, Locals.init []⟩ vis nm hS.env hnm) h1
  obtain ⟨-, -, -, -, hfound⟩ := triple_of_callE
    (envFind_found p hp.envix hp.envrow hp.envfind n ⟨s₀.mem, Locals.init []⟩ vis nm hnm) h1
  rw [ht₁] at hm₁
  subst hm₁
  by_cases h0 : r₁.headD 0 = 0
  · -- `unknownConstError`
    have hnone : fe.find? (decI nm) = none := by rw [hfind]; simp only [decFound, h0, if_true]
    rw [inferConstE.k_env_find.arm1 p n nm us r₁ s₀.mem h0] at hW
    cases h2 : callE p n "pin_at" [13] s₀.mem with
    | error e2 =>
      rw [h2, inferConstE.k_pin_at.none] at hW; cases hW
      exact ErrClaim.of_callE_nv hnv (inferLeavesE_nv "pin_at" (by simp)) h2
    | ok q =>
    obtain ⟨r₂, m₂⟩ := q
    rw [h2] at hW
    obtain ⟨t₂, ht₂, hm₂, -, hlt, hpin⟩ := triple_of_callE (s₀ := ⟨s₀.mem, Locals.init []⟩)
      (pinAt_refines p hp.pinAt n ⟨s₀.mem, Locals.init []⟩ a₀ ⟨fun _ => hS.pins⟩ 13) h2
    have hue : (unknownConstError (decI nm)).run a₀ = .ok (if nm = r₂.headD 0 then
        CheckError.notImplemented "use of the sorryAx axiom" else .invalid "unknown constant", a₀) := by
      have hb := decI_beq (k := .name) nm (r₂.headD 0) hnm hlt
      simp only [unknownConstError, pinSorryAx, show PIN_SORRY_AX = (13 : Word).toNat from rfl,
        StateT.run_bind, hpin, except_ok_bind, hb]
      by_cases he : nm = r₂.headD 0
      · simp only [he, ↓reduceIte]; rfl
      · simp only [he, ↓reduceIte]; rfl
    have hT : inferConstT fe (decI nm) (decI us) =
        (unknownConstError (decI nm) >>= fun err => fail err) := by
      simp only [inferConstT, hnone]
    rw [hT]
    refine ErrClaim.bind_right hue ?_
    by_cases he : nm = r₂.headD 0
    · rw [inferConstE.k_pin_at.abort1 p nm r₂ m₂ he] at hW
      cases hW
      rw [if_pos he]; exact ErrClaim.fail _ _ rfl
    · rw [inferConstE.k_pin_at.abort2 p nm r₂ m₂ he] at hW
      cases hW
      rw [if_neg he]; exact ErrClaim.fail _ _ rfl
  · -- found: the level count
    obtain ⟨htag, hrow, hq⟩ := hfound h0
    obtain ⟨ci, hci⟩ := hS.env.found_some nm hnm htag hrow
    have hfind' : fe.find? (decI nm) = some ci := by
      rw [hfind]; simp only [decFound, h0, ↓reduceIte, hq]; exact hci
    rw [← hq] at hci
    have hcv := decCI_cvA hci (erecP_ext _)
    generalize hcvr : ci.toConstantVal = cv at hcv
    rw [inferConstE.k_env_find.arm2 p n nm us r₁ s₀.mem h0] at hW
    cases h2 : callE p n "ls_node" [us] s₀.mem with
    | error e2 =>
      rw [h2, inferConstE.k_ls_node.none] at hW; cases hW
      exact ErrClaim.of_callE_nv hnv (inferLeavesE_nv "ls_node" (by simp)) h2
    | ok q =>
    obtain ⟨r₂, m₂⟩ := q
    rw [h2] at hW
    obtain ⟨t₂, ht₂, rfl, hne', hr₂⟩ := triple_of_callE (s₀ := ⟨s₀.mem, Locals.init []⟩)
      (lsNode_spec p hp.lsNode n _ us) h2
    simp only at ht₂ hne' hr₂
    subst ht₂ hr₂
    by_cases hl : (lsNodeW s₀.mem us).tail.headD 0 ≠ rdW (s₀.mem.arr64 EREC) (r₁.tail.headD 0 + 3)
    · rw [inferConstE.k_ls_node.abort1 p n us _ _ _ hl] at hW
      cases hW
      obtain ⟨-, -, -, -, hsl⟩ := infer_decCV_words hcv hS.erec
      obtain ⟨ids, hv, hlen1, hlen2⟩ := lsNodeW_view hS.arena.1 hus hne'
      have hlen : (ids.length != cv.levelParams.length) = true := by
        rw [hslice?_length hsl, ← hlen2, ← hlen1]
        simp only [bne_iff_ne, ne_eq]
        intro h; exact hl (UInt64.toNat_inj.mp h)
      have hT : inferConstT fe (decI nm) (decI us) =
          (viewLs (decI us) >>= fun usl => if (usl.length != ci.toConstantVal.levelParams.length) = true
            then fail (.invalid "incorrect number of universe levels")
            else constTyAt ci.toConstantVal (decI us)) := by
        simp only [inferConstT, hfind']
      rw [hT, hcvr]
      refine ErrClaim.bind_right (viewLs_run _ _ _ hv) ?_
      rw [if_pos hlen]
      exact ErrClaim.fail _ _ rfl
    · have hl' : (lsNodeW s₀.mem us).tail.headD 0 = rdW (s₀.mem.arr64 EREC) (r₁.tail.headD 0 + 3) := by
        simpa using hl
      rw [inferConstE.k_ls_node.arm1 p n us _ _ _ hl'] at hW
      cases h3 : callE p n "const_ty_at" _ s₀.mem with
      | error e3 =>
        rw [h3, inferConstE.k_const_ty_at.none] at hW; cases hW
        exact ErrClaim.of_callE_nv hnv (inferLeavesE_nv "const_ty_at" (by simp)) h3
      | ok q => rw [h3, inferConstE.k_const_ty_at.arm1] at hW; cases hW

/-! ## `infer_proj`'s error model (by hand: `l_model … errors` times out on it)

The generated text (`trace`), its spec proved by the ok spec's recipe (`inferProj_spec`). -/

theorem ld64_rdW_specE (a : ArrId) (i : Word) (s₀ : St) :
    ⦃fun s => s = s₀⦄ ld64 a i
    ⦃fun r s' => s' = s₀ ∧ r = rdW (s₀.mem.arr64 a) i ∧ i.toNat < (s₀.mem.arr64 a).size;
     fun e => e = .oob⦄ := by
  apply M.triple_of_run'
  · intro s r s' hs hrun
    subst hs
    simp only [ld64, StateT.run_bind, StateT.run_get, pure_bind] at hrun
    split at hrun
    · rename_i h
      simp only [pure] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      exact ⟨rfl, by simp [rdW, h], h⟩
    · simp [throw, throwThe, MonadExceptOf.throw, StateT.run, StateT.lift] at hrun
      cases hrun
  · intro s e hs hrun
    subst hs
    simp only [ld64, StateT.run_bind, StateT.run_get, pure_bind] at hrun
    split at hrun
    · simp [pure, StateT.pure] at hrun
      cases hrun
    · simp [throw, throwThe, MonadExceptOf.throw, StateT.run, StateT.lift] at hrun
      cases hrun; rfl

def inferProjE.j2 : Except Err (Word × Mem) := .error (.abort R_INVALID_PROJECTION_NOT)

def inferProjE.k_env_find_2 (i : Word) : Except Err (List Word × Mem) → Except Err (Word × Mem)
  | .error ε => .error ε
  | .ok (r, m₁) =>
    if r.headD 0 ≠ 0 ∧ rdW (m₁.arr64 EREC) (r.tail.headD 0) = 4 ∧
        i < rdW (m₁.arr64 EREC) (r.tail.headD 0 + 6) then
      .error (.abort R_PROJECTION_ON_AN)
    else inferProjE.j2

def inferProjE.k_env_find (p : Prog) (n : Nat) (vis i tn : Word) :
    Except Err (List Word × Mem) → Except Err (Word × Mem)
  | .error ε => .error ε
  | .ok (r, m₁) =>
    if r.headD 0 ≠ 0 ∧ rdW (m₁.arr64 EREC) (r.tail.headD 0) = 3 ∧
        rdW (m₁.arr64 EREC) (r.tail.headD 0 + 19) = 1 ∧
        rdW (m₁.arr64 EREC) (r.tail.headD 0 + 17) < tn then
      inferProjE.k_env_find_2 i
        (callE p n "env_find" [rdW (m₁.arr64 EREC) (rdW (m₁.arr64 EREC) (r.tail.headD 0 + 18)), vis] m₁)
    else inferProjE.j2

def inferProjE.k_get_app_args (p : Prog) (n : Nat) (vis i cT : Word) :
    Except Err (List Word × Mem) → Except Err (Word × Mem)
  | .error ε => .error ε
  | .ok (r, m₁) => inferProjE.k_env_find p n vis i (r.tail.headD 0) (callE p n "env_find" [cT, vis] m₁)

def inferProjE.k_find_table (p : Prog) (n : Nat) (vis sn i te cT : Word) :
    Except Err (List Word × Mem) → Except Err (Word × Mem)
  | .error ε => .error ε
  | .ok (r, m₁) =>
    if r.headD 0 ≠ 0 then .error (.abort R_PROJECTION_INDEX_OUT)
    else if cT = sn then inferProjE.k_get_app_args p n vis i cT (callE p n "get_app_args" [te] m₁)
    else inferProjE.j2

def inferProjE.k_infer_proj_at : Except Err (List Word × Mem) → Except Err (Word × Mem)
  | .error ε => .error ε
  | .ok (r, m₁) => .ok (r.headD 0, m₁)

def inferProjE.k_find_proj (p : Prog) (n : Nat) (vis sn i pe te cT cu : Word) :
    Except Err (List Word × Mem) → Except Err (Word × Mem)
  | .error ε => .error ε
  | .ok (r, m₁) =>
    if r.headD 0 = 0 then inferProjE.k_find_table p n vis sn i te cT (callE p n "find_table" [vis, cT] m₁)
    else inferProjE.k_infer_proj_at
      (callE p n "infer_proj_at" [vis, sn, i, pe, te, cT, cu, r.tail.headD 0] m₁)

def inferProjE.k_get_app_fn (p : Prog) (n : Nat) (vis sn i pe te : Word) :
    Except Err (List Word × Mem) → Except Err (Word × Mem)
  | .error ε => .error ε
  | .ok (r, m₁) =>
    if r.headD 0 >>> 28 ≠ 3 then .error (.abort R_INVALID_PROJECTION_NOT)
    else if tierW (r.headD 0) ≠ 0 ∧ rdW (m₁.arr64 CTL) 1 = 0 then .error (.abort 0)
    else if tcnt m₁ CONST (tierW (r.headD 0)) ≤ idxW (r.headD 0) then .error (.abort 0)
    else inferProjE.k_find_proj p n vis sn i pe te
      (tfld m₁ CONST (tierW (r.headD 0)) (idxW (r.headD 0)) 0)
      (tfld m₁ CONST (tierW (r.headD 0)) (idxW (r.headD 0)) 1)
      (callE p n "find_proj" [vis, tfld m₁ CONST (tierW (r.headD 0)) (idxW (r.headD 0)) 0, i] m₁)

def inferProjE.k_whnf (p : Prog) (n : Nat) (vis sn i pe : Word) :
    Except Err (List Word × Mem) → Except Err (Word × Mem)
  | .error ε => .error ε
  | .ok (r, m₁) =>
    inferProjE.k_get_app_fn p n vis sn i pe (r.headD 0) (callE p n "get_app_fn" [r.headD 0] m₁)

def inferProjE.k_infer (p : Prog) (n : Nat) (mode vis d sn i pe : Word) :
    Except Err (List Word × Mem) → Except Err (Word × Mem)
  | .error ε => .error ε
  | .ok (r, m₁) => inferProjE.k_whnf p n vis sn i pe (callE p n "whnf" [mode, vis, d, r.headD 0] m₁)

/-- The subject's type at the grade `io` (`infer_io` or `infer`). -/
def inferProjE.first (p : Prog) (n : Nat) (m : Mem) (mode io vis d pe : Word) :
    Except Err (List Word × Mem) :=
  if io ≠ 0 then callE p n "infer_io" [mode, vis, d, pe] m else callE p n "infer" [mode, vis, d, pe] m

/-- **The error model of `infer_proj`** at fuel `n + 1`. -/
def inferProjE (p : Prog) (n : Nat) (m : Mem) (mode io vis d sn i pe : Word) :
    Except Err (Word × Mem) :=
  inferProjE.k_infer p n mode vis d sn i pe (inferProjE.first p n m mode io vis d pe)

set_option maxHeartbeats 2000000 in
theorem inferProj_specE (p : Prog) (hf : p.lookup "infer_proj" = some inferProjL) (n : Nat)
    (s₀ : St) (mode io vis d sn i pe : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "infer_proj" [mode, io, vis, d, sn, i, pe]
    ⦃fun _ _ => True; fun ε => ε.code ≠ 0 → inferProjE p n s₀.mem mode io vis d sn i pe = .error ε⦄ := by
  rw [invoke_eq _ hf]
  simp only [callFn, inferProjL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_specE,
      callE_spec p n "infer_io", callE_spec p n "infer", callE_spec p n "whnf",
      callE_spec p n "get_app_fn", callE_spec p n "find_proj", callE_spec p n "infer_proj_at",
      callE_spec p n "find_table", callE_spec p n "get_app_args", callE_spec p n "env_find",
        evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] <;>
  simp_all [inferProjE, inferProjE.first, inferProjE.k_infer, inferProjE.k_whnf,
    inferProjE.k_get_app_fn, inferProjE.k_find_proj, inferProjE.k_infer_proj_at,
    inferProjE.k_find_table, inferProjE.k_get_app_args, inferProjE.k_env_find,
    inferProjE.k_env_find_2, inferProjE.j2,
    tierW, idxW, Cmp.eval, LocEq, BinOp.eval,
    St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr,
    Locals.init_cons_zero, Locals.init_cons_succ, CTL, CREC, w_lt_false, w_le_false, tfld, tcnt]

/-! ## `infer_proj`: the twin's failures, the records' words -/

theorem ErrClaim.of_error {α : Type} {T : AM α} {a : AState} {e : Err} {ce : CheckError}
    (h : T.run a = .error ce) (hk : e.cls = twinCls ce) : ErrClaim T a e :=
  fun _ => ⟨ce, h, hk.symm⟩

/-- **`getAppArgs` runs where `getAppFn` ran** (the same walk at the same fuel). -/
theorem getAppArgs_of_getAppFn : ∀ (fuel : Nat) (h : EIdx) (a : AState) (hh : EIdx) (a' : AState),
    (getAppFn fuel h).run a = .ok (hh, a') → ∃ xs, (getAppArgs fuel h).run a = .ok (xs, a)
  | 0, h, a, hh, a', hr => by simp [getAppFn, ConRon.Arena.fail] at hr; cases hr
  | fuel + 1, h, a, hh, a', hr => by
    by_cases ht : (h.tag == ETag.app) = true
    · cases hv : a.store.viewApp h with
      | none =>
        simp [getAppFn, ht, viewApp, hv, StateT.run_bind, failDanglingE, ConRon.Arena.fail] at hr
        cases hr
      | some fx =>
        obtain ⟨f, x⟩ := fx
        have hr' : (getAppFn fuel f).run a = .ok (hh, a') := by
          simpa [getAppFn, ht, viewApp, hv, StateT.run_bind] using hr
        obtain ⟨xs, hxs⟩ := getAppArgs_of_getAppFn fuel f a hh a' hr'
        refine ⟨xs ++ [x], ?_⟩
        simp [getAppArgs, ht, viewApp, hv, StateT.run_bind, hxs]; rfl
    · refine ⟨[], ?_⟩
      simp [getAppArgs, ht]; rfl

theorem inferProj_notConst (r : CoreFnsA) (fe : IFEnv) (d : Nat) (sn : NIdx) (i : Nat) (pe : EIdx)
    (a a₁ a₂ : AState) (it te hh : EIdx)
    (h1 : (r.infer d pe).run a = .ok (it, a₁)) (h2 : (r.whnf d it).run a₁ = .ok (te, a₂))
    (h3 : (getAppFn coreWalkFuel te).run a₂ = .ok (hh, a₂)) (ht : (hh.tag == ETag.const) = false) :
    (inferProj r fe d sn i pe).run a =
      .error (.invalid "invalid projection: not a structure-like type, or no such field") := by
  simp only [inferProj, StateT.run_bind, h1, except_ok_bind, h2, h3, ht]
  rfl

theorem inferProj_miss (r : CoreFnsA) (fe : IFEnv) (d : Nat) (sn : NIdx) (i : Nat) (pe : EIdx)
    (a a₁ a₂ : AState) (it te hh : EIdx) (T : NIdx) (us : LsIdx) (xs : List EIdx)
    (h1 : (r.infer d pe).run a = .ok (it, a₁)) (h2 : (r.whnf d it).run a₁ = .ok (te, a₂))
    (h3 : (getAppFn coreWalkFuel te).run a₂ = .ok (hh, a₂)) (ht : (hh.tag == ETag.const) = true)
    (hv : a₂.store.view hh = some (.const T us)) (h4 : fe.findProj? T i = none)
    (h5 : (getAppArgs coreWalkFuel te).run a₂ = .ok (xs, a₂)) :
    (inferProj r fe d sn i pe).run a =
      .error (projMissError fe (fe.findTable? T).isSome T sn i xs.length) := by
  simp only [inferProj, StateT.run_bind, h1, except_ok_bind, h2, h3, ht, if_true,
    view_run _ _ _ hv, h4, h5]
  rfl

theorem rdW_ext' {a b : Array Word} (hab : ArrExt a b) (hsz : b.size < 2 ^ 63) {q : Word} {k : Nat}
    (hk : k < 64) {w : Word} (ha : a[q.toNat + k]? = some w) : rdW b (q + UInt64.ofNat k) = w := by
  have hb := hab _ _ ha
  have hlt : q.toNat + k < b.size := by
    rcases Nat.lt_or_ge (q.toNat + k) b.size with h' | h'
    · exact h'
    · simp [Array.getElem?_eq_none h'] at hb
  have : (q + UInt64.ofNat k).toNat = q.toNat + k := by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat']; rw [Nat.mod_eq_of_lt (a := k) (by omega)]; omega
  simp only [rdW, this, hb, Option.getD_some]

/-- **An inductive record's parameter count and constructors**: `nparams` at `q + 17`, the
constructor slice at `q + 18`, `q + 19`. -/
theorem decCI_indNC {a b : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Word}
    {cv : IConstantVal} {caps : IIndCaps} (h : decCI a dn q.toNat = some (.indInfo cv caps))
    (hab : ArrExt a b) (hsz : b.size < 2 ^ 63) :
    caps.nparams = (rdW b (q + 17)).toNat ∧ caps.ctors.length = (rdW b (q + 19)).toNat ∧
    ∀ c, caps.ctors = [c] → c = decI (rdW b (rdW b (q + 18))) ∧ HW (rdW b (rdW b (q + 18))) := by
  cases hq : a[q.toNat]? with
  | none => simp [decCI, nat?, hq] at h
  | some w =>
  simp only [decCI, nat?, hq, Option.map_some, Option.bind_eq_bind, Option.bind_some] at h
  rcases hk : w.toNat with _ | _ | _ | _ | _ | _ | _ | k
  all_goals (rw [hk] at h)
  all_goals simp only [Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq, false_and,
    and_false, exists_false, Option.pure_def] at h
  obtain ⟨cv', -, caps', hcaps, hc⟩ := h
  cases hc
  simp only [decCaps, bool?, hd?, nat?, hlist?, Option.bind_eq_bind, Option.pure_def,
    Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.some.injEq] at hcaps
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, np, ⟨wnp, hwnp, rfl⟩, cs,
    ⟨o, ⟨wo, hwo, rfl⟩, c, ⟨wc, hwc, rfl⟩, hs⟩, rfl⟩ := hcaps
  have h17 : rdW b (q + 17) = wnp := rdW_ext' hab hsz (k := 17) (by decide) (by simpa [Nat.add_assoc] using hwnp)
  have h18 : rdW b (q + 18) = wo := rdW_ext' hab hsz (k := 18) (by decide) (by simpa [Nat.add_assoc] using hwo)
  have h19 : rdW b (q + 19) = wc := rdW_ext' hab hsz (k := 19) (by decide) (by simpa [Nat.add_assoc] using hwc)
  refine ⟨by rw [h17], by rw [h19, hslice?_length hs], ?_⟩
  intro c' hc'
  simp only at hc'
  subst hc'
  have h1 : wc.toNat = 1 := by have := hslice?_length hs; simp at this; omega
  rw [h1] at hs
  simp only [hslice?, List.range_one, List.mapM_cons, List.mapM_nil, hd?, Option.bind_eq_bind,
    Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq, Nat.add_zero] at hs
  obtain ⟨x, ⟨w', hw', hx⟩, _, rfl, hxs⟩ := hs
  simp only [List.cons.injEq, and_true] at hxs
  subst hxs
  have hrd : rdW b wo = w' := by simp only [rdW, hab _ _ hw', Option.getD_some]
  rw [h18, hrd]
  split at hx
  · rename_i hlt
    cases hx
    exact ⟨rfl, hlt⟩
  · cases hx

/-- **An ok `env_find` run**: the memory unchanged, the twin's `find?` decoded, a found record
decodes. -/
theorem envFind_callE {p : Prog} (hx : p.lookup "env_ix" = some envIxL)
    (hg : p.lookup "env_row_get" = some envRowGetL) (hp : p.lookup "env_find" = some envFindL)
    {n : Nat} {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {vis : Word} {fe : IFEnv} {w : Word}
    (hE : EnvR dn m vis fe) (hw : HW w) {r : List Word}
    (hc : callE p n "env_find" [w, vis] m = .ok (r, m')) :
    m' = m ∧ fe.find? (decI w) = decFound dn m (r.headD 0) (r.tail.headD 0) ∧
      (r.headD 0 ≠ 0 → ∃ ci, decCI (erecP m) dn (r.tail.headD 0).toNat = some ci) := by
  obtain ⟨t₁, ht₁, hm₁, -, hfind⟩ := triple_of_callE
    (envFind_refines p hx hg hp n ⟨m, Locals.init []⟩ vis w hE hw) hc
  obtain ⟨t₂, ht₂, -, -, hfound⟩ := triple_of_callE
    (envFind_found p hx hg hp n ⟨m, Locals.init []⟩ vis w hw) hc
  refine ⟨ht₁ ▸ hm₁, hfind, fun h0 => ?_⟩
  obtain ⟨htag, hrow, hq⟩ := hfound h0
  rw [hq]
  exact hE.found_some w hw htag hrow

/-- The constructor test of `projIndexedStructLike`: `c` a constructor with more than `i` fields. -/
def ctorFieldsGt (fe : IFEnv) (c : NIdx) (i : Nat) : Bool :=
  match fe.find? c with
  | some (.ctorInfo _ _ nF) => decide (i < nF)
  | _ => false

/-- **`projIndexedStructLike` at `T = sn` from `env_find(T)`'s record**: the L test `f ≠ 0`, kind
`3`, one constructor, fewer parameters than arguments; then the constructor test. -/
theorem pisl_first {fe : IFEnv} {dn : NIdx → Option ConLeche.Name} {m : Mem} {T : NIdx}
    {f q tn : Word} {i : Nat} (hsz : (m.arr64 EREC).size < 2 ^ 63)
    (hf : fe.find? T = decFound dn m f q)
    (hs : f ≠ 0 → ∃ ci, decCI (erecP m) dn q.toNat = some ci) :
    (¬ (f ≠ 0 ∧ rdW (m.arr64 EREC) q = 3 ∧ rdW (m.arr64 EREC) (q + 19) = 1 ∧
        rdW (m.arr64 EREC) (q + 17) < tn) →
      projIndexedStructLike fe T T i tn.toNat = false) ∧
    ((f ≠ 0 ∧ rdW (m.arr64 EREC) q = 3 ∧ rdW (m.arr64 EREC) (q + 19) = 1 ∧
        rdW (m.arr64 EREC) (q + 17) < tn) →
      HW (rdW (m.arr64 EREC) (rdW (m.arr64 EREC) (q + 18))) ∧
      projIndexedStructLike fe T T i tn.toNat =
        ctorFieldsGt fe (decI (rdW (m.arr64 EREC) (rdW (m.arr64 EREC) (q + 18)))) i) := by
  by_cases f0 : f = 0
  · have hn : fe.find? T = none := by rw [hf]; simp [decFound, f0]
    refine ⟨fun _ => ?_, fun h => absurd h.1 (by simpa using f0)⟩
    simp [projIndexedStructLike, hn]
  obtain ⟨ci, hci⟩ := hs f0
  have hfind : fe.find? T = some ci := by rw [hf]; simp only [decFound, f0, ↓reduceIte]; exact hci
  have hK := decCI_indK hci (erecP_ext m) hsz
  by_cases h3 : rdW (m.arr64 EREC) q = 3
  · obtain ⟨cv, caps, rfl⟩ := hK.1 h3
    obtain ⟨hnp, hlen, hc⟩ := decCI_indNC hci (erecP_ext m) hsz
    by_cases h19 : rdW (m.arr64 EREC) (q + 19) = 1
    · have hl1 : caps.ctors.length = 1 := by rw [hlen, h19]; rfl
      obtain ⟨c, hc1⟩ := List.length_eq_one_iff.mp hl1
      obtain ⟨hcw, hhw⟩ := hc c hc1
      by_cases h17 : rdW (m.arr64 EREC) (q + 17) < tn
      · refine ⟨fun h => absurd ⟨f0, h3, h19, h17⟩ h, fun _ => ⟨hhw, ?_⟩⟩
        have hlt : caps.nparams < tn.toNat := by rw [hnp]; exact UInt64.lt_iff_toNat_lt.mp h17
        simp only [projIndexedStructLike, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hfind,
          hc1, hlt, ← hcw, ctorFieldsGt]
        rcases fe.find? c with _ | ci
        · rfl
        · cases ci <;> rfl
      · refine ⟨fun _ => ?_, fun h => absurd h.2.2.2 h17⟩
        have hlt : ¬ caps.nparams < tn.toNat := by
          rw [hnp]; exact fun h => h17 (UInt64.lt_iff_toNat_lt.mpr h)
        simp only [projIndexedStructLike, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hfind,
          hc1, hlt]
    · refine ⟨fun _ => ?_, fun h => absurd h.2.2.1 h19⟩
      have hl1 : caps.ctors.length ≠ 1 := by
        rw [hlen]; exact fun h => h19 (UInt64.toNat_inj.mp (by rw [h]; rfl))
      simp only [projIndexedStructLike, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hfind]
      split
      · rename_i c hc'; rw [hc'] at hl1; simp at hl1
      · rfl
  · refine ⟨fun _ => ?_, fun h => absurd h.2.1 h3⟩
    have hni := hK.2 h3
    simp only [projIndexedStructLike, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hfind]
    split
    · rename_i cv caps hci'; cases hci'; exact absurd rfl (hni cv caps)
    · rfl

/-- **The constructor test from `env_find(c)`'s record**: `f ≠ 0`, kind `4`, `i` below the field
count at `q + 6`. -/
theorem ctorFieldsGt_eq {fe : IFEnv} {dn : NIdx → Option ConLeche.Name} {m : Mem} {c : NIdx}
    {f q iw : Word} (hsz : (m.arr64 EREC).size < 2 ^ 63)
    (hf : fe.find? c = decFound dn m f q)
    (hs : f ≠ 0 → ∃ ci, decCI (erecP m) dn q.toNat = some ci) :
    ctorFieldsGt fe c iw.toNat = decide (f ≠ 0 ∧ rdW (m.arr64 EREC) q = 4 ∧
      iw < rdW (m.arr64 EREC) (q + 6)) := by
  by_cases f0 : f = 0
  · have hn : fe.find? c = none := by rw [hf]; simp [decFound, f0]
    simp [ctorFieldsGt, hn, f0]
  obtain ⟨ci, hci⟩ := hs f0
  have hfind : fe.find? c = some ci := by rw [hf]; simp only [decFound, f0, ↓reduceIte]; exact hci
  have hK := decCI_ctorF hci (erecP_ext m) hsz
  by_cases h4 : rdW (m.arr64 EREC) q = 4
  · obtain ⟨cv, rfl⟩ := hK.1 h4
    simp only [ctorFieldsGt, hfind, f0, h4, ne_eq, not_false_eq_true, true_and, decide_eq_decide]
    exact UInt64.lt_iff_toNat_lt.symm
  · have hni := hK.2 h4
    have : ctorFieldsGt fe c iw.toNat = false := by
      simp only [ctorFieldsGt, hfind]
      split
      · rename_i cv np nf hci'; cases hci'; exact absurd rfl (hni cv np nf)
      · rfl
    rw [this]; simp [h4]

theorem ErrClaim.of_run_eq' {α β : Type} {T : AM α} {T' : AM β} {a a' : AState} {e : Err}
    (h : ∀ ce, T'.run a' = .error ce → T.run a = .error ce) (h' : ErrClaim T' a' e) :
    ErrClaim T a e := fun hk => by
  obtain ⟨ce, hce, hc⟩ := h' hk
  exact ⟨ce, h ce hce, hc⟩

theorem inferProj_err1 (r : CoreFnsA) (fe : IFEnv) (d : Nat) (sn : NIdx) (i : Nat) (pe : EIdx)
    (a : AState) (ce : CheckError) (h1 : (r.infer d pe).run a = .error ce) :
    (inferProj r fe d sn i pe).run a = .error ce := by
  simp only [inferProj, StateT.run_bind, h1]; rfl

theorem inferProj_err2 (r : CoreFnsA) (fe : IFEnv) (d : Nat) (sn : NIdx) (i : Nat) (pe : EIdx)
    (a a₁ : AState) (it : EIdx) (ce : CheckError) (h1 : (r.infer d pe).run a = .ok (it, a₁))
    (h2 : (r.whnf d it).run a₁ = .error ce) :
    (inferProj r fe d sn i pe).run a = .error ce := by
  simp only [inferProj, StateT.run_bind, h1, except_ok_bind, h2]; rfl

/-- `infer_proj_at`'s error claim, under `inferProjAt_refines`'s hypotheses. -/
def InferProjAtE (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb sn i pe te T us q : Word) (tbl : IProjTable),
    CoreS dn s₀.mem a₀ vis fe M eb → decTbl (s₀.mem.arr64 EREC) q.toNat = some tbl →
    (∃ c, fe.findTable? c = some tbl) → i.toNat < tbl.numFields → HW us → HW te → HW pe →
    (∃ ls, denoteLs a₀.store.lss (decI us) = some ls) →
    CoreSpecE p (n + 1) "infer_proj_at" [vis, sn, i, pe, te, T, us, q]
      (projAtT (decI sn) (decI T) (decI us) (tbl.entry i.toNat) (decE te) (decE pe)) s₀ a₀

/-- What `infer_proj`'s error refinement needs of the program beyond `InferProjProg`. -/
structure InferProjEProg (p : Prog) : Prop where
  nv : closedNV p L.Checker.nvFns = true
  tblix : p.lookup "tbl_ix" = some tblIxL
  tblrow : p.lookup "tbl_row_get" = some tblRowGetL
  findTable : p.lookup "find_table" = some findTableL

/-- **`infer_proj`'s verdicts at the grade `io`**, at the record `R` (as `inferProj_grade`): the
subject's type's errors (`hIE`, `whnf`'s slot), a head that is no constant rejects, a miss is
`projMissError`'s verdict (out of range / indexed structure-like decline / reject), a hit is
`infer_proj_at`'s. -/
theorem inferProj_gradeE (p : Prog) (hp : InferProjProg p) (hc : InferProjCallees p)
    (he : InferProjEProg p) (hat : InferProjAtE p) (n : Nat) (hk : KnotUpTo p n)
    (hkE : KnotUpToE p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode io d sn i pe : Word) (R : CoreFnsA)
    (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hsn : HW sn)
    (hpe : HW pe)
    (hWh : R.whnf = (coreKnot (decMode mode) fe id F).whnf)
    (hI : ∀ (r : List Word) (m : Mem), inferProjE.first p n s₀.mem mode io vis d pe = .ok (r, m) →
      CoreRef (R.infer d.toNat (decE pe)) a₀ decH dn s₀.mem vis fe M eb r m)
    (hIE : ∀ e, inferProjE.first p n s₀.mem mode io vis d pe = .error e →
      ErrClaim (R.infer d.toNat (decE pe)) a₀ e) :
    CoreSpecE p (n + 1) "infer_proj" [mode, io, vis, d, sn, i, pe]
      (inferProj R fe d.toNat (decI sn) i.toNat (decE pe)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hcall => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (inferProj_specE p hp.ip n ⟨s₀.mem, Locals.init []⟩ mode io vis d
    sn i pe) hcall (Err.code_ne_of_cls hk0)
  simp only [inferProjE] at hW
  have hK := hk n (Nat.le_refl _)
  have hKE := hkE n (Nat.le_refl _)
  have nvE : ∀ (f : FnName), f ∈ ["env_find", "pin_at", "ls_node", "const_ty_at", "find_table",
      "find_proj", "get_app_fn", "get_app_args"] → ∀ {vs : List Word} {m : Mem} {e : Err},
      callE p n f vs m = .error e → e = er → ErrClaim (inferProj R fe d.toNat (decI sn) i.toNat (decE pe)) a₀ er :=
    fun f hf _ _ _ h hee => hee ▸ ErrClaim.of_callE_nv he.nv (inferLeavesE_nv f hf) h
  -- the subject's type
  cases hc1 : inferProjE.first p n s₀.mem mode io vis d pe with
  | error e1 =>
    rw [hc1] at hW; simp only [inferProjE.k_infer] at hW; cases hW
    exact ErrClaim.of_run_eq' (fun ce h => inferProj_err1 _ _ _ _ _ _ _ ce h) (hIE _ hc1)
  | ok q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [hc1] at hW; simp only [inferProjE.k_infer] at hW
  have h₁ := hI r₁ m₁ hc1
  have hrun1 := ipRun_of_ref h₁
  obtain ⟨-, ⟨M₁, hS₁, hK₁, hSt₁⟩, -, hrw1⟩ := h₁
  -- `whnf`
  cases hc2 : callE p n "whnf" [mode, vis, d, r₁.headD 0] m₁ with
  | error e2 =>
    rw [hc2] at hW; simp only [inferProjE.k_whnf] at hW; cases hW
    have hE2 := CoreSpecE.of_callE (hKE.whnf F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d
      (r₁.headD 0) hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ hrw1) hc2
    rw [← hWh] at hE2
    exact ErrClaim.of_run_eq' (fun ce h => inferProj_err2 _ _ _ _ _ _ _ _ _ ce hrun1 h) hE2
  | ok q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  rw [hc2] at hW; simp only [inferProjE.k_whnf] at hW
  have h₂ := CoreSpec.of_callW (hK.whnf F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d (r₁.headD 0)
    hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ hrw1) (callW_of_callE hc2)
  rw [← hWh] at h₂
  have hrun2 := ipRun_of_ref h₂
  obtain ⟨-, ⟨M₂, hS₂, hK₂, hSt₂⟩, -, hrw2⟩ := h₂
  -- `get_app_fn`
  cases hc3 : callE p n "get_app_fn" [r₂.headD 0] m₂ with
  | error e3 =>
    rw [hc3] at hW; simp only [inferProjE.k_get_app_fn] at hW; cases hW
    exact nvE "get_app_fn" (by simp) hc3 rfl
  | ok q₃ =>
  obtain ⟨r₃, m₃⟩ := q₃
  rw [hc3] at hW; simp only [inferProjE.k_get_app_fn] at hW
  obtain ⟨rfl, hhw, hgaf⟩ := getAppFn_callW hp.leaf hS₂.arena.1 hrw2 (callW_of_callE hc3)
  by_cases g1 : r₃.headD 0 >>> 28 ≠ 3
  · rw [if_pos g1] at hW; cases hW
    have ht : ((decE (r₃.headD 0)).tag == ETag.const) = false := by
      rw [decE_const_tag _ hhw]; simpa using g1
    exact ErrClaim.of_error (inferProj_notConst _ _ _ _ _ _ _ _ _ _ _ _ hrun1 hrun2 hgaf ht) rfl
  rw [if_neg g1] at hW
  have g1' : r₃.headD 0 >>> 28 = 3 := Classical.not_not.mp g1
  have ht : ((decE (r₃.headD 0)).tag == ETag.const) = true := by
    rw [decE_const_tag _ hhw]; simpa using g1'
  by_cases g2 : tierW (r₃.headD 0) ≠ 0 ∧ rdW (m₃.arr64 CTL) 1 = 0
  · rw [if_pos g2] at hW; cases hW; exact ErrClaim.of_cls0 rfl
  rw [if_neg g2] at hW
  by_cases g3 : tcnt m₃ CONST (tierW (r₃.headD 0)) ≤ idxW (r₃.headD 0)
  · rw [if_pos g3] at hW; cases hW; exact ErrClaim.of_cls0 rfl
  rw [if_neg g3] at hW
  have hvOK : viewOK m₃ (r₃.headD 0) CONST := ⟨g2, by simpa using g3⟩
  obtain ⟨cT, cu, hv, hcT, hcu, hcTw, hcuw⟩ :=
    view_const_words m₃ _ hS₂.arena.1 (r₃.headD 0) hhw hvOK g1'
  generalize tfld m₃ CONST (tierW (r₃.headD 0)) (idxW (r₃.headD 0)) 0 = wT at hcT hcTw hW
  generalize tfld m₃ CONST (tierW (r₃.headD 0)) (idxW (r₃.headD 0)) 1 = wu at hcu hcuw hW
  subst hcT hcu
  obtain ⟨lsu, hdu⟩ := (hc.den dn m₃ _ vis fe M₂ eb hS₂).constLs _ _ _ hv
  -- `find_proj`
  cases hc4 : callE p n "find_proj" [vis, wT, i] m₃ with
  | error e4 =>
    rw [hc4] at hW; simp only [inferProjE.k_find_proj] at hW; cases hW
    exact nvE "find_proj" (by simp) hc4 rfl
  | ok q₄ =>
  obtain ⟨r₄, m₄⟩ := q₄
  rw [hc4] at hW; simp only [inferProjE.k_find_proj] at hW
  have h₄ := CoreSpec.of_callW (hc.findProj n ⟨m₃, Locals.init []⟩ _ dn vis fe M₂ eb wT i hS₂ hcTw)
    (callW_of_callE hc4)
  have hrun4 : fe.findProj? (decI wT) i.toNat =
      decEntry (m₃.arr64 EREC) (r₄.headD 0) (r₄.tail.headD 0) i.toNat := h₄.2.2.1
  obtain ⟨-, ⟨M₄, hS₄, hK₄, hSt₄⟩, -, -⟩ := h₄
  have hE₄ : m₄.arr64 EREC = m₃.arr64 EREC :=
    hc.erec n "find_proj" _ m₃ r₄ m₄ (Or.inl rfl) (callW_of_callE hc4)
  by_cases g4 : r₄.headD 0 = 0
  · -- a miss: `projMissError`
    rw [if_pos g4] at hW
    have hnone : fe.findProj? (decI wT) i.toNat = none := by
      rw [hrun4]; simp only [decEntry, g4, ↓reduceIte]
    obtain ⟨xs, hxs⟩ := getAppArgs_of_getAppFn _ _ _ _ _ hgaf
    have hT := inferProj_miss R fe d.toNat (decI sn) i.toNat (decE pe) a₀ _ _ _ _ _ _ _ xs hrun1
      hrun2 hgaf ht hv hnone hxs
    cases hc5 : callE p n "find_table" [vis, wT] m₄ with
    | error e5 =>
      rw [hc5] at hW; simp only [inferProjE.k_find_table] at hW; cases hW
      exact nvE "find_table" (by simp) hc5 rfl
    | ok q₅ =>
    obtain ⟨r₅, m₅⟩ := q₅
    rw [hc5] at hW; simp only [inferProjE.k_find_table] at hW
    obtain ⟨t₅, ht₅, hm₅, -, htbl, hsome⟩ := triple_of_callE (findTable_refines p hp.leaf.core.envix
      hp.leaf.core.envrow he.tblix he.tblrow he.findTable n ⟨m₄, Locals.init []⟩ vis wT hS₄.env hcTw) hc5
    have hm5 : m₅ = m₄ := ht₅ ▸ hm₅
    subst hm5
    by_cases g5 : r₅.headD 0 ≠ 0
    · rw [if_pos g5] at hW; cases hW
      have hts : (fe.findTable? (decI wT)).isSome = true := by rw [htbl]; exact hsome g5
      exact ErrClaim.of_error hT (by rw [hts]; rfl)
    rw [if_neg g5] at hW
    have hts : (fe.findTable? (decI wT)).isSome = false := by
      rw [htbl]; simp only [tblOut, Classical.not_not.mp g5, ↓reduceIte, Option.isSome_none]
    by_cases g6 : wT = sn
    · subst g6
      rw [if_pos rfl] at hW
      cases hc6 : callE p n "get_app_args" [r₂.headD 0] m₅ with
      | error e6 =>
        rw [hc6] at hW; simp only [inferProjE.k_get_app_args] at hW; cases hW
        exact nvE "get_app_args" (by simp) hc6 rfl
      | ok q₆ =>
      obtain ⟨r₆, m₆⟩ := q₆
      rw [hc6] at hW; simp only [inferProjE.k_get_app_args] at hW
      obtain ⟨hf6, -, -, -, xs', hxs', hsp⟩ :=
        getAppArgs_callW hp.leaf.core.spine hS₄ hrw2 (callW_of_callE hc6)
      have hxx : xs' = xs := by
        have := hxs'.symm.trans hxs
        simp only [Except.ok.injEq, Prod.mk.injEq] at this
        exact this.1
      subst hxx
      have hlen : xs'.length = (r₆.tail.headD 0).toNat := by
        have := hsp.size; simpa using this
      have hS₆ := hS₄.frame_stk hf6 (by simp) (by simp)
      cases hc7 : callE p n "env_find" [wT, vis] m₆ with
      | error e7 =>
        rw [hc7] at hW; simp only [inferProjE.k_env_find] at hW; cases hW
        exact nvE "env_find" (by simp) hc7 rfl
      | ok q₇ =>
      obtain ⟨r₇, m₇⟩ := q₇
      rw [hc7] at hW; simp only [inferProjE.k_env_find] at hW
      obtain ⟨rfl, hfind7, hfound7⟩ := envFind_callE hp.leaf.core.envix hp.leaf.core.envrow
        hp.leaf.core.envfind hS₆.env hcTw hc7
      have hP := pisl_first (i := i.toNat) (tn := r₆.tail.headD 0) hS₆.erec hfind7 hfound7
      by_cases C1 : r₇.headD 0 ≠ 0 ∧ rdW (m₇.arr64 EREC) (r₇.tail.headD 0) = 3 ∧
          rdW (m₇.arr64 EREC) (r₇.tail.headD 0 + 19) = 1 ∧
          rdW (m₇.arr64 EREC) (r₇.tail.headD 0 + 17) < r₆.tail.headD 0
      · rw [if_pos C1] at hW
        obtain ⟨hwc, hpe1⟩ := hP.2 C1
        cases hc8 : callE p n "env_find"
            [rdW (m₇.arr64 EREC) (rdW (m₇.arr64 EREC) (r₇.tail.headD 0 + 18)), vis] m₇ with
        | error e8 =>
          rw [hc8] at hW; simp only [inferProjE.k_env_find_2] at hW; cases hW
          exact nvE "env_find" (by simp) hc8 rfl
        | ok q₈ =>
        obtain ⟨r₈, m₈⟩ := q₈
        rw [hc8] at hW; simp only [inferProjE.k_env_find_2] at hW
        obtain ⟨rfl, hfind8, hfound8⟩ := envFind_callE hp.leaf.core.envix hp.leaf.core.envrow
          hp.leaf.core.envfind hS₆.env hwc hc8
        have hcf := ctorFieldsGt_eq (iw := i) hS₆.erec hfind8 hfound8
        by_cases C2 : r₈.headD 0 ≠ 0 ∧ rdW (m₈.arr64 EREC) (r₈.tail.headD 0) = 4 ∧
            i < rdW (m₈.arr64 EREC) (r₈.tail.headD 0 + 6)
        · rw [if_pos C2] at hW; cases hW
          have hpt : projIndexedStructLike fe (decI wT) (decI wT) i.toNat xs'.length = true := by
            rw [hlen, hpe1, hcf]; simpa using C2
          exact ErrClaim.of_error hT (by
            rw [hts]; simp only [projMissError, Bool.false_eq_true, ↓reduceIte, hpt]; rfl)
        · rw [if_neg C2] at hW; simp only [inferProjE.j2] at hW; cases hW
          have hpt : projIndexedStructLike fe (decI wT) (decI wT) i.toNat xs'.length = false := by
            rw [hlen, hpe1, hcf]; simpa using C2
          exact ErrClaim.of_error hT (by
            rw [hts]; simp only [projMissError, Bool.false_eq_true, ↓reduceIte, hpt]; rfl)
      · rw [if_neg C1] at hW; simp only [inferProjE.j2] at hW; cases hW
        have hpt : projIndexedStructLike fe (decI wT) (decI wT) i.toNat xs'.length = false := by
          rw [hlen]; exact hP.1 C1
        exact ErrClaim.of_error hT (by
            rw [hts]; simp only [projMissError, Bool.false_eq_true, ↓reduceIte, hpt]; rfl)
    · rw [if_neg g6] at hW; simp only [inferProjE.j2] at hW; cases hW
      have hne : ((decI wT : NIdx) != decI sn) = true := by
        simp only [bne_iff_ne, ne_eq]; exact fun h => g6 (decI_inj hcTw hsn h)
      have hpt : projIndexedStructLike fe (decI wT) (decI sn) i.toNat xs.length = false := by
        simp [projIndexedStructLike, hne]
      exact ErrClaim.of_error hT (by
            rw [hts]; simp only [projMissError, Bool.false_eq_true, ↓reduceIte, hpt]; rfl)
  · -- a hit: `infer_proj_at`
    rw [if_neg g4] at hW
    obtain ⟨tbl, hdt, hfe⟩ := hc.projFound n m₃ _ dn vis fe M₂ eb wT i r₄ m₄ hS₂ (callW_of_callE hc4) g4
    have hde : decEntry (m₃.arr64 EREC) (r₄.headD 0) (r₄.tail.headD 0) i.toNat =
        some (tbl.entry i.toNat) := by
      unfold decEntry; rw [if_neg g4, hdt]; rfl
    rw [hde] at hrun4
    have hq₄ : decTbl (m₄.arr64 EREC) (r₄.tail.headD 0).toNat = some tbl := by rw [hE₄]; exact hdt
    have hi : i.toNat < tbl.numFields := findProj?_lt hrun4
    cases hc5 : callE p n "infer_proj_at" [vis, sn, i, pe, r₂.headD 0, wT, wu, r₄.tail.headD 0] m₄ with
    | ok q₅ => rw [hc5] at hW; simp only [inferProjE.k_infer_proj_at] at hW; cases hW
    | error e5 =>
    rw [hc5] at hW; simp only [inferProjE.k_infer_proj_at] at hW; cases hW
    cases n with
    | zero =>
      obtain ⟨e', he', h0⟩ := callE_zero p "infer_proj_at"
        [vis, sn, i, pe, r₂.headD 0, wT, wu, r₄.tail.headD 0] m₄
      rw [he'] at hc5; cases hc5; exact ErrClaim.of_cls0 h0
    | succ N =>
    have hE5 := CoreSpecE.of_callE (hat N ⟨m₄, Locals.init []⟩ _ dn vis fe M₄ eb sn i pe (r₂.headD 0)
      wT wu (r₄.tail.headD 0) tbl hS₄ hq₄ hfe hi hcuw hrw2 hpe ⟨lsu, hdu⟩) hc5
    exact ErrClaim.of_run_eq' (fun ce h => (inferProj_hit R fe d.toNat (decI sn) i.toNat (decE pe) a₀
      _ _ _ _ _ _ _ _ hrun1 hrun2 hgaf ht hv hrun4).trans h) hE5

end L.Arena
