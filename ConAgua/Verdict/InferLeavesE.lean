import ConAgua.Arena.InferProj2
import ConAgua.Arena.InferLeaves
import ConAgua.Arena.KnotE
import ConAgua.Checker.NoVerdictClosed

/-!
# Error refinements of `infer_const`, `infer_proj` (lane `verdicts-b`, helper `c1`)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

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

end L.Arena
