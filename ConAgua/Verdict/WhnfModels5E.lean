import ConAgua.Arena.WhnfIotaRefine5
import ConAgua.Arena.Verdict

/-!
# Error models of `iota_certs_full` and its helpers, by hand (lane `verdicts-b`, helper `k2`)

The ok models of `WhnfIotaRefine5.lean` with `callE` for `callW` (an abort's code kept; a failing
store's bound is a class-`0` failure, modelled as `abort 0`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

def icfCheckE (p : Prog) (n : Nat) (m : Mem) (mode vis d ty aco acn arg : Word) :
    Except Err (List Word × Mem) :=
  match callE p n "inst_list" [ty, aco, acn, 0] m with
  | .error e => .error e
  | .ok (ty2, m1) =>
  match callE p n "infer" [mode, vis, d, arg] m1 with
  | .error e => .error e
  | .ok (ta, m2) =>
  match callE p n "defeq" [mode, vis, d, ta.headD 0, ty2.headD 0] m2 with
  | .error e => .error e
  | .ok (ok, m3) => .ok ([ok.headD 0], m3)

theorem icfCheckE_spec (p : Prog) (hp : p.lookup "iota_certs_full_check" = some iotaCertsFullCheckL)
    (n : Nat) (s₀ : St) (mode vis d ty aco acn arg : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "iota_certs_full_check" [mode, vis, d, ty, aco, acn, arg]
    ⦃fun _ _ => True; fun ε => ε.code ≠ 0 →
      icfCheckE p n s₀.mem mode vis d ty aco acn arg = .error ε⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, iotaCertsFullCheckL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
    callE_spec p n "inst_list", callE_spec p n "infer", callE_spec p n "defeq"] <;>
  simp_all [icfCheckE, LocEq, St.setLocs_cons,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ]

def icfForallE (p : Prog) (n : Nat) (m : Mem) (mode vis d h aco acn ao an i : Word) :
    Except Err (List Word × Mem) :=
  match callE p n "iota_certs_full_parts" [h] m with
  | .error e => .error e
  | .ok (pr, m0) =>
  match callE p n "spn_get" [ao + i] m0 with
  | .error e => .error e
  | .ok (ra, m00) =>
  match callE p n "iota_certs_full_check"
      [mode, vis, d, pr.headD 0, aco, acn, ra.headD 0] m00 with
  | .error e => .error e
  | .ok (ok, m3) =>
  if ok.headD 0 = 0 then .ok ([0], m3)
  else if (aco + acn).toNat < (m3.arr64 SPN).size ∧ (136 : Word).toNat < (m3.arr64 CTL).size then
    match callE p n "iota_certs_full_aux"
        [mode, vis, d, pr.tail.headD 0, aco, acn + 1, ao, an, i + 1]
        ((m3.set64 SPN (aco + acn) (ra.headD 0)).set64 CTL 136 (aco + acn + 1)) with
    | .error e => .error e
    | .ok (r, m4) => .ok ([r.headD 0], m4)
  else .error (.abort 0)

theorem icfForallE_spec (p : Prog) (hp : p.lookup "iota_certs_full_forall" = some iotaCertsFullForallL)
    (n : Nat) (s₀ : St) (mode vis d h aco acn ao an i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "iota_certs_full_forall" [mode, vis, d, h, aco, acn, ao, an, i]
    ⦃fun _ _ => True; fun ε => ε.code ≠ 0 →
      icfForallE p n s₀.mem mode vis d h aco acn ao an i = .error ε⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, iotaCertsFullForallL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
    callE_spec p n "iota_certs_full_parts", callE_spec p n "spn_get",
    callE_spec p n "iota_certs_full_check", callE_spec p n "iota_certs_full_aux"] <;>
  simp_all [icfForallE, Cmp.eval, BinOp.eval, Mem.len64, LocEq, St.setLocs_cons,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ, CTL, size_set64]

def icfFlushE (p : Prog) (n : Nat) (m : Mem) (mode vis d h aco acn ao an i : Word) :
    Except Err (List Word × Mem) :=
  match callE p n "expr_view_ok" [h] m with
  | .error e => .error e
  | .ok (_, m0) =>
  if acn = 0 then .ok ([0], m0)
  else match callE p n "inst_list" [h, aco, acn, 0] m0 with
    | .error e => .error e
    | .ok (ty2, m1) =>
      match callE p n "iota_certs_full_aux" [mode, vis, d, ty2.headD 0, aco + acn, 0, ao, an, i] m1 with
      | .error e => .error e
      | .ok (r, m') => .ok ([r.headD 0], m')

theorem icfFlushE_spec (p : Prog) (hp : p.lookup "iota_certs_full_flush" = some iotaCertsFullFlushL)
    (n : Nat) (s₀ : St) (mode vis d h aco acn ao an i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "iota_certs_full_flush" [mode, vis, d, h, aco, acn, ao, an, i]
    ⦃fun _ _ => True; fun ε => ε.code ≠ 0 →
      icfFlushE p n s₀.mem mode vis d h aco acn ao an i = .error ε⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, iotaCertsFullFlushL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
    callE_spec p n "inst_list", callE_spec p n "iota_certs_full_aux",
    callE_spec p n "expr_view_ok"] <;>
  simp_all [icfFlushE, Cmp.eval, BinOp.eval, LocEq, St.setLocs_cons,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ]

def icfAuxE (p : Prog) (n : Nat) (m : Mem) (mode vis d h aco acn ao an i : Word) :
    Except Err (List Word × Mem) :=
  if i < an then
    if h >>> 28 = 6 then
      match callE p n "iota_certs_full_forall" [mode, vis, d, h, aco, acn, ao, an, i] m with
      | .error e => .error e
      | .ok (r, m') => .ok ([r.headD 0], m')
    else if h >>> 28 = 0 then
      match callE p n "iota_certs_full_flush" [mode, vis, d, h, aco, acn, ao, an, i] m with
      | .error e => .error e
      | .ok (r, m') => .ok ([r.headD 0], m')
    else match callE p n "expr_view_ok" [h] m with
      | .error e => .error e
      | .ok (_, m') => .ok ([0], m')
  else .ok ([1], m)

theorem icfAuxE_spec (p : Prog) (hp : p.lookup "iota_certs_full_aux" = some iotaCertsFullAuxL)
    (n : Nat) (s₀ : St) (mode vis d h aco acn ao an i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "iota_certs_full_aux" [mode, vis, d, h, aco, acn, ao, an, i]
    ⦃fun _ _ => True; fun ε => ε.code ≠ 0 →
      icfAuxE p n s₀.mem mode vis d h aco acn ao an i = .error ε⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, iotaCertsFullAuxL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
    callE_spec p n "iota_certs_full_forall", callE_spec p n "iota_certs_full_flush",
    callE_spec p n "expr_view_ok"] <;>
  simp_all [icfAuxE, Cmp.eval, BinOp.eval, Locals.init_cons_zero, Locals.init_cons_succ] <;>
  exact of_decide_eq_true ‹_›

def icfTopE (p : Prog) (n : Nat) (m : Mem) (mode vis d h ao an : Word) :
    Except Err (List Word × Mem) :=
  match callE p n "ctl_get" [136] m with
  | .error e => .error e
  | .ok (t, m0) =>
  match callE p n "iota_certs_full_aux" [mode, vis, d, h, t.headD 0, 0, ao, an, 0] m0 with
  | .error e => .error e
  | .ok (r, m') => .ok ([r.headD 0], m'.set64 CTL 136 (t.headD 0))

theorem icfTopE_spec (p : Prog) (hp : p.lookup "iota_certs_full" = some iotaCertsFullL)
    (n : Nat) (s₀ : St) (mode vis d h ao an : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "iota_certs_full" [mode, vis, d, h, ao, an]
    ⦃fun _ _ => True; fun ε => ε.code ≠ 0 → icfTopE p n s₀.mem mode vis d h ao an = .error ε⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, iotaCertsFullL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
    callE_spec p n "ctl_get", callE_spec p n "iota_certs_full_aux"] <;>
  simp_all [icfTopE, LocEq, St.setLocs_cons,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ]

end L.Arena
