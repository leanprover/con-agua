import ConAgua.Arena.WhnfIotaRecRefine2

/-!
# Error models of `iota_rec_vck` and `iota_rec_fire2`, by hand (lane `verdicts-b`, helper `k2`)

`l_model … errors` fails on both (the index words' arithmetic); the models follow the ok models
`irVckW`, `irFire2W` (`WhnfIotaRecRefine*.lean`) with `callE` for `callW` and the abort's code kept.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

namespace L.Arena

/-- Error model of `iota_rec_vck` past the constructor's type. -/
def irVckTailE (p : Prog) (n : Nat) (m : Mem) (mode vis d recP so rl mo mn tyC : Word) :
    Except Err (Word × Mem) :=
  match callE p n "iota_certs_full" [mode, vis, d, tyC, mo, mn] m with
  | .error e => .error e
  | .ok (rf, m4) =>
  if rf.headD 0 = 0 then .ok (0, m4) else
  match callE p n "iota_index_ok" [mode, vis, d, rdW (m4.arr64 EREC) (recP + 5),
      rdW (m4.arr64 EREC) (recP + 6), rdW (m4.arr64 EREC) (rl + 2), tyC, mo, mn,
      so + (rdW (m4.arr64 EREC) (recP + 6) -
        ixLen (rdW (m4.arr64 EREC) (recP + 6)) (rdW (m4.arr64 EREC) (recP + 5))),
      ixLen (rdW (m4.arr64 EREC) (recP + 5)) (rdW (m4.arr64 EREC) (recP + 6))] m4 with
  | .error e => .error e
  | .ok (ri, m5) => .ok (ri.headD 0, m5)

/-- Error model of `iota_rec_vck`. -/
def irVckE (p : Prog) (n : Nat) (m : Mem) (mode vis d us recP so usj ctorP rl mo mn cmpL : Word) :
    Except Err (Word × Mem) :=
  match callE p n "lvls_eq_c" [usj, cmpL] m with
  | .error e => .error e
  | .ok (rq, m1) =>
  if rq.headD 0 = 0 then .error (.abort R_RESOURCE_LIMIT_FUEL) else
  if rq.headD 0 = 1 then .ok (0, m1) else
  match callE p n "iota_rec_cmp" [mode, vis, d, us, recP, so, rl, mo] m1 with
  | .error e => .error e
  | .ok (rc, m2) =>
  if rc.headD 0 = 0 then .ok (0, m2) else
  match callE p n "const_ty_at" [rdW (m2.arr64 EREC) (ctorP + 1), rdW (m2.arr64 EREC) (ctorP + 2),
      rdW (m2.arr64 EREC) (ctorP + 3), rdW (m2.arr64 EREC) (ctorP + 4), usj] m2 with
  | .error e => .error e
  | .ok (rt, m3) => irVckTailE p n m3 mode vis d recP so rl mo mn (rt.headD 0)

theorem irVckE_spec (p : Prog) (hp : p.lookup "iota_rec_vck" = some iotaRecVckL) (n : Nat)
    (s₀ : St) (mode vis d us recP so usj ctorP rl mo mn cmpL : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "iota_rec_vck" [mode, vis, d, us, recP, so, usj, ctorP, rl, mo, mn, cmpL]
    ⦃fun _ _ => True; fun ε => ε.code ≠ 0 →
      irVckE p n s₀.mem mode vis d us recP so usj ctorP rl mo mn cmpL = .error ε⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, iotaRecVckL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
    callE_spec p n "lvls_eq_c", callE_spec p n "iota_rec_cmp", callE_spec p n "const_ty_at",
    callE_spec p n "iota_certs_full", callE_spec p n "iota_index_ok"] <;>
  simp_all [-UInt64.toNat_add, irVckE, irVckTailE, ixLen, EREC, CTL, BinOp.eval, getElem_rdW',
    Cmp.eval, LocEq, St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil,
    Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal, Sig.retOr]

/-- Error model of `iota_rec_fire2`. -/
def irFire2E (p : Prog) (n : Nat) (m : Mem) (mode vis d c us recP so usj ctorP rl mo mn : Word) :
    Except Err (Word × Word × Mem) :=
  if mn < rdW (m.arr64 EREC) (rl + 2) then .ok (0, 0, m) else
  if mn - rdW (m.arr64 EREC) (rl + 2) ≠ rdW (m.arr64 EREC) (rl + 1) then .ok (0, 0, m) else
  match callE p n "iota_rec_fam" [mode, vis, d, us, recP, so, usj, ctorP, rl, mo, mn] m with
  | .error e => .error e
  | .ok (rf, m1) =>
  if rf.headD 0 = 0 then .ok (0, 0, m1) else
  match callE p n "rule_rhs_at" [c, rdW (m1.arr64 EREC) rl, rdW (m1.arr64 EREC) (recP + 2),
      rdW (m1.arr64 EREC) (recP + 3), rdW (m1.arr64 EREC) (rl + 8), us] m1 with
  | .error e => .error e
  | .ok (rr, m2) =>
  match callE p n "mk_app_n" [rr.headD 0, so,
      rpLen (rdW (m.arr64 EREC) (recP + 5)) (rdW (m.arr64 EREC) (recP + 6))] m2 with
  | .error e => .error e
  | .ok (rx, m3) =>
  match callE p n "mk_app_n_from" [rx.headD 0, mo, mn, rdW (m.arr64 EREC) (rl + 2)] m3 with
  | .error e => .error e
  | .ok (ry, m4) => .ok (1, ry.headD 0, m4)

theorem irFire2E_spec (p : Prog) (hp : p.lookup "iota_rec_fire2" = some iotaRecFire2L)
    (n : Nat) (s₀ : St) (mode vis d c us recP so usj ctorP rl mo mn : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "iota_rec_fire2" [mode, vis, d, c, us, recP, so, usj, ctorP, rl, mo, mn]
    ⦃fun _ _ => True; fun ε => ε.code ≠ 0 →
      irFire2E p n s₀.mem mode vis d c us recP so usj ctorP rl mo mn = .error ε⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, iotaRecFire2L]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
    callE_spec p n "iota_rec_fam", callE_spec p n "rule_rhs_at", callE_spec p n "mk_app_n",
    callE_spec p n "mk_app_n_from"] <;>
  simp_all [-UInt64.toNat_add, irFire2E, rpLen, EREC, CTL, BinOp.eval, getElem_rdW', Cmp.eval, LocEq,
    St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero,
    Locals.init_cons_succ, Sig.retVal, Sig.retOr]

end L.Arena
