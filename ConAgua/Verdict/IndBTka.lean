import ConAgua.Verdict.IndBK53
import ConAgua.Verdict.IndBTmn

/-!
# `target_k53_args`' error claim (lane `verdicts-b`, helper `fin`, fork `tka`)

`TkaE` (IndBK53.lean) proved: the error model of `target_k53_args`, its claim along `tkaW_okC`'s case
chain; the callees outside the verdict closure claim nothing, `target_class_match` is `tcm_claimA`.
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dShape dMajor)
open ConRon.Bridge (CoreStep denote_ext denoteEList_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## The error model (by hand: the generator's step `grind` fails) -/

def tkaE.k8 : Except Err (List Word × Mem) → Except Err (List Word × Mem)
  | .error ε => .error ε
  | .ok (r, m) => .ok ([r.headD 0], m)

def tkaE.k7 (p : Prog) (n : Nat) (vis q fto ftl Mc usp lao lpl : Word) :
    Except Err (List Word × Mem) → Except Err (List Word × Mem)
  | .error ε => .error ε
  | .ok (r, m) =>
    if r.headD 0 = 0 then .ok ([0], m)
    else tkaE.k8 (callE p n "target_class_match" [vis, q, fto, ftl, rdW (m.arr64 IW) (Mc + 11),
      rdW (m.arr64 IW) (Mc + 12), rdW (m.arr64 IW) (Mc + 1), rdW (m.arr64 IW) (Mc + 2),
      rdW (m.arr64 IW) (Mc + 3), usp, lao, lpl] m)

def tkaE.k6 (p : Prog) (n : Nat) (vis q fto ftl Mc usp lao lpl app : Word) :
    Except Err (List Word × Mem) → Except Err (List Word × Mem)
  | .error ε => .error ε
  | .ok (rn, m) => tkaE.k7 p n vis q fto ftl Mc usp lao lpl
      (callE p n "nest_occ" [rn.headD 0, rn.tail.headD 0, 0, 0, app] m)

def tkaE.k5 (p : Prog) (n : Nat) (vis q fto ftl Mc usp lao lpl : Word) :
    Except Err (List Word × Mem) → Except Err (List Word × Mem)
  | .error ε => .error ε
  | .ok (ra, m) => tkaE.k6 p n vis q fto ftl Mc usp lao lpl (ra.headD 0)
      (callE p n "block_shape_member_names" [q] m)

def tkaE.k4 (p : Prog) (n : Nat) (vis q fto ftl Mc usp lao lpl : Word) :
    Except Err (List Word × Mem) → Except Err (List Word × Mem)
  | .error ε => .error ε
  | .ok (r, m) =>
    if 4294967296 ≤ r.headD 0 then .error (.abort 0)
    else tkaE.k5 p n vis q fto ftl Mc usp lao lpl (callE p n "mk_app_n_f" [r.headD 0, lao, lpl] m)

def tkaE.k3 (p : Prog) (n : Nat) (vis q fto ftl Mc ip usp lao lal K : Word) :
    Except Err (List Word × Mem) → Except Err (List Word × Mem)
  | .error ε => .error ε
  | .ok (r, m) =>
    if r.headD 0 = 0 then .ok ([0], m)
    else tkaE.k4 p n vis q fto ftl Mc usp lao (if lal < K then lal else K)
      (callE p n "intern_const" [ip, usp] m)

def tkaE.k2 (p : Prog) (n : Nat) (vis q fto ftl Mc ip usp lao lal K : Word) (r1 : List Word) :
    Except Err (List Word × Mem) → Except Err (List Word × Mem)
  | .error ε => .error ε
  | .ok (r2, m) => tkaE.k3 p n vis q fto ftl Mc ip usp lao lal K
      (callE p n "sl_eq" [r1.headD 0, r1.tail.headD 0, r2.headD 0, r2.tail.headD 0] m)

def tkaE.k1 (p : Prog) (n : Nat) (vis q fto ftl Mc ip usp lao lal mao mal K : Word) :
    Except Err (List Word × Mem) → Except Err (List Word × Mem)
  | .error ε => .error ε
  | .ok (r1, m) => tkaE.k2 p n vis q fto ftl Mc ip usp lao lal K r1
      (callE p n "erase_each" [if mal < K then mao else mao + K, if mal < K then 0 else mal - K] m)

/-- **The error model of `target_k53_args`** (`tkaW`'s shape, every callee through `callE`). -/
def tkaE (p : Prog) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Word → Word → Except Err (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => .error .outOfFuel
  | n + 1, m, vis, q, fto, ftl, Mc, ip, usp, lao, lal, mao, mal =>
    tkaE.k1 p n vis q fto ftl Mc ip usp lao lal mao mal (rdW (m.arr64 IW) (Mc + 4))
      (callE p n "erase_each" [if lal < rdW (m.arr64 IW) (Mc + 4) then lao else lao + rdW (m.arr64 IW) (Mc + 4),
        if lal < rdW (m.arr64 IW) (Mc + 4) then 0 else lal - rdW (m.arr64 IW) (Mc + 4)] m)

theorem tka_ite_neg {α : Sort _} {x K : Word} {a b : α} (h : K ≤ x) : (if x < K then a else b) = b :=
  if_neg (UInt64.not_lt.mpr h)

theorem tka_ite_pos {α : Sort _} {x K : Word} {a b : α} (h : x < K) : (if x < K then a else b) = a :=
  if_pos h

set_option maxHeartbeats 8000000 in
theorem tkaE_spec (p : Prog) (hf : p.lookup "target_k53_args" = some targetK53Args) (n : Nat) (s₀ : St)
    (vis q fto ftl Mc ip usp lao lal mao mal : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_k53_args" [vis, q, fto, ftl, Mc, ip, usp, lao, lal, mao, mal]
    ⦃fun _ _ => True; fun ε => ε.code ≠ 0 →
      tkaE p n s₀.mem vis q fto ftl Mc ip usp lao lal mao mal = .error ε⦄ := by
  cases n with
  | zero =>
    rw [invoke_eq _ hf]; simp only [callFn, targetK53Args]
    vcgen [exec] <;> grind
  | succ n =>
    rw [invoke_eq _ hf]
    simp only [callFn, targetK53Args]
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_specE,
      callE_spec p n "erase_each", callE_spec p n "sl_eq", callE_spec p n "intern_const",
      callE_spec p n "mk_app_n_f", callE_spec p n "block_shape_member_names", callE_spec p n "nest_occ",
      callE_spec p n "target_class_match"]
    all_goals (try simp only [LocEq] at *)
    all_goals (try simp only [*, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
        List.headD_cons, List.headD_nil, List.tail_cons, List.tail_nil, Locals.init_nil,
        Locals.init_cons_zero, Locals.init_cons_succ, loc_init4, loc_init5, loc_init6, loc_init7, loc_init8,
        loc_init9, loc_init10, Cmp.eval, BinOp.eval, Nat.reduceEqDiff,
        reduceIte, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at *)
    all_goals (try simp_all [tka_ite_neg, tka_ite_pos, tkaE, tkaE.k1, tkaE.k2, tkaE.k3, tkaE.k4, tkaE.k5, tkaE.k6, tkaE.k7, tkaE.k8])
    all_goals grind [lang_grind, arena_grind, tkaE, tkaE.k1, tkaE.k2, tkaE.k3, tkaE.k4, tkaE.k5, tkaE.k6,
      tkaE.k7, tkaE.k8]

end L.Ind
