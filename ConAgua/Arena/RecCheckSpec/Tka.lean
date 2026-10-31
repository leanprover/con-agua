module

public import ConAgua.Arena.LdRd
public import ConAgua.Arena.RecCheckSpec.K53Look
public import ConAgua.Arena.RecCheckSpec.EeW
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr

@[expose] public section

/-!
# Tka

`eeK0_some`, `eeK1_some`, `eeK2_some`, `eftF_spec`, `noF_spec`, `ee_spec`, `tte_spec` and the lemmas only they use.
-/

section

noncomputable section

/-!
# `RecCheck`: `targetK53`, the L side (lane `indproofs3`, helper `rec`)

K.53′ at one recorded field: `strip_pis` (stub), the telescope check (`target_k53_tele`: both sides
erased by `erase_each`, compared by `sl_eq`), the head check (`target_k53_heads`: `get_app_fn_f`,
`get_app_args_f` stubs, `e_view`), the argument check (`target_k53_args`: erased indices, the
leaf's class `intern_const` + `mk_app_n_f` (stub) + `nest_occ`, then `target_class_match`).
L: `erase_each` is the twin's `mapM` as a self-recursion consing each result (`sl_cons`, D18); a
handle guard after `intern_const` (`mk_app_n_f`'s contract takes a handle).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section arms
variable (n : Nat) (m : Mem) (o l v : Word) (rv rr rc : List Word)
theorem eeK0_some : eeK0 n o l (some (rv, m)) = eeK1 n (rv.headD 0) (eeW n m (o + 1) (l - 1)) := by
  simp [eeK0]
theorem eeK1_some : eeK1 n v (some (rr, m)) = eeK2 (consW n m v (rr.headD 0) (rr.tail.headD 0)) := rfl
theorem eeK2_some : eeK2 (some (rc, m)) = some ([rc.headD 0, rc.tail.headD 0], m) := rfl
end arms
attribute [ind_grind] eeK0_some eeK1_some eeK2_some

theorem eftF_spec (p : Prog) (L : RcLook p) (n : Nat) (s₀ : St) (e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "erase_fvar_tys" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ eftF n s₀.mem e = some (r, s'.mem); ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n => exact eraseFVarTys_spec p L.rx L.eft n s₀ e

theorem noF_spec (p : Prog) (L : K53Look p) (n : Nat) (s₀ : St) (no nl lo hi e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_occ" [no, nl, lo, hi, e]
    ⦃fun r s' => LocEq s' s₀ ∧ noF n s₀.mem no nl lo hi e = some (r.headD 0, s'.mem); ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n => exact nestOcc_spec p L.hv L.sc L.nf L.np L.ngo L.nnode L.ncl L.no n s₀ no nl lo hi e

theorem ee_spec (p : Prog) (L : K53Look p) (n : Nat) :
    ∀ (s₀ : St) (o l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "erase_each" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ eeW n s₀.mem o l = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero => intro s₀ o l; rw [invoke_eq _ L.ee]; simp only [callFn, eraseEach]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o l
    rw [invoke_eq _ L.ee]
    simp only [callFn, eraseEach]
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih,
      eftF_spec p L.tmn.tcm.tp.rc n, slCons_specW p L.tmn.tcm.ha L.tmn.tcm.ic L.tmn.tcm.sc n]
    all_goals (try simp only [LocEq] at *)
    all_goals (try simp only [*, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
      Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval, Nat.reduceEqDiff,
      reduceIte, beq_iff_eq] at *)
    all_goals grind (gen := 10) [lang_grind, arena_grind, ind_grind, rdW_eq]

section arms
variable (n : Nat) (m : Mem) (bso bsl teo tel e : Word) (r1 r2 : List Word)
theorem tteK1_some : tteK1 n teo tel (some (r1, m)) = tteK2 n r1 (eeW n m teo tel) := rfl
theorem tteK2_some : tteK2 n r1 (some (r2, m)) =
    tteK3 m (eqW n m (r1.headD 0) (r1.tail.headD 0) (r2.headD 0) (r2.tail.headD 0)) := rfl
theorem tteK3_some : tteK3 m (some e) = some ([e], m) := rfl
end arms
attribute [ind_grind] tteK1_some tteK2_some tteK3_some

theorem tte_spec (p : Prog) (L : K53Look p) (n : Nat) (s₀ : St) (bso bsl teo tel : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_k53_tele" [bso, bsl, teo, tel]
    ⦃fun r s' => LocEq s' s₀ ∧ tteW n s₀.mem bso bsl teo tel = some (r, s'.mem); ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n =>
    rw [invoke_eq _ L.tte]
    simp only [callFn, targetK53Tele]
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ee_spec p L n, slEq_spec p L.eq n]
    all_goals (try simp only [LocEq] at *)
    all_goals (try simp only [*, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
      Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, Nat.reduceEqDiff, reduceIte] at *)
    all_goals grind (gen := 20) [lang_grind, arena_grind, ind_grind]

end L.Ind

end
end

end

