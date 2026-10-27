import ConAgua.Arena.RecCheckSpec.TargetMajorAt2
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# ClassGenMajorCi

`rec2DecB_HL_top`, `rec2ExprGetD_specF`, `rec2SimExprGetD`, `classGenMajorTail_spec`, `mjtW`, `classGenMajorOpen_spec` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- A non-empty handle slice decoded below the tops lies below the top. -/
theorem rec2DecB_HL_top {k : IdxKind} {m : Mem} {o l : Nat} {xs : List (Idx k)}
    (h : DecB (fun m => (decHL m o l : Option (List (Idx k)))) m xs) (hl : l ≠ 0) : o + l ≤ iwTop m := by
  have := decHL_getI h (l - 1) (by omega)
  have := (rec2IwH_trunc this).1
  omega

/-! ## `expr_get_d` at every fuel -/

theorem rec2ExprGetD_specF (p : Prog) (hpf : p.lookup "bvar_find" = some bvarFind)
    (hpp : p.lookup "bvar_push" = some bvarPush) (hib : p.lookup "intern_bvar" = some internBVar)
    (hp : p.lookup "expr_get_d" = some exprGetD) (n : Nat) (s₀ : St) (o l i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "expr_get_d" [o, l, i]
    ⦃fun r s' => LocEq s' s₀ ∧ fuelW n (exprGetDW s₀.mem o l i) = some (r, s'.mem); ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n => exact exprGetD_spec p hpf hpp hib hp n s₀ o l i

theorem rec2SimExprGetD {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (n : Nat) (hS : StageR dn vis fe m a) {o l i : Word} {xs : List EIdx}
    (hxs : decHL m o.toNat l.toNat = some xs) (hb : o.toNat + l.toNat < 2 ^ 64) :
    RSim (fuelW n (exprGetDW m o l i)) (ConRon.Arena.exprGetD xs i.toNat) a (KP dn vis fe m decW0E) := by
  rcases n with _ | n
  · exact RSim.none
  rintro ⟨r, m'⟩ h
  obtain ⟨x, a', hrun, hS', hg, h1, h2⟩ := exprGetDW_ok dn vis fe m m' a o l i xs r h hS hxs hb
  exact ⟨x, a', hrun, hS', hg, h1, h2⟩

l_model classGenMajorTail_spec (p : Prog) (h : MjProg p)
  fns [h.mjt ↦ mjtW list]
  specs [internConst_spec p h.cf h.cp h.ic n, slAppend_specW p h.alloc h.copy h.app n, mknF_spec p h.ad n]
  grind [arena_grind] simp []

l_model classGenMajorOpen_spec (p : Prog) (h : MjProg p)
  fns [h.mjo ↦ mjoW list]
  specs [opfF_spec p h.opf n, classGenMajorTail_spec p h n]
  grind [arena_grind] simp []

theorem classGenMajorCi_spec (p : Prog) (h : MjProg p) (n : Nat) (s₀ : St) (ci : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_major_ci" [ci]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = rdW (s₀.mem.arr64 IW) ci ∧ r.tail.headD 0 = rdW (s₀.mem.arr64 IW) (ci + 1) ∧
      r.tail.tail.headD 0 = rdW (s₀.mem.arr64 IW) (ci + 2) ∧
      r.tail.tail.tail.headD 0 = rdW (s₀.mem.arr64 IW) (ci + 3) ∧
      r.tail.tail.tail.tail.headD 0 = rdW (s₀.mem.arr64 IW) (ci + 5); ⊤⦄ := by
  rw [invoke_eq _ h.mci]
  simp only [callFn, classGenMajorCi]
  rcases n with _ | n
  · vcgen [exec] <;> grind
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
    finish (gen := 20) [rdW_eq]

l_model classGenMajor_spec (p : Prog) (h : MjProg p)
  fns [h.mj ↦ mjW list]
  specs [targetMajorAt_spec p h.alloc h.pw h.mtm h.tmd h.tma h.na n,
    rec2ExprGetD_specF p h.bf h.bp h.ib h.egd n, instPisWith_spec p h.ev h.ipw h.hi1 n,
    classGenMajorOpen_spec p h n, classGenMajorCi_spec p h n]
  grind [arena_grind] finish [rdW_eq] gen 20

/-! ## `class_gen_major` refines `ClassGen.major` -/

/-- The twin's `ClassGen.major` after the index telescope is opened. -/
def rec2MajTail (ind : NIdx) (lvls : LsIdx) (ds ifs : List EIdx) : AM (Option (List EIdx × EIdx)) := do
  let hd ← internE (.const ind lvls)
  let maj ← mkAppN hd (ds ++ ifs)
  pure (some (ifs, maj))

/-- The twin's `ClassGen.major` after the parameters are instantiated. -/
def rec2MajOpen (ind : NIdx) (lvls : LsIdx) (ds : List EIdx) (nIdx : Nat) (ty : EIdx) (d : Nat) :
    AM (Option (List EIdx × EIdx)) := do
  match ← openPisAtFvarsF nIdx ty d with
  | none => pure none
  | some (ifs, _) => rec2MajTail ind lvls ds ifs

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-! ## The `abstract1` memo across `class_gen_major` -/

theorem exprGetDW_afr {m m' : Mem} {o l i : Word} {r : List Word} (h : exprGetDW m o l i = some (r, m')) :
    AFr m m' := by
  unfold exprGetDW at h
  afr_auto h [binternW_afr]

theorem exprGetDF_afr {n : Nat} {m m' : Mem} {o l i : Word} {r : List Word}
    (h : fuelW n (exprGetDW m o l i) = some (r, m')) : AFr m m' := by
  cases n with
  | zero => simp [fuelW] at h
  | succ n => exact exprGetDW_afr h

end sims

l_model classGenMotiveTy_spec (p : Prog) (h : MtProg p)
  fns [h.mot ↦ motW list]
  specs [classGenMajor_spec p h.toMjProg n, internSort_spec p h.sf h.sp h.isort n,
    mkForall_spec p h.db h.ff h.fp h.ifa h.mkf n, ftdsF_spec p h.ad n,
    closeTelescope_spec p h.db h.ff h.fp h.ifa h.mkf h.ct h.ab n]
  grind [arena_grind] simp [rdW_eq]

end L.Ind

end
