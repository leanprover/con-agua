import ConAgua.Arena.IndT.Sum3
import ConAgua.Arena.IndInstallSpec.IcvgW
import ConAgua.Arena.IndInstallSpec.InstallRec2PSl

/-!
# `check_struct_field_sorts_i` as a callee under `StageC`

`installSimFsortsC`: a call of `check_struct_field_sorts_i` (`fsortsW_okC`) as a `Sim`;
Used by the block checks (`IndT/IdxSorts`, `Install6`).
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hLC : LvlCacheProg p) (hLT : p.lookup "lv_leq_top" = some lvLeqTop)

include hq henv hLC hLT in
/-- `check_struct_field_sorts_i` under `StageC` as a `Sim` of its call. -/
theorem installSimFsortsC (hP : SumProg p) (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    (isP large s nP fo fl io il j : Word) (hs : H s) (fvs idx : List EIdx) {sP : ConLeche.Level}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) (hsP : denoteL a.store.ls (decI s) = some sP)
    (hfd : decHL m fo.toNat fl.toNat = some fvs) (hfb : fo.toNat + fl.toNat ≤ iwTop m)
    (hid : decHL m io.toNat il.toNat = some idx) (hib : io.toNat + il.toNat ≤ iwTop m)
    (hnj : nP.toNat + j.toNat < 2 ^ 64) {fvsP : List ConLeche.Expr}
    (hfP : Frontend.denoteEList a.store fvs = some fvsP)
    (hws : ∀ i, i < j.toNat → ∀ x, fvsP[i]? = some x →
      ConLeche.Expr.WScoped (nP.toNat + i) x.fvarTypeD) :
    Sim (callW p n "check_struct_field_sorts_i" [vis, isP, large, s, nP, fo, fl, io, il, j] m)
      (checkStructFieldSortsI V fe (isP != 0) (large != 0) (decI s) nP.toNat fvs idx j.toNat) a
      (fun r x m' a' => StageC dn vis fe env m' a' ∧ IWGrow m m' ∧
        decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some x ∧
        (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ AbsOK m') := by
  rcases n with _ | k
  · intro r m' e; rw [callW_zero] at e; cases e
  intro r m' e
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (fsortsW_spec p hP.hg hP.hpw hP.het hP.hcn hP.hfsb hP.hcfg hP.ha hP.hcfs hP.ad.ftd (realCall p)
      (realCall_spec p) k _ vis isP large s nP fo fl io il j) e
  exact fsortsW_okC hq henv hLC hLT k (by omega) m a isP large s nP fo fl io il j fvs idx hC hA hfd hfb hid
    hib hs hsP hnj hfP hws r s'.mem hW

end sims

end L.Ind
