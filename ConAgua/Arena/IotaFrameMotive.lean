module

public import ConAgua.Arena.IotaFrameIface
public import ConAgua.Arena.IotaFrameRef
import ConAgua.Arena.RecClassSpec.CloseLams
import ConAgua.Arena.FormerSortRef
import ConRon.Bridge.Checker.PooledOleans

@[expose] public section

/-!
# `motive_level` refines `motiveLevel?` (lane ronsync8)
-/

open ConRon.Arena
open Std.WP

namespace L.Ind

open L.Arena

theorem viewBVar_run' {a : AState} {h : EIdx} :
    (viewBVar h).run a = .ok (a.store.viewBVar h, a) := by
  simp [viewBVar, StateT.run_get]; rfl

theorem viewSort_run' {a : AState} {h : EIdx} :
    (viewSort h).run a = .ok (a.store.viewSort h, a) := by
  simp [viewSort, StateT.run_get]; rfl

/-- **`e_view` at a `bvar`**: the memory kept, the twin's `viewBVar` the index word. -/
theorem eView_bvar {p : Prog} (hp : p.lookup "e_view" = some eView) {n : Nat}
    {m m' : Mem} {a : AState} (hR : ArenaR m a) {h : Word} {r : List Word}
    (h0 : tagW h = 0) (hc : callW p n "e_view" [h] m = some (r, m')) :
    m' = m ∧ a.store.viewBVar (decE h) = some (r.tail.headD 0).toNat := by
  obtain ⟨rfl, v, hv, hvr, ht⟩ := eView_callW_view hp hR hc
  have h0' : r.headD 0 = 0 := by rw [ht, h0]
  cases v <;> simp only [ViewR, h0'] at hvr
  all_goals first
    | (exfalso; revert hvr; decide)
    | (exfalso; obtain ⟨h1, -⟩ := hvr; revert h1; decide)
    | skip
  rename_i k
  refine ⟨rfl, ?_⟩
  rw [ConRon.Bridge.viewBVar_of_view hv, ← hvr.2, L.getD_one]

/-- **`e_view` at a `sort`**: the memory kept, the twin's `viewSort` the level word. -/
theorem eView_sort {p : Prog} (hp : p.lookup "e_view" = some eView) {n : Nat}
    {m m' : Mem} {a : AState} (hR : ArenaR m a) {h : Word} {r : List Word} (hh : HW h)
    (h2 : tagW h = 2) (hc : callW p n "e_view" [h] m = some (r, m')) :
    m' = m ∧ a.store.viewSort (decE h) = some (decI (r.tail.headD 0)) ∧ HW (r.tail.headD 0) := by
  obtain ⟨rfl, v, hv, hvr, ht⟩ := eView_callW_view hp hR hc
  obtain ⟨rfl, h1⟩ := viewR_sort hvr (by rw [ht, h2])
  have htg : (decE h).tag = ETag.sort := by
    have := decE_tag_sort_beq (e := h) hh; rw [h2] at this; simpa using this
  exact ⟨rfl, L.Arena.viewSort_of_view _ _ _ htg hv, h1⟩

/-- `motiveLevel?`'s answer as `(ok, u)`. -/
def decOL (_m : Mem) (r : List Word) : Option LIdx → Prop
  | none => r.headD 0 = 0
  | some u => r.headD 0 = 1 ∧ HW (r.tail.headD 0) ∧ decI (r.tail.headD 0) = u

theorem iwTop_lt' (m : Mem) : iwTop m < 2 ^ 64 := UInt64.toNat_lt _

/-- **`motive_level` refines `motiveLevel?`**. -/
@[refines ConRon.Arena.motiveLevel?]
theorem motiveLevel_rel {p : Prog} (P : IotaFrameProg p) (n : Nat) (vis : Word) (fe : IFEnv)
    (preO preL nIdx body : Word) (pre : List EIdx) (hpl : preL.toNat < 2 ^ 32)
    (hn : nIdx.toNat < 2 ^ 32) (hb : HW body) :
    RelW (fun m args => callW p n "motive_level" args m) [preO, preL, nIdx, body]
      (fun m a => StageR vis fe m a ∧ decHL m preO.toNat preL.toNat = some pre ∧
        preO.toNat + preL.toNat ≤ iwTop m)
      (motiveLevel? pre nIdx.toNat (decE body)) (KeepPost vis fe decOL) := by
  intro m m' a r hc ⟨hS, hpre, htop⟩
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (motiveLevel_specW p P.motive_level n _ preO preL nIdx body) hc
  have hlen : pre.length = preL.toNat := decHL_length m hpre
  rcases n with _ | n
  · simp [motiveLevelW] at hW
  simp only [motiveLevelW] at hW
  -- `get_app_fn_f`
  rcases h1 : callW p n "get_app_fn_f" [CWF, body] m with _ | ⟨r1, m1⟩
  · rw [h1] at hW; simp [motiveLevelW.k_get_app_fn_f] at hW
  rw [h1] at hW
  obtain ⟨s1, hs1, -, hg1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (gafF_spec0 p P.gaf n _ _) h1
  rw [hs1] at hg1
  obtain ⟨x1, a1, hrun1, hS1, hgr1, hx1, hd1⟩ := gafF_ok vis fe CWF body hb m m1 a r1 hg1 hS
  rw [CWF_eq, ← decE_eq] at hrun1
  unfold motiveLevel?
  rw [StateT.run_bind, hrun1, except_ok_bind]
  dsimp only
  have tb : ((decE (r1.headD 0)).tag == ETag.bvar) = decide (tagW (r1.headD 0) = 0) :=
    decE_tag_beq _ hx1 0 (by decide)
  rw [← hd1, ← decE_eq, tb]
  simp only [motiveLevelW.k_get_app_fn_f] at hW
  by_cases g0 : tagW (r1.headD 0) ≠ 0
  · rw [if_pos g0] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    refine ⟨none, a1, ?_, hS1, hgr1, rfl⟩
    rw [if_neg (by simpa using g0)]; rfl
  rw [if_neg g0] at hW
  have g0 : tagW (r1.headD 0) = 0 := Classical.not_not.mp g0
  -- `e_view` at the `bvar`
  rcases h2 : callW p n "e_view" [r1.headD 0] m1 with _ | ⟨r2, m2⟩
  · rw [h2] at hW; simp [motiveLevelW.k_e_view] at hW
  rw [h2] at hW
  obtain ⟨rfl, hv2⟩ := eView_bvar P.e_view hS1.check.arena.base g0 h2
  rw [if_pos (by simpa using g0)]
  rw [StateT.run_bind, viewBVar_run', hv2, except_ok_bind]
  dsimp only
  simp only [motiveLevelW.k_e_view] at hW
  generalize hw : r2.tail.headD 0 = w at hW
  have hn1 : (nIdx + 1).toNat = nIdx.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hn2 : (nIdx + 1 + preL).toNat = nIdx.toNat + 1 + preL.toNat := by
    rw [UInt64.toNat_add, hn1]; simp; omega
  by_cases c1 : w < nIdx + 1
  · rw [if_pos c1] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have : ¬ nIdx.toNat + 1 ≤ w.toNat := by rw [UInt64.lt_iff_toNat_lt, hn1] at c1; omega
    exact ⟨none, a1, by simp [this]; rfl, hS1, hgr1, rfl⟩
  rw [if_neg c1] at hW
  have c1' : nIdx.toNat + 1 ≤ w.toNat := by rw [UInt64.lt_iff_toNat_lt, hn1] at c1; omega
  by_cases c2 : nIdx + 1 + preL ≤ w
  · rw [if_pos c2] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have : ¬ w.toNat < nIdx.toNat + 1 + pre.length := by
      rw [UInt64.le_iff_toNat_le, hn2] at c2; omega
    exact ⟨none, a1, by simp [c1', this]; rfl, hS1, hgr1, rfl⟩
  rw [if_neg c2] at hW
  have c2' : w.toNat < nIdx.toNat + 1 + pre.length := by
    rw [UInt64.le_iff_toNat_le, hn2] at c2; omega
  simp only [c1', c2', ite_true]
  -- `expr_get_d`
  have hiw : (preL - 1 - (w - (nIdx + 1))).toNat = pre.length - 1 - (w.toNat - (nIdx.toNat + 1)) := by
    have e1 : (w - (nIdx + 1)).toNat = w.toNat - (nIdx.toNat + 1) := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hn1]; omega), hn1]
    have e2 : (preL - 1).toNat = preL.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, e1, e2]; omega), e1, e2, hlen]
  rcases n with _ | n
  · simp [motiveLevelW.k_expr_get_d, callW_zero] at hW
  rcases h3 : callW p (n + 1) "expr_get_d" [preO, preL, preL - 1 - (w - (nIdx + 1))] m2 with _ | ⟨r3, m3⟩
  · rw [h3] at hW; simp [motiveLevelW.k_expr_get_d] at hW
  rw [h3] at hW
  have hpre1 := decHL_grow' hgr1 htop hpre
  obtain ⟨s3, hs3, -, hok3, hS3, hgr3, hx3, hd3⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
    (exprGetD_refines p P.bvar_find P.bvar_push P.intern_bvar P.expr_get_d n ⟨m2, Locals.init []⟩ a1
      (fun _ => none) vis fe preO preL _ pre hS1 hpre1 (by have := iwTop_lt' m; omega)) h3
  simp only at hs3 hS3 hgr3
  subst hs3
  rw [StateT.run_bind, ← hiw, AM.run_of_ok _ _ hok3, except_ok_bind]
  simp only [motiveLevelW.k_expr_get_d] at hW
  generalize AM.res (ConRon.Arena.exprGetD pre (UInt64.toNat (preL - 1 - (w - (nIdx + 1))))) a1 = x3
    at hd3 ⊢
  generalize AM.st (ConRon.Arena.exprGetD pre (UInt64.toNat (preL - 1 - (w - (nIdx + 1))))) a1 = a3
    at hS3 ⊢
  -- `pi_result_f`
  rcases h4 : callW p (n + 1) "pi_result_f" [CWF, r3.headD 0] s3.mem with _ | ⟨r4, m4⟩
  · rw [h4] at hW; simp [motiveLevelW.k_pi_result_f] at hW
  rw [h4] at hW
  obtain ⟨s4, hs4, -, hg4⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (pirF_spec0 p P.pir _ _ _) h4
  rw [hs4] at hg4
  obtain ⟨x4, a4, hrun4, hS4, hgr4, hx4, hd4⟩ := pirF_ok vis fe CWF (r3.headD 0) hx3 _ _ a3 r4 hg4 hS3
  rw [CWF_eq, hd3] at hrun4
  rw [StateT.run_bind, hrun4, except_ok_bind]
  simp only [motiveLevelW.k_pi_result_f] at hW
  have ts : ((decE (r4.headD 0)).tag == ETag.sort) = decide (tagW (r4.headD 0) = 2) :=
    decE_tag_sort_beq (e := r4.headD 0) hx4
  rw [← hd4, ← decE_eq, ts]
  have hg := hgr1.trans (hgr3.trans hgr4)
  by_cases g2 : tagW (r4.headD 0) ≠ 2
  · rw [if_pos g2] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    exact ⟨none, a4, by rw [if_neg (by simpa using g2)]; rfl, hS4, hg, rfl⟩
  rw [if_neg g2] at hW
  have g2 : tagW (r4.headD 0) = 2 := Classical.not_not.mp g2
  rcases h5 : callW p (n + 1) "e_view" [r4.headD 0] m4 with _ | ⟨r5, m5⟩
  · rw [h5] at hW; simp [motiveLevelW.k_e_view_2] at hW
  rw [h5] at hW
  obtain ⟨rfl, hv5, hh5⟩ := eView_sort P.e_view hS4.check.arena.base hx4 g2 h5
  simp only [motiveLevelW.k_e_view_2] at hW
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  rw [if_pos (by simpa using g2), StateT.run_bind, viewSort_run', hv5, except_ok_bind]
  exact ⟨some _, a4, rfl, hS4, hg, rfl, hh5, rfl⟩
end L.Ind
