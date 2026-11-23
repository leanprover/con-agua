module

public import ConAgua.Arena.IotaFrameLift
import ConAgua.Arena.DefEqMidSpine
import ConAgua.Arena.RecClassSpec.IhW
import ConAgua.Arena.RecClassSpec.CloseLams
import ConAgua.Arena.IndSumSpec.DecHLTake
import ConAgua.L.WordOff

@[expose] public section

/-!
# `iota_read_major`, `iota_rec_of` refine `iotaRecMajor`, `iotaRecOf` (lane ronsync8)
-/

open ConRon.Arena
open Std.WP

namespace L.Ind

open L.Arena

theorem viewConst_run' {a : AState} {h : EIdx} :
    (viewConst h).run a = .ok (a.store.viewConst h, a) := rfl

/-- **`e_view` at a `const`**: the memory kept, the twin's `viewConst` the two fields. -/
theorem eView_const {p : Prog} (hp : p.lookup "e_view" = some eView) {n : Nat}
    {m m' : Mem} {a : AState} (hR : ArenaR m a) {h : Word} {r : List Word}
    (h3 : tagW h = 3) (hc : callW p n "e_view" [h] m = some (r, m')) :
    m' = m ∧ a.store.viewConst (decE h) = some (decI (r.tail.headD 0), decI (r.tail.tail.headD 0)) ∧
      HW (r.tail.tail.headD 0) := by
  obtain ⟨rfl, v, hv, hvr, ht⟩ := eView_callW_view hp hR hc
  obtain ⟨rfl, -, h2⟩ := viewR_const hvr (by rw [ht, h3])
  exact ⟨rfl, EStore.viewConst_of_view_r _ _ _ _ hv, h2⟩

/-- **`iota_read_major` refines `iotaRecMajor`**. -/
@[refines ConRon.Arena.iotaRecMajor]
theorem iotaReadMajor_rel {p : Prog} (P : IotaFrameProg p) (n : Nat) (vis : Word) (fe : IFEnv)
    (preO preL domO domL nIdx rP k : Word) (pre doms : List EIdx) (hpl : preL.toNat < 2 ^ 32)
    (hn : nIdx.toNat < 2 ^ 32) (hrP : rP.toNat < 2 ^ 32) :
    RelW (fun m args => callW p n "iota_read_major" args m) [preO, preL, domO, domL, nIdx, rP, k]
      (fun m a => StageR vis fe m a ∧ decHL m preO.toNat preL.toNat = some pre ∧
        preO.toNat + preL.toNat ≤ iwTop m ∧ decHL m domO.toNat domL.toNat = some doms ∧
        domO.toNat + domL.toNat ≤ iwTop m)
      (iotaRecMajor pre doms nIdx.toNat rP.toNat k.toNat) (KeepPost vis fe decOIR) := by
  intro m m' a r hc ⟨hS, hpre, htop, hdoms, htopd⟩
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (iotaReadMajor_specW p P.iota_read_major n _ preO preL domO domL nIdx rP k) hc
  rcases n with _ | n
  · simp [iotaReadMajorW] at hW
  simp only [iotaReadMajorW] at hW
  have hrn : (rP + nIdx).toNat = rP.toNat + nIdx.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨mot, hmot, hj⟩ : ∃ mot : Word, mot.toNat = rP.toNat + nIdx.toNat - k.toNat ∧
      iotaReadMajorW.j1 p n preO preL domO domL nIdx mot m = some (r, s'.mem) := by
    by_cases c : rP + nIdx < k
    · rw [if_pos c] at hW
      refine ⟨0, ?_, hW⟩
      rw [UInt64.lt_iff_toNat_lt, hrn] at c; simp; omega
    · rw [if_neg c] at hW
      refine ⟨_, ?_, hW⟩
      have c' : ¬ (rP + nIdx).toNat < k.toNat := fun h => c (UInt64.lt_iff_toNat_lt.mpr h)
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega), hrn]
  clear hW
  simp only [iotaReadMajorW.j1] at hj
  -- `minors_from`
  rcases h1 : callW p n "minors_from" [preO, preL, mot, 0] m with _ | ⟨r1, m1⟩
  · rw [h1] at hj; simp [iotaReadMajorW.k_minors_from] at hj
  rw [h1] at hj
  obtain ⟨xs1, a1, hrun1, hS1, hg1, hd1⟩ := minorsFrom_rel P n vis fe preO preL mot 0 pre hpl
    m m1 a r1 h1 ⟨hS, hpre, htop⟩
  unfold iotaRecMajor
  rw [UInt64.toNat_zero] at hrun1
  rw [StateT.run_bind, ← hmot, hrun1, except_ok_bind]
  simp only [iotaReadMajorW.k_minors_from] at hj
  -- `expr_get_d`
  rcases n with _ | n
  · simp [iotaReadMajorW.k_expr_get_d, callW_zero] at hj
  rcases h2 : callW p (n + 1) "expr_get_d" [domO, domL, nIdx] m1 with _ | ⟨r2, m2⟩
  · rw [h2] at hj; simp [iotaReadMajorW.k_expr_get_d] at hj
  rw [h2] at hj
  obtain ⟨s2, hs2, -, hok2, hS2, hg2, hx2, hd2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (exprGetD_refines p P.bvar_find P.bvar_push P.intern_bvar P.expr_get_d n ⟨m1, Locals.init []⟩ a1
      (fun _ => none) vis fe domO domL nIdx doms hS1 (decHL_grow' hg1 htopd hdoms)
      (by have := iwTop_lt' m1; have := hg1.iw; omega)) h2
  simp only at hs2 hS2 hg2
  subst hs2
  rw [StateT.run_bind, AM.run_of_ok _ _ hok2, except_ok_bind]
  generalize AM.res (ConRon.Arena.exprGetD doms nIdx.toNat) a1 = x2 at hd2 ⊢
  generalize AM.st (ConRon.Arena.exprGetD doms nIdx.toNat) a1 = a2 at hS2 ⊢
  simp only [iotaReadMajorW.k_expr_get_d] at hj
  -- `get_app_fn_f`
  rcases h3 : callW p (n + 1) "get_app_fn_f" [CWF, r2.headD 0] s2.mem with _ | ⟨r3, m3⟩
  · rw [h3] at hj; simp [iotaReadMajorW.k_get_app_fn_f] at hj
  rw [h3] at hj
  obtain ⟨s3, hs3, -, hg3'⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩) (gafF_spec0 p P.gaf _ _ _) h3
  rw [hs3] at hg3'
  obtain ⟨x3, a3, hrun3, hS3, hg3, hx3, hd3⟩ := gafF_ok vis fe CWF _ hx2 s2.mem m3 a2 r3 hg3' hS2
  rw [CWF_eq, hd2] at hrun3
  rw [StateT.run_bind, hrun3, except_ok_bind]
  simp only [iotaReadMajorW.k_get_app_fn_f] at hj
  have tc : ((decE (r3.headD 0)).tag == ETag.const) = decide (tagW (r3.headD 0) = 3) :=
    decE_tag_beq _ hx3 3 (by decide)
  rw [← hd3, ← decE_eq, tc]
  have hg13 := hg2.trans hg3
  by_cases g3 : tagW (r3.headD 0) ≠ 3
  · rw [if_pos g3] at hj
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hj)
    exact ⟨none, a3, by rw [if_neg (by simpa using g3)]; rfl, hS3, hg1.trans hg13, rfl⟩
  rw [if_neg g3] at hj
  have g3 : tagW (r3.headD 0) = 3 := Classical.not_not.mp g3
  -- `e_view` at the `const`
  rcases h4 : callW p (n + 1) "e_view" [r3.headD 0] m3 with _ | ⟨r4, m4⟩
  · rw [h4] at hj; simp [iotaReadMajorW.k_e_view] at hj
  rw [h4] at hj
  obtain ⟨rfl, hv4, hu4⟩ := eView_const P.e_view hS3.check.arena.base g3 h4
  rw [if_pos (by simpa using g3), StateT.run_bind, viewConst_run', hv4, except_ok_bind]
  dsimp only
  simp only [iotaReadMajorW.k_e_view] at hj
  -- `get_app_args_f`
  rcases h5 : callW p (n + 1) "get_app_args_f" [CWF, r2.headD 0] m4 with _ | ⟨r5, m5⟩
  · rw [h5] at hj; simp [iotaReadMajorW.k_get_app_args_f] at hj
  rw [h5] at hj
  obtain ⟨s5, hs5, -, hg5'⟩ := triple_of_callW (s₀ := ⟨m4, Locals.init []⟩) (gaaF_spec0 p P.gaa _ _ _) h5
  rw [hs5] at hg5'
  obtain ⟨x5, a5, hrun5, hS5, hg5, hd5⟩ := gaaF_ok (fun _ => none) vis fe CWF _ hx2 m4 m5 a3 r5 hg5' hS3
  rw [CWF_eq, hd2] at hrun5
  rw [StateT.run_bind, hrun5, except_ok_bind]
  simp only [iotaReadMajorW.k_get_app_args_f] at hj
  obtain ⟨hargs, hargsb⟩ := hd5
  simp only [L.getD_zero, Nat.zero_add, L.getD_one] at hargs hargsb
  have hlen := decHL_length _ hargs
  obtain ⟨t, ht, hj⟩ : ∃ t : Word, t.toNat = x5.length - nIdx.toNat ∧
      iotaReadMajorW.j2 p (n + 1) preO preL nIdx (r1.headD 0) (r1.tail.headD 0) (r4.tail.tail.headD 0)
        (r5.headD 0) t m5 = some (r, s'.mem) := by
    by_cases c : r5.tail.headD 0 < nIdx
    · rw [if_pos c] at hj
      refine ⟨0, ?_, hj⟩
      have := UInt64.lt_iff_toNat_lt.mp c; simp; omega
    · rw [if_neg c] at hj
      refine ⟨_, ?_, hj⟩
      have : ¬ _ := fun h => c (UInt64.lt_iff_toNat_lt.mpr h)
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]; omega
  simp only [iotaReadMajorW.j2] at hj
  -- `expr_drop_vars_list`
  rcases h6 : callW p (n + 1) "expr_drop_vars_list" [nIdx, r5.headD 0, t] m5 with _ | ⟨r6, m6⟩
  · rw [h6] at hj; simp [iotaReadMajorW.k_expr_drop_vars_list] at hj
  rw [h6] at hj
  obtain ⟨s6, hs6, -, hW6⟩ := triple_of_callW (s₀ := ⟨m5, Locals.init []⟩)
    (edvl_spec p P.drop (n + 1) _ nIdx (r5.headD 0) t) h6
  rw [hs6] at hW6
  obtain ⟨ys, a6, hrun6, hd6, hb6, hS6, hg6⟩ := edvlW_ok P.drop vis fe nIdx (n + 1) m5 m6 a5 (r5.headD 0) t
    (x5.take (x5.length - nIdx.toNat)) r6 hS5 (by rw [ht]; exact decHL_take hargs _ (by omega))
    (by omega) hW6
  rw [StateT.run_bind, hrun6, except_ok_bind]
  simp only [iotaReadMajorW.k_expr_drop_vars_list] at hj
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hj)
  have hg56 := hg5.trans hg6
  have hgall := hg1.trans (hg13.trans hg56)
  refine ⟨_, a6, rfl, hS6, hgall, rfl, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · exact decRL_hl_grow (m := m) hgall ⟨hpre, htop⟩
  · have := decRL_nl_grow (hg13.trans hg56) hd1
    simp only [decRL, L.getD_zero, L.getD_one, List.getD_cons_succ, List.getD_cons_zero,
      Nat.reduceAdd] at this ⊢
    exact this
  · exact hu4
  · rfl
  · exact ⟨hd6, hb6⟩

/-- The first eight words of `r`, rebuilt word by word (`iota_rec_of`'s return). -/
def first8 (r : List Word) : List Word :=
  [r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0,
    r.tail.tail.tail.tail.headD 0, r.tail.tail.tail.tail.tail.headD 0,
    r.tail.tail.tail.tail.tail.tail.headD 0, r.tail.tail.tail.tail.tail.tail.tail.headD 0]

theorem first8_getD (r : List Word) : ∀ i < 8, (first8 r).getD i 0 = r.getD i 0 := by
  intro i hi
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
  all_goals first | omega | skip
  all_goals rcases r with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, t⟩⟩⟩⟩⟩⟩⟩⟩ <;> rfl

/-- `decOIR` reads only the first eight words. -/
theorem decOIR_congr {m : Mem} {r r' : List Word} {x : Option IotaRec}
    (h : ∀ i < 8, r'.getD i 0 = r.getD i 0) (hx : decOIR m r x) : decOIR m r' x := by
  have h0 : r'.headD 0 = r.headD 0 := by rw [← L.getD_zero, ← L.getD_zero, h 0 (by omega)]
  cases x with
  | none => simp only [decOIR] at hx ⊢; rw [h0]; exact hx
  | some x =>
    obtain ⟨h1, ⟨a, b⟩, ⟨c, d⟩, ⟨e, f⟩, ⟨g, k⟩⟩ := hx
    simp only [Nat.reduceAdd] at a b c d e f g k
    refine ⟨h0 ▸ h1, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp only [Nat.reduceAdd] <;>
      rw [h _ (by omega)] <;> (try rw [h _ (by omega)]) <;> assumption

/-- **`iota_rec_of` refines `iotaRecOf`** (`q` the recursor's constant value in `EREC`; the
count words below `2^32`, else `iota_rec_of` aborts). -/
theorem iotaRecOf_rel' {p : Prog} (P : IotaFrameProg p) (n : Nat) (vis : Word) (fe : IFEnv)
    (q mI rP : Word) (cv : IConstantVal) :
    RelW (fun m args => callW p n "iota_rec_of" args m) [q, mI, rP]
      (fun m a => StageR vis fe m a ∧ decCV (erecP m) q.toNat = some cv)
      (iotaRecOf cv mI.toNat rP.toNat) (KeepPost vis fe decOIR) := by
  intro m m' a r hc ⟨hS, hcv⟩
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (iotaRecOf_specW p P.iota_rec_of n _ q mI rP) hc
  rcases n with _ | n
  · simp [iotaRecOfW] at hW
  simp only [iotaRecOfW] at hW
  by_cases hbig : 4294967296 ≤ mI ∨ 4294967296 ≤ rP
  · rw [if_pos hbig] at hW; cases hW
  rw [if_neg hbig] at hW
  have hmI : mI.toNat < 2 ^ 32 := by
    have := fun h => hbig (Or.inl (UInt64.le_iff_toNat_le.mpr h)); simp at this; omega
  have hrP : rP.toNat < 2 ^ 32 := by
    have := fun h => hbig (Or.inr (UInt64.le_iff_toNat_le.mpr h)); simp at this; omega
  obtain ⟨nI, hnI, hj⟩ : ∃ nI : Word, nI.toNat = mI.toNat - rP.toNat ∧
      iotaRecOfW.j1 p n q mI rP nI m = some (r, s'.mem) := by
    by_cases c : mI < rP
    · rw [if_pos c] at hW
      exact ⟨0, by rw [UInt64.lt_iff_toNat_lt] at c; simp; omega, hW⟩
    · rw [if_neg c] at hW
      refine ⟨_, ?_, hW⟩
      have c' : ¬ mI.toNat < rP.toNat := fun h => c (UInt64.lt_iff_toNat_lt.mpr h)
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]
  clear hW
  simp only [iotaRecOfW.j1] at hj
  -- `iota_frame`
  rcases h1 : callW p n "iota_frame" [q, mI, rP] m with _ | ⟨r1, m1⟩
  · rw [h1] at hj; simp [iotaRecOfW.k_iota_frame] at hj
  rw [h1] at hj
  obtain ⟨x1, a1, hrun1, hS1, hg1, hd1⟩ := iotaFrame_rel P n vis fe q mI rP cv hmI hrP m m1 a r1 h1 ⟨hS, hcv⟩
  unfold iotaRecOf
  rw [StateT.run_bind, hrun1, except_ok_bind]
  simp only [iotaRecOfW.k_iota_frame] at hj
  rcases x1 with _ | ⟨pre, doms, body, u⟩
  · simp only [decOF] at hd1
    rw [if_pos hd1] at hj
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hj)
    exact ⟨none, a1, rfl, hS1, hg1, rfl⟩
  obtain ⟨h11, hpl1, hpre, hdoms, hb1, hb2, -⟩ := hd1
  rw [if_neg (by rw [h11]; decide)] at hj
  dsimp only
  simp only [decRL, L.getD_one, L.getD_two, L.getD_three, L.getD_four, Nat.reduceAdd] at hpre hdoms
  have e5 : r1.getD 5 0 = r1.tail.tail.tail.tail.tail.headD 0 := by
    rcases r1 with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, t⟩⟩⟩⟩⟩⟩ <;> rfl
  rw [e5] at hb1 hb2
  -- `get_app_fn_f`
  rcases h3 : callW p n "get_app_fn_f" [CWF, r1.tail.tail.tail.tail.tail.headD 0] m1 with _ | ⟨r3, m3⟩
  · rw [h3] at hj; simp [iotaRecOfW.k_get_app_fn_f] at hj
  rw [h3] at hj
  obtain ⟨s3, hs3, -, hg3'⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩) (gafF_spec0 p P.gaf _ _ _) h3
  rw [hs3] at hg3'
  obtain ⟨x3, a3, hrun3, hS3, hg3, hx3, hd3⟩ := gafF_ok vis fe CWF _ hb1 m1 m3 a1 r3 hg3' hS1
  rw [CWF_eq, ← decE_eq, hb2] at hrun3
  rw [StateT.run_bind, hrun3, except_ok_bind]
  simp only [iotaRecOfW.k_get_app_fn_f] at hj
  dsimp only
  have tb : ((decE (r3.headD 0)).tag == ETag.bvar) = decide (tagW (r3.headD 0) = 0) :=
    decE_tag_beq _ hx3 0 (by decide)
  rw [← hd3, ← decE_eq, tb]
  by_cases g0 : tagW (r3.headD 0) ≠ 0
  · rw [if_pos g0] at hj
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hj)
    exact ⟨none, a3, by rw [if_neg (by simpa using g0)]; rfl, hS3, hg1.trans hg3, rfl⟩
  rw [if_neg g0] at hj
  have g0 : tagW (r3.headD 0) = 0 := Classical.not_not.mp g0
  rcases h4 : callW p n "e_view" [r3.headD 0] m3 with _ | ⟨r4, m4⟩
  · rw [h4] at hj; simp [iotaRecOfW.k_e_view] at hj
  rw [h4] at hj
  obtain ⟨rfl, hv4⟩ := eView_bvar P.e_view hS3.check.arena.base g0 h4
  rw [if_pos (by simpa using g0), StateT.run_bind, viewBVar_run', hv4, except_ok_bind]
  dsimp only
  simp only [iotaRecOfW.k_e_view] at hj
  -- `iota_read_major`
  rcases h5 : callW p n "iota_read_major" [r1.tail.headD 0, r1.tail.tail.headD 0,
      r1.tail.tail.tail.headD 0, r1.tail.tail.tail.tail.headD 0, nI, rP, r4.tail.headD 0] m4 with
    _ | ⟨r5, m5⟩
  · rw [h5] at hj; simp [iotaRecOfW.k_iota_read_major] at hj
  rw [h5] at hj
  simp only [iotaRecOfW.k_iota_read_major] at hj
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hj)
  have hg13 := hg1.trans hg3
  have hpl32 : (r1.tail.tail.headD 0).toNat < 2 ^ 32 := by rw [hpl1]; exact hrP
  obtain ⟨x5, a5, hrun5, hS5, hg5, hd5⟩ := iotaReadMajor_rel P n vis fe _ _ _ _ nI rP _ pre doms
    hpl32 (by omega) hrP m4 _ a3 r5 h5
    ⟨hS3, decHL_grow' hg3 hpre.2 hpre.1, Nat.le_trans hpre.2 hg3.iw,
      decHL_grow' hg3 hdoms.2 hdoms.1, Nat.le_trans hdoms.2 hg3.iw⟩
  rw [hnI] at hrun5
  refine ⟨x5, a5, hrun5, hS5, hg13.trans hg5, ?_⟩
  exact decOIR_congr (first8_getD r5) hd5

end L.Ind
