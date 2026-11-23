module

public import ConAgua.Arena.IotaFrameParts
import ConAgua.Arena.RecLayout.RuleDec
import ConAgua.Arena.ErecRd
import ConAgua.Arena.RecCheckSpec.ErToIwWStage
import ConAgua.Arena.IndSumSpec.ParamLevels
import ConAgua.Arena.IndPosSpec.DpGoW
import ConAgua.Arena.IndMaster
import ConAgua.Arena.IndCopy2
import ConAgua.L.WordOff

@[expose] public section

/-!
# `ctor_levels_at`, `iota_bvars`, `iota_params_at` refine `ctorLevelsAt`, `iotaBVars`,
`iotaParamsAt` (lane ronsync8)
-/

open ConRon.Arena
open Std.WP

namespace L.Ind

open L.Arena

/-- `ctorLevelsAt`'s answer: a level-list handle. -/
def decLsH (_m : Mem) (r : List Word) (x : LsIdx) : Prop := H (r.headD 0) ∧ decI (r.headD 0) = x

/-- **`ctor_levels_at` refines `ctorLevelsAt`**. -/
@[refines ConRon.Arena.ctorLevelsAt]
theorem ctorLevelsAt_rel {p : Prog} (P : IotaFrameProg p) (n : Nat) (vis : Word) (fe : IFEnv)
    (r lpsO lpsL : Word) (rl : IRecRule) (lps : List NIdx) :
    RelW (fun m args => callW p n "ctor_levels_at" args m) [r, lpsO, lpsL]
      (fun m a => StageR vis fe m a ∧ decRule (erecP m) r.toNat = some rl ∧
        decHL m lpsO.toNat lpsL.toNat = some lps ∧ lpsO.toNat + lpsL.toNat ≤ iwTop m)
      (ctorLevelsAt rl lps) (KeepPost vis fe decLsH) := by
  intro m m' a r0 hc ⟨hS, hrl, hlps, htop⟩
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (ctorLevelsAt_specW p P.ctor_levels_at n _ r lpsO lpsL) hc
  rcases n with _ | n
  · simp [ctorLevelsAtW] at hW
  simp only [ctorLevelsAtW] at hW
  rcases decRule_fireE (erRdOK m) hrl with ⟨h0, hf⟩ | ⟨h0, lvls, hf, hsl⟩
  · rw [if_neg (by simpa using h0)] at hW
    rcases h1 : callW p n "param_levels" [lpsO, lpsL] m with _ | ⟨q1, m1⟩
    · rw [h1] at hW; simp [ctorLevelsAtW.k_intern_ls_iw] at hW
    rw [h1] at hW
    simp only [ctorLevelsAtW.k_intern_ls_iw] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨s1, hs1, -, hok, hS1, hg1, hH, hd⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (paramLevels_refines p (P.strip.get "iw_alloc") P.iw_copy P.sl_cons P.sl_get P.param_find
        P.param_push P.intern_param P.param_levels_go P.param_levels P.il n _ a (fun _ => none) vis fe
        lpsO lpsL lps hS hlps (by have := iwTop_lt' m; omega) htop) h1
    simp only at hs1 hS1 hg1
    rw [hs1] at hS1 hg1
    refine ⟨_, _, ?_, hS1, hg1, hH, hd⟩
    unfold ctorLevelsAt
    rw [hf]
    exact AM.run_of_ok _ _ hok
  rw [if_pos h0] at hW
  rcases h1 : callW p n "er_to_iw" [erRd m (r + Rule.lvlsOff), erRd m (r + Rule.lvlsLen)] m with
    _ | ⟨q1, m1⟩
  · rw [h1] at hW; simp [ctorLevelsAtW.k_er_to_iw] at hW
  rw [h1] at hW
  obtain ⟨s1, rfl, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (erToIw_specW p (P.strip.get "iw_alloc") P.er_copy P.er_to_iw n _ _ _) h1
  obtain ⟨hS1, hg1, hd1, -, -⟩ := erToIwW_stage hW1 hS hsl
  simp only [ctorLevelsAtW.k_er_to_iw] at hW
  rcases h2 : callW p n "intern_ls_iw" [q1.headD 0, q1.tail.headD 0] s1.mem with _ | ⟨q2, m2⟩
  · rw [h2] at hW; simp [ctorLevelsAtW.k_intern_ls_iw] at hW
  rw [h2] at hW
  simp only [ctorLevelsAtW.k_intern_ls_iw] at hW
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨s2, hs2, -, hW2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩) (ilF_spec p P.il n _ _) h2
  rw [hs2] at hW2
  obtain ⟨x2, a2, hrun2, hS2, hg2, hd2⟩ := ilF_ok vis fe _ _ lvls s1.mem _ a q2 hW2 ⟨hS1, hd1⟩
  refine ⟨x2, a2, ?_, hS2, hg1.trans hg2, hd2⟩
  unfold ctorLevelsAt
  rcases hf with hf | ⟨pins, hf⟩ <;> rw [hf] <;> exact hrun2

/-- **`iota_bvars`' loop against the twin's recursion**. -/
theorem iotaBVars_loop {p : Prog} (P : IotaFrameProg p) (vis : Word) (fe : IFEnv)
    (rP nn o : Word) (m₀ : Mem) (hnr : nn.toNat ≤ rP.toNat) (ho : iwTop m₀ ≤ o.toNat) :
    ∀ (k : Nat) (m m' : Mem) (a : AState) (i : Word) (ps : List EIdx),
      iotaBVarsW.loop1 p k m rP nn o i = some m' →
      StageR vis fe m a → IWGrow m₀ m → i.toNat ≤ nn.toNat →
      o.toNat + nn.toNat ≤ iwTop m → decHL m o.toNat i.toNat = some ps →
      ∃ xs a', (iotaBVars rP.toNat nn.toNat i.toNat).run a = .ok (xs, a') ∧
        StageR vis fe m' a' ∧ IWGrow m₀ m' ∧ decHL m' o.toNat nn.toNat = some (ps ++ xs) ∧
        o.toNat + nn.toNat ≤ iwTop m' := by
  intro k
  induction k with
  | zero => intro m m' a i ps hl; rw [iotaBVarsW.loop1.eq_1] at hl; cases hl
  | succ k ih =>
  intro m m' a i ps hl hS hg hin hb hps
  have hT := iwTop_lt' m
  by_cases hi : i < nn
  · rw [iotaBVarsW.loop1.arm1 _ _ _ _ _ _ _ hi] at hl
    have hi' : i.toNat < nn.toNat := UInt64.lt_iff_toNat_lt.mp hi
    rcases h1 : callW p k "intern_bvar" [rP - 1 - i] m with _ | ⟨r1, m1⟩
    · rw [h1, iotaBVarsW.k_intern_bvar.none] at hl; cases hl
    by_cases hbig : 4294967296 ≤ r1.headD 0
    · rw [h1, iotaBVarsW.k_intern_bvar.abort1 _ _ _ _ _ _ _ _ hbig] at hl; cases hl
    rw [h1, iotaBVarsW.k_intern_bvar.arm1 _ _ _ _ _ _ _ _ hbig] at hl
    have hH1 : H (r1.headD 0) := by
      have : ¬ (4294967296 : Nat) ≤ (r1.headD 0).toNat := hbig; show _ < _; omega
    obtain ⟨s1, rfl, -, hm⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (internBVar_spec (p := p) P.bvar_find P.bvar_push P.intern_bvar k _ (rP - 1 - i)) h1
    obtain ⟨a1, hrun1, hS1, hg1⟩ := internBVar_stage hS (rP - 1 - i) hm
    have hri : (rP - 1 - i).toNat = rP.toNat - 1 - i.toNat := by
      have e1 : (rP - 1).toNat = rP.toNat - 1 := by
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, e1]; omega), e1]
    have hps1 : decHL s1.mem o.toNat i.toNat = some ps := decHL_grow' hg1 (by omega) hps
    have hi1 : (i + 1).toNat = i.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; omega
    have hsz : o.toNat + i.toNat < (s1.mem.arr64 IW).size := by
      have := hS1.iw.iw; have := hg1.iw; omega
    have hps2 := decHL_write s1.mem o i (r1.headD 0) ps hH1 hS1.iw.iwSize hsz hps1
    rw [← hi1] at hps2
    have hoi : (o + i).toNat = o.toNat + i.toNat := by
      rw [UInt64.toNat_add]; have := hg1.iw; have := iwTop_lt' s1.mem; exact Nat.mod_eq_of_lt (by omega)
    have hg2 : IWGrow m₀ (s1.mem.set64 IW (o + i) (r1.headD 0)) :=
      (hg.trans hg1).set_iw _ _ (by rw [hoi]; have := hg.iw; omega)
    obtain ⟨xs, a', hrun, hS', hg', hd', hb'⟩ := ih _ m' a1 (i + 1) (ps ++ [decI (r1.headD 0)]) hl
      (hS1.set_iw _ _) hg2 (by omega) (by rw [iwTop_set64IW]; have := hg1.iw; omega) hps2
    rw [hi1] at hrun
    refine ⟨decI (r1.headD 0) :: xs, a', ?_, hS', hg', by simpa using hd', hb'⟩
    rw [iotaBVars.eq_def, if_pos hi']
    rw [hri] at hrun1
    have hrun1' : (internBVarE (rP.toNat - 1 - i.toNat)).run a = .ok (decE (r1.headD 0), a1) := hrun1
    rw [StateT.run_bind, hrun1', except_ok_bind, StateT.run_bind, hrun, except_ok_bind]
    rfl
  · rw [iotaBVarsW.loop1.arm2 _ _ _ _ _ _ _ hi] at hl
    cases hl
    have hin' : ¬ i.toNat < nn.toNat := fun h => hi (UInt64.lt_iff_toNat_lt.mpr h)
    have hjf : i.toNat = nn.toNat := by omega
    refine ⟨[], a, ?_, hS, hg, by rw [← hjf]; simpa using hps, hb⟩
    rw [iotaBVars.eq_def, if_neg hin']; rfl

/-- **`iota_bvars` refines `iotaBVars … 0`** (at most `rP` variables). -/
@[refines ConRon.Arena.iotaBVars]
theorem iotaBVars_rel {p : Prog} (P : IotaFrameProg p) (n : Nat) (vis : Word) (fe : IFEnv)
    (rP nn : Word) (hnr : nn.toNat ≤ rP.toNat) :
    RelW (fun m args => callW p n "iota_bvars" args m) [rP, nn] (StageR vis fe)
      (iotaBVars rP.toNat nn.toNat 0) (KeepPost vis fe (decRL (fun m => decHL m) 0)) := by
  intro m m' a r hc hS
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (iotaBVars_specW p P.iota_bvars n _ rP nn) hc
  rcases n with _ | n
  · simp [iotaBVarsW] at hW
  simp only [iotaBVarsW] at hW
  by_cases hq : nn = 0
  · rw [if_pos hq] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    subst hq
    refine ⟨[], a, ?_, hS, IWGrow.refl _, by simp [decHL, hslice?], by simp⟩
    rw [iotaBVars.eq_def, if_neg (by simp)]; rfl
  rw [if_neg hq] at hW
  rcases ha : callW p n "iw_alloc" [nn] m with _ | ⟨r1, m1⟩
  · rw [ha] at hW; simp [iotaBVarsW.k_iw_alloc] at hW
  rw [ha] at hW
  simp only [iotaBVarsW.k_iw_alloc] at hW
  obtain ⟨s1, rfl, -, ha1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (iwAlloc_specW p (P.strip.get "iw_alloc") n _ _) ha
  obtain ⟨hS1, hg1, ho1, ht1⟩ := allocW_stage ha1 hS
  rcases hl : iotaBVarsW.loop1 p (n + 1) s1.mem rP nn (r1.headD 0) 0 with _ | m2
  · rw [hl] at hW; cases hW
  rw [hl] at hW
  simp only [iotaBVarsW.k_loop1] at hW
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨xs, a', hrun, hS', hg', hd', hb'⟩ := iotaBVars_loop P vis fe rP nn (r1.headD 0)
    m hnr (Nat.le_of_eq ho1.symm) (n + 1) s1.mem _ a 0 [] hl hS1 hg1 (by simp)
    (by rw [ht1, ho1]; exact Nat.le_refl _) (by simp [decHL, hslice?])
  exact ⟨xs, a', by simpa using hrun, hS', hg', by simpa using hd', hb'⟩

/-- **`iota_params_at` refines `iotaParamsAt`**. -/
@[refines ConRon.Arena.iotaParamsAt]
theorem iotaParamsAt_rel {p : Prog} (P : IotaFrameProg p) (n : Nat) (vis : Word) (fe : IFEnv)
    (r rP cnP : Word) (rl : IRecRule) :
    RelW (fun m args => callW p n "iota_params_at" args m) [r, rP, cnP]
      (fun m a => StageR vis fe m a ∧ decRule (erecP m) r.toNat = some rl)
      (iotaParamsAt rl rP.toNat cnP.toNat) (KeepPost vis fe (decRL (fun m => decHL m) 0)) := by
  intro m m' a r0 hc ⟨hS, hrl⟩
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (iotaParamsAt_specW p P.iota_params_at n _ r rP cnP) hc
  rcases n with _ | n
  · simp [iotaParamsAtW] at hW
  simp only [iotaParamsAtW] at hW
  obtain ⟨-, -, -, -, hn1, -, -, -⟩ := decRule_rd (erRdOK m) hrl
  by_cases h1 : erRd m (r + Rule.fire) = 1
  · rw [if_pos h1] at hW
    obtain ⟨lv, pins, hf, -, hsl⟩ := hn1 h1
    rcases h2 : callW p n "er_to_iw" [erRd m (r + Rule.pinsOff), erRd m (r + Rule.pinsLen)] m with
      _ | ⟨q1, m1⟩
    · rw [h2] at hW; simp [iotaParamsAtW.k_er_to_iw] at hW
    rw [h2] at hW
    simp only [iotaParamsAtW.k_er_to_iw] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (erToIw_specW p (P.strip.get "iw_alloc") P.er_copy P.er_to_iw n _ _ _) h2
    rw [hs1] at hW1
    obtain ⟨hS1, hg1, hd1, ht1, -⟩ := erToIwW_stage hW1 hS hsl
    refine ⟨pins, a, ?_, hS1, hg1, by simpa using hd1,
      by show (q1.headD 0).toNat + (q1.tail.headD 0).toNat ≤ _; omega⟩
    unfold iotaParamsAt; rw [hf]; rfl
  rw [if_neg h1] at hW
  have hnn := decRule_notNested (erRdOK m) hrl h1
  obtain ⟨k, hk, hj⟩ : ∃ k : Word, k.toNat = min cnP.toNat rP.toNat ∧
      iotaParamsAtW.j1 p n rP k m = some (r0, s'.mem) := by
    by_cases c : rP < cnP
    · rw [if_pos c] at hW
      exact ⟨rP, by rw [UInt64.lt_iff_toNat_lt] at c; omega, hW⟩
    · rw [if_neg c] at hW
      exact ⟨cnP, by have : ¬ _ := fun h => c (UInt64.lt_iff_toNat_lt.mpr h); omega, hW⟩
  simp only [iotaParamsAtW.j1] at hj
  rcases h2 : callW p n "iota_bvars" [rP, k] m with _ | ⟨q1, m1⟩
  · rw [h2] at hj; simp [iotaParamsAtW.k_er_to_iw] at hj
  rw [h2] at hj
  simp only [iotaParamsAtW.k_er_to_iw] at hj
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hj)
  obtain ⟨xs, a1, hrun, hS1, hg1, hd1⟩ := iotaBVars_rel P n vis fe rP k (by omega) m _ a q1 h2 hS
  refine ⟨xs, a1, ?_, hS1, hg1, ?_⟩
  · unfold iotaParamsAt
    rw [← hk]
    rcases hnn with hf | ⟨lv, hf⟩ <;> rw [hf] <;> exact hrun
  · simp only [decRL, Nat.zero_add, L.getD_zero, L.getD_one, List.getD_cons_succ, List.getD_cons_zero] at hd1 ⊢
    exact hd1

end L.Ind
