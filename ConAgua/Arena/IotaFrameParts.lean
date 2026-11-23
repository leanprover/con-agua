module

public import ConAgua.Arena.IotaFrameMajor
import ConAgua.Arena.RecLayout.RuleDec
import ConAgua.Arena.RecGenSpec.DecNLAt
import ConAgua.Arena.RecClassSpec.CloseLams
import ConAgua.Arena.IndSumSpec.DecHLTake
import ConAgua.L.WordOff

@[expose] public section

/-!
# `iota_parts_of_at` refines `iotaPartsOfAt` (lane ronsync8)
-/

open ConRon.Arena
open Std.WP

namespace L.Ind

open L.Arena

/-- A rule's field count, read at any later memory. -/
theorem rule_nfields_at {m m' : Mem} (hg : IWGrow m m') {r : Word} {rl : IRecRule}
    (h : decRule (erecP m) r.toNat = some rl) : (erRd m' (r + Rule.nfields)).toNat = rl.nfields :=
  (decRule_rd (erRdOK m') (hg.ext.decRule h)).2.2.1.symm

/-- Word `i` of a decoded number slice. -/
theorem decNL_rdW {m : Mem} {o l i : Word} {xs : List Nat} (h : decNL m o.toNat l.toNat = some xs)
    (hi : i.toNat < l.toNat) (hb : o.toNat + l.toNat < 2 ^ 64) :
    (rdW (m.arr64 IW) (o + i)).toNat = xs.getD i.toNat 0 := by
  have hoi : (o + i).toNat = o.toNat + i.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have := decNL_at h i.toNat hi
  simp only [iwN, nat?, iwA, aread_apply] at this
  have hlt : i.toNat < xs.length := by rw [decNL_length m h]; exact hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
  cases hx : (m.arr64 IW)[o.toNat + i.toNat]? with
  | none => rw [hx] at this; cases this
  | some v =>
    rw [hx] at this
    simp only [Option.map_some, Option.some.injEq] at this
    simp [rdW, hoi, hx, this]

/-- **`iota_parts_of_at` refines `iotaPartsOfAt`**. -/
theorem iotaPartsOfAt_rel' {p : Prog} (P : IotaFrameProg p) (n : Nat) (vis : Word) (fe : IFEnv)
    (r1 r2 r3 r4 r5 r6 r7 rP nIdx i r : Word) (rr : IotaRec) (rl : IRecRule) :
    RelW (fun m args => callW p n "iota_parts_of_at" args m) [r1, r2, r3, r4, r5, r6, r7, rP, nIdx, i, r]
      (fun m a => StageR vis fe m a ∧ decIRAt 0 m [r1, r2, r3, r4, r5, r6, r7] rr ∧
        decRule (erecP m) r.toNat = some rl)
      (iotaPartsOfAt rr rP.toNat nIdx.toNat i.toNat rl) (KeepPost vis fe decOIP) := by
  intro m m' a r0 hc ⟨hS, hrr, hrl⟩
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (iotaPartsOfAt_specW p P.iota_parts_of_at n _ r1 r2 r3 r4 r5 r6 r7 rP nIdx i r) hc
  obtain ⟨⟨hpre, hpreb⟩, ⟨hmin, hminb⟩, ⟨hus, husd⟩, ⟨hpar, hparb⟩⟩ := hrr
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.reduceAdd, Nat.zero_add] at hpre hpreb hmin hminb hus husd hpar hparb
  have hT := iwTop_lt' m
  rcases n with _ | n
  · simp [iotaPartsOfAtW] at hW
  simp only [iotaPartsOfAtW] at hW
  by_cases hbig : 4294967296 ≤ rP ∨ 4294967296 ≤ nIdx ∨ 4294967296 ≤ erRd m (r + Rule.nfields)
  · rw [ite_eq_left hbig] at hW; cases hW
  rw [ite_eq_right hbig] at hW
  have hrP : rP.toNat < 2 ^ 32 := by
    have := fun h => hbig (Or.inl (UInt64.le_iff_toNat_le.mpr h)); simp at this; omega
  have hnI : nIdx.toNat < 2 ^ 32 := by
    have := fun h => hbig (Or.inr (Or.inl (UInt64.le_iff_toNat_le.mpr h))); simp at this; omega
  have hnf0 := rule_nfields_at (IWGrow.refl m) hrl
  have hnf : rl.nfields < 2 ^ 32 := by
    have := fun h => hbig (Or.inr (Or.inr (UInt64.le_iff_toNat_le.mpr h))); simp at this; omega
  have hml := decNL_length m hmin
  unfold iotaPartsOfAt
  by_cases hi : r4 ≤ i
  · rw [ite_eq_left hi] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have : ¬ i.toNat < rr.minors.length := by rw [hml]; rw [UInt64.le_iff_toNat_le] at hi; omega
    exact ⟨none, a, by rw [ite_eq_right this]; rfl, hS, IWGrow.refl _, rfl⟩
  rw [ite_eq_right hi] at hW
  have hi' : i.toNat < r4.toNat := by rw [UInt64.le_iff_toNat_le] at hi; omega
  rw [ite_eq_left (by rw [hml]; exact hi')]
  dsimp only
  have hqq := decNL_rdW hmin hi' (by omega)
  generalize hqw : rdW (m.arr64 IW) (r3 + i) = qq at hW hqq
  -- `expr_get_d`
  rcases n with _ | n
  · simp [iotaPartsOfAtW.k_expr_get_d, callW_zero] at hW
  rcases h1 : callW p (n + 1) "expr_get_d" [r1, r2, qq] m with _ | ⟨q1, m1⟩
  · rw [h1] at hW; simp [iotaPartsOfAtW.k_expr_get_d] at hW
  rw [h1] at hW
  obtain ⟨s1, hs1, -, hok1, hS1, hg1, hx1, hd1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (exprGetD_refines p P.bvar_find P.bvar_push P.intern_bvar P.expr_get_d n ⟨m, Locals.init []⟩ a
      (fun _ => none) vis fe r1 r2 qq rr.pre hS hpre (by omega)) h1
  simp only at hs1 hS1 hg1
  subst hs1
  rw [StateT.run_bind, ← hqq, AM.run_of_ok _ _ hok1, except_ok_bind]
  generalize AM.res (ConRon.Arena.exprGetD rr.pre qq.toNat) a = x1 at hd1 ⊢
  generalize AM.st (ConRon.Arena.exprGetD rr.pre qq.toNat) a = a1 at hS1 ⊢
  simp only [iotaPartsOfAtW.k_expr_get_d] at hW
  -- `strip_pis`
  rcases h2 : callW p (n + 1) "strip_pis" [erRd s1.mem (r + Rule.nfields), q1.headD 0] s1.mem with
    _ | ⟨q2, m2⟩
  · rw [h2] at hW; simp [iotaPartsOfAtW.k_strip_pis] at hW
  rw [h2] at hW
  have hs2 := stripF_of_callW P.strip h2
  obtain ⟨x2, a2, hrun2, hS2, hg2, hd2⟩ := stripF_pis_ok vis fe _ _ hx1 s1.mem m2 a1 q2 hs2 hS1
  rw [rule_nfields_at hg1 hrl, hd1] at hrun2
  rw [StateT.run_bind, hrun2, except_ok_bind]
  simp only [iotaPartsOfAtW.k_strip_pis] at hW
  rcases x2 with _ | ⟨fd, inner⟩
  · simp only [decOLE] at hd2
    rw [ite_eq_left hd2] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    exact ⟨none, a2, rfl, hS2, hg1.trans hg2, rfl⟩
  obtain ⟨h21, hfd, hinner⟩ := hd2
  rw [ite_eq_right (by rw [h21]; decide)] at hW
  dsimp only
  simp only [decW0E, headD_drop3] at hinner
  simp only [decRL, L.getD_one, L.getD_two, Nat.reduceAdd] at hfd
  obtain ⟨amt, hamt, hj⟩ : ∃ amt : Word, amt.toNat = rP.toNat - qq.toNat ∧
      iotaPartsOfAtW.j1 p (n + 1) r5 r6 r7 nIdx r (q2.tail.headD 0) (q2.tail.tail.headD 0)
        (q2.tail.tail.tail.headD 0) amt m2 = some (r0, s'.mem) := by
    by_cases c : rP < qq
    · rw [ite_eq_left c] at hW
      exact ⟨0, by rw [UInt64.lt_iff_toNat_lt] at c; simp; omega, hW⟩
    · rw [ite_eq_right c] at hW
      refine ⟨_, ?_, hW⟩
      have c' : ¬ rP.toNat < qq.toNat := fun h => c (UInt64.lt_iff_toNat_lt.mpr h)
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]
  clear hW
  simp only [iotaPartsOfAtW.j1] at hj
  -- `lift_field_doms`
  rcases h3 : callW p (n + 1) "lift_field_doms" [amt, q2.tail.headD 0, q2.tail.tail.headD 0] m2 with
    _ | ⟨q3, m3⟩
  · rw [h3] at hj; simp [iotaPartsOfAtW.k_lift_field_doms] at hj
  rw [h3] at hj
  obtain ⟨x3, a3, hrun3, hS3, hg3, hd3⟩ := liftFieldDoms_rel P (n + 1) vis fe amt _ _ fd m2 m3 a2 q3 h3
    ⟨hS2, hfd.1, hfd.2⟩
  rw [hamt] at hrun3
  rw [StateT.run_bind, hrun3, except_ok_bind]
  simp only [iotaPartsOfAtW.k_lift_field_doms] at hj
  -- `pi_tele`
  rcases h4 : callW p (n + 1) "pi_tele" [q2.tail.tail.tail.headD 0] m3 with _ | ⟨q4, m4⟩
  · rw [h4] at hj; simp [iotaPartsOfAtW.k_pi_tele] at hj
  rw [h4] at hj
  obtain ⟨x4, a4, hrun4, hS4, hg4, hn4, hh4, hb4, -⟩ :=
    piTele_rel P.pi_tele P.e_view (n + 1) vis fe _ hinner.1 m3 m4 a3 q4 h4 hS3
  rw [decE_eq, hinner.2] at hrun4
  rw [StateT.run_bind, hrun4, except_ok_bind]
  simp only [iotaPartsOfAtW.k_pi_tele] at hj
  -- `get_app_args_f`
  rcases h5 : callW p (n + 1) "get_app_args_f" [CWF, q4.tail.headD 0] m4 with _ | ⟨q5, m5⟩
  · rw [h5] at hj; simp [iotaPartsOfAtW.k_get_app_args_f] at hj
  rw [h5] at hj
  obtain ⟨s5, hs5, -, hg5'⟩ := triple_of_callW (s₀ := ⟨m4, Locals.init []⟩) (gaaF_spec0 p P.gaa _ _ _) h5
  rw [hs5] at hg5'
  obtain ⟨x5, a5, hrun5, hS5, hg5, hd5⟩ := gaaF_ok (fun _ => none) vis fe CWF _ hh4 m4 m5 a4 q5 hg5' hS4
  rw [CWF_eq, ← decE_eq, hb4] at hrun5
  rw [StateT.run_bind, hrun5, except_ok_bind]
  simp only [iotaPartsOfAtW.k_get_app_args_f] at hj
  obtain ⟨hargs, hargsb⟩ := hd5
  simp only [L.getD_zero, Nat.zero_add, L.getD_one] at hargs hargsb
  have hlen := decHL_length _ hargs
  obtain ⟨al, hal, hj⟩ : ∃ al : Word, al.toNat = min nIdx.toNat x5.length ∧
      iotaPartsOfAtW.j2 p (n + 1) r5 r6 r7 r amt (q3.headD 0) (q3.tail.headD 0) (q4.headD 0)
        (q5.headD 0) al m5 = some (r0, s'.mem) := by
    by_cases c : nIdx < q5.tail.headD 0
    · rw [ite_eq_left c] at hj
      exact ⟨nIdx, by rw [UInt64.lt_iff_toNat_lt] at c; omega, hj⟩
    · rw [ite_eq_right c] at hj
      exact ⟨_, by have : ¬ _ := fun h => c (UInt64.lt_iff_toNat_lt.mpr h); omega, hj⟩
  simp only [iotaPartsOfAtW.j2] at hj
  -- `lift_idx_args`
  have hg15 := hg1.trans (hg2.trans (hg3.trans (hg4.trans hg5)))
  rcases h6 : callW p (n + 1) "lift_idx_args" [amt, q4.headD 0, erRd m5 (r + Rule.nfields),
      q5.headD 0, al] m5 with _ | ⟨q6, m6⟩
  · rw [h6] at hj; simp [iotaPartsOfAtW.k_lift_idx_args] at hj
  rw [h6] at hj
  have htake : decHL m5 (q5.headD 0).toNat al.toNat = some (x5.take nIdx.toNat) := by
    rw [decHL_take hargs al.toNat (by rw [hal]; omega)]
    congr 1
    rw [hal]
    by_cases hle : nIdx.toNat ≤ x5.length
    · rw [Nat.min_eq_left hle]
    · rw [Nat.min_eq_right (by omega), List.take_of_length_le (Nat.le_refl _),
        List.take_of_length_le (by omega)]
  obtain ⟨x6, a6, hrun6, hS6, hg6, hd6⟩ := liftIdxArgs_rel P (n + 1) vis fe amt _ _ _ al _ m5 m6 a5 q6 h6
    ⟨hS5, htake, by omega⟩
  rw [hamt, hn4, rule_nfields_at hg15 hrl] at hrun6
  rw [StateT.run_bind, hrun6, except_ok_bind]
  simp only [iotaPartsOfAtW.k_lift_idx_args] at hj
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hj)
  have hg36 := hg4.trans (hg5.trans hg6)
  have hgall := hg15.trans hg6
  refine ⟨_, a6, rfl, hS6, hgall, rfl, ?_, ?_, ⟨hus, husd⟩, ?_⟩
  · have := decRL_hl_grow hg36 hd3
    simp only [decRL, L.getD_zero, L.getD_one, List.getD_cons_succ, List.getD_cons_zero,
      Nat.reduceAdd] at this ⊢
    exact this
  · have := hd6
    simp only [decRL, L.getD_zero, L.getD_one, List.getD_cons_succ, List.getD_cons_zero,
      Nat.reduceAdd] at this ⊢
    exact this
  · simp only [decRL, List.getD_cons_succ, List.getD_cons_zero, Nat.reduceAdd]
    exact ⟨decHL_grow' hgall hparb hpar, Nat.le_trans hparb hgall.iw⟩

end L.Ind
