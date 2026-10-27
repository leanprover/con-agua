import ConAgua.Arena.Verdict
import ConAgua.Checker.NoVerdictFns
import ConRon.Bridge.Inductives.Decl
import ConAgua.Arena.IndSumSpec.ParamLevels
import ConAgua.Arena.RecGenSpec.SlRGrow

/-!
# Error refinement of `target_major_of_member` (lane `verdicts-b`, helper `ib`)

Mirrors `tmmW_sim` (`RecGenSpec16`): the aborts are the twin's `unwrapOr` internals, the two
rejects the twin's final `fail`; `block_shape_lps`, `param_levels`, `sl_eq`, `mk_target_major`
are `closedNV`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dMajor)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model tmmE_spec (p : Prog) (hf : p.lookup "target_major_of_member" = some targetMajorOfMember)
  fns [hf ↦ tmmE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors

theorem map_decI_inj' {k : IdxKind} : ∀ (ws1 ws2 : List Word), (∀ w ∈ ws1, w.toNat < 2 ^ 32) →
    (∀ w ∈ ws2, w.toNat < 2 ^ 32) → ws1.map (decI : Word → Idx k) = ws2.map decI → ws1 = ws2
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: as, b :: bs, h1, h2, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    have hab := decI_inj (h1 a (by simp)) (h2 b (by simp)) h.1
    rw [hab, map_decI_inj' as bs (fun w hw => h1 w (by simp [hw])) (fun w hw => h2 w (by simp [hw])) h.2]

section sims
variable {p : Prog} (hP : TmmProg p) (hnv : closedNV p _root_.L.Checker.nvFns = true) {env : ConLeche.Env}
  {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

include hP hnv in
theorem tmmE_claim (n : Nat) {m : Mem} {a : AState} {pp cao cal pfo pfl fvo fvl ao al I us t : Word}
    {bs : BlockShape} {css : List (List (IConstantVal × Nat))} {pfvs fvs args : List EIdx}
    (hS : StageR dn vis fe m a) (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    (hcss : PSlR decCNS css cao cal m) (_hpf : DecB (fun m => decHL m pfo.toNat pfl.toNat) m pfvs)
    (hfv : DecB (fun m => decHL m fvo.toNat fvl.toNat) m fvs) (hfvb : fvo.toNat + fvl.toNat ≤ iwTop m)
    (hag : DecB (fun m => decHL m ao.toNat al.toNat) m args) (hagb : ao.toNat + al.toNat ≤ iwTop m)
    (_hI : H I) (hus : H us) (_hPm : PosMR m) :
    ∀ e, tmmE p (n + 1) m pp cao cal pfo pfl fvo fvl ao al I us t = .error e →
      ErrClaim (tmoMemT bs css pfvs fvs args (decI I) (decI us) t.toNat) a e := by
  intro e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hT : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hq hsrc
  have hqt : decBS (truncM m) pp.toNat = some bs := hq
  obtain ⟨hmem, -, -, -, -, -, -⟩ := decBS_some hqt
  obtain ⟨mo, ml, hmo, hml, hmd, -⟩ := partsAt decMS_mono hmem
  obtain ⟨hw0, -, -⟩ := partsIwRd hmo (w := pp) rfl
  obtain ⟨hw1, -, -⟩ := partsIwRd hml (w := pp + 1) (by rw [UInt64.toNat_add]; simp; omega)
  rw [UInt64.ofNat_toNat] at hw0 hw1
  obtain ⟨hnpw, hnpb, -, -⟩ := partsShapeWords (IWGrow.refl m) hq hq9
  by_cases h1 : rdW (m.arr64 IW) (pp + 1) ≤ t
  · rw [tmmE.abort1 p n m pp cao cal pfo pfl fvo fvl ao al I us t h1] at he
    cases he; exact absurd (by decide) hk0
  by_cases h2 : cal ≤ t
  · rw [tmmE.abort2 p n m pp cao cal pfo pfl fvo fvl ao al I us t h1 h2] at he
    cases he; exact absurd (by decide) hk0
  rw [tmmE.arm1 p n m pp cao cal pfo pfl fvo fvl ao al I us t h1 h2] at he
  rw [hw1] at h1
  have htl : t.toNat < ml.toNat := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp h1)
  have htc : t.toNat < cal.toNat := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp h2)
  have hmd' : decPL (truncM m) (decMS (truncM m)) mo.toNat ml.toNat = some bs.members := hmd
  obtain ⟨hlenM, -⟩ := pos2_decPL_trunc hmd'
  have hcd : decPL (truncM m) (decCNS (truncM m)) cao.toNat cal.toNat = some css := hcss.1
  obtain ⟨hlenC, -⟩ := pos2_decPL_trunc hcd
  have hvtl : t.toNat < bs.members.length := by omega
  have hvcl : t.toNat < css.length := by omega
  unfold tmoMemT
  simp only [List.getElem?_eq_getElem hvtl, List.getElem?_eq_getElem hvcl, unwrapOr, pure_bind]
  -- `block_shape_lps`
  cases h3 : callE p n "block_shape_lps" [pp] m with
  | error e3 =>
    rw [h3, tmmE.k_block_shape_lps.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h3
  | ok q3 =>
  obtain ⟨r1, m1⟩ := q3
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockShapeLps_spec p hP.alloc hP.erCopy hP.erToIw hP.lps n _ pp) (callW_of_callE h3)
  obtain ⟨hS1, hg1, hlps1, htop1⟩ := lpsW_ok' hW1 hS hq
  have hT1 : iwTop s1.mem < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1
  subst hs1
  rw [h3, tmmE.k_block_shape_lps.arm1] at he
  -- `param_levels`
  cases h4 : callE p n "param_levels" [r1.headD 0, r1.tail.headD 0] s1.mem with
  | error e4 =>
    rw [h4, tmmE.k_param_levels.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h4
  | ok q4 =>
  obtain ⟨r2, m2⟩ := q4
  obtain ⟨s2', hs2', -, hok, hS2, hg2, hH2, hd2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (paramLevels_refines p hP.alloc hP.copy hP.cons hP.get hP.pfind hP.ppush hP.iparam hP.plgo hP.pl hP.il n _ a dn
      vis fe _ _ _ hS1 hlps1 (by omega) htop1) (callW_of_callE h4)
  rw [hs2'] at hS2 hg2
  subst hs2'
  have hg02 := hg1.trans hg2
  refine ErrClaim.bind_right (partsRunOfOk hok) ?_
  -- the parameter prefixes
  have hnpe : (UInt64.ofNat bs.nP : Word).toNat = bs.nP := UInt64.toNat_ofNat_of_lt' hnpb
  have hmin : ∀ x : Word, (if UInt64.ofNat bs.nP < x then UInt64.ofNat bs.nP else x).toNat = min bs.nP x.toNat := by
    intro x
    have := @UInt64.lt_iff_toNat_lt (UInt64.ofNat bs.nP) x
    split <;> rename_i hx <;> simp only [hx, hnpe, true_iff, false_iff] at this ⊢ <;> omega
  have hagT : decHL (truncM m) ao.toNat al.toNat = some args := hag
  have hfvT : decHL (truncM m) fvo.toNat fvl.toNat = some fvs := hfv
  have hal := decHL_length _ hagT
  have hfl := decHL_length _ hfvT
  have htakeA : DecB (fun m => decHL m ao.toNat (min bs.nP al.toNat)) m (args.take bs.nP) := by
    show decHL (truncM m) _ _ = _
    rw [decHL_take hagT _ (Nat.min_le_right _ _)]
    congr 1; exact take_min_len _ _ _ hal
  have htakeF : DecB (fun m => decHL m fvo.toNat (min bs.nP fvl.toNat)) m (fvs.take bs.nP) := by
    show decHL (truncM m) _ _ = _
    rw [decHL_take hfvT _ (Nat.min_le_right _ _)]
    congr 1; exact take_min_len _ _ _ hfl
  have hj : tmmE.k_param_levels p n pfo pfl fvo fvl ao al I us t
      (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) pp + t) + 1))
      (rdW (m.arr64 IW) (rdW (m.arr64 IW) (cao + t))) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (cao + t) + 1))
      (rdW (m.arr64 IW) (pp + 4)) (Except.ok (r2, s2'.mem)) =
      tmmE.j2 p n pfo pfl fvo ao I us t
      (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) pp + t) + 1))
      (rdW (m.arr64 IW) (rdW (m.arr64 IW) (cao + t))) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (cao + t) + 1))
      (UInt64.ofNat bs.nP) (r2.headD 0) (if UInt64.ofNat bs.nP < al then UInt64.ofNat bs.nP else al)
      (if UInt64.ofNat bs.nP < fvl then UInt64.ofNat bs.nP else fvl) s2'.mem := by
    rw [hnpw]
    by_cases hA : UInt64.ofNat bs.nP < al <;> by_cases hF : UInt64.ofNat bs.nP < fvl <;>
      simp [tmmE.k_param_levels, tmmE.j1, hA, hF]
  rw [h4, hj, tmmE.j2.arm1] at he
  have hnpe' : (if UInt64.ofNat bs.nP < al then UInt64.ofNat bs.nP else al).toNat = min bs.nP al.toNat := hmin al
  -- `sl_eq`
  cases h5 : callE p n "sl_eq" [ao, if UInt64.ofNat bs.nP < al then UInt64.ofNat bs.nP else al, fvo,
      if UInt64.ofNat bs.nP < fvl then UInt64.ofNat bs.nP else fvl] s2'.mem with
  | error e5 =>
    rw [h5, tmmE.k_sl_eq.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h5
  | ok q5 =>
  obtain ⟨r3, m3⟩ := q5
  rw [h5] at he
  obtain ⟨s3, hs3, -, hm3, hW3⟩ := triple_of_callW (s₀ := ⟨s2'.mem, Locals.init []⟩)
    (slEq_spec p hP.eq n _ ao _ fvo _) (callW_of_callE h5)
  have hA2 : decHL s2'.mem ao.toNat (min bs.nP al.toNat) = some (args.take bs.nP) :=
    htakeA.stab (OMono.decHL _ _) s2'.mem hg02
  have hF2 : decHL s2'.mem fvo.toNat (min bs.nP fvl.toNat) = some (fvs.take bs.nP) :=
    htakeF.stab (OMono.decHL _ _) s2'.mem hg02
  obtain ⟨ws1, hsl1, hws1, hlt1⟩ := slR_of_decHL s2'.mem _ _ _ hA2 (by omega)
  obtain ⟨ws2, hsl2, hws2, hlt2⟩ := slR_of_decHL s2'.mem _ _ _ hF2 (by omega)
  have eA : UInt64.ofNat (min bs.nP al.toNat) = (if UInt64.ofNat bs.nP < al then UInt64.ofNat bs.nP else al) :=
    UInt64.toNat_inj.mp (by rw [hmin, UInt64.toNat_ofNat_of_lt' (show min bs.nP al.toNat < 2 ^ 64 by omega)])
  have eF : UInt64.ofNat (min bs.nP fvl.toNat) = (if UInt64.ofNat bs.nP < fvl then UInt64.ofNat bs.nP else fvl) :=
    UInt64.toNat_inj.mp (by rw [hmin, UInt64.toNat_ofNat_of_lt' (show min bs.nP fvl.toNat < 2 ^ 64 by omega)])
  rw [UInt64.ofNat_toNat, eA] at hsl1
  rw [UInt64.ofNat_toNat, eF] at hsl2
  have heq := eqW_ok n s2'.mem _ _ _ _ _ ws1 ws2 hsl1 hsl2 hW3
  by_cases hu0 : ¬ us = r2.headD 0
  · rw [ite_eq_right hu0, tmmE.k_sl_eq.abort1 p n _ _ _ _ _ _ _ _ _ _ _ _ r3 m3 rfl] at he
    cases he
    have hne : ¬ ((decI us == AM.res (paramLevels bs.lps) a) && (List.take bs.nP args == List.take bs.nP fvs)) = true := by
      rw [← hd2]
      have : (decI us : LsIdx) ≠ decI (r2.headD 0) := fun h => hu0 ((clsDecI_inj hus hH2).mp h)
      simp only [Bool.and_eq_true, beq_iff_eq]; exact fun h => this h.1
    exact ErrClaim.ite_neg hne (ErrClaim.fail _ _ (by decide))
  replace hu0 : us = r2.headD 0 := Classical.byContradiction hu0
  rw [ite_eq_left hu0] at he
  by_cases h3 : r3.headD 0 = 0
  · rw [tmmE.k_sl_eq.abort2 p n _ _ _ _ _ _ _ _ _ _ _ _ r3 m3 (by decide) h3] at he
    cases he
    have hne : ¬ ((decI us == AM.res (paramLevels bs.lps) a) && (List.take bs.nP args == List.take bs.nP fvs)) = true := by
      intro hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      have hws : ws1 = ws2 := map_decI_inj' ws1 ws2 hlt1 hlt2 (by rw [← hws1, ← hws2]; exact hc.2)
      rw [ite_eq_left hws] at heq
      rw [h3] at heq
      exact absurd heq (by decide)
    exact ErrClaim.ite_neg hne (ErrClaim.fail _ _ (by decide))
  rw [tmmE.k_sl_eq.arm1 p n _ _ _ _ _ _ _ _ _ _ _ _ r3 m3 (by decide) h3] at he
  -- `mk_target_major`
  unfold tmmE.k_mk_target_major at he
  split at he
  · cases he
    exact ErrClaim.of_callE_nv (f := "mk_target_major") hnv (by decide +kernel) ‹callE _ _ _ _ _ = Except.error _›
  · cases he

include hP hnv in
/-- **`target_major_of_member`'s error claim** (every fuel). -/
theorem tmm_claim (N : Nat) {s₀ : St} {a : AState} {pp cao cal pfo pfl fvo fvl ao al I us t : Word}
    {bs : BlockShape} {css : List (List (IConstantVal × Nat))} {pfvs fvs args : List EIdx}
    (hS : StageR dn vis fe s₀.mem a) (hq : DecB (fun m => decBS m pp.toNat) s₀.mem bs) (hsrc : ShapeSrc s₀.mem pp)
    (hcss : PSlR decCNS css cao cal s₀.mem) (hpf : DecB (fun m => decHL m pfo.toNat pfl.toNat) s₀.mem pfvs)
    (hfv : DecB (fun m => decHL m fvo.toNat fvl.toNat) s₀.mem fvs) (hfvb : fvo.toNat + fvl.toNat ≤ iwTop s₀.mem)
    (hag : DecB (fun m => decHL m ao.toNat al.toNat) s₀.mem args) (hagb : ao.toNat + al.toNat ≤ iwTop s₀.mem)
    (hI : H I) (hus : H us) (hPm : PosMR s₀.mem) :
    CoreSpecE p N "target_major_of_member" [pp, cao, cal, pfo, pfl, fvo, fvl, ao, al, I, us, t]
      (tmoMemT bs css pfvs fvs args (decI I) (decI us) t.toNat) s₀ a := by
  cases N with
  | zero => exact CoreSpecE.zero _ _ _ _ _ _
  | succ n =>
    refine CoreSpecE.of_runs fun e hc => ?_
    by_cases hk0 : e.cls = 0
    · exact ErrClaim.of_cls0 hk0
    exact tmmE_claim hP hnv n hS hq hsrc hcss hpf hfv hfvb hag hagb hI hus hPm e
      (triple_of_callE_err (tmmE_spec p hP.mem (n + 1) s₀ pp cao cal pfo pfl fvo fvl ao al I us t) hc
        (Err.code_ne_of_cls hk0))

end sims

end L.Ind
