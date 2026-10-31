import ConAgua.Arena.RefWalk
import ConAgua.Arena.RecGenSpec.DecTMDecBOf
import ConAgua.Arena.IndInstallSpec.NestCtx
import ConAgua.Arena.IndSumSpec.ParamLevels
import ConAgua.L.ModelGen
import ConRon.Bridge.Inductives.RecCheck
import ConAgua.Arena.IndSumSpec.StructCtorResidOk
import ConAgua.Arena.IndInstallSpec.InstallRec2PSl

/-!
# `target_major_of_member`: one model and one refinement for both outcomes

`tmmE` (`l_model … unified`): every callee (`block_shape_lps`, `param_levels`, `sl_eq`,
`mk_target_major`) is outside the verdict closure, called through its `Option` model. `tmm_ref`
refines the member branch of `targetMajorOf` (`tmoMemT`) for both outcomes: the aborts are the
twin's `unwrapOr` internals (class `0`), the two rejects the twin's final `fail`. It is the member branch of `target_major_of_const`'s refinement (`tmc_ref`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dMajor)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model tmmE_spec (p : Prog) (hP : TmmProg p)
  fns [hP.mem ↦ tmmE]
  specs [blockShapeLps_spec p hP.alloc hP.erCopy hP.erToIw hP.lps n,
    plW_spec p hP.alloc hP.copy hP.cons hP.get hP.pfind hP.ppush hP.iparam hP.plgo hP.pl hP.il n,
    slEq_spec p hP.eq n, mkTargetMajor_spec p hP.alloc hP.mkTm n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- The parameter prefixes' lengths after `param_levels` (the two `min`s of the L code). -/
theorem tmmE_kpl (p : Prog) (n : Nat) (pfo pfl fvo fvl ao al I us t nidx co cl nP : Word)
    (r : List Word) (m : Mem) :
    tmmE.k_param_levels p n pfo pfl fvo fvl ao al I us t nidx co cl nP (.ok (r, m)) =
      tmmE.j2 p n pfo pfl fvo ao I us t nidx co cl nP (r.headD 0) (if nP < al then nP else al)
        (if nP < fvl then nP else fvl) m := by
  by_cases hA : nP < al <;> by_cases hF : nP < fvl <;> simp [tmmE.k_param_levels, tmmE.j1, hA, hF]

/-- What `target_major_of_member` gives besides the twin's record `x` (from `m`): the record's
decoding, the stage invariant, the growth, the frames. -/
structure TmmPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m : Mem)
    (r : Word) (m' : Mem) (x : TargetMajor) (a' : AState) : Prop where
  dec : DecB (fun m => decTM m r.toNat) m' x
  stage : StageR dn vis fe m' a'
  grow : IWGrow m m'
  pos : PosMR m'
  afr : AFr m m'

section sims
variable {p : Prog} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- **`target_major_of_member` refines `targetMajorOf`'s member branch, both outcomes**: the
member's and its constructors' reads, `block_shape_lps`, `paramLevels` (`plW_ok`), the parameter
prefixes compared (`sl_eq`), the record (`mk_target_major`). -/
theorem tmm_ref (n : Nat) {m : Mem} {a : AState} {pp cao cal pfo pfl fvo fvl ao al I us t : Word}
    {bs : BlockShape} {css : List (List (IConstantVal × Nat))} {pfvs fvs args : List EIdx}
    (hS : StageR dn vis fe m a) (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    (hcss : PSlR decCNS css cao cal m) (hpf : DecB (fun m => decHL m pfo.toNat pfl.toNat) m pfvs)
    (hfv : DecB (fun m => decHL m fvo.toNat fvl.toNat) m fvs) (hfvb : fvo.toNat + fvl.toNat ≤ iwTop m)
    (hag : DecB (fun m => decHL m ao.toNat al.toNat) m args) (hagb : ao.toNat + al.toNat ≤ iwTop m)
    (hI : H I) (hus : H us) (hPm : PosMR m) :
    RefE (closedNV p _root_.L.Checker.nvFns = true)
      (tmmE p n m pp cao cal pfo pfl fvo fvl ao al I us t)
      (tmoMemT bs css pfvs fvs args (decI I) (decI us) t.toNat) a
      (fun v x a' => TmmPost dn vis fe m v.1 v.2 x a') := by
  cases n with
  | zero => rw [tmmE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  have hT : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.iw.iw hS.iw.iwSize
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hq hsrc
  have hqt : decBS (truncM m) pp.toNat = some bs := hq
  obtain ⟨hmem, -, -, -, -, -, -⟩ := decBS_some hqt
  obtain ⟨mo, ml, hmo, hml, hmd, -⟩ := partsAt decMS_mono hmem
  obtain ⟨hw0, -, -⟩ := partsIwRd hmo (w := pp) rfl
  obtain ⟨hw1, -, -⟩ := partsIwRd hml (w := pp + 1) (by rw [UInt64.toNat_add]; simp; omega)
  rw [UInt64.ofNat_toNat] at hw0 hw1
  obtain ⟨hnpw, hnpb, -, -⟩ := partsShapeWords (IWGrow.refl m) hq hq9
  by_cases h1 : rdW (m.arr64 IW) (pp + 1) ≤ t
  · rw [tmmE.abort1 p n m pp cao cal pfo pfl fvo fvl ao al I us t h1]; exact RefE.of_cls0 (by decide)
  by_cases h2 : cal ≤ t
  · rw [tmmE.abort2 p n m pp cao cal pfo pfl fvo fvl ao al I us t h1 h2]; exact RefE.of_cls0 (by decide)
  rw [tmmE.arm1 p n m pp cao cal pfo pfl fvo fvl ao al I us t h1 h2]
  rw [hw1] at h1
  have htl : t.toNat < ml.toNat := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp h1)
  have htc : t.toNat < cal.toNat := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp h2)
  -- the members
  have hmd' : decPL (truncM m) (decMS (truncM m)) mo.toNat ml.toNat = some bs.members := hmd
  obtain ⟨hlenM, hgetM⟩ := pos2_decPL_trunc hmd'
  obtain ⟨vt, hvt1, hvt2, hvtl, hvt3⟩ := hgetM t.toNat htl
  obtain ⟨rt, -⟩ := tmRdAt (o := mo) (i := t) hvt2 (by omega)
  obtain ⟨⟨-, -, -⟩, hnit, -⟩ := decMS_some hvt3
  obtain ⟨hnit', hnitlt⟩ := iwN_of_trunc hnit
  have hvtb : vt < 2 ^ 64 := iwN_val_lt hvt2
  have rni : rdW (m.arr64 IW) (UInt64.ofNat vt + 1) = UInt64.ofNat (bs.members[t.toNat]'hvtl).nIdx := by
    have := tmRdAt (o := UInt64.ofNat vt) (i := 1) (by rw [UInt64.toNat_ofNat_of_lt' hvtb]; simpa using hnit')
      (by rw [UInt64.toNat_ofNat_of_lt' hvtb]; simp; omega)
    simpa using this.1
  -- the constructors
  have hcd : decPL (truncM m) (decCNS (truncM m)) cao.toNat cal.toNat = some css := hcss.dec
  obtain ⟨hlenC, hgetC⟩ := pos2_decPL_trunc hcd
  obtain ⟨vc, hvc1, hvc2, hvcl, hvc3⟩ := hgetC t.toNat htc
  obtain ⟨rc, -⟩ := tmRdAt (o := cao) (i := t) hvc2 (by omega)
  have hvc3' : decAt (truncM m) (decPL (truncM m) (decCN (truncM m))) vc = some (css[t.toNat]'hvcl) := hvc3
  obtain ⟨co, cl, hco, hcl, hcsd, -⟩ := partsAt decCN_mono hvc3'
  have hvcb : vc < 2 ^ 64 := iwN_val_lt hvc2
  obtain ⟨hco', hcolt⟩ := iwN_of_trunc hco
  obtain ⟨hcl', hcllt⟩ := iwN_of_trunc hcl
  have rco : rdW (m.arr64 IW) (UInt64.ofNat vc) = co := by
    have := tmRdAt (o := UInt64.ofNat vc) (i := 0) (by rw [UInt64.toNat_ofNat_of_lt' hvcb]; simpa using hco')
      (by rw [UInt64.toNat_ofNat_of_lt' hvcb]; simp; omega)
    simpa using this.1
  have rcl : rdW (m.arr64 IW) (UInt64.ofNat vc + 1) = cl := by
    have := tmRdAt (o := UInt64.ofNat vc) (i := 1) (by rw [UInt64.toNat_ofNat_of_lt' hvcb]; simpa using hcl')
      (by rw [UInt64.toNat_ofNat_of_lt' hvcb]; simp; omega)
    simpa using this.1
  rw [hw0, rt, rni, rc, rco, rcl, hnpw]
  simp only [tmoMemT, List.getElem?_eq_getElem hvtl, List.getElem?_eq_getElem hvcl, unwrapOr, pure_bind]
  -- `block_shape_lps`
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r1 m1 hl1 => ?_
  dsimp only [tmmE.k_block_shape_lps]
  obtain ⟨hS1, hg1, hlps1, htop1⟩ := lpsW_ok' hl1 hS hq
  have hT1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.iw.iw hS1.iw.iwSize
  -- `param_levels`
  refine RefE.bindLift (fun _ => rfl) fun r2 m2 hl2 => ?_
  obtain ⟨blv, a2, run2, hS2, hg2, hH2, hd2⟩ := plW_ok dn vis fe n m1 m2 a _ _ bs.lps r2 hl2 hS1 hlps1
    (by omega) htop1
  refine ⟨_, _, run2, ?_⟩
  rw [tmmE_kpl, tmmE.j2.eq_1]
  have hg02 := hg1.trans hg2
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
  -- `sl_eq`
  rcases hl3 : eqW n m2 ao (if UInt64.ofNat bs.nP < al then UInt64.ofNat bs.nP else al) fvo
      (if UInt64.ofNat bs.nP < fvl then UInt64.ofNat bs.nP else fvl) with _ | r3
  · rw [liftE_none, tmmE.k_sl_eq.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  have hA2 : decHL m2 ao.toNat (min bs.nP al.toNat) = some (args.take bs.nP) :=
    htakeA.stab (OMono.decHL _ _) m2 hg02
  have hF2 : decHL m2 fvo.toNat (min bs.nP fvl.toNat) = some (fvs.take bs.nP) :=
    htakeF.stab (OMono.decHL _ _) m2 hg02
  obtain ⟨ws1, hsl1, hws1, hlt1⟩ := slR_of_decHL m2 _ _ _ hA2 (by omega)
  obtain ⟨ws2, hsl2, hws2, hlt2⟩ := slR_of_decHL m2 _ _ _ hF2 (by omega)
  have eA : UInt64.ofNat (min bs.nP al.toNat) = (if UInt64.ofNat bs.nP < al then UInt64.ofNat bs.nP else al) :=
    UInt64.toNat_inj.mp (by rw [hmin, UInt64.toNat_ofNat_of_lt' (show min bs.nP al.toNat < 2 ^ 64 by omega)])
  have eF : UInt64.ofNat (min bs.nP fvl.toNat) = (if UInt64.ofNat bs.nP < fvl then UInt64.ofNat bs.nP else fvl) :=
    UInt64.toNat_inj.mp (by rw [hmin, UInt64.toNat_ofNat_of_lt' (show min bs.nP fvl.toNat < 2 ^ 64 by omega)])
  rw [UInt64.ofNat_toNat, eA] at hsl1
  rw [UInt64.ofNat_toNat, eF] at hsl2
  have heq := eqW_ok n m2 _ _ _ _ _ ws1 ws2 hsl1 hsl2 hl3
  by_cases hu0 : ¬ us = r2.headD 0
  · rw [ite_eq_right hu0, tmmE.k_sl_eq.abort1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ r3 rfl]
    have hne : ¬ ((decI us == blv) && (List.take bs.nP args == List.take bs.nP fvs)) = true := by
      rw [← hd2]
      have : (decI us : LsIdx) ≠ decI (r2.headD 0) := fun h => hu0 ((decI_inj_iff hus hH2).mp h)
      simp only [Bool.and_eq_true, beq_iff_eq]; exact fun h => this h.1
    exact fun _ => ErrClaim.ite_neg hne (ErrClaim.fail _ _ (by decide))
  replace hu0 : us = r2.headD 0 := Classical.byContradiction hu0
  rw [ite_eq_left hu0]
  by_cases h3 : r3 = 0
  · rw [tmmE.k_sl_eq.abort2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ r3 (by decide) h3]
    have hne : ¬ ((decI us == blv) && (List.take bs.nP args == List.take bs.nP fvs)) = true := by
      intro hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      have hws : ws1 = ws2 := (map_decI_inj ws1 ws2 hlt1 hlt2).mp (by rw [← hws1, ← hws2]; exact hc.2)
      rw [ite_eq_left hws] at heq
      rw [h3] at heq
      exact absurd heq (by decide)
    exact fun _ => ErrClaim.ite_neg hne (ErrClaim.fail _ _ (by decide))
  rw [tmmE.k_sl_eq.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ r3 (by decide) h3]
  have hws : ws1 = ws2 := Decidable.byContradiction fun hne => h3 (by rwa [ite_eq_right hne] at heq)
  have hc : (decI us == blv && args.take bs.nP == fvs.take bs.nP) = true := by
    rw [← hd2, hu0, hws1, hws2, hws]; simp
  refine RefE.ite_pos hc ?_
  -- the record
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r4 m4 hl4 => ?_
  dsimp only [tmmE.k_mk_target_major]
  have hafr : AFr m m4 := ((lpsW_afr hl1).trans (plW_afr hl2)).trans (mkTMW_afr hl4)
  rw [mkTMW_eq, Option.map_eq_some_iff] at hl4
  obtain ⟨⟨q, m4'⟩, hpr, he⟩ := hl4
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  obtain ⟨hS4, hg4, hq4, ht4, hget4⟩ := posRecW_stage hpr hS2 (by simp)
  simp only [List.length_cons, List.length_nil] at ht4
  have hg04 := hg02.trans hg4
  have hnidb : (bs.members[t.toNat]'hvtl).nIdx < 2 ^ 64 := iwN_val_lt hnit'
  have ht1 : (t + 1).toNat = t.toNat + 1 := word_add_toNat (by rw [show (1 : Word).toNat = 1 from rfl]; omega)
  have hdec := decTM_decB_of (m := m4') (q := q.toNat) (by omega)
    (by simpa using hget4 0 (by simp)) (by simpa using hget4 1 (by simp)) (by simpa using hget4 2 (by simp))
    (by simpa using hget4 3 (by simp)) (by simpa using hget4 4 (by simp)) (by simpa using hget4 5 (by simp))
    (by simpa using hget4 6 (by simp)) (by simpa using hget4 7 (by simp)) (by simpa using hget4 8 (by simp))
    (by simpa using hget4 9 (by simp)) (by simpa using hget4 10 (by simp)) (by simpa using hget4 11 (by simp))
    (by simpa using hget4 12 (by simp)) hI hus
    (by rw [← eF, UInt64.toNat_ofNat_of_lt' (show min bs.nP fvl.toNat < 2 ^ 64 by omega)]
        exact htakeF.grow (OMono.decHL _ _) hg04)
    (hcsd.grow (OMono.decPL decCN_mono _ _) hg04)
    (show decPL (truncM m4') (decNCN (truncM m4')) (0 : Word).toNat (0 : Word).toNat = some [] by
      simp [decPL])
    (hpf.grow (OMono.decHL _ _) hg04)
  rw [hnpe, UInt64.toNat_ofNat_of_lt' hnidb, ht1] at hdec
  exact RefE.ret rfl ⟨by simpa [decON] using hdec, hS4, hg04,
    ((hPm.fr (lpsW_mfrP hl1)).fr (plW_mfrP hl2)).fr (posRecW_mfr hpr), hafr⟩

end sims

end L.Ind

end
