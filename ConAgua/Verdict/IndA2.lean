import ConAgua.Verdict.IndA1
import ConAgua.Verdict.IndAGen

/-!
# `check_block`'s error refinement (lane `verdicts-b`, helper `ia`)

`checkBlockE_claim`: `CheckBlockE p` (the claim `check_ind_decl` takes as a hypothesis) from the
claims of `check_block_pass` and `check_block_tail` (`CheckBlockPassE`, `CheckBlockTailE`, in the
shape of `checkBlockPass_refinesC`, `checkBlockTail_refinesC`). The other callees
(`block_shape_all_ctors`, `block_caps_ctor_names`, `block_shape_member_names`, `sl_nodup`,
`flush_caches`, `block_raw_rec`) are outside the verdict closure.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model icbE_spec (p : Prog) (hf : p.lookup "check_block" = some checkBlock)
  fns [hf ↦ icbE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

-- `check_block_pass`'s error claim, in the shape of `checkBlockPass_refinesC`.
err_stmt CheckBlockPassE := checkBlockPass_refinesC fuel n

-- `check_block_tail`'s error claim, in the shape of `checkBlockTail_refinesC`.
err_stmt CheckBlockTailE := checkBlockTail_refinesC fuel n

section
variable {p : Prog}

theorem checkBlockE_claim (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (hpass : CheckBlockPassE p) (htail : CheckBlockTailE p) : CheckBlockE p := by
  intro env hkp henv hV hOpf hLC hLT hApd hCrk hIlpf hLz hP fs fs2 hcl hfs hfr hcl2 hfs2 fsR fsT hclR hfR
    hclT hfT F hF m a dn vis fe bO bL p0 bs block hC hq hsrc hcx hblk hPm hma hA hkP hkt hkr hta hrb hcoh
    hden shP hshP blockP hbP fsH fsM hfRc hclH hfH hclM hfM hlpsDn e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hS := hC.stage
  replace he := triple_of_callE_err (icbE_spec p hP.cb F ⟨m, Locals.init []⟩ vis bO bL p0) he
    (Err.code_ne_of_cls hk0)
  simp only at he
  cases F with
  | zero => rw [icbE.eq_1] at he; cases he; exact absurd Err.cls_outOfFuel hk0
  | succ F =>
  obtain ⟨n, hn, hle⟩ : ∃ n, n + 4 ≤ 2 ^ 62 ∧ F ≤ n + 4 := ⟨F - 4, by omega, by omega⟩
  rw [icbE.arm1] at he
  have hT0 : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨hq', hq9, hptr⟩ := partsShapeFacts hq hsrc
  -- the constructors
  cases c1 : callE p F "block_shape_all_ctors" [p0] m with
  | error e1 =>
    rw [c1, icbE.k_block_shape_all_ctors.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) c1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [c1, icbE.k_block_shape_all_ctors.eq_2] at he
  have c1' := callW_mono (callW_of_callE c1) hle
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockShapeAllCtors_spec p hP.ha hP.cp hP.nco hP.acc hP.acg hP.ac (n + 4) _ p0) c1'
  simp only at hs1 hW1
  subst hs1
  obtain ⟨cq, tot, rfl, hdc, hg1, hf1, htop1, hroom1⟩ := acW_ok _ _ _ p0 _ bs hW1 hq hS.2.2.2.1 hS.2.2.2.2.2
  have hS1 := stage_frame_iw hS hf1 (by omega)
  have hP1 := hPm.fr (MFr.of_iw hf1)
  obtain ⟨mp0, hmp0⟩ := hma
  have hma1 := maMR_mfr (MFr.of_iw hf1) hmp0
  have hA1 : AbsOK s1.mem := AFr.of_frame hf1 (by decide) (by decide) hA
  obtain ⟨tp0, htp0⟩ := hta
  have hta1 : ∃ mp, taMR s1.mem mp := ⟨tp0, taMR_mfr (MFr.of_iw hf1) (by simp) (by simp) htp0⟩
  have hk1 := callW_keepW c1'
  simp only [List.headD_cons, List.tail_cons] at he
  have hT1 : iwTop s1.mem < 2 ^ 64 := (rdW (s1.mem.arr64 CTL) 200).toNat_lt
  -- the constructors' names
  have hdc1 : decPL s1.mem (decCN s1.mem) cq.toNat tot.toNat = some bs.allCtors :=
    hdc.get (OMono.decPL (fun q => decCN_mono q) _ _)
  cases c2 : callE p F "block_caps_ctor_names" [cq, tot] s1.mem with
  | error e2 =>
    rw [c2, icbE.k_block_caps_ctor_names.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) c2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [c2, icbE.k_block_caps_ctor_names.eq_2] at he
  have c2' := callW_mono (callW_of_callE c2) hle
  obtain ⟨s2, hs2, -, hW2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (blockCapsCtorNames_spec p hP.ha hP.mnc hP.bccn (n + 4) _ cq tot) c2'
  simp only at hs2 hW2
  subst hs2
  have hcsd : decPL (truncM s1.mem) (decCN (truncM s1.mem)) cq.toNat tot.toNat = some bs.allCtors := hdc
  have hlen := decPL_length _ hcsd
  obtain ⟨hr2, hd2, hg2, hf2, ht2⟩ := ctorNamesW_dec hW2 hS1.2.2.2.1 hS1.2.2.2.2.2 (Nat.le_of_eq htop1)
    (bs.allCtors.map (·.1)) (by simp [hlen]) (fun j hj => by
      obtain ⟨v, y, hv, hy, hget⟩ := decPL_get tot.toNat cq.toNat bs.allCtors hcsd j hj
      obtain ⟨⟨a', hva, hcv⟩, -⟩ := decCN_some hy
      obtain ⟨hvlt, hv'⟩ := rec2IwN_trunc hv
      obtain ⟨hvlt2, hva'⟩ := rec2IwN_trunc hva
      have hj' : j < bs.allCtors.length := by omega
      have hy' : bs.allCtors[j] = y := by simpa [List.getElem?_eq_getElem hj'] using hget
      refine ⟨v, a', hv', by omega, hva', ?_⟩
      simp only [List.getElem_map, hy']
      exact DecB.get (f := fun m => decCVp m a') (OMono.decCVp _) hcv)
  have hS2 : StageR dn vis fe s2.mem a := stage_frame_iw hS1 hf2 (by
    have := ctorNamesW_room hW2 hS1.2.2.2.1; simp only [iwTop] at this ht2 ⊢; omega)
  subst hr2
  simp only [List.headD_cons, List.tail_cons, List.map_map] at he hd2
  have hP2 := hP1.fr (MFr.of_iw hf2)
  have hma2 := maMR_mfr (MFr.of_iw hf2) hma1
  have hA2 : AbsOK s2.mem := AFr.of_frame hf2 (by decide) (by decide) hA1
  have hta2 : ∃ mp, taMR s2.mem mp :=
    let ⟨mp, h⟩ := hta1; ⟨mp, taMR_mfr (MFr.of_iw hf2) (by simp) (by simp) h⟩
  have hk2 := hk1.trans (callW_keepW c2')
  have hg12 := hg1.trans hg2
  have hT2 : iwTop s2.mem < 2 ^ 64 := (rdW (s2.mem.arr64 CTL) 200).toNat_lt
  -- the members' names
  have hq2 := hq.grow (decBS_mono _) hg12
  have hsrc2 := partsHsrc_grow hg12 hq9 hsrc
  obtain ⟨hqd2, hq92, hptr2⟩ := partsShapeFacts hq2 hsrc2
  cases c3 : callE p F "block_shape_member_names" [p0] s2.mem with
  | error e3 =>
    rw [c3, icbE.k_block_shape_member_names.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) c3
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [c3, icbE.k_block_shape_member_names.eq_2] at he
  have c3' := callW_mono (callW_of_callE c3) hle
  obtain ⟨s3, hs3, hr3, hdn3, hg3, hf3, ht3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (blockShapeMemberNames_refines p hP.ha hP.mnc hP.bsmn (n + 4) _ p0 bs hqd2 (by omega) hS2.2.2.2.1
      hS2.2.2.2.2.2 hsrc2 (fun o l j v h1 h2 h3 h4 => Nat.lt_of_succ_lt (hptr2 o l j v h1 h2 h3 h4))) c3'
  obtain ⟨s3', hs3', -, hW3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (blockShapeMemberNames_spec p hP.ha hP.mnc hP.bsmn (n + 4) _ p0) c3'
  have hroom := memberNamesW_room hW3 hS2.2.2.2.1
  rw [partsShapeK hqd2 hq92] at hroom
  have hkb : bs.k < 2 ^ 64 := by
    obtain ⟨o, l, -, hl', hg'⟩ := decAt_some (decBS_some hqd2).1
    have := iwN_rdW hl' (by omega); rw [BlockShape.k, decPL_length _ hg']; exact this.2
  rw [UInt64.toNat_ofNat_of_lt' hkb] at hroom
  simp only at hs3 hr3 hdn3 hg3 hf3 ht3
  subst hs3
  have hS3 : StageR dn vis fe s3.mem a := stage_frame_iw hS2 hf3 (by
    rw [← ht3]; simp only [iwTop] at hroom ⊢; omega)
  subst hr3
  simp only [List.headD_cons, List.tail_cons] at he
  have hP3 := hP2.fr (MFr.of_iw hf3)
  have hma3 := maMR_mfr (MFr.of_iw hf3) hma2
  have hA3 : AbsOK s3.mem := AFr.of_frame hf3 (by decide) (by decide) hA2
  have hta3 : ∃ mp, taMR s3.mem mp :=
    let ⟨mp, h⟩ := hta2; ⟨mp, taMR_mfr (MFr.of_iw hf3) (by simp) (by simp) h⟩
  have hk3 := hk2.trans (callW_keepW c3')
  -- the two `sl_nodup`s
  have hcn3 : (decHL s3.mem (rdW (s1.mem.arr64 CTL) 200).toNat tot.toNat : Option (List NIdx)) =
      some (bs.allCtors.map (fun x => x.1.name)) := by
    rw [decHL_grow3 hg3 (by omega), hd2]; rfl
  obtain ⟨wc, hslc, hwc, hwcl⟩ := slR_of_decHL s3.mem _ _ _ hcn3 (by rw [ht2]; exact hT2)
  rw [UInt64.ofNat_toNat, UInt64.ofNat_toNat] at hslc
  obtain ⟨wm, hslm, hwm, hwml⟩ := slR_of_decHL s3.mem _ _ _ hdn3
    (by rw [ht3]; exact (rdW (s3.mem.arr64 CTL) 200).toNat_lt)
  rw [UInt64.ofNat_toNat] at hslm
  cases c4 : callE p F "sl_nodup" [rdW (s1.mem.arr64 CTL) 200, tot] s3.mem with
  | error e4 =>
    rw [c4, icbE.k_sl_nodup.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) c4
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [c4, icbE.k_sl_nodup.eq_2] at he
  have c4' := callW_mono (callW_of_callE c4) hle
  obtain ⟨s4, hs4, -, hm4, hnd1⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (slNodup_refines p hP.slc hP.nodup (n + 4) _ _ _ wc hslc hwcl) c4'
  simp only at hs4 hm4 hnd1
  subst hs4
  rw [hm4] at he
  cases c5 : callE p F "sl_nodup" [rdW (s2.mem.arr64 CTL) 200, UInt64.ofNat bs.k] s3.mem with
  | error e5 =>
    rw [c5, icbE.k_sl_nodup_2.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) c5
  | ok q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [c5] at he
  have c5' := callW_mono (callW_of_callE c5) hle
  obtain ⟨s5, hs5, -, hm5, hnd2⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (slNodup_refines p hP.slc hP.nodup (n + 4) _ _ _ wm hslm hwml) c5'
  simp only at hs5 hm5 hnd2
  subst hs5
  rw [← hwc] at hnd1
  rw [← hwm] at hnd2
  rw [icbE.k_sl_nodup_2.eq_2] at he
  by_cases hdup : r4.headD 0 = 0 ∨ r5.headD 0 = 0
  · rw [ite_eq_left hdup] at he
    cases he
    have hcond : (!ConRon.Arena.nameNodup (bs.allCtors.map (fun x => x.1.name)) ||
        !ConRon.Arena.nameNodup bs.memberNames) = true := by
      rw [← hnd1, ← hnd2]
      rcases hdup with h | h
      · rw [h]; rfl
      · rw [h]; simp
    simp only [ConRon.Arena.checkBlock, hcond, ite_true]
    exact ErrClaim.fail _ _ (by decide)
  rw [ite_eq_right hdup] at he
  rw [hm5] at he
  have hnodup : (!ConRon.Arena.nameNodup (bs.allCtors.map (fun x => x.1.name)) ||
      !ConRon.Arena.nameNodup bs.memberNames) = false := by
    rw [← hnd1, ← hnd2]
    have h1 : r4.headD 0 ≠ 0 := fun e => hdup (.inl e)
    have h2 : r5.headD 0 ≠ 0 := fun e => hdup (.inr e)
    have e1 : (r4.headD 0 != 0) = true := by simpa using h1
    have e2 : (r5.headD 0 != 0) = true := by simpa using h2
    rw [e1, e2]; rfl
  simp only [ConRon.Arena.checkBlock, hnodup, Bool.false_eq_true, ite_false]
  -- the flush
  have hg13 := hg12.trans hg3
  cases c6 : callE p F "flush_caches" [] s3.mem with
  | error e6 =>
    rw [c6, icbE.k_flush_caches.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) c6
  | ok q6 =>
  obtain ⟨r6, m6⟩ := q6
  rw [c6, icbE.k_flush_caches.eq_2] at he
  have c6' := callW_mono (callW_of_callE c6) hle
  obtain ⟨s6, hs6, -, hfok, hfm⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (flushCaches_spec p hP.pass.flush (n + 4) _) c6'
  simp only at hs6 hfok hfm
  subst hs6
  obtain ⟨hS6, hg6⟩ := flush_stage hS3 hfok
  have hfr6 : MFr [] [] s3.mem s6.mem := by
    rw [hfm]; exact MFr.of_frame (flushMem_frame s3.mem) (by simp) (by
      intro x hx; left; have := flushCtl_lt x hx; omega)
  rw [← hfm] at hS6 hg6
  have hP6 := hP3.fr hfr6
  have hma6 := maMR_mfr hfr6 hma3
  have hA6 : AbsOK s6.mem := by rw [hfm]; exact AFr.of_frame (flushMem_frame s3.mem) (by decide) (by decide) hA3
  have hta6 : ∃ mp, taMR s6.mem mp :=
    let ⟨mp, h⟩ := hta3; ⟨mp, taMR_mfr hfr6 (by simp) (by simp) h⟩
  have hk6 := hk3.trans (callW_keepW c6')
  have hg16 := hg13.trans hg6
  refine ErrClaim.bind_right (flushCaches_run a) ?_
  -- the raw recursion bit
  have hq6 := hq.grow (decBS_mono _) hg16
  have hsrc6 := partsHsrc_grow hg16 hq9 hsrc
  cases c7 : callE p F "block_raw_rec" [p0] s6.mem with
  | error e7 =>
    rw [c7, icbE.k_block_raw_rec.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) c7
  | ok q7 =>
  obtain ⟨r7, m7⟩ := q7
  rw [c7, icbE.k_block_raw_rec.eq_2] at he
  have c7' := callW_mono (callW_of_callE c7) hle
  obtain ⟨s7, hs7, -, hok7, hst7, hr7, hma7, hS7, hg7⟩ := triple_of_callW (s₀ := ⟨s6.mem, Locals.init []⟩)
    (blockRawRec_refines p hP.ma hP.ha hP.mnc hP.bsmn hP.pdm hP.brm hP.brg hP.brr (n + 3) _ _ dn vis fe p0 bs
      _ hS6 hq6 hsrc6 hma6) (callW_mono c7' (by omega))
  simp only at hs7 hst7 hr7 hma7 hS7 hg7
  subst hs7
  have hP7 := PosMR.ofClosed hcl hfr c7' hP6
  have hA7 : AbsOK s7.mem := hkr _ _ _ _ _ c7' hA6
  have hrun7 := AM.run_of_ok _ _ hok7
  rw [hst7] at hrun7
  refine ErrClaim.bind_right hrun7 ?_
  generalize AM.res (ConRon.Arena.blockRawRec ⟨bs⟩) { a with caches := Caches.empty } = raw at hrun7 hr7 ⊢
  subst hr7
  have hg17 := hg16.trans hg7
  have hta7 := taMR.ofClosed hclT (hfT _ (by decide)) c7' hta6
  have hk7 := hk6.trans (callW_keepW c7')
  obtain ⟨cf, -, -⟩ := ConRon.Bridge.Inductives.ReadOK.flush (μ := V) hC.check.toR
    (show ConRon.Arena.flushCaches a = .ok ((), { a with caches := Caches.empty }) from rfl)
  have hC7 := StageC.of_parts hS7 cf hA7 hC.mem.dnN
  -- the pass
  have hq7 := hq.grow (decBS_mono _) hg17
  have hsrc7 := partsHsrc_grow hg17 hq9 hsrc
  have hcx7 := hcx.grow hg17 hq9 hsrc hptr
  cases c8 : callE p F "check_block_pass" [vis, p0, [if raw then (1 : Word) else 0].headD 0] s7.mem with
  | error e8 =>
    rw [c8, icbE.k_check_block_pass.none] at he
    cases he
    refine ErrClaim.bind_left ?_
    exact hpass hkp henv hV hOpf hLC hLT hApd hCrk hIlpf hLz hP.pass hcl hfs ⟨s7.mem, Locals.init []⟩ _ hC7 hq7 hsrc7 hcx7
      (b := raw) (by cases raw <;> rfl) hP7 hA7 hkP hcoh hden hshP hlpsDn F (by omega) _ c8
  | ok q8 =>
  obtain ⟨r8, m8⟩ := q8
  rw [c8, icbE.k_check_block_pass.eq_2] at he
  have c8' := callW_mono (callW_of_callE c8) hle
  obtain ⟨s8, hs8, -, x8, a8, hrun8, ⟨hS8, hg8, hBP8, hP8, hA8, hrb8, hlp8⟩, env₁, hC8, qP, i8, hcoh8,
      hden8, henv₁, hqP, hTw, henv₂, hMs⟩ :=
    triple_of_callW (s₀ := ⟨s7.mem, Locals.init []⟩)
    (checkBlockPass_refinesC hkp henv hV hOpf hLC hLT hApd hCrk hIlpf hLz hP.pass hcl hfs n hn _ _ hC7 hq7 hsrc7 hcx7 (b := raw)
      (by cases raw <;> rfl) hP7 hA7 hkP hcoh hden hshP hlpsDn) c8'
  simp only at hs8 hS8 hg8 hBP8 hP8 hA8 hrb8 hlp8 hC8
  subst hs8
  have hma8 := maMR.ofClosed hclM (hfM _ (by simp)) c8' hma7
  have hg18 := hg17.trans hg8
  have hta8 := taMR.ofClosed hclT (hfT _ (by decide)) c8' hta7
  replace hrb8 := hrb8 (hrb.grow hg17 (by omega))
  refine ErrClaim.bind_right hrun8 ?_
  -- the tail
  cases c9 : callE p F "check_block_tail" [bO, bL, r8.headD 0] s8.mem with
  | error e9 =>
    rw [c9, icbE.k_check_block_tail.none] at he
    cases he
    exact htail hkp henv₁ hV hOpf hLC hLT hApd hCrk hIlpf hP.tail hP.cbr hfs2 hcl2 hclR hfR ⟨s8.mem, Locals.init []⟩ _ hC8
      hBP8 (hblk.grow (decEBlk_mono _ _ _) hg18) hP8.hbOK hA8 hkt ⟨hP8, hta8⟩ hrb8 hlp8 hcoh8 hden8 hqP
      (ConRon.Bridge.denoteCIList_mono i8.ext _ _ hbP) hTw henv₂ hMs hfRc hclH hfH F (by omega) _ c9
  | ok q9 =>
    rw [c9, icbE.k_check_block_tail.eq_2] at he
    cases he

end

end L.Ind
