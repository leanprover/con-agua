import ConAgua.Verdict.IndsE6
import ConAgua.Verdict.IndA3
import ConAgua.Verdict.IndsE5

/-!
# `check_block_inds`' error refinement (lane `verdicts-b`, helper `ia2-inds`)

`ibiW_simC`'s proof on the error model `cbiE`: member 0's former by `cbtE_claim`, the other
formers by `cbtsE_claim`, the agreements by `cbagE_claim`; past them only class-`0` errors
(`block_shape_with_sort`, `check_block_inds_cv_tas`, `cons_block_inds`, the empty block's abort).
`CheckBlockIndsE` from the claims of `check_constant_val`, `check_sum_tele` and the core stubs.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)


namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section sims
variable {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true) (hcE : CoreStubsE p)
  (eCcv : CheckConstantValE p) (eSum : CheckSumTeleE p)

include hnv hcE eCcv eSum in
/-- **`check_block_inds`' error claim** (`checkBlockInds_refinesC`'s shape), from the claims of
`check_constant_val`, `check_sum_tele` and the core stubs. -/
theorem checkBlockIndsE_claim : CheckBlockIndsE p := by
  intro hq dn vis fe env henv hV hOpf hLC hApd hCrk hLz hP s₀ a pp isRec bs b hC hqd hsrc hcx hb hA hk bsP
    hbsP hfe hcoh hlpsDn F hF e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  replace he := triple_of_callE_err (cbiE_spec p hP.inds F ⟨s₀.mem, Locals.init []⟩ vis pp isRec) he
    (Err.code_ne_of_cls hk0)
  simp only at he
  generalize s₀.mem = m at *
  cases F with
  | zero => rw [cbiE.eq_1] at he; cases he; exact absurd Err.cls_outOfFuel hk0
  | succ n =>
  have hn : n ≤ 2 ^ 62 := by omega
  have hS := hC.stage
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨hq', hq9, -⟩ := partsShapeFacts hqd hsrc
  have hkw := partsShapeK hq' hq9
  obtain ⟨hnpw, hnpb, -, -⟩ := partsShapeWords (IWGrow.refl m) hqd hq9
  have hqt : decBS (truncM m) pp.toNat = some bs := hqd
  obtain ⟨hmem, -, -, -, -, -, -⟩ := decBS_some hqt
  obtain ⟨o, l, ho, hl, hdm, hob⟩ := partsAt decMS_mono hmem
  have hdm' : decPL (truncM m) (decMS (truncM m)) o.toNat l.toNat = some bs.members := hdm
  have hlk : bs.k = l.toNat := decPL_length _ hdm'
  obtain ⟨hw0, -, -⟩ := partsIwRd ho (w := pp) rfl
  rw [UInt64.ofNat_toNat] at hw0
  have hkl : UInt64.ofNat bs.k = l := by rw [hlk]; exact UInt64.ofNat_toNat
  obtain ⟨hmsP, -, -, -, hsP, -, -⟩ := ConRon.Bridge.Inductives.dShape_inv hbsP
  by_cases hl0 : l = 0
  · rw [cbiE.abort1 p n m vis pp isRec (by rw [hkw, hkl]; exact hl0)] at he; cases he; exact absurd rfl hk0
  rw [cbiE.arm1 p n m vis pp isRec (by rw [hkw, hkl]; exact hl0), hkw, hkl, hw0, hnpw] at he
  have hob' : o.toNat + l.toNat ≤ iwTop m := hob.resolve_left hl0
  have hoN : iwN m pp.toNat = some o.toNat := (rec2IwN_trunc ho).2
  have hlN : iwN m (pp.toNat + 1) = some l.toNat := (rec2IwN_trunc hl).2
  have hms : MemsOK m o l bs.members :=
    ⟨⟨hdm, hob'⟩, fun j hj c hc d hd => hcx o.toNat l.toNat hoN hlN j hj c hc d hd⟩
  obtain ⟨q0, ms0, rest, hmeq, hw, hqb, hmok, hrest⟩ := hms.cons hl0
  rw [hw] at he
  unfold ConRon.Arena.checkBlockInds
  simp only [hmeq]
  rw [hmeq] at hmsP
  obtain ⟨ms0P, restP, -, hm0, hrestP⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hmsP
  have hnp : (UInt64.ofNat bs.nP : Word).toNat = bs.nP := UInt64.toNat_ofNat_of_lt' hnpb
  -- member 0's former
  cases h1 : callE p n "check_block_tele" [vis, UInt64.ofNat bs.nP, UInt64.ofNat q0] m with
  | error e1 =>
    rw [h1, cbiE.k_check_block_tele.none] at he; cases he
    have hcl := cbtE_claim hnv eCcv eSum hq henv hV hApd hCrk hP.toCstProg hP.bTele ⟨m, Locals.init []⟩ a
      (UInt64.ofNat bs.nP) _ ms0 hC hmok hA hm0 hfe n hn e h1
    rw [hnp] at hcl
    exact ErrClaim.bind_left hcl
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, cbiE.k_check_block_tele.arm1] at he
  cases n with
  | zero => have := callW_of_callE h1; rw [callW_zero] at this; cases this
  | succ k =>
  obtain ⟨s1, hs1, -, hok1, hT1, hA1, c1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (checkBlockTele_refinesC hq henv hV hApd hCrk hP.toCstProg hP.bTele k (by omega) ⟨m, Locals.init []⟩ a
      (UInt64.ofNat bs.nP) _ ms0 hC hmok hA hm0 hfe) (callW_of_callE h1)
  subst hs1
  have hr1 := partsRunOfOk hok1
  rw [hnp] at hr1 hT1 c1
  generalize AM.st (ConRon.Arena.checkBlockTele V fe bs.nP ms0) a = a1 at hr1 hT1 c1
  generalize AM.res (ConRon.Arena.checkBlockTele V fe bs.nP ms0) a = x1 at hr1 hT1
  obtain ⟨cvTa0, s0⟩ := x1
  obtain ⟨hC1, hg1, hcv1, hcx1, hs32, hsd⟩ := hT1
  obtain ⟨-, ⟨cvTa₀P, s0P⟩, ⟨h1a, h1b, hw1⟩, hfk1⟩ := ConRon.Bridge.Inductives.checkBlockTele_specF fe rfl
    (ConRon.Bridge.CoreSpec.of_core rfl) henv bs.nP ms0 ms0P a a1 _ hC.check ⟨hm0, hfe⟩ hr1
  dsimp only at h1a h1b hw1
  have hc0 := installCvDecB hcv1 hcx1
  have hfe1 := ConRon.Bridge.denoteFEnv_mono c1.ext hfe
  refine ErrClaim.bind_right hr1 ?_
  -- the other members' formers
  cases h2 : callE p (k + 1) "check_block_teles" [vis, UInt64.ofNat bs.nP, o + 1, l - 1] s1.mem with
  | error e2 =>
    rw [h2, cbiE.k_check_block_teles.none] at he; cases he
    have hW2 := triple_of_callE_err (cbtsE_spec p hP.bTeles (k + 1) ⟨s1.mem, Locals.init []⟩ vis
      (UInt64.ofNat bs.nP) (o + 1) (l - 1)) h2 (Err.code_ne_of_cls hk0)
    simp only at hW2
    have hcl := cbtsE_claim hnv eCcv eSum hq henv hV hApd hCrk hP.toInstProg (UInt64.ofNat bs.nP) (k + 1)
      (by omega) s1.mem a1 (o + 1) (l - 1) rest restP hC1 (hrest.grow hg1) hA1
      (ConRon.Bridge.Inductives.dMember_ext.list c1.ext _ _ hrestP) hfe1 e hW2
    rw [hnp] at hcl
    exact ErrClaim.bind_left hcl
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, cbiE.k_check_block_teles.arm1] at he
  obtain ⟨s2, hs2, -, hok2, hC2, hg2, hcvs, hA2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (checkBlockTeles_refinesC hq henv hV hApd hCrk hP.toInstProg (k + 1) (by omega) ⟨s1.mem, Locals.init []⟩ a1
      (UInt64.ofNat bs.nP) (o + 1) (l - 1) rest hC1 (hrest.grow hg1) hA1
      (ConRon.Bridge.Inductives.dMember_ext.list c1.ext _ _ hrestP) hfe1) (callW_of_callE h2)
  subst hs2
  have hr2 := partsRunOfOk hok2
  rw [hnp] at hr2 hC2 hcvs
  generalize AM.st (ConRon.Arena.checkBlockTeles V fe bs.nP rest) a1 = a2 at hr2 hC2
  generalize AM.res (ConRon.Arena.checkBlockTeles V fe bs.nP rest) a1 = cvs at hr2 hcvs
  obtain ⟨c2, cvsP, ⟨h2', hw2⟩, -⟩ := ConRon.Bridge.Inductives.checkBlockTeles_specF fe rfl
    (ConRon.Bridge.CoreSpec.of_core rfl) henv bs.nP rest restP a1 a2 cvs hC1.check
    ⟨ConRon.Bridge.Inductives.dMember_ext.list c1.ext _ _ hrestP, hfe1⟩ hr2
  refine ErrClaim.bind_right hr2 ?_
  -- the agreements
  have hsd' : decI (r1.tail.headD 0) = s0 := hsd
  cases h3 : callE p (k + 1) "check_block_agree" [vis, UInt64.ofNat bs.nP, r1.headD 0, r1.tail.headD 0,
      r2.headD 0, r2.tail.headD 0] s2.mem with
  | error e3 =>
    rw [h3, cbiE.k_check_block_agree.none] at he; cases he
    have hW3 := triple_of_callE_err (cbagE_spec p hP.agreeP.agree (k + 1) ⟨s2.mem, Locals.init []⟩ vis
      (UInt64.ofNat bs.nP) (r1.headD 0) (r1.tail.headD 0) (r2.headD 0) (r2.tail.headD 0)) h3 (Err.code_ne_of_cls hk0)
    simp only at hW3
    rw [← hsd'] at h1b
    have hcl := cbagE_claim hq henv hOpf hLC hnv hcE hP.agreeP (UInt64.ofNat bs.nP) (r1.headD 0)
      (r1.tail.headD 0) cvTa0 hw1 (k + 1) (by omega) s2.mem a2 (r2.headD 0) (r2.tail.headD 0) cvs cvsP hC2 hA2
      (hc0.grow (OMono.decCVp _) hg2) hs32 hcvs (ConRon.Bridge.denoteCV_ext h1a c2.ext)
      (ConRon.Bridge.denoteL_ext h1b c2.ext) h2' hw2 e hW3
    rw [hnp, hsd'] at hcl
    exact ErrClaim.bind_left hcl
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, cbiE.k_check_block_agree.arm1] at he
  -- past the agreements: class-`0` errors only
  cases h4 : callE p (k + 1) "block_shape_with_sort" [pp, r1.tail.headD 0] m3 with
  | error e4 =>
    rw [h4, cbiE.k_block_shape_with_sort.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h4
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [h4, cbiE.k_block_shape_with_sort.arm1] at he
  cases h5 : callE p (k + 1) "check_block_inds_cv_tas" [r1.headD 0, r2.headD 0, r2.tail.headD 0] m4 with
  | error e5 =>
    rw [h5, cbiE.k_check_block_inds_cv_tas.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h5
  | ok q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [h5, cbiE.k_check_block_inds_cv_tas.arm1] at he
  cases h6 : callE p (k + 1) "cons_block_inds" [r4.headD 0, isRec, r5.headD 0, r5.tail.headD 0, vis, 0] m5 with
  | error e6 =>
    rw [h6, cbiE.k_cons_block_inds.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h6
  | ok q6 =>
    obtain ⟨r6, m6⟩ := q6
    rw [h6, cbiE.k_cons_block_inds.arm1] at he; cases he

end sims

end L.Ind
