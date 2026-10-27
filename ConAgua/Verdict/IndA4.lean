import ConAgua.Verdict.IndA2
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Verdict.IndAGen

/-!
# `check_block_tail`'s error refinement (lane `verdicts-b`, helper `ia`)

`checkBlockTailE_claim`: `CheckBlockTailE p` from the claims of `check_block_idx_sorts`,
`check_block_rec` (generated `err_stmt`s) and `check_block_tables` (`CheckBlockTablesE`, in the
shape of `ctbW_simR`); `check_block_tail_rec` is entered through its model `ictrE`.
`cons_block_ctors`, `flush_caches`, `block_nested_bit` and `cons_block_recs_tf` are outside the
verdict closure.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model ictlE_spec (p : Prog) (hf : p.lookup "check_block_tail" = some checkBlockTail)
  fns [hf ↦ ictlE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model ictrE_spec (p : Prog) (hf : p.lookup "check_block_tail_rec" = some checkBlockTailRec)
  fns [hf ↦ ictrE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

-- the error claims of the tail's callees, in the shape of their ok refinements
err_stmt CheckBlockIdxSortsE := checkBlockIdxSorts_refinesC fuel n
err_stmt CheckBlockRecE := checkBlockRec_refinesC fuel n

/-- **`check_block_tables`' error claim**, in the shape of `ctbW_simR` (the recursion over the
members; any fuel `F ≤ 2 ^ 62`). -/
def CheckBlockTablesE (p : Prog) : Prop :=
  ∀ (_ : TabsProg p) (_ : ApdF p) (dn : NIdx → Option ConLeche.Name) (pp : Word) (bs : BlockShape)
    (F : Nat), F ≤ 2 ^ 62 →
    ∀ (m : Mem) (a : AState) (vis : Word) (fe : IFEnv) (mo ml co cl so sl : Word) (mss : List MemberShape)
      (css : List (List (IConstantVal × Nat))) (sss : List (List (List LIdx))),
    StageR dn vis fe m a → DecB (fun m => decBS m pp.toNat) m bs →
    ShapeSrc m pp → PSlR decMS mss mo ml m → PSlR decCNS css co cl m → PSlR decISS sss so sl m → HbMemo m →
    AbsOK m → (∀ f ∈ tablesKeepCallees, AbsKeep p f) →
    ConRon.Bridge.StateOK a → ConRon.Bridge.PinsOK a →
    (∃ pP, ConRon.Bridge.Inductives.dShape a.store bs = some pP) →
    (∃ msP, mss.mapM (ConRon.Bridge.Inductives.dMember a.store) = some msP) →
    (∃ cssP, css.mapM (ConRon.Bridge.Inductives.dCtors a.store) = some cssP) →
    (∃ sssP, sss.mapM (ConRon.Bridge.Inductives.denoteLLists a.store) = some sssP) →
    ∀ e, callE p F "check_block_tables" [pp, mo, ml, co, cl, so, sl, vis] m = .error e →
      ErrClaim (ConRon.Arena.checkBlockTables bs mss css sss fe) a e

section
variable {p : Prog}

theorem checkBlockTailE_claim (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (eIdx : CheckBlockIdxSortsE p) (eRec : CheckBlockRecE p) (eTab : CheckBlockTablesE p) :
    CheckBlockTailE p := by
  intro hkp env₁ henv₁ hV hOpf hLC hLT hApd hCrk hIlpf hP L fs hfs hcl fsR hclR hfR s₀ a dn vis fe bO bL q bp block
    hC hq hblk hM hA hkeep hR hrb hlp hcoh hden qP hqP blockP hbP hTw henv₂ hMs hfRc fsH hclH hfH F hF er he
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  replace he := triple_of_callE_err (ictlE_spec p hP.tail F ⟨s₀.mem, Locals.init []⟩ bO bL q) he
    (Err.code_ne_of_cls hk0)
  simp only at he
  generalize hm : s₀.mem = m at hC hq hblk hM hA hR hrb hlp he
  have hS := hC.stage
  obtain ⟨hdq, hB, hw0, hsrc⟩ := hq
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hq19 := hB.1
  have hk : ∀ k, k < 19 → (q + UInt64.ofNat k).toNat = q.toNat + k := fun k hk => tailToNat (by omega)
  -- the record
  have hdq' : decBPass fe (truncM m) q.toNat = some bp := hdq
  simp only [decBPass, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hdq'
  obtain ⟨cvTas, hcv, pw, hpw, bs, hbs, ctorsAs, hca, sss, hsss, kinds, hkd, nfs, hnfs, params, hpar, rdp,
    hrdp, rd, hrd, cls, hcls, tbl, htbl, rfl⟩ := hdq'
  -- con-ron's reading of the pass record
  obtain ⟨-, hcvP, hpP, hcaP, hssP, -, -, hpaP, hrdP, hclP, htbP⟩ :=
    ConRon.Bridge.Inductives.dPass_inv hqP
  obtain ⟨shP, hshP, hpPeq⟩ : ∃ shP, ConRon.Bridge.Inductives.dShape a.store bs = some shP ∧
      qP.p = ⟨shP⟩ := by
    simp only [ConRon.Bridge.Inductives.dParts, Option.map_eq_some_iff] at hpP
    obtain ⟨shP, h1, h2⟩ := hpP; exact ⟨shP, h1, h2.symm⟩
  obtain ⟨hmsP, -, hnPP, -, -, -, -⟩ := ConRon.Bridge.Inductives.dShape_inv hshP
  obtain ⟨hw3, hpwb⟩ := bpWord hpw (hk 3 (by decide))
  rw [show (q + UInt64.ofNat 3 : Word) = q + 3 from rfl] at hw3
  rw [hw3] at hsrc hrb
  have hpw' : (UInt64.ofNat pw : Word).toNat = pw := UInt64.toNat_ofNat_of_lt' hpwb
  have hbsD : DecB (fun m => decBS m (UInt64.ofNat pw : Word).toNat) m bs := by rw [hpw']; exact hbs
  obtain ⟨hmem, -, -, -, -, -, -⟩ := decBS_some hbs
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hbsD hsrc
  have hpw9 : pw + 9 ≤ iwTop m := by rw [← hpw']; exact hq9
  -- the slices
  have hmss := bpPSl decMS_mono hmem (fun o l h1 h2 => hsrc o l (by rw [hpw']; exact h1) (by rw [hpw']; exact h2))
    (w := UInt64.ofNat pw) (w1 := UInt64.ofNat pw + 1) hpw'
    (by rw [UInt64.toNat_add, hpw']; simp; omega)
  have e : ∀ k : Nat, k < 19 → ∀ w : Word, w = q + UInt64.ofNat k → w.toNat = q.toNat + k :=
    fun k hk w hw => by rw [hw]; exact tailToNat (by omega)
  have hcvs := bpPSl (fun q => OMono.decCVp q) hcv (hB.2 1 (by simp)) (w := q + 1) (w1 := q + 2)
    (e 1 (by decide) _ rfl) (e 2 (by decide) _ rfl)
  have hcas := bpPSl decCNS_mono hca (hB.2 4 (by simp)) (w := q + 4) (w1 := q + 5)
    (e 4 (by decide) _ rfl) (e 5 (by decide) _ rfl)
  have hsss' := bpPSl decISS_mono hsss (hB.2 6 (by simp)) (w := q + 6) (w1 := q + 7)
    (e 6 (by decide) _ rfl) (e 7 (by decide) _ rfl)
  have hkfm : ∀ q, OMono (fun m => decLH m (decPL m (decLH m (decKL m))) q) :=
    fun q => OMono.decAt (fun o l => OMono.decPL (fun q => OMono.decAt (fun o l => decKL_mono o l) q) o l) q
  have hks := bpPSl hkfm hkd (hB.2 8 (by simp)) (w := q + 8) (w1 := q + 9)
    (e 8 (by decide) _ rfl) (e 9 (by decide) _ rfl)
  obtain ⟨hpd, hpb⟩ := bpHSl hpar (hB.2 12 (by simp)) (w := q + 12) (w1 := q + 13)
    (e 12 (by decide) _ rfl) (e 13 (by decide) _ rfl)
  obtain ⟨hw14, hrdb⟩ := bpWord hrdp (e 14 (by decide) _ rfl)
  have hrdD : DecB (fun m => decCR m (UInt64.ofNat rdp : Word).toNat) m rd := by
    rw [UInt64.toNat_ofNat_of_lt' hrdb]; exact hrd
  have hcls' := bpPSl (fun q => decTM_mono q) hcls (hB.2 15 (by simp)) (w := q + 15) (w1 := q + 16)
    (e 15 (by decide) _ rfl) (e 16 (by decide) _ rfl)
  have htbl' := bpPSl (fun q => decNCN_mono q) htbl (hB.2 17 (by simp)) (w := q + 17) (w1 := q + 18)
    (e 17 (by decide) _ rfl) (e 18 (by decide) _ rfl)
  -- `check_block_idx_sorts`
  cases F with
  | zero => rw [ictlE.eq_1] at he; cases he; exact absurd Err.cls_outOfFuel hk0
  | succ n =>
  have hn : n ≤ 2 ^ 62 := by omega
  rw [ictlE.arm1, hw0, hw3] at he
  unfold ConRon.Arena.checkBlockTail
  dsimp only
  cases c1 : callE p n "check_block_idx_sorts" [vis, UInt64.ofNat pw, rdW (m.arr64 IW) (UInt64.ofNat pw),
      rdW (m.arr64 IW) (UInt64.ofNat pw + 1), rdW (m.arr64 IW) (q + 1), rdW (m.arr64 IW) (q + 2)] m with
  | error e1 =>
    rw [c1, ictlE.k_check_block_idx_sorts.none] at he
    cases he
    exact ErrClaim.bind_left (eIdx hkp henv₁ hOpf hLC hLT hP.idx ⟨m, Locals.init []⟩ a _ _ _ _ _ bs bs.members cvTas
      hC hA hbsD hsrc hmss hcvs hshP hcvP hTw hden n hn _ c1)
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [c1, ictlE.k_check_block_idx_sorts.eq_2] at he
  have d1 := callW_of_callE c1
  obtain ⟨s1, rfl, -, hok, hC1, hg1, -, hA1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (checkBlockIdxSorts_refinesC hkp henv₁ hOpf hLC hLT hP.idx n hn _ a _ _ _ _ _ bs bs.members cvTas hC hA hbsD
      hsrc hmss hcvs hshP hcvP hTw hden) d1
  replace hg1 : IWGrow m s1.mem := hg1
  have hrun := AM.run_of_ok _ a hok
  obtain ⟨c1', -⟩ := ConRon.Bridge.Inductives.checkBlockIdxSorts_specF fe
    (ConRon.Bridge.CoreSpec.of_core rfl) henv₁ bs shP bs.members shP.members cvTas qP.cvTas hTw _ _ _
    hC.check ⟨hshP, hmsP, hcvP, hden⟩ hrun
  have hM1 : HbMemo s1.mem := HbMemo.ofClosed hcl (hfs _ (by decide)) d1 hM
  have hR1 : RcMR s1.mem := RcMR.ofClosed hclR (hfR _ (by decide)) d1 hR
  have hk1 : KeepW m s1.mem := callW_keepW d1
  refine ErrClaim.bind_right (partsRunOfOk hok) ?_
  generalize AM.st (ConRon.Arena.checkBlockIdxSorts V fe bs bs.members cvTas) a = a1 at hC1 c1' ⊢
  have hS1 := hC1.stage
  -- `cons_block_ctors` (the twin's `fe₂`, a pure function)
  obtain ⟨hnp1, -, -, -⟩ := partsShapeWords hg1 hbsD hq9
  have hca1 := hcas.grow decCNS_mono hg1
  rw [partsRdIW_grow hg1 (w := q + 4) (by rw [e 4 (by decide) (q + 4) rfl]; omega),
    partsRdIW_grow hg1 (w := q + 5) (by rw [e 5 (by decide) (q + 5) rfl]; omega), hnp1] at he
  cases c2 : callE p n "cons_block_ctors" [UInt64.ofNat bs.nP, rdW (m.arr64 IW) (q + 4),
      rdW (m.arr64 IW) (q + 5), vis] s1.mem with
  | error e2 =>
    rw [c2, ictlE.k_cons_block_ctors.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) c2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [c2, ictlE.k_cons_block_ctors.eq_2] at he
  have d2 := callW_of_callE c2
  obtain ⟨s2, rfl, -, hS2, hg2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (consBlockCtors_refines p hP.recp hP.hci hP.hcs hP.hcbc n _ a1 dn fe _ _ _ vis ctorsAs hS1 hca1) d2
  have hM2 : HbMemo s2.mem := HbMemo.ofClosed hcl (hfs _ (by decide)) d2 hM1
  have hA2 : AbsOK s2.mem := hkeep _ (by simp [tailKeepCalleesC, grcKeepCalleesC]) _ _ _ _ _ d2 hA1
  have hR2 : RcMR s2.mem := RcMR.ofClosed hclR (hfR _ (by decide)) d2 hR1
  have hk2 := hk1.trans (callW_keepW d2)
  rw [UInt64.toNat_ofNat_of_lt' (partsShapeWords (IWGrow.refl m) hbsD hq9).2.1] at hS2
  obtain ⟨hcons, hconsOK⟩ := ConRon.Bridge.Inductives.consBlockCtors_spec a1.store bs.nP ctorsAs
    qP.ctorsAs fe env₁ (ConRon.Bridge.Inductives.dCtors_ext.list c1'.ext _ _ hcaP)
    (ConRon.Bridge.denoteFEnv_mono c1'.ext hden) hcoh
  -- the flush
  cases c3 : callE p n "flush_caches" [] s2.mem with
  | error e3 =>
    rw [c3, ictlE.k_flush_caches.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) c3
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [c3, ictlE.k_flush_caches.eq_2] at he
  have d3 := callW_of_callE c3
  obtain ⟨u3, a3, hrun3, hS3, hg3, hM3⟩ := tailSimFlush hP.flush n hS2 hM2 _ _ d3
  have hR3 : RcMR m3 := RcMR.ofClosed hclR (hfR _ (by decide)) d3 hR2
  have hk3 := hk2.trans (callW_keepW d3)
  have hA3 : AbsOK m3 := by
    obtain ⟨s', rfl, -, -, hmem⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩) (flushCaches_spec p hP.flush n _) d3
    rw [hmem]; exact AFr.of_frame (flushMem_frame _) (by decide) (by decide) hA2
  obtain ⟨hck3, -, hst3⟩ := ConRon.Bridge.Inductives.ReadOK.flush (μ := V)
    (⟨c1'.ok.state, c1'.ok.pins, hconsOK c1'.ok.state.wf (ConRon.Bridge.TablesStored.of_envWF henv₁) c1'.ok.ienv.toS a1 rfl⟩ :
      ConRon.Bridge.Inductives.ReadOK _ _ a1) hrun3
  have hC3 := StageC.of_parts hS3 hck3 hA3
    (fun k x e => by rw [hst3]; exact c1'.ext.lss.ls.ns k x (hC.mem.dnN k x e))
  refine ErrClaim.bind_right hrun3 ?_
  have hg03 := (hg1.trans hg2).trans hg3
  -- `block_nested_bit` (the twin's `nested`, a pure function)
  have hks3 := hks.grow hkfm hg03
  rw [partsRdIW_grow hg03 (w := q + 8) (by rw [e 8 (by decide) (q + 8) rfl]; omega),
    partsRdIW_grow hg03 (w := q + 9) (by rw [e 9 (by decide) (q + 9) rfl]; omega)] at he
  cases c4 : callE p n "block_nested_bit" [UInt64.ofNat pw, rdW (m.arr64 IW) (q + 8), rdW (m.arr64 IW) (q + 9)] m3 with
  | error e4 =>
    rw [c4, ictlE.k_block_nested_bit.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) c4
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [c4, ictlE.k_block_nested_bit.eq_2] at he
  have d4 := callW_of_callE c4
  obtain ⟨s4, rfl, hs4, hr4⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (blockNestedBit_refines p hP.nf hP.ni hP.nm hP.nk hP.ng hP.nb n _ _ _ _ bs kinds hS3.2.2.2.1
      (DecB.get (decBS_mono _) (hbsD.grow (decBS_mono _) hg03)) (DecB.get (OMono.decPL hkfm _ _) hks3.1)) d4
  subst hs4
  have hnb : (r4.headD 0 != 0) = ConRon.Arena.blockNestedBit bs kinds := by
    rw [hr4]; cases ConRon.Arena.blockNestedBit bs kinds <;> rfl
  simp only at he c4 d4
  -- through `check_block_tail_rec`
  cases c5 : callE p n "check_block_tail_rec" [bO, bL, q, UInt64.ofNat pw, r2.headD 0, r4.headD 0] m3 with
  | ok q5 =>
    obtain ⟨r5, m5⟩ := q5
    rw [c5, ictlE.k_check_block_tail_rec.eq_2] at he
    cases he
  | error e5 =>
  rw [c5, ictlE.k_check_block_tail_rec.none] at he
  cases he
  have h5 := triple_of_callE_err (ictrE_spec p hP.tailrec n ⟨m3, Locals.init []⟩ bO bL q (UInt64.ofNat pw)
    (r2.headD 0) (r4.headD 0)) c5 (Err.code_ne_of_cls hk0)
  simp only at h5
  cases n with
  | zero => rw [ictrE.eq_1] at h5; cases h5; exact absurd Err.cls_outOfFuel hk0
  | succ k =>
  rw [ictrE.arm1] at h5
  -- `check_block_rec`
  have hrd3 : rdW (m3.arr64 IW) (q + 14) = UInt64.ofNat rdp := by
    rw [partsRdIW_grow hg03 (w := q + 14) (by rw [e 14 (by decide) (q + 14) rfl]; omega)]; exact hw14
  have hbs3 := hbsD.grow (decBS_mono _) hg03
  have hsrc3 := partsHsrc_grow hg03 hq9 hsrc
  obtain ⟨-, -, hmv3⟩ := partsShapeFacts hbs3 hsrc3
  have hBS3 : BSOK m3 (UInt64.ofNat pw : Word).toNat bs :=
    ⟨hbs3, hsrc3, fun o l j v ho hl hj hv => by have := hmv3 o l j v ho hl hj hv; omega⟩
  have hrb3 : RecsB m3 (UInt64.ofNat pw) := hrb.grow hg03 (by rw [hpw']; omega)
  have r15 : rdW (m3.arr64 IW) (q + 15) = rdW (m.arr64 IW) (q + 15) :=
    partsRdIW_grow hg03 (by rw [e 15 (by decide) (q + 15) rfl]; omega)
  have r16 : rdW (m3.arr64 IW) (q + 16) = rdW (m.arr64 IW) (q + 16) :=
    partsRdIW_grow hg03 (by rw [e 16 (by decide) (q + 16) rfl]; omega)
  have hlp3 : ClassesLp m3 (rdW (m3.arr64 IW) (q + 15)) (rdW (m3.arr64 IW) (q + 16)) := by
    rw [r15, r16]; exact hlp.grow hcls' hg03 hk3 hS.2.2.2.1
  have hpre : BSOK m3 (UInt64.ofNat pw : Word).toNat bs ∧
      decHL m3 (rdW (m3.arr64 IW) (q + 12)).toNat (rdW (m3.arr64 IW) (q + 13)).toNat = some params ∧
      (rdW (m3.arr64 IW) (q + 12)).toNat + (rdW (m3.arr64 IW) (q + 13)).toNat ≤ iwTop m3 ∧
      PSlR decNCN tbl (rdW (m3.arr64 IW) (q + 17)) (rdW (m3.arr64 IW) (q + 18)) m3 ∧
      DecB (fun m => decCR m (rdW (m3.arr64 IW) (q + 14)).toNat) m3 rd ∧
      PSlR decTM cls (rdW (m3.arr64 IW) (q + 15)) (rdW (m3.arr64 IW) (q + 16)) m3 ∧
      PSlR decCVp cvTas (rdW (m3.arr64 IW) (q + 1)) (rdW (m3.arr64 IW) (q + 2)) m3 ∧
      DecB (fun m => decEBlk dn m bO.toNat bL.toNat) m3 block := by
    have r : ∀ k, k < 19 → ∀ w : Word, w = q + UInt64.ofNat k → rdW (m3.arr64 IW) w = rdW (m.arr64 IW) w :=
      fun k hk w hw => partsRdIW_grow hg03 (by rw [e k hk w hw]; omega)
    refine ⟨hBS3, ?_, ?_, ?_, ?_, ?_, ?_, hblk.grow ?_ hg03⟩
    · rw [r 12 (by decide) (q + 12) rfl, r 13 (by decide) (q + 13) rfl]; exact (by rw [decHL_grow3 hg03 hpb]; exact hpd)
    · rw [r 12 (by decide) (q + 12) rfl, r 13 (by decide) (q + 13) rfl]; exact Nat.le_trans hpb hg03.1
    · rw [r 17 (by decide) (q + 17) rfl, r 18 (by decide) (q + 18) rfl]; exact htbl'.grow (fun q => decNCN_mono q) hg03
    · rw [hrd3]; exact hrdD.grow (decCR_mono _) hg03
    · rw [r 15 (by decide) (q + 15) rfl, r 16 (by decide) (q + 16) rfl]; exact hcls'.grow (fun q => decTM_mono q) hg03
    · rw [r 1 (by decide) (q + 1) rfl, r 2 (by decide) (q + 2) rfl]; exact hcvs.grow (fun q => OMono.decCVp q) hg03
    · exact decEBlk_mono _ _ _
  have hx3 : Ext a.store a3.store := by rw [hst3]; exact c1'.ext
  have hnP : qP.p.nP = bs.nP := by rw [hpPeq]; exact hnPP.symm
  rw [hnP] at henv₂
  rw [hpPeq] at hMs
  have dd1 := ConRon.Bridge.Inductives.dShape_ext hx3 _ _ hshP
  have dd2 := ConRon.Bridge.denoteEList_ext hx3 _ _ hpaP
  have dd3 := ConRon.Bridge.Inductives.dCtorNf_ext.list hx3 _ _ htbP
  have dd4 := ConRon.Bridge.Inductives.dClassRead_ext hx3 _ _ hrdP
  have dd5 := ConRon.Bridge.Inductives.dMajor_ext.list hx3 _ _ hclP
  have dd6 : cvTas.mapM (Frontend.denoteCV a3.store) = some qP.cvTas :=
    ConRon.Bridge.Inductives.DExt.list (d := Frontend.denoteCV)
      (fun hx _ _ h => ConRon.Bridge.denoteCV_ext h hx) hx3 _ _ hcvP
  have dd7 := ConRon.Bridge.denoteCIList_mono hx3 _ _ hbP
  have hden₂ : ConRon.Bridge.denoteFEnv a3.store (ConRon.Arena.consBlockCtors bs.nP ctorsAs fe) =
      some (ConLeche.consBlockCtors bs.nP qP.ctorsAs env₁) := by
    obtain ⟨e, h, rfl⟩ := hcons.denote; rw [hst3]; exact h
  have hfRc1 : ∀ f ∈ grcMemoCallees, f ∈ fsR := fun f hf => hfR f (by
    simp only [grcMemoCallees, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl <;> decide)
  cases c6 : callE p k "check_block_rec" [r2.headD 0, UInt64.ofNat pw, r4.headD 0,
      rdW (m3.arr64 IW) (q + 12), rdW (m3.arr64 IW) (q + 13), rdW (m3.arr64 IW) (q + 17),
      rdW (m3.arr64 IW) (q + 18), rdW (m3.arr64 IW) (q + 14), rdW (m3.arr64 IW) (q + 15),
      rdW (m3.arr64 IW) (q + 16), bO, bL, rdW (m3.arr64 IW) (q + 1), rdW (m3.arr64 IW) (q + 2)] m3 with
  | error e6 =>
    rw [c6, ictrE.k_check_block_rec.none] at h5
    cases h5
    rw [← hnb]
    exact ErrClaim.bind_left (eRec hkp henv₂ hV hApd hCrk hIlpf hP.crec hP.grc hclR hfRc1
      ⟨m3, Locals.init []⟩ a3 dn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bs
      params tbl rd cls cvTas block hC3 hpre hrb3 hlp3 hR3 hA3
      (fun f hf => hkeep f (List.mem_append_right _ hf)) hcons.coh hden₂ dd1 dd2 dd3 dd4 dd5 dd6 dd7 hMs hTw
      (fun f hf => hfRc f (List.mem_append_left _ hf)) k (by omega) _ c6)
  | ok q6 =>
  obtain ⟨r6, m6⟩ := q6
  rw [c6, ictrE.k_check_block_rec.eq_2] at h5
  have d6 := callW_of_callE c6
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
    cases k with
    | zero =>
      obtain ⟨e0, h0, -⟩ := callE_zero p "check_block_rec" [r2.headD 0, UInt64.ofNat pw, r4.headD 0,
        rdW (m3.arr64 IW) (q + 12), rdW (m3.arr64 IW) (q + 13), rdW (m3.arr64 IW) (q + 17),
        rdW (m3.arr64 IW) (q + 18), rdW (m3.arr64 IW) (q + 14), rdW (m3.arr64 IW) (q + 15),
        rdW (m3.arr64 IW) (q + 16), bO, bL, rdW (m3.arr64 IW) (q + 1), rdW (m3.arr64 IW) (q + 2)] m3
      rw [h0] at c6; cases c6
    | succ j => exact ⟨j, rfl⟩
  have hM3' : HbMemo m3 := hM3
  obtain ⟨s5, hs5, -, hok5, hC5', hg5, hd5, hA5, hR5, -⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (checkBlockRec_refinesC hkp henv₂ hV hApd hCrk hIlpf hP.crec hP.grc hclR hfRc1 j (by omega)
      ⟨m3, Locals.init []⟩ a3 dn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bs
      params tbl rd cls cvTas block hC3 hpre hrb3 hlp3 hR3 hA3
      (fun f hf => hkeep f (List.mem_append_right _ hf)) hcons.coh hden₂ dd1 dd2 dd3 dd4 dd5 dd6 dd7 hMs hTw
      (fun f hf => hfRc f (List.mem_append_left _ hf))) d6
  simp only at hs5 hok5 hC5' hg5 hd5 hA5 hR5
  subst hs5
  rw [hnb] at hok5 hC5' hd5
  have hM5 : HbMemo s5.mem := HbMemo.ofClosed hcl (hfs _ (by decide)) d6 hM3
  have hrun5 := AM.run_of_ok _ a3 hok5
  generalize AM.res (ConRon.Arena.checkBlockRec V (ConRon.Arena.consBlockCtors bs.nP ctorsAs fe) ⟨bs⟩
    (ConRon.Arena.blockNestedBit bs kinds) params tbl rd cls block cvTas) a3 = x5 at hrun5 hC5' hd5
  generalize AM.st (ConRon.Arena.checkBlockRec V (ConRon.Arena.consBlockCtors bs.nP ctorsAs fe) ⟨bs⟩
    (ConRon.Arena.blockNestedBit bs kinds) params tbl rd cls block cvTas) a3 = a5 at hrun5 hC5'
  obtain ⟨fe2b, outs⟩ := x5
  refine ErrClaim.bind_right hrun5 ?_
  dsimp only
  have hS5 := hC5'.stage
  -- con-ron's recursor stage on the twin's run (the recursors' readings, their freshness)
  obtain ⟨cr3, outP, ⟨hcoh₂b, hfe₂b, hout, hfresh⟩, -⟩ :=
    ConRon.Bridge.Inductives.recStage (μ := V) rfl (ConRon.Bridge.CoreSpec.of_core rfl) _ _ ⟨bs⟩ ⟨shP⟩
      _ params qP.params tbl qP.tbl.toList rd qP.rd cls qP.cls cvTas qP.cvTas block blockP henv₂ hcons.coh hTw
      hMs a3 a5 _ hck3
      ⟨hden₂, by simp only [ConRon.Bridge.Inductives.dParts, ConRon.Bridge.Inductives.dShape_ext hx3 _ _ hshP]; rfl,
        dd2, dd3, dd4, dd5, dd6, dd7⟩ hrun5
  have x35 := cr3.ext
  -- `cons_block_recs_tf`
  rw [hS2.1.env.vis]
  cases c7 : callE p (j + 1) "cons_block_recs_tf" [r2.headD 0, UInt64.ofNat pw, 0, r6.tail.headD 0, r6.tail.tail.headD 0,
      r6.headD 0] s5.mem with
  | error e7 =>
    rw [c7, ictrE.k_cons_block_recs_tf.none] at h5
    cases h5
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) c7
  | ok q7 =>
  obtain ⟨r7, m7⟩ := q7
  rw [c7, ictrE.k_cons_block_recs_tf.eq_2] at h5
  have d7 := callW_of_callE c7
  obtain ⟨fe3, a6, hrun6, hS6, hg6, hM6, hA6⟩ := consRecsTFSim_of L hcl (hfs _ (by decide)) (j + 1) dn (r6.headD 0)
    (r2.headD 0) (UInt64.ofNat pw) fe2b s5.mem a5 bs r6.tail outs hS5
    ((hbsD.grow (decBS_mono _) hg03).grow (decBS_mono _) hg5) hd5 hM5 hA5 _ _ d7
  have hR6 : RcMR m7 := RcMR.ofClosed hclR (hfRc _ (by simp)) d7 hR5
  refine ErrClaim.bind_right hrun6 ?_
  -- con-ron's recursors' cons on the twin's run: the store extended, the state and pins kept
  have hvis : fe2b.visibleBelow = (ConRon.Arena.consBlockCtors bs.nP ctorsAs fe).visibleBelow := by
    rw [hcoh₂b.1, hcons.coh.1, hfe₂b]
  have hfind₂b : fe2b.find? = (ConRon.Arena.consBlockCtors bs.nP ctorsAs fe).find? := by
    funext n; rw [hcoh₂b.find?, hcons.coh.find?, hfe₂b]
  have hraw₂b : ∀ n, fe2b.rawTable? n = (ConRon.Arena.consBlockCtors bs.nP ctorsAs fe).rawTable? n := by
    intro n; rw [hcoh₂b.rawTable?, hcons.coh.rawTable?, hfe₂b]
  have hden₂b : ConRon.Bridge.denoteFEnv a5.store fe2b = some (ConLeche.consBlockCtors bs.nP qP.ctorsAs env₁) := by
    have h' := ConRon.Bridge.denoteFEnv_mono x35 hden₂
    simp only [ConRon.Bridge.denoteFEnv] at h' ⊢; rw [hfe₂b]; exact h'
  have x05 : Ext a.store a5.store := hx3.trans x35
  have hview : (fe2b.restrictTo (ConRon.Arena.consBlockCtors bs.nP ctorsAs fe).visibleBelow).find?
      = (ConRon.Arena.consBlockCtors bs.nP ctorsAs fe).find? := by
    rw [← hvis]; exact hfind₂b
  obtain ⟨c4'', -⟩ := ConRon.Bridge.Inductives.consBlockRecsTF_spec (μ := V)
    (ConRon.Arena.consBlockCtors bs.nP ctorsAs fe).visibleBelow bs shP outs outP 0
    fe2b _ a5 a6 fe3 cr3.ok (ConRon.Bridge.Inductives.RC.IFEnvOK.of_find? cr3.ok.ienv hview hraw₂b)
    (Nat.le_of_eq hvis.symm) hcoh₂b hden₂b (ConRon.Bridge.Inductives.dShape_ext x05 _ _ hshP) hout hfresh
    (by rw [hS2.1.env.vis]; exact hrun6)
  have x06 : Ext a.store a6.store := x05.trans c4''.ext
  -- `check_block_tables`
  have hg06 := (hg03.trans hg5).trans hg6
  have r : ∀ k, k < 19 → ∀ w : Word, w = q + UInt64.ofNat k → rdW (m7.arr64 IW) w = rdW (m.arr64 IW) w :=
    fun k hk w hw => partsRdIW_grow hg06 (by rw [e k hk w hw]; omega)
  rw [partsRdIW_grow hg06 (w := UInt64.ofNat pw) (by rw [hpw']; omega),
    partsRdIW_grow hg06 (w := UInt64.ofNat pw + 1) (by rw [UInt64.toNat_add, hpw']; simp; omega),
    r 4 (by decide) (q + 4) rfl, r 5 (by decide) (q + 5) rfl, r 6 (by decide) (q + 6) rfl,
    r 7 (by decide) (q + 7) rfl] at h5
  cases c8 : callE p (j + 1) "check_block_tables" [UInt64.ofNat pw, rdW (m.arr64 IW) (UInt64.ofNat pw),
      rdW (m.arr64 IW) (UInt64.ofNat pw + 1), rdW (m.arr64 IW) (q + 4), rdW (m.arr64 IW) (q + 5),
      rdW (m.arr64 IW) (q + 6), rdW (m.arr64 IW) (q + 7), r7.headD 0] m7 with
  | error e8 =>
    rw [c8, ictrE.k_check_block_tables.none] at h5
    cases h5
    exact eTab hP.tabs hApd dn (UInt64.ofNat pw) bs (j + 1) (by omega) m7 a6 (r7.headD 0) fe3 _ _ _ _ _ _
      bs.members ctorsAs sss hS6 (hbsD.grow (decBS_mono _) hg06) (partsHsrc_grow hg06 hq9 hsrc)
      (hmss.grow decMS_mono hg06) (hcas.grow decCNS_mono hg06) (hsss'.grow decISS_mono hg06) hM6 hA6
      (fun f hf => hkeep f (by simp_all [tablesKeepCallees, tailKeepCalleesC, grcKeepCalleesC]))
      c4''.ok.state c4''.ok.pins ⟨shP, ConRon.Bridge.Inductives.dShape_ext x06 _ _ hshP⟩
      ⟨_, ConRon.Bridge.Inductives.dMember_ext.list x06 _ _ hmsP⟩
      ⟨_, ConRon.Bridge.Inductives.dCtors_ext.list x06 _ _ hcaP⟩
      ⟨_, ConRon.Bridge.Inductives.DExt.list (d := ConRon.Bridge.Inductives.denoteLLists)
        (fun hx x y h => ConRon.Bridge.Inductives.BI.denoteLLists_ext hx x y h) x06 _ _ hssP⟩ _ c8
  | ok q8 =>
    rw [c8] at h5
    cases h5

end

end L.Ind
