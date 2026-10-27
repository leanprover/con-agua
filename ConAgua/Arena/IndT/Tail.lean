import ConAgua.Arena.IndInstallSpec35
import ConAgua.Arena.IndT.Install5
import ConAgua.Arena.IndT.GenRec3
import ConAgua.Arena.IndT.ArmMemos
import ConAgua.Arena.IndRealSctC
import ConAgua.Arena.IndInstallSpec29
import ConAgua.Arena.IndT.Install4
import ConAgua.Arena.RecCheckSpec4

/-!
# `checkBlockTail` under `StageC` (lane `indstaget`)

`check_block_tail`'s model (over the program's own calls), from `StageC` at the formers' index
and the pass record's denotation (con-ron's `checkBlockTail_of`): the index binders' sorts
(`checkBlockIdxSorts_refinesC`), the constructors consed (L only; con-ron's `consBlockCtors_spec`
gives the pushed index's reading), the flush entering them (`ReadOK.flush`: `StageC` at the pushed
index and environment), the recursor stage (`checkBlockRec_refinesC`), then the recursors consed
and the tables under `StageR` (no core call follows them).
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- `StageC` from its parts: the stage relation, con-ron's `CheckOK`, the memory's half from
`AbsOK`, the name decoder's agreement. -/
theorem StageC.of_parts {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {env : ConLeche.Env} {m : Mem} {a : AState} (hS : StageR dn vis fe m a)
    (hck : ConRon.Bridge.CheckOK V env fe a) (hA : AbsOK m)
    (hdn : ∀ (k : NIdx) (x : ConLeche.Name), dn k = some x → denoteN a.store.ns k = some x) :
    StageC dn vis fe env m a :=
  ⟨hS, hck,
    ⟨hA.2.2.2.2.2.1, hA.2.2.2.2.2.2.1, hA.2.2.2.2.2.2.2.1, ⟨hA.2.2.2.1, hA.1, hA.2.2.2.2.1⟩, hdn⟩,
    hA.2.2.2.2.2.2.2.2⟩

section sims
variable {p : Prog} (hkp : KnotStageProg p) {env₁ : ConLeche.Env} (henv₁ : ConLeche.EnvWF env₁)
  (hV : ValProg p)
  (hOpf : OpfF p) (hLC : LvlCacheProg p) (hLT : p.lookup "lv_leq_top" = some lvLeqTop)
  (hApd : ApdF p) (hCrk : CrKeep p) (hIlpf : IlpfF p)

include hkp henv₁ hV hOpf hLC hLT hApd hCrk hIlpf in
/-- **`check_block_tail` under `StageC`** (`ictlW_sim`'s; twin side con-ron's `checkBlockTail_of`). -/
theorem ictlW_simC (hP : TailProg p) (hRecs : ConsRecsTFSim p) {fs : List FnName}
    (hfs : ∀ f ∈ tailCallees, f ∈ fs) (hcl : closedA p hbFreeA hbFreeC fs = true) (n : Nat)
    {fsR : List FnName} (hclR : closedA p rcFreeA rcFreeC fsR = true)
    (hfR : ∀ f ∈ tailRcCallees, f ∈ fsR) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {m : Mem} {a : AState} {bO bL q : Word} {bp : BlockPass} {block : List IConstantInfo}
    (hn : n ≤ 2 ^ 62) (hC : StageC dn vis fe env₁ m a) (hq : BPassR vis fe m q bp)
    (hblk : DecB (fun m => decEBlk dn m bO.toNat bL.toNat) m block) (hM : HbMemo m) (hA : AbsOK m)
    (hkeep : ∀ f ∈ tailKeepCalleesC, AbsKeep p f) (hR : RcMR m)
    (hrb : RecsB m (rdW (m.arr64 IW) (q + 3)))
    (hlp : ClassesLp m (rdW (m.arr64 IW) (q + 15)) (rdW (m.arr64 IW) (q + 16)))

    (hcoh : ConRon.Bridge.IFEnvCoh fe) (hden : ConRon.Bridge.denoteFEnv a.store fe = some env₁)
    {qP : ConLeche.BlockPass ConLeche.Env}
    (hqP : ConRon.Bridge.Inductives.dPass a.store env₁ bp = some qP)
    {blockP : List ConLeche.ConstantInfo} (hbP : Frontend.denoteCIList a.store block = some blockP)
    (hTw : ∀ cv ∈ qP.cvTas, ConLeche.Expr.WScoped 0 cv.type)
    (henv₂ : ConLeche.EnvWF (ConLeche.consBlockCtors qP.p.nP qP.ctorsAs env₁))
    (hMs : ∀ M ∈ qP.cls, ConLeche.Cached.ClassMajScoped qP.p.nP M)
    (hfRc : ∀ f ∈ grcRcCallees ++ ["cons_block_recs_tf"], f ∈ fsR) {fsH : List FnName}
    (hclH : closedA p rcHbFreeA rcHbFreeC fsH = true) (hfH : "check_block_tables" ∈ fsH) :
    Sim (ictlW p n m bO bL q) (ConRon.Arena.checkBlockTail V block bp) a
      (fun r x m' a' => StageR dn (r.headD 0) x m' a' ∧ IWGrow m m' ∧ HbMemo m' ∧ AbsOK m' ∧ RcMR m') := by
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
  unfold ictlW
  rw [hw0, hw3]
  unfold ConRon.Arena.checkBlockTail
  refine Sim.bindK (K := ictlK1 p n bO bL q (UInt64.ofNat pw) vis) rfl (fun _ _ => rfl)
    (Q := fun _ _ m1 a1 => StageC dn vis fe env₁ m1 a1 ∧ IWGrow m m1 ∧ HbMemo m1 ∧ RcMR m1 ∧
      KeepW m m1 ∧ AbsOK m1 ∧ ConRon.Bridge.CoreStep V env₁ fe a a1)
    (fun r m1 e1 => by
      obtain ⟨s1, rfl, -, hok, hC1, hg1, -, hA1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
        (checkBlockIdxSorts_refinesC hkp henv₁ hOpf hLC hLT hP.idx n hn _ a _ _ _ _ _ bs bs.members cvTas hC hA hbsD
          hsrc hmss hcvs hshP hcvP hTw hden) e1
      have hrun := AM.run_of_ok _ a hok
      obtain ⟨c1, -⟩ := ConRon.Bridge.Inductives.checkBlockIdxSorts_specF fe
        (ConRon.Bridge.CoreSpec.of_core rfl) henv₁ bs shP bs.members shP.members cvTas qP.cvTas hTw _ _ _
        hC.check ⟨hshP, hmsP, hcvP, hden⟩ hrun
      exact ⟨_, _, partsRunOfOk hok, hC1, hg1, HbMemo.ofClosed hcl (hfs _ (by decide)) e1 hM,
        RcMR.ofClosed hclR (hfR _ (by decide)) e1 hR, callW_keepW e1, hA1, c1⟩) ?_
  rintro r1 - m1 a1 ⟨hC1, hg1, hM1, hR1, hk1, hA1, c1⟩
  have hS1 := hC1.stage
  rw [ictlK1_some]
  -- `cons_block_ctors` (the twin's `fe₂`, a pure function)
  obtain ⟨hnp1, -, -, -⟩ := partsShapeWords hg1 hbsD hq9
  have hca1 := hcas.grow decCNS_mono hg1
  refine Sim.mstep (K := ictlK2 p n bO bL q (UInt64.ofNat pw)) rfl (fun _ _ => rfl) fun r2 m2 h2 => ?_
  rw [partsRdIW_grow hg1 (w := q + 4) (by rw [e 4 (by decide) (q + 4) rfl]; omega),
    partsRdIW_grow hg1 (w := q + 5) (by rw [e 5 (by decide) (q + 5) rfl]; omega)] at h2
  rw [hnp1] at h2
  obtain ⟨s2, rfl, -, hS2, hg2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (consBlockCtors_refines p hP.recp hP.hci hP.hcs hP.hcbc n _ a1 dn fe _ _ _ vis ctorsAs hS1 hca1) h2
  have hM2 : HbMemo s2.mem := HbMemo.ofClosed hcl (hfs _ (by decide)) h2 hM1
  have hA2 : AbsOK s2.mem := hkeep _ (by simp [tailKeepCalleesC, grcKeepCalleesC]) _ _ _ _ _ h2 hA1
  have hR2 : RcMR s2.mem := RcMR.ofClosed hclR (hfR _ (by decide)) h2 hR1
  have hk2 := hk1.trans (callW_keepW h2)
  rw [UInt64.toNat_ofNat_of_lt' (partsShapeWords (IWGrow.refl m) hbsD hq9).2.1] at hS2
  obtain ⟨hcons, hconsOK⟩ := ConRon.Bridge.Inductives.consBlockCtors_spec a1.store bs.nP ctorsAs
    qP.ctorsAs fe env₁ (ConRon.Bridge.Inductives.dCtors_ext.list c1.ext _ _ hcaP)
    (ConRon.Bridge.denoteFEnv_mono c1.ext hden) hcoh
  rw [ictlK2_some]
  -- the flush
  dsimp only
  refine Sim.bindK (K := ictlK3 p n bO bL q (UInt64.ofNat pw) (r2.headD 0)) rfl (fun _ _ => rfl)
    (Sim.withRunC (Sim.withFr (F := fun m3 => (RcMR m3 ∧ KeepW m m3) ∧ AbsOK m3) (tailSimFlush hP.flush n hS2 hM2)
      (fun _ m3 e3 => ⟨⟨RcMR.ofClosed hclR (hfR _ (by decide)) e3 hR2, hk2.trans (callW_keepW e3)⟩, by
        obtain ⟨s', rfl, -, -, hmem⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩) (flushCaches_spec p hP.flush n _) e3
        rw [hmem]; exact AFr.of_frame (flushMem_frame _) (by decide) (by decide) hA2⟩))) ?_
  intro u3 x3 m3 a3 hh3
  obtain ⟨⟨⟨hS3, hg3, hM3⟩, ⟨hR3, hk3⟩, hA3⟩, hrun3⟩ := hh3
  obtain ⟨hck3, -, hst3⟩ := ConRon.Bridge.Inductives.ReadOK.flush (μ := V)
    (⟨c1.ok.state, c1.ok.pins, hconsOK c1.ok.state.wf (ConRon.Bridge.TablesStored.of_envWF henv₁) c1.ok.ienv.toS a1 rfl⟩ :
      ConRon.Bridge.Inductives.ReadOK _ _ a1) hrun3
  have hC3 := StageC.of_parts hS3 hck3 hA3
    (fun k x e => by rw [hst3]; exact c1.ext.lss.ls.ns k x (hC.mem.dnN k x e))
  rw [ictlK3_some]
  have hg03 := (hg1.trans hg2).trans hg3
  -- `block_nested_bit` (the twin's `nested`, a pure function)
  refine Sim.mstep (K := ictlK4 p n bO bL q (UInt64.ofNat pw) (r2.headD 0)) rfl (fun _ _ => rfl) fun r4 m4 h4 => ?_
  have hks3 := hks.grow hkfm hg03
  rw [partsRdIW_grow hg03 (w := q + 8) (by rw [e 8 (by decide) (q + 8) rfl]; omega),
    partsRdIW_grow hg03 (w := q + 9) (by rw [e 9 (by decide) (q + 9) rfl]; omega)] at h4
  obtain ⟨s4, rfl, hs4, hr4⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (blockNestedBit_refines p hP.nf hP.ni hP.nm hP.nk hP.ng hP.nb n _ _ _ _ bs kinds hS3.2.2.2.1
      (DecB.get (decBS_mono _) (hbsD.grow (decBS_mono _) hg03)) (DecB.get (OMono.decPL hkfm _ _) hks3.1)) h4
  subst hs4
  have hnb : (r4.headD 0 != 0) = ConRon.Arena.blockNestedBit bs kinds := by
    rw [hr4]; cases ConRon.Arena.blockNestedBit bs kinds <;> rfl
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
  -- through `check_block_tail_rec`
  rw [ictlK4_some]
  refine Sim.post (K := ictlK7) rfl (fun _ _ => rfl) ?_ (fun r x m' a' h => h)
  cases n with
  | zero => rw [callW_zero]; exact Sim.of_none
  | succ k =>
  refine Sim.of_model (mo' := ictrW p k m3 bO bL q (UInt64.ofNat pw) (r2.headD 0) (r4.headD 0))
    (fun r m' e => ?_) ?_
  · obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
      (ictr_spec p hP.tailrec k _ bO bL q (UInt64.ofNat pw) (r2.headD 0) (r4.headD 0)) e
    exact hW
  unfold ictrW
  have hrec : Sim (callW p k "check_block_rec" [r2.headD 0, UInt64.ofNat pw, r4.headD 0,
        rdW (m3.arr64 IW) (q + 12), rdW (m3.arr64 IW) (q + 13), rdW (m3.arr64 IW) (q + 17),
        rdW (m3.arr64 IW) (q + 18), rdW (m3.arr64 IW) (q + 14), rdW (m3.arr64 IW) (q + 15),
        rdW (m3.arr64 IW) (q + 16), bO, bL, rdW (m3.arr64 IW) (q + 1), rdW (m3.arr64 IW) (q + 2)] m3)
      (ConRon.Arena.checkBlockRec V (ConRon.Arena.consBlockCtors bs.nP ctorsAs fe) ⟨bs⟩ (ConRon.Arena.blockNestedBit bs kinds) params tbl rd
        cls block cvTas) a3
      (fun r x m' a' => ((StageR dn (r.headD 0) x.1 m' a' ∧ IWGrow m3 m' ∧ decRRS m' r.tail x.2 ∧ AbsOK m' ∧
        RcMR m') ∧ HbMemo m') ∧ (ConRon.Arena.checkBlockRec V (ConRon.Arena.consBlockCtors bs.nP ctorsAs fe) ⟨bs⟩
          (ConRon.Arena.blockNestedBit bs kinds) params tbl rd cls block cvTas).run a3 = .ok (x, a')) := by
    have hx3 : Ext a.store a3.store := by rw [hst3]; exact c1.ext
    have hnP : qP.p.nP = bs.nP := by rw [hpPeq]; exact hnPP.symm
    rw [hnP] at henv₂
    rw [hpPeq] at hMs
    have d1 := ConRon.Bridge.Inductives.dShape_ext hx3 _ _ hshP
    have d2 := ConRon.Bridge.denoteEList_ext hx3 _ _ hpaP
    have d3 := ConRon.Bridge.Inductives.dCtorNf_ext.list hx3 _ _ htbP
    have d4 := ConRon.Bridge.Inductives.dClassRead_ext hx3 _ _ hrdP
    have d5 := ConRon.Bridge.Inductives.dMajor_ext.list hx3 _ _ hclP
    have d6 : cvTas.mapM (Frontend.denoteCV a3.store) = some qP.cvTas :=
      ConRon.Bridge.Inductives.DExt.list (d := Frontend.denoteCV)
        (fun hx _ _ h => ConRon.Bridge.denoteCV_ext h hx) hx3 _ _ hcvP
    have d7 := ConRon.Bridge.denoteCIList_mono hx3 _ _ hbP
    refine Sim.withRunC <| Sim.withFr (Sim.callW_posB (N := k) (fun j hj => installSimCall
      (checkBlockRec_refinesC hkp henv₂ hV hApd hCrk hIlpf hP.crec hP.grc hclR (fun f hf => hfR f (by
          simp only [grcMemoCallees, List.mem_cons, List.not_mem_nil, or_false] at hf
          rcases hf with rfl | rfl <;> decide)) j (by omega)
        ⟨m3, Locals.init []⟩ a3 dn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bs
        params tbl rd cls cvTas block hC3 hpre hrb3 hlp3 hR3 hA3
        (fun f hf => hkeep f (List.mem_append_right _ hf)) hcons.coh
        (by obtain ⟨e, h, rfl⟩ := hcons.denote; rw [hst3]; exact h) d1 d2 d3 d4 d5 d6 d7 hMs hTw (fun f hf => hfRc f (List.mem_append_left _ hf))) (fun r s' h => by
          obtain ⟨-, hok, hC', hg, hd, hA', hR', -⟩ := h; rw [hnb] at hok hC' hd
          exact ⟨hok, hC'.stage, hg, hd, hA', hR'⟩)) k (Nat.le_refl _))
      (fun r m' e5 => HbMemo.ofClosed hcl (hfs _ (by decide)) e5 hM3)
  refine Sim.bindK (K := ictrK5 p k q (UInt64.ofNat pw) (r2.headD 0)) rfl (fun _ _ => rfl)
    hrec ?_
  rintro r5 ⟨fe2b, outs⟩ m5 a5 ⟨⟨⟨hS5, hg5, hd5, hA5, hR5⟩, hM5⟩, hrun5⟩
  dsimp only
  rw [ictrK5_some, hS2.1.env.vis]
  -- con-ron's recursor stage on the twin's run (the recursors' readings, their freshness)
  have hx3 : Ext a.store a3.store := by rw [hst3]; exact c1.ext
  have hnP : qP.p.nP = bs.nP := by rw [hpPeq]; exact hnPP.symm
  rw [hnP] at henv₂
  rw [hpPeq] at hMs
  have hden₂ : ConRon.Bridge.denoteFEnv a3.store (ConRon.Arena.consBlockCtors bs.nP ctorsAs fe) =
      some (ConLeche.consBlockCtors bs.nP qP.ctorsAs env₁) := by
    obtain ⟨e, h, rfl⟩ := hcons.denote; rw [hst3]; exact h
  obtain ⟨c3, outP, ⟨hcoh₂b, hfe₂b, hout, hfresh⟩, -⟩ :=
    ConRon.Bridge.Inductives.recStage (μ := V) rfl (ConRon.Bridge.CoreSpec.of_core rfl) _ _ ⟨bs⟩ ⟨shP⟩
      _ params qP.params tbl qP.tbl.toList rd qP.rd cls qP.cls cvTas qP.cvTas block blockP henv₂ hcons.coh hTw
      hMs a3 a5 _ hck3
      ⟨hden₂, by simp only [ConRon.Bridge.Inductives.dParts, ConRon.Bridge.Inductives.dShape_ext hx3 _ _ hshP]; rfl,
        ConRon.Bridge.denoteEList_ext hx3 _ _ hpaP, ConRon.Bridge.Inductives.dCtorNf_ext.list hx3 _ _ htbP,
        ConRon.Bridge.Inductives.dClassRead_ext hx3 _ _ hrdP, ConRon.Bridge.Inductives.dMajor_ext.list hx3 _ _ hclP,
        ConRon.Bridge.Inductives.DExt.list (d := Frontend.denoteCV)
          (fun hx _ _ h => ConRon.Bridge.denoteCV_ext h hx) hx3 _ _ hcvP,
        ConRon.Bridge.denoteCIList_mono hx3 _ _ hbP⟩ hrun5
  have x35 := c3.ext
  -- `cons_block_recs_tf`
  refine Sim.bindK (K := ictrK6 p k q (UInt64.ofNat pw))
    rfl (fun _ _ => rfl)
    (Sim.withRunC <| Sim.withFr (F := RcMR) (hRecs k dn (r5.headD 0) (r2.headD 0) (UInt64.ofNat pw) fe2b m5 a5 bs r5.tail outs hS5
      ((hbsD.grow (decBS_mono _) hg03).grow (decBS_mono _) hg5) hd5 hM5 hA5)
      (fun _ _ e6 => RcMR.ofClosed hclR (hfRc _ (by simp)) e6 hR5)) ?_
  rintro r6 fe3 m6 a6 ⟨⟨⟨hS6, hg6, hM6, hA6⟩, hR6⟩, hrun6⟩
  rw [ictrK6_some]
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
  obtain ⟨c4, -⟩ := ConRon.Bridge.Inductives.consBlockRecsTF_spec (μ := V)
    (ConRon.Arena.consBlockCtors bs.nP ctorsAs fe).visibleBelow bs shP outs outP 0
    fe2b _ a5 a6 fe3 c3.ok (ConRon.Bridge.Inductives.RC.IFEnvOK.of_find? c3.ok.ienv hview hraw₂b)
    (Nat.le_of_eq hvis.symm) hcoh₂b hden₂b (ConRon.Bridge.Inductives.dShape_ext x05 _ _ hshP) hout hfresh
    (by rw [hS2.1.env.vis]; exact hrun6)
  have x06 : Ext a.store a6.store := x05.trans c4.ext
  -- `check_block_tables`
  have hg06 := (hg03.trans hg5).trans hg6
  have r : ∀ k, k < 19 → ∀ w : Word, w = q + UInt64.ofNat k → rdW (m6.arr64 IW) w = rdW (m.arr64 IW) w :=
    fun k hk w hw => partsRdIW_grow hg06 (by rw [e k hk w hw]; omega)
  rw [partsRdIW_grow hg06 (w := UInt64.ofNat pw) (by rw [hpw']; omega),
    partsRdIW_grow hg06 (w := UInt64.ofNat pw + 1) (by rw [UInt64.toNat_add, hpw']; simp; omega),
    r 4 (by decide) (q + 4) rfl, r 5 (by decide) (q + 5) rfl, r 6 (by decide) (q + 6) rfl,
    r 7 (by decide) (q + 7) rfl]
  refine Sim.post (K := ictlK7) rfl (fun _ _ => rfl)
    (Q := fun r x m' a' => StageR dn (r.headD 0) x m' a' ∧ IWGrow m6 m' ∧ HbMemo m' ∧ AbsOK m' ∧ RcMR m')
    (fun r m' e7 => by
      obtain ⟨s7, rfl, -, hW7⟩ := triple_of_callW (s₀ := ⟨m6, Locals.init []⟩)
        (ctb_spec p hP.tabs.tabs k _ _ _ _ _ _ _ _ _) e7
      obtain ⟨x, a', h1, h2, h3, h4⟩ := ctbW_simR hP.tabs hApd dn (UInt64.ofNat pw) bs k m6 a6 (r6.headD 0) fe3 _ _ _ _ _
        _ bs.members ctorsAs sss
        hS6 ((hbsD.grow (decBS_mono _) hg06)) (partsHsrc_grow hg06 hq9 hsrc) (hmss.grow decMS_mono hg06)
        (hcas.grow decCNS_mono hg06) (hsss'.grow decISS_mono hg06) hM6 hA6
        (fun f hf => hkeep f (by simp_all [tablesKeepCallees, tailKeepCalleesC, grcKeepCalleesC]))
        c4.ok.state c4.ok.pins ⟨shP, ConRon.Bridge.Inductives.dShape_ext x06 _ _ hshP⟩
        ⟨_, ConRon.Bridge.Inductives.dMember_ext.list x06 _ _ hmsP⟩
        ⟨_, ConRon.Bridge.Inductives.dCtors_ext.list x06 _ _ hcaP⟩
        ⟨_, ConRon.Bridge.Inductives.DExt.list (d := ConRon.Bridge.Inductives.denoteLLists)
          (fun hx x y h => ConRon.Bridge.Inductives.BI.denoteLLists_ext hx x y h) x06 _ _ hssP⟩ r s7.mem hW7
      exact ⟨x, a', h1, h2, h3, h4.1, h4.2.1, RcMR.ofClosedHb hclH hfH e7 hR6 h4.1⟩)
    (fun r x m7 a7 h => ⟨h.1, hg06.trans h.2.1, h.2.2⟩)

include hkp henv₁ hV hOpf hLC hLT hApd hCrk hIlpf in
/-- **`check_block_tail` refines `checkBlockTail` under `StageC`** (`checkBlockTail_refines`'s;
twin side con-ron's `checkBlockTail_of`): from `StageC` at the formers' index and the pass record's
denotation; the post is `StageR` (no core call follows the tables). -/
@[refines ConRon.Arena.checkBlockTail]
theorem checkBlockTail_refinesC (hP : TailProg p) (L : CbrLook p) {fs : List FnName}
    (hfs : ∀ f ∈ tailCallees, f ∈ fs) (hcl : closedA p hbFreeA hbFreeC fs = true) (n : Nat)
    (hn : n ≤ 2 ^ 62) {fsR : List FnName} (hclR : closedA p rcFreeA rcFreeC fsR = true)
    (hfR : ∀ f ∈ tailRcCallees, f ∈ fsR) (s₀ : St) (a₀ : AState) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {bO bL q : Word} {bp : BlockPass} {block : List IConstantInfo}
    (hC : StageC dn vis fe env₁ s₀.mem a₀) (hq : BPassR vis fe s₀.mem q bp)
    (hblk : DecB (fun m => decEBlk dn m bO.toNat bL.toNat) s₀.mem block) (hM : HbMemo s₀.mem)
    (hA : AbsOK s₀.mem) (hk : ∀ f ∈ tailKeepCalleesC, AbsKeep p f)
    (hR : RcMR s₀.mem) (hrb : RecsB s₀.mem (rdW (s₀.mem.arr64 IW) (q + 3)))
    (hlp : ClassesLp s₀.mem (rdW (s₀.mem.arr64 IW) (q + 15)) (rdW (s₀.mem.arr64 IW) (q + 16)))
    (hcoh : ConRon.Bridge.IFEnvCoh fe) (hden : ConRon.Bridge.denoteFEnv a₀.store fe = some env₁)
    {qP : ConLeche.BlockPass ConLeche.Env}
    (hqP : ConRon.Bridge.Inductives.dPass a₀.store env₁ bp = some qP)
    {blockP : List ConLeche.ConstantInfo} (hbP : Frontend.denoteCIList a₀.store block = some blockP)
    (hTw : ∀ cv ∈ qP.cvTas, ConLeche.Expr.WScoped 0 cv.type)
    (henv₂ : ConLeche.EnvWF (ConLeche.consBlockCtors qP.p.nP qP.ctorsAs env₁))
    (hMs : ∀ M ∈ qP.cls, ConLeche.Cached.ClassMajScoped qP.p.nP M)
    (hfRc : ∀ f ∈ grcRcCallees ++ ["cons_block_recs_tf"], f ∈ fsR) {fsH : List FnName}
    (hclH : closedA p rcHbFreeA rcHbFreeC fsH = true) (hfH : "check_block_tables" ∈ fsH) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check_block_tail" [bO, bL, q]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.checkBlockTail V block bp) a₀ ∧
      StageR dn (r.headD 0) (AM.res (ConRon.Arena.checkBlockTail V block bp) a₀) s'.mem
        (AM.st (ConRon.Arena.checkBlockTail V block bp) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ HbMemo s'.mem ∧ AbsOK s'.mem ∧ RcMR s'.mem; ⊤⦄ := by
  refine triple_post (ictl_spec p hP.tail n s₀ bO bL q) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hg, hM', hA', hR'⟩ :=
    ictlW_simC hkp henv₁ hV hOpf hLC hLT hApd hCrk hIlpf hP (consRecsTFSim_of L hcl (hfs _ (by decide))) hfs hcl n hclR hfR hn hC
      hq hblk hM hA hk hR hrb hlp hcoh hden hqP hbP hTw henv₂ hMs hfRc hclH hfH r s'.mem hm
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hres, hst]; exact hS', hg, hM', hA', hR'⟩

end sims

end L.Ind
