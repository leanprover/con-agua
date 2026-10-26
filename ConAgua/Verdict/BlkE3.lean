import ConAgua.Verdict.IndA4
import ConAgua.Verdict.IndBE
import ConAgua.Arena.IndRealSctC

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model ctoE_spec (p : Prog) (hf : p.lookup "check_block_tables_one" = some checkBlockTablesOne)
  fns [hf ↦ ctoE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] heartbeats 1000000 simp [rdW] errors

l_model ctbE_spec (p : Prog) (hf : p.lookup "check_block_tables" = some checkBlockTables)
  fns [hf ↦ ctbE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] heartbeats 1000000 simp [rdW] errors

theorem blkE3_nv : ∀ f ∈ ["struct_proj_guards", "block_shape_lps"], f ∈ _root_.L.Checker.nvFns := by
  decide +kernel

/-- **`check_struct_proj_table`'s error claim in the shape of `tblW_okR`** (under `StageR` and
the twin's `StateOK`, as `check_block_tables` runs it; `CheckStructProjTableE` is the `StageC`
shape of `checkStructProjTable_refinesC`). -/
def CheckStructProjTableRE (p : Prog) : Prop :=
  ∀ (_ : TblProg p) (_ : ApdF p) (F : Nat), F ≤ 2 ^ 62 → ∀ {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} (m : Mem) (a : AState) (T C lo ll nP nF rs go gl cvCaw : Word) (lps : List NIdx)
    (guards : List LIdx) (cvCa : IConstantVal),
    StageR dn vis fe m a → H T → H C → H rs → nP.toNat + 1 < 2 ^ 64 →
    decHL m lo.toNat ll.toNat = some lps → lo.toNat + ll.toNat ≤ iwTop m →
    decHL m go.toNat gl.toNat = some guards → go.toNat + gl.toNat ≤ iwTop m →
    DecB (fun m => decCVp m cvCaw.toNat) m cvCa → AbsOK m → ConRon.Bridge.StateOK a →
    (∃ ks, lps.mapM (denoteN a.store.lss.ls.ns) = some ks) →
    ∀ {TP : ConLeche.Name}, denoteN a.store.ns (decI T) = some TP →
    ∀ {ctyP : ConLeche.Expr}, denoteE a.store cvCa.type = some ctyP →
    ∀ e, callE p F "check_struct_proj_table" [T, C, lo, ll, nP, nF, rs, go, gl, cvCaw, vis] m = .error e →
      ErrClaim (checkStructProjTable (decI T) (decI C) lps nP.toNat nF.toNat (decI rs) guards cvCa fe) a e

/-- **`check_block_tables_one`'s error claim** (the model at fuel `n + 1`; `ctoW_simR`'s
hypotheses). -/
theorem ctoE_claim {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (eTbl : CheckStructProjTableRE p) (hP : TabsProg p) (hp : ApdF p) (n : Nat) (hn : n ≤ 2 ^ 62)
    {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {m : Mem} {a : AState} {pp ms co so : Word} {bs : BlockShape} {msh : MemberShape}
    {cA : IConstantVal} {nF : Nat} {sorts : List LIdx}
    (hS : StageR dn vis fe m a) (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    (hms : DecB (fun m => decMS m ms.toNat) m msh) (hcs : PSlR decCN [(cA, nF)] co 1 m)
    (hss : PSlR decIS [sorts] so 1 m) (hM : HbMemo m) (hA : AbsOK m)
    (hkeep : ∀ f ∈ tablesKeepCallees, AbsKeep p f)
    (hok : ConRon.Bridge.StateOK a) (hpins : ConRon.Bridge.PinsOK a)
    {pP : ConLeche.BlockShape} (hsh : ConRon.Bridge.Inductives.dShape a.store bs = some pP)
    {mP : ConLeche.MemberShape} (hmP : ConRon.Bridge.Inductives.dMember a.store msh = some mP)
    {cAP : ConLeche.ConstantVal} (hcAP : Frontend.denoteCV a.store cA = some cAP)
    {sortsP : List ConLeche.Level} (hsP : denoteLList a.store.ls sorts = some sortsP) (e : Err)
    (he : ctoE p (n + 1) m pp ms co so vis = .error e) :
    ErrClaim (tabOne fe bs msh cA nF sorts) a e := by
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨pc, y, ys, hy, hw0, hpcb, hdc, -⟩ := partsPSl_cons hcs (by decide)
  simp only [List.cons.injEq] at hy
  obtain ⟨rfl, -⟩ := hy
  obtain ⟨⟨cvp, hcvp, hcv⟩, hnF⟩ := decCN_some (show decCN (truncM m) pc = some (cA, nF) from hdc)
  have hpc' : (UInt64.ofNat pc : Word).toNat = pc := UInt64.toNat_ofNat_of_lt' hpcb
  have hlt1 := partsIwLt hnF
  obtain ⟨hw1, hcvb, -⟩ := partsIwRd hcvp hpc'
  obtain ⟨hw2, hnFb, -⟩ := partsIwRd hnF (w := UInt64.ofNat pc + 1)
    (by rw [UInt64.toNat_add, hpc']; simp; omega)
  obtain ⟨ps, z, zs, hz, hw3, hpsb, hds, -⟩ := partsPSl_cons hss (by decide)
  simp only [List.cons.injEq] at hz
  obtain ⟨rfl, -⟩ := hz
  have hps' : (UInt64.ofNat ps : Word).toNat = ps := UInt64.toNat_ofNat_of_lt' hpsb
  obtain ⟨so', sl', hso, hsl, hdd⟩ := decAt_some (show decIS (truncM m) ps = some sorts from hds)
  have hlt2 := partsIwLt hsl
  obtain ⟨hw4, hsob, -⟩ := partsIwRd hso hps'
  obtain ⟨hw5, hslb, -⟩ := partsIwRd hsl (w := UInt64.ofNat ps + 1)
    (by rw [UInt64.toNat_add, hps']; simp; omega)
  have hso' : (UInt64.ofNat so' : Word).toNat = so' := UInt64.toNat_ofNat_of_lt' hsob
  have hsl' : (UInt64.ofNat sl' : Word).toNat = sl' := UInt64.toNat_ofNat_of_lt' hslb
  have hsorts : decHL m so' sl' = some sorts ∧ (sl' = 0 ∨ so' + sl' ≤ iwTop m) := by
    by_cases h0 : sl' = 0
    · subst h0
      have : sorts = [] := by simpa [decHL, hslice?] using hdd.symm
      subst this; exact ⟨by simp [decHL, hslice?], .inl rfl⟩
    · have hb := decHL_truncM_bound hdd h0
      exact ⟨by rw [← decHL_truncM hb]; exact hdd, .inr hb⟩
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hq hsrc
  obtain ⟨hnpw, hnpb, hrs32, hrse⟩ := partsShapeWords (IWGrow.refl m) hq hq9
  have hmsT : decMS (truncM m) ms.toNat = some msh := hms
  obtain ⟨⟨cvm, hcvm, hcvT⟩, -, -⟩ := decMS_some hmsT
  obtain ⟨hw6, hcvmb, -⟩ := partsIwRd hcvm rfl
  by_cases hg0 : rdW (m.arr64 IW) (pp + 4) + rdW (m.arr64 IW) (rdW (m.arr64 IW) co + 1) + 1 ≤
      rdW (m.arr64 IW) (pp + 4)
  · rw [ctoE.abort1 p n m pp ms co so vis hg0] at he; cases he; exact absurd rfl hk0
  rw [ctoE.arm1 p n m pp ms co so vis hg0, hw0, hw1, hw2, hw3, hw4, hw5, hnpw] at he
  rw [hw0, hw2, hnpw] at hg0
  have hb := nPnF_bound hg0
  rw [UInt64.toNat_ofNat_of_lt' hnpb, UInt64.toNat_ofNat_of_lt' hnFb] at hb
  obtain ⟨w, hwT, hwl, hwd⟩ := sumTypeWord (q := UInt64.ofNat cvp)
    (by rw [UInt64.toNat_ofNat_of_lt' hcvb]; exact DecB.get (OMono.decCVp _) hcv) hS.2.2.2.2.1
  rw [hwT] at he
  unfold tabOne
  cases h1 : callE p n "struct_proj_guards" [w, UInt64.ofNat bs.nP, UInt64.ofNat nF, UInt64.ofNat so',
      UInt64.ofNat sl'] m with
  | error e1 =>
    rw [h1, ctoE.k_struct_proj_guards.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (blkE3_nv _ (by simp)) h1
  | ok q1 =>
  obtain ⟨rg, m1⟩ := q1
  rw [h1, ctoE.k_struct_proj_guards.arm1] at he
  match n, hn, h1, he with
  | 0, _, h1, _ => have := callW_of_callE h1; rw [callW_zero] at this; cases this
  | 1, _, h1, _ =>
    obtain ⟨s', -, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (spg_spec p hP.tbl.hv hP.hf hP.hput hP.hins hP.hgo hP.hbp hP.hst hP.hsg hP.tbl.ha hP.tbl.hc hP.tbl.hsc
        hP.hul hP.hgd hP.hmf hP.hmp hP.him hP.hcol hP.hrow hP.hpw hP.hcl hP.hspg 0 _ _ _ _ _ _)
      (callW_of_callE h1)
    rw [spgW_zero] at hW; cases hW
  | j + 2, hn, h1, he =>
  have hsim := sctSim_withRun (by
      have h := tabSimSpg hP (j + 1) w (UInt64.ofNat bs.nP) (UInt64.ofNat nF) (UInt64.ofNat so')
        (UInt64.ofNat sl') sorts hwl
        (by rw [UInt64.toNat_ofNat_of_lt' hnpb, UInt64.toNat_ofNat_of_lt' hnFb]; exact hb) hS hM
        (by rw [hso', hsl']; exact hsorts.1)
        (by rcases hsorts.2 with h | h
            · left; rw [h]; rfl
            · right; rw [hso', hsl']; exact h)
      rw [hwd, UInt64.toNat_ofNat_of_lt' hnpb, UInt64.toNat_ofNat_of_lt' hnFb] at h
      exact (Sim.withFr (F := fun m1 => AFr m m1) h
        fun _ _ e => hkeep _ (by simp [tablesKeepCallees]) _ _ _ _ _ e))
  obtain ⟨guards, a1, -, ⟨⟨⟨hS1, hg1, hgd1, hgt1, hM1⟩, ha1⟩, hrun1⟩⟩ := hsim rg m1 (callW_of_callE h1)
  obtain ⟨ps1, -⟩ := ConRon.Bridge.Inductives.structProjGuards_spec cA.type cAP.type bs.nP nF sorts sortsP
    a a1 guards hok hpins ⟨ConRon.Bridge.denoteCV_type hcAP, hsP⟩ hrun1
  refine ErrClaim.bind_right hrun1 ?_
  cases h2 : callE p (j + 2) "block_shape_lps" [pp] m1 with
  | error e2 =>
    rw [h2, ctoE.k_block_shape_lps.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (blkE3_nv _ (by simp)) h2
  | ok q2 =>
  obtain ⟨rl, m2⟩ := q2
  rw [h2, ctoE.k_block_shape_lps.arm1] at he
  obtain ⟨s2, hs2, -, hW2, -⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (blockShapeLps_spec2 p hP.tbl.ha hP.erCopy hP.erToIw hP.lps (j + 2) _ pp) (callW_of_callE h2)
  subst hs2
  obtain ⟨hS2, hg2, hl2, hlb2⟩ := lpsW_ok' hW2 hS1 (hq.grow (decBS_mono _) hg1)
  have hA2 : AbsOK s2.mem := lpsW_afr hW2 (ha1 hA)
  have hg12 := hg1.trans hg2
  obtain ⟨hnpw2, -, hrs2, hrse2⟩ := partsShapeWords hg12 hq hq9
  have hms2 : rdW (s2.mem.arr64 IW) ms = UInt64.ofNat cvm := by
    rw [partsRdIW_grow hg12 (by have := partsIwLt hcvm; omega)]; exact hw6
  obtain ⟨hT32, hTn⟩ := partsCVName hg12 hcvT hcvmb
  obtain ⟨hC32, hCn⟩ := partsCVName hg12 hcv hcvb
  rw [hnpw2, hms2] at he
  cases h3 : callE p (j + 2) "check_struct_proj_table" [rdW (s2.mem.arr64 EREC) (UInt64.ofNat cvm),
      rdW (s2.mem.arr64 EREC) (UInt64.ofNat cvp), rl.headD 0, rl.tail.headD 0, UInt64.ofNat bs.nP,
      UInt64.ofNat nF, rdW (s2.mem.arr64 IW) (pp + 6), rg.headD 0, rg.tail.headD 0, UInt64.ofNat cvp, vis]
      s2.mem with
  | error e3 =>
    rw [h3, ctoE.k_check_struct_proj_table.none] at he; cases he
    have h := eTbl hP.tbl hp (j + 2) hn s2.mem a1
      (rdW (s2.mem.arr64 EREC) (UInt64.ofNat cvm)) (rdW (s2.mem.arr64 EREC) (UInt64.ofNat cvp))
      (rl.headD 0) (rl.tail.headD 0) (UInt64.ofNat bs.nP) (UInt64.ofNat nF) (rdW (s2.mem.arr64 IW) (pp + 6))
      (rg.headD 0) (rg.tail.headD 0)
      (UInt64.ofNat cvp) bs.lps guards cA hS2 hT32 hC32 hrs2
      (by rw [UInt64.toNat_ofNat_of_lt' hnpb]; omega) hl2 hlb2
      (by rw [decHL_grow hg2 (Nat.le_of_eq hgt1)]; exact hgd1) (by rw [hgt1]; exact hg2.1)
      (by rw [UInt64.toNat_ofNat_of_lt' hcvb]; exact DecB.grow (OMono.decCVp _) hg12 hcv) hA2 ps1.ok
      (names_ext ps1.ext ⟨pP.lps, denoteNList_mapM (ConRon.Bridge.Inductives.BlockShape.lps_spec hsh)⟩)
      (TP := mP.cvT.name) (by
        rw [hTn]
        exact ConRon.Bridge.denoteN_ext
          (ConRon.Bridge.denoteCV_name (ConRon.Bridge.Inductives.dMember_inv hmP).1) ps1.ext)
      (ConRon.Bridge.denoteCV_type (ConRon.Bridge.denoteCV_ext hcAP ps1.ext)) _ h3
    rw [hTn, hCn, hrse2, UInt64.toNat_ofNat_of_lt' hnpb, UInt64.toNat_ofNat_of_lt' hnFb] at h
    exact h
  | ok q3 =>
    obtain ⟨r3, m3⟩ := q3
    rw [h3, ctoE.k_check_struct_proj_table.arm1] at he; cases he

end L.Ind
