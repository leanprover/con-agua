import ConAgua.Arena.IndRealSctC
import ConAgua.Arena.IndInstallSpec.SpgWZero
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.RecCheckSpec.DecHLTruncMBound
import ConAgua.Arena.IndInstallSpec.ConsBlockCtors
import ConAgua.Arena.IndInstallSpec.InstallRec2PSl
import ConAgua.Arena.IndInstallSpec.NestCtx
import ConAgua.Arena.IndInstallSpec.PosFreeMfr

/-!
# `check_block_tables`: one model and one refinement for both outcomes

`ctoE` (`check_block_tables_one`) and `ctbE` (`check_block_tables`), `l_model … unified`:
`struct_proj_guards` and `block_shape_lps` (outside the verdict closure) through their runs
(`callW`), `check_struct_proj_table` through its run (`callE`; its error half the hypothesis
`CheckStructProjTableRE`), `ctbE` calls `ctoE`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

l_model ctoE_spec (p : Prog) (hP : TabsProg p)
  fns [hP.one ↦ ctoE]
  specs [callW_spec p n "struct_proj_guards", callW_spec p n "block_shape_lps"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model ctbE_spec (p : Prog) (hP : TabsProg p)
  fns [hP.tabs ↦ ctbE]
  specs [ctoE_spec p hP n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`check_struct_proj_table`'s error claim in the `StageR` shape** (under the twin's `StateOK`,
as `check_block_tables` runs it; `CheckStructProjTableE` is the `StageC` shape of
`checkStructProjTable_refinesC`): what the tables' error arms assume. -/
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

/-- What a table install leaves: the stage relation at the returned view, the growth, the memo, the
absence of stale records, the twin's step. -/
structure TabPost (dn : NIdx → Option ConLeche.Name) (m : Mem) (a : AState) (v : Word × Mem) (x : IFEnv)
    (a' : AState) : Prop where
  stage : StageR dn v.1 x v.2 a'
  grow : IWGrow m v.2
  memo : HbMemo v.2
  abs : AbsOK v.2
  step : ConRon.Bridge.Inductives.PStep a a'

/-- **`check_block_tables_one` refines one member's install**, both outcomes (the table through the
real `all_level_params_defined`: `tblW_okR`; its errors by `CheckStructProjTableRE`), from the twin's
`StateOK`, `PinsOK` and the shape's, the member's, the constructor's and its sorts' readings
(con-ron's `structProjGuards_spec`). -/
theorem cto_ref {p : Prog} (hP : TabsProg p) (hp : ApdF p) (n : Nat) (hn : n ≤ 2 ^ 62)
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
    {sortsP : List ConLeche.Level} (hsP : denoteLList a.store.ls sorts = some sortsP) :
    RefE (CheckStructProjTableRE p) (ctoE p n m pp ms co so vis) (tabOne fe bs msh cA nF sorts) a
      (fun v x a' => TabPost dn m a v x a') := by
  cases n with
  | zero => rw [ctoE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n =>
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  -- the constructor `[cv, nF]`
  obtain ⟨pc, y, ys, hy, hw0, hpcb, hdc, -⟩ := partsPSl_cons hcs (by decide)
  simp only [List.cons.injEq] at hy
  obtain ⟨rfl, -⟩ := hy
  obtain ⟨⟨cvp, hcvp, hcv⟩, hnF⟩ := decCN_some (show decCN (truncM m) pc = some (cA, nF) from hdc)
  have hpc' : (UInt64.ofNat pc : Word).toNat = pc := UInt64.toNat_ofNat_of_lt' hpcb
  have hlt1 := partsIwLt hnF
  obtain ⟨hw1, hcvb, -⟩ := partsIwRd hcvp hpc'
  obtain ⟨hw2, hnFb, -⟩ := partsIwRd hnF (w := UInt64.ofNat pc + 1)
    (by rw [UInt64.toNat_add, hpc']; simp; omega)
  -- the sorts `[off, len]`
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
  -- the shape's words
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hq hsrc
  obtain ⟨hnpw, hnpb, hrs32, hrse⟩ := partsShapeWords (IWGrow.refl m) hq hq9
  -- the member's name
  have hmsT : decMS (truncM m) ms.toNat = some msh := hms
  obtain ⟨⟨cvm, hcvm, hcvT⟩, -, -⟩ := decMS_some hmsT
  obtain ⟨hw6, hcvmb, -⟩ := partsIwRd hcvm rfl
  -- the capacity abort
  by_cases hg0 : rdW (m.arr64 IW) (pp + 4) + rdW (m.arr64 IW) (rdW (m.arr64 IW) co + 1) + 1 ≤
      rdW (m.arr64 IW) (pp + 4)
  · rw [ctoE.abort1 p n m pp ms co so vis hg0]; exact RefE.of_cls0 rfl
  rw [ctoE.arm1 p n m pp ms co so vis hg0, hw0, hw1, hw2, hw3, hw4, hw5, hnpw]
  rw [hw0, hw2, hnpw] at hg0
  have hb := nPnF_bound hg0
  rw [UInt64.toNat_ofNat_of_lt' hnpb, UInt64.toNat_ofNat_of_lt' hnFb] at hb
  obtain ⟨w, hwT, hwl, hwd⟩ := sumTypeWord (q := UInt64.ofNat cvp)
    (by rw [UInt64.toNat_ofNat_of_lt' hcvb]; exact DecB.get (OMono.decCVp _) hcv) hS.2.2.2.2.1
  rw [hwT]
  unfold tabOne
  -- `struct_proj_guards` (outside the verdict closure)
  rcases h1 : callW p n "struct_proj_guards" [w, UInt64.ofNat bs.nP, UInt64.ofNat nF, UInt64.ofNat so',
      UInt64.ofNat sl'] m with _ | ⟨rg, m1⟩
  · rw [liftE_none, ctoE.k_struct_proj_guards.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, ctoE.k_struct_proj_guards.arm1]
  match n, hn, h1 with
  | 0, _, h1 => rw [callW_zero] at h1; cases h1
  | 1, _, h1 =>
    obtain ⟨s', -, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (spg_spec p hP.tbl.hv hP.hf hP.hput hP.hins hP.hgo hP.hbp hP.hst hP.hsg hP.tbl.ha hP.tbl.hc hP.tbl.hsc
        hP.hul hP.hgd hP.hmf hP.hmp hP.him hP.hcol hP.hrow hP.hpw hP.hcl hP.hspg 0 _ _ _ _ _ _) h1
    rw [spgW_zero] at hW; cases hW
  | j + 2, hn, h1 =>
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
  obtain ⟨guards, a1, -, ⟨⟨⟨hS1, hg1, hgd1, hgt1, hM1⟩, ha1⟩, hrun1⟩⟩ := hsim rg m1 h1
  obtain ⟨ps1, -⟩ := ConRon.Bridge.Inductives.structProjGuards_spec cA.type cAP.type bs.nP nF sorts sortsP
    a a1 guards hok hpins ⟨ConRon.Bridge.denoteCV_type hcAP, hsP⟩ hrun1
  refine RefE.bind_right hrun1 ?_
  -- `block_shape_lps` (outside the verdict closure)
  rcases h2 : callW p (j + 2) "block_shape_lps" [pp] m1 with _ | ⟨rl, m2⟩
  · rw [liftE_none, ctoE.k_block_shape_lps.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, ctoE.k_block_shape_lps.arm1]
  obtain ⟨s2, rfl, -, hW2, -⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (blockShapeLps_spec2 p hP.tbl.ha hP.erCopy hP.erToIw hP.lps (j + 2) _ pp) h2
  obtain ⟨hS2, hg2, hl2, hlb2⟩ := lpsW_ok' hW2 hS1 (hq.grow (decBS_mono _) hg1)
  have hM2 : HbMemo s2.mem := hM1.fr (lpsW_mfrT hW2)
  have hA2 : AbsOK s2.mem := lpsW_afr hW2 (ha1 hA)
  have hg12 := hg1.trans hg2
  -- `check_struct_proj_table`
  obtain ⟨hnpw2, -, hrs2, hrse2⟩ := partsShapeWords hg12 hq hq9
  have hms2 : rdW (s2.mem.arr64 IW) ms = UInt64.ofNat cvm := by
    rw [partsRdIW_grow hg12 (by have := partsIwLt hcvm; omega)]; exact hw6
  obtain ⟨hT32, hTn⟩ := partsCVName hg12 hcvT hcvmb
  obtain ⟨hC32, hCn⟩ := partsCVName hg12 hcv hcvb
  rw [hnpw2, hms2]
  have hlpsP := names_ext ps1.ext ⟨pP.lps, denoteNList_mapM (ConRon.Bridge.Inductives.BlockShape.lps_spec hsh)⟩
  have hTP : denoteN a1.store.ns (decI (rdW (s2.mem.arr64 EREC) (UInt64.ofNat cvm))) = some mP.cvT.name := by
    rw [hTn]
    exact ConRon.Bridge.denoteN_ext
      (ConRon.Bridge.denoteCV_name (ConRon.Bridge.Inductives.dMember_inv hmP).1) ps1.ext
  have hcty := ConRon.Bridge.denoteCV_type (ConRon.Bridge.denoteCV_ext hcAP ps1.ext)
  have hcvD : DecB (fun m => decCVp m (UInt64.ofNat cvp : Word).toNat) s2.mem cA := by
    rw [UInt64.toNat_ofNat_of_lt' hcvb]; exact DecB.grow (OMono.decCVp _) hg12 hcv
  have hgd2 : decHL s2.mem (rg.headD 0).toNat (rg.tail.headD 0).toNat = some guards := by
    rw [decHL_grow hg2 (Nat.le_of_eq hgt1)]; exact hgd1
  have hnp1 : (UInt64.ofNat bs.nP : Word).toNat + 1 < 2 ^ 64 := by
    rw [UInt64.toNat_ofNat_of_lt' hnpb]; omega
  cases h3 : callE p (j + 2) "check_struct_proj_table" [rdW (s2.mem.arr64 EREC) (UInt64.ofNat cvm),
      rdW (s2.mem.arr64 EREC) (UInt64.ofNat cvp), rl.headD 0, rl.tail.headD 0, UInt64.ofNat bs.nP,
      UInt64.ofNat nF, rdW (s2.mem.arr64 IW) (pp + 6), rg.headD 0, rg.tail.headD 0, UInt64.ofNat cvp, vis]
      s2.mem with
  | error e3 =>
    rw [ctoE.k_check_struct_proj_table.none]
    intro eTbl
    have h := eTbl hP.tbl hp (j + 2) (by omega) s2.mem a1
      (rdW (s2.mem.arr64 EREC) (UInt64.ofNat cvm)) (rdW (s2.mem.arr64 EREC) (UInt64.ofNat cvp))
      (rl.headD 0) (rl.tail.headD 0) (UInt64.ofNat bs.nP) (UInt64.ofNat nF) (rdW (s2.mem.arr64 IW) (pp + 6))
      (rg.headD 0) (rg.tail.headD 0) (UInt64.ofNat cvp) bs.lps guards cA hS2 hT32 hC32 hrs2 hnp1 hl2 hlb2
      hgd2 (by rw [hgt1]; exact hg2.1) hcvD hA2 ps1.ok hlpsP hTP hcty _ h3
    rw [hTn, hCn, hrse2, UInt64.toNat_ofNat_of_lt' hnpb, UInt64.toNat_ofNat_of_lt' hnFb] at h
    exact h
  | ok q3 =>
    obtain ⟨r3, m3⟩ := q3
    rw [ctoE.k_check_struct_proj_table.arm1]
    obtain ⟨s3, rfl, -, hW3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
      (tblW_spec p hP.tbl (realCall p) (realCall_spec p) j _ (rdW (s2.mem.arr64 EREC) (UInt64.ofNat cvm))
        (rdW (s2.mem.arr64 EREC) (UInt64.ofNat cvp)) (rl.headD 0) (rl.tail.headD 0) (UInt64.ofNat bs.nP)
        (UInt64.ofNat nF) (rdW (s2.mem.arr64 IW) (pp + 6)) (rg.headD 0) (rg.tail.headD 0)
        (UInt64.ofNat cvp) vis) (callW_of_callE h3)
    have h := tblW_okR (dn := dn) (vis := vis) (fe := fe) p hP.tbl hp j s2.mem a1
      (rdW (s2.mem.arr64 EREC) (UInt64.ofNat cvm)) (rdW (s2.mem.arr64 EREC) (UInt64.ofNat cvp))
      (rl.headD 0) (rl.tail.headD 0) (UInt64.ofNat bs.nP) (UInt64.ofNat nF) (rdW (s2.mem.arr64 IW) (pp + 6))
      (rg.headD 0) (rg.tail.headD 0) (UInt64.ofNat cvp) bs.lps guards cA hS2 hT32 hC32 hrs2 hnp1 hl2 hlb2
      hgd2 (by rw [hgt1]; exact hg2.1) hcvD hA2 ps1.ok hlpsP (TP := mP.cvT.name) hTP hcty
    rw [hTn, hCn, hrse2, UInt64.toNat_ofNat_of_lt' hnpb, UInt64.toNat_ofNat_of_lt' hnFb] at h
    obtain ⟨x, a3, hrun3, hS3, hg3, hf3, hA3, ps3⟩ := h r3 s3.mem hW3
    exact RefE.ret hrun3 ⟨hS3, hg12.trans hg3, hM2.fr hf3, hA3, ps1.trans ps3⟩

/-- **`check_block_tables` refines `checkBlockTables`**, both outcomes (each member's install by
`cto_ref`, a `PStep`, so the readings hold at the next), from the twin's `StateOK`, `PinsOK` and the
shape's, the members', the constructors' and their sorts' readings. -/
theorem ctb_ref {p : Prog} (hP : TabsProg p) (hp : ApdF p) (dn : NIdx → Option ConLeche.Name) (pp : Word)
    (bs : BlockShape) (n : Nat) (hn : n ≤ 2 ^ 62) :
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
    RefE (CheckStructProjTableRE p) (ctbE p n m pp mo ml co cl so sl vis)
      (ConRon.Arena.checkBlockTables bs mss css sss fe) a (fun v x a' => TabPost dn m a v x a') := by
  induction n with
  | zero => intros; rw [ctbE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a vis fe mo ml co cl so sl mss css sss hS hq hsrc hmss hcss hsss hM hA hkeep hok hpins
    ⟨pP, hsh⟩ ⟨msP, hmsP⟩ ⟨cssP, hcsP⟩ ⟨sssP, hssP⟩
  have hnil : RefE (CheckStructProjTableRE p) (.ok (vis, m)) (pure fe : AM IFEnv) a
      (fun v x a' => TabPost dn m a v x a') :=
    RefE.ret rfl ⟨hS, IWGrow.refl m, hM, hA, ConRon.Bridge.Inductives.PStep.refl hok⟩
  by_cases hml : ml = 0
  · subst hml
    rw [ctbE.arm1 p n m pp mo 0 co cl so sl vis rfl, cbt_nil bs mss css sss fe (.inl (partsPSl_nil hmss))]
    exact hnil
  by_cases hcl : cl = 0
  · subst hcl
    rw [ctbE.arm2 p n m pp mo ml co 0 so sl vis hml rfl,
      cbt_nil bs mss css sss fe (.inr (.inl (partsPSl_nil hcss)))]
    exact hnil
  by_cases hsl : sl = 0
  · subst hsl
    rw [ctbE.arm3 p n m pp mo ml co cl so 0 vis hml hcl rfl,
      cbt_nil bs mss css sss fe (.inr (.inr (partsPSl_nil hsss)))]
    exact hnil
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hq hsrc
  obtain ⟨msp, msh, rest, rfl, hwm, hmsb, hdm, hrest⟩ := partsPSl_cons hmss hml
  obtain ⟨csp, cs, css', rfl, hwc, hcsb, hdc, hcss'⟩ := partsPSl_cons hcss hcl
  obtain ⟨ssp, ss, sss', rfl, hws, hssb, hds, hsss'⟩ := partsPSl_cons hsss hsl
  obtain ⟨mP, msP', -, hmP, hrestP⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hmsP
  obtain ⟨csP, cssP', -, hcsy, hcssP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hcsP
  obtain ⟨ssP, sssP', -, hssy, hsssP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hssP
  have hmsp' : (UInt64.ofNat msp : Word).toNat = msp := UInt64.toNat_ofNat_of_lt' hmsb
  have hcsp' : (UInt64.ofNat csp : Word).toNat = csp := UInt64.toNat_ofNat_of_lt' hcsb
  have hssp' : (UInt64.ofNat ssp : Word).toNat = ssp := UInt64.toNat_ofNat_of_lt' hssb
  -- the member's constructors `[off, len]`
  obtain ⟨o1, l1, ho1, hl1, hd1, hb1⟩ := partsAt decCN_mono
    (show decAt (truncM m) (decPL (truncM m) (decCN (truncM m))) csp = some cs from hdc)
  have hlt1 := partsIwLt hl1
  obtain ⟨hwo1, -, -⟩ := partsIwRd ho1 hcsp'
  obtain ⟨hwl1, -, -⟩ := partsIwRd hl1 (w := UInt64.ofNat csp + 1)
    (by rw [UInt64.toNat_add, hcsp']; simp; omega)
  rw [ofNat_toNat_word] at hwo1 hwl1
  have hlen1 : cs.length = l1.toNat := decPL_length _ hd1
  -- the member's sorts `[off, len]`
  obtain ⟨o2, l2, ho2, hl2, hd2, hb2⟩ := partsAt decIS_mono
    (show decAt (truncM m) (fun o l => decPL (truncM m) (decIS (truncM m)) o l) ssp = some ss from hds)
  have hlt2 := partsIwLt hl2
  obtain ⟨hwo2, -, -⟩ := partsIwRd ho2 hssp'
  obtain ⟨hwl2, -, -⟩ := partsIwRd hl2 (w := UInt64.ofNat ssp + 1)
    (by rw [UInt64.toNat_add, hssp']; simp; omega)
  rw [ofNat_toNat_word] at hwo2 hwl2
  have hlen2 : ss.length = l2.toNat := decPL_length _ hd2
  -- the member's index count
  obtain ⟨-, hni, -⟩ := decMS_some (show decMS (truncM m) msp = some msh from hdm)
  have hlt3 := partsIwLt hni
  obtain ⟨hwn, hnib, -⟩ := partsIwRd hni (w := UInt64.ofNat msp + 1)
    (by rw [UInt64.toNat_add, hmsp']; simp; omega)
  have hni0 : (UInt64.ofNat msh.nIdx : Word) = 0 ↔ msh.nIdx = 0 := by
    constructor
    · intro e; have := congrArg UInt64.toNat e; rwa [UInt64.toNat_ofNat_of_lt' hnib] at this
    · intro e; rw [e]; rfl
  have hw1 : ∀ w : Word, w = 1 ↔ w.toNat = 1 := fun w =>
    ⟨fun e => by rw [e]; rfl, fun e => UInt64.toNat_inj.mp (by rw [e]; rfl)⟩
  by_cases hc : l1 = 1 ∧ l2 = 1 ∧ msh.nIdx = 0
  · obtain ⟨e1, e2, e3⟩ := hc
    subst e1 e2
    obtain ⟨⟨cA, nF⟩, rfl⟩ := List.length_eq_one_iff.mp (show cs.length = 1 by rw [hlen1]; rfl)
    obtain ⟨sorts, rfl⟩ := List.length_eq_one_iff.mp (show ss.length = 1 by rw [hlen2]; rfl)
    obtain ⟨cAP', -, -, hcA1, -⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hcsy
    obtain ⟨cAP, hcAP, -⟩ := Option.map_eq_some_iff.mp hcA1
    obtain ⟨sortsP, -, -, hsP, -⟩ := ConRon.Bridge.Inductives.BT.denoteLLists_cons_inv hssy
    rw [ctbE.arm4 p n m pp mo ml co cl so sl vis hml hcl hsl (by rw [hwc, hwl1]) (by rw [hws, hwl2])
      (by rw [hwm, hwn, (hni0).mpr e3]), cbt_one bs msh rest css' sss' fe cA nF sorts e3, hwm, hwc, hws,
      hwo1, hwo2]
    have h1 := cto_ref (fe := fe) hP hp n (by omega) hS hq hsrc (by rw [hmsp']; exact hdm)
      ⟨hd1, hb1.resolve_left (by decide)⟩ ⟨hd2, hb2.resolve_left (by decide)⟩ hM hA hkeep hok hpins
      hsh hmP hcAP hsP
    rcases hc1 : ctoE p n m pp (UInt64.ofNat msp) o1 o2 vis with e1 | ⟨vis2, m1⟩
    · rw [ctbE.k_check_block_tables_one.none]
      rw [hc1] at h1
      exact RefE.bind_left h1
    rw [hc1] at h1
    obtain ⟨fe₂, a1, hrun1, ⟨hS1, hg1, hM1, hA1, ps1⟩⟩ := h1
    rw [ctbE.k_check_block_tables_one.arm1, ctbE.j1.arm1]
    refine RefE.bind_right hrun1 (RefE.mono (ih (by omega) m1 a1 vis2 fe₂ (mo + 1) (ml - 1) (co + 1) (cl - 1)
        (so + 1) (sl - 1) rest css' sss' hS1 (hq.grow (decBS_mono _) hg1) (partsHsrc_grow hg1 hq9 hsrc)
        (hrest.grow decMS_mono hg1) (hcss'.grow decCNS_mono hg1) (hsss'.grow decISS_mono hg1) hM1 hA1 hkeep
        ps1.ok (hpins.mono ps1.ext ps1.pins) ⟨pP, ConRon.Bridge.Inductives.dShape_ext ps1.ext _ _ hsh⟩
        ⟨msP', ConRon.Bridge.Inductives.dMember_ext.list ps1.ext _ _ hrestP⟩
        ⟨cssP', ConRon.Bridge.Inductives.dCtors_ext.list ps1.ext _ _ hcssP'⟩
        ⟨sssP', ConRon.Bridge.Inductives.DExt.list
          (d := ConRon.Bridge.Inductives.denoteLLists)
          (fun hx x y h => ConRon.Bridge.Inductives.BI.denoteLLists_ext hx x y h) ps1.ext _ _ hsssP'⟩) ?_)
    exact fun v x a' h => ⟨h.stage, hg1.trans h.grow, h.memo, h.abs, ps1.trans h.step⟩
  · have hcw : ¬ (rdW (m.arr64 IW) (rdW (m.arr64 IW) co + 1) = 1 ∧ rdW (m.arr64 IW) (rdW (m.arr64 IW) so + 1) = 1 ∧
        rdW (m.arr64 IW) (rdW (m.arr64 IW) mo + 1) = 0) := by
      rw [hwc, hwl1, hws, hwl2, hwm, hwn, hni0]; exact hc
    have hskip : ctbE p (n + 1) m pp mo ml co cl so sl vis = ctbE.j1 p n pp mo ml co cl so sl vis m := by
      by_cases c1 : rdW (m.arr64 IW) (rdW (m.arr64 IW) co + 1) = 1
      · by_cases c2 : rdW (m.arr64 IW) (rdW (m.arr64 IW) so + 1) = 1
        · have c3 : rdW (m.arr64 IW) (rdW (m.arr64 IW) mo + 1) ≠ 0 := fun h => hcw ⟨c1, c2, h⟩
          exact ctbE.arm5 p n m pp mo ml co cl so sl vis hml hcl hsl c1 c2 c3
        · exact ctbE.arm6 p n m pp mo ml co cl so sl vis hml hcl hsl c1 c2
      · exact ctbE.arm7 p n m pp mo ml co cl so sl vis hml hcl hsl c1
    rw [hskip, ctbE.j1.arm1, cbt_skip bs msh rest cs css' ss sss' fe (by
        rw [hlen1, hlen2, ← hw1, ← hw1]; exact hc)]
    exact ih (by omega) m a vis fe (mo + 1) (ml - 1) (co + 1) (cl - 1) (so + 1) (sl - 1) rest css' sss'
      hS hq hsrc hrest hcss' hsss' hM hA hkeep hok hpins ⟨pP, hsh⟩ ⟨msP', hrestP⟩ ⟨cssP', hcssP'⟩
      ⟨sssP', hsssP'⟩

end L.Ind
