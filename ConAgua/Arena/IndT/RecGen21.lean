import ConAgua.Arena.IndT.RecGen19
import ConAgua.Arena.IndInstallSpec.PosFreeMfr
import ConAgua.Census.Attr

/-!
# `checkBlockClasses` under `StageC` (lane `indstaget`)

`check_block_classes`' model (over the program's own calls); twin side con-ron's
`checkBlockClasses_spec`'s proof: `classRead` (`classRead_spec`), the classes (L only), the keys
(`classKeysOf_spec`), the majors (`clmW_simC`, `classMajors_spec`), one class per member (L only).
The walk memos across `class_read` by its real `open_pis_at_fvars_f` (`classRead_refinesA`), across
the other calls by the program facts `AbsKeep`.
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
variable {p : Prog} (hq : KnotStageProg p) (hIlpf : IlpfF p) (hLC : LvlCacheProg p) (henv : ConLeche.EnvWF env)

include hq hIlpf hLC henv in
/-- **`check_block_classes` under `StageC`** (`cbcW_sim`'s). -/
theorem cbcW_simC (hP : CbcProg p) {fs : List FnName}
    (hcl : closedA p posFreeA posFreeC fs = true) (hfr : "class_read" ∈ fs)
    (hfc : "class_read_classes" ∈ fs) (n : Nat)
    (hn : n ≤ 2 ^ 62) (m : Mem) (a : AState)
    (pp po pl co cl : Word) (bs : BlockShape) (css : List (List (IConstantVal × Nat)))
    (pfvs : List EIdx) (hC : StageC dn vis fe env m a) (hb : BSOK m pp.toNat bs)
    (hsrc : ShapeSrc m pp)
    (hrecs : RecsDec m (rdW (m.arr64 IW) (pp + 2)) (rdW (m.arr64 IW) (pp + 3)) bs.recs)
    (hcss : PSlR decCNS css co cl m) (hpf : DecB (fun m => decHL m po.toNat pl.toNat) m pfvs)
    (hpfb : po.toNat + pl.toNat ≤ iwTop m) (hPm : PosMR m) (hA : AbsOK m)
    (hOpf : OpfF p) (hk2 : AbsKeep p "class_read_classes")
    (hk3 : AbsKeep p "check_block_classes_keys")
    {pP : ConLeche.BlockShape} {pfvsP : List ConLeche.Expr}
    {cssP : List (List (ConLeche.ConstantVal × Nat))}
    (hpl : pfvsP.length = pP.nP) (hpw : ∀ x ∈ pfvsP, ConLeche.Expr.WScoped pP.nP x)
    (hshP : ConRon.Bridge.Inductives.dShape a.store bs = some pP)
    (hpfP : Frontend.denoteEList a.store pfvs = some pfvsP)
    (hcssP : css.mapM (ConRon.Bridge.Inductives.dCtors a.store) = some cssP) :
    Sim (cbcW p (n + 1) m vis pp po pl co cl) (ConRon.Arena.checkBlockClasses V fe bs pfvs css) a
      (fun r x m' a' => StageC dn vis fe env m' a' ∧ IWGrow m m' ∧
        DecB (fun m => decCR m (r.headD 0).toNat) m' x.1 ∧
        PSlR decTM x.2 (r.tail.headD 0) (r.tail.tail.headD 0) m' ∧ PosMR m' ∧ AbsOK m' ∧
        ConRon.Bridge.CoreStep V env fe a a') := by
  intro r m' h
  have hS := hC.stage
  obtain ⟨-, hrecsP, hnPP, -, -, -, -⟩ := ConRon.Bridge.Inductives.dShape_inv hshP
  have hbsD : DecB (fun m => decBS m pp.toNat) m bs := hb.1
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hbsD hsrc
  obtain ⟨hnp, hnpb, -, -⟩ := partsShapeWords (IWGrow.refl m) hbsD hq9
  have hnpT : (UInt64.ofNat bs.nP : Word).toNat = bs.nP := UInt64.toNat_ofNat_of_lt' hnpb
  rw [cbcW.arm1] at h
  -- `class_read`
  obtain ⟨⟨r1, m1⟩, c1, h⟩ := of_K h rfl
  obtain ⟨s1, hs1, -, hok1, ⟨hS1, hg1, hd1⟩, hA1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (classRead_refinesA p hP.read hOpf n _ a dn vis fe pp _ _ _ bs bs.recs hS hA hb hrecs) c1
  simp only at hs1 hS1 hg1 hd1 hA1
  subst hs1
  have hP1 := PosMR.ofClosed hcl hfr c1 hPm
  rw [hnp, hnpT] at hok1 hS1 hd1
  have hrun1 := AM.run_of_ok _ a hok1
  obtain ⟨p1, ho1⟩ := ConRon.Bridge.Inductives.classRead_spec bs pP env fe bs.nP bs.recs pP.recs a _ _
    hC.check.state ⟨hshP, hC.check.ienv.toS, hrecsP⟩ hrun1
  generalize hx1 : AM.res (ConRon.Arena.classRead bs fe bs.nP bs.recs) a = x1 at hrun1 hd1 ho1
  generalize ha1 : AM.st (ConRon.Arena.classRead bs fe bs.nP bs.recs) a = a1 at hrun1 hS1 p1 ho1
  have hC1 : StageC dn vis fe env s1.mem a1 := hC.of_pstep hS1 hA1 p1
  have c1' := p1.toCore hC.check
  rcases x1 with _ | rd
  · simp only [decRead] at hd1; rw [cbcW.k_class_read.abort1 p n vis pp po pl co cl r1 s1.mem hd1] at h; cases h
  obtain ⟨rdP, -, hrd⟩ := ho1
  have hsl : rd.slots.mapM (ConRon.Bridge.Inductives.dSlot a1.store) = some rdP.slots := by
    simp only [ConRon.Bridge.Inductives.dClassRead, Option.map_eq_some_iff] at hrd
    obtain ⟨q, hq, rfl⟩ := hrd
    exact hq
  have hcls := ConRon.Bridge.Inductives.classes_denote rd.recCls hsl
  obtain ⟨h1ok, hrdS, so, sl, hso, hsl', hspl⟩ := hd1
  have h1ne : ¬ r1.headD 0 = 0 := by rw [h1ok]; decide
  rw [cbcW.k_class_read.arm1 p n vis pp po pl co cl r1 s1.mem h1ne] at h
  have hsz1 : (s1.mem.arr64 IW).size < 2 ^ 64 := hS1.2.2.2.1
  obtain ⟨wso, hwsob⟩ := iwN_rdW_at (k := 0) (w := r1.tail.headD 0) (by simpa using hso) hsz1
  obtain ⟨wsl, hwslb⟩ := iwN_rdW_at (k := 1) (w := r1.tail.headD 0) hsl' hsz1
  rw [show (r1.tail.headD 0 + UInt64.ofNat 0 : Word) = r1.tail.headD 0 by simp] at wso
  rw [show (UInt64.ofNat 1 : Word) = 1 from rfl] at wsl
  rw [wso, wsl] at h
  have hsoT : (UInt64.ofNat so : Word).toNat = so := UInt64.toNat_ofNat_of_lt' hwsob
  have hslT : (UInt64.ofNat sl : Word).toNat = sl := UInt64.toNat_ofNat_of_lt' hwslb
  obtain ⟨hslots, hext⟩ := slots_ok hspl hsz1
  -- `class_read_classes` (L only)
  obtain ⟨⟨r2, m2⟩, c2, h⟩ := of_K h rfl
  rw [cbcW.k_class_read_classes.arm1] at h
  obtain ⟨s2, hs2, -, hS2, hg2, hcc⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (classReadClasses_refines p hP.clm.keys.copy hP.ha hP.clm.keys.cons hP.crc n _ a1 dn vis fe
      (UInt64.ofNat so) (UInt64.ofNat sl) rd.slots hS1 (by rw [hsoT, hslT]; exact hslots)
      (by rw [hsoT, hslT]; exact hext)) c2
  simp only at hs2 hS2 hg2 hcc
  subst hs2
  have hP2 := PosMR.ofClosed hcl hfc c2 hP1
  have hA2 := hk2 n _ s1.mem r2 s2.mem c2 hA1
  have hC2 : StageC dn vis fe env s2.mem a1 := hC1.of_check hS2 hA2 hC1.check (Ext.refl _)
  have hg02 := hg1.trans hg2
  -- the keys
  obtain ⟨hnp2, -, -, -⟩ := partsShapeWords hg02 hbsD hq9
  rw [hnp2] at h
  obtain ⟨⟨r3, m3⟩, c3, h⟩ := of_K h rfl
  rw [cbcW.k_check_block_classes_keys.arm1] at h
  obtain ⟨s3, hs3, -, hW3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (ckk_spec p hP.clm.keys.keys n _ (UInt64.ofNat bs.nP) po pl (r2.headD 0) (r2.tail.headD 0)) c3
  simp only at hs3 hW3
  subst hs3
  obtain ⟨keys, a3, hrun3, hS3, hg3, hks, hP3⟩ :=
    ckkW_sim hP.clm.keys dn vis fe (UInt64.ofNat bs.nP) po pl pfvs n s2.mem a1 _ _ _ hS2
      (hpf.grow (OMono.decHL _ _) hg02) (Nat.le_trans hpfb hg02.1) (ccRes_pslR hcc) hP2 r3 s3.mem hW3
  rw [hnpT] at hrun3
  have hA3 := hk3 n _ s2.mem r3 s3.mem c3 hA2
  obtain ⟨c2', keysP, ⟨hkeys, hwk⟩, -⟩ := ConRon.Bridge.Inductives.classKeysOf_spec fe bs.nP pfvs
    pfvsP (by rw [hpl, hnPP]) (by rw [hnPP]; exact hpw) _ _ [] [] (fun _ h => nomatch h) a1 a3 keys
    c1'.ok ⟨ConRon.Bridge.denoteEList_ext c1'.ext _ _ hpfP, hcls, rfl⟩ hrun3
  have c12 := c1'.trans c2'
  have hC3 : StageC dn vis fe env s3.mem a3 := hC2.of_check hS3 hA3 c2'.ok c2'.ext
  have hg03 := hg02.trans hg3
  -- the majors
  obtain ⟨⟨r4, m4⟩, c4, h⟩ := of_K h rfl
  rw [cbcW.k_class_majors.arm1] at h
  obtain ⟨s4, hs4, -, hW4⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (clm_spec p hP.clm.cm n _ vis pp co cl po pl (r3.headD 0) (r3.tail.headD 0)) c4
  simp only at hs4 hW4
  subst hs4
  obtain ⟨ms, a4, hrun4, hC4, hg4, hms, hP4, hA4⟩ :=
    clmW_simC hq hIlpf hLC henv hP.clm pp co cl po pl bs css pfvs pP cssP pfvsP hpw n hn s3.mem a3 _ _ keys
      keysP hC3 hA3 (hbsD.grow (decBS_mono _) hg03) (partsHsrc_grow hg03 hq9 hsrc)
      (hcss.grow decCNS_mono hg03) (hpf.grow (OMono.decHL _ _) hg03) (Nat.le_trans hpfb hg03.1) hks
      hP3 (fun k hk x hx => ⟨pP.nP, hnPP ▸ hwk k hk x hx⟩)
      (ConRon.Bridge.Inductives.dShape_ext c12.ext _ _ hshP)
      (ConRon.Bridge.Inductives.dCtors_ext.list c12.ext _ _ hcssP)
      (ConRon.Bridge.denoteEList_ext c12.ext _ _ hpfP) hkeys r4 s4.mem hW4
  obtain ⟨c3', -⟩ := ConRon.Bridge.Inductives.classMajors_spec fe (ConRon.Bridge.CoreSpec.of_core rfl)
    henv bs pP css cssP pfvs pfvsP hpl hpw keys keysP (fun k hk x hx => ⟨pP.nP, hnPP ▸ hwk k hk x hx⟩) a3 a4
    ms hC3.check ⟨ConRon.Bridge.Inductives.dShape_ext c12.ext _ _ hshP,
      ConRon.Bridge.Inductives.dCtors_ext.list c12.ext _ _ hcssP,
      ConRon.Bridge.denoteEList_ext c12.ext _ _ hpfP, hkeys⟩ hrun4
  have hg04 := hg03.trans hg4
  -- one class per member (L only)
  obtain ⟨⟨r5, m5⟩, c5, h⟩ := of_K h rfl
  obtain ⟨s5, hs5, -, hm5, hW5⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (opm_spec p hP.cnt hP.opm n _ 0 (rdW (s4.mem.arr64 IW) (pp + 1)) (r4.headD 0) (r4.tail.headD 0)) c5
  simp only at hs5 hm5 hW5
  subst hs5
  have hS4 := hC4.stage
  have hT0 : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hpp1 : pp.toNat + 1 < 2 ^ 64 := by omega
  have hq1 : (pp + 1 : Word).toNat = pp.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hk1' : rdW (s4.mem.arr64 IW) (pp + 1) = UInt64.ofNat bs.k := by
    rw [partsRdIW_grow hg04 (by rw [hq1]; omega)]
    have e : (pp + 1 : Word) = UInt64.ofNat (pp.toNat + 1) := by
      apply UInt64.toNat_inj.mp; rw [hq1]; simp; omega
    rw [e]; exact decBS_k (hbsD.get (decBS_mono _)) hpp1
  have hsz4 : (s4.mem.arr64 IW).size < 2 ^ 64 := hS4.2.2.2.1
  have hgood := opmW_ok n s4.mem 0 _ _ _ _ ms hW5 (hms.1.get (OMono.decPL (fun q => decTM_mono q) _ _))
    (by have := hms.2; have := Nat.lt_of_le_of_lt hS4.2.1 hsz4; omega) hsz4
  obtain ⟨ok, lk, -, hlk, hgdk⟩ := decAt_some (decBS_some (hbsD.get (decBS_mono _))).1
  have hkb : bs.k < 2 ^ 64 := by rw [BlockShape.k, decPL_length _ hgdk]; exact (iwN_rdW hlk hpp1).2
  rw [hk1', UInt64.toNat_ofNat_of_lt' hkb, show (0 : Word).toNat = 0 from rfl, Nat.sub_zero,
    ← List.range_eq_range'] at hgood
  by_cases hz : r5.headD 0 = 0
  · rw [cbcW.k_check_block_classes_one_per_member.abort1 _ _ _ _ _ _ hz] at h; cases h
  rw [cbcW.k_check_block_classes_one_per_member.arm1 _ _ _ _ _ _ hz] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hall : (List.range bs.k).all (fun t => (ms.filter (·.member == some t)).length == 1) = true := by
    have : (r5.headD 0 != 0) = true := by simpa using hz
    rw [this] at hgood; exact hgood.symm
  rw [hm5]
  refine ⟨(rd, ms), a4, ?_, hC4, hg04, ?_, by simpa using hms, hP4, hA4, c12.trans c3'⟩
  · simp only [ConRon.Arena.checkBlockClasses, StateT.run_bind, hrun1, except_ok_bind]
    simp only [hrun3, except_ok_bind, hrun4, hall, ite_true]
    rfl
  · exact stab_decCR_decB (by simpa using hrdS.grow (hg2.trans (hg3.trans hg4))) hS4.2.2.2.1

include hq hIlpf hLC henv in
/-- **`check_block_classes` refines `checkBlockClasses`** under `StageC` (the inputs' denotations
as con-ron's `checkBlockClasses_spec` asks; the walk memos across the callees by `AbsKeep`). -/
@[refines ConRon.Arena.checkBlockClasses]
theorem checkBlockClasses_refinesC (hP : CbcProg p) {fs : List FnName}
    (hcl : closedA p posFreeA posFreeC fs = true) (hfr : "class_read" ∈ fs)
    (hfc : "class_read_classes" ∈ fs) (n : Nat)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (pp po pl co cl : Word) (bs : BlockShape) (css : List (List (IConstantVal × Nat)))
    (pfvs : List EIdx) (hC : StageC dn vis fe env s₀.mem a₀) (hb : BSOK s₀.mem pp.toNat bs)
    (hsrc : ShapeSrc s₀.mem pp)
    (hrecs : RecsDec s₀.mem (rdW (s₀.mem.arr64 IW) (pp + 2)) (rdW (s₀.mem.arr64 IW) (pp + 3)) bs.recs)
    (hcss : PSlR decCNS css co cl s₀.mem)
    (hpf : DecB (fun m => decHL m po.toNat pl.toNat) s₀.mem pfvs)
    (hpfb : po.toNat + pl.toNat ≤ iwTop s₀.mem) (hPm : PosMR s₀.mem) (hA : AbsOK s₀.mem)
    (hOpf : OpfF p) (hk2 : AbsKeep p "class_read_classes")
    (hk3 : AbsKeep p "check_block_classes_keys")
    {pP : ConLeche.BlockShape} {pfvsP : List ConLeche.Expr}
    {cssP : List (List (ConLeche.ConstantVal × Nat))}
    (hpl : pfvsP.length = pP.nP) (hpw : ∀ x ∈ pfvsP, ConLeche.Expr.WScoped pP.nP x)
    (hshP : ConRon.Bridge.Inductives.dShape a₀.store bs = some pP)
    (hpfP : Frontend.denoteEList a₀.store pfvs = some pfvsP)
    (hcssP : css.mapM (ConRon.Bridge.Inductives.dCtors a₀.store) = some cssP) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check_block_classes" [vis, pp, po, pl, co, cl]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.checkBlockClasses V fe bs pfvs css) a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (ConRon.Arena.checkBlockClasses V fe bs pfvs css) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      DecB (fun m => decCR m (r.headD 0).toNat) s'.mem
        (AM.res (ConRon.Arena.checkBlockClasses V fe bs pfvs css) a₀).1 ∧
      PSlR decTM (AM.res (ConRon.Arena.checkBlockClasses V fe bs pfvs css) a₀).2
        (r.tail.headD 0) (r.tail.tail.headD 0) s'.mem ∧ PosMR s'.mem ∧ AbsOK s'.mem ∧
      ConRon.Bridge.CoreStep V env fe a₀
        (AM.st (ConRon.Arena.checkBlockClasses V fe bs pfvs css) a₀); ⊤⦄ :=
  triple_post (cbc_spec p hP.cbc (n + 1) s₀ vis pp po pl co cl) fun _ _ ⟨hl, hm⟩ =>
    let ⟨hok, hQ⟩ := Sim.run (cbcW_simC hq hIlpf hLC henv hP hcl hfr hfc n hn _ a₀ pp po pl co cl bs css
      pfvs hC hb hsrc hrecs hcss hpf hpfb hPm hA hOpf hk2 hk3 hpl hpw hshP hpfP hcssP) hm
    ⟨hl, hok, hQ⟩

end sims

end L.Ind
