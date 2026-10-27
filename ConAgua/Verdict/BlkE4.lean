import ConAgua.Verdict.IndA3
import ConAgua.Verdict.IndBE
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen

/-!
# `check_block_classes`' error claim (lane `verdicts-b`, helper `ia2`, fork `blk`)

`check_block_classes_keys` (`ckkE_claim` by induction on the fuel: `class_key_of`'s claim
`ClassKeyOfE`, its ok run by `kofCall_sim`), `check_block_classes` (`checkBlockClassesE_claim`:
`classRead`'s `none` and the one-class-per-member test reject as the twin's; `class_majors` by
`ClassMajorsE`; `class_read`, `class_read_classes`, the count claim nothing).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model ckkE_spec (p : Prog) (hf : p.lookup "check_block_classes_keys" = some checkBlockClassesKeys)
  fns [hf ↦ ckkE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model cbcE_spec (p : Prog) (hf : p.lookup "check_block_classes" = some checkBlockClassesL)
  fns [hf ↦ cbcE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] heartbeats 1000000 simp [rdW] errors

theorem blkE4_nv : ∀ f ∈ ["sl_cons", "class_read", "class_read_classes", "check_block_classes_one_per_member"],
    f ∈ _root_.L.Checker.nvFns := by
  decide +kernel

/-- **`check_block_classes_keys`' error claim** (the model at fuel `n`; `ckkW_sim`'s hypotheses),
from `class_key_of`'s. -/
theorem ckkE_claim {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true) (eKey : ClassKeyOfE p)
    (hP : KeysProg p) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (nP po pl : Word) (pfvs : List EIdx) (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (ko kl : Word) (ks : List ClassKey),
    StageR dn vis fe m a → DecB (fun m => decHL m po.toNat pl.toNat) m pfvs →
    po.toNat + pl.toNat ≤ iwTop m → PSlR decCK ks ko kl m → PosMR m →
    ∀ e, ckkE p n m nP po pl ko kl = .error e →
      ErrClaim (ks.mapM (ConRon.Arena.classKeyOf nP.toNat pfvs)) a e := by
  induction n with
  | zero =>
    intro m a ko kl ks _ _ _ _ _ e he
    rw [ckkE.eq_1] at he; cases he; exact ErrClaim.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a ko kl ks hS hpf hpb hks hPm e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  by_cases hkl : kl = 0
  · rw [ckkE.arm1 p n m nP po pl ko kl hkl] at he; cases he
  obtain ⟨q, k0, ks', rfl, hw, hqb, hdk, hks'⟩ := partsPSl_cons hks hkl
  have hq' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  rw [ckkE.arm2 p n m nP po pl ko kl hkl, hw] at he
  simp only [List.mapM_cons]
  cases h1 : callE p n "class_key_of" [nP, po, pl, UInt64.ofNat q] m with
  | error e1 =>
    rw [h1, ckkE.k_class_key_of.none] at he; cases he
    exact ErrClaim.bind_left (eKey hP.toKofProg dn fe vis ⟨m, Locals.init []⟩ a nP po pl (UInt64.ofNat q) pfvs k0 hS
      (hpf.get (OMono.decHL _ _)) hpb (by rw [hq']; exact hdk) hPm n (by omega) _ h1)
  | ok q1 =>
    obtain ⟨r1, m1⟩ := q1
    rw [h1, ckkE.k_class_key_of.arm1] at he
    obtain ⟨x1, a1, hrun1, hd1, hS1, hg1, hP1⟩ :=
      kofCall_sim hP.toKofProg n hS (hpf.get (OMono.decHL _ _)) hpb (by rw [hq']; exact hdk) hPm r1 m1
        (callW_of_callE h1)
    refine ErrClaim.bind_right hrun1 ?_
    cases h2 : ckkE p n m1 nP po pl (ko + 1) (kl - 1) with
    | error e2 =>
      rw [h2, ckkE.k_check_block_classes_keys.none] at he; cases he
      exact ErrClaim.bind_left (ih (by omega) m1 a1 (ko + 1) (kl - 1) ks' hS1 (hpf.grow (OMono.decHL _ _) hg1)
        (Nat.le_trans hpb hg1.1) (hks'.grow decCK_mono hg1) hP1 _ h2)
    | ok q2 =>
      obtain ⟨r2, m2⟩ := q2
      rw [h2, ckkE.k_check_block_classes_keys.arm1] at he
      cases h3 : callE p n "sl_cons" [r1.headD 0, r2.headD 0, r2.tail.headD 0] m2 with
      | error e3 =>
        rw [h3, ckkE.k_sl_cons.none] at he; cases he
        exact ErrClaim.of_callE_nv hnv (blkE4_nv _ (by simp)) h3
      | ok q3 => obtain ⟨r3, m3⟩ := q3; rw [h3, ckkE.k_sl_cons.arm1] at he; cases he

/-- **`check_block_classes`' error claim** (`CheckBlockClassesE`, the `err_stmt` of
`checkBlockClasses_refinesC`): the two rejects (`classRead`'s `none`, not one class per member) are
the twin's; `check_block_classes_keys` by `ckkE_claim`, `class_majors` by `ClassMajorsE`. -/
theorem checkBlockClassesE_claim {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (eKey : ClassKeyOfE p) (eClm : ClassMajorsE p) : CheckBlockClassesE p := by
  intro dn vis fe env hq hIlpf hLC henv hP fs hcl hfr hfc s₀ a pp po pl co cl bs css pfvs hC hb hsrc hrecs
    hcss hpf hpfb hPm hA hOpf hk2 hk3 pP pfvsP cssP hpl hpw hshP hpfP hcssP F hF e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  replace he := triple_of_callE_err (cbcE_spec p hP.cbc F ⟨s₀.mem, Locals.init []⟩ vis pp po pl co cl) he
    (Err.code_ne_of_cls hk0)
  simp only at he
  cases F with
  | zero => rw [cbcE.eq_1] at he; cases he; exact absurd Err.cls_outOfFuel hk0
  | succ n =>
  have hn : n ≤ 2 ^ 62 := by omega
  have hS := hC.stage
  obtain ⟨-, hrecsP, hnPP, -, -, -, -⟩ := ConRon.Bridge.Inductives.dShape_inv hshP
  have hbsD : DecB (fun m => decBS m pp.toNat) s₀.mem bs := hb.1
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hbsD hsrc
  obtain ⟨hnp, hnpb, -, -⟩ := partsShapeWords (IWGrow.refl s₀.mem) hbsD hq9
  have hnpT : (UInt64.ofNat bs.nP : Word).toNat = bs.nP := UInt64.toNat_ofNat_of_lt' hnpb
  rw [cbcE.arm1] at he
  -- `class_read`
  cases c1 : callE p n "class_read" [pp, vis, rdW (s₀.mem.arr64 IW) (pp + 4), rdW (s₀.mem.arr64 IW) (pp + 2),
      rdW (s₀.mem.arr64 IW) (pp + 3)] s₀.mem with
  | error e1 =>
    rw [c1, cbcE.k_class_read.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (blkE4_nv _ (by simp)) c1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [c1] at he
  obtain ⟨s1, hs1, -, hok1, ⟨hS1, hg1, hd1⟩, hA1⟩ := triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩)
    (classRead_refinesA p hP.read hOpf n _ a dn vis fe pp _ _ _ bs bs.recs hS hA hb hrecs) (callW_of_callE c1)
  simp only at hs1 hS1 hg1 hd1 hA1
  subst hs1
  have hP1 := PosMR.ofClosed hcl hfr (callW_of_callE c1) hPm
  rw [hnp, hnpT] at hok1 hS1 hd1
  have hrun1 := AM.run_of_ok _ a hok1
  obtain ⟨p1, ho1⟩ := ConRon.Bridge.Inductives.classRead_spec bs pP env fe bs.nP bs.recs pP.recs a _ _
    hC.check.state ⟨hshP, hC.check.ienv.toS, hrecsP⟩ hrun1
  generalize hx1 : AM.res (ConRon.Arena.classRead bs fe bs.nP bs.recs) a = x1 at hrun1 hd1 ho1
  generalize ha1 : AM.st (ConRon.Arena.classRead bs fe bs.nP bs.recs) a = a1 at hrun1 hS1 p1 ho1
  have hC1 : StageC dn vis fe env s1.mem a1 := hC.of_pstep hS1 hA1 p1
  have c1' := p1.toCore hC.check
  unfold ConRon.Arena.checkBlockClasses
  refine ErrClaim.bind_right hrun1 ?_
  rcases x1 with _ | rd
  · simp only [decRead] at hd1
    rw [cbcE.k_class_read.abort1 p n vis pp po pl co cl r1 s1.mem hd1] at he; cases he
    exact ErrClaim.fail _ _ (by decide)
  obtain ⟨rdP, -, hrd⟩ := ho1
  have hsl : rd.slots.mapM (ConRon.Bridge.Inductives.dSlot a1.store) = some rdP.slots := by
    simp only [ConRon.Bridge.Inductives.dClassRead, Option.map_eq_some_iff] at hrd
    obtain ⟨q, hq, rfl⟩ := hrd
    exact hq
  have hcls := ConRon.Bridge.Inductives.classes_denote rd.recCls hsl
  obtain ⟨h1ok, hrdS, so, sl, hso, hsl', hspl⟩ := hd1
  have h1ne : ¬ r1.headD 0 = 0 := by rw [h1ok]; decide
  rw [cbcE.k_class_read.arm1 p n vis pp po pl co cl r1 s1.mem h1ne] at he
  have hsz1 : (s1.mem.arr64 IW).size < 2 ^ 64 := hS1.2.2.2.1
  obtain ⟨wso, hwsob⟩ := iwN_rdW_at (k := 0) (w := r1.tail.headD 0) (by simpa using hso) hsz1
  obtain ⟨wsl, hwslb⟩ := iwN_rdW_at (k := 1) (w := r1.tail.headD 0) hsl' hsz1
  rw [show (r1.tail.headD 0 + UInt64.ofNat 0 : Word) = r1.tail.headD 0 by simp] at wso
  rw [show (UInt64.ofNat 1 : Word) = 1 from rfl] at wsl
  rw [wso, wsl] at he
  have hsoT : (UInt64.ofNat so : Word).toNat = so := UInt64.toNat_ofNat_of_lt' hwsob
  have hslT : (UInt64.ofNat sl : Word).toNat = sl := UInt64.toNat_ofNat_of_lt' hwslb
  obtain ⟨hslots, hext⟩ := slots_ok hspl hsz1
  -- `class_read_classes` (L only)
  cases c2 : callE p n "class_read_classes" [UInt64.ofNat so, UInt64.ofNat sl] s1.mem with
  | error e2 =>
    rw [c2, cbcE.k_class_read_classes.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (blkE4_nv _ (by simp)) c2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [c2, cbcE.k_class_read_classes.arm1] at he
  obtain ⟨s2, hs2, -, hS2, hg2, hcc⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (classReadClasses_refines p hP.clm.keys.copy hP.ha hP.clm.keys.cons hP.crc n _ a1 dn vis fe
      (UInt64.ofNat so) (UInt64.ofNat sl) rd.slots hS1 (by rw [hsoT, hslT]; exact hslots)
      (by rw [hsoT, hslT]; exact hext)) (callW_of_callE c2)
  simp only at hs2 hS2 hg2 hcc
  subst hs2
  have hP2 := PosMR.ofClosed hcl hfc (callW_of_callE c2) hP1
  have hA2 := hk2 n _ s1.mem r2 s2.mem (callW_of_callE c2) hA1
  have hC2 : StageC dn vis fe env s2.mem a1 := hC1.of_check hS2 hA2 hC1.check (Ext.refl _)
  have hg02 := hg1.trans hg2
  -- the keys
  obtain ⟨hnp2, -, -, -⟩ := partsShapeWords hg02 hbsD hq9
  rw [hnp2] at he
  cases c3 : callE p n "check_block_classes_keys" [UInt64.ofNat bs.nP, po, pl, r2.headD 0, r2.tail.headD 0]
      s2.mem with
  | error e3 =>
    rw [c3, cbcE.k_check_block_classes_keys.none] at he; cases he
    have hW := triple_of_callE_err (ckkE_spec p hP.clm.keys.keys n ⟨s2.mem, Locals.init []⟩ (UInt64.ofNat bs.nP)
      po pl (r2.headD 0) (r2.tail.headD 0)) c3 (Err.code_ne_of_cls hk0)
    simp only at hW
    have h := ckkE_claim hnv eKey hP.clm.keys dn vis fe (UInt64.ofNat bs.nP) po pl pfvs n hn s2.mem a1 _ _ _ hS2
      (hpf.grow (OMono.decHL _ _) hg02) (Nat.le_trans hpfb hg02.1) (ccRes_pslR hcc) hP2 _ hW
    rw [hnpT] at h
    exact ErrClaim.bind_left h
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [c3, cbcE.k_check_block_classes_keys.arm1] at he
  obtain ⟨s3, hs3, -, hW3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (ckk_spec p hP.clm.keys.keys n _ (UInt64.ofNat bs.nP) po pl (r2.headD 0) (r2.tail.headD 0))
    (callW_of_callE c3)
  simp only at hs3 hW3
  subst hs3
  obtain ⟨keys, a3, hrun3, hS3, hg3, hks, hP3⟩ :=
    ckkW_sim hP.clm.keys dn vis fe (UInt64.ofNat bs.nP) po pl pfvs n s2.mem a1 _ _ _ hS2
      (hpf.grow (OMono.decHL _ _) hg02) (Nat.le_trans hpfb hg02.1) (ccRes_pslR hcc) hP2 r3 s3.mem hW3
  rw [hnpT] at hrun3
  have hA3 := hk3 n _ s2.mem r3 s3.mem (callW_of_callE c3) hA2
  obtain ⟨c2', keysP, ⟨hkeys, hwk⟩, -⟩ := ConRon.Bridge.Inductives.classKeysOf_spec fe bs.nP pfvs
    pfvsP (by rw [hpl, hnPP]) (by rw [hnPP]; exact hpw) _ _ [] [] (fun _ h => nomatch h) a1 a3 keys
    c1'.ok ⟨ConRon.Bridge.denoteEList_ext c1'.ext _ _ hpfP, hcls, rfl⟩ hrun3
  have c12 := c1'.trans c2'
  have hC3 : StageC dn vis fe env s3.mem a3 := hC2.of_check hS3 hA3 c2'.ok c2'.ext
  have hg03 := hg02.trans hg3
  refine ErrClaim.bind_right hrun3 ?_
  -- the majors
  cases c4 : callE p n "class_majors" [vis, pp, co, cl, po, pl, r3.headD 0, r3.tail.headD 0] s3.mem with
  | error e4 =>
    rw [c4, cbcE.k_class_majors.none] at he; cases he
    exact ErrClaim.bind_left (eClm hq hIlpf hLC henv hP.clm ⟨s3.mem, Locals.init []⟩ a3 pp co cl po pl _ _ bs css
      pfvs keys hC3 hA3 (hbsD.grow (decBS_mono _) hg03) (partsHsrc_grow hg03 hq9 hsrc)
      (hcss.grow decCNS_mono hg03) (hpf.grow (OMono.decHL _ _) hg03) (Nat.le_trans hpfb hg03.1) hks hP3
      hpw (fun k hk x hx => ⟨pP.nP, hnPP ▸ hwk k hk x hx⟩)
      (ConRon.Bridge.Inductives.dShape_ext c12.ext _ _ hshP)
      (ConRon.Bridge.Inductives.dCtors_ext.list c12.ext _ _ hcssP)
      (ConRon.Bridge.denoteEList_ext c12.ext _ _ hpfP) hkeys n hn _ c4)
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [c4, cbcE.k_class_majors.arm1] at he
  obtain ⟨s4, hs4, -, hW4⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (clm_spec p hP.clm.cm n _ vis pp co cl po pl (r3.headD 0) (r3.tail.headD 0)) (callW_of_callE c4)
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
  have hg04 := hg03.trans hg4
  refine ErrClaim.bind_right hrun4 ?_
  -- one class per member (L only)
  cases c5 : callE p n "check_block_classes_one_per_member" [0, rdW (s4.mem.arr64 IW) (pp + 1), r4.headD 0,
      r4.tail.headD 0] s4.mem with
  | error e5 =>
    rw [c5, cbcE.k_check_block_classes_one_per_member.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (blkE4_nv _ (by simp)) c5
  | ok q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [c5] at he
  obtain ⟨s5, hs5, -, hm5, hW5⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (opm_spec p hP.cnt hP.opm n _ 0 (rdW (s4.mem.arr64 IW) (pp + 1)) (r4.headD 0) (r4.tail.headD 0))
    (callW_of_callE c5)
  simp only at hs5 hm5 hW5
  subst hs5
  have hS4 := hC4.stage
  have hT0 : iwTop s₀.mem < 2 ^ 64 := (rdW (s₀.mem.arr64 CTL) 200).toNat_lt
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
  · rw [cbcE.k_check_block_classes_one_per_member.abort1 _ _ _ _ _ _ hz] at he; cases he
    have hall : (List.range bs.k).all (fun t => (ms.filter (·.member == some t)).length == 1) = false := by
      have : (r5.headD 0 != 0) = false := by rw [hz]; rfl
      rw [this] at hgood; exact hgood.symm
    show ErrClaim (if (List.range bs.k).all (fun t => (ms.filter (·.member == some t)).length == 1) then _ else _)
      _ _
    rw [hall]
    exact ErrClaim.fail _ _ (by decide)
  · rw [cbcE.k_check_block_classes_one_per_member.arm1 _ _ _ _ _ _ hz] at he; cases he

end L.Ind
