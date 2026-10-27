import ConAgua.Arena.IndT.RecCheckTmn

/-!
# `classesNfs` under `StageC` (lane `indstaget`, helper `pds`)

`classes_nfs`' loop (`cnsW`, the callees through the program's `callW`), from `StageC` and the
inputs' denotations con-ron's `classesNfs_spec` asks; its twin side transcribed from that spec's
proof: per class `targetMajorNfs` (`tmnW_okPC`, con-ron's `targetMajorNfs_spec` on its run for the
extension), the record's copy (L only).
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dShape dCtors dCtorNf dMajor)
open ConRon.Bridge (CoreStep denote_ext denoteEList_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq henv in
/-- **`tmnW_okP` under `StageC`** (twin side as `tmnW_okC`). -/
theorem tmnW_okPC (mb : Mem) (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ {m m' : Mem} {a : AState} {q fto ftl pfo pfl us dso dsl cto ctl nfo nfl : Word}
    {r : List Word} {bs : BlockShape} {formerTys pfvs ds : List EIdx} {ctors : List (IConstantVal × Nat)}
    {nfs : List NestCtorNf} {pP : ConLeche.BlockShape} {formerTysP pfvsP dsP : List ConLeche.Expr}
    {usP : List ConLeche.Level} {ctorsP : List (ConLeche.ConstantVal × Nat)}
    {nfsP : List ConLeche.NestCtorNf},
    tmnW (realCall p) n m vis q fto ftl pfo pfl us dso dsl cto ctl nfo nfl = some (r, m') →
    StageC dn vis fe env m a → AbsOK m → BSOK m q.toNat bs → H us →
    decHL m fto.toNat ftl.toNat = some formerTys → fto.toNat + ftl.toNat ≤ iwTop m →
    HSl0 m pfo pfl pfvs → HSl0 m dso dsl ds →
    DecB (fun m => decPL m (decCN m) cto.toNat ctl.toNat) m ctors → cto.toNat + ctl.toNat < 2 ^ 64 →
    PSlR decNCN nfs nfo nfl m → (∃ ps, decNL m nfo.toNat nfl.toNat = some ps ∧ PtrsB mb ps nfs) →
    RcMR m →
    dShape a.store bs = some pP → Frontend.denoteEList a.store formerTys = some formerTysP →
    Frontend.denoteEList a.store pfvs = some pfvsP → denoteLs a.store.lss (decI us) = some usP →
    Frontend.denoteEList a.store ds = some dsP → dCtors a.store ctors = some ctorsP →
    nfs.mapM (dCtorNf a.store) = some nfsP →
    (∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t) →
    (∀ x ∈ pfvsP, ConLeche.Expr.WScoped pfvsP.length x) →
    ∃ ys a', (ConRon.Arena.targetMajorNfs V fe bs formerTys pfvs (decI us) ds ctors nfs).run a = .ok (ys, a') ∧
      PSlR decNCN ys (r.headD 0) (r.tail.headD 0) m' ∧ StageC dn vis fe env m' a' ∧ IWGrow m m' ∧
      RcMR m' ∧ AbsOK m' ∧
      (r.tail.headD 0 = 0 ∨ iwTop m ≤ (r.headD 0).toNat) ∧
      ∃ ps, decNL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some ps ∧ PtrsB mb ps ys := by
  induction n with
  | zero =>
    intro m m' a q fto ftl pfo pfl us dso dsl cto ctl nfo nfl r bs formerTys pfvs ds ctors nfs pP
      formerTysP pfvsP dsP usP ctorsP nfsP h
    simp [tmnW] at h
  | succ n ih =>
  intro m m' a q fto ftl pfo pfl us dso dsl cto ctl nfo nfl r bs formerTys pfvs ds ctors nfs pP
    formerTysP pfvsP dsP usP ctorsP nfsP h hC hA hbs hus hft hftb hpf hds hct hctb hnf hptr hP hsh hftP
    hpfP husP hdsP hctP hnfP hformer hpw
  have hS := hC.stage
  by_cases hl : nfl = 0
  · rw [tmnW_nil (h := hl)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    subst hl
    have : nfs = [] := by
      have := decPL_length _ (hnf.1.get (OMono.decPL decNCN_mono _ _)); simpa using this
    subst this
    exact ⟨[], a, rfl, PSlR.nil _ _, hC, IWGrow.refl _, hP, hA, .inl rfl, [], by simp [decNL], FA2.nil⟩
  rw [tmnW_cons (h := hl)] at h
  have hsz := hS.2.2.2.1
  obtain ⟨nf, nfs', rfl, hnf0, hnf'⟩ := hnf.uncons hl hsz
  obtain ⟨nfP, nfsP', rfl, hnfP1, hnfsP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hnfP
  obtain ⟨ps, hps, hpb⟩ := hptr
  have hb64 := hS.lt64 hnf.2
  obtain ⟨e1, e2, hl0⟩ := slice_step hl hb64
  obtain ⟨L, hL⟩ : ∃ L, nfl.toNat = L + 1 := ⟨nfl.toNat - 1, by omega⟩
  rw [hL, decNL_succ] at hps
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hps
  obtain ⟨v, hv, ps', hps', rfl⟩ := hps
  cases hpb with
  | cons hpv hpb' =>
  obtain ⟨⟨rr, m1⟩, h1, h⟩ := of_K h rfl
  rw [tmnK1_some] at h
  obtain ⟨ys, a1, run1, hys, hC1, hg1, hP1, hA1, hfr1, pr, hpr, hprb⟩ := ih (by omega) h1 hC hA hbs
    hus hft hftb hpf hds hct hctb hnf' ⟨ps', by rw [e1, e2, hL]; simpa using hps', hpb'⟩ hP hsh hftP
    hpfP husP hdsP hctP hnfsP' hformer hpw
  obtain ⟨c1, -⟩ := ConRon.Bridge.Inductives.targetMajorNfs_spec fe (ConRon.Bridge.CoreSpec.of_core rfl)
    henv bs pP formerTys pfvs formerTysP pfvsP (decI us) usP ds dsP ctors ctorsP hformer hpw nfs'
    nfsP' a a1 ys hC.check ⟨hsh, hftP, hpfP, husP, hdsP, hctP, hnfsP'⟩ run1
  have hS1 := hC1.stage
  have hnfo : nfo.toNat < iwTop m := by have := hnf.2; omega
  have he : rdW (m1.arr64 IW) nfo = rdW (m.arr64 IW) nfo := by
    simp only [rdW]; rw [hg1.2.2.1 _ hnfo]
  rw [he] at h
  have hev : rdW (m.arr64 IW) nfo = UInt64.ofNat v := by
    have := (iwN_rdW hv (by omega)).1; rwa [UInt64.ofNat_toNat] at this
  have hvb : v < 2 ^ 64 := (iwN_rdW hv (by omega)).2
  generalize hE : rdW (m.arr64 IW) nfo = e at h hnf0
  have heT : e.toNat = v := by rw [← hE, hev, UInt64.toNat_ofNat_of_lt' hvb]
  have hnf1 : DecB (fun m' => decNCN m' e.toNat) m1 nf := hnf0.grow (decNCN_mono _) hg1
  have hsz1 := hS1.2.2.2.1
  obtain ⟨hcH, hcD, hlH, hlD, hdsl⟩ := decNCN_fields hnf1 hsz1
  have hct1 := hct.grow (OMono.decPL decCN_mono _ _) hg1
  obtain ⟨hv', h2, h⟩ := of_K h rfl
  obtain ⟨hany, -⟩ := chnW_ok n m1 cto ctl _ hv' ctors h2 (hct1.get (OMono.decPL decCN_mono _ _)) hcH hctb
  rw [hcD] at hany
  have hrun_tail : ∀ {α : Type} (k : List NestCtorNf → AM α),
      ((ConRon.Arena.targetMajorNfs V fe bs formerTys pfvs (decI us) ds ctors nfs') >>= k).run a =
        (k ys).run a1 := by
    intro α k; simp only [StateT.run_bind, run1]; rfl
  have hprg : ∀ {m2 : Mem}, IWGrow m1 m2 → decNL m2 (rr.headD 0).toNat (rr.tail.headD 0).toNat = some pr := by
    intro m2 hg; rw [decNL_grow hg hys.2]; exact hpr
  by_cases hh : hv' = 0
  · rw [tmnK2_no (h := hh)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    refine ⟨ys, a1, ?_, hys, hC1, hg1, hP1, hA1, by simpa using hfr1, pr, by simpa using hpr, hprb⟩
    have hf : ctors.any (fun c => c.1.name == nf.ctor) = false := by rw [← hany, hh]; rfl
    rw [ConRon.Arena.targetMajorNfs, hrun_tail]; simp only [hf, Bool.false_eq_true, ite_false]; rfl
  rw [tmnK2_yes (h := hh)] at h
  have ht : ctors.any (fun c => c.1.name == nf.ctor) = true := by rw [← hany]; simpa using hh
  obtain ⟨-, hlvP, hedP, -⟩ := ConRon.Bridge.Inductives.RC.dCtorNf_inv
    (ConRon.Bridge.Inductives.dCtorNf_ext c1.ext _ _ hnfP1)
  obtain ⟨⟨rk, m2⟩, h3, h⟩ := of_K h rfl
  obtain ⟨c, a2, run2, hc, hC2, hg2, hP2, hA2⟩ := tcmF_okC hq henv n (by omega) h3 hC1 hA1
    (hbs.grow hg1) hus hlH (by rw [decHL_grow hg1 hftb]; exact hft) (by have := hg1.1; omega)
    (hpf.grow hg1) (hds.grow hg1) hdsl hP1
    (ConRon.Bridge.Inductives.dShape_ext c1.ext _ _ hsh) (denoteEList_ext c1.ext _ _ hftP)
    (denoteEList_ext c1.ext _ _ hpfP) (ConRon.Bridge.denoteLs_ext husP c1.ext)
    (denoteEList_ext c1.ext _ _ hdsP) (by rw [hlD]; exact hlvP) hedP hformer hpw
  rw [hlD] at run2
  have hg12 := hg1.trans hg2
  by_cases hk : rk.headD 0 = 0
  · rw [tmnK3_drop (h := hk)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have hc0 : c = false := by rw [← hc, hk]; rfl
    subst hc0
    refine ⟨ys, a2, ?_, hys.grow (fun q => decNCN_mono q) hg2, hC2, hg12, hP2, hA2, by simpa using hfr1,
      pr, by simpa using hprg hg2, hprb⟩
    rw [ConRon.Arena.targetMajorNfs, hrun_tail]
    simp only [ht, ite_true, StateT.run_bind, run2, except_ok_bind, Bool.false_eq_true, ite_false]; rfl
  rw [tmnK3_keep (h := hk)] at h
  have hc1 : c = true := by rw [← hc]; simpa using hk
  subst hc1
  obtain ⟨⟨rc, m3⟩, h4, h⟩ := of_K h rfl
  rw [tmnK4_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hS3, hg3, hps3, hf3⟩ := consW_pslr (fun q => decNCN_mono q) h4 hC2.stage
    (hys.grow (fun q => decNCN_mono q) hg2) (hnf1.grow (decNCN_mono _) hg2)
  have hA3 := consW_afr h4 hA2
  have hys2 := hys.grow (fun q => decNCN_mono q) hg2
  obtain ⟨hr, hd, -, -, -, -⟩ := consW_decN h4 hC2.stage.2.2.2.1 hC2.stage.2.2.2.2.2 hys2.2 (hprg hg2)
  subst hr
  refine ⟨nf :: ys, a2, ?_, by simpa using hps3, hC2.of_pstep hS3 hA3 (PStep.refl hC2.check.state),
    hg12.trans hg3, hP2.fr hf3, hA3, ?_, e.toNat :: pr, by simpa using hd, ?_⟩
  · rw [ConRon.Arena.targetMajorNfs, hrun_tail]
    simp only [ht, ite_true, StateT.run_bind, run2, except_ok_bind]; rfl
  · right; simp only [List.headD_cons]; exact hg12.1
  · rw [heT]; exact FA2.cons hpv hprb

end sims

section loop
variable {p : Prog} (hkp : KnotStageProg p) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (P : CnsProg p) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
  (vis q fto ftl tblo tbll mo ml qr : Word) (bs : BlockShape) (formerTys : List EIdx)
  (tbl : List NestCtorNf) (ms : List TargetMajor) (mb : Mem)
  {pP : ConLeche.BlockShape} {formerTysP : List ConLeche.Expr} {tblP : List ConLeche.NestCtorNf}
include hkp henv P

/-- **`classes_nfs`' loop under `StageC`** (twin side: con-ron's `classesNfs_spec`'s list induction;
`cnsW_ok`'s words). -/
theorem cnsW_okC (hq : qr.toNat = iwTop mb) (hms : PSlR decTM ms mo ml mb) (htbl : PSlR decNCN tbl tblo tbll mb)
    (hbs : BSOK mb q.toNat bs) (hft : decHL mb fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop mb) (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (k : Nat) (hk : k ≤ 2 ^ 62) :
    ∀ (m m' : Mem) (a : AState) (j : Word) (acc : List TargetMajor) (ws : List Nat)
      (MsP : List ConLeche.TargetMajor),
    cnsW p k m vis q fto ftl tblo tbll mo ml qr j = some m' →
    StageC dn vis fe env m a → AbsOK m → IWGrow mb m → qr.toNat + ml.toNat ≤ iwTop m → RcMR m → j ≤ ml →
    decNL m qr.toNat j.toNat = some ws → FA2 (CnsRec mb (CnsSrc mb mo ml) (qr.toNat + ml.toNat) m) ws acc →
    dShape a.store bs = some pP → Frontend.denoteEList a.store formerTys = some formerTysP →
    tbl.mapM (dCtorNf a.store) = some tblP → (ms.drop j.toNat).mapM (dMajor a.store) = some MsP →
    (∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) →
    ∃ rest a', (ConRon.Arena.classesNfs V fe bs formerTys tbl (ms.drop j.toNat)).run a = .ok (rest, a') ∧
      StageC dn vis fe env m' a' ∧ IWGrow mb m' ∧ qr.toNat + ml.toNat ≤ iwTop m' ∧ RcMR m' ∧ AbsOK m' ∧
      ∃ ws', decNL m' qr.toNat ml.toNat = some ws' ∧ FA2 (CnsRec mb (CnsSrc mb mo ml) (qr.toNat + ml.toNat) m') ws' (acc ++ rest) := by
  have hms0 : decPL (truncM mb) (decTM (truncM mb)) mo.toNat ml.toNat = some ms := hms.1
  have hlen := decPL_length _ hms0
  obtain ⟨tps, -, htps, hmap⟩ := sumDecNL_of_decB htbl.1
  have htpb : PtrsB mb tps tbl := ptrsB_of_mapM hmap
  induction k with
  | zero => intro m m' a j acc ws MsP h; simp [cnsW] at h
  | succ k ih =>
  intro m m' a j acc ws MsP h hC hA hg htop hP hje hws hacc hsh hftP htblP hmsP hMs
  have hS := hC.stage
  have hsz := hS.2.2.2.1
  have hjm : j.toNat ≤ ml.toNat := UInt64.le_iff_toNat_le.mp hje
  have hT := (rdW (m.arr64 CTL) 200).toNat_lt
  by_cases hj : ¬ j < ml
  · rw [cnsW_exit (h := hj)] at h
    simp only [Option.some.injEq] at h; subst h
    have h1 : ml.toNat ≤ j.toNat := by simpa [UInt64.lt_iff_toNat_lt] using hj
    have hjeq : j.toNat = ml.toNat := by omega
    have : ms.drop j.toNat = [] := List.drop_eq_nil_of_le (by omega)
    rw [this]
    refine ⟨[], a, rfl, hC, hg, htop, hP, hA, ws, by rw [← hjeq]; exact hws, by simpa using hacc⟩
  simp only [Decidable.not_not] at hj
  have hjl : j.toNat < ml.toNat := UInt64.lt_iff_toNat_lt.mp hj
  have hml := ml.toNat_lt
  have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  -- the class `j`
  obtain ⟨p0, hp0, hsrc⟩ := decPL_getH (truncM mb) hms0 j.toNat hjl
  obtain ⟨hp0t, hp0m⟩ := rec2IwN_trunc hp0
  have hp0m' : iwN m (mo.toNat + j.toNat) = some p0 := by
    simp only [iwN, nat?, iwA] at hp0m ⊢; rw [hg.2.2.1 _ hp0t]; exact hp0m
  obtain ⟨hrd, hp0b⟩ := iwN_rdW_at (w := mo) (k := j.toNat) hp0m' hsz
  rw [show mo + UInt64.ofNat j.toNat = mo + j by simp] at hrd
  rw [cnsW_step (h := hj), hrd] at h
  have hp0T : (UInt64.ofNat p0 : Word).toNat = p0 := UInt64.toNat_ofNat_of_lt' hp0b
  have hsrcmb : DecB (fun m => decTM m p0) mb (ms[j.toNat]'(by omega)) := by
    show decTM (truncM mb) p0 = _; rw [hsrc]
  have hsrcB : DecB (fun m => decTM m (UInt64.ofNat p0 : Word).toNat) m (ms[j.toNat]'(by omega)) := by
    rw [hp0T]; exact hsrcmb.grow (decTM_mono _) hg
  obtain ⟨hlH, hlD, hdsS, hpfS, hctB, hctb⟩ := cnsTM_parts hsrcB hsz
  rw [List.drop_eq_getElem_cons (by omega)] at hmsP
  obtain ⟨MP, MsP', rfl, hmP, hmsP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hmsP
  obtain ⟨-, hlvls, hdsP, -, -, hctorsP, -, -, hpfvsP⟩ := ConRon.Bridge.Inductives.dMajor_inv hmP
  obtain ⟨hscp, -⟩ := hMs MP List.mem_cons_self
  -- `target_major_nfs`
  obtain ⟨⟨r1, m1⟩, c1, h⟩ := of_K h rfl
  rw [cnsK1_some] at h
  obtain ⟨s1, hs1, -, hw1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (tmn_spec p P.tmn (realCall p) (realCall_spec p) k _ vis q fto ftl
    (rdW (m.arr64 IW) (UInt64.ofNat p0 + 11)) (rdW (m.arr64 IW) (UInt64.ofNat p0 + 12))
    (rdW (m.arr64 IW) (UInt64.ofNat p0 + 1)) (rdW (m.arr64 IW) (UInt64.ofNat p0 + 2))
    (rdW (m.arr64 IW) (UInt64.ofNat p0 + 3)) (rdW (m.arr64 IW) (UInt64.ofNat p0 + 6))
    (rdW (m.arr64 IW) (UInt64.ofNat p0 + 7)) tblo tbll) c1
  simp only at hs1 hw1; subst hs1
  obtain ⟨es, a1, run1, hes, hC1, hg1, hP1, hA1, hfr, pse, hpse, hpseb⟩ := tmnW_okPC hkp henv mb k
    (by omega) hw1 hC hA
    (hbs.grow hg) hlH (by rw [decHL_grow hg hftb]; exact hft) (by have := hg.1; omega) hpfS hdsS hctB hctb
    (htbl.grow (fun q => decNCN_mono q) hg) ⟨tps, by rw [decNL_grow hg htbl.2]; exact htps, htpb⟩ hP
    hsh hftP hpfvsP (by rw [hlD]; exact hlvls) hdsP hctorsP htblP hformer hscp
  rw [hlD] at run1
  obtain ⟨c1, -⟩ := ConRon.Bridge.Inductives.targetMajorNfs_spec fe (ConRon.Bridge.CoreSpec.of_core rfl)
    henv bs pP formerTys _ formerTysP _ _ _ _ _ _ _ hformer hscp tbl tblP a a1 es hC.check
    ⟨hsh, hftP, hpfvsP, hlvls, hdsP, hctorsP, htblP⟩ run1
  have hS1 := hC1.stage
  -- `iw_alloc(13)`
  obtain ⟨⟨r2, m2⟩, c2, h⟩ := of_K h rfl
  rw [cnsK2_some] at h
  obtain ⟨s2, hs2, -, hw2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩) (iwAlloc_specW p P.ha k _ 13) c2
  simp only at hs2 hw2; subst hs2
  obtain ⟨hS2, hg2, hnm, ht2⟩ := allocW_stage hw2 hS1
  have hP2 := hP1.fr (allocW_mfr hw2)
  have hA2 := allocW_afr hw2 hA1
  generalize hNM : r2.headD 0 = nm at h hnm
  have h13 : (13 : Word).toNat = 13 := rfl
  rw [h13] at ht2
  have hI2 := hS2.2.1
  have hnmb : nm.toNat + 13 < 2 ^ 64 := by have := hS2.2.2.2.1; omega
  have hp13 : p0 + 13 ≤ nm.toNat := by
    obtain ⟨_, hw12⟩ := decTM_get hsrc 12 (by omega)
    have := (truncM_iw_get hw12).1
    have := hg.1; have := hg1.1; omega
  have hmw : (UInt64.ofNat p0 : Word).toNat + 9 ≤ nm.toNat := by rw [hp0T]; omega
  -- the copy loop
  obtain ⟨m3, c3, h⟩ := of_K h rfl
  obtain ⟨g1, g2⟩ := ncpW_words nm _ (by omega) hmw (k + 1) _ _ 0 c3 (by simp)
  have hS3 := ncpW_ind nm (UInt64.ofNat p0) (by omega) (fun m'' => StageR dn vis fe m'' a1)
    (fun _ _ _ h _ => h.set_iw _ _) (k + 1) _ _ 0 c3 (by simp) hS2
  have hg3 := ncpW_ind nm (UInt64.ofNat p0) (by omega) (fun m'' => IWGrow s1.mem m'')
    (fun _ x _ h hx => h.set_iw _ _ (by omega)) (k + 1) _ _ 0 c3 (by simp) hg2
  have hP3 := ncpW_ind nm (UInt64.ofNat p0) (by omega) (fun m'' => MFr [] [] s2.mem m'')
    (fun _ x _ h _ => h.trans (MFr.set_iw _ _ _)) (k + 1) _ _ 0 c3 (by simp) (MFr.refl _ _ _)
  have hA3 := ncpW_ind nm (UInt64.ofNat p0) (by omega) (fun m'' => AFr s2.mem m'')
    (fun _ _ _ h _ => h.trans (set64IW_afr _ _ _)) (k + 1) _ _ 0 c3 (by simp) (AFr.refl _) hA2
  have ht3 := ncpW_ind nm (UInt64.ofNat p0) (by omega) (fun m'' => iwTop m'' = iwTop s2.mem)
    (fun _ x _ h _ => by rw [cnsTop_set]; exact h) (k + 1) _ _ 0 c3 (by simp) rfl
  -- the record's tail and the result slot
  by_cases hb : ¬ ((nm + 9).toNat < (m3.arr64 IW).size ∧ (nm + 10).toNat < (m3.arr64 IW).size ∧
      (nm + 11).toNat < (m3.arr64 IW).size ∧ (nm + 12).toNat < (m3.arr64 IW).size ∧
      (qr + j).toNat < (m3.arr64 IW).size)
  · rw [cnsK3_bad (h := hb)] at h; cases h
  simp only [Decidable.not_not] at hb
  rw [cnsK3_ok (h := hb)] at h
  obtain ⟨b9, b10, b11, b12, bq⟩ := hb
  simp only [wrTail] at h
  generalize hA : m3.set64 IW (nm + 9) (r1.headD 0) = mA at h
  generalize hB : mA.set64 IW (nm + 10) (r1.tail.headD 0) = mB at h
  generalize hC : mB.set64 IW (nm + 11) (rdW (mB.arr64 IW) (UInt64.ofNat p0 + 11)) = mC at h
  generalize hD : mC.set64 IW (nm + 12) (rdW (mC.arr64 IW) (UInt64.ofNat p0 + 12)) = mD at h
  generalize hE : mD.set64 IW (qr + j) nm = m4 at h
  have hqb := hS.lt64 htop
  have hqj : (qr + j).toNat = qr.toNat + j.toNat := by rw [UInt64.toNat_add]; simp; omega
  have hn9 : (nm + 9).toNat = nm.toNat + 9 := by rw [UInt64.toNat_add]; simp; omega
  have hn10 : (nm + 10).toNat = nm.toNat + 10 := by rw [UInt64.toNat_add]; simp; omega
  have hn11 : (nm + 11).toNat = nm.toNat + 11 := by rw [UInt64.toNat_add]; simp; omega
  have hn12 : (nm + 12).toNat = nm.toNat + 12 := by rw [UInt64.toNat_add]; simp; omega
  have hmt : ∀ t, t < 13 → (UInt64.ofNat p0 + UInt64.ofNat t : Word).toNat = p0 + t := fun t ht => by
    rw [UInt64.toNat_add, hp0T]; simp; omega
  have hgm1 : iwTop m ≤ iwTop s1.mem := hg1.1
  have hqnm : qr.toNat + ml.toNat ≤ nm.toNat := by omega
  -- sizes
  have szA : (mA.arr64 IW).size = (m3.arr64 IW).size := by rw [← hA, size_set64]
  have szB : (mB.arr64 IW).size = (m3.arr64 IW).size := by rw [← hB, size_set64, szA]
  have szC : (mC.arr64 IW).size = (m3.arr64 IW).size := by rw [← hC, size_set64, szB]
  have szD : (mD.arr64 IW).size = (m3.arr64 IW).size := by rw [← hD, size_set64, szC]
  -- the stage relation, growth, tops, memos
  have hS4 : StageR dn vis fe m4 a1 := by
    rw [← hE, ← hD, ← hC, ← hB, ← hA]
    exact ((((hS3.set_iw _ _).set_iw _ _).set_iw _ _).set_iw _ _).set_iw _ _
  have hA4 : AbsOK m4 := by
    rw [← hE, ← hD, ← hC, ← hB, ← hA]
    exact ((((hA3.iw (set64IW_frame _ _ _)).iw (set64IW_frame _ _ _)).iw (set64IW_frame _ _ _)).iw
      (set64IW_frame _ _ _)).iw (set64IW_frame _ _ _)
  have hC4 : StageC dn vis fe env m4 a1 := hC1.of_pstep hS4 hA4 (PStep.refl hC1.check.state)
  have hgD : IWGrow s1.mem mD := by
    rw [← hD, ← hC, ← hB, ← hA]
    exact (((hg3.set_iw _ _ (by omega)).set_iw _ _ (by omega)).set_iw _ _ (by omega)).set_iw _ _ (by omega)
  have hg4 : IWGrow mb m4 := by
    rw [← hE]; exact ((hg.trans hg1).trans hgD).set_iw _ _ (by omega)
  have hFr : FrX (qr.toNat + j.toNat) m m4 := by
    rw [← hE]; exact (FrX.trans_grow (FrX.of_grow hg1) hgD).set _ _ hqj
  have ht4 : iwTop m4 = iwTop s2.mem := by
    rw [← hE, ← hD, ← hC, ← hB, ← hA]; simp only [cnsTop_set]; exact ht3
  have hP4 : RcMR m4 := by
    rw [← hE, ← hD, ← hC, ← hB, ← hA]
    exact hP2.fr (hP3.trans ((((MFr.set_iw _ _ _).trans (MFr.set_iw _ _ _)).trans (MFr.set_iw _ _ _)).trans
      ((MFr.set_iw _ _ _).trans (MFr.set_iw _ _ _))))
  -- the record's words
  have hsrcw : ∀ t, t < 13 → ∀ v, (iwA (truncM mb))[p0 + t]? = some v →
      rdW (s2.mem.arr64 IW) (UInt64.ofNat p0 + UInt64.ofNat t) = v := by
    intro t ht v hv
    obtain ⟨hlt, hv'⟩ := truncM_iw_get hv
    have e : (s2.mem.arr64 IW)[p0 + t]? = (mb.arr64 IW)[p0 + t]? := ((hg.trans hg1).trans hg2).2.2.1 _ hlt
    simp only [rdW, hmt t ht, e]; simp only [iwA] at hv'; rw [hv']; rfl
  have hlow : ∀ i, i < nm.toNat → (mC.arr64 IW)[i]? = (s2.mem.arr64 IW)[i]? := by
    intro i hi
    rw [← hC, set64IW_get, ite_eq_right (by omega), ← hB, set64IW_get, ite_eq_right (by omega), ← hA, set64IW_get,
      ite_eq_right (by omega)]
    exact g1 i (by omega)
  have hrdC : ∀ t, t < 13 → rdW (mC.arr64 IW) (UInt64.ofNat p0 + UInt64.ofNat t) =
      rdW (s2.mem.arr64 IW) (UInt64.ofNat p0 + UInt64.ofNat t) := by
    intro t ht; simp only [rdW, hmt t ht]; rw [hlow (p0 + t) (by omega)]
  have hrdB : ∀ t, t < 13 → rdW (mB.arr64 IW) (UInt64.ofNat p0 + UInt64.ofNat t) =
      rdW (s2.mem.arr64 IW) (UInt64.ofNat p0 + UInt64.ofNat t) := by
    intro t ht
    rw [← hrdC t ht, ← hC, rdW_set_ne (by rw [hmt t ht, hn11]; omega)]
  have hwords : ∀ k, k < 13 → k ≠ 9 → k ≠ 10 →
      (m4.arr64 IW)[nm.toNat + k]? = (iwA (truncM mb))[p0 + k]? := by
    intro k hk h9 h10
    obtain ⟨v, hv⟩ := decTM_get hsrc k hk
    rw [hv, ← hE, set64IW_get, ite_eq_right (by omega)]
    by_cases k12 : k = 12
    · subst k12
      rw [← hD, set64IW_get, ite_eq_left ⟨by omega, by rw [szC]; omega⟩]
      rw [show (12 : Word) = UInt64.ofNat 12 from rfl, hrdC 12 (by omega), hsrcw 12 (by omega) v hv]
    rw [← hD, set64IW_get, ite_eq_right (by omega)]
    by_cases k11 : k = 11
    · subst k11
      rw [← hC, set64IW_get, ite_eq_left ⟨by omega, by rw [szB]; omega⟩]
      rw [show (11 : Word) = UInt64.ofNat 11 from rfl, hrdB 11 (by omega), hsrcw 11 (by omega) v hv]
    rw [← hC, set64IW_get, ite_eq_right (by omega), ← hB, set64IW_get, ite_eq_right (by omega), ← hA, set64IW_get,
      ite_eq_right (by omega), g2 k (by simp) (by omega), hsrcw k hk v hv]
  have hw9 : iwN m4 (nm.toNat + 9) = some (r1.headD 0).toNat := by
    simp only [iwN, nat?, iwA]
    rw [← hE, set64IW_get, ite_eq_right (by omega), ← hD, set64IW_get, ite_eq_right (by omega), ← hC, set64IW_get,
      ite_eq_right (by omega), ← hB, set64IW_get, ite_eq_right (by omega), ← hA, set64IW_get, ite_eq_left ⟨by omega, by rw [hn9] at b9; exact b9⟩]
    rfl
  have hw10 : iwN m4 (nm.toNat + 10) = some (r1.tail.headD 0).toNat := by
    simp only [iwN, nat?, iwA]
    rw [← hE, set64IW_get, ite_eq_right (by omega), ← hD, set64IW_get, ite_eq_right (by omega), ← hC, set64IW_get,
      ite_eq_right (by omega), ← hB, set64IW_get, ite_eq_left ⟨by omega, by rw [szA]; rw [hn10] at b10; exact b10⟩]
    rfl
  have hFr1 : FrX (qr.toNat + j.toNat) s1.mem m4 := by
    rw [← hE]; exact (FrX.trans_grow (FrX.of_grow (IWGrow.refl _)) hgD).set _ _ hqj
  have hfr' : (r1.tail.headD 0).toNat = 0 ∨ qr.toNat + ml.toNat ≤ (r1.headD 0).toNat := by
    rcases hfr with h0 | h0
    · left; rw [h0]; rfl
    · right; omega
  have hes4 : decNL m4 (r1.headD 0).toNat (r1.tail.headD 0).toNat = some pse := by
    rw [decNL_frX hFr1 hes.2 (by omega)]
    exact hpse
  have hnew : CnsRec mb (CnsSrc mb mo ml) (qr.toNat + ml.toNat) m4 nm.toNat { ms[j.toNat]'(by omega) with nfs := es } :=
    ⟨p0, _, _, _, pse, hsrcmb, ⟨j.toNat, hjl, hp0m⟩, hqnm, by rw [ht4]; omega, hwords, hw9, hw10, hes4,
      by have := hes.2; rw [ht4]; omega, hfr', hpseb, rfl⟩
  -- the result slot
  have hws4 : decNL m4 qr.toNat (j + 1).toNat = some (ws ++ [nm.toNat]) := by
    rw [hj1, decNL_snoc, decNL_frX hFr (by omega) (by right; right; omega), hws]
    have : iwN m4 (qr.toNat + j.toNat) = some nm.toNat := by
      simp only [iwN, nat?, iwA]
      rw [← hE, set64IW_get, ite_eq_left ⟨hqj.symm, by rw [szD]; rw [hqj] at bq; exact bq⟩]
      rfl
    simp [this]
  have hacc4 : FA2 (CnsRec mb (CnsSrc mb mo ml) (qr.toNat + ml.toNat) m4) (ws ++ [nm.toNat])
      (acc ++ [{ ms[j.toNat]'(by omega) with nfs := es }]) :=
    FA2.snoc (FA2.imp (fun _ _ hr => CnsRec.frame hr hFr (by omega)) hacc) hnew
  have hje1 : j + 1 ≤ ml := UInt64.le_iff_toNat_le.mpr (by omega)
  obtain ⟨rest, a', run', hC', hg', ht', hP', hA', ws', hws', hacc'⟩ := ih (by omega) m4 m' a1 (j + 1) _ _
    MsP' h hC4 hA4 hg4 (by rw [ht4]; omega) hP4 hje1 hws4 hacc4
    (ConRon.Bridge.Inductives.dShape_ext c1.ext _ _ hsh) (denoteEList_ext c1.ext _ _ hftP)
    (ConRon.Bridge.Inductives.dCtorNf_ext.list c1.ext _ _ htblP)
    (by rw [hj1]; exact ConRon.Bridge.Inductives.dMajor_ext.list c1.ext _ _ hmsP')
    (fun N hN => hMs N (List.mem_cons_of_mem _ hN))
  refine ⟨{ ms[j.toNat]'(by omega) with nfs := es } :: rest, a', ?_, hC', hg', ht', hP', hA', ws', hws',
    by simpa using hacc'⟩
  rw [List.drop_eq_getElem_cons (by omega), ConRon.Arena.classesNfs]
  rw [hj1] at run'
  simp only [StateT.run_bind, run1, except_ok_bind, run']
  rfl

end loop

/-- **`classes_nfs` refines `classesNfs`** under `StageC` (the knot's core calls; the inputs'
denotations and scoping as con-ron's `classesNfs_spec` asks). -/
@[refines ConRon.Arena.classesNfs]
theorem classesNfs_refinesC {p : Prog} (hkp : KnotStageProg p) {env : ConLeche.Env}
    (henv : ConLeche.EnvWF env) (P : CnsProg p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis q fto ftl tblo tbll mo ml : Word)
    (bs : BlockShape) (formerTys : List EIdx) (tbl : List NestCtorNf) (ms : List TargetMajor)
    (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem) (hbs : BSOK s₀.mem q.toNat bs)
    (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys) (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem)
    (htbl : PSlR decNCN tbl tblo tbll s₀.mem) (hms : PSlR decTM ms mo ml s₀.mem) (hP : RcMR s₀.mem)
    {pP : ConLeche.BlockShape} {formerTysP : List ConLeche.Expr} {tblP : List ConLeche.NestCtorNf}
    {MsP : List ConLeche.TargetMajor} (hsh : dShape a₀.store bs = some pP)
    (hftP : Frontend.denoteEList a₀.store formerTys = some formerTysP)
    (htblP : tbl.mapM (dCtorNf a₀.store) = some tblP) (hmsP : ms.mapM (dMajor a₀.store) = some MsP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "classes_nfs" [vis, q, fto, ftl, tblo, tbll, mo, ml]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classesNfs V fe bs formerTys tbl ms) a₀ ∧
      PSlR decTM (AM.res (ConRon.Arena.classesNfs V fe bs formerTys tbl ms) a₀) (r.headD 0) (r.tail.headD 0) s'.mem ∧
      StageC dn vis fe env s'.mem (AM.st (ConRon.Arena.classesNfs V fe bs formerTys tbl ms) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ RcMR s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  rcases n with _ | n
  · exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  refine triple_post (cnfs_spec p P.cns n s₀ vis q fto ftl tblo tbll mo ml) ?_
  rintro r s' ⟨hl, hm⟩
  rw [cnfsW_eq] at hm
  obtain ⟨⟨r0, m0⟩, c0, hm⟩ := of_K hm rfl
  rw [cnfsK1_some] at hm
  obtain ⟨mF, c1, hm⟩ := of_K hm rfl
  rw [cnfsK2_some] at hm
  simp only [Option.some.injEq, Prod.mk.injEq] at hm; obtain ⟨rfl, hmF⟩ := hm
  obtain ⟨s0, rfl, -, hw0⟩ := triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩) (iwAlloc_specW p P.ha n _ ml) c0
  obtain ⟨hS0, hg0, hq0, ht0⟩ := allocW_stage hw0 hC.stage
  have hA0 := allocW_afr hw0 hA
  obtain ⟨rest, a', run, hSF, hgF, htF, hPF, hAF, ws', hws', hacc'⟩ := cnsW_okC hkp henv P dn fe vis q fto ftl
    tblo tbll mo ml (r0.headD 0) bs formerTys tbl ms s₀.mem hq0 hms htbl hbs hft hftb hformer (n + 1)
    (by omega) s0.mem mF a₀ 0 [] [] MsP c1 (hC.of_pstep hS0 hA0 (PStep.refl hC.check.state)) hA0 hg0
    (by omega) (hP.fr (allocW_mfr hw0)) UInt64.zero_le (by simp [decNL]) FA2.nil hsh hftP htblP
    (by simpa using hmsP) hMs
  simp only [UInt64.toNat_zero, List.drop_zero, List.nil_append] at run hacc'
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  rw [← hmF]
  refine ⟨hl, hok, ?_, by rw [hst]; exact hSF, hgF, hPF, hAF⟩
  rw [hres]
  refine ⟨?_, by simpa using htF⟩
  show decPL (truncM mF) (decTM (truncM mF)) _ _ = some rest
  simp only [List.headD_cons, List.tail_cons]
  rw [decPL_eq_bind, show decNL (truncM mF) (r0.headD 0).toNat ml.toNat = some ws' from decNL_decB hws' htF]
  exact cnsRec_mapM hgF hacc'

end L.Ind
