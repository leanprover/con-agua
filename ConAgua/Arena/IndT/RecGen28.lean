import ConAgua.Verdict.IndBTmn
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.IndT.RecGen28Models

/-!
# `classes_nfs`' loop refinement

`classes_nfs` has nested loops, so its model (`RecGen28Models.lean`) is written by hand (the generator models one loop per
function), in the shape of a `unified` model: `cnfsE` and its loop `cnsE` (`Except`: an error of
class `≠ 0` is the model's), `target_major_nfs` through its run (`callE`), `iw_alloc` and the
copy loop (`ncpW`, `RecGenSpec/DecB`) outside the verdict closure (class `0` on failure, as are the
stores out of bounds and the fuel). `cnfsE_spec` is its `unified` spec. `cns_ref` refines the loop
against con-ron's `classesNfs` for both outcomes, from `StageC` and the inputs' denotations
con-ron's `classesNfs_spec` asks; `cnfs_ref` (`IndT/GenRec1`) is the function's refinement.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dShape dCtors dCtorNf dMajor)
open ConRon.Bridge (CoreStep denote_ext denoteEList_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## The loop's refinement -/

/-- What `classes_nfs`' loop gives besides the twin's records `rest` (from cursor `j`, the records
`acc` before it; the classes' slice `(mo, ml)` and the inputs in `mb`, the result slots at `qr`):
the stage, the growth from `mb`, the result slots below the top, the memos, `AbsOK`, and the
slots' records, `acc ++ rest`. -/
structure CnsPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (mb : Mem) (mo ml qr : Word) (acc : List TargetMajor) (m' : Mem) (rest : List TargetMajor)
    (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow mb m'
  top : qr.toNat + ml.toNat ≤ iwTop m'
  rc : RcMR m'
  abs : AbsOK m'
  recs : ∃ ws', decNL m' qr.toNat ml.toNat = some ws' ∧
    FA2 (CnsRec mb (CnsSrc mb mo ml) (qr.toNat + ml.toNat) m') ws' (acc ++ rest)

section loop
variable {p : Prog} (hkp : KnotStageProg p) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (P : CnsProg p) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
  (vis q fto ftl tblo tbll mo ml qr : Word) (bs : BlockShape) (formerTys : List EIdx)
  (tbl : List NestCtorNf) (ms : List TargetMajor) (mb : Mem)
  {pP : ConLeche.BlockShape} {formerTysP : List ConLeche.Expr} {tblP : List ConLeche.NestCtorNf}
include hkp henv P

/-- **`classes_nfs`' loop refines `classesNfs`, both outcomes** (twin side: con-ron's `classesNfs_spec`'s
list induction): per class `target_major_nfs` (`tmn_ref` through its run; on an ok run con-ron's
`targetMajorNfs_spec` for the extension), `iw_alloc` and the record's copy (L only, class `0` on
failure). -/
theorem cns_ref (hq : qr.toNat = iwTop mb) (hms : PSlR decTM ms mo ml mb) (htbl : PSlR decNCN tbl tblo tbll mb)
    (hbs : BSOK mb q.toNat bs) (hft : decHL mb fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop mb) (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (k : Nat) (hk : k ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (j : Word) (acc : List TargetMajor) (ws : List Nat)
      (MsP : List ConLeche.TargetMajor),
    StageC dn vis fe env m a → AbsOK m → IWGrow mb m → qr.toNat + ml.toNat ≤ iwTop m → RcMR m → j ≤ ml →
    decNL m qr.toNat j.toNat = some ws → FA2 (CnsRec mb (CnsSrc mb mo ml) (qr.toNat + ml.toNat) m) ws acc →
    dShape a.store bs = some pP → Frontend.denoteEList a.store formerTys = some formerTysP →
    tbl.mapM (dCtorNf a.store) = some tblP → (ms.drop j.toNat).mapM (dMajor a.store) = some MsP →
    (∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) →
    RefE (VerdictCtx p) (cnsE p k m vis q fto ftl tblo tbll mo ml qr j)
      (ConRon.Arena.classesNfs V fe bs formerTys tbl (ms.drop j.toNat)) a
      (fun m' rest a' => CnsPost dn vis fe env mb mo ml qr acc m' rest a') := by
  have hms0 : decPL (truncM mb) (decTM (truncM mb)) mo.toNat ml.toNat = some ms := hms.dec
  have hlen := decPL_length _ hms0
  obtain ⟨tps, -, htps, hmap⟩ := sumDecNL_of_decB htbl.dec
  have htpb : PtrsB mb tps tbl := ptrsB_of_mapM hmap
  induction k with
  | zero => intros; rw [cnsE_zero]; exact RefE.of_cls0 (by simp)
  | succ k ih =>
  intro m a j acc ws MsP hC hA hg htop hP hje hws hacc hsh hftP htblP hmsP hMs
  have hS := hC.stage
  have hsz := hS.iw.iwSize
  have hjm : j.toNat ≤ ml.toNat := UInt64.le_iff_toNat_le.mp hje
  have hT := (rdW (m.arr64 CTL) 200).toNat_lt
  by_cases hj : ¬ j < ml
  · rw [cnsE_exit (h := hj)]
    have h1 : ml.toNat ≤ j.toNat := by simpa [UInt64.lt_iff_toNat_lt] using hj
    have hjeq : j.toNat = ml.toNat := by omega
    have : ms.drop j.toNat = [] := List.drop_eq_nil_of_le (by omega)
    rw [this]
    exact RefE.ret rfl ⟨hC, hg, htop, hP, hA, ws, by rw [← hjeq]; exact hws, by simpa using hacc⟩
  simp only [Decidable.not_not] at hj
  have hjl : j.toNat < ml.toNat := UInt64.lt_iff_toNat_lt.mp hj
  have hml := ml.toNat_lt
  have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  -- the class `j`
  obtain ⟨p0, hp0, hsrc⟩ := decPL_getH (truncM mb) hms0 j.toNat hjl
  obtain ⟨hp0t, hp0m⟩ := rec2IwN_trunc hp0
  have hp0m' : iwN m (mo.toNat + j.toNat) = some p0 := by
    simp only [iwN, nat?, iwA] at hp0m ⊢; rw [hg.iwGet _ hp0t]; exact hp0m
  obtain ⟨hrd, hp0b⟩ := iwN_rdW_at (w := mo) (k := j.toNat) hp0m' hsz
  rw [show mo + UInt64.ofNat j.toNat = mo + j by simp] at hrd
  rw [cnsE_step (h := hj), hrd]
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
  rw [List.drop_eq_getElem_cons (by omega), ConRon.Arena.classesNfs]
  have hsT := tmnE_spec p P.tmn k ⟨m, Locals.init []⟩ vis q fto ftl
    (rdW (m.arr64 IW) (UInt64.ofNat p0 + 11)) (rdW (m.arr64 IW) (UInt64.ofNat p0 + 12))
    (rdW (m.arr64 IW) (UInt64.ofNat p0 + 1)) (rdW (m.arr64 IW) (UInt64.ofNat p0 + 2))
    (rdW (m.arr64 IW) (UInt64.ofNat p0 + 3)) (rdW (m.arr64 IW) (UInt64.ofNat p0 + 6))
    (rdW (m.arr64 IW) (UInt64.ofNat p0 + 7)) tblo tbll
  have hT := tmn_ref hkp henv k (by omega) hC hA
    (hbs.grow hg) hlH (by rw [decHL_grow hg hftb]; exact hft) (by have := hg.iw; omega) hpfS hdsS hctB hctb
    (htbl.grow (fun q => decNCN_mono q) hg) hP hsh hftP hpfvsP (by rw [hlD]; exact hlvls) hdsP hctorsP
    htblP hformer hscp
  rw [hlD] at hT
  refine RefE.bindRun (s₀ := ⟨m, Locals.init []⟩) (fun _ => rfl) hsT (fun hG => hG.nv) id hT
    fun r1 s1 es a1 c1 _ run1 hR1 => ?_
  rw [cnsEK1_ok]
  obtain ⟨hes, hC1, hg1, hP1, hA1, hptrs⟩ := hR1
  obtain ⟨hfr, pse, hpse, hpseb⟩ := hptrs mb tps (by rw [decNL_grow hg htbl.bound]; exact htps) htpb
  dsimp only at hes hC1 hg1 hP1 hA1 hfr hpse
  obtain ⟨c1, -⟩ := ConRon.Bridge.Inductives.targetMajorNfs_spec fe (ConRon.Bridge.CoreSpec.of_core rfl)
    henv bs pP formerTys _ formerTysP _ _ _ _ _ _ _ hformer hscp tbl tblP a a1 es hC.check
    ⟨hsh, hftP, hpfvsP, hlvls, hdsP, hctorsP, htblP⟩ run1
  have hS1 := hC1.stage
  -- `iw_alloc(13)`
  cases c2 : callW p k "iw_alloc" [13] s1.mem with
  | none => rw [cnsEK2_none]; exact RefE.of_cls0 (by simp)
  | some q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [cnsEK2_some]
  obtain ⟨s2, hs2, -, hw2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩) (iwAlloc_specW p P.ha k _ 13) c2
  simp only at hs2 hw2; subst hs2
  obtain ⟨hS2, hg2, hnm, ht2⟩ := allocW_stage hw2 hS1
  have hP2 := hP1.fr (allocW_mfr hw2)
  have hA2 := allocW_afr hw2 hA1
  generalize hNM : r2.headD 0 = nm at hnm ⊢
  have h13 : (13 : Word).toNat = 13 := rfl
  rw [h13] at ht2
  have hI2 := hS2.iw.iw
  have hnmb : nm.toNat + 13 < 2 ^ 64 := by have := hS2.iw.iwSize; omega
  have hp13 : p0 + 13 ≤ nm.toNat := by
    obtain ⟨_, hw12⟩ := decTM_get hsrc 12 (by omega)
    have := (truncM_iw_get hw12).1
    have := hg.iw; have := hg1.iw; omega
  have hmw : (UInt64.ofNat p0 : Word).toNat + 9 ≤ nm.toNat := by rw [hp0T]; omega
  -- the copy loop
  cases c3 : ncpW (k + 1) s2.mem nm (UInt64.ofNat p0) 0 with
  | none => rw [cnsEK3_none]; exact RefE.of_cls0 (by simp)
  | some m3 =>
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
  · rw [cnsEK3_bad (h := hb)]; exact RefE.of_cls0 (by simp)
  simp only [Decidable.not_not] at hb
  rw [cnsEK3_ok (h := hb)]
  obtain ⟨b9, b10, b11, b12, bq⟩ := hb
  simp only [wrTail]
  generalize hA : m3.set64 IW (nm + 9) (r1.headD 0) = mA
  generalize hB : mA.set64 IW (nm + 10) (r1.tail.headD 0) = mB
  generalize hC : mB.set64 IW (nm + 11) (rdW (mB.arr64 IW) (UInt64.ofNat p0 + 11)) = mC
  generalize hD : mC.set64 IW (nm + 12) (rdW (mC.arr64 IW) (UInt64.ofNat p0 + 12)) = mD
  generalize hE : mD.set64 IW (qr + j) nm = m4
  have hqb := hS.lt64 htop
  have hqj : (qr + j).toNat = qr.toNat + j.toNat := by rw [UInt64.toNat_add]; simp; omega
  have hn9 : (nm + 9).toNat = nm.toNat + 9 := by rw [UInt64.toNat_add]; simp; omega
  have hn10 : (nm + 10).toNat = nm.toNat + 10 := by rw [UInt64.toNat_add]; simp; omega
  have hn11 : (nm + 11).toNat = nm.toNat + 11 := by rw [UInt64.toNat_add]; simp; omega
  have hn12 : (nm + 12).toNat = nm.toNat + 12 := by rw [UInt64.toNat_add]; simp; omega
  have hmt : ∀ t, t < 13 → (UInt64.ofNat p0 + UInt64.ofNat t : Word).toNat = p0 + t := fun t ht => by
    rw [UInt64.toNat_add, hp0T]; simp; omega
  have hgm1 : iwTop m ≤ iwTop s1.mem := hg1.iw
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
    have e : (s2.mem.arr64 IW)[p0 + t]? = (mb.arr64 IW)[p0 + t]? := ((hg.trans hg1).trans hg2).iwGet _ hlt
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
  have := ih (by omega) m4 a1 (j + 1) _ _ MsP' hC4 hA4 hg4 (by rw [ht4]; omega) hP4 hje1 hws4 hacc4
    (ConRon.Bridge.Inductives.dShape_ext c1.ext _ _ hsh) (denoteEList_ext c1.ext _ _ hftP)
    (ConRon.Bridge.Inductives.dCtorNf_ext.list c1.ext _ _ htblP)
    (by rw [hj1]; exact ConRon.Bridge.Inductives.dMajor_ext.list c1.ext _ _ hmsP')
    (fun N hN => hMs N (List.mem_cons_of_mem _ hN))
  rw [hj1] at this
  exact RefE.tailMap_pure (k := id) (f := id) (fun _ => rfl) (fun _ => rfl) id
    (fun _ _ _ hR => ⟨hR.stage, hR.grow, hR.top, hR.rc, hR.abs, by simpa using hR.recs⟩) this

end loop

end L.Ind
end
