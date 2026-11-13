module

public import ConAgua.Arena.RecGenSpec.DecCIIndCv
import ConAgua.Arena.RecLayout.CapsDec
public import ConAgua.Verdict.PosFt
public import ConAgua.Arena.IndRealIlpL
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
import ConAgua.Arena.RefWalk
import ConAgua.Arena.IlpRdReal
import ConAgua.Arena.RecClassSpec.IhW
import ConAgua.Arena.RecGenSpec.CkcW
import ConAgua.Arena.RecClassSpec.MjProg
import ConAgua.Arena.IndInstallSpec.DomsW
import ConRon.Bridge.Inductives.Positivity
import ConRon.Bridge.Inductives.GenRec
import all ConAgua.Arena.RecGen
public import ConAgua.Arena.IndPartsSpec.PartsConsPL
public import ConRon.Bridge.Inductives.RecCheck
import ConAgua.Arena.RecGenSpec.Set64
import ConAgua.Arena.IndPosSpec.EnvFindWHit

@[expose] public section

/-!
# `class_former_ty`, `gen_rec_check_former_tys_c`: one model and one refinement each, both outcomes

`class_former_ty` reads an outside class's former through `family_telescope` (whose errors are the
core's), so `gen_rec_check_former_tys_c` is inside the verdict closure: `cft_ref` refines
`classFormerTy .verified` (`family_telescope` by `ft_ref`, `inst_lp_fast` by its real reading),
`gfc_ref` the loop against `ms.mapM (classFormerTy fe cvTas)`.
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

set_option experimental.vcgen true in
/-- **`class_former_ty`'s unified model**: `intern_bvar`, `env_find`, `er_to_iw`, `inst_lp_fast`
lifted, `family_telescope` through its call. -/
l_model cftE_spec (p : Prog) (hP : CftProg p)
  fns [hP.cft ↦ cftE]
  specs [callW_spec p n "intern_bvar", callW_spec p n "env_find", callW_spec p n "er_to_iw",
    callW_spec p n "inst_lp_fast"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

set_option experimental.vcgen true in
/-- **`gen_rec_check_former_tys_c`'s unified model**: `iw_alloc` lifted, `class_former_ty` through
its call. -/
l_model gfcE_spec (p : Prog) (hP : CftProg p)
  (hg : p.lookup "gen_rec_check_former_tys_c" = some genRecCheckFormerTysC)
  fns [hg ↦ gfcE]
  specs [callW_spec p n "iw_alloc"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `class_former_ty` gives besides the twin's type `x` (from `m`, `a`): the stage, the pools
grown, `AbsOK`, the type's word. -/
structure CftPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (a : AState) (v : Word × Mem) (x : EIdx) (a' : AState) : Prop where
  stage : StageC dn vis fe env v.2 a'
  grow : IWGrow m v.2
  abs : AbsOK v.2
  dec : decW0E v.2 [v.1] x
  core : ConRon.Bridge.CoreStep env fe a a'

section cft
variable {p : Prog} (hq : KnotStageProg p) (hP : CftProg p) (hF : FtProg p) (hIlpf : IlpfF p)
  {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  (henv : ConLeche.EnvWF env)

/-- The ok half's facts before the twin's core step is known (`cft_ref`'s inner post). -/
structure CftQ (vis : Word) (fe : IFEnv) (m : Mem) (v : Word × Mem) (x : EIdx) (a' : AState) : Prop where
  stage : StageR vis fe v.2 a'
  grow : IWGrow m v.2
  abs : AbsOK v.2
  dec : decW0E v.2 [v.1] x

include hq hP hF hIlpf henv in
theorem cft_refQ (k : Nat) (hk : k ≤ 2 ^ 62) {m : Mem} {a : AState} {o l mp : Word}
    {M : TargetMajor} {cvTas : List IConstantVal} {MP : ConLeche.TargetMajor}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hM : DecB (fun m => decTM m mp.toNat) m M) (hcv : decPL m (decCVp m) o.toNat l.toNat = some cvTas)
    (hol : o.toNat + l.toNat < 2 ^ 64) (hMP : ConRon.Bridge.Inductives.dMajor a.store M = some MP) :
    RefE (WtG p) (cftE p k m vis o l mp) (ConRon.Arena.classFormerTy V fe cvTas M) a
      (fun v x a' => CftQ vis fe m v x a') := by
  cases k with
  | zero => rw [cftE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ N =>
  have hS := hC.stage
  have hsz := hS.iw.iwSize
  have hM0 := hM.get (decTM_mono _)
  obtain ⟨kk, hkk, hmem⟩ := decTM_member hM0
  have hrk := iwN_rdW_at (w := mp) (k := 8) hkk hsz
  rw [show UInt64.ofNat 8 = (8 : Word) from rfl] at hrk
  have hlen := decPL_length m hcv
  by_cases hk0 : rdW (m.arr64 IW) (mp + 8) ≠ 0
  · have hk0' : kk ≠ 0 := by intro e; apply hk0; rw [hrk.1, e]; rfl
    have hmem' : M.member = some (kk - 1) := by rw [hmem]; simp [decON, hk0']
    have hkw : rdW (m.arr64 IW) (mp + 8) - 1 = UInt64.ofNat (kk - 1) := by
      rw [hrk.1]; apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hrk.2]; simp; omega),
        UInt64.toNat_ofNat_of_lt' hrk.2, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; have := hrk.2; omega)]
      simp
    by_cases hlt : rdW (m.arr64 IW) (mp + 8) - 1 < l
    · rw [cftE.arm1 _ _ _ _ _ _ _ hk0 hlt]
      rw [hkw] at hlt ⊢
      have hlt' : kk - 1 < l.toNat := by
        have := UInt64.lt_iff_toNat_lt.mp hlt
        rwa [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; have := hrk.2; omega)] at this
      obtain ⟨v, hv, hcvv⟩ := decPL_getH m hcv (kk - 1) hlt'
      have hrv := iwN_rdW_at (w := o) (k := kk - 1) hv hsz
      rw [hrv.1]
      have hv64 := hrv.2
      have hty := decCVp_type (q := UInt64.ofNat v) (by rw [UInt64.toNat_ofNat_of_lt' hv64]; exact hcvv)
      refine RefE.ret (y := (cvTas[kk - 1]'(by omega)).type) (a' := a) ?_ ⟨hS, IWGrow.refl m, hA, ⟨hty.1, hty.2⟩⟩
      simp only [ConRon.Arena.classFormerTy, hmem', List.getElem?_eq_getElem (by omega : kk - 1 < cvTas.length)]
      rfl
    · rw [cftE.arm2 _ _ _ _ _ _ _ hk0 hlt]
      have hge : ¬ kk - 1 < cvTas.length := by
        rw [hkw] at hlt; intro h'; apply hlt
        rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; have := hrk.2; omega)]
        omega
      simp only [ConRon.Arena.classFormerTy, hmem', List.getElem?_eq_none (by omega : cvTas.length ≤ kk - 1)]
      refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r1 m1 h1 => ?_
      obtain ⟨s1, hs1, -, hb⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
        (internBVar_spec p hP.bf hP.bp hP.ib N _ 0) h1
      simp only at hs1 hb
      subst hs1
      by_cases hbig : 4294967296 ≤ r1.headD 0
      · rw [cftE.k_intern_bvar.abort1 _ _ _ hbig]; exact RefE.of_cls0 rfl
      rw [cftE.k_intern_bvar.arm1 _ _ _ hbig]
      obtain ⟨a1, hrun, hS1, hg1⟩ := internBVar_stage hS 0 hb
      refine RefE.ret hrun ⟨hS1, hg1, binternW_afr hb hA, ?_, rfl⟩
      show (r1.headD 0).toNat < 2 ^ 32
      have : ¬ (4294967296 : Word).toNat ≤ (r1.headD 0).toNat :=
        fun x => hbig (UInt64.le_iff_toNat_le.mpr x)
      simpa using this
  · have hk00 : kk = 0 := by
      have := congrArg UInt64.toNat ((show rdW (m.arr64 IW) (mp + 8) = 0 by simpa using hk0).symm.trans hrk.1)
      rw [UInt64.toNat_ofNat_of_lt' hrk.2] at this; exact this.symm
    rw [cftE.arm3 _ _ _ _ _ _ _ (by simpa using hk0)]
    have hmem' : M.member = none := by rw [hmem, hk00]; rfl
    obtain ⟨wi, hwi, hwiH, hwiE⟩ := iwH_rdW_at (w := mp) (k := 0) (by simpa using decTM_ind hM0) hsz
    rw [show mp + UInt64.ofNat 0 = mp by simp] at hwi
    rw [hwi]
    have hE := hS.check.env
    simp only [ConRon.Arena.classFormerTy, hmem']
    refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r1 m1 h1 => ?_
    obtain ⟨s1, rfl, hs1m, -, hr1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (envFind_spec p hP.rowGet hP.baseGet hP.find N _ vis wi) h1
    simp only at hs1m hr1
    rw [hs1m]; subst hr1
    by_cases hf0 : (findRes m vis wi).headD 0 = 0
    · rw [cftE.k_env_find.abort1 _ _ _ _ _ _ hf0]; exact RefE.of_cls0 rfl
    obtain ⟨hfind, ci, hci⟩ := findRes_hit hE hwiH hf0
    generalize hqq : (findRes m vis wi).tail.headD 0 = q at hci hfind
    by_cases h3 : erRd m q ≠ 3
    · rw [cftE.k_env_find.abort2 _ _ _ _ _ _ hf0 (by rw [hqq]; exact h3)]; exact RefE.of_cls0 rfl
    rw [cftE.k_env_find.arm1 _ _ _ _ _ _ hf0 (by rw [hqq]; exact (Decidable.not_not.mp h3 : erRd m q = 3)), hqq]
    have hk3 : nat? (erecP m) q.toNat = some 3 := by
      obtain ⟨w, hw⟩ := decCI_rd hci
      have h3' : erRd m q = 3 := Decidable.not_not.mp h3
      rw [(erRd_of_erecP hw).1] at h3'
      simp [nat?, hw, h3']
    obtain ⟨cv, caps, rfl, hcaps⟩ := decCI_kind3 hci hk3
    have hfci : fe.find? M.ind = some (.indInfo cv caps) := by rw [← hwiE, hfind, hci]
    rw [hfci]
    have hcvq : decCV (erecP m) (q.toNat + CI.cv.toNat) = some cv := (decCI_indInfo_iff.mp hci).2.1
    obtain ⟨v16, hv16⟩ := decCI_indInfo_word hci
    have hq64 := L.Arena.erecP_lt64 hv16
    have := CI.indCaps_ge
    have e1 : (q + 1).toNat = q.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have e5 : (q + 5).toNat = q.toNat + 5 := by rw [UInt64.toNat_add]; simp; omega
    -- the twin's family and its denotation
    obtain ⟨hindP, -⟩ := ConRon.Bridge.Inductives.dMajor_inv hMP
    obtain ⟨cc, hcc, he⟩ := ConRon.Bridge.Inductives.find_some_rel hC.check.ienv hindP hfci
    obtain ⟨cvP, capsP, hcvP, hcapsP, rfl⟩ := ConRon.Bridge.Inductives.denoteCI_indInfo_inv hcc
    have hws : ConLeche.Expr.WScoped 0 cvP.type :=
      ConLeche.Expr.WScoped.of_not_hasFvar (henv.consts _ (ConLeche.Env.find?_mem he)).1
    have hcvB : DecB (fun m => decCVp m (q + 1).toNat) m cv := by
      show decCV (erA (truncM m)) _ = _
      rw [truncM_erA, e1]; exact hcvq
    have hFT := ft_ref hq hF henv N (by omega) (cvq := q + CI.cv) (capsq := q + CI.indCaps) hC hA hcvB
      (by rw [e5]; exact hcaps) hcvP hws
    refine RefE.bindRun (s₀ := ⟨m, Locals.init []⟩) (fun _ => rfl) (ftE_spec p hF N _ vis _ _) (fun hG => hG.nv)
      id hFT fun r3 s3 ty a2 _ _ hr3 hP3 => ?_
    dsimp only [cftE.k_family_telescope]
    have hS3 := hP3.stage.stage
    have hg3 := hP3.grow
    generalize s3.mem = m3 at hS3 hg3 hP3 ⊢
    -- the levels
    have hcv3 : decCV (erecP m3) (q.toNat + CI.cv.toNat) = some cv := ArrExt.decCV (IWGrow.ext hg3) hcvq
    obtain ⟨w1, w2, hw1, hw2, hsl⟩ := decCV_slice hcv3
    have e1' : erRd m3 (q + (CI.cv + CV.lpsOff)) = w1 :=
      (erRdOK m3).at _ (CI.cv_add_toNat CV.lpsOff_le) (by rw [← Nat.add_assoc]; exact hw1)
    have e2' : erRd m3 (q + (CI.cv + CV.lpsLen)) = w2 :=
      (erRdOK m3).at _ (CI.cv_add_toNat CV.lpsLen_le) (by rw [← Nat.add_assoc]; exact hw2)
    change RefE _ (cftE.k_er_to_iw p N mp (r3.headD 0) (liftE (callW p N "er_to_iw" [erRd m3 (q + (CI.cv + CV.lpsOff)), erRd m3 (q + (CI.cv + CV.lpsLen))] m3))) _ _ _
    rw [e1', e2']
    refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r4 m4 h4 => ?_
    obtain ⟨s4, hs4, -, h4W⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
      (erToIw_specW p hP.alloc hP.copy hP.eti N _ _ _) h4
    simp only at hs4 h4W
    subst hs4
    obtain ⟨hS4, hg4, hdec4, -, -⟩ := erToIwW_stage h4W hS3 (k := .name) (xs := cv.levelParams) hsl
    have hM4 : decTM s4.mem mp.toNat = some M := hM.stab (decTM_mono _) s4.mem (hg3.trans hg4)
    obtain ⟨wu, hwu, hwuH, hwuE⟩ := iwH_rdW_at (w := mp) (k := 1) (decTM_lvls' hM4) hS4.iw.iwSize
    rw [show UInt64.ofNat 1 = (1 : Word) from rfl] at hwu
    dsimp only [cftE.k_er_to_iw]
    rw [hwu]
    -- `inst_lp_fast`
    refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r5 m5 h5 => ?_
    obtain ⟨x, a5, hrun5, ⟨hS5, hg5, hx5⟩, -, hA5⟩ :=
      IlpRd.realC hIlpf hP3.stage N CWF (r4.headD 0) (r4.tail.headD 0) wu (r3.headD 0)
        cv.levelParams s4.mem m5 a2 r5 hwuH hP3.hw ⟨rfl, erToIwW_iwFr h4W⟩ hS4 hdec4 h5
    rw [CWF_eq, hwuE, hP3.dec] at hrun5
    dsimp only [cftE.k_inst_lp_fast]
    refine RefE.ret hrun5 ⟨hS5, (hg3.trans hg4).trans hg5,
      ((AFr.iw (erToIwW_iwFr h4W)).trans hA5) hP3.abs, hx5⟩

include hq hP hF hIlpf henv in
/-- **`class_former_ty` refines `classFormerTy .verified`, both outcomes** (under `StageC`; the
twin's core step from con-ron's `classFormerTy_spec` on the whole run). -/
theorem cft_ref (k : Nat) (hk : k ≤ 2 ^ 62) {m : Mem} {a : AState} {o l mp : Word}
    {M : TargetMajor} {cvTas : List IConstantVal} {MP : ConLeche.TargetMajor}
    {cvTasP : List ConLeche.ConstantVal}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hM : DecB (fun m => decTM m mp.toNat) m M) (hcv : decPL m (decCVp m) o.toNat l.toNat = some cvTas)
    (hol : o.toNat + l.toNat < 2 ^ 64) (hMP : ConRon.Bridge.Inductives.dMajor a.store M = some MP)
    (hcvP : cvTas.mapM (Frontend.denoteCV a.store) = some cvTasP) :
    RefE (WtG p) (cftE p k m vis o l mp) (ConRon.Arena.classFormerTy V fe cvTas M) a
      (fun v x a' => CftPost dn vis fe env m a v x a') := by
  have h := cft_refQ hq hP hF hIlpf henv k hk hC hA hM hcv hol hMP
  cases hx : cftE p k m vis o l mp with
  | error e => rw [hx] at h; exact h
  | ok v =>
    rw [hx] at h
    obtain ⟨y, a', hrun, hQ⟩ := h
    obtain ⟨c, -⟩ := ConRon.Bridge.Inductives.classFormerTy_spec fe ConRon.Bridge.CoreSpec.of_core henv
      cvTas cvTasP M MP a a' y hC.check ⟨hcvP, hMP⟩ hrun
    exact ⟨y, a', hrun, ⟨hC.of_check hQ.stage hQ.abs c.ok c.ext, hQ.grow, hQ.abs, hQ.dec, c⟩⟩

/-- A twin's trailing `pure`-map, against the same model. -/
theorem RefE.bindPure {α β γ : Type} {G : Prop} {x : Except Err α} {T : AM β} {a : AState}
    {R : α → β → AState → Prop} {R' : α → γ → AState → Prop} {h : β → γ} (H : RefE G x T a R)
    (hR : ∀ v y a', R v y a' → R' v (h y) a') : RefE G x (T >>= fun y => pure (h y)) a R' := by
  cases x with
  | error e => exact RefE.bind_left H
  | ok v =>
    obtain ⟨y, a₁, hr, hQ⟩ := H
    refine ⟨h y, a₁, ?_, hR _ _ _ hQ⟩
    simp only [StateT.run_bind, hr, except_ok_bind]; rfl

include hq hP hF hIlpf henv in
/-- **The loop of `gen_rec_check_former_tys_c` refines `(ms.drop j).mapM (classFormerTy fe cvTas)`**,
both outcomes, from cursor `j`. -/
theorem gfcLoop_ref (s0 : Mem) (co cl mo ml q : Word) (cvTas : List IConstantVal) (ms : List TargetMajor)
    {cvTasP : List ConLeche.ConstantVal} {MsP : List ConLeche.TargetMajor}
    (hcv : PSlR decCVp cvTas co cl s0) (hms : PSlR decTM ms mo ml s0) (hq0 : q.toNat = iwTop s0)
    (k : Nat) (hk : k ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (j : Word) (acc : List EIdx),
    StageC dn vis fe env m a → AbsOK m → IWGrow s0 m → q.toNat + ml.toNat ≤ iwTop m → j ≤ ml →
    decHL m q.toNat j.toNat = some acc →
    cvTas.mapM (Frontend.denoteCV a.store) = some cvTasP →
    ms.mapM (ConRon.Bridge.Inductives.dMajor a.store) = some MsP →
    RefE (WtG p) (gfcE.loop1 p k m vis co cl mo ml q j)
      ((ms.drop j.toNat).mapM (ConRon.Arena.classFormerTy V fe cvTas)) a
      (fun m' rest a' => StageC dn vis fe env m' a' ∧ AbsOK m' ∧ IWGrow s0 m' ∧
        q.toNat + ml.toNat ≤ iwTop m' ∧ decHL m' q.toNat ml.toNat = some (acc ++ rest)) := by
  induction k with
  | zero => intro m a j acc _ _ _ _ _ _ _ _; rw [gfcE.loop1.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ k ih =>
  intro m a j acc hC hA hg ht hjl hacc hcvP hmsP
  have hS := hC.stage
  have hlen : ms.length = ml.toNat := decPL_length _ hms.dec
  have hjl' : j.toNat ≤ ml.toNat := UInt64.le_iff_toNat_le.mp hjl
  by_cases hj : ¬ j < ml
  · rw [gfcE.loop1.arm2 _ _ _ _ _ _ _ _ _ _ hj]
    have hj' : j.toNat = ml.toNat := by
      have : ¬ j.toNat < ml.toNat := fun e => hj (UInt64.lt_iff_toNat_lt.mpr e)
      omega
    refine RefE.ret (y := []) (a' := a) ?_ ⟨hC, hA, hg, ht, by rw [← hj']; simpa using hacc⟩
    rw [List.drop_eq_nil_of_le (by omega)]; rfl
  simp only [Decidable.not_not] at hj
  rw [gfcE.loop1.arm1 _ _ _ _ _ _ _ _ _ _ hj]
  have hjn : j.toNat < ml.toNat := UInt64.lt_iff_toNat_lt.mp hj
  have hI1 := hS.iw.iw
  have hsz := hS.iw.iwSize
  have hgt : iwTop s0 ≤ iwTop m := hg.iw
  -- class `j`
  have hmsm := hms.grow (fun q => decTM_mono q) hg
  obtain ⟨v, hv, hdv⟩ := decPL_getH (truncM m) hmsm.1 j.toNat hjn
  obtain ⟨-, hvm⟩ := L.Ind.iwN_truncM_some hv
  have hrv : (rdW (m.arr64 IW) (mo + j)).toNat = v := rd_iwN hvm (by have := hmsm.2; omega)
  have hM : DecB (fun m' => decTM m' (rdW (m.arr64 IW) (mo + j)).toNat) m (ms[j.toNat]'(by omega)) := by
    show decTM (truncM m) _ = _; rw [hrv]; exact hdv
  have hcvm := hcv.grow (fun q => OMono.decCVp q) hg
  have hdcv : decPL m (decCVp m) co.toNat cl.toNat = some cvTas :=
    hcvm.1.get (OMono.decPL (fun q => OMono.decCVp q) _ _)
  obtain ⟨MP, hMP⟩ : ∃ MP, ConRon.Bridge.Inductives.dMajor a.store (ms[j.toNat]'(by omega)) = some MP := by
    exact L.Arena.mapM_some_mem _ _ hmsP _ (List.getElem_mem _)
  rw [List.drop_eq_getElem_cons (by omega), List.mapM_cons]
  have hR1 := cft_ref hq hP hF hIlpf henv k (by omega) hC hA hM hdcv (by have := hcvm.2; omega) hMP hcvP
  refine RefE.bindRun (s₀ := ⟨m, Locals.init []⟩) (fun _ => gfcE.k_class_former_ty.none ..) (cftE_spec p hP k _ vis _ _ _)
    (fun hG => hG.nv) id hR1 fun r1 s1 x a1 _ _ hrun1 hP1 => ?_
  rw [gfcE.k_class_former_ty.arm1]
  obtain ⟨hC1, hg1, hA1, ⟨hr1, he1⟩, c1⟩ := hP1
  dsimp only at hC1 hg1 hA1 hr1 he1
  generalize s1.mem = m1 at hC1 hg1 hA1 hr1 he1 ⊢
  have hS1 := hC1.stage
  have hI1' := hS1.iw.iw
  have hsz1 := hS1.iw.iwSize
  have hacc1 : decHL m1 q.toNat j.toNat = some acc := by
    rw [decHL_grow hg1 (by omega)]; exact hacc
  have hqj : q.toNat + j.toNat < (m1.arr64 IW).size := by have := hg1.iw; omega
  have hdec := decHL_write m1 q j (r1.headD 0) acc hr1 hsz1 hqj hacc1
  have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hqj' : (q + j).toNat = q.toNat + j.toNat := by rw [UInt64.toNat_add]; simp; omega
  have hA2 : AbsOK (m1.set64 IW (q + j) (r1.headD 0)) := AFr.set64 _ IW (by decide) (by decide) _ _ hA1
  have hC2 : StageC dn vis fe env (m1.set64 IW (q + j) (r1.headD 0)) a1 :=
    hC1.of_pstep (hS1.set_iw _ _) hA2 (ConRon.Bridge.Inductives.PStep.refl hC1.check.state)
  have ih' := ih (by omega) _ a1 (j + 1) (acc ++ [x]) hC2 hA2
    ((hg.trans hg1).set_iw _ _ (by rw [hqj']; have := hg1.iw; omega)) (by rw [L.Ind.iwTop_set_iw]; have := hg1.iw; omega)
    (UInt64.le_iff_toNat_le.mpr (by rw [hj1]; omega)) (by rw [hj1, hdec, ← he1]; rfl)
    (ConRon.Bridge.Inductives.dExt_denoteCV.list c1.ext _ _ hcvP)
    (ConRon.Bridge.Inductives.dMajor_ext.list c1.ext _ _ hmsP)
  rw [hj1] at ih'
  exact RefE.bindPure ih' fun _ _ _ ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, h4, by simpa using h5⟩

include hq hP hF hIlpf henv in
/-- **`gen_rec_check_former_tys_c` refines `ms.mapM (classFormerTy fe cvTas)`, both outcomes**: a
fresh slice (`iw_alloc`), the loop (`gfcLoop_ref`). -/
theorem gfc_ref (_hg : p.lookup "gen_rec_check_former_tys_c" = some genRecCheckFormerTysC)
    (k : Nat) (hk : k ≤ 2 ^ 62) {m : Mem} {a : AState} {co cl mo ml : Word}
    {cvTas : List IConstantVal} {ms : List TargetMajor}
    {cvTasP : List ConLeche.ConstantVal} {MsP : List ConLeche.TargetMajor}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hcv : PSlR decCVp cvTas co cl m) (hms : PSlR decTM ms mo ml m)
    (hcvP : cvTas.mapM (Frontend.denoteCV a.store) = some cvTasP)
    (hmsP : ms.mapM (ConRon.Bridge.Inductives.dMajor a.store) = some MsP) :
    RefE (WtG p) (gfcE p k m vis co cl mo ml) (ms.mapM (ConRon.Arena.classFormerTy V fe cvTas)) a
      (fun v xs a' => StageC dn vis fe env v.2 a' ∧ AbsOK v.2 ∧ IWGrow m v.2 ∧
        decHL v.2 (v.1.headD 0).toNat (v.1.tail.headD 0).toNat = some xs ∧
        (v.1.headD 0).toNat + (v.1.tail.headD 0).toNat ≤ iwTop v.2) := by
  cases k with
  | zero => rw [gfcE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ k =>
  rw [gfcE.arm1]
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r0 m0 c0 => ?_
  rw [gfcE.k_iw_alloc.arm1]
  obtain ⟨s0, hs0, -, hw0⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (iwAlloc_specW p hP.alloc k _ ml) c0
  simp only at hs0 hw0; subst hs0
  obtain ⟨hS0, hg0, hq0, ht0⟩ := allocW_stage hw0 hC.stage
  have hA0 : AbsOK s0.mem := AFr.iw (allocW_iwFrame hw0) hA
  have hC0 : StageC dn vis fe env s0.mem a :=
    hC.of_pstep hS0 hA0 (ConRon.Bridge.Inductives.PStep.refl hC.check.state)
  have hL := gfcLoop_ref hq hP hF hIlpf henv m co cl mo ml (r0.headD 0) cvTas ms hcv hms hq0 (k + 1) (by omega)
    s0.mem a 0 [] hC0 hA0 hg0 (by omega) (UInt64.zero_le) (by simp [decHL, hslice?]) hcvP hmsP
  simp only [UInt64.toNat_zero, List.drop_zero, List.nil_append] at hL
  exact RefE.lastE (K := gfcE.k_loop1 p ml (r0.headD 0)) (f := fun m' => ([r0.headD 0, ml], m'))
    (fun _ => rfl) (fun _ => rfl) id hL fun _ _ _ _ ⟨h1, h2, h3, h4, h5⟩ =>
      ⟨h1, h2, h3, by simpa using h5, by simpa using h4⟩

end cft

end L.Ind

end
