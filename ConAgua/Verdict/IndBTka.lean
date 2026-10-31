import ConAgua.Arena.IndT.RecCheckK53
import ConAgua.Arena.RecCheckSpec.Tka
import ConAgua.Verdict.IndBTcm
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
/-!
# `target_k53_args`: one model and one refinement for both outcomes

`tkaE` (`l_model … unified`): `target_class_match` through its unified model (`tcmE`), the callees
outside the verdict closure (`erase_each`, `sl_eq`, `intern_const`, `mk_app_n_f`, the shape's
member names, `nest_occ`) through their `Option` models. `tka_ref` refines `tkArgs` (the arguments'
part of `targetK53`) for both outcomes; `target_k53_heads`' refinement reads it through the model.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dShape dMajor)
open ConRon.Bridge (CoreStep denote_ext denoteEList_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

-- `cut 3`: the code after the parameter count and the two index slices' `if`s has its own step
-- theorem (`tkaE_spec.tail`), so the step does not run through it once per slice combination
-- (21.5 s -> 4.9 s); `finish (gen := 20)`: the tail's generation depth (the default 8 leaves the
-- early `return 0` after `sl_eq` open)
l_model tkaE_spec (p : Prog) (hL : K53Look p)
  fns [hL.tka ↦ tkaE]
  specs [ee_spec p hL n, slEq_spec p hL.eq n, internConst_spec p hL.cf hL.cp hL.ic n, mknF_spec p hL.ad n,
    blockShapeMemberNames_spec p hL.tmn.tcm.ha hL.tmn.tcm.mnc hL.tmn.tcm.mn n, noF_spec p hL n,
    tcmE_spec p hL.tmn.tcm n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  finish [] gen 20 heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem] cut 3

/-- `tkaE` after the parameter count, the two index slices as `if`s. -/
theorem tkaE_succ (p : Prog) (n : Nat) (m : Mem) (vis q fto ftl Mc ip usp lao lal mao mal : Word) :
    tkaE p (n + 1) m vis q fto ftl Mc ip usp lao lal mao mal =
      tkaE.j2 p n vis q fto ftl Mc ip usp lao lal (rdW (m.arr64 IW) (Mc + 4))
        (if lal < rdW (m.arr64 IW) (Mc + 4) then lao else lao + rdW (m.arr64 IW) (Mc + 4))
        (if lal < rdW (m.arr64 IW) (Mc + 4) then 0 else lal - rdW (m.arr64 IW) (Mc + 4))
        (if mal < rdW (m.arr64 IW) (Mc + 4) then mao else mao + rdW (m.arr64 IW) (Mc + 4))
        (if mal < rdW (m.arr64 IW) (Mc + 4) then 0 else mal - rdW (m.arr64 IW) (Mc + 4)) m := by
  by_cases h1 : lal < rdW (m.arr64 IW) (Mc + 4) <;> by_cases h2 : mal < rdW (m.arr64 IW) (Mc + 4)
  · rw [tkaE.arm1 (hc1 := h1), tkaE.j1.arm1 (hc1 := h2), ite_eq_left h1, ite_eq_left h1, ite_eq_left h2, ite_eq_left h2]
  · rw [tkaE.arm1 (hc1 := h1), tkaE.j1.arm2 (hc1 := h2), ite_eq_left h1, ite_eq_left h1, ite_eq_right h2, ite_eq_right h2]
  · rw [tkaE.arm2 (hc1 := h1), tkaE.j1.arm1 (hc1 := h2), ite_eq_right h1, ite_eq_right h1, ite_eq_left h2, ite_eq_left h2]
  · rw [tkaE.arm2 (hc1 := h1), tkaE.j1.arm2 (hc1 := h2), ite_eq_right h1, ite_eq_right h1, ite_eq_right h2, ite_eq_right h2]

/-- `tkaE` after `sl_eq` found the erased indices equal: the leaf's parameters as an `if`. -/
theorem tkaE_slEq (p : Prog) (n : Nat) (vis q fto ftl Mc ip usp lao lal K : Word) (m : Mem) (e : Word)
    (he : e ≠ 0) :
    tkaE.k_sl_eq p n vis q fto ftl Mc ip usp lao lal K m (.ok e) =
      tkaE.j3 p n vis q fto ftl Mc ip usp lao (if lal < K then lal else K) m := by
  by_cases h : lal < K
  · rw [tkaE.k_sl_eq.arm2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ he h, ite_eq_left h]
  · rw [tkaE.k_sl_eq.arm3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ he h, ite_eq_right h]

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq henv in
/-- **`target_k53_args` refines `tkArgs`, both outcomes** (twin side: con-ron's `targetK53_spec`,
the arguments' part): the indices erased (`eraseAll_spec`), compared, the leaf's class
(`internConstE_run`, `mkAppN_run`; `nestOcc` read-only), then `targetClassMatch` (`tcm_ref`). -/
theorem tka_ref (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    {q fto ftl Mc ip usp lao lal mao mal : Word}
    {bs : BlockShape} {formerTys : List EIdx} {TM : TargetMajor} {la ma : List EIdx}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hbs : BSOK m q.toNat bs) (hft : decHL m fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop m) (hMc : DecB (fun m => decTM m Mc.toNat) m TM)
    (hip : H ip) (hus : H usp) (hla : HSl0 m lao lal la) (hma : HSl0 m mao mal ma) (hP : RcMR m)
    {pP : ConLeche.BlockShape} {formerTysP laP maP : List ConLeche.Expr} {McP : ConLeche.TargetMajor}
    {I'P : ConLeche.Name} {us'P : List ConLeche.Level}
    (hsh : dShape a.store bs = some pP)
    (hftP : Frontend.denoteEList a.store formerTys = some formerTysP)
    (hMcP : dMajor a.store TM = some McP)
    (hipP : denoteN a.store.ns (decI ip) = some I'P)
    (husP : denoteLs a.store.lss (decI usp) = some us'P)
    (hlaP : Frontend.denoteEList a.store la = some laP)
    (hmaP : Frontend.denoteEList a.store ma = some maP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ConLeche.Cached.TargetMajScoped McP) :
    RefE (VerdictCtx p) (tkaE p n m vis q fto ftl Mc ip usp lao lal mao mal)
      (tkArgs fe bs formerTys TM (decI ip) (decI usp) la ma) a
      (fun v c a' => TcmPost dn vis fe env m v.1 v.2 c a') := by
  have hS := hC.stage
  obtain ⟨-, hMlv, hMds, hMnpc, -, -, -, -, hMpf⟩ := ConRon.Bridge.Inductives.dMajor_inv hMcP
  obtain _ | n := n
  · rw [tkaE.eq_1]; exact RefE.of_cls0 (by simp)
  rw [tkaE_succ, tkaE.j2.arm1]
  have hsz := hS.iw.iwSize
  obtain ⟨hlvH, hlvD, hdsS, hnP, hpfS, hMt⟩ := tmFields hMc hsz
  have hMk : ∀ k : Nat, k ≤ 12 → (Mc + UInt64.ofNat k).toNat < iwTop m := fun k hk => by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by omega : k < 2 ^ 64), Nat.mod_eq_of_lt (by
      have := (rdW (m.arr64 CTL) 200).toNat_lt; simp only [iwTop] at hMt; omega)]; omega
  generalize hK : rdW (m.arr64 IW) (Mc + 4) = K at hnP ⊢
  unfold tkArgs
  -- `erase_each` of the leaf's indices
  refine RefE.bindLift (fun _ => rfl) fun r1 m1 h1 => ?_
  obtain ⟨le, a1, run1, hd1, hb1, hS1, hg1, hP1⟩ := eeW_ok dn fe vis n h1 hS hla.drop hP
  rw [hnP] at run1
  refine ⟨_, _, run1, ?_⟩
  dsimp only [tkaE.k_erase_each]
  have hA1 := eeW_afr n h1 hA
  -- `erase_each` of the major's indices
  refine RefE.bindLift (fun _ => rfl) fun r2 m2 h2 => ?_
  obtain ⟨me, a2, run2, hd2, hb2, hS2, hg2, hP2⟩ := eeW_ok dn fe vis n h2 hS1 (hma.grow hg1).drop hP1
  rw [hnP] at run2
  refine ⟨_, _, run2, ?_⟩
  dsimp only [tkaE.k_erase_each_2]
  have hA2 := eeW_afr n h2 hA1
  have hg12 := hg1.trans hg2
  obtain ⟨q1, -⟩ := eraseAll_spec (la.drop TM.nPc) (laP.drop TM.nPc) a a1 le hC.check.state
    hC.check.pins ⟨trivial, ConRon.Bridge.Inductives.denoteEList_drop hlaP TM.nPc⟩ run1
  have hC1 := hC.of_pstep hS1 hA1 q1
  obtain ⟨q2, -⟩ := eraseAll_spec (ma.drop TM.nPc) (maP.drop TM.nPc) a1 a2 me hC1.check.state
    hC1.check.pins ⟨trivial, ConRon.Bridge.Inductives.denoteEList_drop
      (denoteEList_ext q1.ext _ _ hmaP) TM.nPc⟩ run2
  have hC2 := hC1.of_pstep hS2 hA2 q2
  have q12 := q1.trans q2
  -- `sl_eq`
  rcases h3 : eqW n m2 (r1.headD 0) (r1.tail.headD 0) (r2.headD 0) (r2.tail.headD 0) with _ | e
  · rw [liftE_none, tkaE.k_sl_eq.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  have he := eqW_dec h3 (by rw [decHL_grow hg2 hb1]; exact hd1) (hS2.lt64 (by have := hg2.iw; omega)) hd2
    (hS2.lt64 hb2)
  by_cases he0 : e = 0
  · rw [tkaE.k_sl_eq.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ he0]
    have hne : le ≠ me := by intro hq; rw [hq] at he; simp at he; exact absurd he (by rw [he0]; decide)
    have : (le != me) = true := by simpa using hne
    rw [ite_eq_left this]
    exact RefE.ret (y := false) rfl ⟨rfl, hC2, hg12, hP2, hA2⟩
  rw [tkaE_slEq _ _ _ _ _ _ _ _ _ _ _ _ _ _ he0, tkaE.j3.arm1]
  have heq : le = me := by
    by_cases hq' : le = me
    · exact hq'
    · rw [ite_eq_right hq'] at he; exact absurd he he0
  subst heq
  refine RefE.ite_neg (by simp) ?_
  -- `intern_const`
  refine RefE.bindLift (fun _ => rfl) fun hd m3 h4 => ?_
  obtain ⟨a3, run3, hS3, hg3⟩ := internConst_stage hS2 ip usp hip hus h4
  refine ⟨_, _, run3, ?_⟩
  have hA3 := ceinternW_afr h4 hA2
  obtain ⟨q3, hhdP⟩ := ConRon.Bridge.Inductives.internConstE_run hC2.check.state
    (ConRon.Bridge.denoteN_ext hipP q12.ext) (ConRon.Bridge.denoteLs_ext husP q12.ext) run3
  have hC3 := hC2.of_pstep hS3 hA3 q3
  have q13 := q12.trans q3
  dsimp only [tkaE.k_intern_const]
  refine RefE.abort0 rfl fun hb4 => ?_
  have hhd : H hd := by simp only [H]; rw [UInt64.le_iff_toNat_le] at hb4; simp at hb4; omega
  have hP3 : RcMR m3 := hP2.fr (ceinternW_mfr h4)
  have hg03 := hg12.trans hg3
  have hlp := (hla.grow hg03).take (k := K)
  rw [hnP] at hlp
  generalize hL : (if lal < K then lal else K) = lpl at hlp ⊢
  -- `mk_app_n_f`
  refine RefE.bindLift (fun _ => rfl) fun ra m4 h5 => ?_
  obtain ⟨app, a4, run4, hS4, hg4, happH, happD⟩ := mknF_ok dn vis fe hd lao lpl hhd _ m3 m4 a3 ra h5
    ⟨hS3, hlp.1⟩
  have hA4 := mknF_afr h5 hA3
  have hlpP := denoteEList_ext q13.ext _ _ (ConRon.Bridge.Inductives.denoteEList_take hlaP TM.nPc)
  obtain ⟨q4, -⟩ := ConRon.Bridge.Inductives.mkAppN_run (la.take TM.nPc) (laP.take TM.nPc)
    hC3.check.state hhdP hlpP run4
  have hC4 := hC3.of_pstep hS4 hA4 q4
  have q14 := q13.trans q4
  have hP4 : RcMR m4 := hP3.fr (MFr.ofMknF h5)
  have hg04 := hg03.trans hg4
  rw [← happD] at run4
  refine ⟨_, _, run4, ?_⟩
  dsimp only [tkaE.k_mk_app_n_f]
  -- `block_shape_member_names`
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun rn m5 h6 => ?_
  dsimp only [tkaE.k_block_shape_member_names]
  have hbs4 := hbs.grow hg04
  obtain ⟨hS5, hg5, -, hdn, htn⟩ := memberNamesW_stage h6 hS4 hbs4
  have hf5 := (memberNamesW_dec h6 hS4.iw.iwSize hS4.iw.ctl hbs4.dec
    (by have := hbs4.ptop; have := hS4.lt64 (Nat.le_refl _); omega) hbs4.2.1 hbs4.2.2).2.2.2.1
  have hP5 : RcMR m5 := hP4.fr (MFr.of_iw hf5)
  have hA5 := AFr.iw hf5 hA4
  have hC5 := hC4.of_pstep hS5 hA5 (PStep.refl hC4.check.state)
  -- `nest_occ`
  refine RefE.bindLift (fun _ => rfl) fun occ m6 h7 => ?_
  obtain ⟨b, run6, hb6, hS6, hg6, hP6⟩ := noF_ok dn fe vis n h7 hS5 happH hdn (Nat.le_of_eq htn) hP5
  refine ⟨_, _, run6, ?_⟩
  have hA6 := noF_afr h7 hA5
  have hC6 := hC5.of_pstep hS6 hA6 (PStep.refl hC5.check.state)
  have hg06 := (hg04.trans hg5).trans hg6
  by_cases ho : occ = 0
  · rw [tkaE.k_nest_occ.arm1 _ _ _ _ _ _ _ _ _ _ _ _ ho]
    have : b = false := by rw [← hb6, ho]; rfl
    subst this
    exact RefE.ret (y := false) rfl ⟨rfl, hC6, hg06, hP6, hA6⟩
  rw [tkaE.k_nest_occ.arm2 _ _ _ _ _ _ _ _ _ _ _ _ ho]
  have hb1 : b = true := by rw [← hb6]; simpa using ho
  subst hb1
  rw [ite_eq_left rfl]
  have hMk6 : ∀ k : Nat, k ≤ 12 → rdW (m6.arr64 IW) (Mc + UInt64.ofNat k) =
      rdW (m.arr64 IW) (Mc + UInt64.ofNat k) :=
    fun k hk => rdW_grow hg06 (hMk k hk)
  have e11 := hMk6 11 (by omega); have e12 := hMk6 12 (by omega); have e1 := hMk6 1 (by omega)
  have e2 := hMk6 2 (by omega); have e3 := hMk6 3 (by omega)
  simp only [show UInt64.ofNat 11 = (11 : Word) from rfl, show UInt64.ofNat 12 = (12 : Word) from rfl,
    show UInt64.ofNat 1 = (1 : Word) from rfl, show UInt64.ofNat 2 = (2 : Word) from rfl,
    show UInt64.ofNat 3 = (3 : Word) from rfl] at e11 e12 e1 e2 e3
  rw [e11, e12, e1, e2, e3]
  -- `target_class_match`: the twin's last step
  have h8 := tcm_ref hq henv n (by omega) hC6 hA6
    (hbs.grow hg06) hlvH hus
    (by rw [decHL_grow hg06 hftb]; exact hft) (by have := hg06.iw; omega) (hpfS.grow hg06) (hdsS.grow hg06)
    (hlp.grow ((hg4.trans hg5).trans hg6)) hP6
    (ConRon.Bridge.Inductives.dShape_ext q14.ext _ _ hsh) (denoteEList_ext q14.ext _ _ hftP)
    (denoteEList_ext q14.ext _ _ hMpf) (by rw [hlvD]; exact ConRon.Bridge.denoteLs_ext hMlv q14.ext)
    (denoteEList_ext q14.ext _ _ hMds) (ConRon.Bridge.denoteLs_ext husP q14.ext)
    (denoteEList_ext q4.ext _ _ hlpP) hformer hMs.1
  rw [hlvD] at h8
  exact RefE.mono h8 fun v c a' h => ⟨h.res, h.stage, hg06.trans h.grow, h.rc, h.abs⟩

end sims

end L.Ind
