import ConAgua.Arena.IndRealLvlC
import ConAgua.Arena.RecClassSpec.CrW
import ConAgua.Arena.RecGenSpec.ClassKeyCanon
import ConAgua.Verdict.IndBTmf
import ConAgua.Arena.IndInstallSpec.ConsBlockCtors
import ConAgua.Arena.DeclBasisSpec

/-!
# `target_major_of` under `StageC` with the real `inst_lp_fast` (lane `indstaget`, helper `rcC`)

`AbsOK` across `target_major_of`'s callees (moved from `IndT/RecGen19.lean`); the refinements of
`target_major_of` for both outcomes, with their post `TmoPost`: the outside branch `tmt_ref`
(`target_major_of_outside_tail`) and `tmo_ref` (`target_major_of_outside`), `tmc_ref`
(`target_major_of_const`) and `tmf_ref` (`target_major_of`). `StageC` and `AbsOK` are carried to `target_outside_inst`'s call by con-ron's steps of `targetMajorOf_spec`'s proof
(`getAppArgs_run`, `getAppFn_run`, `viewConst_run`, `targetCtorsOf_spec`, `allM_E_pstep` of
`RC.closed1_run`, `anyM_E_pstep` of `nestOcc_spec`), so the real `inst_lp_fast` meets its contract
there (`IlpRd.realC`); after it `StageR` and `AbsOK`.
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dMajor)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `AbsOK` across `target_major_of` -/

theorem ckc2W_afr : ∀ (n : Nat) (m m' : Mem) (nP o l : Word) (r : List Word),
    ckc2W n m nP o l = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, h => by simp [ckc2W] at h
  | n + 1, m, m', nP, o, l, r, h => by
    by_cases hl : l = 0
    · rw [ckc2W_nil n m nP o l hl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact AFr.refl _
    rw [ckc2W_cons n m nP o l hl] at h
    obtain ⟨⟨rb, m1⟩, h1, h⟩ := of_K h (by simp only [ckc2K1])
    refine (bvbW_afr h1).trans ?_
    by_cases hb : rb ≠ 0
    · rw [ckc2K1_open (h := hb)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact AFr.refl _
    rw [ckc2K1_closed (h := hb)] at h
    obtain ⟨⟨rf, m2⟩, h2, h⟩ := of_K h (by simp only [ckc2K2])
    refine (fvbF_afr h2).trans ?_
    by_cases hf : nP < rf.headD 0
    · rw [ckc2K2_open (h := hf)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact AFr.refl _
    rw [ckc2K2_closed (h := hf)] at h
    obtain ⟨⟨r3, m3⟩, h3, h⟩ := of_K h rfl
    rw [ckcK3_some] at h
    cases h; exact ckc2W_afr n _ _ _ _ _ _ h3

section calls
variable {p : Prog} {n : Nat} {m m' : Mem} {r : List Word}

theorem noC_afr (hN : NoProg p) {no nl lo hi e : Word}
    (h : callW p n "nest_occ" [no, nl, lo, hi, e] m = some (r, m')) : AFr m m' := by
  rcases n with _ | k
  · rw [callW_zero] at h; cases h
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (nestOcc_spec p hN.hv hN.hc hN.hf hN.hput hN.hgo hN.hnode hN.hcl hN.hp k _ no nl lo hi e) h
  exact noConstWf_afr (n := k + 1) hW

theorem ocW_afr (hN : NoProg p) : ∀ (n : Nat) (m m' : Mem) (no nl o l : Word) (r : List Word),
    ocW p n m no nl o l = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, h => by simp [ocW] at h
  | n + 1, m, m', no, nl, o, l, r, h => by
    by_cases hl : l = 0
    · rw [ocW_nil p n m no nl o l hl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact AFr.refl _
    rw [ocW_cons p n m no nl o l hl] at h
    obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h (by simp only [ocK1])
    refine (noC_afr hN h1).trans ?_
    by_cases hb : r1.headD 0 ≠ 0
    · rw [ocK1_hit p n m1 no nl o l r1 hb] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact AFr.refl _
    rw [ocK1_miss p n m1 no nl o l r1 hb] at h
    obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h rfl
    rw [ocK2_some] at h
    cases h; exact ocW_afr hN n _ _ _ _ _ _ _ h2

theorem mkTmC_afr (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hp : p.lookup "mk_target_major" = some mkTargetMajor)
    {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : Word}
    (h : callW p n "mk_target_major" [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12] m =
      some (r, m')) : AFr m m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (mkTargetMajor_spec p ha hp n _ _ _ _ _ _ _ _ _ _ _ _ _ _) h
  exact mkTMW_afr hW

end calls

/-! ## The sims under `StageC` -/

/-- What `target_major_of_outside` and its tail give besides the twin's major `x` (from `m`): the
major's record at the result word, the stage, the growth, `PosMR`, `AbsOK`. -/
structure TmoPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m : Mem) (w : Word)
    (m' : Mem) (x : TargetMajor) (a' : AState) : Prop where
  dec : DecB (fun m => decTM m w.toNat) m' x
  stage : StageR dn vis fe m' a'
  grow : IWGrow m m'
  pos : PosMR m'
  abs : AbsOK m'

/-- **`target_major_of_outside_tail` refines `tmoTailT`, both outcomes** (the real `inst_lp_fast`
and `lvl_eq_c`): `toi_ref`, then con-ron's `targetOutsideInst_spec` (a core step) gives `StageC`
and the instance's sort's readback, so `lvlEqC_simC` applies to `lvl_eq_c`; its two rejects are
the twin's `liftFueled` decline and the universe fail. -/
theorem tmt_ref {p : Prog} (hP : TmtProg p) (hIlpf : IlpfF p) (hcore : CoreStageClosed p)
    (hLC : LvlCacheProg p) {env : ConLeche.Env} {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} (n : Nat) {m : Mem} {a : AState} {pp pfo pfl I us dso dsl cso csl : Word}
    {bs : BlockShape} {pfvs ds : List EIdx} {ctors : List (IConstantVal × Nat)}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hq : DecB (fun m => decBS m pp.toNat) m bs) (hq9 : pp.toNat + 9 ≤ iwTop m)
    (hI : H I) (hus : H us) (hds : DecB (fun m => decHL m dso.toNat dsl.toNat) m ds)
    (hdsb : dso.toNat + dsl.toNat < 2 ^ 64)
    (hct : DecB (fun m => decPL m (decCN m) cso.toNat csl.toNat) m ctors)
    (hpf : DecB (fun m => decHL m pfo.toNat pfl.toNat) m pfvs) (hPm : PosMR m)
    {IP : ConLeche.Name} (hIP : denoteN a.store.ns (decI I) = some IP)
    {usP : List ConLeche.Level} (husP : denoteLs a.store.lss (decI us) = some usP)
    {dsP : List ConLeche.Expr} (hdsP : Frontend.denoteEList a.store ds = some dsP)
    {lr : ConLeche.Level} (hres : denoteL a.store.ls bs.resSort = some lr) :
    RefE (closedNV p _root_.L.Checker.nvFns = true) (tmtE p n m vis pp pfo pfl I us dso dsl cso csl)
      (tmoTailT fe bs pfvs ds dsl.toNat ctors (decI I) (decI us)) a
      (fun v x a' => TmoPost dn vis fe m v.1 v.2 x a') := by
  cases n with
  | zero => rw [tmtE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n =>
  rw [tmtE.arm1]
  unfold tmoTailT
  have hR1 := toi_ref hP.toi hIlpf n hC hI hus hds hdsb
  rcases h1 : toiE p n m vis I us dso dsl with e1 | ⟨r1, m1⟩ <;> rw [h1] at hR1
  · rw [tmtE.k_target_outside_inst.none]; exact RefE.bind_left hR1
  rw [tmtE.k_target_outside_inst.arm1]
  obtain ⟨x, a1, hrun, hR⟩ := hR1
  have hA1 := hR.afr hA
  obtain ⟨c1, v, ⟨-, hlP⟩, -⟩ := ConRon.Bridge.Inductives.targetOutsideInst_spec fe (decI I) IP
    (decI us) usP ds dsP a a1 x hC.check ⟨hIP, husP, hdsP⟩ hrun
  obtain ⟨hr1, hn1, hsH, hsd⟩ := hR.res
  refine RefE.bind_right hrun ?_
  have hg1 : IWGrow m m1 := hR.grow
  have hP1 : PosMR m1 := hPm.fr hR.mfr
  have hC1 : StageC dn vis fe env m1 a1 := hC.of_check hR.stage hA1 c1.ok c1.ext
  obtain ⟨-, -, hrsH, hrsd⟩ := partsShapeWords hg1 hq hq9
  have hdu : denoteL a1.store.ls (decI (r1.tail.headD 0)) = some v.2 := by rw [hsd]; exact hlP
  have hdv : denoteL a1.store.ls (decI (rdW (m1.arr64 IW) (pp + 6))) = some lr := by
    rw [hrsd]; exact ConRon.Bridge.denoteL_ext hres c1.ext
  rcases h2 : callW p n "lvl_eq_c" [r1.tail.headD 0, rdW (m1.arr64 IW) (pp + 6)] m1 with _ | ⟨r2, m2⟩
  · rw [liftE_none, tmtE.k_lvl_eq_c.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨xl, al, hrunl, hC2, hg2, hx, hA2, -⟩ := lvlEqC_simC p hcore hLC n hC1 hA1 _ _ hsH hrsH v.2 lr
    hdu hdv r2 m2 h2
  rw [hsd, hrsd] at hrunl
  refine RefE.bind_right hrunl ?_
  by_cases h0 : r2.headD 0 = 0
  · rw [tmtE.k_lvl_eq_c.abort1 p n pfo pfl I us dso dsl cso csl _ r2 m2 h0]
    have hn : xl = none := by
      rcases xl with _ | b
      · rfl
      · cases b <;> simp only [decLvlEq] at hx <;> rw [hx] at h0 <;> exact absurd h0 (by decide)
    subst hn
    exact RefE.bind_left fun _ => ErrClaim.fail _ _ (by decide)
  by_cases h2' : r2.headD 0 ≠ 2
  · rw [tmtE.k_lvl_eq_c.abort2 p n pfo pfl I us dso dsl cso csl _ r2 m2 h0 h2']
    have hf : xl = some false := by
      rcases xl with _ | b
      · simp only [decLvlEq] at hx; exact absurd hx h0
      · cases b
        · rfl
        · simp only [decLvlEq] at hx; exact absurd hx h2'
    subst hf
    simp only [liftFueled, pure_bind, Bool.false_eq_true, ite_false]
    exact RefE.bind_left fun _ => ErrClaim.fail _ _ (by decide)
  replace h2' : r2.headD 0 = 2 := by simpa using h2'
  rw [tmtE.k_lvl_eq_c.arm1 p n pfo pfl I us dso dsl cso csl _ r2 m2 h0 h2']
  have ho : xl = some true := by
    rcases xl with _ | b
    · simp only [decLvlEq] at hx; exact absurd hx h0
    · cases b
      · simp only [decLvlEq] at hx; exact absurd (hx.symm.trans h2') (by decide)
      · rfl
  subst ho
  simp only [liftFueled, pure_bind]
  have hP2 : PosMR m2 := hP1.fr (MFr.of_frame (run_memFrame hcore (by decide) (run_of_callW h2)).1
    coreStageA_stage coreStageC_stage)
  rcases e4 : callW p n "mk_target_major" [I, us, dso, dsl, dsl, r1.headD 0, cso, csl, 0, 0, 0, pfo, pfl] m2
    with _ | ⟨r4, m4⟩
  · rw [liftE_none, tmtE.k_mk_target_major.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, tmtE.k_mk_target_major.arm1]
  have hA4 := mkTmC_afr hP.toi.alloc hP.mkTm e4 hA2
  obtain ⟨s4, rfl, -, hW4⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
    (mkTargetMajor_spec p hP.toi.alloc hP.mkTm n _ _ _ _ _ _ _ _ _ _ _ _ _ _) e4
  rw [mkTMW_eq, Option.map_eq_some_iff] at hW4
  obtain ⟨⟨q, m4'⟩, hpr, he⟩ := hW4
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨hS4, hg4, hq4, ht4, hget4⟩ := posRecW_stage hpr hC2.stage (by simp)
  simp only [List.length_cons, List.length_nil] at ht4
  have hg04 := (hg1.trans hg2).trans hg4
  have hq4' : q.toNat = iwTop m2 := hq4
  have ht4' : iwTop s4.mem = iwTop m2 + 13 := ht4
  have hdec := decTM_decB_of (m := s4.mem) (q := q.toNat) (by omega)
    (by simpa using hget4 0 (by simp)) (by simpa using hget4 1 (by simp)) (by simpa using hget4 2 (by simp))
    (by simpa using hget4 3 (by simp)) (by simpa using hget4 4 (by simp)) (by simpa using hget4 5 (by simp))
    (by simpa using hget4 6 (by simp)) (by simpa using hget4 7 (by simp)) (by simpa using hget4 8 (by simp))
    (by simpa using hget4 9 (by simp)) (by simpa using hget4 10 (by simp)) (by simpa using hget4 11 (by simp))
    (by simpa using hget4 12 (by simp)) hI hus (hds.grow (OMono.decHL _ _) hg04)
    (hct.grow (OMono.decPL decCN_mono _ _) hg04)
    (show decPL (truncM s4.mem) (decNCN (truncM s4.mem)) (0 : Word).toNat (0 : Word).toNat = some [] by
      simp [decPL])
    (hpf.grow (OMono.decHL _ _) hg04)
  have hn1' : (r1.head?.getD 0).toNat = x.1 := by simpa using hn1
  rw [hn1'] at hdec
  exact RefE.ret rfl ⟨by simpa [decON] using hdec, hS4, hg04, hP2.fr (posRecW_mfr hpr), hA4⟩

/-- **`target_major_of_outside` refines `tmoOutT`, both outcomes**: the rejects are the twin's
`fail`s (Quot, not a stored inductive, too few arguments, the closedness test, the occurrence
test); the tail is `tmt_ref`. -/
theorem tmo_ref {p : Prog} (hP : TmoOProg p) (hIlpf : IlpfF p) (hcore : CoreStageClosed p)
    (hLC : LvlCacheProg p) {env : ConLeche.Env} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    (n : Nat) {m : Mem} {a : AState}
    {pp pfo pfl I us ao al mno mnl : Word} {bs : BlockShape} {pfvs args : List EIdx} {ws : List Word}
    (hS : StageR dn vis fe m a) (hq : DecB (fun m => decBS m pp.toNat) m bs) (hq9 : pp.toNat + 9 ≤ iwTop m)
    (hws : SlR m mno mnl ws) (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32)
    (hwsb : ∀ i < mnl.toNat, mno.toNat + i < iwTop m) (hnames : ws.map (fun w => (decI w : NIdx)) = bs.memberNames)
    (hag : DecB (fun m => decHL m ao.toNat al.toNat) m args) (hagb : ao.toNat + al.toNat ≤ iwTop m)
    (hpf : DecB (fun m => decHL m pfo.toNat pfl.toNat) m pfvs) (hI : H I) (hus : H us) (hPm : PosMR m)
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) {pP : ConLeche.BlockShape}
    (hshP : ConRon.Bridge.Inductives.dShape a.store bs = some pP) {IP : ConLeche.Name}
    (hIP : denoteN a.store.ns (decI I) = some IP) {usP : List ConLeche.Level}
    (husP : denoteLs a.store.lss (decI us) = some usP) {argsP : List ConLeche.Expr}
    (hargsP : Frontend.denoteEList a.store args = some argsP) :
    RefE (closedNV p _root_.L.Checker.nvFns = true) (tmoE p n m vis pp pfo pfl I us ao al mno mnl)
      (tmoOutT fe bs pfvs args (decI I) (decI us)) a (fun v x a' => TmoPost dn vis fe m v.1 v.2 x a') := by
  cases n with
  | zero => rw [tmoE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n =>
  have hT : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.iw.1 hS.iw.2.2.1
  rw [tmoE.arm1]
  unfold tmoOutT
  -- `pin_at`
  rcases h1 : callW p n "pin_at" [47] m with _ | ⟨r1, m1⟩
  · rw [liftE_none, tmoE.k_pin_at.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨s1, rfl, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (L.Arena.pinAt_specW p hP.pin n _ 47) h1
  obtain ⟨hm1, hr1, hqH, hrun1⟩ := L.Arena.pinAtW_ok (a := a) hW1 hS.check.pins
  have hm1' : s1.mem = m := hm1
  simp only at hr1 hqH hrun1
  rw [hm1']
  subst hr1
  refine RefE.bind_right hrun1 ?_
  by_cases hIq : I = pinW m (1 + (47 : Word).toNat)
  · rw [tmoE.k_pin_at.abort1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hIq]
    simp only [hIq, beq_self_eq_true, ite_true]
    exact fun _ => ErrClaim.fail _ _ (by decide)
  rw [tmoE.k_pin_at.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hIq]
  have hne : ((decI I : NIdx) == decI (pinW m (1 + (47 : Word).toNat))) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; rw [decI_inj_iff hI hqH]; exact hIq
  simp only [hne, Bool.false_eq_true, ite_false]
  -- `target_ctors_of`
  rcases h2 : callW p n "target_ctors_of" [vis, I] m with _ | ⟨r2, m2⟩
  · rw [liftE_none, tmoE.k_target_ctors_of.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  rcases n with _ | k
  · rw [callW_zero] at h2; cases h2
  obtain ⟨s2, rfl, -, hW2⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (tco_spec p hP.nt hP.tco k _ vis I) h2
  rcases k with _ | k'
  · simp [ntWf, tcoPK] at hW2
  rcases hnt : ntW k' m vis I with _ | y
  · rw [show ntWf (k' + 1) _ vis I = ntW k' _ vis I from rfl, hnt] at hW2; simp [tcoPK] at hW2
  obtain ⟨r, m'⟩ := y
  rw [show ntWf (k' + 1) _ vis I = ntW k' _ vis I from rfl, hnt, tcoPK_some] at hW2
  obtain ⟨rfl, hm'⟩ := Prod.mk.inj (Option.some.inj hW2)
  obtain ⟨x, a', hrun, hS2, hg2, hout⟩ := ntW_ok dn fe vis I hI k' m m' a r hnt hS
  have hf : MFr [] [] m m' := ntWf_mfr (k := k' + 1) (show ntWf (k' + 1) m vis I = some (r, m') from hnt)
  have hA2 : AbsOK m' := ntWf_afr (k := k' + 1) (show ntWf (k' + 1) m vis I = some (r, m') from hnt) hA
  obtain ⟨p2, -⟩ := ConRon.Bridge.Inductives.targetCtorsOf_spec (env := env) fe (decI I) IP a a' x
    hC.check.state ⟨hC.check.ienv.toS, hIP⟩ hrun
  have hC2 := hC.of_pstep hS2 hA2 p2
  have hP2 : PosMR m' := hPm.fr hf
  rw [← hm']
  refine RefE.bind_right hrun ?_
  rcases x with _ | ⟨nPc, cs⟩
  · have hz : r.headD 0 = 0 := by simpa [NcOut] using hout
    rw [tmoE.k_target_ctors_of.abort1 _ _ _ _ _ _ _ _ _ _ _ _ [r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0] _ (by simpa using hz)]
    exact fun _ => ErrClaim.fail _ _ (by decide)
  obtain ⟨h1, hnP, hcl, hcb, hcsat⟩ := hout
  have hne0 : r.headD 0 ≠ 0 := by rw [h1]; decide
  have hagT : decHL (truncM m) ao.toNat al.toNat = some args := hag
  have hal' := decHL_length _ hagT
  by_cases hal : al < r.tail.headD 0
  · rw [tmoE.k_target_ctors_of.abort2 _ _ _ _ _ _ _ _ _ _ _ _ [r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0] _
      (by simpa using hne0) (by simpa using hal)]
    have hlt : al.toNat < nPc := by have := UInt64.lt_iff_toNat_lt.mp hal; omega
    refine RefE.ite_pos ?_ (fun _ => ErrClaim.fail _ _ (by decide))
    simp only [bne_iff_ne, ne_eq, List.length_take]; omega
  rw [tmoE.k_target_ctors_of.arm1 _ _ _ _ _ _ _ _ _ _ _ _ [r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0] _
    (by simpa using hne0) (by simpa using hal)]
  simp only [List.tail_cons, List.headD_cons]
  have hnal : nPc ≤ al.toNat := by
    have : ¬ al.toNat < (r.tail.headD 0).toNat := fun h => hal (UInt64.lt_iff_toNat_lt.mpr h)
    omega
  have hlen : (args.take nPc).length = nPc := by simp; omega
  refine RefE.ite_neg (by simp only [hlen, bne_self_eq_false, Bool.false_eq_true, not_false_eq_true]) ?_
  have hT2 : iwTop m' < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
  have htake : DecB (fun m => decHL m ao.toNat (r.tail.headD 0).toNat) m (args.take nPc) := by
    show decHL (truncM m) _ _ = _
    rw [hnP, decHL_take hagT _ hnal]
  have htake2 : decHL m' ao.toNat (r.tail.headD 0).toNat = some (args.take nPc) :=
    htake.stab (OMono.decHL _ _) m' hg2
  obtain ⟨hnpw, hnpb, -, -⟩ := partsShapeWords hg2 hq hq9
  -- the closedness test
  rcases h3 : callW p (k' + 1 + 1) "target_major_of_outside_closed"
      [ao, r.tail.headD 0, rdW (m'.arr64 IW) (pp + 4)] m' with _ | ⟨r3, m3⟩
  · rw [liftE_none, tmoE.k_target_major_of_outside_closed.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨s3, rfl, -, hW3⟩ := triple_of_callW (s₀ := ⟨m', Locals.init []⟩)
    (tmoc_spec p hP.bvb hP.hf hP.tmoc (k' + 1 + 1) _ ao (r.tail.headD 0) (rdW (m'.arr64 IW) (pp + 4))) h3
  obtain ⟨b, a3, hrun3, hS3, hg3, hb3, -⟩ := ckc2W_ok dn fe vis (k' + 1 + 1) m' s3.mem a' _ ao _ _ r3 hW3 hS2
    htake2 (by have := hg2.1; omega) (by have := hg2.1; omega)
  rw [hnpw, UInt64.toNat_ofNat_of_lt' hnpb] at hrun3
  have hA3 : AbsOK s3.mem := ckc2W_afr _ _ _ _ _ _ _ hW3 hA2
  obtain ⟨p3, -⟩ := ConRon.Bridge.Inductives.allM_E_pstep (fun _ => True) (fun _ h => h)
    (fun e eP s₀ s' b hok _ he hrun => ConRon.Bridge.Inductives.RC.closed1_run hok he hrun)
    _ _ a' a3 b hC2.check.state trivial
    (ConRon.Bridge.Inductives.denoteEList_take (ConRon.Bridge.denoteEList_ext p2.ext _ _ hargsP) nPc) hrun3
  refine RefE.bind_right hrun3 ?_
  cases b
  · have hz : r3.headD 0 = 0 := by simpa using hb3
    rw [tmoE.k_target_major_of_outside_closed.abort1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hz]
    exact RefE.ite_pos (by simp) (fun _ => ErrClaim.fail _ _ (by decide))
  have h0 : r3.headD 0 ≠ 0 := by simpa using hb3
  rw [tmoE.k_target_major_of_outside_closed.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h0]
  refine RefE.ite_neg (by simp) ?_
  have hP3 : PosMR s3.mem := hP2.fr (ckc2W_mfr _ _ _ _ _ _ _ hW3)
  have hC3 := hC2.of_pstep hS3 hA3 p3
  have hg03 := hg2.trans hg3
  -- the occurrence test
  rw [← hnames]
  rcases h4 : callW p (k' + 1 + 1) "target_major_of_outside_occ" [mno, mnl, ao, r.tail.headD 0] s3.mem
    with _ | ⟨r4, m4⟩
  · rw [liftE_none, tmoE.k_target_major_of_outside_occ.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨s4, rfl, -, hW4⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (oc_spec p hP.occ (k' + 1 + 1) _ mno mnl ao (r.tail.headD 0)) h4
  have hT3 : iwTop s3.mem < 2 ^ 64 := Nat.lt_of_le_of_lt hS3.2.1 hS3.2.2.2.1
  obtain ⟨b, a4, hrun4, hb4, hS4, hg4, hP4⟩ := ocW_sim hP.no mno mnl ws hwlt (k' + 1 + 1) s3.mem a3 ao _
    (args.take nPc) hS3 (slR_grow hg03 hT hws hwsb)
    (fun i hi => Nat.lt_of_lt_of_le (hwsb i hi) hg03.1) (htake.stab (OMono.decHL _ _) s3.mem hg03)
    (by have := hg03.1; omega) hP3 r4 s4.mem hW4
  have hA4 : AbsOK s4.mem := ocW_afr hP.no _ _ _ _ _ _ _ _ hW4 hA3
  have hx3 := (p2.trans p3).ext
  have hnm : Frontend.denoteNList a3.store.ns (ws.map (fun w => (decI w : NIdx))) = some pP.memberNames := by
    rw [hnames]; exact ConRon.Bridge.denoteNListE_ext hx3 _ _
      (ConRon.Bridge.Inductives.BlockShape.memberNames_spec hshP)
  obtain ⟨p4, -⟩ := ConRon.Bridge.Inductives.anyM_E_pstep
    (fun st => Frontend.denoteNList st.ns (ws.map (fun w => (decI w : NIdx))) = some pP.memberNames)
    (fun hx h => ConRon.Bridge.denoteNListE_ext hx _ _ h)
    (fun e eP s₀ s' b hok hq he hrun => ConRon.Bridge.Inductives.nestOcc_spec _ pP.memberNames 0 0 e eP
      s₀ s' b hok ⟨hq, he⟩ hrun)
    _ _ a3 a4 b hC3.check.state hnm
    (ConRon.Bridge.Inductives.denoteEList_take (ConRon.Bridge.denoteEList_ext hx3 _ _ hargsP) nPc) hrun4
  refine RefE.bind_right hrun4 ?_
  cases b
  · have hz : r4.headD 0 = 0 := by simpa using hb4
    rw [tmoE.k_target_major_of_outside_occ.abort1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hz]
    exact RefE.ite_neg (by simp) (RefE.bind_left fun _ => ErrClaim.fail _ _ (by decide))
  have h0 : r4.headD 0 ≠ 0 := by simpa using hb4
  rw [tmoE.k_target_major_of_outside_occ.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ h0]
  refine RefE.ite_pos (by simp) ?_
  -- the tail
  have hC4 := hC3.of_pstep hS4 hA4 p4
  have hg04 := hg03.trans hg4
  have hx4 := (p2.trans (p3.trans p4)).ext
  obtain ⟨-, -, -, -, hsP, -, -⟩ := ConRon.Bridge.Inductives.dShape_inv hshP
  have hcsd := csAt_decB hcsat hcb
  rw [← hcl] at hcsd
  have := tmt_ref hP.tmt hIlpf hcore hLC (k' + 1 + 1) (bs := bs) (pfvs := pfvs) (ds := args.take nPc)
    (ctors := cs) hC4 hA4 (hq.grow (decBS_mono _) hg04) (by have := hg04.1; omega) hI hus
    (htake.grow (OMono.decHL _ _) hg04) (by have := hg04.1; omega)
    (hcsd.grow (OMono.decPL decCN_mono _ _) (hg3.trans hg4)) (hpf.grow (OMono.decHL _ _) hg04) hP4
    (ConRon.Bridge.denoteN_ext hIP hx4) (ConRon.Bridge.denoteLs_ext husP hx4)
    (ConRon.Bridge.Inductives.denoteEList_take (ConRon.Bridge.denoteEList_ext hx4 _ _ hargsP) nPc)
    (ConRon.Bridge.denoteL_ext hsP hx4)
  rw [hnP] at this
  exact this.mono fun _ _ _ h => ⟨h.dec, h.stage, hg04.trans h.grow, h.pos, h.abs⟩

/-- **`target_major_of_const` refines `targetMajorOf` after the head's view, both outcomes**: the
member branch is `tmm_ref`, the outside branch `tmo_ref`; `block_shape_member_names` and
`sl_find` are lifted. -/
theorem tmc_ref {p : Prog} (hP : TmfProg p) (hIlpf : IlpfF p) (hcore : CoreStageClosed p)
    (hLC : LvlCacheProg p) {env : ConLeche.Env} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    (n : Nat) {m : Mem} {a : AState}
    {pp cao cal pfo pfl fvo fvl ao al x y : Word} {bs : BlockShape}
    {css : List (List (IConstantVal × Nat))} {pfvs fvs args : List EIdx}
    (hS : StageR dn vis fe m a) (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    (hcss : PSlR decCNS css cao cal m) (hpf : DecB (fun m => decHL m pfo.toNat pfl.toNat) m pfvs)
    (hfv : DecB (fun m => decHL m fvo.toNat fvl.toNat) m fvs) (hfvb : fvo.toNat + fvl.toNat ≤ iwTop m)
    (hag : DecB (fun m => decHL m ao.toNat al.toNat) m args) (hagb : ao.toNat + al.toNat ≤ iwTop m)
    (hx : H x) (hy : H y) (hPm : PosMR m)
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) {pP : ConLeche.BlockShape}
    (hshP : ConRon.Bridge.Inductives.dShape a.store bs = some pP) {IP : ConLeche.Name}
    (hIP : denoteN a.store.ns (decI x) = some IP) {usP : List ConLeche.Level}
    (husP : denoteLs a.store.lss (decI y) = some usP) {argsP : List ConLeche.Expr}
    (hargsP : Frontend.denoteEList a.store args = some argsP) :
    RefE (closedNV p _root_.L.Checker.nvFns = true) (tmcE p n m vis pp cao cal pfo pfl fvo fvl ao al x y)
      (match bs.memberNames.findIdx? (· == (decI x : NIdx)) with
        | some t => tmoMemT bs css pfvs fvs args (decI x) (decI y) t
        | none => tmoOutT fe bs pfvs args (decI x) (decI y)) a
      (fun v x a' => TmoPost dn vis fe m v.1 v.2 x a') := by
  cases n with
  | zero => rw [tmcE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n =>
  have hT : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.iw.1 hS.iw.2.2.1
  obtain ⟨hqd, hq9, hptr⟩ := partsShapeFacts hq hsrc
  rw [tmcE.arm1]
  -- `block_shape_member_names`
  rcases h4 : callW p n "block_shape_member_names" [pp] m with _ | ⟨r4, m4⟩
  · rw [liftE_none, tmcE.k_block_shape_member_names.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, tmcE.k_block_shape_member_names.arm1]
  obtain ⟨s4, rfl, hr4, hdn, hg4, hf4, ht4⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockShapeMemberNames_refines p hP.tmm.alloc hP.mnc hP.bsmn n _ pp bs hqd (by omega) hS.iw.2.2.1 hS.iw.2.2.2.2
      hsrc (fun o l j v h1 h2 h3 h4 => Nat.lt_of_succ_lt (hptr o l j v h1 h2 h3 h4))) h4
  obtain ⟨s4', hs4', -, hW4⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockShapeMemberNames_spec p hP.tmm.alloc hP.mnc hP.bsmn n _ pp) h4
  have hroom := memberNamesW_room hW4 hS.iw.2.2.1
  rw [partsShapeK hqd hq9] at hroom
  have hkb : bs.k < 2 ^ 64 := by
    obtain ⟨o, l, -, hl', hg'⟩ := decAt_some (decBS_some hqd).1
    have := iwN_rdW hl' (by omega); rw [BlockShape.k, decPL_length _ hg']; exact this.2
  rw [UInt64.toNat_ofNat_of_lt' hkb] at hroom
  simp only at hr4 hdn hg4 hf4 ht4
  have hS4 : StageR dn vis fe s4.mem a := stage_frame_iw hS hf4 (by
    rw [← ht4]; simp only [iwTop] at hroom ⊢; omega)
  have hT4 : iwTop s4.mem < 2 ^ 64 := Nat.lt_of_le_of_lt hS4.iw.1 hS4.iw.2.2.1
  have hP4 : PosMR s4.mem := hPm.fr (MFr.of_iw hf4)
  have hA4 : AbsOK s4.mem := memberNamesW_afr (hs4' ▸ hW4) hA
  have hC4 : StageC dn vis fe env s4.mem a := hC.of_pstep hS4 hA4 (PStep.refl hC.check.state)
  subst hr4
  simp only [List.headD_cons, List.tail_cons]
  obtain ⟨ws, hsl, hws, hwlt⟩ := slR_of_decHL s4.mem _ _ _ hdn (by omega)
  rw [UInt64.ofNat_toNat] at hsl
  -- `sl_find`
  rcases h5 : callW p n "sl_find" [rdW (m.arr64 CTL) 200, UInt64.ofNat bs.k, x] s4.mem with _ | ⟨r5, m5⟩
  · rw [liftE_none, tmcE.k_sl_find.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨s5, rfl, -, hm5, hW5⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (slFind_spec p hP.find n _ _ _ x) h5
  simp only at hm5
  have hlen : ws.length < 2 ^ 64 := by rw [slR_length hsl]; exact UInt64.toNat_lt _
  have hr5 := findW_ok n s4.mem _ _ x r5 ws hsl hW5 hlen
  rw [hm5]
  rw [hws, findIdx_map_decI x hx ws hwlt]
  cases hfi : ws.findIdx? (· == x) with
  | some i =>
    rw [hfi] at hr5
    subst hr5
    rw [tmcE.k_sl_find.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by simp)]
    simp only [List.tail_cons, List.headD_cons]
    obtain ⟨hi, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hfi
    have hie : (UInt64.ofNat i : Word).toNat = i := UInt64.toNat_ofNat_of_lt' (show i < 2 ^ 64 by omega)
    have := tmm_ref (p := p) (dn := dn) (vis := vis) (fe := fe) n (t := UInt64.ofNat i) (bs := bs) (css := css) hS4
      (hq.grow (decBS_mono _) hg4) (partsHsrc_grow hg4 hq9 hsrc) (hcss.grow decCNS_mono hg4)
      (hpf.grow (OMono.decHL _ _) hg4) (hfv.grow (OMono.decHL _ _) hg4) (Nat.le_trans hfvb hg4.1)
      (hag.grow (OMono.decHL _ _) hg4) (Nat.le_trans hagb hg4.1) hx hy hP4
    rw [hie] at this
    exact this.mono fun _ _ _ h => ⟨h.dec, h.stage, hg4.trans h.grow, h.pos, h.afr hA4⟩
  | none =>
    rw [hfi] at hr5
    subst hr5
    rw [tmcE.k_sl_find.arm2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by simp)]
    exact (tmo_ref hP.tmo hIlpf hcore hLC n (m := s4.mem) hS4 (hq.grow (decBS_mono _) hg4)
      (by have := hg4.1; omega) hsl hwlt (fun j hj => by rw [UInt64.toNat_ofNat_of_lt' hkb] at hj; omega)
      hws.symm (hag.grow (OMono.decHL _ _) hg4) (Nat.le_trans hagb hg4.1) (hpf.grow (OMono.decHL _ _) hg4)
      hx hy hP4 hC4 hA4 hshP hIP husP hargsP).mono
      fun _ _ _ h => ⟨h.dec, h.stage, hg4.trans h.grow, h.pos, h.abs⟩

/-- **`target_major_of` refines `targetMajorOf`, both outcomes**: the reject is the twin's "not an
inductive's application" fail; `get_app_args_f`, `get_app_fn_f` and `e_view` are lifted; the tail
is `tmc_ref`. -/
theorem tmf_ref {p : Prog} (hP : TmfProg p) (hIlpf : IlpfF p) (hcore : CoreStageClosed p)
    (hLC : LvlCacheProg p) {env : ConLeche.Env} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    (n : Nat) {m : Mem} {a : AState}
    {pp cao cal pfo pfl fvo fvl mty : Word} {bs : BlockShape}
    {css : List (List (IConstantVal × Nat))} {pfvs fvs : List EIdx}
    (hS : StageR dn vis fe m a) (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    (hcss : PSlR decCNS css cao cal m) (hpf : DecB (fun m => decHL m pfo.toNat pfl.toNat) m pfvs)
    (hfv : DecB (fun m => decHL m fvo.toNat fvl.toNat) m fvs) (hfvb : fvo.toNat + fvl.toNat ≤ iwTop m)
    (hmty : H mty) (hPm : PosMR m)
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) {pP : ConLeche.BlockShape}
    (hshP : ConRon.Bridge.Inductives.dShape a.store bs = some pP) {mtyP : ConLeche.Expr}
    (hmtyP : denoteE a.store (decI mty) = some mtyP) :
    RefE (closedNV p _root_.L.Checker.nvFns = true) (tmfE p n m vis pp cao cal pfo pfl fvo fvl mty)
      (ConRon.Arena.targetMajorOf fe bs css pfvs fvs (decI mty)) a
      (fun v x a' => TmoPost dn vis fe m v.1 v.2 x a') := by
  cases n with
  | zero => rw [tmfE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n =>
  rw [tmfE.arm1, targetMajorOf_eq]
  -- the arguments
  rcases h1 : callW p n "get_app_args_f" [CWF, mty] m with _ | ⟨r1, m1⟩
  · rw [liftE_none, tmfE.k_get_app_args_f.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, tmfE.k_get_app_args_f.arm1]
  obtain ⟨s1, rfl, -, hs1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (gaaF_spec p hP.ad n _ [CWF, mty]) h1
  obtain ⟨x, a1, hrun, hS1, hg1, hd1⟩ := gaaF_ok dn vis fe CWF mty hmty m s1.mem a r1 hs1 hS
  rw [CWF_eq] at hrun
  obtain ⟨ha1, hargsP⟩ := ConRon.Bridge.Inductives.getAppArgs_run hC.check.state hmtyP hrun
  rw [ha1] at hrun hS1
  refine RefE.bind_right hrun ?_
  obtain ⟨hd1, hb1⟩ := hd1
  have hP1 : PosMR s1.mem := hPm.fr (MFr.ofGaaF hs1)
  have hA1 : AbsOK s1.mem := gaaF_afr hs1 hA
  have hC1 : StageC dn vis fe env s1.mem a := hC.of_pstep hS1 hA1 (PStep.refl hC.check.state)
  rw [getD_zero, getD_one] at hd1 hb1
  -- the head
  rcases h2 : callW p n "get_app_fn_f" [CWF, mty] s1.mem with _ | ⟨r2, m2⟩
  · rw [liftE_none, tmfE.k_get_app_fn_f.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨s2, rfl, -, hs2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩) (gafF_spec p hP.ad n _ [CWF, mty]) h2
  obtain ⟨x2, a2, hrun2, hS2, hg2, hw32, hwd⟩ := gafF_ok dn vis fe CWF mty hmty s1.mem s2.mem a r2 hs2 hS1
  rw [CWF_eq] at hrun2
  obtain ⟨ha2, hhd⟩ := ConRon.Bridge.Inductives.getAppFn_run hC1.check.state hmtyP hrun2
  rw [ha2] at hrun2 hS2
  refine RefE.bind_right hrun2 ?_
  have hP2 : PosMR s2.mem := hP1.fr (MFr.ofGafF hs2)
  have hA2 : AbsOK s2.mem := gafF_afr hs2 hA1
  have hC2 : StageC dn vis fe env s2.mem a := hC1.of_pstep hS2 hA2 (PStep.refl hC1.check.state)
  have hct := decE_tag_eq (r2.headD 0) hw32 3 (by decide)
  subst hwd
  rw [show (decI (r2.headD 0) : EIdx) = decE (r2.headD 0) from rfl] at hhd ⊢
  by_cases hng : r2.headD 0 >>> 28 ≠ 3
  · rw [tmfE.k_get_app_fn_f.abort1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hng]
    refine RefE.ite_neg (fun hc => hng (hct.mp (beq_iff_eq.mp hc))) ?_
    exact fun _ => ErrClaim.fail _ _ (by decide)
  have hg : r2.headD 0 >>> 28 = 3 := by simpa using hng
  rw [tmfE.k_get_app_fn_f.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hg]
  have htag0 : (decE (r2.headD 0)).tag = ETag.const := hct.mpr hg
  have htag : ((decE (r2.headD 0)).tag == ETag.const) = true := by simpa using htag0
  refine RefE.ite_pos htag ?_
  -- the view
  rcases h3 : callW p n "e_view" [r2.headD 0] s2.mem with _ | ⟨r3, m3⟩
  · rw [liftE_none, tmfE.k_e_view.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, tmfE.k_e_view.arm1]
  obtain ⟨s3, rfl, hs3e, hne, hr3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (eView_spec p hP.ev n _ (r2.headD 0)) h3
  have hm3 : s3.mem = s2.mem := by rw [hs3e]
  obtain ⟨hrun3, hxH, hyH⟩ := viewConstW hS2.1.arena.base (by rw [← hr3]; exact hne) hg
  rw [← hr3] at hrun3 hxH hyH
  obtain ⟨-, hvc⟩ := ConRon.Bridge.Inductives.viewConst_run hrun3
  obtain ⟨IP, usP, -, hIP, husP⟩ := ConRon.Bridge.denote_const_inv hC2.check.state.wf
    (ConRon.Bridge.view_of_viewConst_tag htag hvc.symm) hhd
  refine RefE.bind_right hrun3 ?_
  simp only
  rw [hm3]
  have hg12 := hg1.trans hg2
  exact (tmc_ref hP hIlpf hcore hLC n hS2 (hq.grow (decBS_mono _) hg12)
    (partsHsrc_grow hg12 (partsShapeFacts hq hsrc).2.1 hsrc) (hcss.grow decCNS_mono hg12)
    (hpf.grow (OMono.decHL _ _) hg12) (hfv.grow (OMono.decHL _ _) hg12) (Nat.le_trans hfvb hg12.1)
    (decHL_decB (by rw [decHL_grow hg2 hb1]; exact hd1) (Nat.le_trans hb1 hg2.1))
    (Nat.le_trans hb1 hg2.1) hxH hyH hP2 hC2 hA2 hshP hIP husP hargsP).mono
    fun _ _ _ h => ⟨h.dec, h.stage, hg12.trans h.grow, h.pos, h.abs⟩

end L.Ind
