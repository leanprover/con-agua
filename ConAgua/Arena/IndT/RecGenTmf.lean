import ConAgua.Arena.IndRealLvlC
import ConAgua.Arena.RecClassSpec.CrW
import ConAgua.Arena.RecGenSpec.ClassKeyCanon
import ConAgua.Arena.RecGenSpec.Tmc
import ConAgua.Arena.IndInstallSpec.ConsBlockCtors
import ConAgua.Arena.DeclBasisSpec
import ConAgua.Verdict.IndBTmm
import ConAgua.Verdict.IndBTmo

/-!
# `target_major_of` under `StageC` with the real `inst_lp_fast` (lane `indstaget`, helper `rcC`)

`AbsOK` across `target_major_of`'s callees (moved from `IndT/RecGen19.lean`); the refinements of
the outside branch for both outcomes, `tmt_ref` (`target_major_of_outside_tail`) and `tmo_ref`
(`target_major_of_outside`), with their post `TmoPost`; and the StageC versions of the other sims
(`tmcW_simC`, `tmfW_simC`; `RecGenSpec17/18`'s `tmcW_sim`, `tmfW_sim`): `StageC` and `AbsOK`
carried to `target_outside_inst`'s call by con-ron's steps of `targetMajorOf_spec`'s proof
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
  have hT : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  rw [tmoE.arm1]
  unfold tmoOutT
  -- `pin_at`
  rcases h1 : callW p n "pin_at" [47] m with _ | ⟨r1, m1⟩
  · rw [liftE_none, tmoE.k_pin_at.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨s1, rfl, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (L.Arena.pinAt_specW p hP.pin n _ 47) h1
  obtain ⟨hm1, hr1, hqH, hrun1⟩ := L.Arena.pinAtW_ok (a := a) hW1 hS.1.pins
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

theorem tmcW_simC {p : Prog} (hP : TmfProg p) (hIlpf : IlpfF p) (hcore : CoreStageClosed p)
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
    Sim (tmcW p n m vis pp cao cal pfo pfl fvo fvl ao al x y)
      (match bs.memberNames.findIdx? (· == (decI x : NIdx)) with
        | some t => tmoMemT bs css pfvs fvs args (decI x) (decI y) t
        | none => tmoOutT fe bs pfvs args (decI x) (decI y)) a
      (fun r x m' a' => DecB (fun m => decTM m (r.headD 0).toNat) m' x ∧ StageR dn vis fe m' a' ∧
        IWGrow m m' ∧ PosMR m' ∧ AbsOK m') := by
  have hT : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  obtain ⟨hqd, hq9, hptr⟩ := partsShapeFacts hq hsrc
  unfold tmcW
  refine Sim.mstep (K := tmcK1 p n vis pp cao cal pfo pfl fvo fvl ao al x y) rfl (fun _ _ => rfl) fun r4 m4 e4 => ?_
  obtain ⟨s4, rfl, hr4, hdn, hg4, hf4, ht4⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockShapeMemberNames_refines p hP.tmm.alloc hP.mnc hP.bsmn n _ pp bs hqd (by omega) hS.2.2.2.1 hS.2.2.2.2.2
      hsrc (fun o l j v h1 h2 h3 h4 => Nat.lt_of_succ_lt (hptr o l j v h1 h2 h3 h4))) e4
  obtain ⟨s4', hs4', -, hW4⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockShapeMemberNames_spec p hP.tmm.alloc hP.mnc hP.bsmn n _ pp) e4
  have hroom := memberNamesW_room hW4 hS.2.2.2.1
  rw [partsShapeK hqd hq9] at hroom
  have hkb : bs.k < 2 ^ 64 := by
    obtain ⟨o, l, -, hl', hg'⟩ := decAt_some (decBS_some hqd).1
    have := iwN_rdW hl' (by omega); rw [BlockShape.k, decPL_length _ hg']; exact this.2
  rw [UInt64.toNat_ofNat_of_lt' hkb] at hroom
  simp only at hr4 hdn hg4 hf4 ht4
  have hS4 : StageR dn vis fe s4.mem a := stage_frame_iw hS hf4 (by
    rw [← ht4]; simp only [iwTop] at hroom ⊢; omega)
  have hT4 : iwTop s4.mem < 2 ^ 64 := Nat.lt_of_le_of_lt hS4.2.1 hS4.2.2.2.1
  have hP4 : PosMR s4.mem := hPm.fr (MFr.of_iw hf4)
  have hA4 : AbsOK s4.mem := memberNamesW_afr (hs4' ▸ hW4) hA
  have hC4 : StageC dn vis fe env s4.mem a := hC.of_pstep hS4 hA4 (PStep.refl hC.check.state)
  rw [tmcK1_some, hr4]
  simp only [List.headD_cons, List.tail_cons]
  obtain ⟨ws, hsl, hws, hwlt⟩ := slR_of_decHL s4.mem _ _ _ hdn (by omega)
  rw [UInt64.ofNat_toNat] at hsl
  refine Sim.mstep (K := tmcK2 p n vis pp cao cal pfo pfl fvo fvl ao al x y _) rfl (fun _ _ => rfl)
    fun r5 m5 e5 => ?_
  obtain ⟨s5, rfl, -, hm5, hW5⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (slFind_spec p hP.find n _ _ _ x) e5
  simp only at hm5
  have hlen : ws.length < 2 ^ 64 := by rw [slR_length hsl]; exact UInt64.toNat_lt _
  have hr5 := findW_ok n s4.mem _ _ x r5 ws hsl hW5 hlen
  rw [hm5] at *
  rw [hws, findIdx_map_decI x hx ws hwlt, tmcK2_some]
  have hT4' : (rdW (m.arr64 CTL) 200).toNat + bs.k = iwTop s4.mem := ht4
  cases hfi : ws.findIdx? (· == x) with
  | some i =>
    rw [hfi] at hr5
    subst hr5
    simp only [List.headD_cons, List.tail_cons, ne_eq, show (1 : Word) ≠ 0 by decide, not_false_eq_true, ite_true]
    obtain ⟨hi, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hfi
    have hie : (UInt64.ofNat i : Word).toNat = i := UInt64.toNat_ofNat_of_lt' (show i < 2 ^ 64 by omega)
    refine Sim.post (K := tmfK6) (f := fun r => [r.headD 0]) rfl (fun _ _ => rfl)
      (Q := fun r x m' a' => DecB (fun m => decTM m (r.headD 0).toNat) m' x ∧ StageR dn vis fe m' a' ∧
        IWGrow s4.mem m' ∧ PosMR m' ∧ AbsOK m') ?_ ?_
    · intro r6 m6 e6
      obtain ⟨s6, rfl, -, x', a', hrun, hR⟩ := RefE.run_okW
        (tmmE_spec p hP.tmm n ⟨s4.mem, Locals.init []⟩ pp cao cal pfo pfl fvo fvl ao al x y (UInt64.ofNat i))
        (tmm_ref (dn := dn) (vis := vis) (fe := fe) n (t := UInt64.ofNat i) (bs := bs) (css := css) hS4
          (hq.grow (decBS_mono _) hg4) (partsHsrc_grow hg4 hq9 hsrc) (hcss.grow decCNS_mono hg4)
          (hpf.grow (OMono.decHL _ _) hg4) (hfv.grow (OMono.decHL _ _) hg4) (Nat.le_trans hfvb hg4.1)
          (hag.grow (OMono.decHL _ _) hg4) (Nat.le_trans hagb hg4.1) hx hy hP4) e6
      rw [hie] at hrun
      exact ⟨x', a', hrun, hR.dec, hR.stage, hR.grow, hR.pos, hR.afr hA4⟩
    rintro r x' m' a' ⟨h1, h2, h3, h4, h5⟩
    exact ⟨by simpa using h1, h2, hg4.trans h3, h4, h5⟩
  | none =>
    rw [hfi] at hr5
    subst hr5
    simp only [List.headD_cons, List.tail_cons, ne_eq, not_true_eq_false, ite_false]
    refine Sim.post (K := tmfK6) (f := fun r => [r.headD 0]) rfl (fun _ _ => rfl)
      (Q := fun r x m' a' => DecB (fun m => decTM m (r.headD 0).toNat) m' x ∧ StageR dn vis fe m' a' ∧
        IWGrow s4.mem m' ∧ PosMR m' ∧ AbsOK m') ?_ ?_
    · intro r6 m6 e6
      obtain ⟨s6, rfl, -, x', a', hrun, hR⟩ := RefE.run_okW
        (tmoE_spec p hP.tmo n ⟨s4.mem, Locals.init []⟩ vis pp pfo pfl x y ao al _ _)
        (tmo_ref hP.tmo hIlpf hcore hLC n (m := s4.mem) hS4 (hq.grow (decBS_mono _) hg4) (by have := hg4.1; omega)
          hsl hwlt (fun j hj => by rw [UInt64.toNat_ofNat_of_lt' hkb] at hj; omega) hws.symm
          (hag.grow (OMono.decHL _ _) hg4) (Nat.le_trans hagb hg4.1) (hpf.grow (OMono.decHL _ _) hg4) hx hy hP4
          hC4 hA4 hshP hIP husP hargsP) e6
      exact ⟨x', a', hrun, hR.dec, hR.stage, hR.grow, hR.pos, hR.abs⟩
    rintro r x' m' a' ⟨h1, h2, h3, h4, h5⟩
    exact ⟨by simpa using h1, h2, hg4.trans h3, h4, h5⟩

theorem tmfW_simC {p : Prog} (hP : TmfProg p) (hIlpf : IlpfF p) (hcore : CoreStageClosed p)
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
    Sim (tmfW p n m vis pp cao cal pfo pfl fvo fvl mty) (ConRon.Arena.targetMajorOf fe bs css pfvs fvs (decI mty)) a
      (fun r x m' a' => DecB (fun m => decTM m (r.headD 0).toNat) m' x ∧ StageR dn vis fe m' a' ∧
        IWGrow m m' ∧ PosMR m' ∧ AbsOK m') := by
  unfold tmfW
  rw [targetMajorOf_eq]
  refine Sim.bindK (K := tmfK1 p n vis pp cao cal pfo pfl fvo fvl mty) rfl (fun _ _ => rfl)
    (Q := fun r x m' a' => decRL (fun m => decHL m) 0 m' r x ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧ PosMR m' ∧
      a' = a ∧ AbsOK m' ∧ Frontend.denoteEList a.store x = some mtyP.getAppArgs)
    ?_ ?_
  · intro r1 m1 e1
    obtain ⟨s1, rfl, -, hs1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (gaaF_spec p hP.ad n _ [CWF, mty]) e1
    obtain ⟨x, a', hrun, hS1, hg1, hd1⟩ := gaaF_ok dn vis fe CWF mty hmty m s1.mem a r1 hs1 hS
    rw [CWF_eq] at hrun
    obtain ⟨ha', hargs⟩ := ConRon.Bridge.Inductives.getAppArgs_run hC.check.state hmtyP hrun
    exact ⟨x, a', hrun, hd1, hS1, hg1, hPm.fr (MFr.ofGaaF hs1), ha', gaaF_afr hs1 hA, hargs⟩
  rintro r1 args m1 a1 ⟨⟨hd1, hb1⟩, hS1, hg1, hP1, ha1, hA1, hargsP⟩
  subst a1
  have hC1 : StageC dn vis fe env m1 a := hC.of_pstep hS1 hA1 (PStep.refl hC.check.state)
  rw [getD_zero, getD_one] at hd1 hb1
  rw [tmfK1_some]
  refine Sim.bindK (K := tmfK2 p n vis pp cao cal pfo pfl fvo fvl r1) rfl (fun _ _ => rfl)
    (Q := fun r x m' a' => decW0E m' r x ∧ StageR dn vis fe m' a' ∧ IWGrow m1 m' ∧ PosMR m' ∧
      a' = a ∧ AbsOK m' ∧ denoteE a.store x = some mtyP.getAppFn) ?_ ?_
  · intro r2 m2 e2
    obtain ⟨s2, rfl, -, hs2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩) (gafF_spec p hP.ad n _ [CWF, mty]) e2
    obtain ⟨x, a', hrun, hS2, hg2, hd2⟩ := gafF_ok dn vis fe CWF mty hmty m1 s2.mem a r2 hs2 hS1
    rw [CWF_eq] at hrun
    obtain ⟨ha', hhd⟩ := ConRon.Bridge.Inductives.getAppFn_run hC1.check.state hmtyP hrun
    exact ⟨x, a', hrun, hd2, hS2, hg2, hP1.fr (MFr.ofGafF hs2), ha', gafF_afr hs2 hA1, hhd⟩
  rintro r2 hd m2 a2 ⟨⟨hw32, hwd⟩, hS2, hg2, hP2, ha2, hA2, hhdP⟩
  subst a2
  have hC2 : StageC dn vis fe env m2 a := hC1.of_pstep hS2 hA2 (PStep.refl hC1.check.state)
  rw [tmfK2_some]
  generalize hw : r2.headD 0 = w at hw32 hwd ⊢
  by_cases hng : w >>> 28 ≠ 3
  · rw [ite_eq_left hng]; exact Sim.of_none
  have hg : w >>> 28 = 3 := by simpa using hng
  rw [ite_eq_right hng]
  have hct := decE_tag_eq w hw32 3 (by decide)
  have htag0 : (decE w).tag = ETag.const := hct.mpr hg
  have htag : ((decE w).tag == ETag.const) = true := by simpa using htag0
  rw [← hwd, show (decI w : EIdx) = decE w from rfl]
  simp only [htag, ite_true]
  -- the view
  refine Sim.mstep (K := tmfK3 p n vis pp cao cal pfo pfl fvo fvl r1) rfl (fun _ _ => rfl) fun r3 m3 e3 => ?_
  obtain ⟨s3, rfl, hs3⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩) (eView_spec p hP.ev n _ w) e3
  obtain ⟨hs3e, hne, hr3⟩ := hs3
  have hm3 : s3.mem = m2 := by rw [hs3e]
  obtain ⟨hrun3, hxH, hyH⟩ := viewConstW hS2.1.arena.1 (by rw [← hr3]; exact hne) hg
  rw [← hr3] at hrun3 hxH hyH
  obtain ⟨-, hvc⟩ := ConRon.Bridge.Inductives.viewConst_run hrun3
  rw [← hwd] at hhdP
  obtain ⟨IP, usP, -, hIP, husP⟩ := ConRon.Bridge.denote_const_inv hC2.check.state.wf
    (ConRon.Bridge.view_of_viewConst_tag htag hvc.symm) hhdP
  refine Sim.bind_twin hrun3 ?_
  simp only
  rw [tmfK3_some, hm3]
  have hg12 := hg1.trans hg2
  refine Sim.post (K := tmfK6) (f := fun r => [r.headD 0]) rfl (fun _ _ => rfl)
    (Q := fun r x m' a' => DecB (fun m => decTM m (r.headD 0).toNat) m' x ∧ StageR dn vis fe m' a' ∧
      IWGrow m2 m' ∧ PosMR m' ∧ AbsOK m') ?_ ?_
  · intro r6 m6 e6
    rcases n with _ | k
    · rw [callW_zero] at e6; cases e6
    obtain ⟨s6, rfl, -, hW6⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
      (tmc_spec p hP.tmc k _ vis pp cao cal pfo pfl fvo fvl _ _ _ _) e6
    exact tmcW_simC hP hIlpf hcore hLC k hS2 (hq.grow (decBS_mono _) hg12)
      (partsHsrc_grow hg12 (partsShapeFacts hq hsrc).2.1 hsrc) (hcss.grow decCNS_mono hg12)
      (hpf.grow (OMono.decHL _ _) hg12) (hfv.grow (OMono.decHL _ _) hg12) (Nat.le_trans hfvb hg12.1)
      (decHL_decB (by rw [decHL_grow hg2 hb1]; exact hd1) (Nat.le_trans hb1 hg2.1))
      (Nat.le_trans hb1 hg2.1) hxH hyH hP2 hC2 hA2 hshP hIP husP hargsP r6 s6.mem hW6
  rintro r x' m' a' ⟨h1, h2, h3, h4, h5⟩
  exact ⟨by simpa using h1, h2, hg12.trans h3, h4, h5⟩

end L.Ind
