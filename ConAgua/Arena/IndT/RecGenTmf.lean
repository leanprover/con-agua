module

public import ConRon.Bridge.Inductives.BlockParts
public import ConRon.Bridge.Inductives.PosWalks
public import ConAgua.Arena.IndRealLvlC
public import ConAgua.Arena.RecClassSpec.CrW
public import ConAgua.Arena.RecGenSpec.ClassKeyCanon
public import ConAgua.Verdict.IndBTmf
public import ConAgua.Arena.IndInstallSpec.ConsBlockCtors
public import ConAgua.Arena.DeclBasisSpec

@[expose] public section

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

/-- **The family's walk package from `(m₀, a₀)` to `(m, a)`**: the stage, `AbsOK`, `PosMR`, the
`IW` growth and the twin store's extension. -/
structure TmAt (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m₀ : Mem) (a₀ : AState) (m : Mem) (a : AState) : Prop where
  stage : StageC dn vis fe env m a
  abs : AbsOK m
  pos : PosMR m
  grow : IWGrow m₀ m
  ext : ConRon.Arena.Ext a₀.store a.store

namespace TmAt
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {m₀ m₁ m : Mem} {a₀ a₁ a : AState}

theorem trans (h₁ : TmAt dn vis fe env m₀ a₀ m₁ a₁) (h₂ : TmAt dn vis fe env m₁ a₁ m a) :
    TmAt dn vis fe env m₀ a₀ m a :=
  ⟨h₂.stage, h₂.abs, h₂.pos, h₁.grow.trans h₂.grow, h₁.ext.trans h₂.ext⟩

/-- A step that con-ron calls a `PStep`. -/
theorem pstep (h : StageC dn vis fe env m₀ a₀) (hS : StageR dn vis fe m a) (hA : AbsOK m)
    (hg : IWGrow m₀ m) (hP : PosMR m) (hp : PStep a₀ a) : TmAt dn vis fe env m₀ a₀ m a :=
  ⟨h.of_pstep hS hA hp, hA, hP, hg, hp.ext⟩

theorem decHL {k : IdxKind} (h : TmAt dn vis fe env m₀ a₀ m a) {o l : Nat} {xs : List (Idx k)}
    (hd : _root_.L.Ind.decHL m₀ o l = some xs) (hb : o + l ≤ iwTop m₀) :
    _root_.L.Ind.decHL m o l = some xs := by
  rw [decHL_grow h.grow hb]; exact hd

theorem top (h : TmAt dn vis fe env m₀ a₀ m a) {x : Nat} (hb : x ≤ iwTop m₀) : x ≤ iwTop m :=
  Nat.le_trans hb h.grow.iw

end TmAt

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
  refine RefE.bindE (fun _ => rfl) id (toi_ref hP.toi hIlpf n hC hI hus hds hdsb)
    fun ⟨r1, m1⟩ x a1 hrun hR => ?_
  dsimp only [tmtE.k_target_outside_inst]
  have hA1 := hR.afr hA
  obtain ⟨c1, v, ⟨-, hlP⟩, -⟩ := ConRon.Bridge.Inductives.targetOutsideInst_spec fe (decI I) IP
    (decI us) usP ds dsP a a1 x hC.check ⟨hIP, husP, hdsP⟩ hrun
  obtain ⟨hr1, hn1, hsH, hsd⟩ := hR.res
  have hg1 : IWGrow m m1 := hR.grow
  have hP1 : PosMR m1 := hPm.fr hR.mfr
  have hC1 : StageC dn vis fe env m1 a1 := hC.of_check hR.stage hA1 c1.ok c1.ext
  obtain ⟨-, -, hrsH, hrsd⟩ := partsShapeWords hg1 hq hq9
  have hdu : denoteL a1.store.ls (decI (r1.tail.headD 0)) = some v.2 := by rw [hsd]; exact hlP
  have hdv : denoteL a1.store.ls (decI (rdW (m1.arr64 IW) (pp + 6))) = some lr := by
    rw [hrsd]; exact ConRon.Bridge.denoteL_ext hres c1.ext
  rw [← hsd, ← hrsd]
  refine RefE.bindLift (fun _ => rfl) fun r2 m2 h2 => ?_
  obtain ⟨xl, al, hrunl, hC2, hg2, hx, hA2, -⟩ := lvlEqC_simC p hcore hLC n hC1 hA1 _ _ hsH hrsH v.2 lr
    hdu hdv r2 m2 h2
  refine ⟨_, _, hrunl, ?_⟩
  dsimp only [tmtE.k_lvl_eq_c]
  simp only [decLvlEq] at hx
  rcases xl with _ | _ | _
  · exact RefE.abortAt hx fun _ => ErrClaim.bind_left (ErrClaim.fail _ _ (by decide))
  · refine RefE.pass (by rw [hx]; decide) (RefE.abortAt (by rw [hx]; decide) fun _ => ?_)
    simp only [liftFueled, pure_bind, Bool.false_eq_true, ite_false]
    exact ErrClaim.bind_left (ErrClaim.fail _ _ (by decide))
  refine RefE.pass (by rw [hx]; decide) (RefE.pass (by rw [hx]; decide) ?_)
  simp only [liftFueled, pure_bind, ite_true]
  have hP2 : PosMR m2 := hP1.fr (MFr.of_frame (run_memFrame hcore (by decide) (run_of_callW h2)).1
    coreStageA_stage coreStageC_stage)
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r4 m4 e4 => ?_
  dsimp only [tmtE.k_mk_target_major]
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
  have hT : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.iw.iw hS.iw.iwSize
  rw [tmoE.arm1]
  unfold tmoOutT
  -- `pin_at`
  refine RefE.bindLift (fun _ => rfl) fun r1 m1 h1 => ?_
  obtain ⟨s1, rfl, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (L.Arena.pinAt_specW p hP.pin n _ 47) h1
  obtain ⟨hm1, rfl, hqH, hrun1⟩ := L.Arena.pinAtW_ok (a := a) hW1 hS.check.pins
  refine ⟨_, _, hrun1, ?_⟩
  dsimp only [tmoE.k_pin_at]
  rw [show s1.mem = m from hm1]
  refine RefE.guardThen (by decide) (fun h => by simp [h]) (fun h => (decI_inj_iff hI hqH).mp (beq_iff_eq.mp h))
    fun hIq _ => ?_
  -- `target_ctors_of`
  refine RefE.bindLift (fun _ => rfl) fun r2 m2 h2 => ?_
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
  have hnt' : ntWf (k' + 1) m vis I = some (r, m') := hnt
  obtain ⟨p2, -⟩ := ConRon.Bridge.Inductives.targetCtorsOf_spec (env := env) fe (decI I) IP a a' x
    hC.check.state ⟨hC.check.ienv.toS, hIP⟩ hrun
  have k2 := TmAt.pstep hC hS2 (ntWf_afr hnt' hA) hg2 (hPm.fr (ntWf_mfr hnt')) p2
  refine ⟨_, _, hrun, ?_⟩
  rw [← hm']
  dsimp only [tmoE.k_target_ctors_of, List.headD_cons, List.tail_cons]
  rcases x with _ | ⟨nPc, cs⟩
  · exact RefE.abortAt (by simpa [NcOut] using hout) fun _ => ErrClaim.fail _ _ (by decide)
  obtain ⟨h1, hnP, hcl, hcb, hcsat⟩ := hout
  refine RefE.pass (by rw [h1]; decide) ?_
  have hagT : decHL (truncM m) ao.toNat al.toNat = some args := hag
  have hal' := decHL_length _ hagT
  refine RefE.guardThen (by decide) (fun hal => by
      have := UInt64.lt_iff_toNat_lt.mp hal; simp only [bne_iff_ne, ne_eq, List.length_take]; omega)
    (fun h => by simp only [bne_iff_ne, ne_eq, List.length_take] at h; exact UInt64.lt_iff_toNat_lt.mpr (by omega))
    fun hal _ => ?_
  have hnal : nPc ≤ al.toNat := by
    have : ¬ al.toNat < (r.tail.headD 0).toNat := fun h => hal (UInt64.lt_iff_toNat_lt.mpr h)
    omega
  have htake : DecB (fun m => decHL m ao.toNat (r.tail.headD 0).toNat) m (args.take nPc) := by
    show decHL (truncM m) _ _ = _
    rw [hnP, decHL_take hagT _ hnal]
  have htake2 : decHL m' ao.toNat (r.tail.headD 0).toNat = some (args.take nPc) :=
    htake.stab (OMono.decHL _ _) m' hg2
  obtain ⟨hnpw, hnpb, -, -⟩ := partsShapeWords hg2 hq hq9
  -- the closedness test
  refine RefE.bindLift (fun _ => rfl) fun r3 m3 h3 => ?_
  obtain ⟨s3, rfl, -, hW3⟩ := triple_of_callW (s₀ := ⟨m', Locals.init []⟩)
    (tmoc_spec p hP.bvb hP.hf hP.tmoc (k' + 1 + 1) _ ao (r.tail.headD 0) (rdW (m'.arr64 IW) (pp + 4))) h3
  obtain ⟨b, a3, hrun3, hS3, hg3, hb3, -⟩ := ckc2W_ok dn fe vis (k' + 1 + 1) m' s3.mem a' _ ao _ _ r3 hW3 hS2
    htake2 (by have := hg2.iw; omega) (by have := hg2.iw; omega)
  rw [hnpw, UInt64.toNat_ofNat_of_lt' hnpb] at hrun3
  obtain ⟨p3, -⟩ := ConRon.Bridge.Inductives.allM_E_pstep (fun _ => True) (fun _ h => h)
    (fun e eP s₀ s' b hok _ he hrun => ConRon.Bridge.Inductives.RC.closed1_run hok he hrun)
    _ _ a' a3 b k2.stage.check.state trivial
    (ConRon.Bridge.Inductives.denoteEList_take (ConRon.Bridge.denoteEList_ext k2.ext _ _ hargsP) nPc) hrun3
  have k3 := TmAt.pstep k2.stage hS3 (ckc2W_afr _ _ _ _ _ _ _ hW3 k2.abs) hg3
    (k2.pos.fr (ckc2W_mfr _ _ _ _ _ _ _ hW3)) p3
  refine ⟨_, _, hrun3, ?_⟩
  dsimp only [tmoE.k_target_major_of_outside_closed]
  refine RefE.guardThen (by decide) (fun hz => by grind) (fun hb => by grind)
    fun _ _ => ?_
  -- the occurrence test
  rw [← hnames]
  have k23 := k2.trans k3
  refine RefE.bindLift (fun _ => rfl) fun r4 m4 h4 => ?_
  obtain ⟨s4, rfl, -, hW4⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (oc_spec p hP.occ (k' + 1 + 1) _ mno mnl ao (r.tail.headD 0)) h4
  have hT3 : iwTop s3.mem < 2 ^ 64 := Nat.lt_of_le_of_lt hS3.iw.iw hS3.iw.iwSize
  obtain ⟨b, a4, hrun4, hb4, hS4, hg4, hP4⟩ := ocW_sim hP.no mno mnl ws hwlt (k' + 1 + 1) s3.mem a3 ao _
    (args.take nPc) hS3 (slR_grow k23.grow hT hws hwsb)
    (fun i hi => k23.top (hwsb i hi)) (htake.stab (OMono.decHL _ _) s3.mem k23.grow)
    (by have := k23.grow.iw; omega) k3.pos r4 s4.mem hW4
  have hnm : Frontend.denoteNList a3.store.ns (ws.map (fun w => (decI w : NIdx))) = some pP.memberNames := by
    rw [hnames]; exact ConRon.Bridge.denoteNListE_ext k23.ext _ _
      (ConRon.Bridge.Inductives.BlockShape.memberNames_spec hshP)
  obtain ⟨p4, -⟩ := ConRon.Bridge.Inductives.anyM_E_pstep
    (fun st => Frontend.denoteNList st.ns (ws.map (fun w => (decI w : NIdx))) = some pP.memberNames)
    (fun hx h => ConRon.Bridge.denoteNListE_ext hx _ _ h)
    (fun e eP s₀ s' b hok hq he hrun => ConRon.Bridge.Inductives.nestOcc_spec _ pP.memberNames 0 0 e eP
      s₀ s' b hok ⟨hq, he⟩ hrun)
    _ _ a3 a4 b k3.stage.check.state hnm
    (ConRon.Bridge.Inductives.denoteEList_take (ConRon.Bridge.denoteEList_ext k23.ext _ _ hargsP) nPc) hrun4
  have k4 := TmAt.pstep k3.stage hS4 (ocW_afr hP.no _ _ _ _ _ _ _ _ hW4 k3.abs) hg4 hP4 p4
  refine ⟨_, _, hrun4, ?_⟩
  dsimp only [tmoE.k_target_major_of_outside_occ]
  refine RefE.guard (by decide) (fun hz => by grind) (fun hb => by grind)
    fun _ _ => ?_
  -- the tail
  have k24 := k23.trans k4
  obtain ⟨-, -, -, -, hsP, -, -⟩ := ConRon.Bridge.Inductives.dShape_inv hshP
  have hcsd := csAt_decB hcsat hcb
  rw [← hcl] at hcsd
  have := tmt_ref hP.tmt hIlpf hcore hLC (k' + 1 + 1) (bs := bs) (pfvs := pfvs) (ds := args.take nPc)
    (ctors := cs) k4.stage k4.abs (hq.grow (decBS_mono _) k24.grow) (k24.top hq9) hI hus
    (htake.grow (OMono.decHL _ _) k24.grow) (by have := k24.grow.iw; omega)
    (hcsd.grow (OMono.decPL decCN_mono _ _) (k3.grow.trans k4.grow)) (hpf.grow (OMono.decHL _ _) k24.grow) k4.pos
    (ConRon.Bridge.denoteN_ext hIP k24.ext) (ConRon.Bridge.denoteLs_ext husP k24.ext)
    (ConRon.Bridge.Inductives.denoteEList_take (ConRon.Bridge.denoteEList_ext k24.ext _ _ hargsP) nPc)
    (ConRon.Bridge.denoteL_ext hsP k24.ext)
  rw [hnP] at this
  exact this.mono fun _ _ _ h => ⟨h.dec, h.stage, k24.grow.trans h.grow, h.pos, h.abs⟩

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
  have hT : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.iw.iw hS.iw.iwSize
  obtain ⟨hqd, hq9, hptr⟩ := partsShapeFacts hq hsrc
  rw [tmcE.arm1]
  -- `block_shape_member_names`
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r4 m4 h4 => ?_
  obtain ⟨s4, rfl, rfl, hdn, hg4, hf4, ht4⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockShapeMemberNames_refines p hP.tmm.alloc hP.mnc hP.bsmn n _ pp bs hqd (by omega) hS.iw.iwSize hS.iw.ctl
      hsrc (fun o l j v h1 h2 h3 h4 => Nat.lt_of_succ_lt (hptr o l j v h1 h2 h3 h4))) h4
  dsimp only [tmcE.k_block_shape_member_names]
  obtain ⟨s4', hs4', -, hW4⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockShapeMemberNames_spec p hP.tmm.alloc hP.mnc hP.bsmn n _ pp) h4
  have hroom := memberNamesW_room hW4 hS.iw.iwSize
  rw [partsShapeK hqd hq9] at hroom
  have hkb : bs.k < 2 ^ 64 := by
    obtain ⟨o, l, -, hl', hg'⟩ := decAt_some (decBS_some hqd).1
    have := iwN_rdW hl' (by omega); rw [BlockShape.k, decPL_length _ hg']; exact this.2
  rw [UInt64.toNat_ofNat_of_lt' hkb] at hroom
  have hS4 : StageR dn vis fe s4.mem a := stage_frame_iw hS hf4 (by
    rw [← ht4]; simp only [iwTop] at hroom ⊢; omega)
  have k4 := TmAt.pstep hC hS4 (memberNamesW_afr (hs4' ▸ hW4) hA) hg4 (hPm.fr (MFr.of_iw hf4))
    (PStep.refl hC.check.state)
  simp only [List.headD_cons, List.tail_cons]
  obtain ⟨ws, hsl, hws, hwlt⟩ := slR_of_decHL s4.mem _ _ _ hdn (by have := hS4.iw.iw; have := hS4.iw.iwSize; omega)
  rw [UInt64.ofNat_toNat] at hsl
  -- `sl_find`
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r5 m5 h5 => ?_
  obtain ⟨s5, rfl, -, hm5, hW5⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (slFind_spec p hP.find n _ _ _ x) h5
  rw [show s5.mem = s4.mem from hm5]
  have hlen : ws.length < 2 ^ 64 := by rw [slR_length hsl]; exact UInt64.toNat_lt _
  have hr5 := findW_ok n s4.mem _ _ x r5 ws hsl hW5 hlen
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
      (hpf.grow (OMono.decHL _ _) hg4) (hfv.grow (OMono.decHL _ _) hg4) (k4.top hfvb)
      (hag.grow (OMono.decHL _ _) hg4) (k4.top hagb) hx hy k4.pos
    rw [hie] at this
    exact this.mono fun _ _ _ h => ⟨h.dec, h.stage, hg4.trans h.grow, h.pos, h.afr k4.abs⟩
  | none =>
    rw [hfi] at hr5
    subst hr5
    rw [tmcE.k_sl_find.arm2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by simp)]
    exact (tmo_ref hP.tmo hIlpf hcore hLC n (m := s4.mem) hS4 (hq.grow (decBS_mono _) hg4)
      (k4.top hq9) hsl hwlt (fun j hj => by rw [UInt64.toNat_ofNat_of_lt' hkb] at hj; omega)
      hws.symm (hag.grow (OMono.decHL _ _) hg4) (k4.top hagb) (hpf.grow (OMono.decHL _ _) hg4)
      hx hy k4.pos k4.stage k4.abs hshP hIP husP hargsP).mono
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
  refine RefE.bindLift (fun _ => rfl) fun r1 m1 h1 => ?_
  obtain ⟨s1, rfl, -, hs1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (gaaF_spec p hP.ad n _ [CWF, mty]) h1
  obtain ⟨x, a1, hrun, hS1, hg1, hd1, hb1⟩ := gaaF_ok dn vis fe CWF mty hmty m s1.mem a r1 hs1 hS
  rw [CWF_eq] at hrun
  obtain ⟨rfl, hargsP⟩ := ConRon.Bridge.Inductives.getAppArgs_run hC.check.state hmtyP hrun
  refine ⟨_, _, hrun, ?_⟩
  dsimp only [tmfE.k_get_app_args_f]
  have k1 := TmAt.pstep hC hS1 (gaaF_afr hs1 hA) hg1 (hPm.fr (MFr.ofGaaF hs1)) (PStep.refl hC.check.state)
  rw [getD_zero, getD_one] at hd1 hb1
  -- the head
  refine RefE.bindLift (fun _ => rfl) fun r2 m2 h2 => ?_
  obtain ⟨s2, rfl, -, hs2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩) (gafF_spec p hP.ad n _ [CWF, mty]) h2
  obtain ⟨x2, a2, hrun2, hS2, hg2, hw32, rfl⟩ := gafF_ok dn vis fe CWF mty hmty s1.mem s2.mem _ r2 hs2 hS1
  rw [CWF_eq] at hrun2
  obtain ⟨rfl, hhd⟩ := ConRon.Bridge.Inductives.getAppFn_run hC.check.state hmtyP hrun2
  refine ⟨_, _, hrun2, ?_⟩
  dsimp only [tmfE.k_get_app_fn_f]
  have k2 := TmAt.pstep k1.stage hS2 (gafF_afr hs2 k1.abs) hg2 (k1.pos.fr (MFr.ofGafF hs2))
    (PStep.refl hC.check.state)
  have hct := decE_tag_eq (r2.headD 0) hw32 3 (by decide)
  rw [show (decI (r2.headD 0) : EIdx) = decE (r2.headD 0) from rfl] at hhd ⊢
  refine RefE.guardIf (by decide) (fun hc => Bool.eq_false_iff.mpr fun h => hc (hct.mp (beq_iff_eq.mp h)))
    (fun hb hg => Bool.eq_false_iff.mp hb (beq_iff_eq.mpr (hct.mpr hg))) fun _ htag => ?_
  -- the view
  refine RefE.bindLift (fun _ => rfl) fun r3 m3 h3 => ?_
  obtain ⟨s3, rfl, hs3e, hne, rfl⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (eView_spec p hP.ev n _ (r2.headD 0)) h3
  obtain ⟨hrun3, hxH, hyH⟩ := viewConstW hS2.check.arena.base hne (by grind)
  obtain ⟨-, hvc⟩ := ConRon.Bridge.Inductives.viewConst_run hrun3
  obtain ⟨IP, usP, -, hIP, husP⟩ := ConRon.Bridge.denote_const_inv hC.check.state.wf
    (ConRon.Bridge.view_of_viewConst_tag htag hvc.symm) hhd
  refine ⟨_, _, hrun3, ?_⟩
  dsimp only [tmfE.k_e_view]
  rw [hs3e]
  have k12 := k1.trans k2
  exact (tmc_ref hP hIlpf hcore hLC n k2.stage.stage (hq.grow (decBS_mono _) k12.grow)
    (partsHsrc_grow k12.grow (partsShapeFacts hq hsrc).2.1 hsrc) (hcss.grow decCNS_mono k12.grow)
    (hpf.grow (OMono.decHL _ _) k12.grow) (hfv.grow (OMono.decHL _ _) k12.grow) (k12.top hfvb)
    (decHL_decB (k2.decHL hd1 hb1) (k2.top hb1)) (k2.top hb1) hxH hyH k2.pos k2.stage k2.abs hshP hIP husP
    hargsP).mono fun _ _ _ h => ⟨h.dec, h.stage, k12.grow.trans h.grow, h.pos, h.abs⟩

end L.Ind
