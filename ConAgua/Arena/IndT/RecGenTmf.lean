import ConAgua.Arena.RecGenSpec19
import ConAgua.Arena.IndT.RecCheckPins
import ConAgua.Arena.IndRealAbsPos
import ConAgua.Arena.RecClassSpecI
import ConAgua.Arena.IndSumSpec4
import ConAgua.Arena.IndInstallSpec23
import ConAgua.Arena.IlpRdReal
import ConAgua.Arena.IndRealLvlC
import ConRon.Bridge.Inductives.GenRec
import ConRon.Bridge.Inductives.RecCheck

/-!
# `target_major_of` under `StageC` with the real `inst_lp_fast` (lane `indstaget`, helper `rcC`)

`AbsOK` across `target_major_of`'s callees (moved from `IndT/RecGen19.lean`), and the StageC
versions of the outside branch's sims (`tmoW_simC`, `tmcW_simC`, `tmfW_simC`; `RecGenSpec17/18`'s
`tmoW_sim`, `tmcW_sim`, `tmfW_sim`): `StageC` and `AbsOK` carried to `target_outside_inst`'s call by
con-ron's steps of `targetMajorOf_spec`'s proof (`getAppArgs_run`, `getAppFn_run`, `viewConst_run`,
`targetCtorsOf_spec`, `allM_E_pstep` of `RC.closed1_run`, `anyM_E_pstep` of `nestOcc_spec`), so the
real `inst_lp_fast` meets its contract there (`IlpRd.realC`); after it `StageR` and `AbsOK`.
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dMajor)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `AbsOK` across `target_major_of` -/

theorem nameCopyW_afr : ∀ (n : Nat) (m m' : Mem) (d s l : Word), nameCopyW n m d s l = some m' →
    AFr m m'
  | 0, _, _, _, _, _, h => by simp [nameCopyW] at h
  | n + 1, m, m', d, s, l, h => by
    by_cases hl : l = 0
    · rw [nameCopyW_nil n m d s l hl] at h; cases h; exact AFr.refl _
    · rw [nameCopyW_step n m d s l hl] at h
      exact (set64IW_afr _ _ _).trans (nameCopyW_afr n _ _ _ _ _ h)

theorem memberNamesW_afr {n : Nat} {m m' : Mem} {p : Word} {r : List Word}
    (h : memberNamesW n m p = some (r, m')) : AFr m m' := by
  unfold memberNamesW at h
  split at h; · cases h
  rename_i q m1 hal
  split at h; · cases h
  rename_i m2 hc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact (allocW_afr hal).trans (nameCopyW_afr _ _ _ _ _ _ hc)

theorem ckc2W_afr : ∀ (n : Nat) (m m' : Mem) (nP o l : Word) (r : List Word),
    ckc2W n m nP o l = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, h => by simp [ckc2W] at h
  | n + 1, m, m', nP, o, l, r, h => by
    by_cases hl : l = 0
    · rw [ckc2W_nil n m nP o l hl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact AFr.refl _
    rw [ckc2W_cons n m nP o l hl] at h
    cases h1 : bvbW n m (rdW (m.arr64 IW) o) CWF with
    | none => rw [h1] at h; simp [ckc2K1] at h
    | some p1 =>
    obtain ⟨rb, m1⟩ := p1
    rw [h1] at h
    refine (bvbW_afr h1).trans ?_
    by_cases hb : rb ≠ 0
    · rw [ckc2K1_open (h := hb)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact AFr.refl _
    rw [ckc2K1_closed (h := hb)] at h
    cases h2 : fvbF m1 [CWF, rdW (m.arr64 IW) o] with
    | none => rw [h2] at h; simp [ckc2K2] at h
    | some p2 =>
    obtain ⟨rf, m2⟩ := p2
    rw [h2] at h
    refine (fvbF_afr h2).trans ?_
    by_cases hf : nP < rf.headD 0
    · rw [ckc2K2_open (h := hf)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact AFr.refl _
    rw [ckc2K2_closed (h := hf)] at h
    cases h3 : ckc2W n m2 nP (o + 1) (l - 1) with
    | none => rw [h3] at h; simp [ckcK3] at h
    | some p3 =>
    obtain ⟨r3, m3⟩ := p3
    rw [h3, ckcK3_some] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact ckc2W_afr n _ _ _ _ _ _ h3

theorem toiW_afr {N : Nat} {m m' : Mem} {vis I us dso dsl : Word} {r : List Word}
    (h : toiW stubCall N m vis I us dso dsl = some (r, m')) : AFr m m' := by
  cases N with
  | zero => simp [toiW] at h
  | succ N =>
  rw [toiW_eq] at h
  unfold toiK1 toiK2 toiK3 toiK4 toiK5 at h
  simp only [stubCall] at h
  afr_auto h [envFindW_afr, erToIwW_afr, stub_afr, instW_afr _ _ _ _ _ _ _, piBW_afr _ _ _ _ _ _]

section calls
variable {p : Prog} {n : Nat} {m m' : Mem} {r : List Word}

theorem gaaC_afr (hP : AdF p) {args : List Word}
    (h : callW p n "get_app_args_f" args m = some (r, m')) : AFr m m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (gaaF_spec p hP n _ args) h
  exact gaaF_afr hW

theorem gafC_afr (hP : AdF p) {args : List Word}
    (h : callW p n "get_app_fn_f" args m = some (r, m')) : AFr m m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (gafF_spec p hP n _ args) h
  exact gafF_afr hW

theorem evC_afr (hP : p.lookup "e_view" = some eView) {w : Word}
    (h : callW p n "e_view" [w] m = some (r, m')) : AFr m m' := by
  obtain ⟨s', rfl, he, -⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (eView_spec p hP n _ w) h
  rw [he]; exact AFr.refl _

theorem bsmnC_afr (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "member_names_copy" = some memberNamesCopy)
    (hp : p.lookup "block_shape_member_names" = some blockShapeMemberNames) {q : Word}
    (h : callW p n "block_shape_member_names" [q] m = some (r, m')) : AFr m m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockShapeMemberNames_spec p ha hc hp n _ q) h
  exact memberNamesW_afr hW

theorem findC_afr (hp : p.lookup "sl_find" = some slFind) {o l x : Word}
    (h : callW p n "sl_find" [o, l, x] m = some (r, m')) : AFr m m' := by
  obtain ⟨s', rfl, -, hm, -⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (slFind_spec p hp n _ o l x) h
  rw [hm]; exact AFr.refl _

theorem tmmC_afr (hP : TmmProg p) {pp cao cal pfo pfl fvo fvl ao al I us t : Word}
    (h : callW p n "target_major_of_member" [pp, cao, cal, pfo, pfl, fvo, fvl, ao, al, I, us, t] m =
      some (r, m')) : AFr m m' := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ k =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (tmm_spec p hP.mem k _ pp cao cal pfo pfl fvo fvl ao al I us t) h
  unfold tmmW at hW
  split at hW; · cases hW
  split at hW; · cases hW
  unfold tmmK1 tmmK2 tmmK3 tmmK4 at hW
  split at hW; · cases hW
  rename_i r1 m1 h1
  obtain ⟨s1, rfl, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockShapeLps_spec p hP.alloc hP.erCopy hP.erToIw hP.lps k _ pp) h1
  refine (lpsW_afr hW1).trans ?_
  split at hW; · cases hW
  rename_i r2 m2 h2
  obtain ⟨s2, rfl, -, hW2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (plW_spec p hP.alloc hP.copy hP.cons hP.get hP.pfind hP.ppush hP.iparam hP.plgo hP.pl hP.il k _ _ _) h2
  refine (plW_afr hW2).trans ?_
  split at hW; · cases hW
  rename_i r3 m3 h3
  obtain ⟨s3, rfl, -, hm3, -⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (slEq_spec p hP.eq k _ ao _ fvo _) h3
  simp only at hm3
  rw [← hm3]
  split at hW; · cases hW
  split at hW; · cases hW
  split at hW; · cases hW
  rename_i r4 m4 h4
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  rw [← hW.2]
  obtain ⟨s4, rfl, -, hW4⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (mkTargetMajor_spec p hP.alloc hP.mkTm k _ _ _ _ _ _ _ _ _ _ _ _ _ _) h4
  exact mkTMW_afr hW4

theorem pinC_afr (hp : p.lookup "pin_at" = some pinAtL) {i : Word}
    (h : callW p n "pin_at" [i] m = some (r, m')) : AFr m m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (L.Arena.pinAt_specW p hp n _ i) h
  unfold L.Arena.pinAtW at hW
  split at hW; · cases hW
  split at hW; · cases hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  rw [← hW.2]; exact AFr.refl _

theorem tcoC_afr (hl : NtLook p) (hp : p.lookup "target_ctors_of" = some targetCtorsOf) {vis I : Word}
    (h : callW p n "target_ctors_of" [vis, I] m = some (r, m')) : AFr m m' := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ k =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (tco_spec p hl hp k _ vis I) h
  unfold tcoPK at hW
  split at hW; · cases hW
  rename_i r1 m1 h1
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  rw [← hW.2]; exact ntWf_afr h1

theorem tmocC_afr (hb : BvbProg p) (hf : HfF p)
    (hp : p.lookup "target_major_of_outside_closed" = some targetMajorOfOutsideClosed) {o l nP : Word}
    (h : callW p n "target_major_of_outside_closed" [o, l, nP] m = some (r, m')) : AFr m m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (tmoc_spec p hb hf hp n _ o l nP) h
  exact ckc2W_afr _ _ _ _ _ _ _ hW

theorem noC_afr (hN : NoProg p) {no nl lo hi e : Word}
    (h : callW p n "nest_occ" [no, nl, lo, hi, e] m = some (r, m')) : AFr m m' := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ k =>
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
    cases h1 : callW p n "nest_occ" [no, nl, 0, 0, rdW (m.arr64 IW) o] m with
    | none => rw [h1] at h; simp [ocK1] at h
    | some x =>
    obtain ⟨r1, m1⟩ := x
    rw [h1] at h
    refine (noC_afr hN h1).trans ?_
    by_cases hb : r1.headD 0 ≠ 0
    · rw [ocK1_hit p n m1 no nl o l r1 hb] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact AFr.refl _
    rw [ocK1_miss p n m1 no nl o l r1 hb] at h
    cases h2 : ocW p n m1 no nl (o + 1) (l - 1) with
    | none => rw [h2] at h; simp [ocK2] at h
    | some y =>
    obtain ⟨r2, m2⟩ := y
    rw [h2, ocK2_some] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact ocW_afr hN n _ _ _ _ _ _ _ h2

theorem occC_afr (hN : NoProg p)
    (hp : p.lookup "target_major_of_outside_occ" = some targetMajorOfOutsideOcc) {no nl o l : Word}
    (h : callW p n "target_major_of_outside_occ" [no, nl, o, l] m = some (r, m')) : AFr m m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (oc_spec p hp n _ no nl o l) h
  exact ocW_afr hN _ _ _ _ _ _ _ _ hW

theorem toiC_afr (hP : ToiProg p) {vis I us dso dsl : Word}
    (h : callW p n "target_outside_inst" [vis, I, us, dso, dsl] m = some (r, m')) : AFr m m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (targetOutsideInst_spec p hP stubCall (stubCall_spec p) n _ vis I us dso dsl) h
  exact toiW_afr hW

theorem stubC_afr {f : FnName} {args : List Word} (h : callW p n f args m = some (r, m'))
    (hf : f ∈ stubNames := by decide) : AFr m m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (stubM_spec p f n _ args) h
  exact stub_afr hW hf

theorem lvlEqC_afr {args : List Word} (h : callW p n "lvl_eq_c" args m = some (r, m')) : AFr m m' :=
  stubC_afr h

theorem mkTmC_afr (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hp : p.lookup "mk_target_major" = some mkTargetMajor)
    {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : Word}
    (h : callW p n "mk_target_major" [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12] m =
      some (r, m')) : AFr m m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (mkTargetMajor_spec p ha hp n _ _ _ _ _ _ _ _ _ _ _ _ _ _) h
  exact mkTMW_afr hW

theorem tmtC_afr (hP : TmtProg p) {vis pp pfo pfl I us dso dsl cso csl : Word}
    (h : callW p n "target_major_of_outside_tail" [vis, pp, pfo, pfl, I, us, dso, dsl, cso, csl] m =
      some (r, m')) : AFr m m' := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ k =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (tmt_spec p hP.tail k _ vis pp pfo pfl I us dso dsl cso csl) h
  unfold tmtW tmtK1 tmtK2 tmtK3 at hW
  afr_auto hW [toiC_afr hP.toi, lvlEqC_afr, mkTmC_afr hP.toi.alloc hP.mkTm]

theorem tmoC_afr (hP : TmoOProg p) {vis pp pfo pfl I us ao al mno mnl : Word}
    (h : callW p n "target_major_of_outside" [vis, pp, pfo, pfl, I, us, ao, al, mno, mnl] m =
      some (r, m')) : AFr m m' := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ k =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (tmo_spec p hP.out k _ vis pp pfo pfl I us ao al mno mnl) h
  unfold tmoW tmoK1 tmoK2 tmoK2b tmoK3 tmoK4 at hW
  afr_auto hW [pinC_afr hP.pin, tcoC_afr hP.nt hP.tco, tmocC_afr hP.bvb hP.hf hP.tmoc,
    occC_afr hP.no hP.occ, tmtC_afr hP.tmt]

theorem tmcC_afr (hP : TmfProg p) {vis pp cao cal pfo pfl fvo fvl ao al x y : Word}
    (h : callW p n "target_major_of_const" [vis, pp, cao, cal, pfo, pfl, fvo, fvl, ao, al, x, y] m =
      some (r, m')) : AFr m m' := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ k =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (tmc_spec p hP.tmc k _ vis pp cao cal pfo pfl fvo fvl ao al x y) h
  unfold tmcW tmcK1 tmcK2 tmfK6 at hW
  afr_auto hW [bsmnC_afr hP.tmm.alloc hP.mnc hP.bsmn, findC_afr hP.find, tmmC_afr hP.tmm,
    tmoC_afr hP.tmo]

/-- **`AbsOK` across `target_major_of`.** -/
theorem tmfC_afr (hP : TmfProg p) {vis pp cao cal pfo pfl fvo fvl mty : Word}
    (h : callW p n "target_major_of" [vis, pp, cao, cal, pfo, pfl, fvo, fvl, mty] m = some (r, m')) :
    AFr m m' := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ k =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (tmf_spec p hP.tmf k _ vis pp cao cal pfo pfl fvo fvl mty) h
  unfold tmfW tmfK1 tmfK2 tmfK3 tmfK6 at hW
  afr_auto hW [gaaC_afr hP.ad, gafC_afr hP.ad, evC_afr hP.ev, tmcC_afr hP]

end calls

/-- `AbsOK` across `target_outside_inst`'s callees after `inst_lp_fast`. -/
theorem toiAfr : ToiAfr := fun _ _ _ _ _ _ h => piBW_afr _ _ _ _ _ _ h


/-! ## The sims under `StageC` -/

/-- **`target_major_of_outside_tail`'s model under `StageC`** (`tmtW_simG`'s, with the real
`inst_lp_fast` and `lvl_eq_c`): con-ron's `targetOutsideInst_spec` (a core step) gives `StageC` and
the instance's sort's readback after `target_outside_inst`, so `lvlEqC_simC` applies to
`lvl_eq_c`. -/
theorem tmtW_simC {p : Prog} (hP : TmtProg p) (hIlpf : IlpfF p) (hcore : CoreStageClosed p)
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
    Sim (tmtW p n m vis pp pfo pfl I us dso dsl cso csl)
      (tmoTailT fe bs pfvs ds dsl.toNat ctors (decI I) (decI us)) a
      (fun r x m' a' => DecB (fun m => decTM m (r.headD 0).toNat) m' x ∧ StageR dn vis fe m' a' ∧
        IWGrow m m' ∧ PosMR m' ∧ AbsOK m') := by
  have hS := hC.stage
  unfold tmtW tmoTailT
  refine Sim.bindK (K := tmtK1 p n pp I us dso dsl cso csl pfo pfl) rfl (fun _ _ => rfl)
    (Q := fun r x m' a' => ToiR r x ∧ StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ PosMR m' ∧ AbsOK m' ∧
      ConRon.Bridge.CoreStep V env fe a a' ∧ ∃ l, denoteL a'.store.ls x.2 = some l) ?_ ?_
  · intro r1 m1 e1
    obtain ⟨s1, rfl, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (targetOutsideInst_spec p hP.toi (realCall p) (realCall_spec p) n _ vis I us dso dsl) e1
    obtain ⟨x, a', hrun, hS1, hg1, hT1, hAF⟩ := toiW_ok (IlpRd.realC hIlpf hC) hW1 hS hI hus hds hdsb
    have hA1 := hAF toiAfr hA
    obtain ⟨c1, v, ⟨-, hlP⟩, -⟩ := ConRon.Bridge.Inductives.targetOutsideInst_spec fe (decI I) IP
      (decI us) usP ds dsP a a' x hC.check ⟨hIP, husP, hdsP⟩ hrun
    exact ⟨x, a', hrun, hT1, hC.of_check hS1 hA1 c1.ok c1.ext, hg1,
      hPm.fr (toiW_mfr (IlpFr.real hIlpf) hW1), hA1, c1, v.2, hlP⟩
  rintro r1 ⟨nIdx, sI⟩ m1 a1 ⟨⟨hr1, hn1, hsH, hsd⟩, hC1, hg1, hP1, hA1, c1, lP, hlP⟩
  obtain ⟨-, -, hrsH, hrsd⟩ := partsShapeWords hg1 hq hq9
  rw [tmtK1_some]
  refine Sim.bindK (K := tmtK2 p n I us dso dsl cso csl pfo pfl r1) rfl (fun _ _ => rfl)
    (Q := fun r x m' a' => decLvlEq m' r x ∧ StageR dn vis fe m' a' ∧ IWGrow m1 m' ∧ PosMR m' ∧
      AbsOK m') ?_ ?_
  · intro r2 m2 e2
    have hdu : denoteL a1.store.ls (decI (r1.tail.headD 0)) = some lP := by rw [hsd]; exact hlP
    have hdv : denoteL a1.store.ls (decI (rdW (m1.arr64 IW) (pp + 6))) = some lr := by
      rw [hrsd]; exact ConRon.Bridge.denoteL_ext hres c1.ext
    obtain ⟨x, a', hrun, hC2, hg2, hx, hA2, -⟩ :=
      lvlEqC_simC p hcore hLC n hC1 hA1 _ _ hsH hrsH lP lr hdu hdv r2 m2 e2
    rw [hsd, hrsd] at hrun
    exact ⟨x, a', hrun, hx, hC2.stage, hg2,
      hP1.fr (MFr.of_frame (run_memFrame hcore (by decide) (run_of_callW e2)).1 coreStageA_stage
        coreStageC_stage), hA2⟩
  rintro r2 o m2 a2 ⟨hd2, hS2, hg2, hP2, hA2⟩
  rw [tmtK2_some]
  by_cases h2 : r2.headD 0 ≠ 2
  · rw [if_pos h2]; exact Sim.of_none
  rw [if_neg h2]
  have ho : o = some true := by
    rcases o with _ | b
    · simp only [decLvlEq] at hd2; exact absurd (by rw [hd2]; decide) h2
    · cases b
      · simp only [decLvlEq] at hd2; exact absurd (by rw [hd2]; decide) h2
      · rfl
  subst ho
  simp only [liftFueled, pure_bind]
  refine Sim.mstep (K := tmtK3) rfl (fun _ _ => rfl) fun r4 m4 e4 => ?_
  have hA4 := mkTmC_afr hP.toi.alloc hP.mkTm e4 hA2
  obtain ⟨s4, rfl, -, hW4⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
    (mkTargetMajor_spec p hP.toi.alloc hP.mkTm n _ _ _ _ _ _ _ _ _ _ _ _ _ _) e4
  rw [mkTMW_eq, Option.map_eq_some_iff] at hW4
  obtain ⟨⟨q, m4'⟩, hpr, he⟩ := hW4
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨hS4, hg4, hq4, ht4, hget4⟩ := posRecW_stage hpr hS2 (by simp)
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
  have hn1' : (r1.head?.getD 0).toNat = nIdx := by simpa using hn1
  rw [hn1'] at hdec
  exact Sim.ret ⟨by simpa [decON] using hdec, hS4, hg04, hP2.fr (posRecW_mfr hpr), hA4⟩

theorem tmoW_simC {p : Prog} (hP : TmoOProg p) (hIlpf : IlpfF p) (hcore : CoreStageClosed p)
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
    Sim (tmoW p n m vis pp pfo pfl I us ao al mno mnl) (tmoOutT fe bs pfvs args (decI I) (decI us)) a
      (fun r x m' a' => DecB (fun m => decTM m (r.headD 0).toNat) m' x ∧ StageR dn vis fe m' a' ∧
        IWGrow m m' ∧ PosMR m' ∧ AbsOK m') := by
  have hT : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  unfold tmoW tmoOutT
  refine Sim.mstep (K := tmoK1 p n vis pp I us ao al pfo pfl mno mnl) rfl (fun _ _ => rfl) fun r1 m1 e1 => ?_
  obtain ⟨s1, rfl, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (L.Arena.pinAt_specW p hP.pin n _ 47) e1
  obtain ⟨hm1, hr1, hqH, hrun1⟩ := L.Arena.pinAtW_ok (a := a) hW1 hS.1.pins
  have hm1' : s1.mem = m := hm1
  simp only at hr1 hqH hrun1
  rw [hm1']
  subst hr1
  refine Sim.bind_twin (x := decI (pinW m (1 + (47 : Word).toNat))) (a₁ := a) hrun1 ?_
  rw [tmoK1_some]
  simp only [List.headD_cons]
  by_cases hIq : I = pinW m (1 + (47 : Word).toNat)
  · simp only [hIq, if_true]; exact Sim.of_none
  simp only [hIq, if_false]
  have hne : ((decI I : NIdx) == decI (pinW m (1 + (47 : Word).toNat))) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; rw [clsDecI_inj hI hqH]; exact hIq
  simp only [hne, Bool.false_eq_true, if_false]
  -- `target_ctors_of`
  refine Sim.bindK (K := tmoK2 p n vis pp I us ao al pfo pfl mno mnl) rfl (fun _ _ => rfl)
    (Q := fun r x m' a' => NcOut m' r x ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧ PosMR m' ∧
      StageC dn vis fe env m' a' ∧ AbsOK m' ∧ PStep a a') ?_ ?_
  · intro r2 m2 e2
    cases n with
    | zero => rw [callW_zero] at e2; cases e2
    | succ k =>
    obtain ⟨s2, rfl, -, hW2⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (tco_spec p hP.nt hP.tco k _ vis I) e2
    cases k with
    | zero => simp [ntWf, tcoPK] at hW2
    | succ k' =>
    cases hnt : ntW k' m vis I with
    | none => rw [show ntWf (k' + 1) _ vis I = ntW k' _ vis I from rfl, hnt] at hW2; simp [tcoPK] at hW2
    | some y =>
    obtain ⟨r, m'⟩ := y
    rw [show ntWf (k' + 1) _ vis I = ntW k' _ vis I from rfl, hnt, tcoPK_some] at hW2
    simp only [Option.some.injEq, Prod.mk.injEq] at hW2
    obtain ⟨rfl, hm'⟩ := hW2
    obtain ⟨x, a', hrun, hS2, hg2, hout⟩ := ntW_ok dn fe vis I hI k' m m' a r hnt hS
    have hf : MFr [] [] m m' := ntWf_mfr (k := k' + 1) (show ntWf (k' + 1) m vis I = some (r, m') from hnt)
    have hA2 : AbsOK m' := ntWf_afr (k := k' + 1) (show ntWf (k' + 1) m vis I = some (r, m') from hnt) hA
    obtain ⟨p2, -⟩ := ConRon.Bridge.Inductives.targetCtorsOf_spec (env := env) fe (decI I) IP a a' x
      hC.check.state ⟨hC.check.ienv.toS, hIP⟩ hrun
    have hC2 := hC.of_pstep hS2 hA2 p2
    rw [← hm']
    refine ⟨x, a', hrun, ?_, hS2, hg2, hPm.fr hf, hC2, hA2, p2⟩
    rcases x with _ | ⟨nPc, cs⟩
    · simpa [NcOut] using hout
    · simpa [NcOut] using hout
  rintro r2 x m2 a2 ⟨hnc, hS2, hg2, hP2, hC2, hA2, p2⟩
  rw [tmoK2_some]
  rcases x with _ | ⟨nPc, cs⟩
  · have h0 : r2.headD 0 = 0 := hnc
    simp only [h0, if_true]; exact Sim.of_none
  obtain ⟨h1, hnP, hcl, hcb, hcsat⟩ := hnc
  simp only [h1, show (1 : Word) ≠ 0 by decide, if_false]
  by_cases hal : al < r2.tail.headD 0
  · simp only [hal, if_true]; exact Sim.of_none
  simp only [hal, if_false]
  have hT2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
  have hnal : nPc ≤ al.toNat := by
    have : ¬ al.toNat < (r2.tail.headD 0).toNat := fun h => hal (UInt64.lt_iff_toNat_lt.mpr h)
    omega
  have hagT : decHL (truncM m) ao.toNat al.toNat = some args := hag
  have hal' := decHL_length _ hagT
  have hlen : (args.take nPc).length = nPc := by simp; omega
  simp only [hlen, bne_self_eq_false, Bool.false_eq_true, if_false]
  have htake : DecB (fun m => decHL m ao.toNat (r2.tail.headD 0).toNat) m (args.take nPc) := by
    show decHL (truncM m) _ _ = _
    rw [hnP, decHL_take hagT _ hnal]
  have htake2 : decHL m2 ao.toNat (r2.tail.headD 0).toNat = some (args.take nPc) :=
    htake.stab (OMono.decHL _ _) m2 hg2
  obtain ⟨hnpw, hnpb, -, -⟩ := partsShapeWords hg2 hq hq9
  -- the closedness test
  refine Sim.bindK (K := tmoK2b p n vis pp I us ao pfo pfl mno mnl r2) rfl (fun _ _ => rfl)
    (Q := fun r b m' a' => (r.headD 0 != 0) = b ∧ StageR dn vis fe m' a' ∧ IWGrow m2 m' ∧ PosMR m' ∧
      StageC dn vis fe env m' a' ∧ AbsOK m' ∧ PStep a2 a') ?_ ?_
  · intro r3 m3 e3
    obtain ⟨s3, rfl, -, hW3⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
      (tmoc_spec p hP.bvb hP.hf hP.tmoc n _ ao (r2.tail.headD 0) (rdW (m2.arr64 IW) (pp + 4))) e3
    obtain ⟨b, a', hrun, hS3, hg3, hb3, -⟩ := ckc2W_ok dn fe vis n m2 s3.mem a2 _ ao _ _ r3 hW3 hS2 htake2
      (by have := hg2.1; omega) (by have := hg2.1; omega)
    rw [hnpw, UInt64.toNat_ofNat_of_lt' hnpb] at hrun
    have hA3 : AbsOK s3.mem := ckc2W_afr _ _ _ _ _ _ _ hW3 hA2
    obtain ⟨p3, -⟩ := ConRon.Bridge.Inductives.allM_E_pstep (fun _ => True) (fun _ h => h)
      (fun e eP s₀ s' b hok _ he hrun => ConRon.Bridge.Inductives.RC.closed1_run hok he hrun)
      _ _ a2 a' b hC2.check.state trivial
      (ConRon.Bridge.Inductives.denoteEList_take (ConRon.Bridge.denoteEList_ext p2.ext _ _ hargsP) nPc) hrun
    exact ⟨b, a', hrun, hb3, hS3, hg3, hP2.fr (ckc2W_mfr _ _ _ _ _ _ _ hW3), hC2.of_pstep hS3 hA3 p3, hA3, p3⟩
  rintro r3 b m3 a3 ⟨hb3, hS3, hg3, hP3, hC3, hA3, p3⟩
  rw [tmoK2b_some]
  cases b with
  | false =>
    have h0 : r3.headD 0 = 0 := by simpa using hb3
    simp only [h0, if_true]; exact Sim.of_none
  | true =>
  have h0 : r3.headD 0 ≠ 0 := by simpa using hb3
  simp only [h0, if_false, Bool.not_true, Bool.false_eq_true]
  have hg03 := hg2.trans hg3
  -- the occurrence test
  rw [← hnames]
  refine Sim.bindK (K := tmoK3 p n vis pp I us ao pfo pfl r2) rfl (fun _ _ => rfl)
    (Q := fun r b m' a' => (r.headD 0 != 0) = b ∧ StageR dn vis fe m' a' ∧ IWGrow m3 m' ∧ PosMR m' ∧
      StageC dn vis fe env m' a' ∧ AbsOK m' ∧ PStep a3 a') ?_ ?_
  · intro r4 m4 e4
    obtain ⟨s4, rfl, -, hW4⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
      (oc_spec p hP.occ n _ mno mnl ao (r2.tail.headD 0)) e4
    have hT3 : iwTop m3 < 2 ^ 64 := Nat.lt_of_le_of_lt hS3.2.1 hS3.2.2.2.1
    obtain ⟨b, a', hrun, hb4, hS4', hg4', hP4'⟩ := ocW_sim hP.no mno mnl ws hwlt n m3 a3 ao _ (args.take nPc) hS3 (slR_grow (hg2.trans hg3) hT hws hwsb)
      (fun i hi => Nat.lt_of_lt_of_le (hwsb i hi) hg03.1) (htake.stab (OMono.decHL _ _) m3 hg03)
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
      _ _ a3 a' b hC3.check.state hnm
      (ConRon.Bridge.Inductives.denoteEList_take (ConRon.Bridge.denoteEList_ext hx3 _ _ hargsP) nPc) hrun
    exact ⟨b, a', hrun, hb4, hS4', hg4', hP4', hC3.of_pstep hS4' hA4 p4, hA4, p4⟩
  rintro r4 b m4 a4 ⟨hb4, hS4, hg4, hP4, hC4, hA4, p4⟩
  rw [tmoK3_some]
  cases b with
  | false =>
    have h0 : r4.headD 0 = 0 := by simpa using hb4
    simp only [h0, if_true]; exact Sim.of_none
  | true =>
  have h0 : r4.headD 0 ≠ 0 := by simpa using hb4
  simp only [h0, if_false]
  simp only [if_true]
  have hg04 := hg03.trans hg4
  -- the tail
  refine Sim.post (K := tmoK4) (f := fun r => [r.headD 0]) rfl (fun _ _ => rfl)
    (Q := fun r x m' a' => DecB (fun m => decTM m (r.headD 0).toNat) m' x ∧ StageR dn vis fe m' a' ∧
      IWGrow m4 m' ∧ PosMR m' ∧ AbsOK m') ?_ ?_
  · intro r5 m5 e5
    cases n with
    | zero => rw [callW_zero] at e5; cases e5
    | succ k =>
    obtain ⟨s5, rfl, -, hW5⟩ := triple_of_callW (s₀ := ⟨m4, Locals.init []⟩)
      (tmt_spec p hP.tmt.tail k _ vis pp pfo pfl I us ao _ _ _) e5
    have hcsd := csAt_decB hcsat hcb
    rw [← hcl] at hcsd
    have hx4 := (p2.trans (p3.trans p4)).ext
    obtain ⟨-, -, -, -, hsP, -, -⟩ := ConRon.Bridge.Inductives.dShape_inv hshP
    have := tmtW_simC hP.tmt hIlpf hcore hLC k (bs := bs) (pfvs := pfvs) (ds := args.take nPc) (ctors := cs)
      hC4 hA4 (hq.grow (decBS_mono _) hg04) (by have := hg04.1; omega) hI hus
      (htake.grow (OMono.decHL _ _) hg04) (by have := hg04.1; omega)
      (hcsd.grow (OMono.decPL decCN_mono _ _) (hg3.trans hg4)) (hpf.grow (OMono.decHL _ _) hg04) hP4
      (ConRon.Bridge.denoteN_ext hIP hx4) (ConRon.Bridge.denoteLs_ext husP hx4)
      (ConRon.Bridge.Inductives.denoteEList_take (ConRon.Bridge.denoteEList_ext hx4 _ _ hargsP) nPc)
      (ConRon.Bridge.denoteL_ext hsP hx4) r5 s5.mem hW5
    rw [hnP] at this
    exact this
  rintro r x m' a' ⟨h1, h2, h3, h4, h5⟩
  exact ⟨by simpa using h1, h2, hg04.trans h3, h4, h5⟩


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
  rw [hws, findIdx_decIP ws x hwlt hx, tmcK2_some]
  have hT4' : (rdW (m.arr64 CTL) 200).toNat + bs.k = iwTop s4.mem := ht4
  cases hfi : ws.findIdx? (· == x) with
  | some i =>
    rw [hfi] at hr5
    subst hr5
    simp only [List.headD_cons, List.tail_cons, ne_eq, show (1 : Word) ≠ 0 by decide, not_false_eq_true, if_true]
    obtain ⟨hi, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hfi
    have hie : (UInt64.ofNat i : Word).toNat = i := UInt64.toNat_ofNat_of_lt' (show i < 2 ^ 64 by omega)
    refine Sim.post (K := tmfK6) (f := fun r => [r.headD 0]) rfl (fun _ _ => rfl)
      (Q := fun r x m' a' => DecB (fun m => decTM m (r.headD 0).toNat) m' x ∧ StageR dn vis fe m' a' ∧
        IWGrow s4.mem m' ∧ PosMR m' ∧ AbsOK m') ?_ ?_
    · intro r6 m6 e6
      cases n with
      | zero => rw [callW_zero] at e6; cases e6
      | succ k =>
      obtain ⟨s6, rfl, -, hW6⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
        (tmm_spec p hP.tmm.mem k _ pp cao cal pfo pfl fvo fvl ao al x y (UInt64.ofNat i)) e6
      have := tmmW_sim hP.tmm k (t := UInt64.ofNat i) (bs := bs) (css := css) hS4 (hq.grow (decBS_mono _) hg4)
        (partsHsrc_grow hg4 hq9 hsrc) (hcss.grow decCNS_mono hg4) (hpf.grow (OMono.decHL _ _) hg4)
        (hfv.grow (OMono.decHL _ _) hg4) (Nat.le_trans hfvb hg4.1) (hag.grow (OMono.decHL _ _) hg4)
        (Nat.le_trans hagb hg4.1) hx hy hP4 r6 s6.mem hW6
      rw [hie] at this
      obtain ⟨x', a', hrun, h1, h2, h3, h4⟩ := this
      exact ⟨x', a', hrun, h1, h2, h3, h4, tmmC_afr hP.tmm e6 hA4⟩
    rintro r x' m' a' ⟨h1, h2, h3, h4, h5⟩
    exact ⟨by simpa using h1, h2, hg4.trans h3, h4, h5⟩
  | none =>
    rw [hfi] at hr5
    subst hr5
    simp only [List.headD_cons, List.tail_cons, ne_eq, not_true_eq_false, if_false]
    refine Sim.post (K := tmfK6) (f := fun r => [r.headD 0]) rfl (fun _ _ => rfl)
      (Q := fun r x m' a' => DecB (fun m => decTM m (r.headD 0).toNat) m' x ∧ StageR dn vis fe m' a' ∧
        IWGrow s4.mem m' ∧ PosMR m' ∧ AbsOK m') ?_ ?_
    · intro r6 m6 e6
      cases n with
      | zero => rw [callW_zero] at e6; cases e6
      | succ k =>
      obtain ⟨s6, rfl, -, hW6⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
        (tmo_spec p hP.tmo.out k _ vis pp pfo pfl x y ao al _ _) e6
      exact tmoW_simC hP.tmo hIlpf hcore hLC k hS4 (hq.grow (decBS_mono _) hg4) (by have := hg4.1; omega) hsl hwlt
        (fun j hj => by rw [UInt64.toNat_ofNat_of_lt' hkb] at hj; omega) hws.symm
        (hag.grow (OMono.decHL _ _) hg4) (Nat.le_trans hagb hg4.1) (hpf.grow (OMono.decHL _ _) hg4) hx hy hP4
        hC4 hA4 hshP hIP husP hargsP r6 s6.mem hW6
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
  · rw [if_pos hng]; exact Sim.of_none
  have hg : w >>> 28 = 3 := by simpa using hng
  rw [if_neg hng]
  have hct := ctag_iff w hw32 3 (by decide)
  have htag0 : (decE w).tag = ETag.const := hct.mpr hg
  have htag : ((decE w).tag == ETag.const) = true := by simpa using htag0
  rw [← hwd, show (decI w : EIdx) = decE w from rfl]
  simp only [htag, if_true]
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
    cases n with
    | zero => rw [callW_zero] at e6; cases e6
    | succ k =>
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
