import ConAgua.Verdict.IndBGrp
import ConAgua.Verdict.IndBTmn
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# `classes_nfs`' error claim (lane `verdicts-b`, helper `verdicts-b-fin`, fork `nfs`)

`ClassesNfsE` (IndBGrp.lean) proved. `classes_nfs` has nested loops (the generator cannot model
it): its error model is written by hand over the ok model's pieces (`cnsW`, `ncpW`,
RecGenSpec/DecB.lean), keeping only what an error of class `≠ 0` can come from, the
`target_major_nfs` call (`iw_alloc` is outside the verdict closure, the copy loop and the stores
fail with code `0`). The claim follows `cnsW_okC` (IndT/RecGen28.lean) step by step;
`target_major_nfs`' claim in `tmnW_okPC`'s shape (`tmnE_claimP`, a copy of `tmnE_claim`): the
classes' constructor slices are decoded without a bound on an empty slice's offset.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep TAArgs dShape dCtors dCtorNf dMajor)
open ConRon.Bridge (CoreStep denote_ext denoteEList_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section tmn
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hnv : closedNV p _root_.L.Checker.nvFns = true) (hcE : CoreStubsE p)

include hq henv hnv hcE in
/-- **`target_major_nfs`' model error claim in `tmnW_okPC`'s shape** (the constructors decoded below
the tops without a bound on an empty slice's offset; the table's pointers those of `mb`). -/
theorem tmnE_claimP (L : TmnLook p) (mb : Mem) (n : Nat) (hn : n ≤ 2 ^ 62) : ∀ {m : Mem} {a : AState}
    {q fto ftl pfo pfl us dso dsl cto ctl nfo nfl : Word}
    {bs : BlockShape} {formerTys pfvs ds : List EIdx} {ctors : List (IConstantVal × Nat)}
    {nfs : List NestCtorNf} {pP : ConLeche.BlockShape} {formerTysP pfvsP dsP : List ConLeche.Expr}
    {usP : List ConLeche.Level} {ctorsP : List (ConLeche.ConstantVal × Nat)}
    {nfsP : List ConLeche.NestCtorNf},
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
    ∀ e, callE p n "target_major_nfs" [vis, q, fto, ftl, pfo, pfl, us, dso, dsl, cto, ctl, nfo, nfl] m = .error e →
      ErrClaim (ConRon.Arena.targetMajorNfs V fe bs formerTys pfvs (decI us) ds ctors nfs) a e := by
  induction n with
  | zero =>
    intro m a q fto ftl pfo pfl us dso dsl cto ctl nfo nfl bs formerTys pfvs ds ctors nfs pP
      formerTysP pfvsP dsP usP ctorsP nfsP hC hA hbs hus hft hftb hpf hds hct hctb hnf hptr hP hsh hftP hpfP
      husP hdsP hctP hnfP hformer hpw e hc'
    obtain ⟨e', he', h0⟩ := callE_zero p "target_major_nfs"
      [vis, q, fto, ftl, pfo, pfl, us, dso, dsl, cto, ctl, nfo, nfl] m
    rw [hc'] at he'
    cases he'
    exact ErrClaim.of_cls0 h0
  | succ n ih =>
  intro m a q fto ftl pfo pfl us dso dsl cto ctl nfo nfl bs formerTys pfvs ds ctors nfs pP
    formerTysP pfvsP dsP usP ctorsP nfsP hC hA hbs hus hft hftb hpf hds hct hctb hnf hptr hP hsh hftP hpfP
    husP hdsP hctP hnfP hformer hpw e hc'
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have he := triple_of_callE_err (tmnE_spec p L.tmn (n + 1) ⟨m, Locals.init []⟩ vis q fto ftl pfo pfl us dso dsl
    cto ctl nfo nfl) hc' (Err.code_ne_of_cls hk0)
  have hS := hC.stage
  by_cases hl : nfl = 0
  · rw [tmnE.arm1 p n m vis q fto ftl pfo pfl us dso dsl cto ctl nfo nfl hl] at he
    cases he
  rw [tmnE.arm2 p n m vis q fto ftl pfo pfl us dso dsl cto ctl nfo nfl hl] at he
  have hsz := hS.2.2.2.1
  obtain ⟨nf, nfs', rfl, hnf0, hnf'⟩ := hnf.uncons hl hsz
  obtain ⟨nfP, nfsP', rfl, hnfP, hnfsP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hnfP
  obtain ⟨ps, hps, hpb⟩ := hptr
  have hb64 := hS.lt64 hnf.2
  obtain ⟨e1, e2, hl0⟩ := slice_step hl hb64
  obtain ⟨LL, hLL⟩ : ∃ LL, nfl.toNat = LL + 1 := ⟨nfl.toNat - 1, by omega⟩
  rw [hLL, decNL_succ] at hps
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hps
  obtain ⟨v, hv, ps', hps', rfl⟩ := hps
  cases hpb with
  | cons hpv hpb' =>
  have hptr' : ∃ ps, decNL m (nfo + 1).toNat (nfl - 1).toNat = some ps ∧ PtrsB mb ps nfs' :=
    ⟨ps', by rw [e1, e2, hLL]; simpa using hps', hpb'⟩
  rw [ConRon.Arena.targetMajorNfs]
  cases h1 : callE p n "target_major_nfs" [vis, q, fto, ftl, pfo, pfl, us, dso, dsl, cto, ctl, nfo + 1, nfl - 1] m with
  | error e1 =>
    rw [h1, tmnE.k_target_major_nfs.none] at he
    cases he
    refine ErrClaim.bind_left ?_
    exact ih (by omega) hC hA hbs hus hft hftb hpf hds hct hctb hnf' hptr' hP hsh hftP hpfP husP hdsP hctP hnfsP'
      hformer hpw _ h1
  | ok q1 =>
  obtain ⟨rr, m1⟩ := q1
  rw [h1, tmnE.k_target_major_nfs.arm1] at he
  obtain ⟨s1, hs1, -, h1m⟩ := triple_of_callW (tmn_spec p L (realCall p) (realCall_spec p) n
    ⟨m, Locals.init []⟩ vis q fto ftl pfo pfl us dso dsl cto ctl (nfo + 1) (nfl - 1)) (callW_of_callE h1)
  subst hs1
  dsimp only at h1m
  obtain ⟨ys, a1, run1, hys, hC1, hg1, hP1, hA1, -⟩ := tmnW_okPC hq henv mb n (by omega) h1m hC hA hbs hus hft hftb hpf hds
    hct hctb hnf' hptr' hP hsh hftP hpfP husP hdsP hctP hnfsP' hformer hpw
  obtain ⟨c1, -⟩ := ConRon.Bridge.Inductives.targetMajorNfs_spec fe (ConRon.Bridge.CoreSpec.of_core rfl)
    henv bs pP formerTys pfvs formerTysP pfvsP (decI us) usP ds dsP ctors ctorsP hformer hpw nfs'
    nfsP' a a1 ys hC.check ⟨hsh, hftP, hpfP, husP, hdsP, hctP, hnfsP'⟩ run1
  refine ErrClaim.bind_right run1 ?_
  have hS1 := hC1.stage
  have hnfo : nfo.toNat < iwTop m := by
    have := hnf.2; have := (slice_step hl (hS.lt64 hnf.2)).2.2; omega
  have hE : rdW (s1.mem.arr64 IW) nfo = rdW (m.arr64 IW) nfo := by
    simp only [rdW]; rw [hg1.2.2.1 _ hnfo]
  generalize hEe : rdW (m.arr64 IW) nfo = ee at hE hnf0
  rw [hE] at he
  have hnf1 : DecB (fun m' => decNCN m' ee.toNat) s1.mem nf := hnf0.grow (decNCN_mono _) hg1
  have hsz1 := hS1.2.2.2.1
  obtain ⟨hcH, hcD, hlH, hlD, hdsl⟩ := decNCN_fields hnf1 hsz1
  have hct1 := hct.grow (OMono.decPL decCN_mono _ _) hg1
  cases h2 : callE p n "ctors_have_name" [cto, ctl, rdW (s1.mem.arr64 IW) ee] s1.mem with
  | error e2 =>
    rw [h2, tmnE.k_ctors_have_name.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  obtain ⟨s2, hs2, -, h2m⟩ := triple_of_callW (ctorsHaveName_spec p L.chn n ⟨s1.mem, Locals.init []⟩ cto ctl
    (rdW (s1.mem.arr64 IW) ee)) (callW_of_callE h2)
  subst hs2
  dsimp only at h2m
  obtain ⟨hm2, h2m⟩ := h2m
  obtain ⟨hany, -⟩ := chnW_ok n s1.mem cto ctl _ (r2.headD 0) ctors h2m (hct1.get (OMono.decPL decCN_mono _ _)) hcH
    hctb
  rw [hcD] at hany
  by_cases hh : r2.headD 0 = 0
  · rw [h2, tmnE.k_ctors_have_name.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hh] at he
    cases he
  rw [h2, tmnE.k_ctors_have_name.arm2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hh] at he
  rw [hm2] at he
  have ht : ctors.any (fun c => c.1.name == nf.ctor) = true := by rw [← hany]; simpa using hh
  refine ErrClaim.ite_pos (c := (ctors.any fun x => x.fst.name == nf.ctor) = true) ht ?_
  obtain ⟨-, hlvP, hedP, -⟩ := ConRon.Bridge.Inductives.RC.dCtorNf_inv
    (ConRon.Bridge.Inductives.dCtorNf_ext c1.ext _ _ hnfP)
  cases h3 : callE p n "target_class_match" [vis, q, fto, ftl, pfo, pfl, us, dso, dsl,
      rdW (s1.mem.arr64 IW) (ee + 1), rdW (s1.mem.arr64 IW) (ee + 2), rdW (s1.mem.arr64 IW) (ee + 3)] s1.mem with
  | error e3 =>
    rw [h3, tmnE.k_target_class_match.none] at he
    cases he
    refine ErrClaim.bind_left ?_
    have := CoreSpecE.of_callE (tcm_claimA hq henv hnv hcE L.tcm n (by omega) ⟨s1.mem, Locals.init []⟩ a1 q fto ftl
      pfo pfl us dso dsl _ _ _ bs formerTys pfvs ds _ hC1 hA1 (hbs.grow hg1) hus hlH
      (by rw [decHL_grow hg1 hftb]; exact hft) (by dsimp only; have := hg1.1; omega)
      (hpf.grow hg1) (hds.grow hg1) hdsl hP1
      (ConRon.Bridge.Inductives.dShape_ext c1.ext _ _ hsh) (denoteEList_ext c1.ext _ _ hftP)
      (denoteEList_ext c1.ext _ _ hpfP) (ConRon.Bridge.denoteLs_ext husP c1.ext)
      (denoteEList_ext c1.ext _ _ hdsP) (by rw [hlD]; exact hlvP) hedP hformer hpw) h3
    rwa [hlD] at this
  | ok q3 =>
  obtain ⟨rk, m3⟩ := q3
  by_cases hk : rk.headD 0 = 0
  · rw [h3, tmnE.k_target_class_match.arm1 _ _ _ _ _ _ _ hk] at he
    cases he
  rw [h3, tmnE.k_target_class_match.arm2 _ _ _ _ _ _ _ hk] at he
  cases h4 : callE p n "sl_cons" [ee, rr.headD 0, rr.tail.headD 0] m3 with
  | error e4 =>
    rw [h4, tmnE.k_sl_cons.none] at he
    cases he
    exact ErrClaim.bind_left (ErrClaim.of_callE_nv hnv (by decide +kernel) h4)
  | ok q4 =>
    rw [h4, tmnE.k_sl_cons.arm1] at he
    cases he

end tmn

/-! ## The error model of `classes_nfs` -/

section model
variable (p : Prog)

/-- After the copy loop: the record's tail and the result slot (a store out of bounds: `oob`). -/
def cnsEK3 (nm mw eo el qr j : Word) (rest : Mem → Except Err Mem) : Option Mem → Except Err Mem
  | none => .error .oob
  | some m =>
    if (nm + 9).toNat < (m.arr64 IW).size ∧ (nm + 10).toNat < (m.arr64 IW).size ∧
        (nm + 11).toNat < (m.arr64 IW).size ∧ (nm + 12).toNat < (m.arr64 IW).size ∧
        (qr + j).toNat < (m.arr64 IW).size then rest (wrTail m nm mw eo el qr j)
    else .error .oob

/-- After `iw_alloc(13)` (its failure claims nothing): the copy loop. -/
def cnsEK2 (k : Nat) (mw eo el qr j : Word) (rest : Mem → Except Err Mem) :
    Option (List Word × Mem) → Except Err Mem
  | none => .error .oob
  | some (r, m) => cnsEK3 (r.headD 0) mw eo el qr j rest (ncpW (k + 1) m (r.headD 0) mw 0)

/-- After `target_major_nfs`: its error passed on, else the fresh record. -/
def cnsEK1 (k : Nat) (mw qr j : Word) (rest : Mem → Except Err Mem) :
    Except Err (List Word × Mem) → Except Err Mem
  | .error ε => .error ε
  | .ok (r, m) => cnsEK2 k mw (r.headD 0) (r.tail.headD 0) qr j rest (callW p k "iw_alloc" [13] m)

/-- **The error model of `classes_nfs`' loop** at L fuel `k` (`cnsW` with `target_major_nfs`
through `callE`): an error of class `≠ 0` of the loop is the model's. -/
def cnsE : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Except Err Mem
  | 0, _, _, _, _, _, _, _, _, _, _, _ => .error .outOfFuel
  | k + 1, m, vis, q, fto, ftl, tblo, tbll, mo, ml, qr, j =>
    if j < ml then
      cnsEK1 p k (rdW (m.arr64 IW) (mo + j)) qr j
        (fun m' => cnsE k m' vis q fto ftl tblo tbll mo ml qr (j + 1))
        (callE p k "target_major_nfs" [vis, q, fto, ftl,
          rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 11), rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 12),
          rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 1), rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 2),
          rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 3), rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 6),
          rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 7), tblo, tbll] m)
    else .ok m

section arms
variable (k : Nat) (m : Mem) (vis q fto ftl tblo tbll mo ml qr j nm mw eo el : Word) (r : List Word)
  (rest : Mem → Except Err Mem) (ε : Err)
theorem cnsEK3_none : cnsEK3 nm mw eo el qr j rest none = .error .oob := rfl
theorem cnsEK3_ok (h : (nm + 9).toNat < (m.arr64 IW).size ∧ (nm + 10).toNat < (m.arr64 IW).size ∧
    (nm + 11).toNat < (m.arr64 IW).size ∧ (nm + 12).toNat < (m.arr64 IW).size ∧
    (qr + j).toNat < (m.arr64 IW).size) :
    cnsEK3 nm mw eo el qr j rest (some m) = rest (wrTail m nm mw eo el qr j) := by
  simp only [cnsEK3]; rw [ite_eq_left h]
theorem cnsEK3_bad (h : ¬ ((nm + 9).toNat < (m.arr64 IW).size ∧ (nm + 10).toNat < (m.arr64 IW).size ∧
    (nm + 11).toNat < (m.arr64 IW).size ∧ (nm + 12).toNat < (m.arr64 IW).size ∧
    (qr + j).toNat < (m.arr64 IW).size)) :
    cnsEK3 nm mw eo el qr j rest (some m) = .error .oob := by
  simp only [cnsEK3]; rw [ite_eq_right h]
theorem cnsEK2_none : cnsEK2 k mw eo el qr j rest none = .error .oob := rfl
theorem cnsEK2_some : cnsEK2 k mw eo el qr j rest (some (r, m)) =
    cnsEK3 (r.headD 0) mw eo el qr j rest (ncpW (k + 1) m (r.headD 0) mw 0) := rfl
theorem cnsEK1_err : cnsEK1 p k mw qr j rest (.error ε) = .error ε := rfl
theorem cnsEK1_ok : cnsEK1 p k mw qr j rest (.ok (r, m)) =
    cnsEK2 k mw (r.headD 0) (r.tail.headD 0) qr j rest (callW p k "iw_alloc" [13] m) := rfl
theorem cnsE_zero : cnsE p 0 m vis q fto ftl tblo tbll mo ml qr j = .error .outOfFuel := rfl
theorem cnsE_exit (h : ¬ j < ml) : cnsE p (k + 1) m vis q fto ftl tblo tbll mo ml qr j = .ok m := by
  simp only [cnsE]; rw [ite_eq_right h]
theorem cnsE_step (h : j < ml) : cnsE p (k + 1) m vis q fto ftl tblo tbll mo ml qr j =
    cnsEK1 p k (rdW (m.arr64 IW) (mo + j)) qr j
      (fun m' => cnsE p k m' vis q fto ftl tblo tbll mo ml qr (j + 1))
      (callE p k "target_major_nfs" [vis, q, fto, ftl,
        rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 11), rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 12),
        rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 1), rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 2),
        rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 3), rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 6),
        rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 7), tblo, tbll] m) := by
  simp only [cnsE]; rw [ite_eq_left h]
end arms

end model

attribute [ind_grind =] cnsEK3_none cnsEK3_ok cnsEK3_bad cnsEK2_none cnsEK2_some cnsEK1_err cnsEK1_ok
  cnsE_zero cnsE_exit cnsE_step

/-- `iw_alloc`'s ok model and its failures' class `0`. -/
theorem iwAlloc_specNV {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true) (k : Nat)
    (vs : List Word) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "iw_alloc" vs
    ⦃fun r s' => LocEq s' s₀ ∧ callW p k "iw_alloc" vs s₀.mem = some (r, s'.mem); fun e => e.cls = 0⦄ :=
  Triple.and_err (callW_spec p k "iw_alloc" vs s₀)
    (M.triple_of_run' (fun _ _ _ _ _ => trivial) fun _ _ _ hr =>
      M.of_run_err (P := fun _ => True) trivial hr
        (invoke_nv p hnv k "iw_alloc" (by decide +kernel) vs))

/-- The copy loop's ok model and its failures' class `0`. -/
theorem ncpLoop_specNV {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true) (f : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ exec p f ncpLoop
    ⦃fun r s' => r = .normal ∧ s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧
      s'.loc 3 = s₀.loc 3 ∧ s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧ s'.loc 6 = s₀.loc 6 ∧
      s'.loc 7 = s₀.loc 7 ∧ s'.loc 8 = s₀.loc 8 ∧ s'.loc 9 = s₀.loc 9 ∧ s'.loc 10 = s₀.loc 10 ∧
      s'.loc 11 = s₀.loc 11 ∧ s'.loc 12 = s₀.loc 12 ∧ s'.loc 13 = s₀.loc 13 ∧
      ncpW f s₀.mem (s₀.loc 13) (s₀.loc 10) (s₀.loc 14) = some s'.mem; fun e => e.cls = 0⦄ :=
  Triple.and_err (ncpLoop_spec p f s₀)
    (M.triple_of_run' (fun _ _ _ _ _ => trivial) fun _ _ _ hr =>
      M.of_run_err (P := fun _ => True) trivial hr (exec_nv p hnv f ncpLoop (by decide +kernel)))

set_option maxHeartbeats 1600000 in
theorem cnsLoop_specE {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ exec p k cnsLoop
    ⦃fun _ _ => True; fun ε => ε.cls ≠ 0 →
      cnsE p k s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6)
        (s₀.loc 7) (s₀.loc 8) (s₀.loc 9) = .error ε⦄ := by
  induction k generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ k ih =>
    rw [exec, step_while (w := cnsLoop) rfl]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih,
        callE_spec p k "target_major_nfs", iwAlloc_specNV hnv k,
        fun s => Triple.step_exec' (ncpLoop_specNV hnv (k + 1) s)] <;>
      finish (gen := 40) (instances := 20000) [rdW_eq, wrTail, Err.cls]

/-- After the result slice's allocation: the loop. -/
def cnfsEK1 (p : Prog) (n : Nat) (vis q fto ftl tblo tbll mo ml : Word) :
    Option (List Word × Mem) → Except Err Mem
  | none => .error .oob
  | some (r, m) => cnsE p (n + 1) m vis q fto ftl tblo tbll mo ml (r.headD 0) 0

/-- **The error model of `classes_nfs`** (exec fuel `n + 1`). -/
def cnfsE (p : Prog) (n : Nat) (m : Mem) (vis q fto ftl tblo tbll mo ml : Word) : Except Err Mem :=
  cnfsEK1 p n vis q fto ftl tblo tbll mo ml (callW p n "iw_alloc" [ml] m)

theorem cnfsEK1_none (p : Prog) (n : Nat) (vis q fto ftl tblo tbll mo ml : Word) :
    cnfsEK1 p n vis q fto ftl tblo tbll mo ml none = .error .oob := rfl
theorem cnfsEK1_some (p : Prog) (n : Nat) (vis q fto ftl tblo tbll mo ml : Word) (r : List Word) (m : Mem) :
    cnfsEK1 p n vis q fto ftl tblo tbll mo ml (some (r, m)) =
      cnsE p (n + 1) m vis q fto ftl tblo tbll mo ml (r.headD 0) 0 := rfl
theorem cnfsE_eq (p : Prog) (n : Nat) (m : Mem) (vis q fto ftl tblo tbll mo ml : Word) :
    cnfsE p n m vis q fto ftl tblo tbll mo ml =
      cnfsEK1 p n vis q fto ftl tblo tbll mo ml (callW p n "iw_alloc" [ml] m) := rfl

attribute [ind_grind =] cnfsEK1_none cnfsEK1_some

set_option maxHeartbeats 1600000 in
theorem cnfs_specE {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (hp : p.lookup "classes_nfs" = some classesNfsL) (n : Nat) (s₀ : St)
    (vis q fto ftl tblo tbll mo ml : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "classes_nfs" [vis, q, fto, ftl, tblo, tbll, mo, ml]
    ⦃fun _ _ => True; fun ε => ε.cls ≠ 0 → cnfsE p n s₀.mem vis q fto ftl tblo tbll mo ml = .error ε⦄ := by
  rw [invoke_eq _ hp, classesNfsL_eq]
  simp only [callFn, classesNfsL']
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, iwAlloc_specNV hnv n,
      fun s => Triple.step_exec' (cnsLoop_specE hnv (n + 1) s)] <;>
    finish (gen := 40) (instances := 20000) [cnfsE_eq, loc_init4, loc_init5, loc_init6, loc_init7]

section loopE
variable {p : Prog} (hkp : KnotStageProg p) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (P : CnsProg p) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
  (vis q fto ftl tblo tbll mo ml qr : Word) (bs : BlockShape) (formerTys : List EIdx)
  (tbl : List NestCtorNf) (ms : List TargetMajor) (mb : Mem)
  {pP : ConLeche.BlockShape} {formerTysP : List ConLeche.Expr} {tblP : List ConLeche.NestCtorNf}
  (hnv : closedNV p _root_.L.Checker.nvFns = true) (hcE : CoreStubsE p)
include hkp henv P hnv hcE

/-- **`classes_nfs`' loop's error claim** (`cnsW_okC`'s hypotheses, step by step): a failing loop of
class `≠ 0` is a class's `target_major_nfs`. -/
theorem cnsE_claim (hq : qr.toNat = iwTop mb) (hms : PSlR decTM ms mo ml mb) (htbl : PSlR decNCN tbl tblo tbll mb)
    (hbs : BSOK mb q.toNat bs) (hft : decHL mb fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop mb) (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (k : Nat) (hk : k ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (j : Word) (acc : List TargetMajor) (ws : List Nat)
      (MsP : List ConLeche.TargetMajor) (e : Err),
    cnsE p k m vis q fto ftl tblo tbll mo ml qr j = .error e → e.cls ≠ 0 →
    StageC dn vis fe env m a → AbsOK m → IWGrow mb m → qr.toNat + ml.toNat ≤ iwTop m → RcMR m → j ≤ ml →
    decNL m qr.toNat j.toNat = some ws → FA2 (CnsRec mb (CnsSrc mb mo ml) (qr.toNat + ml.toNat) m) ws acc →
    dShape a.store bs = some pP → Frontend.denoteEList a.store formerTys = some formerTysP →
    tbl.mapM (dCtorNf a.store) = some tblP → (ms.drop j.toNat).mapM (dMajor a.store) = some MsP →
    (∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) →
    ErrClaim (ConRon.Arena.classesNfs V fe bs formerTys tbl (ms.drop j.toNat)) a e := by
  have hms0 : decPL (truncM mb) (decTM (truncM mb)) mo.toNat ml.toNat = some ms := hms.1
  have hlen := decPL_length _ hms0
  obtain ⟨tps, -, htps, hmap⟩ := sumDecNL_of_decB htbl.1
  have htpb : PtrsB mb tps tbl := ptrsB_of_mapM hmap
  induction k with
  | zero => intro m a j acc ws MsP e h hk0; rw [cnsE_zero] at h; cases h; simp at hk0
  | succ k ih =>
  intro m a j acc ws MsP e h hk0 hC hA hg htop hP hje hws hacc hsh hftP htblP hmsP hMs
  have hS := hC.stage
  have hsz := hS.2.2.2.1
  have hjm : j.toNat ≤ ml.toNat := UInt64.le_iff_toNat_le.mp hje
  have hT := (rdW (m.arr64 CTL) 200).toNat_lt
  by_cases hj : ¬ j < ml
  · rw [cnsE_exit (h := hj)] at h; cases h
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
  rw [cnsE_step (h := hj), hrd] at h
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
  cases c1 : callE p k "target_major_nfs" [vis, q, fto, ftl,
    (rdW (m.arr64 IW) (UInt64.ofNat p0 + 11)), (rdW (m.arr64 IW) (UInt64.ofNat p0 + 12)),
    (rdW (m.arr64 IW) (UInt64.ofNat p0 + 1)), (rdW (m.arr64 IW) (UInt64.ofNat p0 + 2)),
    (rdW (m.arr64 IW) (UInt64.ofNat p0 + 3)), (rdW (m.arr64 IW) (UInt64.ofNat p0 + 6)),
    (rdW (m.arr64 IW) (UInt64.ofNat p0 + 7)), tblo, tbll] m with
  | error e1 =>
    rw [c1, cnsEK1_err] at h
    cases h
    refine ErrClaim.bind_left ?_
    have := tmnE_claimP hkp henv hnv hcE P.tmn mb k (by omega) hC hA
      (hbs.grow hg) hlH (by rw [decHL_grow hg hftb]; exact hft) (by have := hg.1; omega) hpfS hdsS hctB hctb
      (htbl.grow (fun q => decNCN_mono q) hg) ⟨tps, by rw [decNL_grow hg htbl.2]; exact htps, htpb⟩ hP
      hsh hftP hpfvsP (by rw [hlD]; exact hlvls) hdsP hctorsP htblP hformer hscp _ c1
    rwa [hlD] at this
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [c1, cnsEK1_ok] at h
  obtain ⟨s1, hs1, -, hw1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (tmn_spec p P.tmn (realCall p) (realCall_spec p) k _ vis q fto ftl
    (rdW (m.arr64 IW) (UInt64.ofNat p0 + 11)) (rdW (m.arr64 IW) (UInt64.ofNat p0 + 12))
    (rdW (m.arr64 IW) (UInt64.ofNat p0 + 1)) (rdW (m.arr64 IW) (UInt64.ofNat p0 + 2))
    (rdW (m.arr64 IW) (UInt64.ofNat p0 + 3)) (rdW (m.arr64 IW) (UInt64.ofNat p0 + 6))
    (rdW (m.arr64 IW) (UInt64.ofNat p0 + 7)) tblo tbll) (callW_of_callE c1)
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
  refine ErrClaim.bind_right run1 (ErrClaim.bind_left ?_)
  cases c2 : callW p k "iw_alloc" [13] s1.mem with
  | none => rw [c2, cnsEK2_none] at h; cases h; simp at hk0
  | some q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [c2, cnsEK2_some] at h
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
  cases c3 : ncpW (k + 1) s2.mem nm (UInt64.ofNat p0) 0 with
  | none => rw [c3, cnsEK3_none] at h; cases h; simp at hk0
  | some m3 =>
  rw [c3] at h
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
  · rw [cnsEK3_bad (h := hb)] at h; cases h; simp at hk0
  simp only [Decidable.not_not] at hb
  rw [cnsEK3_ok (h := hb)] at h
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
  have := ih (by omega) m4 a1 (j + 1) _ _ MsP' e h hk0 hC4 hA4 hg4 (by rw [ht4]; omega) hP4 hje1 hws4 hacc4
    (ConRon.Bridge.Inductives.dShape_ext c1.ext _ _ hsh) (denoteEList_ext c1.ext _ _ hftP)
    (ConRon.Bridge.Inductives.dCtorNf_ext.list c1.ext _ _ htblP)
    (by rw [hj1]; exact ConRon.Bridge.Inductives.dMajor_ext.list c1.ext _ _ hmsP')
    (fun N hN => hMs N (List.mem_cons_of_mem _ hN))
  rwa [hj1] at this

end loopE

/-- **`classes_nfs`' error claim** (`ClassesNfsE`, the hypothesis of `genRecCheck_claim'`), at
every `dn`, `vis`, `fe`, `env` (the error half of `classesNfs_refinesLpC`). -/
theorem classesNfsE_of {p : Prog} (hkp : KnotStageProg p) {env : ConLeche.Env}
    (henv : ConLeche.EnvWF env) (P : CnsProg p) (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (hcE : CoreStubsE p) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) :
    ClassesNfsE p dn vis fe env := by
  intro n hn s₀ a₀ q fto ftl tblo tbll mo ml bs formerTys tbl ms pP formerTysP tblP MsP hC hA hbs hft
    hftb htbl hms hP hlp hsh hftP htblP hmsP hformer hMs
  refine CoreSpecE.of_runs fun e hc => ?_
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  rcases n with _ | n
  · obtain ⟨e', he', h0⟩ := callE_zero p "classes_nfs" [vis, q, fto, ftl, tblo, tbll, mo, ml] s₀.mem
    rw [hc] at he'
    cases he'
    exact ErrClaim.of_cls0 h0
  have hW := triple_of_callE_err (cnfs_specE hnv P.cns n ⟨s₀.mem, Locals.init []⟩ vis q fto ftl tblo tbll mo ml)
    hc hk0
  rw [cnfsE_eq] at hW
  cases c0 : callW p n "iw_alloc" [ml] s₀.mem with
  | none => rw [c0, cnfsEK1_none] at hW; cases hW; simp at hk0
  | some q0 =>
  obtain ⟨r0, m0⟩ := q0
  rw [c0, cnfsEK1_some] at hW
  obtain ⟨s0, rfl, -, hw0⟩ := triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩) (iwAlloc_specW p P.ha n _ ml) c0
  obtain ⟨hS0, hg0, hq0, ht0⟩ := allocW_stage hw0 hC.stage
  have hA0 := allocW_afr hw0 hA
  have := cnsE_claim hkp henv P dn fe vis q fto ftl tblo tbll mo ml (r0.headD 0) bs formerTys tbl ms s₀.mem
    hnv hcE hq0 hms htbl hbs hft hftb hformer (n + 1) (by omega) s0.mem a₀ 0 [] [] MsP e hW hk0
    (hC.of_pstep hS0 hA0 (PStep.refl hC.check.state)) hA0 hg0 (by omega) (hP.fr (allocW_mfr hw0))
    UInt64.zero_le (by simp [decNL]) FA2.nil hsh hftP htblP (by simpa using hmsP) hMs
  simpa using this

end L.Ind
