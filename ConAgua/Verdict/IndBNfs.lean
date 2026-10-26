import ConAgua.Verdict.IndBGrp
import ConAgua.Verdict.IndBTmn

/-!
# `classes_nfs`' error claim (lane `verdicts-b`, helper `verdicts-b-fin`, fork `nfs`)

`ClassesNfsE` (IndBGrp.lean) proved. `classes_nfs` has nested loops (the generator cannot model
it): its error model is written by hand over the ok model's pieces (`cnsW`, `ncpW`,
RecGenSpec28.lean), keeping only what an error of class `≠ 0` can come from, the
`target_major_nfs` call (`iw_alloc` is outside the verdict closure, the copy loop and the stores
fail with code `0`). The claim follows `cnsW_okC` (IndT/RecGen28.lean) step by step;
`target_major_nfs`' claim in `tmnW_okPC`'s shape (`tmnE_claimP`, a copy of `tmnE_claim`): the
classes' constructor slices are decoded without a bound on an empty slice's offset.
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false
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
  simp only [cnsEK3]; rw [if_pos h]
theorem cnsEK3_bad (h : ¬ ((nm + 9).toNat < (m.arr64 IW).size ∧ (nm + 10).toNat < (m.arr64 IW).size ∧
    (nm + 11).toNat < (m.arr64 IW).size ∧ (nm + 12).toNat < (m.arr64 IW).size ∧
    (qr + j).toNat < (m.arr64 IW).size)) :
    cnsEK3 nm mw eo el qr j rest (some m) = .error .oob := by
  simp only [cnsEK3]; rw [if_neg h]
theorem cnsEK2_none : cnsEK2 k mw eo el qr j rest none = .error .oob := rfl
theorem cnsEK2_some : cnsEK2 k mw eo el qr j rest (some (r, m)) =
    cnsEK3 (r.headD 0) mw eo el qr j rest (ncpW (k + 1) m (r.headD 0) mw 0) := rfl
theorem cnsEK1_err : cnsEK1 p k mw qr j rest (.error ε) = .error ε := rfl
theorem cnsEK1_ok : cnsEK1 p k mw qr j rest (.ok (r, m)) =
    cnsEK2 k mw (r.headD 0) (r.tail.headD 0) qr j rest (callW p k "iw_alloc" [13] m) := rfl
theorem cnsE_zero : cnsE p 0 m vis q fto ftl tblo tbll mo ml qr j = .error .outOfFuel := rfl
theorem cnsE_exit (h : ¬ j < ml) : cnsE p (k + 1) m vis q fto ftl tblo tbll mo ml qr j = .ok m := by
  simp only [cnsE]; rw [if_neg h]
theorem cnsE_step (h : j < ml) : cnsE p (k + 1) m vis q fto ftl tblo tbll mo ml qr j =
    cnsEK1 p k (rdW (m.arr64 IW) (mo + j)) qr j
      (fun m' => cnsE p k m' vis q fto ftl tblo tbll mo ml qr (j + 1))
      (callE p k "target_major_nfs" [vis, q, fto, ftl,
        rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 11), rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 12),
        rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 1), rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 2),
        rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 3), rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 6),
        rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + j) + 7), tblo, tbll] m) := by
  simp only [cnsE]; rw [if_pos h]
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

end L.Ind
