module

import ConAgua.Arena.LdRd
import ConAgua.Arena.RecFireEnv
import ConAgua.Arena.WhnfIotaRefine6
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.DerRel
import ConAgua.Arena.RefWalk
import ConAgua.Arena.WhnfCoreProj
import ConAgua.Arena.WhnfCoreRefine
import ConAgua.Checker.NoVerdictTree
import ConAgua.L.ModelGen
public import ConAgua.Arena.WhnfCoreApp
public import ConAgua.Arena.WhnfIotaRecRefine
import all ConAgua.Arena.WhnfIotaRec

@[expose] public section

/-!
# `iota_rec_at`'s pieces, part 2: the certificate family, the fire, the major, the recursor

`iota_rec_fam`, `iota_rec_fire2`, `iota_rec_fire`, `iota_rec_major`, `iota_rec_c` and the top
`iota_rec_at`, each by its word-level model and a refinement in `CoreSpec` shape
(`WhnfIotaRecRefine.lean` has the twin's blocks and the inner pieces).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## `iota_rec_fam(mode, vis, d, us, recP, so, usj, ctorP, rl, mo, mn)` -/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`iota_rec_fam` refines the certificate family, both outcomes**: the errors are
`iota_rec_vck`'s. -/
theorem fam_ref (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hnF : n ≤ F) (hn62 : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d us recP so usj ctorP rl mo mn sn : Word) (lps : List NIdx)
    (rule : IRecRule) (cvj : IConstantVal) (np nf : Nat) (args margs : Array EIdx)
    (hS : CoreS dn s₀.mem a₀ vis fe MM eb) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hus : HW us) (husj : HW usj)
    (hlps : hslice? (erecP s₀.mem) (rdW (s₀.mem.arr64 EREC) (recP + 2)).toNat
      (rdW (s₀.mem.arr64 EREC) (recP + 3)).toNat = some lps)
    (hrule : decRule (erecP s₀.mem) rl.toNat = some rule)
    (hci : decCI (erecP s₀.mem) ctorP.toNat = some (.ctorInfo cvj np nf))
    (hfe : FireEnv fe lps rule cvj)
    (hsa : SpineR s₀.mem so sn args) (hsat : so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat)
    (hmI : (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat + 1 = sn.toNat)
    (hsm : SpineR s₀.mem mo mn margs) (hsmt : mo + mn = spTop s₀.mem)
    (hcpm : rule.ctorParams ≤ mn.toNat) :
    RefE (FamG p n) (irFamE p (n + 1) s₀.mem mode vis d us recP so usj ctorP rl mo mn)
      (iotaRecFamT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat
        (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat (rdW (s₀.mem.arr64 EREC) (recP + 6)).toNat lps
        (decI us) args.toList (decI usj) cvj rule margs.toList) a₀
      (CorePost decBool dn s₀.mem vis fe MM eb ResH) := by
  simp only [irFamE]
  have hspn := hS.spn
  have herec := hS.erec
  have hfc := fireCore_of hS hrule hci hfe
  have hld := lpsDen_of hS hfe
  obtain ⟨-, -, -, -, -, -, -, -, hkw⟩ := decRule_rd herec hrule
  have hcv := decCI_ctorInfo_cv hci
  have hmsz : (mo + mn).toNat = mo.toNat + mn.toNat := by
    have := hsm.bound; rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  unfold iotaRecFamT
  refine RefE.retIf (fun hv => by rw [decMode_verified mode hm4]; simpa using hv)
    (fun hvc => by rw [decMode_verified mode hm4] at hvc; simpa using hvc)
    (fun _ => CorePost.ret hS rfl (by show HW (1 : Word); unfold HW; decide)) fun _ _ => ?_
  generalize hE0 : s₀.mem.arr64 EREC = E at *
  -- the comparand levels
  refine RefE.bindLift (fun _ => rfl) fun rv m1 c1 => ?_
  obtain ⟨hrun1, ⟨M1, hS1, hK1, hSt1⟩, hr1⟩ := CoreSpec.run
    (hc.recFireLevels n ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb _ _ _ _ _ us _ _ rule lps
      cvj.levelParams hS hus (by show hslice? (erecP s₀.mem) _ _ = _; rw [hE0]; exact hlps)
      hld hfc) c1
  have e1 : m1.arr64 EREC = E := by rw [hER _ _ _ _ _ _ (by simp) c1, hE0]
  refine ⟨_, _, hrun1, ?_⟩
  simp only [irFamE.k_rec_fire_levels, e1]
  -- case 3
  refine RefE.bindLift (fun _ => rfl) fun r3 m2 c2 => ?_
  obtain ⟨hrun2, ⟨M2, hS2, hK2, hSt2⟩, hr2⟩ := CoreSpec.run
    (iotaCase3_refines p hp.toIotaProg4 hc.capsNeverZero n ⟨m1, Locals.init []⟩ _ dn vis fe M1
      eb (rdW E (rl + 9)) ctorP (rv.headD 0) rule cvj np nf hS1 hr1 hkw (by rw [e1]; exact hci)) c2
  have e2 : m2.arr64 EREC = E := by rw [hER _ _ _ _ _ _ (by simp) c2, e1]
  have hSt12 := hSt1.trans hSt2
  refine ⟨_, _, hrun2, ?_⟩
  dsimp only [irFamE.k_iota_case3]
  refine RefE.retIf decBool_f_m2c (fun h => by simpa [decBool] using h)
    (fun _ => ⟨⟨M2, hS2, hK1.trans hK2, hSt12⟩, rfl, by show HW (1 : Word); unfold HW; decide⟩) fun g0 _ => ?_
  cases n with
  | zero => exact RefE.callE_zero (fun _ => rfl)
  | succ N =>
  have hsa2 := hsa.keep hSt12.size hSt12.below hsat hspn
  have hsat2 : so.toNat + sn.toNat ≤ (spTop m2).toNat := by rw [hSt12.1]; exact hsat
  have hsm2 := hsm.keep hSt12.size hSt12.below (by rw [← hsmt, hmsz]; exact Nat.le_refl _) hspn
  have hsmt2 : mo + mn = spTop m2 := by rw [hSt12.1]; exact hsmt
  have hvk := vck_ref p hp hc hw hEI hER hEK N (hk.mono (by omega)) F (by omega) (by omega)
    ⟨m2, Locals.init []⟩ _ dn vis fe M2 eb mode d us recP so usj ctorP rl mo mn (rv.headD 0) sn lps rule
    cvj args margs hS2 hm4 hebm hus husj hr1
  simp only [e2] at hvk
  rw [← bind_pure (iotaRecVckT _ _ _ _ _ _ _ _ _ _ _ _ _)]
  refine RefE.bindRun (s₀ := ⟨m2, Locals.init []⟩) (fun _ => rfl)
    (vckE_spec p hp.vck (N + 1) ⟨m2, Locals.init []⟩ mode vis d us recP so usj ctorP rl mo mn (rv.headD 0))
    (fun hG => hG.nv) (fun hG => hG.mono (by omega)) (hvk hlps hrule hcv hsa2 hsat2 hmI hsm2 hsmt2 hcpm)
    fun rk s3 _ a3 _ _ _ ⟨⟨M3, hS3, hK3, hSt3⟩, hr3, hv3⟩ => ?_
  exact RefE.ret rfl ⟨⟨M3, hS3, hK1.trans (hK2.trans hK3), hSt12.trans hSt3⟩, hr3, hv3⟩
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`iota_rec_fam` refines the certificate family** (`fam_ref`'s ok half). -/
theorem iotaRecFam_refines' (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p)
    :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d us recP so usj ctorP rl mo mn sn : Word) (lps : List NIdx)
    (rule : IRecRule) (cvj : IConstantVal) (np nf : Nat) (args margs : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW us → HW usj →
    hslice? (erecP s₀.mem) (rdW (s₀.mem.arr64 EREC) (recP + 2)).toNat
      (rdW (s₀.mem.arr64 EREC) (recP + 3)).toNat = some lps →
    decRule (erecP s₀.mem) rl.toNat = some rule →
    decCI (erecP s₀.mem) ctorP.toNat = some (.ctorInfo cvj np nf) →
    FireEnv fe lps rule cvj →
    SpineR s₀.mem so sn args → so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat + 1 = sn.toNat →
    SpineR s₀.mem mo mn margs → mo + mn = spTop s₀.mem → rule.ctorParams ≤ mn.toNat →
    CoreSpec p (n + 1) "iota_rec_fam" [mode, vis, d, us, recP, so, usj, ctorP, rl, mo, mn]
      (iotaRecFamT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat
        (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat (rdW (s₀.mem.arr64 EREC) (recP + 6)).toNat lps
        (decI us) args.toList (decI usj) cvj rule margs.toList) decBool s₀ a₀ dn vis fe MM eb :=
  fun n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d us recP so usj ctorP rl mo mn sn lps rule cvj np nf
      args margs hS hm4 hebm hus husj hlps hrule hci hfe hsa hsat hmI hsm hsmt hcpm =>
    RefE.coreSpec (irFamE_spec p hp.fam (n + 1) s₀ mode vis d us recP so usj ctorP rl mo mn)
      (fam_ref p hp hc hw hEI hER hEK n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d us recP so usj ctorP
        rl mo mn sn lps rule cvj np nf args margs hS hm4 hebm hus husj hlps hrule hci hfe hsa hsat hmI
        hsm hsmt hcpm)
-/

/-! ## The record pool across `iota_rec_vck` and `iota_rec_fam` -/

theorem callW_iotaRecVck_erec (p : Prog) (hp : IotaRecProg' p) (hER : ErecKeptRec p)
    (hEK : ErecKeptKnot p) (n : Nat) (m : Mem) (vs : List Word) (r : List Word) (m' : Mem)
    (hvs : vs.length = 12) (h : callW p n "iota_rec_vck" vs m = some (r, m')) :
    m'.arr64 EREC = m.arr64 EREC := by
  sorry

theorem callW_iotaRecFam_erec (p : Prog) (hp : IotaRecProg' p) (hER : ErecKeptRec p)
    (hEK : ErecKeptKnot p) (n : Nat) (m : Mem) (vs : List Word) (r : List Word) (m' : Mem)
    (hvs : vs.length = 11) (h : callW p n "iota_rec_fam" vs m = some (r, m')) :
    m'.arr64 EREC = m.arr64 EREC := by
  sorry

/-! ## `mk_app_n`, `mk_app_n_from` as runs -/

theorem irCallW_mkAppN (p : Prog) (hp : SpineProg p) (n : Nat) (m : Mem) (a : AState)
    (hD : ArenaD m a) (f o k : Word) (xs : Array EIdx) (hf : HW f) (hx : SpineR m o k xs)
    (r : List Word) (m' : Mem) (h : callW p n "mk_app_n" [f, o, k] m = some (r, m')) :
    (mkAppN (decE f) xs.toList).run a = .ok (decE (r.headD 0), AM.st (mkAppN (decE f) xs.toList) a) ∧
    ArenaD m' (AM.st (mkAppN (decE f) xs.toList) a) ∧
    MemFrame [AREC, ASLOT, ADER, tier1 AREC, tier1 ASLOT, tier1 ADER] [4, 5] m m' ∧ HW (r.headD 0) := by
  obtain ⟨s', rfl, -, hok, hD', hres, hfr⟩ := triple_of_callW
    (mkAppN_refines' p hp.mkn hp.derb hp.appf hp.appp hp.appi hp.mkapp n ⟨m, Locals.init []⟩ a hD f o
      k xs hx) h
  obtain ⟨s'', hm, -, hW⟩ := triple_of_callW (mkAppNL_spec p hp.derb hp.appf hp.appp hp.appi
    hp.mkapp hp.mkn n ⟨m, Locals.init []⟩ f o k) h
  have hrun := AM.run_of_ok _ _ hok
  rw [hres] at hrun
  rw [hm] at hW
  exact ⟨hrun, hD', hfr, mkAppNFromW_hw k.toNat m a f o k 0 (by simp) hD hf _ _ hW⟩

theorem irCallW_mkAppNFrom (p : Prog) (hp : SpineProg p) (n : Nat) (m : Mem) (a : AState)
    (hD : ArenaD m a) (f o k i : Word) (xs : Array EIdx) (hf : HW f) (hx : SpineR m o k xs)
    (hik : i.toNat ≤ k.toNat) (r : List Word) (m' : Mem)
    (h : callW p n "mk_app_n_from" [f, o, k, i] m = some (r, m')) :
    (mkAppNFrom (decE f) xs i.toNat).run a =
      .ok (decE (r.headD 0), AM.st (mkAppNFrom (decE f) xs i.toNat) a) ∧
    ArenaD m' (AM.st (mkAppNFrom (decE f) xs i.toNat) a) ∧
    MemFrame [AREC, ASLOT, ADER, tier1 AREC, tier1 ASLOT, tier1 ADER] [4, 5] m m' ∧ HW (r.headD 0) := by
  obtain ⟨s', rfl, -, hok, hD', hres, hfr⟩ := triple_of_callW
    (mkAppNFrom_refines' p hp.mknf hp.derb hp.appf hp.appp hp.appi hp.mkapp n ⟨m, Locals.init []⟩ a hD
      f o k i xs hx hik) h
  obtain ⟨s'', hm, -, hW⟩ := triple_of_callW (mkAppNFromL_spec p hp.derb hp.appf hp.appp hp.appi
    hp.mkapp hp.mknf n ⟨m, Locals.init []⟩ f o k i) h
  have hrun := AM.run_of_ok _ _ hok
  rw [hres] at hrun
  rw [hm] at hW
  exact ⟨hrun, hD', hfr, mkAppNFromW_hw _ m a f o k i rfl hD hf _ _ hW⟩

theorem mkAppN_append (f : EIdx) : ∀ (xs ys : List EIdx),
    mkAppN f (xs ++ ys) = (do let g ← mkAppN f xs; mkAppN g ys)
  | [], ys => by simp [mkAppN]
  | x :: xs, ys => by
    simp only [List.cons_append, mkAppN, bind_assoc]
    congr 1; funext g; exact mkAppN_append g xs ys

/-! ## `iota_rec_fire2(mode, vis, d, c, us, recP, so, usj, ctorP, rl, mo, mn)` -/

/-- The leading-argument count of `iota_rec_fire2`: `rP`, at most the spine's `mI + 1` (the
twin's `args.take rP`). -/
def rpLen (mI rP : Word) : Word := rP - (rP - mI - 1) * Cmp.ult.evalW mI rP

theorem rpLen_toNat (mI rP : Word) : (rpLen mI rP).toNat = min rP.toNat (mI.toNat + 1) := by
  unfold rpLen Cmp.evalW
  by_cases h : mI < rP
  · have : Cmp.ult.eval mI rP = true := by simp [Cmp.eval, h]
    rw [ite_eq_left this, UInt64.mul_one]
    have h' := UInt64.lt_iff_toNat_lt.mp h
    have e1 : (rP - mI).toNat = rP.toNat - mI.toNat := UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt h)
    have e2 : (rP - mI - 1).toNat = rP.toNat - mI.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, e1]; simp; omega), e1]; simp
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, e2]; omega), e2]
    omega
  · have : Cmp.ult.eval mI rP = false := by simp [Cmp.eval, h]
    rw [ite_eq_right (by simp [this]), UInt64.mul_zero, UInt64.sub_zero]
    have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp h)
    omega

/-- **`iota_rec_fire2`'s model, both outcomes** (generated; `iota_rec_fam` through its run,
`rule_rhs_at`, `mk_app_n`, `mk_app_n_from` lifted). -/
l_model fire2E_spec (p : Prog) (hp : p.lookup "iota_rec_fire2" = some iotaRecFire2L)
  fns [hp ↦ fire2E list]
  specs [callW_spec p n "rule_rhs_at", callW_spec p n "mk_app_n", callW_spec p n "mk_app_n_from"]
  grind [arena_grind] fold [rpLen] extra [ld64_rdW_specE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

theorem decOptR_none_rec (r : List Word) (h0 : r.headD 0 = 0) : decOptR r = none := by
  unfold decOptR decOpt; rw [ite_eq_left h0]

theorem decOptR_some_rec (r : List Word) (h1 : r.headD 0 = 1) : decOptR r = some (decE (r.tail.headD 0)) := by
  unfold decOptR decOpt; rw [ite_eq_right (by rw [h1]; decide)]

theorem cpl_mkAppN (f : EIdx) (l : List EIdx) (a a' : AState) (x : EIdx)
    (h : (mkAppN f l).run a = .ok (x, a')) : cpl a' = cpl a := by
  have := keeps_cpl_mkAppNFrom f l.toArray 0
  rw [mkAppNFrom_eq_mkAppN] at this
  unfold Keeps at this
  exact this a x a' (by simpa using h)

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`iota_rec_fire2` refines the fire past the major's arguments, both outcomes**: the errors are
`iota_rec_fam`'s. -/
theorem fire2_ref (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hnF : n ≤ F) (hn62 : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d c us recP so usj ctorP rl mo mn sn : Word) (lps : List NIdx)
    (rule : IRecRule) (cvj : IConstantVal) (np nf : Nat) (args margs : Array EIdx)
    (hS : CoreS dn s₀.mem a₀ vis fe MM eb) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hcw : HW c) (hus : HW us) (husj : HW usj)
    (hlps : hslice? (erecP s₀.mem) (rdW (s₀.mem.arr64 EREC) (recP + 2)).toNat
      (rdW (s₀.mem.arr64 EREC) (recP + 3)).toNat = some lps)
    (hrule : decRule (erecP s₀.mem) rl.toNat = some rule)
    (hci : decCI (erecP s₀.mem) ctorP.toNat = some (.ctorInfo cvj np nf))
    (hfe : FireEnv fe lps rule cvj)
    (hsa : SpineR s₀.mem so sn args) (hsat : so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat)
    (hmI : (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat + 1 = sn.toNat)
    (hsm : SpineR s₀.mem mo mn margs) (hsmt : mo + mn = spTop s₀.mem) :
    RefE (FamG p n) (fire2E p (n + 1) s₀.mem mode vis d c us recP so usj ctorP rl mo mn)
      (iotaRecFire2T (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI c)
        (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat (rdW (s₀.mem.arr64 EREC) (recP + 6)).toNat lps
        (decI us) args.toList (decI usj) cvj rule margs.toList) a₀
      (CorePost decOptR dn s₀.mem vis fe MM eb ResW) := by
  simp only [fire2E]
  have hspn := hS.spn
  have herec := hS.erec
  obtain ⟨hctw, hctor, hnfw, hcpw, -, -, hrhsw, hrhs, -⟩ := decRule_rd herec hrule
  generalize hE0 : s₀.mem.arr64 EREC = E at *
  have hmsz : (mo + mn).toNat = mo.toNat + mn.toNat := by
    have := hsm.bound; rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hmsize : margs.toList.length = mn.toNat := by simp [hsm.size]
  -- the count
  have hlen_iff : margs.toList.length = rule.ctorParams + rule.nfields ↔
      ¬ mn < rdW E (rl + 2) ∧ mn - rdW E (rl + 2) = rdW E (rl + 1) := by
    rw [hmsize, hcpw, hnfw]
    constructor
    · intro h
      refine ⟨fun h' => by have := UInt64.lt_iff_toNat_lt.mp h'; omega, ?_⟩
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]; omega
    · rintro ⟨h1, h2⟩
      have h1' : (rdW E (rl + 2)).toNat ≤ mn.toNat := by
        have := UInt64.not_lt.mp h1; exact UInt64.le_iff_toNat_le.mp this
      have := congrArg UInt64.toNat h2
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr h1')] at this; omega
  have hres0 : RefE (FamG p n) (.ok ([0, 0], s₀.mem) : Except Err (List Word × Mem))
      (iotaRecFire2T (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI c)
        (rdW E (recP + 5)).toNat (rdW E (recP + 6)).toNat lps (decI us) args.toList (decI usj) cvj
        rule margs.toList) a₀ (CorePost decOptR dn s₀.mem vis fe MM eb ResW) ∨
      margs.toList.length = rule.ctorParams + rule.nfields := by
    by_cases h : margs.toList.length = rule.ctorParams + rule.nfields
    · exact .inr h
    · refine .inl (RefE.ret (by rw [iotaRecFire2T, ite_eq_right h]; rfl) ⟨⟨MM, hS, KeptAll.refl _ _,
        StackKept.refl _⟩, (decOptR_none_rec _ rfl).symm, by show ResW [0, 0]; unfold ResW HW; decide⟩)
  by_cases l1 : mn < rdW E (rl + 2)
  · rw [ite_eq_left l1]
    exact hres0.resolve_right fun h => (hlen_iff.mp h).1 l1
  rw [ite_eq_right l1]
  by_cases l2 : mn - rdW E (rl + 2) ≠ rdW E (rl + 1)
  · rw [ite_eq_left l2]
    exact hres0.resolve_right fun h => l2 (hlen_iff.mp h).2
  rw [ite_eq_right l2]
  have hlen : margs.toList.length = rule.ctorParams + rule.nfields :=
    hlen_iff.mpr ⟨l1, Classical.not_not.mp l2⟩
  have hcpm : rule.ctorParams ≤ mn.toNat := by omega
  unfold iotaRecFire2T
  rw [ite_eq_left hlen]
  simp only [mkAppN_append, bind_assoc]
  cases n with
  | zero => exact RefE.callE_zero (fun _ => rfl)
  | succ N =>
  -- the family
  have hfR := fam_ref p hp hc hw hEI hER hEK N (hk.mono (by omega)) F (by omega) (by omega)
    ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb mode d us recP so usj ctorP rl mo mn sn lps rule cvj
    np nf args margs hS hm4 hebm hus husj
  simp only [hE0] at hfR
  refine RefE.bindRun (s₀ := ⟨s₀.mem, Locals.init []⟩) (fun _ => rfl)
    (irFamE_spec p hp.fam (N + 1) ⟨s₀.mem, Locals.init []⟩ mode vis d us recP so usj ctorP rl mo mn)
    (fun hG => hG.nv) (fun hG => hG.mono (by omega)) (hfR hlps hrule hci hfe hsa hsat hmI hsm hsmt hcpm)
    fun rf s1 _ a1 c1 _ _ ⟨⟨M1, hS1, hK1, hSt1⟩, hr1, _⟩ => ?_
  have e1 : s1.mem.arr64 EREC = E := by
    rw [callW_iotaRecFam_erec p hp hER hEK _ _ _ _ _ rfl (callW_of_callE c1), hE0]
  dsimp only [fire2E.k_iota_rec_fam]
  subst hr1
  refine RefE.retIf decBool_f_m2c (fun h => by simpa [decBool] using h)
    (fun _ => ⟨⟨M1, hS1, hK1, hSt1⟩, (decOptR_none_rec _ rfl).symm, by show ResW [0, 0]; unfold ResW HW; decide⟩)
    fun g0 _ => ?_
  rw [e1]
  -- the right-hand side
  refine RefE.bindLift (fun _ => rfl) fun rr m2 c2 => ?_
  obtain ⟨ok2, ⟨M2, hS2, hK2, hSt2⟩, res2, hr2⟩ := CoreSpec.of_callW
    (ruleRhsAt_refines' p hp.toIotaProg' hw.instLP (N + 1) ⟨s1.mem, Locals.init []⟩ _ dn vis fe M1 eb c (rdW E rl)
      (rdW E (recP + 2)) (rdW E (recP + 3)) (rdW E (rl + 8)) us lps hS1 hcw hctw hrhsw hus
      (by rw [e1]; exact hlps)) c2
  have hrhs' : (decE (rdW E (rl + 8)) : EIdx) = rule.rhs := hrhs.symm
  rw [← hctor, hrhs'] at ok2 res2 hS2
  have hrun2' := AM.run_of_ok _ _ ok2
  rw [res2] at hrun2'
  simp only [decH] at hrun2'
  have hSt12 := hSt1.trans hSt2
  refine ⟨_, _, hrun2', ?_⟩
  dsimp only [fire2E.k_rule_rhs_at]
  -- the leading arguments
  have hsa2 : SpineR m2 so sn args := hsa.keep hSt12.size hSt12.below hsat hspn
  have hxa := SpineR.take hsa2 (rpLen (rdW E (recP + 5)) (rdW E (recP + 6)))
    (by rw [rpLen_toNat]; omega)
  rw [rpLen_toNat, hmI, ← hsa.size, Array.length_toList.symm,
    ← List.take_eq_take_min] at hxa
  refine RefE.bindLift (fun _ => rfl) fun rx m3 c3 => ?_
  obtain ⟨hrun3, hD3, hf3, hw3⟩ := irCallW_mkAppN p hp.spine (N + 1) m2 _ hS2.arena _ _ _ _ hr2 hxa
    rx m3 c3
  simp only at hrun3 hD3
  have hS3 := hS2.of_app hD3 (cpl_mkAppN _ _ _ _ _ hrun3) hf3
  have hSt3 := StackKept.of_app_frame hf3
  refine ⟨_, _, hrun3, ?_⟩
  dsimp only [fire2E.k_mk_app_n]
  -- the fields
  have hSt13 := hSt12.trans hSt3
  have hsm3 : SpineR m3 mo mn margs := hsm.keep hSt13.size hSt13.below (by rw [← hsmt]; omega) hspn
  refine RefE.bindLift (fun _ => rfl) fun ry m4 c4 => ?_
  obtain ⟨hrun4, hD4, hf4, hw4⟩ := irCallW_mkAppNFrom p hp.spine (N + 1) m3 _ hD3 _ _ _ _ _ hw3 hsm3
    (by rw [← hcpw]; exact hcpm) ry m4 c4
  rw [mkAppNFrom_eq_mkAppN' margs.size _ margs _ (by omega) (by rw [hsm.size, ← hcpw]; exact hcpm),
    ← hcpw] at hrun4 hD4
  have hS4 := hS3.of_app hD4 (cpl_mkAppN _ _ _ _ _ hrun4) hf4
  have hSt4 := StackKept.of_app_frame hf4
  refine ⟨_, _, hrun4, ?_⟩
  dsimp only [fire2E.k_mk_app_n_from]
  refine RefE.ret rfl ⟨⟨M2, hS4, hK1.trans hK2, hSt13.trans hSt4⟩, ?_, ?_⟩
  · rw [decOptR_some_rec _ rfl]; rfl
  · show ResW [1, ry.headD 0]; unfold ResW HW; exact ⟨by simp, hw4⟩
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`iota_rec_fire2` refines the fire past the major's arguments** (`fire2_ref`'s ok half). -/
theorem iotaRecFire2_refines' (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p)
    :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d c us recP so usj ctorP rl mo mn sn : Word) (lps : List NIdx)
    (rule : IRecRule) (cvj : IConstantVal) (np nf : Nat) (args margs : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW c → HW us → HW usj →
    hslice? (erecP s₀.mem) (rdW (s₀.mem.arr64 EREC) (recP + 2)).toNat
      (rdW (s₀.mem.arr64 EREC) (recP + 3)).toNat = some lps →
    decRule (erecP s₀.mem) rl.toNat = some rule →
    decCI (erecP s₀.mem) ctorP.toNat = some (.ctorInfo cvj np nf) →
    FireEnv fe lps rule cvj →
    SpineR s₀.mem so sn args → so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat + 1 = sn.toNat →
    SpineR s₀.mem mo mn margs → mo + mn = spTop s₀.mem →
    CoreSpec p (n + 1) "iota_rec_fire2" [mode, vis, d, c, us, recP, so, usj, ctorP, rl, mo, mn]
      (iotaRecFire2T (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI c)
        (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat (rdW (s₀.mem.arr64 EREC) (recP + 6)).toNat lps
        (decI us) args.toList (decI usj) cvj rule margs.toList) decOptR s₀ a₀ dn vis fe MM eb ResW :=
  fun n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d c us recP so usj ctorP rl mo mn sn lps rule cvj np nf
      args margs hS hm4 hebm hcw hus husj hlps hrule hci hfe hsa hsat hmI hsm hsmt =>
    RefE.coreSpec (fire2E_spec p hp.fire2 (n + 1) s₀ mode vis d c us recP so usj ctorP rl mo mn)
      (fire2_ref p hp hc hw hEI hER hEK n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d c us recP so usj
        ctorP rl mo mn sn lps rule cvj np nf args margs hS hm4 hebm hcw hus husj hlps hrule hci hfe hsa
        hsat hmI hsm hsmt)
-/

/-! ## `iota_rec_fire(mode, vis, d, c, us, recP, so, usj, ctorP, rl, major)` -/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`iota_rec_fire` refines the fire, both outcomes** (the major's arguments, then
`iotaRecFire2T`, the top put back): the errors are `iota_rec_fire2`'s. -/
theorem fire_ref (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hnF : n ≤ F) (hn62 : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d c us recP so usj ctorP rl major sn : Word) (lps : List NIdx)
    (rule : IRecRule) (cvj : IConstantVal) (np nf : Nat) (args : Array EIdx)
    (hS : CoreS dn s₀.mem a₀ vis fe MM eb) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hcw : HW c) (hus : HW us) (husj : HW usj) (hmaj : HW major)
    (hlps : hslice? (erecP s₀.mem) (rdW (s₀.mem.arr64 EREC) (recP + 2)).toNat
      (rdW (s₀.mem.arr64 EREC) (recP + 3)).toNat = some lps)
    (hrule : decRule (erecP s₀.mem) rl.toNat = some rule)
    (hci : decCI (erecP s₀.mem) ctorP.toNat = some (.ctorInfo cvj np nf))
    (hfe : FireEnv fe lps rule cvj)
    (hsa : SpineR s₀.mem so sn args) (hsat : so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat)
    (hmI : (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat + 1 = sn.toNat) :
    RefE (FamG p n) (irFireE p (n + 1) s₀.mem mode vis d c us recP so usj ctorP rl major)
      (iotaRecFireT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI c)
        (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat (rdW (s₀.mem.arr64 EREC) (recP + 6)).toNat lps
        (decI us) args.toList (decE major) (decI usj) cvj rule) a₀
      (CorePost decOptR dn s₀.mem vis fe MM eb ResW) := by
  simp only [irFireE]
  have hspn := hS.spn
  cases n with
  | zero => rw [callW_zero, liftE_none, irFireE.k_get_app_args.none]; exact RefE.of_cls0 (by simp)
  | succ N =>
  -- the major's arguments
  unfold iotaRecFireT
  refine RefE.bindLift (fun _ => rfl) fun ra m1 c1 => ?_
  obtain ⟨t1, ht1, -, fr1, gr1, hr0, htop1, xs, hrunA, hxs⟩ := triple_of_callW
    (getAppArgs_refines' p hp.spine.args hp.spine.cnt hp.spine.fill (N + 1) ⟨s₀.mem, Locals.init []⟩ a₀
      hS.arena.base major hmaj hspn) c1
  rw [ht1] at fr1 gr1 htop1 hxs
  have hS1 : CoreS dn m1 a₀ vis fe MM eb := hS.frame_stk fr1 (by simp) (by simp)
  have e1 : m1.arr64 EREC = s₀.mem.arr64 EREC := fr1.1 EREC (by simp [SPN, EREC]) (by decide)
  refine ⟨_, _, hrunA, ?_⟩
  simp only [irFireE.k_get_app_args]
  have hsa1 := hsa.keep gr1.size gr1.below hsat hspn
  have hsat1 : so.toNat + sn.toNat ≤ (spTop m1).toNat := by
    have := UInt64.le_iff_toNat_le.mp gr1.1
    have htq : (spTop ({ mem := s₀.mem, loc := Locals.init [] } : St).mem).toNat =
      (spTop s₀.mem).toNat := rfl
    omega
  have hsm1 : ra.headD 0 + ra.tail.headD 0 = spTop m1 := by rw [htop1, hr0]
  -- the fire
  have h := fire2_ref p hp hc hw hEI hER hEK N (hk.mono (by omega)) F (by omega) (by omega)
    ⟨m1, Locals.init []⟩ a₀ dn vis fe MM eb mode d c us recP so usj ctorP rl (ra.headD 0)
    (ra.tail.headD 0) sn lps rule cvj np nf args xs.toArray hS1 hm4 hebm hcw hus husj
  simp only [e1] at h
  rw [← bind_pure (iotaRecFire2T _ _ _ _ _ _ _ _ _ _ _ _ _ _)]
  refine RefE.bindRun (s₀ := ⟨m1, Locals.init []⟩) (fun _ => rfl)
    (fire2E_spec p hp.fire2 (N + 1) ⟨m1, Locals.init []⟩ mode vis d c us recP so usj ctorP rl (ra.headD 0)
      (ra.tail.headD 0)) (fun hG => hG.nv) (fun hG => hG.mono (by omega))
    (h hlps hrule hci hfe hsa1 hsat1 hmI hxs hsm1) fun rf s2 _ a2 _ _ _ hP => ?_
  obtain ⟨M2, hS2, hK2, hSt2⟩ := hP.after
  exact RefE.ret rfl ⟨⟨M2, hS2.frame_stk (MemFrame.setCtl _ _ _) (by simp) (by simp), hK2,
    StackKept.restoreG' (gr1.trans hSt2.toGrew)⟩, hP.res, hP.valid⟩
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`iota_rec_fire` refines the fire** (`fire_ref`'s ok half). -/
theorem iotaRecFire_refines' (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p)
    :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d c us recP so usj ctorP rl major sn : Word) (lps : List NIdx)
    (rule : IRecRule) (cvj : IConstantVal) (np nf : Nat) (args : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW c → HW us → HW usj →
    HW major →
    hslice? (erecP s₀.mem) (rdW (s₀.mem.arr64 EREC) (recP + 2)).toNat
      (rdW (s₀.mem.arr64 EREC) (recP + 3)).toNat = some lps →
    decRule (erecP s₀.mem) rl.toNat = some rule →
    decCI (erecP s₀.mem) ctorP.toNat = some (.ctorInfo cvj np nf) →
    FireEnv fe lps rule cvj →
    SpineR s₀.mem so sn args → so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat + 1 = sn.toNat →
    CoreSpec p (n + 1) "iota_rec_fire" [mode, vis, d, c, us, recP, so, usj, ctorP, rl, major]
      (iotaRecFireT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI c)
        (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat (rdW (s₀.mem.arr64 EREC) (recP + 6)).toNat lps
        (decI us) args.toList (decE major) (decI usj) cvj rule) decOptR s₀ a₀ dn vis fe MM eb
      ResW :=
  fun n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d c us recP so usj ctorP rl major sn lps rule cvj np
      nf args hS hm4 hebm hcw hus husj hmaj hlps hrule hci hfe hsa hsat hmI =>
    RefE.coreSpec (irFireE_spec p hp.fire (n + 1) s₀ mode vis d c us recP so usj ctorP rl major)
      (fire_ref p hp hc hw hEI hER hEK n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d c us recP so usj
        ctorP rl major sn lps rule cvj np nf args hS hm4 hebm hcw hus husj hmaj hlps hrule hci hfe hsa
        hsat hmI)
-/

/-! ## `env_find` and `intern_bvar` as runs -/

/-- **`env_find` as a run**: the memory unchanged, `find?` decoded at the record pool. -/
theorem irEnvFind (p : Prog) (hp : IotaProg' p) (n : Nat) (dn : NIdx → Option ConLeche.Name)
    (m : Mem) (vis : Word) (fe : IFEnv) (hE : EnvR m vis fe) (w : Word) (hw : HW w)
    (r : List Word) (m' : Mem) (h : callW p n "env_find" [w, vis] m = some (r, m')) :
    m' = m ∧ (r.headD 0 = 0 → fe.find? (decI w) = none) ∧
      (r.headD 0 ≠ 0 → ∃ ci, fe.find? (decI w) = some ci ∧
        decCI (erecP m) (r.tail.headD 0).toNat = some ci) := by
  sorry

/-- **`intern_bvar` under `CoreS`.** -/
theorem irCallW_internBVar (p : Prog) (hp : IotaRecProg' p) (n : Nat)
    {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {vis : Word} {fe : IFEnv}
    {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) (u : Word) (r : List Word) (m' : Mem)
    (h : callW p n "intern_bvar" [u] m = some (r, m')) :
    (internE (.bvar u.toNat)).run a = .ok (decE (r.headD 0), AM.st (internE (.bvar u.toNat)) a) ∧
    CoreS dn m' (AM.st (internE (.bvar u.toNat)) a) vis fe M eb ∧ StackKept m m' ∧
    m'.arr64 EREC = m.arr64 EREC ∧ (m'.arr64 SPN) = m.arr64 SPN := by
  obtain ⟨s', rfl, -, hm⟩ := triple_of_callW
    (internBVar_spec p hp.bvf hp.bvp hp.bvi n ⟨m, Locals.init []⟩ u) h
  obtain ⟨h1, h2, h3⟩ := internBVar_D m a hS.arena u _ _ hm
  have hfr := binternW_frame _ _ _ _ hm
  have hrun := AM.run_of_ok _ _ h1
  rw [h3] at hrun
  obtain ⟨-, hst, -⟩ := AM.of_run_ok _ _ _ _ hrun
  have hcpl : cpl (AM.st (internE (.bvar u.toNat)) a) = cpl a := by
    have := keeps_cpl_internBVar u.toNat
    unfold Keeps at this
    exact this a _ _ hrun
  refine ⟨hrun, hS.of_bvar h2 hcpl hfr, ?_, hfr.arr EREC (by simp [tier1, BREC, BSLOT, EREC]) (by decide),
    hfr.arr SPN (by simp [tier1, BREC, BSLOT, SPN]) (by decide)⟩
  have hspn : s'.mem.arr64 SPN = m.arr64 SPN := hfr.arr SPN (by simp [tier1, BREC, BSLOT, SPN]) (by decide)
  have h136 : rdW (s'.mem.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hfr.ctl 136 (by simp)
  exact StackKept.of_frame hfr

/-! ## `iota_rec_major(mode, vis, d, c, us, recP, so, sn)` -/

/-! ## `iota_rec_head(hh)` -/

/-- **`iota_rec_head` is its model `irHeadW`** (generated). -/
l_model iotaRecHead_spec (p : Prog) (hp : p.lookup "iota_rec_head" = some iotaRecHeadL)
  fns [hp ↦ irHeadW ro list]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rd_spec, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

/-- **`iota_rec_head` as a run**: the memory unchanged; another tag, or the `const` view. -/
theorem irCallW_head (p : Prog) (hp : p.lookup "iota_rec_head" = some iotaRecHeadL) (n : Nat)
    (m : Mem) (a : AState) (hR : ArenaR m a) (hh : Word) (hw : HW hh) (r : List Word) (m' : Mem)
    (h : callW p n "iota_rec_head" [hh] m = some (r, m')) :
    m' = m ∧ (r.headD 0 = 0 → (decE hh).tag ≠ ETag.const) ∧
      (r.headD 0 ≠ 0 → (decE hh).tag = ETag.const ∧
        a.store.view (decE hh) = some (.const (decI (r.tail.headD 0)) (decI (r.tail.tail.headD 0))) ∧
        HW (r.tail.headD 0) ∧ HW (r.tail.tail.headD 0)) := by
  obtain ⟨t, ht, -, hm, hW⟩ := triple_of_callW (iotaRecHead_spec p hp n ⟨m, Locals.init []⟩ hh) h
  rw [ht] at hm
  refine ⟨hm, fun h0 => ?_, fun h0 => ?_⟩
  · simp only [irHeadW] at hW
    intro htag
    have h3 : tagW hh = 3 := (decE_tag_eq _ hw 3 (by decide)).mp htag
    simp only [h3, ne_eq, not_true_eq_false, ↓reduceIte] at hW
    split at hW
    · cases hW
    split at hW
    · cases hW
    · simp only [Option.some.injEq] at hW; rw [← hW] at h0; simp at h0
  · simp only [irHeadW] at hW
    by_cases h3 : tagW hh = 3
    · simp only [h3, ne_eq, not_true_eq_false, ↓reduceIte] at hW
      obtain ⟨hv1, hW⟩ := of_ite_none hW
      obtain ⟨hv2, hW⟩ := of_ite_none hW
      simp only [Option.some.injEq] at hW
      subst hW
      obtain ⟨hvw, hn32, hu32⟩ := view_const_f m a hR hh hw ⟨hv1, UInt64.not_le.mp hv2⟩ h3
      exact ⟨(decE_tag_eq _ hw 3 (by decide)).mpr h3, hvw, hn32, hu32⟩
    · simp only [h3, ne_eq, not_false_eq_true, ↓reduceIte, Option.some.injEq] at hW
      rw [← hW] at h0; simp at h0

/-! ## `iota_rec_major(mode, vis, d, c, us, recP, so, sn)` -/

theorem view_run_of (a : AState) (h : EIdx) (v : ENodeView) (hv : a.store.view h = some v) :
    (view h).run a = .ok (v, a) := by
  simp [view, hv, StateT.run_bind, StateT.run_get]; rfl

theorem findRule_mem : ∀ (rules : List IRecRule) (c : NIdx) (rl : IRecRule),
    findRule rules c = some rl → rl ∈ rules ∧ rl.ctor = c
  | [], _, _, h => by simp [findRule] at h
  | x :: xs, c, rl, h => by
    simp only [findRule] at h
    split at h
    · rename_i hx; cases h; exact ⟨List.mem_cons_self .., by simpa using hx⟩
    · obtain ⟨h1, h2⟩ := findRule_mem xs c rl h; exact ⟨List.mem_cons_of_mem _ h1, h2⟩


/-- A found rule's record is one of the slice's: `find_rule` answers `ro + 11 * j`, `j < rc`. -/
theorem frN_found (E : Array Word) (ro rc c : Word) (i : Nat) (hne : (frN E ro rc c i).headD 0 ≠ 0) :
    ∃ j : Word, j < rc ∧ (frN E ro rc c i).tail.headD 0 = ro + 11 * j := by
  fun_induction frN E ro rc c i with
  | case1 i hi _ => exact ⟨UInt64.ofNat i, UInt64.lt_iff_toNat_lt.mpr (by have := rc.toNat_lt; simp; omega), rfl⟩
  | case2 i _ _ ih => exact ih hne
  | case3 => simp at hne

/-- **`find_rule`'s answer decodes** when it found one. -/
theorem findRule_found (p : Prog) (hp : p.lookup "find_rule" = some findRuleL) (n : Nat) (m : Mem)
    (ro rc c : Word) (rules : List IRecRule) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hr : decRules (erecP m) ro.toNat rc.toNat = some rules) (r : List Word) (m' : Mem)
    (h : callW p n "find_rule" [ro, rc, c] m = some (r, m')) (hne : r.headD 0 ≠ 0) :
    ∃ rule, decRule (erecP m) (r.tail.headD 0).toNat = some rule := by
  sorry

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- `prepare_major`'s error claim at fuel `N + 1` (the premises of `prepareMajor_refines'`). -/
def PrepareMajorE (p : Prog) : Prop :=
  ∀ (N : Nat), KnotUpTo p N → KnotUpToE p N → ∀ (F : Nat), N ≤ F → N ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d rec ro rc major : Word) (rules : List IRecRule),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW major →
    decRules (erecP s₀.mem) ro.toNat rc.toNat = some rules →
    CoreSpecE p (N + 1) "prepare_major" [mode, vis, d, rec, ro, rc, major]
      (prepareMajor (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI rec) rules
        (decE major)) s₀ a₀
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- `iota_rec_fire`'s error claim at fuel `N + 1` (the premises of `iotaRecFire_refines'`). -/
def IotaRecFireE (p : Prog) : Prop :=
  ∀ (N : Nat), KnotUpTo p N → KnotUpToE p N → ∀ (F : Nat), N ≤ F → N ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d c us recP so usj ctorP rl major sn : Word) (lps : List NIdx)
    (rule : IRecRule) (cvj : IConstantVal) (np nf : Nat) (args : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW c → HW us → HW usj →
    HW major →
    hslice? (erecP s₀.mem) (rdW (s₀.mem.arr64 EREC) (recP + 2)).toNat
      (rdW (s₀.mem.arr64 EREC) (recP + 3)).toNat = some lps →
    decRule (erecP s₀.mem) rl.toNat = some rule →
    decCI (erecP s₀.mem) ctorP.toNat = some (.ctorInfo cvj np nf) →
    FireEnv fe lps rule cvj →
    SpineR s₀.mem so sn args → so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat + 1 = sn.toNat →
    CoreSpecE p (N + 1) "iota_rec_fire" [mode, vis, d, c, us, recP, so, usj, ctorP, rl, major]
      (iotaRecFireT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI c)
        (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat (rdW (s₀.mem.arr64 EREC) (recP + 6)).toNat lps
        (decI us) args.toList (decE major) (decI usj) cvj rule) s₀ a₀
-/

/-- **What `iota_rec_major`'s errors assume** at L fuel `n`: the knot's slots', the verdict
closure, `prepare_major`'s and `iota_rec_fire`'s claims. -/
structure MajorG (p : Prog) (n : Nat) : Prop where
  knot : KnotUpToE p n
  nv : closedNV p L.Checker.nvFns = true
  pm : PrepareMajorE p
  fire : IotaRecFireE p

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`iota_rec_major` refines `iotaRecMajorT`, both outcomes**: the errors are `prepare_major`'s
and `iota_rec_fire`'s. -/
theorem major_ref (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hsup : ∀ fe : IFEnv, SupKeep fe) (hmtc : MajorToCtorOK p)
    (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hnF : n ≤ F) (hn62 : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d c us recP so sn : Word) (cv : IConstantVal) (rules : List IRecRule)
    (xs : Array EIdx) (hS : CoreS dn s₀.mem a₀ vis fe MM eb) (hm4 : mode < 4)
    (hebm : eb = (mode >>> 1) &&& 1) (hcw : HW c) (hus : HW us)
    (hcv : decCV (erecP s₀.mem) (recP.toNat + 1) = some cv)
    (hrules : decRules (erecP s₀.mem) (rdW (s₀.mem.arr64 EREC) (recP + 7)).toNat
      (rdW (s₀.mem.arr64 EREC) (recP + 8)).toNat = some rules)
    (hrecF : ∃ cr mI rP, fe.find? cr = some (.recInfo cv mI rP rules))
    (hsa : SpineR s₀.mem so sn xs) (hsat : so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat)
    (hmI : (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat + 1 = sn.toNat) :
    RefE (MajorG p n) (irMajorE p (n + 1) s₀.mem mode vis d c us recP so sn)
      (iotaRecMajorT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI c) (decI us)
        cv (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat (rdW (s₀.mem.arr64 EREC) (recP + 6)).toNat rules
        xs.toList) a₀ (CorePost decOptR dn s₀.mem vis fe MM eb ResW) := by
  simp only [irMajorE]
  have hspn := hS.spn
  have herec := hS.erec
  obtain ⟨-, -, hlps, -, -, -⟩ := decCV_rd1 herec hcv
  generalize hE0 : s₀.mem.arr64 EREC = E at *
  cases n with
  | zero => rw [callW_zero, liftE_none, irMajorE.k_intern_bvar.none]; exact RefE.of_cls0 (by simp)
  | succ N =>
  unfold iotaRecMajorT
  -- `bvar 0`
  refine RefE.bindLift (fun _ => rfl) fun rb m1 c0 => ?_
  obtain ⟨hrun0, hS1, hSt1, e1, hspn1⟩ := irCallW_internBVar p hp (N + 1) hS 0 rb m1 c0
  refine ⟨_, _, hrun0, ?_⟩
  simp only [irMajorE.k_intern_bvar, e1, hE0, hspn1]
  -- the major
  have hmIl : (rdW E (recP + 5)).toNat < sn.toNat := by omega
  have hmw : so + rdW E (recP + 5) = so + (rdW E (recP + 5)).toNat.toUInt64 := by
    rw [toUInt64_toNat_self]
  have hmaj : HW (rdW (s₀.mem.arr64 SPN) (so + rdW E (recP + 5))) := by
    have := hsa.lt _ hmIl; unfold HW; rw [hmw]; exact this
  have hgetD : xs.toList.getD (rdW E (recP + 5)).toNat (decE (rb.headD 0)) =
      decE (rdW (s₀.mem.arr64 SPN) (so + rdW E (recP + 5))) := by
    have hsz := hsa.size
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hsz]; exact hmIl),
      Option.getD_some]
    have := hsa.get _ (by rw [hsz]; exact hmIl)
    simp only [Array.getElem_toList]
    rw [this, hmw]; rfl
  rw [hgetD]
  have hrules1 : decRules (erecP m1) (rdW E (recP + 7)).toNat (rdW E (recP + 8)).toNat =
      some rules := by rw [e1, hE0]; exact hrules
  rcases c1 : callE p (N + 1) "prepare_major" [mode, vis, d, c, rdW E (recP + 7), rdW E (recP + 8),
      rdW (s₀.mem.arr64 SPN) (so + rdW E (recP + 5))] m1 with e1' | ⟨rm, m2⟩
  · exact RefE.bind_left fun hG => CoreSpecE.of_callE (hG.pm N (hk.mono (by omega))
      (hG.knot.mono (by omega)) F (by omega) (by omega) ⟨m1, Locals.init []⟩ _ dn vis fe MM eb mode d c
      (rdW E (recP + 7)) (rdW E (recP + 8)) (rdW (s₀.mem.arr64 SPN) (so + rdW E (recP + 5))) rules hS1
      hm4 hebm hmaj hrules1) c1
  have hpm := prepareMajor_refines' p hp.toIotaProg4 hc hw hsup hmtc hEK N (hk.mono (by omega)) F
    (by omega) (by omega) ⟨m1, Locals.init []⟩ _ dn vis fe MM eb mode d c (rdW E (recP + 7))
    (rdW E (recP + 8)) (rdW (s₀.mem.arr64 SPN) (so + rdW E (recP + 5))) rules hS1 hm4 hebm hmaj
  obtain ⟨hrun1, ⟨M2, hS2, hK2, hSt2⟩, hr1⟩ := CoreSpec.run (hpm hrules1) (callW_of_callE c1)
  simp only [decH] at hrun1
  have e2 : m2.arr64 EREC = E := by rw [hEK _ _ _ _ _ _ (by simp) (callW_of_callE c1), e1, hE0]
  refine RefE.bind_right hrun1 ?_
  simp only [irMajorE.k_prepare_major]
  -- the head
  refine RefE.bindLift (fun _ => rfl) fun rh m3 c2 => ?_
  obtain ⟨t2, ht2, hm3, -, hhw, hrun2⟩ := triple_of_callW
    (getAppFn_refines' p hp.spine.fn (N + 1) ⟨m2, Locals.init []⟩ _ hS2.arena.base (rm.headD 0) hr1) c2
  have hm3' : m2 = m3 := hm3.symm.trans ht2
  subst hm3'
  refine ⟨_, _, hrun2, ?_⟩
  dsimp only [irMajorE.k_get_app_fn]
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun rv m4 c3 => ?_
  obtain ⟨hm4, hnot, hyes⟩ := irCallW_head p hp.head (N + 1) m2 _ hS2.arena.base _ hhw rv m4 c3
  subst m4
  have hSt12 := hSt1.trans hSt2
  have hpost : ∀ (a : AState), CoreAfter dn s₀.mem m2 a vis fe MM eb →
      CorePost decOptR dn s₀.mem vis fe MM eb ResW ([0, 0], m2) none a :=
    fun a h => ⟨h, rfl, ⟨by show HW (0 : Word); unfold HW; decide, by show HW (0 : Word); unfold HW; decide⟩⟩
  dsimp only [irMajorE.k_iota_rec_head]
  refine RefE.retIf (fun v0 => by simpa using hnot v0)
    (fun h => Classical.byContradiction fun v0 => absurd (hyes v0).1 (by simpa using h))
    (fun _ => hpost _ ⟨M2, hS2, hK2, hSt12⟩) fun v0 _ => ?_
  obtain ⟨htag, hview, hcjw, husjw⟩ := hyes v0
  refine RefE.bind_right (view_run_of _ _ _ hview) ?_
  -- the constructor
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun re m5 c4 => ?_
  obtain ⟨hm5, hfnone, hfsome⟩ := irEnvFind p hp.toIotaProg' (N + 1) dn m2 vis fe hS2.env _ hcjw re m5 c4
  subst m5
  dsimp only [irMajorE.k_env_find]
  rw [e2]
  by_cases f0 : re.headD 0 = 0
  · rw [ite_eq_left f0, hfnone f0]; exact RefE.ret rfl (hpost _ ⟨M2, hS2, hK2, hSt12⟩)
  rw [ite_eq_right f0]
  obtain ⟨ci, hfind, hci⟩ := hfsome f0
  rw [e2] at hci
  rw [hfind]
  by_cases k4 : rdW E (re.tail.headD 0) ≠ 4
  · rw [ite_eq_left k4]
    have hnc := (decCI_ctor hci (ArrExt.refl _) herec).2 k4
    cases ci <;> first | exact absurd rfl (hnc _ _ _) | exact RefE.ret rfl (hpost _ ⟨M2, hS2, hK2, hSt12⟩)
  rw [ite_eq_right k4]
  obtain ⟨cvj, np, nf, rfl, -⟩ := decCI_ctor_rd hci (Classical.not_not.mp k4)
  -- the rule
  have hEsz : (m2.arr64 EREC).size < 2 ^ 64 := by rw [e2]; omega
  have hrules2 : decRules (erecP m2) (rdW E (recP + 7)).toNat (rdW E (recP + 8)).toNat =
      some rules := by rw [e2]; exact hrules
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun rr m6 c5 => ?_
  obtain ⟨t5, ht5, hm6, -, hfr⟩ := triple_of_callW
    (findRule_refines p hp.findRule (N + 1) ⟨m2, Locals.init []⟩ _ _ _ rules hcjw hEsz hrules2) c5
  have hm6' : m2 = m6 := hm6.symm.trans ht5
  subst hm6'
  dsimp only [irMajorE.k_find_rule]
  by_cases g0 : rr.headD 0 = 0
  · rw [ite_eq_left g0, hfr]
    simp only [decRuleAt, g0, ↓reduceIte]
    exact RefE.ret rfl (hpost _ ⟨M2, hS2, hK2, hSt12⟩)
  rw [ite_eq_right g0]
  obtain ⟨rule, hdr⟩ := findRule_found p hp.findRule (N + 1) m2 _ _ _ rules hEsz hrules2 rr m2 c5 g0
  rw [e2] at hdr
  have hfrs : findRule rules (decI (rv.tail.headD 0)) = some rule := by
    rw [hfr]; simp only [decRuleAt, g0, ↓reduceIte, e2, hdr]
  rw [hfrs]
  obtain ⟨hmem, -⟩ := findRule_mem _ _ _ hfrs
  have hfe : FireEnv fe cv.levelParams rule cvj := by
    obtain ⟨cr, mI, rP, hfr⟩ := hrecF
    exact ⟨⟨cr, cv, mI, rP, rules, hfr, rfl, hmem⟩, ⟨_, np, nf, hfind⟩⟩
  have hsa2 := hsa.keep hSt12.size hSt12.below hsat hspn
  have hsat2 : so.toNat + sn.toNat ≤ (spTop m2).toNat := by rw [hSt12.1]; exact hsat
  -- the fire
  rcases c6 : callE p (N + 1) "iota_rec_fire" [mode, vis, d, c, us, recP, so, rv.tail.tail.headD 0,
      re.tail.headD 0, rr.tail.headD 0, rm.headD 0] m2 with e6 | ⟨rf, m7⟩
  · intro hG
    have h := hG.fire N (hk.mono (by omega)) (hG.knot.mono (by omega)) F (by omega) (by omega)
      ⟨m2, Locals.init []⟩ _ dn vis fe M2 eb mode d c us recP so (rv.tail.tail.headD 0)
      (re.tail.headD 0) (rr.tail.headD 0) (rm.headD 0) sn cv.levelParams rule cvj np nf xs hS2 hm4
      hebm hcw hus husjw hr1
    simp only [e2] at h
    exact CoreSpecE.of_callE (h hlps hdr hci hfe hsa2 hsat2 hmI) c6
  have hfi := iotaRecFire_refines' p hp hc hw hEI hER hEK N (hk.mono (by omega)) F (by omega)
    (by omega) ⟨m2, Locals.init []⟩ _ dn vis fe M2 eb mode d c us recP so (rv.tail.tail.headD 0)
    (re.tail.headD 0) (rr.tail.headD 0) (rm.headD 0) sn cv.levelParams rule cvj np nf xs hS2 hm4 hebm
    hcw hus husjw hr1
  simp only [e2] at hfi
  obtain ⟨hrun6, ⟨M6, hS6, hK6, hSt6⟩, hr6⟩ := CoreSpec.run (hfi hlps hdr hci hfe hsa2 hsat2 hmI)
    (callW_of_callE c6)
  dsimp only [irMajorE.k_iota_rec_fire]
  refine RefE.ret hrun6 ⟨⟨M6, hS6, hK2.trans hK6, hSt12.trans hSt6⟩, ?_, ?_⟩
  · simp only [decOptR]; rfl
  · unfold ResW at hr6 ⊢; exact hr6
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`iota_rec_major` refines `iotaRecMajorT`** (`major_ref`'s ok half). -/
theorem iotaRecMajor_refines' (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hsup : ∀ fe : IFEnv, SupKeep fe) (hmtc : MajorToCtorOK p)
    (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d c us recP so sn : Word) (cv : IConstantVal) (rules : List IRecRule)
    (xs : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW c → HW us →
    decCV (erecP s₀.mem) (recP.toNat + 1) = some cv →
    decRules (erecP s₀.mem) (rdW (s₀.mem.arr64 EREC) (recP + 7)).toNat
      (rdW (s₀.mem.arr64 EREC) (recP + 8)).toNat = some rules →
    (∃ cr mI rP, fe.find? cr = some (.recInfo cv mI rP rules)) →
    SpineR s₀.mem so sn xs → so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat + 1 = sn.toNat →
    CoreSpec p (n + 1) "iota_rec_major" [mode, vis, d, c, us, recP, so, sn]
      (iotaRecMajorT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI c) (decI us)
        cv (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat (rdW (s₀.mem.arr64 EREC) (recP + 6)).toNat rules
        xs.toList) decOptR s₀ a₀ dn vis fe MM eb ResW :=
  fun n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d c us recP so sn cv rules xs hS hm4 hebm hcw hus
      hcv hrules hrecF hsa hsat hmI =>
    RefE.coreSpec (irMajorE_spec p hp.major (n + 1) s₀ mode vis d c us recP so sn)
      (major_ref p hp hc hw hsup hmtc hEI hER hEK n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d c us recP
        so sn cv rules xs hS hm4 hebm hcw hus hcv hrules hrecF hsa hsat hmI)
-/

end L.Arena
