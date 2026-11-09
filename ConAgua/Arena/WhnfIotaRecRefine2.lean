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

/-- **`iota_rec_fam` refines the certificate family, both outcomes**: the errors are
`iota_case3_at`'s and `iota_rec_vck`'s. -/
theorem fam_ref (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hnF : n ≤ F) (hn62 : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d us recP so usj ctorP rl mo mn sn : Word) (lps : List NIdx)
    (rule : IRecRule) (cvj : IConstantVal) (np nf : Nat) (args margs : Array EIdx)
    (hS : CoreS dn s₀.mem a₀ vis fe MM eb) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hus : HW us) (husj : HW usj)
    (hlps : hslice? (erecP s₀.mem) (erRdT s₀.mem (recP + 2)).toNat
      (erRdT s₀.mem (recP + 3)).toNat = some lps)
    (hrule : decRule (erecP s₀.mem) rl.toNat = some rule)
    (hci : decCI (erecP s₀.mem) ctorP.toNat = some (.ctorInfo cvj np nf))
    (hfe : FireEnv fe lps rule cvj)
    (hsa : SpineR s₀.mem so sn args) (hsat : so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat)
    (hmI : (erRdT s₀.mem (recP + 5)).toNat + 1 = sn.toNat)
    (hsm : SpineR s₀.mem mo mn margs) (hsmt : mo + mn = spTop s₀.mem)
    (hcpm : np ≤ mn.toNat) :
    RefE (FamG p n) (irFamE p (n + 1) s₀.mem mode vis d us recP so usj ctorP rl mo mn)
      (iotaRecFamT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (erRdT s₀.mem (recP + 9) != 0)
        (erRdT s₀.mem (recP + 5)).toNat (erRdT s₀.mem (recP + 6)).toNat np lps
        (decI us) args.toList (decI usj) cvj rule margs.toList) a₀
      (CorePost decBool dn s₀.mem vis fe MM eb ResH) := by
  sorry

/-- **`iota_rec_fam` refines the certificate family** (`fam_ref`'s ok half). -/
theorem iotaRecFam_refines' (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d us recP so usj ctorP rl mo mn sn : Word) (lps : List NIdx)
    (rule : IRecRule) (cvj : IConstantVal) (np nf : Nat) (args margs : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW us → HW usj →
    hslice? (erecP s₀.mem) (erRdT s₀.mem (recP + 2)).toNat
      (erRdT s₀.mem (recP + 3)).toNat = some lps →
    decRule (erecP s₀.mem) rl.toNat = some rule →
    decCI (erecP s₀.mem) ctorP.toNat = some (.ctorInfo cvj np nf) →
    FireEnv fe lps rule cvj →
    SpineR s₀.mem so sn args → so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    (erRdT s₀.mem (recP + 5)).toNat + 1 = sn.toNat →
    SpineR s₀.mem mo mn margs → mo + mn = spTop s₀.mem → np ≤ mn.toNat →
    CoreSpec p (n + 1) "iota_rec_fam" [mode, vis, d, us, recP, so, usj, ctorP, rl, mo, mn]
      (iotaRecFamT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (erRdT s₀.mem (recP + 9) != 0)
        (erRdT s₀.mem (recP + 5)).toNat (erRdT s₀.mem (recP + 6)).toNat np lps
        (decI us) args.toList (decI usj) cvj rule margs.toList) decBool s₀ a₀ dn vis fe MM eb :=
  fun n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d us recP so usj ctorP rl mo mn sn lps rule cvj np nf
      args margs hS hm4 hebm hus husj hlps hrule hci hfe hsa hsat hmI hsm hsmt hcpm =>
    RefE.coreSpec (irFamE_spec p hp.fam (n + 1) s₀ mode vis d us recP so usj ctorP rl mo mn)
      (fam_ref p hp hc hw hEI hER hEK n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d us recP so usj ctorP
        rl mo mn sn lps rule cvj np nf args margs hS hm4 hebm hus husj hlps hrule hci hfe hsa hsat hmI
        hsm hsmt hcpm)

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
  grind [arena_grind] fold [rpLen] extra [ld64_rdW_specE, ld64_rdW_specT] unified
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
    (hlps : hslice? (erecP s₀.mem) (erRdT s₀.mem (recP + 2)).toNat
      (erRdT s₀.mem (recP + 3)).toNat = some lps)
    (hrule : decRule (erecP s₀.mem) rl.toNat = some rule)
    (hci : decCI (erecP s₀.mem) ctorP.toNat = some (.ctorInfo cvj np nf))
    (hfe : FireEnv fe lps rule cvj)
    (hsa : SpineR s₀.mem so sn args) (hsat : so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat)
    (hmI : (erRdT s₀.mem (recP + 5)).toNat + 1 = sn.toNat)
    (hsm : SpineR s₀.mem mo mn margs) (hsmt : mo + mn = spTop s₀.mem) :
    RefE (FamG p n) (fire2E p (n + 1) s₀.mem mode vis d c us recP so usj ctorP rl mo mn)
      (iotaRecFire2T (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI c) (erRdT s₀.mem (recP + 9) != 0)
        (erRdT s₀.mem (recP + 5)).toNat (erRdT s₀.mem (recP + 6)).toNat np lps
        (decI us) args.toList (decI usj) cvj rule margs.toList) a₀
      (CorePost decOptR dn s₀.mem vis fe MM eb ResW) := by
  sorry

/-- **`iota_rec_fire2` refines the fire past the major's arguments** (`fire2_ref`'s ok half). -/
theorem iotaRecFire2_refines' (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d c us recP so usj ctorP rl mo mn sn : Word) (lps : List NIdx)
    (rule : IRecRule) (cvj : IConstantVal) (np nf : Nat) (args margs : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW c → HW us → HW usj →
    hslice? (erecP s₀.mem) (erRdT s₀.mem (recP + 2)).toNat
      (erRdT s₀.mem (recP + 3)).toNat = some lps →
    decRule (erecP s₀.mem) rl.toNat = some rule →
    decCI (erecP s₀.mem) ctorP.toNat = some (.ctorInfo cvj np nf) →
    FireEnv fe lps rule cvj →
    SpineR s₀.mem so sn args → so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    (erRdT s₀.mem (recP + 5)).toNat + 1 = sn.toNat →
    SpineR s₀.mem mo mn margs → mo + mn = spTop s₀.mem →
    CoreSpec p (n + 1) "iota_rec_fire2" [mode, vis, d, c, us, recP, so, usj, ctorP, rl, mo, mn]
      (iotaRecFire2T (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI c) (erRdT s₀.mem (recP + 9) != 0)
        (erRdT s₀.mem (recP + 5)).toNat (erRdT s₀.mem (recP + 6)).toNat np lps
        (decI us) args.toList (decI usj) cvj rule margs.toList) decOptR s₀ a₀ dn vis fe MM eb ResW :=
  fun n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d c us recP so usj ctorP rl mo mn sn lps rule cvj np nf
      args margs hS hm4 hebm hcw hus husj hlps hrule hci hfe hsa hsat hmI hsm hsmt =>
    RefE.coreSpec (fire2E_spec p hp.fire2 (n + 1) s₀ mode vis d c us recP so usj ctorP rl mo mn)
      (fire2_ref p hp hc hw hEI hER hEK n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d c us recP so usj
        ctorP rl mo mn sn lps rule cvj np nf args margs hS hm4 hebm hcw hus husj hlps hrule hci hfe hsa
        hsat hmI hsm hsmt)

/-! ## `iota_rec_fire(mode, vis, d, c, us, recP, so, usj, ctorP, rl, major)` -/

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
    (hlps : hslice? (erecP s₀.mem) (erRdT s₀.mem (recP + 2)).toNat
      (erRdT s₀.mem (recP + 3)).toNat = some lps)
    (hrule : decRule (erecP s₀.mem) rl.toNat = some rule)
    (hci : decCI (erecP s₀.mem) ctorP.toNat = some (.ctorInfo cvj np nf))
    (hfe : FireEnv fe lps rule cvj)
    (hsa : SpineR s₀.mem so sn args) (hsat : so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat)
    (hmI : (erRdT s₀.mem (recP + 5)).toNat + 1 = sn.toNat) :
    RefE (FamG p n) (irFireE p (n + 1) s₀.mem mode vis d c us recP so usj ctorP rl major)
      (iotaRecFireT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI c) (erRdT s₀.mem (recP + 9) != 0)
        (erRdT s₀.mem (recP + 5)).toNat (erRdT s₀.mem (recP + 6)).toNat np lps
        (decI us) args.toList (decE major) (decI usj) cvj rule) a₀
      (CorePost decOptR dn s₀.mem vis fe MM eb ResW) := by
  sorry

/-- **`iota_rec_fire` refines the fire** (`fire_ref`'s ok half). -/
theorem iotaRecFire_refines' (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d c us recP so usj ctorP rl major sn : Word) (lps : List NIdx)
    (rule : IRecRule) (cvj : IConstantVal) (np nf : Nat) (args : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW c → HW us → HW usj →
    HW major →
    hslice? (erecP s₀.mem) (erRdT s₀.mem (recP + 2)).toNat
      (erRdT s₀.mem (recP + 3)).toNat = some lps →
    decRule (erecP s₀.mem) rl.toNat = some rule →
    decCI (erecP s₀.mem) ctorP.toNat = some (.ctorInfo cvj np nf) →
    FireEnv fe lps rule cvj →
    SpineR s₀.mem so sn args → so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    (erRdT s₀.mem (recP + 5)).toNat + 1 = sn.toNat →
    CoreSpec p (n + 1) "iota_rec_fire" [mode, vis, d, c, us, recP, so, usj, ctorP, rl, major]
      (iotaRecFireT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI c) (erRdT s₀.mem (recP + 9) != 0)
        (erRdT s₀.mem (recP + 5)).toNat (erRdT s₀.mem (recP + 6)).toNat np lps
        (decI us) args.toList (decE major) (decI usj) cvj rule) decOptR s₀ a₀ dn vis fe MM eb
      ResW :=
  fun n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d c us recP so usj ctorP rl major sn lps rule cvj np
      nf args hS hm4 hebm hcw hus husj hmaj hlps hrule hci hfe hsa hsat hmI =>
    RefE.coreSpec (irFireE_spec p hp.fire (n + 1) s₀ mode vis d c us recP so usj ctorP rl major)
      (fire_ref p hp hc hw hEI hER hEK n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d c us recP so usj
        ctorP rl major sn lps rule cvj np nf args hS hm4 hebm hcw hus husj hmaj hlps hrule hci hfe hsa
        hsat hmI)

/-! ## `env_find` and `intern_bvar` as runs -/

/-- **`env_find` as a run**: the memory unchanged, `find?` decoded at the record pool. -/
theorem irEnvFind (p : Prog) (hp : IotaProg' p) (n : Nat) (dn : NIdx → Option ConLeche.Name)
    (m : Mem) (vis : Word) (fe : IFEnv) (hE : EnvR m vis fe) (w : Word) (hw : HW w)
    (r : List Word) (m' : Mem) (h : callW p n "env_find" [w, vis] m = some (r, m')) :
    m' = m ∧ (r.headD 0 = 0 → fe.find? (decI w) = none) ∧
      (r.headD 0 ≠ 0 → ∃ ci, fe.find? (decI w) = some ci ∧
        decCI (erecP m) (r.tail.headD 0).toNat = some ci) := by
  obtain ⟨s', hs', h1, -, hfind, hdec⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envFind_refines p hp.envrow hp.baserow hp.envfind n _ vis w hE hw) h
  refine ⟨hs'.symm.trans h1, fun h0 => by rw [hfind]; simp only [envFound, h0, ↓reduceIte], fun h0 => ?_⟩
  obtain ⟨ci, hci⟩ := hdec h0
  exact ⟨ci, by rw [hfind]; simp only [envFound, h0, ↓reduceIte]; exact hci, hci⟩

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
theorem frN_found (rd : Word → Word) (ro rc c : Word) (i : Nat) (hne : (frN rd ro rc c i).headD 0 ≠ 0) :
    ∃ j : Word, j < rc ∧ (frN rd ro rc c i).tail.headD 0 = ro + 11 * j := by
  fun_induction frN rd ro rc c i with
  | case1 i hi _ => exact ⟨UInt64.ofNat i, UInt64.lt_iff_toNat_lt.mpr (by have := rc.toNat_lt; simp; omega), rfl⟩
  | case2 i _ _ ih => exact ih hne
  | case3 => simp at hne

/-- **`find_rule`'s answer decodes** when it found one. -/
theorem findRule_found (p : Prog) (hp : p.lookup "find_rule" = some findRuleL) (n : Nat) (m : Mem)
    (ro rc c : Word) (rules : List IRecRule)
    (hr : decRules (erecP m) ro.toNat rc.toNat = some rules) (r : List Word) (m' : Mem)
    (h : callW p n "find_rule" [ro, rc, c] m = some (r, m')) (hne : r.headD 0 ≠ 0) :
    ∃ rule, decRule (erecP m) (r.tail.headD 0).toNat = some rule := by
  obtain ⟨t, ht, -, -, hW⟩ := triple_of_callW (findRule_spec p hp n ⟨m, Locals.init []⟩ ro rc c) h
  subst hW
  obtain ⟨j, hj, hq⟩ := frN_found _ ro rc c 0 hne
  obtain ⟨hl, hg⟩ := decRules_getR _ _ _ hr
  have hj' : j.toNat < rc.toNat := hj
  have hdr := hg j.toNat hj'
  obtain ⟨rule, hrule⟩ : ∃ rule, rules[j.toNat]? = some rule :=
    ⟨rules[j.toNat], List.getElem?_eq_getElem (by omega)⟩
  rw [hrule] at hdr
  have hw := rule_idx (erRdOK m) ro j rule hdr
  refine ⟨rule, ?_⟩
  rw [hq]
  show decRule (erecP m) (ro + 11 * j).toNat = some rule
  rw [hw]; exact hdr

/-- `prepare_major`'s error claim at fuel `N + 1` (the premises of `prepareMajor_refines'`). -/
def PrepareMajorE (p : Prog) : Prop :=
  ∀ (N : Nat), KnotUpTo p N → KnotUpToE p N → ∀ (F : Nat), N ≤ F → N ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d rec isK ro rc major : Word) (rules : List IRecRule),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW major →
    decRules (erecP s₀.mem) ro.toNat rc.toNat = some rules →
    CoreSpecE p (N + 1) "prepare_major" [mode, vis, d, rec, isK, ro, rc, major]
      (prepareMajor (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI rec)
        (isK != 0) rules (decE major)) s₀ a₀

/-- `iota_rec_fire`'s error claim at fuel `N + 1` (the premises of `iotaRecFire_refines'`). -/
def IotaRecFireE (p : Prog) : Prop :=
  ∀ (N : Nat), KnotUpTo p N → KnotUpToE p N → ∀ (F : Nat), N ≤ F → N ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d c us recP so usj ctorP rl major sn : Word) (lps : List NIdx)
    (rule : IRecRule) (cvj : IConstantVal) (np nf : Nat) (args : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW c → HW us → HW usj →
    HW major →
    hslice? (erecP s₀.mem) (erRdT s₀.mem (recP + 2)).toNat
      (erRdT s₀.mem (recP + 3)).toNat = some lps →
    decRule (erecP s₀.mem) rl.toNat = some rule →
    decCI (erecP s₀.mem) ctorP.toNat = some (.ctorInfo cvj np nf) →
    FireEnv fe lps rule cvj →
    SpineR s₀.mem so sn args → so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    (erRdT s₀.mem (recP + 5)).toNat + 1 = sn.toNat →
    CoreSpecE p (N + 1) "iota_rec_fire" [mode, vis, d, c, us, recP, so, usj, ctorP, rl, major]
      (iotaRecFireT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI c)
        (erRdT s₀.mem (recP + 9) != 0)
        (erRdT s₀.mem (recP + 5)).toNat (erRdT s₀.mem (recP + 6)).toNat np lps
        (decI us) args.toList (decE major) (decI usj) cvj rule) s₀ a₀

/-- **What `iota_rec_major`'s errors assume** at L fuel `n`: the knot's slots', the verdict
closure, `prepare_major`'s and `iota_rec_fire`'s claims. -/
structure MajorG (p : Prog) (n : Nat) : Prop where
  knot : KnotUpToE p n
  nv : closedNV p L.Checker.nvFns = true
  pm : PrepareMajorE p
  fire : IotaRecFireE p

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
    (hrules : decRules (erecP s₀.mem) (erRdT s₀.mem (recP + 7)).toNat
      (erRdT s₀.mem (recP + 8)).toNat = some rules)
    (hrecF : ∃ cr mI rP isK, fe.find? cr = some (.recInfo cv mI rP isK rules))
    (hsa : SpineR s₀.mem so sn xs) (hsat : so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat)
    (hmI : (erRdT s₀.mem (recP + 5)).toNat + 1 = sn.toNat) :
    RefE (MajorG p n) (irMajorE p (n + 1) s₀.mem mode vis d c us recP so sn)
      (iotaRecMajorT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI c) (decI us)
        cv (erRdT s₀.mem (recP + 5)).toNat (erRdT s₀.mem (recP + 6)).toNat
        (erRdT s₀.mem (recP + 9) != 0) rules xs.toList) a₀ (CorePost decOptR dn s₀.mem vis fe MM eb ResW) := by
  sorry

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
    decRules (erecP s₀.mem) (erRdT s₀.mem (recP + 7)).toNat
      (erRdT s₀.mem (recP + 8)).toNat = some rules →
    (∃ cr mI rP isK, fe.find? cr = some (.recInfo cv mI rP isK rules)) →
    SpineR s₀.mem so sn xs → so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    (erRdT s₀.mem (recP + 5)).toNat + 1 = sn.toNat →
    CoreSpec p (n + 1) "iota_rec_major" [mode, vis, d, c, us, recP, so, sn]
      (iotaRecMajorT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI c) (decI us)
        cv (erRdT s₀.mem (recP + 5)).toNat (erRdT s₀.mem (recP + 6)).toNat
        (erRdT s₀.mem (recP + 9) != 0) rules xs.toList) decOptR s₀ a₀ dn vis fe MM eb ResW :=
  fun n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d c us recP so sn cv rules xs hS hm4 hebm hcw hus hcv
      hrules hrecF hsa hsat hmI =>
    RefE.coreSpec (irMajorE_spec p hp.major (n + 1) s₀ mode vis d c us recP so sn)
      (major_ref p hp hc hw hsup hmtc hEI hER hEK n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d c us
        recP so sn cv rules xs hS hm4 hebm hcw hus hcv hrules hrecF hsa hsat hmI)

end L.Arena
