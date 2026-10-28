import ConAgua.Arena.LdRd
import ConAgua.Arena.RecFireEnv
import ConAgua.Arena.WhnfIotaRefine6
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.RefECore
import ConAgua.Arena.KnotE
import ConAgua.Verdict.WhnfModels3E
import ConAgua.L.GrindAttr

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

section famRun
variable (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth mI rP : Nat)
  (lps : List NIdx) (us : LsIdx) (args : List EIdx) (usj : LsIdx) (cvj : IConstantVal)
  (rl : IRecRule) (margs : List EIdx)

theorem famT_run_trusted (a : AState) (h : mode.verifiedChecks = false) :
    (iotaRecFamT mode r fe depth mI rP lps us args usj cvj rl margs).run a = .ok (true, a) := by
  simp only [iotaRecFamT, h, Bool.false_eq_true, ↓reduceIte]; rfl

theorem famT_run_nc3 (a a1 a2 : AState) (cmpL : LsIdx) (h : mode.verifiedChecks = true)
    (h1 : (recFireLevels rl lps us cvj.levelParams).run a = .ok (cmpL, a1))
    (h2 : (iotaCase3 fe rl cvj cmpL).run a1 = .ok (false, a2)) :
    (iotaRecFamT mode r fe depth mI rP lps us args usj cvj rl margs).run a = .ok (true, a2) := by
  simp only [iotaRecFamT, h, ↓reduceIte, StateT.run_bind, h1, except_ok_bind, h2,
    Bool.false_eq_true]; rfl

theorem famT_run_vck (a a1 a2 a3 : AState) (cmpL : LsIdx) (b : Bool) (h : mode.verifiedChecks = true)
    (h1 : (recFireLevels rl lps us cvj.levelParams).run a = .ok (cmpL, a1))
    (h2 : (iotaCase3 fe rl cvj cmpL).run a1 = .ok (true, a2))
    (h3 : (iotaRecVckT r fe depth mI rP lps us args usj cvj rl margs cmpL).run a2 = .ok (b, a3)) :
    (iotaRecFamT mode r fe depth mI rP lps us args usj cvj rl margs).run a = .ok (b, a3) := by
  simp only [iotaRecFamT, h, ↓reduceIte, StateT.run_bind, h1, except_ok_bind, h2, h3]

theorem famT_err_vck (a a1 a2 : AState) (cmpL : LsIdx) (h : mode.verifiedChecks = true)
    (h1 : (recFireLevels rl lps us cvj.levelParams).run a = .ok (cmpL, a1))
    (h2 : (iotaCase3 fe rl cvj cmpL).run a1 = .ok (true, a2)) (ce : CheckError)
    (h3 : (iotaRecVckT r fe depth mI rP lps us args usj cvj rl margs cmpL).run a2 = .error ce) :
    (iotaRecFamT mode r fe depth mI rP lps us args usj cvj rl margs).run a = .error ce := by
  simp only [iotaRecFamT, h, ↓reduceIte, StateT.run_bind, h1, except_ok_bind, h2, h3]

end famRun

/-- `iota_rec_vck`'s error claim at fuel `n + 1` (the premises of `iotaRecVck_refines'`). -/
def IotaRecVckE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d us recP so usj ctorP rl mo mn cmpL sn : Word) (lps : List NIdx)
    (rule : IRecRule) (cvj : IConstantVal) (args margs : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW us → HW usj →
    HW cmpL →
    hslice? (s₀.mem.arr64 EREC) (rdW (s₀.mem.arr64 EREC) (recP + 2)).toNat
      (rdW (s₀.mem.arr64 EREC) (recP + 3)).toNat = some lps →
    decRule (s₀.mem.arr64 EREC) rl.toNat = some rule →
    decCV (s₀.mem.arr64 EREC) (ctorP.toNat + 1) = some cvj →
    SpineR s₀.mem so sn args → so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat + 1 = sn.toNat →
    SpineR s₀.mem mo mn margs → mo + mn = spTop s₀.mem → rule.ctorParams ≤ mn.toNat →
    CoreSpecE p (n + 1) "iota_rec_vck" [mode, vis, d, us, recP, so, usj, ctorP, rl, mo, mn, cmpL]
      (iotaRecVckT (coreKnot (decMode mode) fe id F) fe d.toNat
        (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat (rdW (s₀.mem.arr64 EREC) (recP + 6)).toNat lps
        (decI us) args.toList (decI usj) cvj rule margs.toList (decI cmpL)) s₀ a₀

/-- **What the certificate family's errors assume** at L fuel `n`: the knot's slots' claims,
`iota_rec_vck`'s. -/
structure FamG (p : Prog) (n : Nat) : Prop where
  knot : KnotUpToE p n
  vck : IotaRecVckE p

theorem FamG.mono {p : Prog} {n n' : Nat} (h : FamG p n) (hn : n' ≤ n) : FamG p n' :=
  ⟨h.knot.mono hn, h.vck⟩

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
    (hlps : hslice? (s₀.mem.arr64 EREC) (rdW (s₀.mem.arr64 EREC) (recP + 2)).toNat
      (rdW (s₀.mem.arr64 EREC) (recP + 3)).toNat = some lps)
    (hrule : decRule (s₀.mem.arr64 EREC) rl.toNat = some rule)
    (hci : decCI (s₀.mem.arr64 EREC) dn ctorP.toNat = some (.ctorInfo cvj np nf))
    (hfe : FireEnv fe lps rule cvj)
    (hsa : SpineR s₀.mem so sn args) (hsat : so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat)
    (hmI : (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat + 1 = sn.toNat)
    (hsm : SpineR s₀.mem mo mn margs) (hsmt : mo + mn = spTop s₀.mem)
    (hcpm : rule.ctorParams ≤ mn.toNat) :
    RefE (FamG p n) (irFamE p (n + 1) s₀.mem mode vis d us recP so usj ctorP rl mo mn)
      (iotaRecFamT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat
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
  by_cases hv : mode &&& 1 ≠ 0
  · rw [ite_eq_left hv]
    have hvc : (decMode mode).verifiedChecks = false := by
      rw [decMode_verified mode hm4]; simpa using hv
    exact RefE.ret (famT_run_trusted (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat _ _
      lps (decI us) args.toList (decI usj) cvj rule margs.toList a₀ hvc)
      (CorePost.ret hS rfl (by show HW (1 : Word); unfold HW; decide))
  rw [ite_eq_right hv]
  have hvc : (decMode mode).verifiedChecks = true := by
    rw [decMode_verified mode hm4]; simpa using hv
  generalize hE0 : s₀.mem.arr64 EREC = E at *
  -- the comparand levels
  rcases c1 : callW p n "rec_fire_levels" [rdW E (rl + 3), rdW E (rl + 4), rdW E (rl + 5),
      rdW E (recP + 2), rdW E (recP + 3), us, rdW E (ctorP + 2), rdW E (ctorP + 3)] s₀.mem with
    _ | ⟨rv, m1⟩
  · rw [liftE_none, irFamE.k_rec_fire_levels.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨hrun1, ⟨M1, hS1, hK1, hSt1⟩, hr1⟩ := CoreSpec.run
    (hc.recFireLevels n ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb _ _ _ _ _ us _ _ rule lps
      cvj.levelParams hS hus (by show hslice? (s₀.mem.arr64 EREC) _ _ = _; rw [hE0]; exact hlps)
      hld hfc) c1
  have e1 : m1.arr64 EREC = E := by rw [hER _ _ _ _ _ _ (by simp) c1, hE0]
  simp only [irFamE.k_rec_fire_levels, e1]
  -- case 3
  rcases c2 : callW p n "iota_case3" [rdW E (rl + 9), vis, ctorP, rv.headD 0] m1 with _ | ⟨r3, m2⟩
  · rw [liftE_none, irFamE.k_iota_case3.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨hrun2, ⟨M2, hS2, hK2, hSt2⟩, hr2⟩ := CoreSpec.run
    (iotaCase3_refines p hp.toIotaProg4 hc.capsNeverZero n ⟨m1, Locals.init []⟩ _ dn vis fe M1
      eb (rdW E (rl + 9)) ctorP (rv.headD 0) rule cvj np nf hS1 hr1 hkw (by rw [e1]; exact hci)) c2
  have e2 : m2.arr64 EREC = E := by rw [hER _ _ _ _ _ _ (by simp) c2, e1]
  have hSt12 := hSt1.trans hSt2
  simp only [irFamE.k_iota_case3]
  by_cases g0 : r3.headD 0 = 0
  · rw [ite_eq_left g0]
    rw [decBool_f_m2c g0] at hrun2
    exact RefE.ret (famT_run_nc3 (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat
      _ _ lps (decI us) args.toList (decI usj) cvj rule margs.toList a₀ _ _ _ hvc hrun1 hrun2)
      ⟨⟨M2, hS2, hK1.trans hK2, hSt12⟩, rfl, by show HW (1 : Word); unfold HW; decide⟩
  rw [ite_eq_right g0]
  rw [decBool_t_m2c g0] at hrun2
  cases n with
  | zero =>
    obtain ⟨e', he', h0⟩ := callE_zero p "iota_rec_vck" [mode, vis, d, us, recP, so, usj, ctorP, rl,
      mo, mn, rv.headD 0] m2
    rw [he']; exact RefE.of_cls0 h0
  | succ N =>
  have hsa2 := hsa.keep hSt12.size hSt12.below hsat hspn
  have hsat2 : so.toNat + sn.toNat ≤ (spTop m2).toNat := by rw [hSt12.1]; exact hsat
  have hsm2 := hsm.keep hSt12.size hSt12.below (by rw [← hsmt, hmsz]; exact Nat.le_refl _) hspn
  have hsmt2 : mo + mn = spTop m2 := by rw [hSt12.1]; exact hsmt
  rcases c3 : callE p (N + 1) "iota_rec_vck" [mode, vis, d, us, recP, so, usj, ctorP, rl, mo, mn,
      rv.headD 0] m2 with e3 | ⟨rk, m3⟩
  · intro hG
    have h := hG.vck N (hk.mono (by omega)) (hG.knot.mono (by omega)) F (by omega) (by omega)
      ⟨m2, Locals.init []⟩ _ dn vis fe M2 eb mode d us recP so usj ctorP rl mo mn (rv.headD 0) sn
      lps rule cvj args margs hS2 hm4 hebm hus husj hr1
    simp only [e2] at h
    exact ErrClaim.of_run_err (fun ce h' => famT_err_vck _ _ _ _ _ _ _ _ _ _ _ _ _ a₀ _ _ _ hvc hrun1
      hrun2 ce h') (CoreSpecE.of_callE (h hlps hrule hcv hsa2 hsat2 hmI hsm2 hsmt2 hcpm) c3)
  have hvk := iotaRecVck_refines' p hp hc hw hEI hER hEK N (hk.mono (by omega)) F
    (by omega) (by omega) ⟨m2, Locals.init []⟩ _ dn vis fe M2 eb mode d us recP so usj ctorP rl mo mn
    (rv.headD 0) sn lps rule cvj args margs hS2 hm4 hebm hus husj hr1
  simp only [e2] at hvk
  obtain ⟨hrun3, ⟨M3, hS3, hK3, hSt3⟩, hr3⟩ := CoreSpec.run (hvk hlps hrule hcv hsa2 hsat2 hmI hsm2
    hsmt2 hcpm) (callW_of_callE c3)
  exact RefE.ret (famT_run_vck (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat _
    _ lps (decI us) args.toList (decI usj) cvj rule margs.toList a₀ _ _ _ _ _ hvc hrun1 hrun2
    hrun3) ⟨⟨M3, hS3, hK1.trans (hK2.trans hK3), hSt12.trans hSt3⟩, rfl, hr3⟩

/-- **`iota_rec_fam` refines the certificate family** (`fam_ref`'s ok half). -/
theorem iotaRecFam_refines' (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p)
    :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d us recP so usj ctorP rl mo mn sn : Word) (lps : List NIdx)
    (rule : IRecRule) (cvj : IConstantVal) (np nf : Nat) (args margs : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW us → HW usj →
    hslice? (s₀.mem.arr64 EREC) (rdW (s₀.mem.arr64 EREC) (recP + 2)).toNat
      (rdW (s₀.mem.arr64 EREC) (recP + 3)).toNat = some lps →
    decRule (s₀.mem.arr64 EREC) rl.toNat = some rule →
    decCI (s₀.mem.arr64 EREC) dn ctorP.toNat = some (.ctorInfo cvj np nf) →
    FireEnv fe lps rule cvj →
    SpineR s₀.mem so sn args → so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat + 1 = sn.toNat →
    SpineR s₀.mem mo mn margs → mo + mn = spTop s₀.mem → rule.ctorParams ≤ mn.toNat →
    CoreSpec p (n + 1) "iota_rec_fam" [mode, vis, d, us, recP, so, usj, ctorP, rl, mo, mn]
      (iotaRecFamT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat
        (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat (rdW (s₀.mem.arr64 EREC) (recP + 6)).toNat lps
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
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  match vs, hvs with
  | [mode, vis, d, us, recP, so, usj, ctorP, rl, mo, mn, cmpL], _ =>
  obtain ⟨t, ht, -, hW⟩ := triple_of_callW
    (iotaRecVck_spec p hp.vck n ⟨m, Locals.init []⟩ mode vis d us recP so usj ctorP rl mo mn cmpL) h
  rw [ht] at hW
  simp only [irVckW] at hW
  split at hW
  · cases hW
  rename_i rq m1 c1
  have e1 := hER _ _ _ _ _ _ (by simp) c1
  split at hW
  · cases hW
  split at hW
  · simp only [Option.some.injEq, Prod.mk.injEq] at hW; rw [← hW.2, e1]
  split at hW
  · cases hW
  rename_i rc m2 c2
  have e2 := callW_iotaRecCmp_erec p hp hER hEK _ _ _ _ _ rfl c2
  split at hW
  · simp only [Option.some.injEq, Prod.mk.injEq] at hW; rw [← hW.2, e2, e1]
  split at hW
  · cases hW
  rename_i rt m3 c3
  have e3 := hER _ _ _ _ _ _ (by simp) c3
  simp only [irVckTail] at hW
  split at hW
  · cases hW
  rename_i rf m4 c4
  have e4 := hER _ _ _ _ _ _ (by simp) c4
  split at hW
  · simp only [Option.some.injEq, Prod.mk.injEq] at hW; rw [← hW.2, e4, e3, e2, e1]
  split at hW
  · cases hW
  rename_i ri m5 c5
  have e5 := hEK _ _ _ _ _ _ (by simp) c5
  simp only [Option.some.injEq, Prod.mk.injEq] at hW; rw [← hW.2, e5, e4, e3, e2, e1]

theorem callW_iotaRecFam_erec (p : Prog) (hp : IotaRecProg' p) (hER : ErecKeptRec p)
    (hEK : ErecKeptKnot p) (n : Nat) (m : Mem) (vs : List Word) (r : List Word) (m' : Mem)
    (hvs : vs.length = 11) (h : callW p n "iota_rec_fam" vs m = some (r, m')) :
    m'.arr64 EREC = m.arr64 EREC := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  match vs, hvs with
  | [mode, vis, d, us, recP, so, usj, ctorP, rl, mo, mn], _ =>
  obtain ⟨t, ht, -, hW⟩ := triple_of_callE
    (irFamE_spec p hp.fam (n + 1) ⟨m, Locals.init []⟩ mode vis d us recP so usj ctorP rl mo mn)
    (callE_of_callW h)
  rw [ht] at hW
  simp only [irFamE, irFamE.k_rec_fire_levels, irFamE.k_iota_case3, irFamE.k_iota_rec_vck] at hW
  split at hW
  · simp only [Except.ok.injEq, Prod.mk.injEq] at hW; rw [← hW.2]
  cases c1 : callW p n "rec_fire_levels" [rdW (m.arr64 EREC) (rl + 3), rdW (m.arr64 EREC) (rl + 4),
      rdW (m.arr64 EREC) (rl + 5), rdW (m.arr64 EREC) (recP + 2), rdW (m.arr64 EREC) (recP + 3), us,
      rdW (m.arr64 EREC) (ctorP + 2), rdW (m.arr64 EREC) (ctorP + 3)] m with
  | none => rw [c1] at hW; cases hW
  | some q =>
  obtain ⟨rv, m1⟩ := q
  rw [c1, liftE_some] at hW
  simp only at hW
  have e1 := hER _ _ _ _ _ _ (by simp) c1
  cases c2 : callW p n "iota_case3" [rdW (m1.arr64 EREC) (rl + 9), vis, ctorP, rv.headD 0] m1 with
  | none => rw [c2] at hW; cases hW
  | some q =>
  obtain ⟨r3, m2⟩ := q
  rw [c2, liftE_some] at hW
  have e2 := hER _ _ _ _ _ _ (by simp) c2
  simp only at hW
  split at hW
  · simp only [Except.ok.injEq, Prod.mk.injEq] at hW; rw [← hW.2, e2, e1]
  cases c3 : callE p n "iota_rec_vck" [mode, vis, d, us, recP, so, usj, ctorP, rl, mo, mn, rv.headD 0]
      m2 with
  | error e => rw [c3] at hW; cases hW
  | ok q =>
  obtain ⟨rk, m3⟩ := q
  rw [c3] at hW
  have e3 := callW_iotaRecVck_erec p hp hER hEK _ _ _ _ _ rfl (callW_of_callE c3)
  simp only [Except.ok.injEq, Prod.mk.injEq] at hW; rw [← hW.2, e3, e2, e1]

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

/-- **`iota_rec_fire2` is its model `irFire2W`** (generated). -/
l_model iotaRecFire2_spec (p : Prog) (hp : p.lookup "iota_rec_fire2" = some iotaRecFire2L)
  fns [hp ↦ irFire2W tuple]
  specs [callW_spec p n "iota_rec_fam", callW_spec p n "rule_rhs_at", callW_spec p n "mk_app_n",
    callW_spec p n "mk_app_n_from"]
  grind [arena_grind] fold [rpLen] extra [ld64_rd_spec] simp [rpLen, Cmp.evalW] locals

section fire2Run
variable (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (c : NIdx)
  (mI rP : Nat) (lps : List NIdx) (us : LsIdx) (args : List EIdx) (usj : LsIdx)
  (cvj : IConstantVal) (rl : IRecRule) (margs : List EIdx)

theorem fire2T_run_len (a : AState) (h : ¬ margs.length = rl.ctorParams + rl.nfields) :
    (iotaRecFire2T mode r fe depth c mI rP lps us args usj cvj rl margs).run a = .ok (none, a) := by
  simp only [iotaRecFire2T, h, ↓reduceIte]; rfl

theorem fire2T_run_fam (a a1 : AState) (h : margs.length = rl.ctorParams + rl.nfields)
    (h1 : (iotaRecFamT mode r fe depth mI rP lps us args usj cvj rl margs).run a = .ok (false, a1)) :
    (iotaRecFire2T mode r fe depth c mI rP lps us args usj cvj rl margs).run a = .ok (none, a1) := by
  simp only [iotaRecFire2T, h, ↓reduceIte, StateT.run_bind, h1, except_ok_bind,
    Bool.false_eq_true]; rfl

theorem fire2T_run_fire (a a1 a2 a3 a4 : AState) (rhs x1 x : EIdx)
    (h : margs.length = rl.ctorParams + rl.nfields)
    (h1 : (iotaRecFamT mode r fe depth mI rP lps us args usj cvj rl margs).run a = .ok (true, a1))
    (h2 : (ruleRhsAt c rl.ctor lps rl.rhs us).run a1 = .ok (rhs, a2))
    (h3 : (mkAppN rhs (args.take rP)).run a2 = .ok (x1, a3))
    (h4 : (mkAppN x1 (margs.drop rl.ctorParams)).run a3 = .ok (x, a4)) :
    (iotaRecFire2T mode r fe depth c mI rP lps us args usj cvj rl margs).run a = .ok (some x, a4) := by
  simp only [iotaRecFire2T, h, ↓reduceIte, StateT.run_bind, h1, except_ok_bind, h2, mkAppN_append,
    h3, h4]; rfl

end fire2Run

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

/-- **`iota_rec_fire2` refines the fire past the major's arguments.** -/
theorem iotaRecFire2_refines' (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p)
    :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d c us recP so usj ctorP rl mo mn sn : Word) (lps : List NIdx)
    (rule : IRecRule) (cvj : IConstantVal) (np nf : Nat) (args margs : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW c → HW us → HW usj →
    hslice? (s₀.mem.arr64 EREC) (rdW (s₀.mem.arr64 EREC) (recP + 2)).toNat
      (rdW (s₀.mem.arr64 EREC) (recP + 3)).toNat = some lps →
    decRule (s₀.mem.arr64 EREC) rl.toNat = some rule →
    decCI (s₀.mem.arr64 EREC) dn ctorP.toNat = some (.ctorInfo cvj np nf) →
    FireEnv fe lps rule cvj →
    SpineR s₀.mem so sn args → so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat + 1 = sn.toNat →
    SpineR s₀.mem mo mn margs → mo + mn = spTop s₀.mem →
    CoreSpec p (n + 1) "iota_rec_fire2" [mode, vis, d, c, us, recP, so, usj, ctorP, rl, mo, mn]
      (iotaRecFire2T (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI c)
        (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat (rdW (s₀.mem.arr64 EREC) (recP + 6)).toNat lps
        (decI us) args.toList (decI usj) cvj rule margs.toList) decOptR s₀ a₀ dn vis fe MM eb ResW := by
  intro n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d c us recP so usj ctorP rl mo mn sn lps rule cvj
    np nf args margs hS hm4 hebm hcw hus husj hlps hrule hci hfe hsa hsat hmI hsm hsmt
  refine triple_post (iotaRecFire2_spec p hp.fire2 (n + 1) s₀ mode vis d c us recP so usj ctorP rl mo mn)
    fun r s' ⟨hloc, hW⟩ => ⟨hloc, ?_⟩
  simp only [irFire2W, irFire2W.k_iota_rec_fam, irFire2W.k_rule_rhs_at, irFire2W.k_mk_app_n,
    irFire2W.k_mk_app_n_from] at hW
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
  have hres0 : ∀ (m : Mem) (a : AState) (M : ModeMaps), CoreS dn m a vis fe M eb →
      KeptAll MM M eb → StackKept s₀.mem m → r.headD 0 = 0 → r.tail.headD 0 = 0 → s'.mem = m →
      (iotaRecFire2T (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI c)
        (rdW E (recP + 5)).toNat (rdW E (recP + 6)).toNat lps (decI us) args.toList (decI usj) cvj
        rule margs.toList).run a₀ = .ok (none, a) →
      CoreRef (iotaRecFire2T (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI c)
        (rdW E (recP + 5)).toNat (rdW E (recP + 6)).toNat lps (decI us) args.toList (decI usj) cvj
        rule margs.toList) a₀ decOptR dn s₀.mem vis fe MM eb r s'.mem ResW := by
    intro m a M hSm hK hSt h0 h1 hm hrunT
    obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _ hrunT
    refine ⟨hokF, ⟨M, by rw [hstF, hm]; exact hSm, hK, by rw [hm]; exact hSt⟩, ?_, ?_⟩
    · rw [hresF, decOptR_none_rec r h0]
    · unfold ResW HW; rw [h0, h1]; decide
  by_cases l1 : mn < rdW E (rl + 2)
  · rw [ite_eq_left l1] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨h0, h1, hm⟩ := hW
    exact hres0 s₀.mem a₀ MM hS (KeptAll.refl _ _) (StackKept.refl _) h0.symm h1.symm hm.symm
      (fire2T_run_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ a₀ (fun h => (hlen_iff.mp h).1 l1))
  rw [ite_eq_right l1] at hW
  by_cases l2 : mn - rdW E (rl + 2) ≠ rdW E (rl + 1)
  · rw [ite_eq_left l2] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨h0, h1, hm⟩ := hW
    exact hres0 s₀.mem a₀ MM hS (KeptAll.refl _ _) (StackKept.refl _) h0.symm h1.symm hm.symm
      (fire2T_run_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ a₀ (fun h => l2 (hlen_iff.mp h).2))
  rw [ite_eq_right l2] at hW
  have hlen : margs.toList.length = rule.ctorParams + rule.nfields :=
    hlen_iff.mpr ⟨l1, Classical.not_not.mp l2⟩
  have hcpm : rule.ctorParams ≤ mn.toNat := by omega
  cases n with
  | zero => rw [callW_zero] at hW; cases hW
  | succ N =>
  -- the family
  rcases c1 : callW p (N + 1) "iota_rec_fam" [mode, vis, d, us, recP, so, usj, ctorP, rl, mo, mn]
      s₀.mem with _ | ⟨rf, m1⟩ <;> simp only [c1, reduceCtorEq] at hW
  have hfm := iotaRecFam_refines' p hp hc hw hEI hER hEK N (hk.mono (by omega)) F (by omega)
    (by omega) ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb mode d us recP so usj ctorP rl mo mn sn lps
    rule cvj np nf args margs hS hm4 hebm hus husj
  simp only [hE0] at hfm
  obtain ⟨hrun1, ⟨M1, hS1, hK1, hSt1⟩, hr1⟩ := CoreSpec.run (hfm hlps hrule hci hfe hsa hsat hmI
    hsm hsmt hcpm) c1
  have e1 : m1.arr64 EREC = E := by rw [callW_iotaRecFam_erec p hp hER hEK _ _ _ _ _ rfl c1, hE0]
  by_cases g0 : rf.headD 0 = 0
  · rw [ite_eq_left g0] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨h0, h1, hm⟩ := hW
    rw [decBool_f_m2c g0] at hrun1
    exact hres0 m1 _ M1 hS1 hK1 hSt1 h0.symm h1.symm hm.symm
      (fire2T_run_fam _ _ _ _ _ _ _ _ _ _ _ _ _ _ a₀ _ hlen hrun1)
  rw [ite_eq_right g0] at hW
  rw [decBool_t_m2c g0] at hrun1
  rw [e1] at hW
  -- the right-hand side
  rcases c2 : callW p (N + 1) "rule_rhs_at" [c, rdW E rl, rdW E (recP + 2), rdW E (recP + 3),
      rdW E (rl + 8), us] m1 with _ | ⟨rr, m2⟩ <;> simp only [c2, reduceCtorEq] at hW
  obtain ⟨ok2, ⟨M2, hS2, hK2, hSt2⟩, res2, hr2⟩ := CoreSpec.of_callW
    (ruleRhsAt_refines' p hp.toIotaProg' hw.instLP (N + 1) ⟨m1, Locals.init []⟩ _ dn vis fe M1 eb c (rdW E rl)
      (rdW E (recP + 2)) (rdW E (recP + 3)) (rdW E (rl + 8)) us lps hS1 hcw hctw hrhsw hus
      (by rw [e1]; exact hlps)) c2
  have hrhs' : (decE (rdW E (rl + 8)) : EIdx) = rule.rhs := hrhs.symm
  rw [← hctor, hrhs'] at ok2 res2 hS2
  have hrun2' := AM.run_of_ok _ _ ok2
  rw [res2] at hrun2'
  simp only [decH] at hrun2'
  have hSt12 := hSt1.trans hSt2
  -- the leading arguments
  have hsa2 : SpineR m2 so sn args := hsa.keep hSt12.size hSt12.below hsat hspn
  have hxa := SpineR.take hsa2 (rpLen (rdW E (recP + 5)) (rdW E (recP + 6)))
    (by rw [rpLen_toNat]; omega)
  rw [rpLen_toNat, hmI, ← hsa.size, Array.length_toList.symm,
    ← List.take_eq_take_min] at hxa
  rcases c3 : callW p (N + 1) "mk_app_n" [rr.headD 0, so, rpLen (rdW E (recP + 5)) (rdW E (recP + 6))]
      m2 with _ | ⟨rx, m3⟩ <;> simp only [c3, reduceCtorEq] at hW
  obtain ⟨hrun3, hD3, hf3, hw3⟩ := irCallW_mkAppN p hp.spine (N + 1) m2 _ hS2.arena _ _ _ _ hr2 hxa
    rx m3 c3
  simp only at hrun3 hD3
  have hS3 := hS2.of_app hD3 (cpl_mkAppN _ _ _ _ _ hrun3) hf3
  have hSt3 := StackKept.of_app_frame hf3
  -- the fields
  have hSt13 := hSt12.trans hSt3
  have hsm3 : SpineR m3 mo mn margs := hsm.keep hSt13.size hSt13.below (by rw [← hsmt]; omega) hspn
  rcases c4 : callW p (N + 1) "mk_app_n_from" [rx.headD 0, mo, mn, rdW E (rl + 2)] m3 with _ | ⟨ry, m4⟩ <;>
    simp only [c4, reduceCtorEq] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨h0, h1, hm⟩ := hW
  obtain ⟨hrun4, hD4, hf4, hw4⟩ := irCallW_mkAppNFrom p hp.spine (N + 1) m3 _ hD3 _ _ _ _ _ hw3 hsm3
    (by rw [← hcpw]; exact hcpm) ry m4 c4
  rw [mkAppNFrom_eq_mkAppN' margs.size _ margs _ (by omega) (by rw [hsm.size, ← hcpw]; exact hcpm),
    ← hcpw] at hrun4 hD4
  have hS4 := hS3.of_app hD4 (cpl_mkAppN _ _ _ _ _ hrun4) hf4
  have hSt4 := StackKept.of_app_frame hf4
  have hrunF := fire2T_run_fire (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI c)
    _ _ lps (decI us) args.toList (decI usj) cvj rule margs.toList a₀ _ _ _ _ _ _ _ hlen hrun1 hrun2'
    hrun3 hrun4
  refine CoreRef.of_run hrunF (hm ▸ ⟨M2, hS4, hK1.trans hK2, hSt13.trans hSt4⟩) ?_ ?_
  · rw [decOptR_some_rec r h0.symm, ← h1]
  · unfold ResW HW; rw [← h0, ← h1]; exact ⟨by decide, hw4⟩

/-! ## `iota_rec_fire(mode, vis, d, c, us, recP, so, usj, ctorP, rl, major)` -/

/-- `iota_rec_fire2`'s error claim at fuel `n + 1` (the premises of `iotaRecFire2_refines'`). -/
def IotaRecFire2E (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d c us recP so usj ctorP rl mo mn sn : Word) (lps : List NIdx)
    (rule : IRecRule) (cvj : IConstantVal) (np nf : Nat) (args margs : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW c → HW us → HW usj →
    hslice? (s₀.mem.arr64 EREC) (rdW (s₀.mem.arr64 EREC) (recP + 2)).toNat
      (rdW (s₀.mem.arr64 EREC) (recP + 3)).toNat = some lps →
    decRule (s₀.mem.arr64 EREC) rl.toNat = some rule →
    decCI (s₀.mem.arr64 EREC) dn ctorP.toNat = some (.ctorInfo cvj np nf) →
    FireEnv fe lps rule cvj →
    SpineR s₀.mem so sn args → so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat + 1 = sn.toNat →
    SpineR s₀.mem mo mn margs → mo + mn = spTop s₀.mem →
    CoreSpecE p (n + 1) "iota_rec_fire2" [mode, vis, d, c, us, recP, so, usj, ctorP, rl, mo, mn]
      (iotaRecFire2T (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI c)
        (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat (rdW (s₀.mem.arr64 EREC) (recP + 6)).toNat lps
        (decI us) args.toList (decI usj) cvj rule margs.toList) s₀ a₀

/-- **What the fire's errors assume** at L fuel `n`: the knot's slots' claims, `iota_rec_fire2`'s. -/
structure FireG (p : Prog) (n : Nat) : Prop where
  knot : KnotUpToE p n
  fire2 : IotaRecFire2E p

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
    (hlps : hslice? (s₀.mem.arr64 EREC) (rdW (s₀.mem.arr64 EREC) (recP + 2)).toNat
      (rdW (s₀.mem.arr64 EREC) (recP + 3)).toNat = some lps)
    (hrule : decRule (s₀.mem.arr64 EREC) rl.toNat = some rule)
    (hci : decCI (s₀.mem.arr64 EREC) dn ctorP.toNat = some (.ctorInfo cvj np nf))
    (hfe : FireEnv fe lps rule cvj)
    (hsa : SpineR s₀.mem so sn args) (hsat : so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat)
    (hmI : (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat + 1 = sn.toNat) :
    RefE (FireG p n) (irFireE p (n + 1) s₀.mem mode vis d c us recP so usj ctorP rl major)
      (iotaRecFireT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI c)
        (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat (rdW (s₀.mem.arr64 EREC) (recP + 6)).toNat lps
        (decI us) args.toList (decE major) (decI usj) cvj rule) a₀
      (CorePost decOptR dn s₀.mem vis fe MM eb ResW) := by
  simp only [irFireE]
  have hspn := hS.spn
  cases n with
  | zero => rw [callW_zero, liftE_none, irFireE.k_get_app_args.none]; exact RefE.of_cls0 (by simp)
  | succ N =>
  -- the major's arguments
  rcases c1 : callW p (N + 1) "get_app_args" [major] s₀.mem with _ | ⟨ra, m1⟩
  · rw [liftE_none, irFireE.k_get_app_args.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨t1, ht1, -, fr1, gr1, hr0, htop1, xs, hrunA, hxs⟩ := triple_of_callW
    (getAppArgs_refines' p hp.spine.args hp.spine.cnt hp.spine.fill (N + 1) ⟨s₀.mem, Locals.init []⟩ a₀
      hS.arena.1 major hmaj hspn) c1
  rw [ht1] at fr1 gr1 htop1 hxs
  have hS1 : CoreS dn m1 a₀ vis fe MM eb := hS.frame_stk fr1 (by simp) (by simp)
  have e1 : m1.arr64 EREC = s₀.mem.arr64 EREC := fr1.1 EREC (by simp [SPN, EREC]) (by decide)
  simp only [irFireE.k_get_app_args]
  have hEq : (iotaRecFireT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI c)
      (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat (rdW (s₀.mem.arr64 EREC) (recP + 6)).toNat lps
      (decI us) args.toList (decE major) (decI usj) cvj rule).run a₀ =
      (iotaRecFire2T (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI c)
      (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat (rdW (s₀.mem.arr64 EREC) (recP + 6)).toNat lps
      (decI us) args.toList (decI usj) cvj rule xs.toArray.toList).run a₀ := by
    simp only [iotaRecFireT, StateT.run_bind, hrunA, except_ok_bind]
  refine RefE.of_run_eq hEq ?_
  have hsa1 := hsa.keep gr1.size gr1.below hsat hspn
  have hsat1 : so.toNat + sn.toNat ≤ (spTop m1).toNat := by
    have := UInt64.le_iff_toNat_le.mp gr1.1
    have htq : (spTop ({ mem := s₀.mem, loc := Locals.init [] } : St).mem).toNat =
      (spTop s₀.mem).toNat := rfl
    omega
  have hsm1 : ra.headD 0 + ra.tail.headD 0 = spTop m1 := by rw [htop1, hr0]
  -- the fire
  rcases c2 : callE p (N + 1) "iota_rec_fire2" [mode, vis, d, c, us, recP, so, usj, ctorP, rl,
      ra.headD 0, ra.tail.headD 0] m1 with e2 | ⟨rf, m2⟩
  · intro hG
    have h := hG.fire2 N (hk.mono (by omega)) (hG.knot.mono (by omega)) F (by omega) (by omega)
      ⟨m1, Locals.init []⟩ a₀ dn vis fe MM eb mode d c us recP so usj ctorP rl (ra.headD 0)
      (ra.tail.headD 0) sn lps rule cvj np nf args xs.toArray hS1 hm4 hebm hcw hus husj
    simp only [e1] at h
    exact CoreSpecE.of_callE (h hlps hrule hci hfe hsa1 hsat1 hmI hxs hsm1) c2
  have hf2 := iotaRecFire2_refines' p hp hc hw hEI hER hEK N (hk.mono (by omega)) F (by omega)
    (by omega) ⟨m1, Locals.init []⟩ a₀ dn vis fe MM eb mode d c us recP so usj ctorP rl (ra.headD 0)
    (ra.tail.headD 0) sn lps rule cvj np nf args xs.toArray hS1 hm4 hebm hcw hus husj
  simp only [e1] at hf2
  obtain ⟨hrun2, hP⟩ := (CoreSpec.of_callW (hf2 hlps hrule hci hfe hsa1 hsat1 hmI hxs hsm1)
    (callW_of_callE c2)).post
  refine RefE.ret hrun2 ?_
  obtain ⟨M2, hS2, hK2, hSt2⟩ := hP.after
  exact ⟨⟨M2, hS2.frame_stk (MemFrame.setCtl _ _ _) (by simp) (by simp), hK2,
    StackKept.restoreG' (gr1.trans hSt2.toGrew)⟩, hP.res, hP.valid⟩

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
    hslice? (s₀.mem.arr64 EREC) (rdW (s₀.mem.arr64 EREC) (recP + 2)).toNat
      (rdW (s₀.mem.arr64 EREC) (recP + 3)).toNat = some lps →
    decRule (s₀.mem.arr64 EREC) rl.toNat = some rule →
    decCI (s₀.mem.arr64 EREC) dn ctorP.toNat = some (.ctorInfo cvj np nf) →
    FireEnv fe lps rule cvj →
    SpineR s₀.mem so sn args → so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat + 1 = sn.toNat →
    CoreSpec p (n + 1) "iota_rec_fire" [mode, vis, d, c, us, recP, so, usj, ctorP, rl, major]
      (iotaRecFireT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI c)
        (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat (rdW (s₀.mem.arr64 EREC) (recP + 6)).toNat lps
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
    (m : Mem) (vis : Word) (fe : IFEnv) (hE : EnvR dn m vis fe) (w : Word) (hw : HW w)
    (r : List Word) (m' : Mem) (h : callW p n "env_find" [w, vis] m = some (r, m')) :
    m' = m ∧ (r.headD 0 = 0 → fe.find? (decI w) = none) ∧
      (r.headD 0 ≠ 0 → ∃ ci, fe.find? (decI w) = some ci ∧
        decCI (m.arr64 EREC) dn (r.tail.headD 0).toNat = some ci) := by
  obtain ⟨t₂, ht₂, hm₂, -, hfind⟩ := triple_of_callW
    (envFind_refines p hp.envix hp.envrow hp.envfind n ⟨m, Locals.init []⟩ vis w hE hw) h
  obtain ⟨t₂', ht₂', hm₂', -, hfound⟩ := triple_of_callW
    (envFind_found p hp.envix hp.envrow hp.envfind n ⟨m, Locals.init []⟩ vis w hw) h
  rw [ht₂] at hm₂
  refine ⟨hm₂, fun h0 => ?_, fun h0 => ?_⟩
  · rw [hfind]; simp only [decFound, h0, ↓reduceIte]
  · obtain ⟨htag2, hrow, hq⟩ := hfound h0
    obtain ⟨ci, hci⟩ := hE.found_some w hw htag2 hrow
    refine ⟨ci, ?_, ?_⟩
    · rw [hfind]; simp only [decFound, h0, ↓reduceIte, hq]; exact hci
    · rw [hq]; exact (erecP_ext m).decCI hci

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
  extra [ld64_rd_spec, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp []

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
    have h3 : hh >>> 28 = 3 := (decE_tag_eq _ hw 3 (by decide)).mp htag
    simp only [h3, ne_eq, not_true_eq_false, ↓reduceIte] at hW
    split at hW
    · cases hW
    split at hW
    · cases hW
    · simp only [Option.some.injEq] at hW; rw [← hW] at h0; simp at h0
  · simp only [irHeadW] at hW
    by_cases h3 : hh >>> 28 = 3
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

section majorRun
variable (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (c : NIdx)
  (us : LsIdx) (cv : IConstantVal) (mI rP : Nat) (rules : List IRecRule) (args : List EIdx)

theorem view_run_of (a : AState) (h : EIdx) (v : ENodeView) (hv : a.store.view h = some v) :
    (view h).run a = .ok (v, a) := by
  simp [view, hv, StateT.run_bind, StateT.run_get]; rfl

theorem majorT_run_tag (a a0 a1 : AState) (b0 major hh : EIdx)
    (h0 : (internE (.bvar 0)).run a = .ok (b0, a0))
    (h1 : (prepareMajor mode r fe depth c rules (args.getD mI b0)).run a0 = .ok (major, a1))
    (h2 : (getAppFn coreWalkFuel major).run a1 = .ok (hh, a1)) (ht : hh.tag ≠ ETag.const) :
    (iotaRecMajorT mode r fe depth c us cv mI rP rules args).run a = .ok (none, a1) := by
  have : (hh.tag == ETag.const) = false := by simpa using ht
  simp only [iotaRecMajorT, StateT.run_bind, h0, except_ok_bind, h1, h2, this,
    Bool.false_eq_true, ↓reduceIte]; rfl

theorem majorT_run_find (a a0 a1 : AState) (b0 major hh : EIdx) (cj : NIdx) (usj : LsIdx)
    (h0 : (internE (.bvar 0)).run a = .ok (b0, a0))
    (h1 : (prepareMajor mode r fe depth c rules (args.getD mI b0)).run a0 = .ok (major, a1))
    (h2 : (getAppFn coreWalkFuel major).run a1 = .ok (hh, a1)) (ht : hh.tag = ETag.const)
    (hv : a1.store.view hh = some (.const cj usj))
    (hf : ∀ cvj np nf, fe.find? cj ≠ some (.ctorInfo cvj np nf)) :
    (iotaRecMajorT mode r fe depth c us cv mI rP rules args).run a = .ok (none, a1) := by
  simp only [iotaRecMajorT, StateT.run_bind, h0, except_ok_bind, h1, h2, ht, beq_self_eq_true,
    ↓reduceIte, view_run_of _ _ _ hv]
  cases h : fe.find? cj with
  | none => rfl
  | some ci =>
    cases ci with
    | ctorInfo cvj np nf => exact absurd h (hf cvj np nf)
    | _ => rfl

theorem majorT_run_rule (a a0 a1 : AState) (b0 major hh : EIdx) (cj : NIdx) (usj : LsIdx)
    (cvj : IConstantVal) (np nf : Nat)
    (h0 : (internE (.bvar 0)).run a = .ok (b0, a0))
    (h1 : (prepareMajor mode r fe depth c rules (args.getD mI b0)).run a0 = .ok (major, a1))
    (h2 : (getAppFn coreWalkFuel major).run a1 = .ok (hh, a1)) (ht : hh.tag = ETag.const)
    (hv : a1.store.view hh = some (.const cj usj)) (hf : fe.find? cj = some (.ctorInfo cvj np nf))
    (hr : findRule rules cj = none) :
    (iotaRecMajorT mode r fe depth c us cv mI rP rules args).run a = .ok (none, a1) := by
  simp only [iotaRecMajorT, StateT.run_bind, h0, except_ok_bind, h1, h2, ht, beq_self_eq_true,
    ↓reduceIte, view_run_of _ _ _ hv, hf, hr]; rfl

theorem majorT_run_fire (a a0 a1 a2 : AState) (b0 major hh : EIdx) (cj : NIdx) (usj : LsIdx)
    (cvj : IConstantVal) (np nf : Nat) (rl : IRecRule) (res : Option EIdx)
    (h0 : (internE (.bvar 0)).run a = .ok (b0, a0))
    (h1 : (prepareMajor mode r fe depth c rules (args.getD mI b0)).run a0 = .ok (major, a1))
    (h2 : (getAppFn coreWalkFuel major).run a1 = .ok (hh, a1)) (ht : hh.tag = ETag.const)
    (hv : a1.store.view hh = some (.const cj usj)) (hf : fe.find? cj = some (.ctorInfo cvj np nf))
    (hr : findRule rules cj = some rl)
    (h3 : (iotaRecFireT mode r fe depth c mI rP cv.levelParams us args major usj cvj rl).run a1 =
      .ok (res, a2)) :
    (iotaRecMajorT mode r fe depth c us cv mI rP rules args).run a = .ok (res, a2) := by
  simp only [iotaRecMajorT, StateT.run_bind, h0, except_ok_bind, h1, h2, ht, beq_self_eq_true,
    ↓reduceIte, view_run_of _ _ _ hv, hf, hr, h3]

theorem majorT_err_pm (a a0 : AState) (b0 : EIdx)
    (h0 : (internE (.bvar 0)).run a = .ok (b0, a0)) (ce : CheckError)
    (h1 : (prepareMajor mode r fe depth c rules (args.getD mI b0)).run a0 = .error ce) :
    (iotaRecMajorT mode r fe depth c us cv mI rP rules args).run a = .error ce := by
  simp only [iotaRecMajorT, StateT.run_bind, h0, except_ok_bind, h1]; rfl

theorem majorT_err_fire (a a0 a1 : AState) (b0 major hh : EIdx) (cj : NIdx) (usj : LsIdx)
    (cvj : IConstantVal) (np nf : Nat) (rl : IRecRule)
    (h0 : (internE (.bvar 0)).run a = .ok (b0, a0))
    (h1 : (prepareMajor mode r fe depth c rules (args.getD mI b0)).run a0 = .ok (major, a1))
    (h2 : (getAppFn coreWalkFuel major).run a1 = .ok (hh, a1)) (ht : hh.tag = ETag.const)
    (hv : a1.store.view hh = some (.const cj usj)) (hf : fe.find? cj = some (.ctorInfo cvj np nf))
    (hr : findRule rules cj = some rl) (ce : CheckError)
    (h3 : (iotaRecFireT mode r fe depth c mI rP cv.levelParams us args major usj cvj rl).run a1 =
      .error ce) :
    (iotaRecMajorT mode r fe depth c us cv mI rP rules args).run a = .error ce := by
  simp only [iotaRecMajorT, StateT.run_bind, h0, except_ok_bind, h1, h2, ht, beq_self_eq_true,
    ↓reduceIte, view_run_of _ _ _ hv, hf, hr, h3]

end majorRun

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
    (hr : decRules (m.arr64 EREC) ro.toNat rc.toNat = some rules) (r : List Word) (m' : Mem)
    (h : callW p n "find_rule" [ro, rc, c] m = some (r, m')) (hne : r.headD 0 ≠ 0) :
    ∃ rule, decRule (m.arr64 EREC) (r.tail.headD 0).toNat = some rule := by
  obtain ⟨t, ht, -, -, hW⟩ := triple_of_callW (findRule_spec p hp n ⟨m, Locals.init []⟩ ro rc c) h
  subst hW
  obtain ⟨j, hj, hq⟩ := frN_found _ ro rc c 0 hne
  obtain ⟨hl, hg⟩ := decRules_get _ _ _ _ hr
  have hj' : j.toNat < rc.toNat := hj
  have hdr := hg j.toNat hj'
  obtain ⟨rule, hrule⟩ : ∃ rule, rules[j.toNat]? = some rule :=
    ⟨rules[j.toNat], List.getElem?_eq_getElem (by omega)⟩
  rw [hrule] at hdr
  obtain ⟨hw, -⟩ := rule_idx _ ro j rule hsz hdr
  refine ⟨rule, ?_⟩
  rw [hq]
  show decRule (m.arr64 EREC) (ro + 11 * j).toNat = some rule
  rw [hw]; exact hdr

/-- `prepare_major`'s error claim at fuel `N + 1` (the premises of `prepareMajor_refines'`). -/
def PrepareMajorE (p : Prog) : Prop :=
  ∀ (N : Nat), KnotUpTo p N → KnotUpToE p N → ∀ (F : Nat), N ≤ F → N ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d rec ro rc major : Word) (rules : List IRecRule),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW major →
    decRules (s₀.mem.arr64 EREC) ro.toNat rc.toNat = some rules →
    CoreSpecE p (N + 1) "prepare_major" [mode, vis, d, rec, ro, rc, major]
      (prepareMajor (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI rec) rules
        (decE major)) s₀ a₀

/-- `iota_rec_fire`'s error claim at fuel `N + 1` (the premises of `iotaRecFire_refines'`). -/
def IotaRecFireE (p : Prog) : Prop :=
  ∀ (N : Nat), KnotUpTo p N → KnotUpToE p N → ∀ (F : Nat), N ≤ F → N ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d c us recP so usj ctorP rl major sn : Word) (lps : List NIdx)
    (rule : IRecRule) (cvj : IConstantVal) (np nf : Nat) (args : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW c → HW us → HW usj →
    HW major →
    hslice? (s₀.mem.arr64 EREC) (rdW (s₀.mem.arr64 EREC) (recP + 2)).toNat
      (rdW (s₀.mem.arr64 EREC) (recP + 3)).toNat = some lps →
    decRule (s₀.mem.arr64 EREC) rl.toNat = some rule →
    decCI (s₀.mem.arr64 EREC) dn ctorP.toNat = some (.ctorInfo cvj np nf) →
    FireEnv fe lps rule cvj →
    SpineR s₀.mem so sn args → so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat + 1 = sn.toNat →
    CoreSpecE p (N + 1) "iota_rec_fire" [mode, vis, d, c, us, recP, so, usj, ctorP, rl, major]
      (iotaRecFireT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI c)
        (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat (rdW (s₀.mem.arr64 EREC) (recP + 6)).toNat lps
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
    (hcv : decCV (s₀.mem.arr64 EREC) (recP.toNat + 1) = some cv)
    (hrules : decRules (s₀.mem.arr64 EREC) (rdW (s₀.mem.arr64 EREC) (recP + 7)).toNat
      (rdW (s₀.mem.arr64 EREC) (recP + 8)).toNat = some rules)
    (hrecF : ∃ cr mI rP, fe.find? cr = some (.recInfo cv mI rP rules))
    (hsa : SpineR s₀.mem so sn xs) (hsat : so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat)
    (hmI : (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat + 1 = sn.toNat) :
    RefE (MajorG p n) (irMajorE p (n + 1) s₀.mem mode vis d c us recP so sn)
      (iotaRecMajorT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI c) (decI us)
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
  -- `bvar 0`
  rcases c0 : callW p (N + 1) "intern_bvar" [0] s₀.mem with _ | ⟨rb, m1⟩
  · rw [liftE_none, irMajorE.k_intern_bvar.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨hrun0, hS1, hSt1, e1, hspn1⟩ := irCallW_internBVar p hp (N + 1) hS 0 rb m1 c0
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
  have hrules1 : decRules (m1.arr64 EREC) (rdW E (recP + 7)).toNat (rdW E (recP + 8)).toNat =
      some rules := by rw [e1, hE0]; exact hrules
  rcases c1 : callE p (N + 1) "prepare_major" [mode, vis, d, c, rdW E (recP + 7), rdW E (recP + 8),
      rdW (s₀.mem.arr64 SPN) (so + rdW E (recP + 5))] m1 with e1' | ⟨rm, m2⟩
  · intro hG
    exact ErrClaim.of_run_err (fun ce h' => majorT_err_pm (h0 := hrun0) (ce := ce)
        (h1 := by rw [hgetD]; exact h') ..)
      (CoreSpecE.of_callE (hG.pm N (hk.mono (by omega)) (hG.knot.mono (by omega)) F (by omega)
        (by omega) ⟨m1, Locals.init []⟩ _ dn vis fe MM eb mode d c (rdW E (recP + 7))
        (rdW E (recP + 8)) (rdW (s₀.mem.arr64 SPN) (so + rdW E (recP + 5))) rules hS1 hm4 hebm hmaj
        hrules1) c1)
  have hpm := prepareMajor_refines' p hp.toIotaProg4 hc hw hsup hmtc hEK N (hk.mono (by omega)) F
    (by omega) (by omega) ⟨m1, Locals.init []⟩ _ dn vis fe MM eb mode d c (rdW E (recP + 7))
    (rdW E (recP + 8)) (rdW (s₀.mem.arr64 SPN) (so + rdW E (recP + 5))) rules hS1 hm4 hebm hmaj
  obtain ⟨hrun1, ⟨M2, hS2, hK2, hSt2⟩, hr1⟩ := CoreSpec.run (hpm hrules1) (callW_of_callE c1)
  simp only [decH] at hrun1
  have e2 : m2.arr64 EREC = E := by rw [hEK _ _ _ _ _ _ (by simp) (callW_of_callE c1), e1, hE0]
  simp only [irMajorE.k_prepare_major]
  -- the head
  rcases c2 : callW p (N + 1) "get_app_fn" [rm.headD 0] m2 with _ | ⟨rh, m3⟩
  · rw [liftE_none, irMajorE.k_get_app_fn.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨t2, ht2, hm3, -, hhw, hrun2⟩ := triple_of_callW
    (getAppFn_refines' p hp.spine.fn (N + 1) ⟨m2, Locals.init []⟩ _ hS2.arena.1 (rm.headD 0) hr1) c2
  have hm3' : m2 = m3 := hm3.symm.trans ht2
  subst hm3'
  simp only [irMajorE.k_get_app_fn]
  rcases c3 : callW p (N + 1) "iota_rec_head" [rh.headD 0] m2 with _ | ⟨rv, m4⟩
  · rw [liftE_none, irMajorE.k_iota_rec_head.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨hm4, hnot, hyes⟩ := irCallW_head p hp.head (N + 1) m2 _ hS2.arena.1 _ hhw rv m4 c3
  subst m4
  have hSt12 := hSt1.trans hSt2
  have hpost : ∀ (a : AState), CorePost decOptR dn s₀.mem vis fe MM eb ResW ([0, 0], m2) none a ↔
      CoreAfter dn s₀.mem m2 a vis fe MM eb :=
    fun a => ⟨fun h => h.after, fun h => ⟨h, rfl,
      ⟨by show HW (0 : Word); unfold HW; decide, by show HW (0 : Word); unfold HW; decide⟩⟩⟩
  simp only [irMajorE.k_iota_rec_head]
  by_cases v0 : rv.headD 0 = 0
  · rw [ite_eq_left v0]
    exact RefE.ret (majorT_run_tag _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrun0
      (by rw [hgetD]; exact hrun1) hrun2 (hnot v0)) ((hpost _).mpr ⟨M2, hS2, hK2, hSt12⟩)
  rw [ite_eq_right v0]
  obtain ⟨htag, hview, hcjw, husjw⟩ := hyes v0
  -- the constructor
  rcases c4 : callW p (N + 1) "env_find" [rv.tail.headD 0, vis] m2 with _ | ⟨re, m5⟩
  · rw [liftE_none, irMajorE.k_env_find.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨hm5, hfnone, hfsome⟩ := irEnvFind p hp.toIotaProg' (N + 1) dn m2 vis fe hS2.env _ hcjw re m5 c4
  subst m5
  simp only [irMajorE.k_env_find, e2]
  by_cases f0 : re.headD 0 = 0
  · rw [ite_eq_left f0]
    exact RefE.ret (majorT_run_find _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrun0
      (by rw [hgetD]; exact hrun1) hrun2 htag hview
      (fun cvj np nf h => by rw [hfnone f0] at h; cases h)) ((hpost _).mpr ⟨M2, hS2, hK2, hSt12⟩)
  rw [ite_eq_right f0]
  obtain ⟨ci, hfind, hci⟩ := hfsome f0
  rw [e2] at hci
  by_cases k4 : rdW E (re.tail.headD 0) ≠ 4
  · rw [ite_eq_left k4]
    have hnc := (decCI_ctor hci (ArrExt.refl _) herec).2 k4
    exact RefE.ret (majorT_run_find _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrun0
      (by rw [hgetD]; exact hrun1) hrun2 htag hview
      (fun cvj np nf h => by rw [hfind] at h; cases h; exact hnc cvj np nf rfl))
      ((hpost _).mpr ⟨M2, hS2, hK2, hSt12⟩)
  rw [ite_eq_right k4]
  obtain ⟨cvj, np, nf, rfl, -⟩ := decCI_ctor_rd hci (Classical.not_not.mp k4)
  -- the rule
  have hEsz : (m2.arr64 EREC).size < 2 ^ 64 := by rw [e2]; omega
  have hrules2 : decRules (m2.arr64 EREC) (rdW E (recP + 7)).toNat (rdW E (recP + 8)).toNat =
      some rules := by rw [e2]; exact hrules
  rcases c5 : callW p (N + 1) "find_rule" [rdW E (recP + 7), rdW E (recP + 8), rv.tail.headD 0] m2
    with _ | ⟨rr, m6⟩
  · rw [liftE_none, irMajorE.k_find_rule.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨t5, ht5, hm6, -, hfr⟩ := triple_of_callW
    (findRule_refines p hp.findRule (N + 1) ⟨m2, Locals.init []⟩ _ _ _ rules hcjw hEsz hrules2) c5
  have hm6' : m2 = m6 := hm6.symm.trans ht5
  subst hm6'
  simp only [irMajorE.k_find_rule]
  by_cases g0 : rr.headD 0 = 0
  · rw [ite_eq_left g0]
    have : findRule rules (decI (rv.tail.headD 0)) = none := by
      rw [hfr]; simp only [decRuleAt, g0, ↓reduceIte]
    exact RefE.ret (majorT_run_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrun0
      (by rw [hgetD]; exact hrun1) hrun2 htag hview hfind this)
      ((hpost _).mpr ⟨M2, hS2, hK2, hSt12⟩)
  rw [ite_eq_right g0]
  obtain ⟨rule, hdr⟩ := findRule_found p hp.findRule (N + 1) m2 _ _ _ rules hEsz hrules2 rr m2 c5 g0
  rw [e2] at hdr
  have hfrs : findRule rules (decI (rv.tail.headD 0)) = some rule := by
    rw [hfr]; simp only [decRuleAt, g0, ↓reduceIte, e2, hdr]
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
    exact ErrClaim.of_run_err (fun ce h' => majorT_err_fire (h0 := hrun0)
        (h1 := by rw [hgetD]; exact hrun1) (h2 := hrun2) (ht := htag) (hv := hview) (hf := hfind)
        (hr := hfrs) (ce := ce) (h3 := h') ..)
      (CoreSpecE.of_callE (h hlps hdr hci hfe hsa2 hsat2 hmI) c6)
  have hfi := iotaRecFire_refines' p hp hc hw hEI hER hEK N (hk.mono (by omega)) F (by omega)
    (by omega) ⟨m2, Locals.init []⟩ _ dn vis fe M2 eb mode d c us recP so (rv.tail.tail.headD 0)
    (re.tail.headD 0) (rr.tail.headD 0) (rm.headD 0) sn cv.levelParams rule cvj np nf xs hS2 hm4 hebm
    hcw hus husjw hr1
  simp only [e2] at hfi
  obtain ⟨hrun6, ⟨M6, hS6, hK6, hSt6⟩, hr6⟩ := CoreSpec.run (hfi hlps hdr hci hfe hsa2 hsat2 hmI)
    (callW_of_callE c6)
  simp only [irMajorE.k_iota_rec_fire]
  refine RefE.ret (majorT_run_fire _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrun0
    (by rw [hgetD]; exact hrun1) hrun2 htag hview hfind hfrs hrun6)
    ⟨⟨M6, hS6, hK2.trans hK6, hSt12.trans hSt6⟩, ?_, ?_⟩
  · simp only [decOptR]; rfl
  · unfold ResW at hr6 ⊢; exact hr6

/-- **`iota_rec_major` refines `iotaRecMajorT`** (`major_ref`'s ok half). -/
theorem iotaRecMajor_refines' (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hsup : ∀ fe : IFEnv, SupKeep fe) (hmtc : MajorToCtorOK p)
    (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d c us recP so sn : Word) (cv : IConstantVal) (rules : List IRecRule)
    (xs : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW c → HW us →
    decCV (s₀.mem.arr64 EREC) (recP.toNat + 1) = some cv →
    decRules (s₀.mem.arr64 EREC) (rdW (s₀.mem.arr64 EREC) (recP + 7)).toNat
      (rdW (s₀.mem.arr64 EREC) (recP + 8)).toNat = some rules →
    (∃ cr mI rP, fe.find? cr = some (.recInfo cv mI rP rules)) →
    SpineR s₀.mem so sn xs → so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat + 1 = sn.toNat →
    CoreSpec p (n + 1) "iota_rec_major" [mode, vis, d, c, us, recP, so, sn]
      (iotaRecMajorT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI c) (decI us)
        cv (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat (rdW (s₀.mem.arr64 EREC) (recP + 6)).toNat rules
        xs.toList) decOptR s₀ a₀ dn vis fe MM eb ResW :=
  fun n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d c us recP so sn cv rules xs hS hm4 hebm hcw hus
      hcv hrules hrecF hsa hsat hmI =>
    RefE.coreSpec (irMajorE_spec p hp.major (n + 1) s₀ mode vis d c us recP so sn)
      (major_ref p hp hc hw hsup hmtc hEI hER hEK n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d c us recP
        so sn cv rules xs hS hm4 hebm hcw hus hcv hrules hrecF hsa hsat hmI)

end L.Arena
