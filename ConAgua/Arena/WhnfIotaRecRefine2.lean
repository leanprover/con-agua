module

import ConAgua.Arena.RecLayout.CapsDec
import ConAgua.Arena.LdRd
import ConAgua.Arena.RecFireEnv
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.DerRel
import ConAgua.Arena.RefWalk
import ConAgua.Arena.WhnfCoreProj
import ConAgua.Arena.WhnfCoreRefine
import ConAgua.Checker.NoVerdictTree
import ConAgua.L.ModelGen
public import ConAgua.Arena.WhnfIotaRecRefine
import all ConAgua.Arena.WhnfIotaRec
import all ConAgua.Arena.WhnfIota
import ConAgua.Arena.IotaCase3Ref
import ConAgua.L.WordOff
import ConAgua.Arena.DefEqMid
import ConAgua.Arena.IndRealOpf2
import ConAgua.Arena.RecLayout.CIDec

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

/-! ## The stored facts: `rec_fire_level_count`, `iota_no_cert` -/

/-- **`rec_fire_level_count`'s model** (read-only, no callee). -/
l_model rflcW_spec (p : Prog) (hp : p.lookup "rec_fire_level_count" = some recFireLevelCountL)
  fns [hp ↦ rflcW ro]
  grind [arena_grind]

/-- **`iota_no_cert`'s model**: one `env_find`, the family record's words. -/
l_model incW_spec (p : Prog) (hp : p.lookup "iota_no_cert" = some iotaNoCertL)
  fns [hp ↦ incW]
  specs [callW_spec p n "env_find"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE]

/-- **`rec_fire_level_count` refines `recFireLevelCount`** at a decoded rule and constructor: the
fire kind word `rl + Rule.fire`, the stored level list's length `rl + Rule.lvlsLen`, the constructor's level count
`ctorP + (CI.cv + CV.lpsLen)`. -/
@[refines ConRon.Arena.recFireLevelCount]
theorem rflc_count {m : Mem} {rl ctorP : Word} {rule : IRecRule} {cvj : IConstantVal} {np nf : Nat}
    {fam : NIdx} (hrule : decRule (erecP m) rl.toNat = some rule)
    (hci : decCI (erecP m) ctorP.toNat = some (.ctorInfo cvj np nf fam)) :
    rflcW m (erRd m (rl + Rule.fire)) (erRd m (rl + Rule.lvlsLen)) (erRd m (ctorP + (CI.cv + CV.lpsLen))) =
      some (if erRd m (rl + Rule.fire) = 0 then erRd m (ctorP + (CI.cv + CV.lpsLen)) else erRd m (rl + Rule.lvlsLen)) ∧
    recFireLevelCount rule cvj.levelParams =
      (if erRd m (rl + Rule.fire) = 0 then erRd m (ctorP + (CI.cv + CV.lpsLen)) else erRd m (rl + Rule.lvlsLen)).toNat := by
  refine ⟨by unfold rflcW; split <;> simp_all, ?_⟩
  obtain ⟨-, -, -, hlen, -, -⟩ := decCV_rd_ci (p := ctorP) (erRdOK m) (decCI_ctorInfo_iff.mp hci).2.1
  rcases decRule_fireE (erRdOK m) hrule with ⟨h0, hpl⟩ | ⟨h0, lvls, hk, hsl⟩
  · simp only [recFireLevelCount, hpl, h0, ↓reduceIte, hlen]
  · rw [ite_eq_right h0]
    rcases hk with hk | ⟨pins, hk⟩ <;> simp only [recFireLevelCount, hk] <;> exact hslice?_lenR hsl

/-- **`iota_no_cert` as a run**: the memory unchanged; the answer word is the twin's
`iotaNoCert` at the family handle `T` and the count `nn`. -/
theorem inc_ok (p : Prog) (hp : IotaProg' p) {n : Nat} {dn : NIdx → Option ConLeche.Name} {m : Mem}
    {a : AState} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb)
    {isK T nn : Word} (hT : HW T) {r : Word} {m' : Mem}
    (h : incW p n m vis isK T nn = some (r, m')) :
    m' = m ∧ (r ≠ 0 ↔ iotaNoCert fe (isK != 0) (decI T) nn.toNat = true) := by
  cases n with
  | zero => simp [incW] at h
  | succ n =>
  simp only [incW] at h
  by_cases hK : isK ≠ 0
  · rw [ite_eq_left hK] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, by simp [iotaNoCert, hK]⟩
  rw [ite_eq_right hK] at h
  have hK' : (isK != 0) = false := by simpa using hK
  rcases c4 : callW p n "env_find" [T, vis] m with _ | ⟨r₄, m₄⟩
  · rw [c4] at h; simp [incW.k_env_find] at h
  rw [c4] at h
  obtain ⟨t₄, ht₄, hm₄, -, hfind, hdec⟩ := triple_of_callW
    (envFind_refines p hp.envrow hp.baserow hp.envfind n ⟨m, Locals.init []⟩ vis _ hS.env hT) c4
  have e4 : m = m₄ := hm₄.symm.trans ht₄
  subst e4
  simp only [incW.k_env_find] at h
  by_cases h0 : r₄.headD 0 = 0
  · rw [ite_eq_left h0] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hnone : fe.find? (decI T) = none := by rw [hfind]; simp only [envFound, h0, ↓reduceIte]
    exact ⟨rfl, by simp [iotaNoCert, hK', hnone]⟩
  rw [ite_eq_right h0] at h
  obtain ⟨ci, hci4⟩ := hdec h0
  have hf' : fe.find? (decI T) = some ci := by
    rw [hfind]; simp only [envFound, h0, ↓reduceIte]; exact hci4
  have hk := decCI_ind_rd (erRdOK m) hci4
  by_cases k3 : erRd m (r₄.tail.headD 0) ≠ 3
  · rw [ite_eq_left (by simpa [erRd] using k3)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, ?_⟩
    simp only [iotaNoCert, hK', hf', Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false,
      false_iff]
    cases ci <;> first | exact absurd rfl (hk.2 k3 _ _) | simp
  rw [ite_eq_right (by simpa [erRd] using k3)] at h
  obtain ⟨cvT, caps, rfl⟩ := hk.1 (Classical.not_not.mp k3)
  obtain ⟨-, -, hnz, -⟩ := decCI_indInfo_rd (erRdOK m) hci4
  obtain ⟨-, -, -, hlen, -, -⟩ := decCV_rd_ci (erRdOK m) (decCI_indInfo_iff.mp hci4).2.1
  simp only [erRd] at hnz hlen
  generalize r₄.tail.headD 0 = q at *
  by_cases g : rdW (m.arr64 (tierA EREC ((q + (CI.indCaps + Caps.neverZero)) >>> 40)))
      (q + (CI.indCaps + Caps.neverZero) &&& 1099511627775) = 0
  · rw [ite_eq_left g] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, by simp [iotaNoCert, hK', hf', hnz, g]⟩
  rw [ite_eq_right g] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨rfl, ?_⟩
  by_cases e : rdW (m.arr64 (tierA EREC ((q + (CI.cv + CV.lpsLen)) >>> 40))) (q + (CI.cv + CV.lpsLen) &&& 1099511627775) = nn
  · simp [iotaNoCert, hK', hf', hnz, g, hlen, e]
  · have e' : ¬ (rdW (m.arr64 (tierA EREC ((q + (CI.cv + CV.lpsLen)) >>> 40))) (q + (CI.cv + CV.lpsLen) &&& 1099511627775)).toNat =
        nn.toNat := fun h' => e (UInt64.toNat_inj.mp h')
    simp [iotaNoCert, hK', hf', hnz, g, hlen, e, e']

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
    (hlps : hslice? (erecP s₀.mem) (erRd s₀.mem (recP + (CI.cv + CV.lpsOff))).toNat
      (erRd s₀.mem (recP + (CI.cv + CV.lpsLen))).toNat = some lps)
    (hrule : decRule (erecP s₀.mem) rl.toNat = some rule)
    {fam : NIdx} (hci : decCI (erecP s₀.mem) ctorP.toNat = some (.ctorInfo cvj np nf fam))
    (hfe : FireEnv fe lps rule cvj)
    (hsa : SpineR s₀.mem so sn args) (hsat : so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat)
    (hmI : (erRd s₀.mem (recP + CI.recMajor)).toNat + 1 = sn.toNat)
    (hsm : SpineR s₀.mem mo mn margs) (hsmt : mo + mn = spTop s₀.mem)
    (hcpm : np ≤ mn.toNat) :
    RefE (FamG p n) (irFamE p (n + 1) s₀.mem mode vis d us recP so usj ctorP rl mo mn)
      (iotaRecFamT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (erRd s₀.mem (recP + CI.recIsK) != 0) fam
        (erRd s₀.mem (recP + CI.recMajor)).toNat (erRd s₀.mem (recP + CI.recPrefix)).toNat np lps
        (decI us) args.toList (decI usj) cvj rule margs.toList) a₀
      (CorePost decBool dn s₀.mem vis fe MM eb ResH) := by
  simp only [irFamE]
  have hspn := hS.spn
  have hfc := fireCore_of hS hrule hci hfe
  have hld := lpsDen_of hS hfe
  have hmsz : (mo + mn).toNat = mo.toNat + mn.toNat := by
    have := hsm.bound; rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  unfold iotaRecFamT
  rw [decMode_verified mode hm4]
  by_cases hv : mode &&& 1 ≠ 0
  · rw [ite_eq_left hv, ite_eq_left (by simpa using hv)]
    exact RefE.ret rfl (CorePost.ret hS rfl (by show HW (1 : Word); unfold HW; decide))
  rw [ite_eq_right hv, ite_eq_right (by simpa using hv)]
  -- the stored facts (`iotaNoCert`)
  have hk4 : erRd s₀.mem ctorP = 4 := Classical.byContradiction fun h =>
    (decCI_ctorR (erRdOK s₀.mem) hci).2 h _ _ _ _ rfl
  obtain ⟨cv', he, hfw⟩ := (decCI_ctorR (erRdOK s₀.mem) hci).1 hk4
  simp only [IConstantInfo.ctorInfo.injEq] at he
  obtain ⟨-, -, -, rfl⟩ := he
  obtain ⟨hW0, hcnt⟩ := rflc_count hrule hci
  rcases c0 : callW p n "rec_fire_level_count" [erRd s₀.mem (rl + Rule.fire), erRd s₀.mem (rl + Rule.lvlsLen),
      erRd s₀.mem (ctorP + (CI.cv + CV.lpsLen))] s₀.mem with _ | ⟨r0, m0⟩
  · erw [c0, liftE_none, irFamE.k_rec_fire_level_count.none]; exact RefE.of_cls0 (by simp)
  erw [c0, liftE_some, irFamE.k_rec_fire_level_count.arm1]
  obtain ⟨t0, ht0, -, hm0, hr0⟩ := triple_of_callW
    (rflcW_spec p hp.recFireLevelCount n ⟨s₀.mem, Locals.init []⟩ _ _ _) c0
  have em0 : m0 = s₀.mem := ht0.symm.trans hm0
  subst em0
  rw [hW0] at hr0
  have hr0' := (Option.some.inj hr0).symm
  rcases c1 : callW p n "iota_no_cert" [vis, erRd s₀.mem (recP + CI.recIsK), erRd s₀.mem (ctorP + CI.ctorInduct),
      r0.headD 0] s₀.mem with _ | ⟨r1, m1⟩
  · erw [c1, liftE_none, irFamE.k_iota_no_cert.none]; exact RefE.of_cls0 (by simp)
  erw [c1, liftE_some]
  obtain ⟨t1, ht1, -, hW1⟩ := triple_of_callW
    (incW_spec p hp.iotaNoCert n ⟨s₀.mem, Locals.init []⟩ _ _ _ _) c1
  obtain ⟨em1, hnc⟩ := inc_ok p hp.toIotaProg' hS hfw hW1
  have em1' : m1 = s₀.mem := ht1.symm.trans em1
  subst em1'
  rw [hr0', ← hcnt] at hnc
  by_cases g1 : r1.headD 0 ≠ 0
  · erw [irFamE.k_iota_no_cert.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g1]
    rw [ite_eq_left (hnc.mp g1)]
    exact RefE.ret rfl (CorePost.ret hS rfl (by show HW (1 : Word); unfold HW; decide))
  erw [irFamE.k_iota_no_cert.arm2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by simpa using g1)]
  rw [ite_eq_right (fun h => g1 (hnc.mpr h))]
  -- the comparand levels
  refine RefE.bindLift (fun _ => rfl) fun rv m1 c1 => ?_
  obtain ⟨hrun1, ⟨M1, hS1, hK1, hSt1⟩, hr1⟩ := CoreSpec.run
    (hc.recFireLevels n ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb _ _ _ _ _ us _ _ rule lps
      cvj.levelParams hS hus hlps hld hfc) c1
  have k1 := hER.all (by simp [iotaKeptFns]) c1
  refine ⟨_, _, hrun1, ?_⟩
  simp only [irFamE.k_rec_fire_levels, erRd_congr k1.1 k1.2.1]
  cases n with
  | zero => exact RefE.callE_zero (fun _ => rfl)
  | succ N =>
  -- case 3
  refine RefE.bindRun (s₀ := ⟨m1, Locals.init []⟩) (fun _ => rfl)
    (ic3E_spec p hp.iotaCase3At hp.formerNeverZeroAt hp.formerSortLoop (N + 1) ⟨m1, Locals.init []⟩
      mode vis (erRd s₀.mem (recP + CI.recIsK)) (erRd s₀.mem (ctorP + CI.ctorInduct)) (rv.headD 0))
    (fun hG => hG.nv) (fun hG => hG.knot.mono (Nat.le_succ _))
    (ic3_ref p hp.toIotaProg4 (hp.fnzaProg hw.instLP hc.inst1) N F (hk.mono (Nat.le_succ _)) (by omega)
      (by omega) dn vis fe eb mode hm4 hebm m1 _ M1 _ _ _ hS1 hfw hr1)
    fun r3 s2 _ a2 c2 _ _ hP => ?_
  obtain ⟨⟨M2, hS2, hK2, hSt2⟩, hr3, -⟩ := hP
  have k2 := erecKeep_trans (hER.all (by simp [iotaKeptFns]) (callW_of_callE c2)) k1
  have hSt12 := hSt1.trans hSt2
  dsimp only [irFamE.k_iota_case3_at]
  subst hr3
  refine RefE.retIf L.Arena.decBool_false_of (fun h => by simpa [decBool] using h)
    (fun _ => ⟨⟨M2, hS2, hK1.trans hK2, hSt12⟩, rfl, by show HW (1 : Word); unfold HW; decide⟩) fun g0 _ => ?_
  have hsa2 := hsa.keep hSt12.size hSt12.below hsat hspn
  have hsat2 : so.toNat + sn.toNat ≤ (spTop s2.mem).toNat := by rw [hSt12.1]; exact hsat
  have hsm2 := hsm.keep hSt12.size hSt12.below (by rw [← hsmt, hmsz]; exact Nat.le_refl _) hspn
  have hsmt2 : mo + mn = spTop s2.mem := by rw [hSt12.1]; exact hsmt
  have hvk := vck_ref p hp hc hw hEI hER hEK N (hk.mono (by omega)) F (by omega) (by omega)
    ⟨s2.mem, Locals.init []⟩ _ dn vis fe M2 eb mode d us recP so usj ctorP rl mo mn (rv.headD 0) sn lps rule
    cvj np nf args margs hS2 hm4 hebm hus husj hr1
  rw [k2.2.2.1, k2.2.2.2] at hvk
  rw [← bind_pure (iotaRecVckT _ _ _ _ _ _ _ _ _ _ _ _ _ _)]
  refine RefE.bindRun (s₀ := ⟨s2.mem, Locals.init []⟩) (fun _ => rfl)
    (vckE_spec p hp.vck (N + 1) ⟨s2.mem, Locals.init []⟩ mode vis d us recP so usj ctorP rl mo mn (rv.headD 0))
    (fun hG => hG.nv) (fun hG => hG.mono (by omega)) (hvk hlps hrule hci hsa2 hsat2 hmI hsm2 hsmt2 hcpm)
    fun rk s3 _ a3 _ _ _ ⟨⟨M3, hS3, hK3, hSt3⟩, hr3, hv3⟩ => ?_
  exact RefE.ret rfl ⟨⟨M3, hS3, hK1.trans (hK2.trans hK3), hSt12.trans hSt3⟩, hr3, hv3⟩

/-- **`iota_rec_fam` refines the certificate family** (`fam_ref`'s ok half). -/
theorem iotaRecFam_refines' (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d us recP so usj ctorP rl mo mn sn : Word) (lps : List NIdx)
    (rule : IRecRule) (cvj : IConstantVal) (np nf : Nat) (fam : NIdx) (args margs : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW us → HW usj →
    hslice? (erecP s₀.mem) (erRd s₀.mem (recP + (CI.cv + CV.lpsOff))).toNat
      (erRd s₀.mem (recP + (CI.cv + CV.lpsLen))).toNat = some lps →
    decRule (erecP s₀.mem) rl.toNat = some rule →
    decCI (erecP s₀.mem) ctorP.toNat = some (.ctorInfo cvj np nf fam) →
    FireEnv fe lps rule cvj →
    SpineR s₀.mem so sn args → so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    (erRd s₀.mem (recP + CI.recMajor)).toNat + 1 = sn.toNat →
    SpineR s₀.mem mo mn margs → mo + mn = spTop s₀.mem → np ≤ mn.toNat →
    CoreSpec p (n + 1) "iota_rec_fam" [mode, vis, d, us, recP, so, usj, ctorP, rl, mo, mn]
      (iotaRecFamT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (erRd s₀.mem (recP + CI.recIsK) != 0) fam
        (erRd s₀.mem (recP + CI.recMajor)).toNat (erRd s₀.mem (recP + CI.recPrefix)).toNat np lps
        (decI us) args.toList (decI usj) cvj rule margs.toList) decBool s₀ a₀ dn vis fe MM eb :=
  fun n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d us recP so usj ctorP rl mo mn sn lps rule cvj np nf _fam
      args margs hS hm4 hebm hus husj hlps hrule hci hfe hsa hsat hmI hsm hsmt hcpm =>
    RefE.coreSpec (irFamE_spec p hp.fam (n + 1) s₀ mode vis d us recP so usj ctorP rl mo mn)
      (fam_ref p hp hc hw hEI hER hEK n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d us recP so usj ctorP
        rl mo mn sn lps rule cvj np nf args margs hS hm4 hebm hus husj hlps hrule hci hfe hsa hsat hmI
        hsm hsmt hcpm)

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

/-- **`eidx_copy_upto`'s model** (generated): its loop `ecuW.loop1`. -/
l_model eidxCopy_spec (p : Prog) (hp : p.lookup "eidx_copy_upto" = some eidxCopyUptoL)
  fns [hp ↦ ecuW list]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE,
    evalE_idxAE, evalE_idxGE, evalE_tagE]

/-- **`iota_rec_fire2`'s model, both outcomes** (generated; `iota_rec_fam` through its run,
`rule_body_at`, `mk_app_n`, `mk_app_n_from` lifted). -/
l_model fire2E_spec (p : Prog) (hp : p.lookup "iota_rec_fire2" = some iotaRecFire2L)
  fns [hp ↦ fire2E list]
  specs [callW_spec p n "rule_body_at", callW_spec p n "eidx_copy_upto", callW_spec p n "inst_list"]
  grind [arena_grind] fold [rpLen] extra [ld64_rdW_specE, ld64_rdW_specT] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

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
    (hlps : hslice? (erecP s₀.mem) (erRd s₀.mem (recP + (CI.cv + CV.lpsOff))).toNat
      (erRd s₀.mem (recP + (CI.cv + CV.lpsLen))).toNat = some lps)
    (hrule : decRule (erecP s₀.mem) rl.toNat = some rule)
    {fam : NIdx} (hci : decCI (erecP s₀.mem) ctorP.toNat = some (.ctorInfo cvj np nf fam))
    (hfe : FireEnv fe lps rule cvj)
    (hsa : SpineR s₀.mem so sn args) (hsat : so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat)
    (hmI : (erRd s₀.mem (recP + CI.recMajor)).toNat + 1 = sn.toNat)
    (hsm : SpineR s₀.mem mo mn margs) (hsmt : mo + mn = spTop s₀.mem) :
    RefE (FamG p n) (fire2E p (n + 1) s₀.mem mode vis d c us recP so usj ctorP rl mo mn)
      (iotaRecFire2T (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI c) (erRd s₀.mem (recP + CI.recIsK) != 0) fam
        (erRd s₀.mem (recP + CI.recMajor)).toNat (erRd s₀.mem (recP + CI.recPrefix)).toNat np lps
        (decI us) args.toList (decI usj) cvj rule margs.toList) a₀
      (CorePost decOptR dn s₀.mem vis fe MM eb ResW) := by
  sorry

/-- **`iota_rec_fire2` refines the fire past the major's arguments** (`fire2_ref`'s ok half). -/
theorem iotaRecFire2_refines' (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d c us recP so usj ctorP rl mo mn sn : Word) (lps : List NIdx)
    (rule : IRecRule) (cvj : IConstantVal) (np nf : Nat) (fam : NIdx) (args margs : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW c → HW us → HW usj →
    hslice? (erecP s₀.mem) (erRd s₀.mem (recP + (CI.cv + CV.lpsOff))).toNat
      (erRd s₀.mem (recP + (CI.cv + CV.lpsLen))).toNat = some lps →
    decRule (erecP s₀.mem) rl.toNat = some rule →
    decCI (erecP s₀.mem) ctorP.toNat = some (.ctorInfo cvj np nf fam) →
    FireEnv fe lps rule cvj →
    SpineR s₀.mem so sn args → so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    (erRd s₀.mem (recP + CI.recMajor)).toNat + 1 = sn.toNat →
    SpineR s₀.mem mo mn margs → mo + mn = spTop s₀.mem →
    CoreSpec p (n + 1) "iota_rec_fire2" [mode, vis, d, c, us, recP, so, usj, ctorP, rl, mo, mn]
      (iotaRecFire2T (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI c) (erRd s₀.mem (recP + CI.recIsK) != 0) fam
        (erRd s₀.mem (recP + CI.recMajor)).toNat (erRd s₀.mem (recP + CI.recPrefix)).toNat np lps
        (decI us) args.toList (decI usj) cvj rule margs.toList) decOptR s₀ a₀ dn vis fe MM eb ResW :=
  fun n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d c us recP so usj ctorP rl mo mn sn lps rule cvj np nf _fam
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
    (hlps : hslice? (erecP s₀.mem) (erRd s₀.mem (recP + (CI.cv + CV.lpsOff))).toNat
      (erRd s₀.mem (recP + (CI.cv + CV.lpsLen))).toNat = some lps)
    (hrule : decRule (erecP s₀.mem) rl.toNat = some rule)
    {fam : NIdx} (hci : decCI (erecP s₀.mem) ctorP.toNat = some (.ctorInfo cvj np nf fam))
    (hfe : FireEnv fe lps rule cvj)
    (hsa : SpineR s₀.mem so sn args) (hsat : so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat)
    (hmI : (erRd s₀.mem (recP + CI.recMajor)).toNat + 1 = sn.toNat) :
    RefE (FamG p n) (irFireE p (n + 1) s₀.mem mode vis d c us recP so usj ctorP rl major)
      (iotaRecFireT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI c) (erRd s₀.mem (recP + CI.recIsK) != 0) fam
        (erRd s₀.mem (recP + CI.recMajor)).toNat (erRd s₀.mem (recP + CI.recPrefix)).toNat np lps
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
  have k1 := hER.all (by simp [iotaKeptFns]) c1
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
  rw [k1.2.2.1, k1.2.2.2] at h
  rw [← bind_pure (iotaRecFire2T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)]
  refine RefE.bindRun (s₀ := ⟨m1, Locals.init []⟩) (fun _ => rfl)
    (fire2E_spec p hp.fire2 (N + 1) ⟨m1, Locals.init []⟩ mode vis d c us recP so usj ctorP rl (ra.headD 0)
      (ra.tail.headD 0)) (fun hG => hG.nv) (fun hG => hG.mono (by omega))
    (h hlps hrule hci hfe hsa1 hsat1 hmI hxs hsm1) fun rf s2 _ a2 _ _ _ hP => ?_
  obtain ⟨M2, hS2, hK2, hSt2⟩ := hP.after
  exact RefE.ret rfl ⟨⟨M2, hS2.frame_stk (MemFrame.setCtl _ _ _) (by simp) (by simp), hK2,
    StackKept.restoreG' (gr1.trans hSt2.toGrew)⟩, hP.res, hP.valid⟩

/-- **`iota_rec_fire` refines the fire** (`fire_ref`'s ok half). -/
theorem iotaRecFire_refines' (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d c us recP so usj ctorP rl major sn : Word) (lps : List NIdx)
    (rule : IRecRule) (cvj : IConstantVal) (np nf : Nat) (fam : NIdx) (args : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW c → HW us → HW usj →
    HW major →
    hslice? (erecP s₀.mem) (erRd s₀.mem (recP + (CI.cv + CV.lpsOff))).toNat
      (erRd s₀.mem (recP + (CI.cv + CV.lpsLen))).toNat = some lps →
    decRule (erecP s₀.mem) rl.toNat = some rule →
    decCI (erecP s₀.mem) ctorP.toNat = some (.ctorInfo cvj np nf fam) →
    FireEnv fe lps rule cvj →
    SpineR s₀.mem so sn args → so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    (erRd s₀.mem (recP + CI.recMajor)).toNat + 1 = sn.toNat →
    CoreSpec p (n + 1) "iota_rec_fire" [mode, vis, d, c, us, recP, so, usj, ctorP, rl, major]
      (iotaRecFireT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI c) (erRd s₀.mem (recP + CI.recIsK) != 0) fam
        (erRd s₀.mem (recP + CI.recMajor)).toNat (erRd s₀.mem (recP + CI.recPrefix)).toNat np lps
        (decI us) args.toList (decE major) (decI usj) cvj rule) decOptR s₀ a₀ dn vis fe MM eb
      ResW :=
  fun n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d c us recP so usj ctorP rl major sn lps rule cvj np
      nf _fam args hS hm4 hebm hcw hus husj hmaj hlps hrule hci hfe hsa hsat hmI =>
    RefE.coreSpec (irFireE_spec p hp.fire (n + 1) s₀ mode vis d c us recP so usj ctorP rl major)
      (fire_ref p hp hc hw hEI hER hEK n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d c us recP so usj
        ctorP rl major sn lps rule cvj np nf args hS hm4 hebm hcw hus husj hmaj hlps hrule hci hfe hsa
        hsat hmI)

/-! ## `env_find` and `intern_bvar` as runs -/

/-- **`env_find` as a run**: the memory unchanged, `find?` decoded at the record pool. -/
theorem irEnvFind (p : Prog) (hp : IotaProg' p) (n : Nat) (_dn : NIdx → Option ConLeche.Name)
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

theorem findRule_mem : ∀ (rules : List IRecRule) (c : NIdx) (rl : IRecRule),
    findRule rules c = some rl → rl ∈ rules ∧ rl.ctor = c
  | [], _, _, h => by simp [findRule] at h
  | x :: xs, c, rl, h => by
    simp only [findRule] at h
    split at h
    · rename_i hx; cases h; exact ⟨List.mem_cons_self .., by simpa using hx⟩
    · obtain ⟨h1, h2⟩ := findRule_mem xs c rl h; exact ⟨List.mem_cons_of_mem _ h1, h2⟩


/-- A found rule's record is one of the slice's: `find_rule` answers `ro + Rule.size * j`, `j < rc`. -/
theorem frN_found (rd : Word → Word) (ro rc c : Word) (i : Nat) (hne : (frN rd ro rc c i).headD 0 ≠ 0) :
    ∃ j : Word, j < rc ∧ (frN rd ro rc c i).tail.headD 0 = ro + Rule.size * j := by
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
  obtain ⟨hl, hg⟩ := decRules_get hr
  have hj' : j.toNat < rc.toNat := hj
  have hdr := hg j.toNat hj'
  obtain ⟨rule, hrule⟩ : ∃ rule, rules[j.toNat]? = some rule :=
    ⟨rules[j.toNat], List.getElem?_eq_getElem (by omega)⟩
  rw [hrule] at hdr
  have hw := rule_idx (erRdOK m) ro j hdr
  refine ⟨rule, ?_⟩
  rw [hq]
  show decRule (erecP m) (ro + Rule.size * j).toNat = some rule
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
    (rule : IRecRule) (cvj : IConstantVal) (np nf : Nat) (fam : NIdx) (args : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW c → HW us → HW usj →
    HW major →
    hslice? (erecP s₀.mem) (erRd s₀.mem (recP + (CI.cv + CV.lpsOff))).toNat
      (erRd s₀.mem (recP + (CI.cv + CV.lpsLen))).toNat = some lps →
    decRule (erecP s₀.mem) rl.toNat = some rule →
    decCI (erecP s₀.mem) ctorP.toNat = some (.ctorInfo cvj np nf fam) →
    FireEnv fe lps rule cvj →
    SpineR s₀.mem so sn args → so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    (erRd s₀.mem (recP + CI.recMajor)).toNat + 1 = sn.toNat →
    CoreSpecE p (N + 1) "iota_rec_fire" [mode, vis, d, c, us, recP, so, usj, ctorP, rl, major]
      (iotaRecFireT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI c)
        (erRd s₀.mem (recP + CI.recIsK) != 0) fam
        (erRd s₀.mem (recP + CI.recMajor)).toNat (erRd s₀.mem (recP + CI.recPrefix)).toNat np lps
        (decI us) args.toList (decE major) (decI usj) cvj rule) s₀ a₀

/-! ## A constructor view is the environment's -/

theorem AM.run_bind_ok' {α β : Type} {x : AM α} {f : α → AM β} {a a' : AState} {v : β}
    (h : (x >>= f).run a = .ok (v, a')) : ∃ y a₁, x.run a = .ok (y, a₁) ∧ (f y).run a₁ = .ok (v, a') := by
  rw [StateT.run_bind] at h
  cases hx : x.run a with
  | error e => rw [hx] at h; cases h
  | ok q => rw [hx] at h; exact ⟨q.1, q.2, rfl, h⟩

theorem AM.run_pure_ok {α : Type} {x v : α} {a a' : AState} (h : (pure x : AM α).run a = .ok (v, a')) :
    v = x := by
  have := (Prod.mk.inj (Except.ok.inj h)).1; exact this.symm

/-- **A constructor view's record is the environment's**: `fe.find?` gives the view's record. -/
def ViewFound (fe : IFEnv) (v : MajorView) : Prop :=
  ∀ e cj usj cvj nP nF ind, v = .ctor e cj usj cvj nP nF ind →
    fe.find? cj = some (.ctorInfo cvj nP nF ind)

theorem ViewFound.stuck (fe : IFEnv) (e : EIdx) : ViewFound fe (.stuck e) :=
  fun _ _ _ _ _ _ _ h => by cases h

theorem ctorView_found {fe : IFEnv} {e : EIdx} {a a' : AState} {v : MajorView}
    (h : (ctorView fe e).run a = .ok (v, a')) : ViewFound fe v := by
  unfold ctorView at h
  obtain ⟨hd, a1, -, h⟩ := AM.run_bind_ok' h
  split at h
  · obtain ⟨o, a2, -, h⟩ := AM.run_bind_ok' h
    split at h
    · simp [failDanglingE, ConRon.Arena.fail, StateT.run] at h; cases h
    · rename_i cj usj
      split at h
      · rename_i cvj nP nF ind hf
        rw [AM.run_pure_ok h]
        intro _ _ _ _ _ _ _ hv
        cases hv; exact hf
      · rw [AM.run_pure_ok h]; exact ViewFound.stuck _ _
  · rw [AM.run_pure_ok h]; exact ViewFound.stuck _ _

theorem majorToCtor_found {mode : ConLeche.CheckMode} {r : CoreFnsA} {fe : IFEnv} {d : Nat} {rec : NIdx}
    {isK : Bool} {rules : List IRecRule} {major : EIdx} {a a' : AState} {v : MajorView}
    (h : (majorToCtor mode r fe d rec isK rules major).run a = .ok (v, a')) : ViewFound fe v := by
  unfold majorToCtor at h
  obtain ⟨v1, a1, h1, h⟩ := AM.run_bind_ok' h
  split at h
  · rw [AM.run_pure_ok h]; exact ctorView_found h1
  · obtain ⟨x, a2, -, h⟩ := AM.run_bind_ok' h
    split at h
    · rw [AM.run_pure_ok h]; exact ViewFound.stuck _ _
    · exact ctorView_found h

theorem prepareMajorWhnf_found {mode : ConLeche.CheckMode} {r : CoreFnsA} {fe : IFEnv} {d : Nat}
    {rec : NIdx} {isK : Bool} {rules : List IRecRule} {major : EIdx} {a a' : AState} {v : MajorView}
    (h : (prepareMajorWhnf mode r fe d rec isK rules major).run a = .ok (v, a')) : ViewFound fe v := by
  unfold prepareMajorWhnf at h
  obtain ⟨_, _, -, h⟩ := AM.run_bind_ok' h
  obtain ⟨_, _, -, h⟩ := AM.run_bind_ok' h
  exact majorToCtor_found h

theorem prepareMajor_found {mode : ConLeche.CheckMode} {r : CoreFnsA} {fe : IFEnv} {d : Nat}
    {rec : NIdx} {isK : Bool} {rules : List IRecRule} {major : EIdx} {a a' : AState} {v : MajorView}
    (h : (prepareMajor mode r fe d rec isK rules major).run a = .ok (v, a')) : ViewFound fe v := by
  unfold prepareMajor at h
  split at h
  · exact majorToCtor_found h
  · have tail : ∀ (vE : MajorView) (a2 : AState), ViewFound fe vE →
        (if vE.isCtor = true then (do
            let b ← isNatSuccApp vE.expr
            if b = true then prepareMajorWhnf mode r fe d rec isK rules vE.expr else pure vE)
          else prepareMajorWhnf mode r fe d rec isK rules vE.expr).run a2 = .ok (v, a') →
        ViewFound fe v := by
      intro vE a2 hf h
      split at h
      · obtain ⟨b, _, -, h⟩ := AM.run_bind_ok' h
        split at h
        · exact prepareMajorWhnf_found h
        · rw [AM.run_pure_ok h]; exact hf
      · exact prepareMajorWhnf_found h
    obtain ⟨s, a1, -, h⟩ := AM.run_bind_ok' h
    simp only at h
    split at h
    · obtain ⟨vE, a2, h2, h⟩ := AM.run_bind_ok' h
      rw [AM.run_pure_ok h2] at h
      exact tail _ _ (ViewFound.stuck _ _) h
    · obtain ⟨vE, a2, h2, h⟩ := AM.run_bind_ok' h
      exact tail _ _ (majorToCtor_found h2) h

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
    (hw : WhnfCallees p) (hmtc : MajorToCtorOK p)
    (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hnF : n ≤ F) (hn62 : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d c us recP so sn : Word) (cv : IConstantVal) (rules : List IRecRule)
    (xs : Array EIdx) (hS : CoreS dn s₀.mem a₀ vis fe MM eb) (hm4 : mode < 4)
    (hebm : eb = (mode >>> 1) &&& 1) (hcw : HW c) (hus : HW us)
    (hcv : decCV (erecP s₀.mem) (recP.toNat + CI.cv.toNat) = some cv)
    (hrules : decRules (erecP s₀.mem) (erRd s₀.mem (recP + CI.recRulesOff)).toNat
      (erRd s₀.mem (recP + CI.recRulesLen)).toNat = some rules)
    (hrecF : ∃ cr mI rP isK, fe.find? cr = some (.recInfo cv mI rP isK rules))
    (hsa : SpineR s₀.mem so sn xs) (hsat : so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat)
    (hmI : (erRd s₀.mem (recP + CI.recMajor)).toNat + 1 = sn.toNat) :
    RefE (MajorG p n) (irMajorE p (n + 1) s₀.mem mode vis d c us recP so sn)
      (iotaRecMajorT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI c) (decI us)
        cv (erRd s₀.mem (recP + CI.recMajor)).toNat (erRd s₀.mem (recP + CI.recPrefix)).toNat
        (erRd s₀.mem (recP + CI.recIsK) != 0) rules xs.toList) a₀ (CorePost decOptR dn s₀.mem vis fe MM eb ResW) := by
  simp only [irMajorE]
  have hspn := hS.spn
  obtain ⟨-, -, hlps, -, -, -⟩ := decCV_rd_ci (erRdOK s₀.mem) hcv
  cases n with
  | zero => rw [callW_zero, liftE_none, irMajorE.k_intern_bvar.eq_1]; exact RefE.of_cls0 (by simp)
  | succ N =>
  unfold iotaRecMajorT
  -- `bvar 0`
  refine RefE.bindLift (fun _ => rfl) fun rb m1 c0 => ?_
  obtain ⟨hrun0, hS1, hSt1, -, hspn1⟩ := irCallW_internBVar p hp (N + 1) hS 0 rb m1 c0
  have k1 := hER.all (by simp [iotaKeptFns]) c0
  refine ⟨_, _, hrun0, ?_⟩
  simp only [irMajorE.k_intern_bvar, erRd_congr k1.1 k1.2.1, hspn1]
  -- the major
  have hmIl : (erRd s₀.mem (recP + CI.recMajor)).toNat < sn.toNat := by omega
  have hmw : so + erRd s₀.mem (recP + CI.recMajor) = so + (erRd s₀.mem (recP + CI.recMajor)).toNat.toUInt64 := by
    rw [L.toUInt64_toNat]
  have hmaj : HW (rdW (s₀.mem.arr64 SPN) (so + erRd s₀.mem (recP + CI.recMajor))) := by
    have := hsa.lt _ hmIl; unfold HW; rw [hmw]; exact this
  have hgetD : xs.toList.getD (erRd s₀.mem (recP + CI.recMajor)).toNat (decE (rb.headD 0)) =
      decE (rdW (s₀.mem.arr64 SPN) (so + erRd s₀.mem (recP + CI.recMajor))) := by
    have hsz := hsa.size
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hsz]; exact hmIl),
      Option.getD_some]
    have := hsa.get _ (by rw [hsz]; exact hmIl)
    simp only [Array.getElem_toList]
    rw [this, hmw]; rfl
  rw [hgetD]
  have hrules1 : decRules (erecP m1) (erRd s₀.mem (recP + CI.recRulesOff)).toNat (erRd s₀.mem (recP + CI.recRulesLen)).toNat =
      some rules := by rw [k1.2.2.2]; exact hrules
  rcases c1 : callE p (N + 1) "prepare_major" [mode, vis, d, c, erRd s₀.mem (recP + CI.recIsK),
      erRd s₀.mem (recP + CI.recRulesOff), erRd s₀.mem (recP + CI.recRulesLen),
      rdW (s₀.mem.arr64 SPN) (so + erRd s₀.mem (recP + CI.recMajor))] m1 with e1' | ⟨rm, m2⟩
  · exact RefE.bind_left fun hG => CoreSpecE.of_callE (hG.pm N (hk.mono (by omega))
      (hG.knot.mono (by omega)) F (by omega) (by omega) ⟨m1, Locals.init []⟩ _ dn vis fe MM eb mode d c
      (erRd s₀.mem (recP + CI.recIsK)) (erRd s₀.mem (recP + CI.recRulesOff)) (erRd s₀.mem (recP + CI.recRulesLen))
      (rdW (s₀.mem.arr64 SPN) (so + erRd s₀.mem (recP + CI.recMajor))) rules hS1 hm4 hebm hmaj hrules1) c1
  have hpm := prepareMajor_refines' p hp.toIotaProg4 hc hw hmtc hER N (hk.mono (by omega)) F
    (by omega) (by omega) ⟨m1, Locals.init []⟩ _ dn vis fe MM eb mode d c (erRd s₀.mem (recP + CI.recIsK))
    (erRd s₀.mem (recP + CI.recRulesOff)) (erRd s₀.mem (recP + CI.recRulesLen))
    (rdW (s₀.mem.arr64 SPN) (so + erRd s₀.mem (recP + CI.recMajor))) rules hS1 hm4 hebm hmaj
  obtain ⟨hrun1, ⟨M2, hS2, hK2, hSt2⟩, hr1⟩ := CoreSpec.run (hpm hrules1) (callW_of_callE c1)
  have hfound := prepareMajor_found hrun1
  have k2 := erecKeep_trans (hER.all (by simp [iotaKeptFns]) (callW_of_callE c1)) k1
  refine RefE.bind_right hrun1 ?_
  simp only [irMajorE.k_prepare_major]
  have hSt12 := hSt1.trans hSt2
  have hpost : ∀ (a : AState), CoreAfter dn s₀.mem m2 a vis fe MM eb →
      CorePost decOptR dn s₀.mem vis fe MM eb ResW ([0, 0], m2) none a :=
    fun a h => ⟨h, rfl, ⟨by show HW (0 : Word); unfold HW; decide, by show HW (0 : Word); unfold HW; decide⟩⟩
  obtain ⟨hlen, hw1, hw2, hw3, hq⟩ := hr1
  by_cases v0 : rm.headD 0 = 0
  · rw [ite_eq_left v0]
    have : decMV m1 rm = .stuck (decE (rm.getD 1 0)) := by unfold decMV; dsimp only; rw [if_pos v0]
    simp only [this]
    exact RefE.ret rfl (hpost _ ⟨M2, hS2, hK2, hSt12⟩)
  rw [ite_eq_right v0]
  obtain ⟨cvj, cnP, cnF, ind, hci⟩ := hq v0
  have hview : decMV m1 rm = .ctor (decE (rm.getD 1 0)) (decI (rm.getD 2 0)) (decI (rm.getD 3 0)) cvj cnP cnF ind := by
    unfold decMV; simp only [v0, ↓reduceIte, hci]
  have hfind := hfound _ _ _ _ _ _ _ hview
  rw [k1.2.2.2] at hci
  simp only [hview]
  have hg1 : rm.getD 1 0 = rm.tail.headD 0 := by
    match rm, hlen with | [_, _, _, _, _], _ => rfl
  have hg2 : rm.getD 2 0 = rm.tail.tail.headD 0 := by
    match rm, hlen with | [_, _, _, _, _], _ => rfl
  have hg3 : rm.getD 3 0 = rm.tail.tail.tail.headD 0 := by
    match rm, hlen with | [_, _, _, _, _], _ => rfl
  have hg4 : rm.getD 4 0 = rm.tail.tail.tail.tail.headD 0 := by
    match rm, hlen with | [_, _, _, _, _], _ => rfl
  rw [hg1] at hw1 ⊢; rw [hg2] at hw2 ⊢; rw [hg3] at hw3 ⊢; rw [hg4] at hci
  simp only [erRd_congr k2.1 k2.2.1]
  -- the rule
  have hrules2 : decRules (erecP m2) (erRd s₀.mem (recP + CI.recRulesOff)).toNat (erRd s₀.mem (recP + CI.recRulesLen)).toNat =
      some rules := by rw [k2.2.2.2]; exact hrules
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun rr m6 c5 => ?_
  obtain ⟨t5, ht5, hm6, -, hfr⟩ := triple_of_callW
    (findRule_refines p hp.findRule (N + 1) ⟨m2, Locals.init []⟩ _ _ _ rules hw2 hrules2) c5
  have hm6' : m2 = m6 := hm6.symm.trans ht5
  subst hm6'
  dsimp only [irMajorE.k_find_rule]
  by_cases g0 : rr.headD 0 = 0
  · rw [ite_eq_left g0, hfr]
    simp only [decRuleAt, g0, ↓reduceIte]
    exact RefE.ret rfl (hpost _ ⟨M2, hS2, hK2, hSt12⟩)
  rw [ite_eq_right g0]
  obtain ⟨rule, hdr⟩ := findRule_found p hp.findRule (N + 1) m2 _ _ _ rules hrules2 rr m2 c5 g0
  have hfrs : findRule rules (decI (rm.tail.tail.headD 0)) = some rule := by
    rw [hfr]; simp only [decRuleAt, g0, ↓reduceIte, hdr]
  rw [k2.2.2.2] at hdr
  rw [hfrs]
  obtain ⟨hmem, -⟩ := findRule_mem _ _ _ hfrs
  have hfe : FireEnv fe cv.levelParams rule cvj := by
    obtain ⟨cr, mI, rP, isK, hfr⟩ := hrecF
    exact ⟨⟨cr, cv, mI, rP, isK, rules, hfr, rfl, hmem⟩, ⟨_, _, _, _, hfind⟩⟩
  have hsa2 := hsa.keep hSt12.size hSt12.below hsat hspn
  have hsat2 : so.toNat + sn.toNat ≤ (spTop m2).toNat := by rw [hSt12.1]; exact hsat
  -- the fire
  rcases c6 : callE p (N + 1) "iota_rec_fire" [mode, vis, d, c, us, recP, so, rm.tail.tail.tail.headD 0,
      rm.tail.tail.tail.tail.headD 0, rr.tail.headD 0, rm.tail.headD 0] m2 with e6 | ⟨rf, m7⟩
  · intro hG
    have h := hG.fire N (hk.mono (by omega)) (hG.knot.mono (by omega)) F (by omega) (by omega)
      ⟨m2, Locals.init []⟩ _ dn vis fe M2 eb mode d c us recP so (rm.tail.tail.tail.headD 0)
      (rm.tail.tail.tail.tail.headD 0) (rr.tail.headD 0) (rm.tail.headD 0) sn cv.levelParams rule cvj cnP
      cnF ind xs hS2 hm4 hebm hcw hus hw3 hw1
    rw [k2.2.2.1, k2.2.2.2] at h
    exact CoreSpecE.of_callE (h hlps hdr hci hfe hsa2 hsat2 hmI) c6
  have hfi := iotaRecFire_refines' p hp hc hw hEI hER hEK N (hk.mono (by omega)) F (by omega)
    (by omega) ⟨m2, Locals.init []⟩ _ dn vis fe M2 eb mode d c us recP so (rm.tail.tail.tail.headD 0)
    (rm.tail.tail.tail.tail.headD 0) (rr.tail.headD 0) (rm.tail.headD 0) sn cv.levelParams rule cvj cnP cnF
    ind xs hS2 hm4 hebm hcw hus hw3 hw1
  rw [k2.2.2.1, k2.2.2.2] at hfi
  obtain ⟨hrun6, ⟨M6, hS6, hK6, hSt6⟩, hr6⟩ := CoreSpec.run (hfi hlps hdr hci hfe hsa2 hsat2 hmI)
    (callW_of_callE c6)
  dsimp only [irMajorE.k_iota_rec_fire]
  refine RefE.ret hrun6 ⟨⟨M6, hS6, hK2.trans hK6, hSt12.trans hSt6⟩, ?_, ?_⟩
  · simp only [decOptR]; rfl
  · unfold ResW at hr6 ⊢; exact hr6

/-- **`iota_rec_major` refines `iotaRecMajorT`** (`major_ref`'s ok half). -/
theorem iotaRecMajor_refines' (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hmtc : MajorToCtorOK p)
    (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d c us recP so sn : Word) (cv : IConstantVal) (rules : List IRecRule)
    (xs : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW c → HW us →
    decCV (erecP s₀.mem) (recP.toNat + CI.cv.toNat) = some cv →
    decRules (erecP s₀.mem) (erRd s₀.mem (recP + CI.recRulesOff)).toNat
      (erRd s₀.mem (recP + CI.recRulesLen)).toNat = some rules →
    (∃ cr mI rP isK, fe.find? cr = some (.recInfo cv mI rP isK rules)) →
    SpineR s₀.mem so sn xs → so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    (erRd s₀.mem (recP + CI.recMajor)).toNat + 1 = sn.toNat →
    CoreSpec p (n + 1) "iota_rec_major" [mode, vis, d, c, us, recP, so, sn]
      (iotaRecMajorT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI c) (decI us)
        cv (erRd s₀.mem (recP + CI.recMajor)).toNat (erRd s₀.mem (recP + CI.recPrefix)).toNat
        (erRd s₀.mem (recP + CI.recIsK) != 0) rules xs.toList) decOptR s₀ a₀ dn vis fe MM eb ResW :=
  fun n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d c us recP so sn cv rules xs hS hm4 hebm hcw hus hcv
      hrules hrecF hsa hsat hmI =>
    RefE.coreSpec (irMajorE_spec p hp.major (n + 1) s₀ mode vis d c us recP so sn)
      (major_ref p hp hc hw hmtc hEI hER hEK n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d c us
        recP so sn cv rules xs hS hm4 hebm hcw hus hcv hrules hrecF hsa hsat hmI)

end L.Arena
