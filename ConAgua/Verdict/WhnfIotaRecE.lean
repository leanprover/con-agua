import ConAgua.Verdict.WhnfModels4E
import ConAgua.Verdict.WhnfIotaE

/-!
# The fire's verdict claims: `iota_rec_fire`, `iota_rec_fire2`, `iota_rec_fam`, `iota_rec_vck`
(lane `verdicts-b`, helper `k2`)

`iota_rec_vck`'s level comparison out of fuel declines (the twin's `liftFueled`); its other claims
are `iota_rec_cmp`'s, `iota_certs_full`'s, `iota_index_ok`'s (hypotheses `IotaRecCmpE`,
`IotaCertsFullE`, `IotaIndexOkE`, the premises of their ok refinements). The rest propagates
(`iotaRecFireE_of`: `IotaRecFireE`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

/-- `iota_rec_cmp`'s error claim at fuel `N + 1` (the premises of `iotaRecCmp_refines'`). -/
def IotaRecCmpE (p : Prog) : Prop :=
  ∀ (N : Nat), KnotUpTo p N → KnotUpToE p N → ∀ (F : Nat), N ≤ F → N ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d us recP so rl mo mn sn : Word) (lps : List NIdx) (rule : IRecRule)
    (args margs : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW us →
    hslice? (s₀.mem.arr64 EREC) (rdW (s₀.mem.arr64 EREC) (recP + 2)).toNat
      (rdW (s₀.mem.arr64 EREC) (recP + 3)).toNat = some lps →
    decRule (s₀.mem.arr64 EREC) rl.toNat = some rule →
    SpineR s₀.mem so sn args → so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat + 1 = sn.toNat →
    SpineR s₀.mem mo mn margs → mo.toNat + mn.toNat ≤ (spTop s₀.mem).toNat →
    rule.ctorParams ≤ mn.toNat →
    CoreSpecE p (N + 1) "iota_rec_cmp" [mode, vis, d, us, recP, so, rl, mo]
      (iotaRecCmpT (coreKnot (decMode mode) fe id F) fe d.toNat rule lps (decI us) args.toList
        (rdW (s₀.mem.arr64 EREC) (recP + 6)).toNat margs.toList) s₀ a₀

/-- `iota_certs_full`'s error claim at fuel `N + 1` (the premises of `iotaCertsFull_refines'`). -/
def IotaCertsFullE (p : Prog) : Prop :=
  ∀ (N : Nat), KnotUpTo p N → KnotUpToE p N → ∀ (F : Nat), N ≤ F → N ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d h ao an : Word) (args : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW h →
    SpineR s₀.mem ao an args → ao + an = spTop s₀.mem →
    CoreSpecE p (N + 1) "iota_certs_full" [mode, vis, d, h, ao, an]
      (iotaCertsFull (coreKnot (decMode mode) fe id F) fe d.toNat (decE h) args.toList) s₀ a₀

/-- `iota_index_ok`'s error claim at fuel `N + 1` (the premises of `iotaIndexOk_refines'`). -/
def IotaIndexOkE (p : Prog) : Prop :=
  ∀ (N : Nat), KnotUpTo p N → KnotUpToE p N → ∀ (F : Nat), N ≤ F → N ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d mI rP cnP tyCtor mo mn xo xn : Word) (margs idx : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW tyCtor →
    SpineR s₀.mem mo mn margs → SpineR s₀.mem xo xn idx →
    mo.toNat + mn.toNat ≤ (spTop s₀.mem).toNat → xo.toNat + xn.toNat ≤ (spTop s₀.mem).toNat →
    CoreSpecE p (N + 1) "iota_index_ok" [mode, vis, d, mI, rP, cnP, tyCtor, mo, mn, xo, xn]
      (iotaIndexOk (coreKnot (decMode mode) fe id F) fe d.toNat mI.toNat rP.toNat cnP.toNat
        (decE tyCtor) margs.toList idx.toList) s₀ a₀

section vckErr
variable (r : CoreFnsA) (fe : IFEnv) (depth mI rP : Nat) (lps : List NIdx) (us : LsIdx)
  (args : List EIdx) (usj : LsIdx) (cvj : IConstantVal) (rl : IRecRule) (margs : List EIdx)
  (cmpL : LsIdx)

theorem vckT_fail_lvl (a a1 : AState) (h1 : (lvlsEq? usj cmpL).run a = .ok (none, a1)) :
    (iotaRecVckT r fe depth mI rP lps us args usj cvj rl margs cmpL).run a =
      (ConRon.Arena.fail (.notImplemented "resource limit: fuel exhausted: level comparison") :
        AM Bool).run a1 := by
  rw [iotaRecVckT_eq]
  simp only [StateT.run_bind, h1, except_ok_bind, liftFueled]
  rfl

theorem vckT_err_cmp (a a1 : AState) (h1 : (lvlsEq? usj cmpL).run a = .ok (some true, a1))
    (ce : CheckError) (h2 : (iotaRecCmpT r fe depth rl lps us args rP margs).run a1 = .error ce) :
    (iotaRecVckT r fe depth mI rP lps us args usj cvj rl margs cmpL).run a = .error ce := by
  rw [iotaRecVckT_eq]
  simp only [StateT.run_bind, h1, except_ok_bind, liftFueled_run_some, ↓reduceIte, h2]; rfl

theorem vckT_err_cert (a a1 a2 a3 : AState) (tyC : EIdx)
    (h1 : (lvlsEq? usj cmpL).run a = .ok (some true, a1))
    (h2 : (iotaRecCmpT r fe depth rl lps us args rP margs).run a1 = .ok (true, a2))
    (h3 : (constTyAt cvj usj).run a2 = .ok (tyC, a3)) (ce : CheckError)
    (h4 : (iotaCertsFull r fe depth tyC margs).run a3 = .error ce) :
    (iotaRecVckT r fe depth mI rP lps us args usj cvj rl margs cmpL).run a = .error ce := by
  rw [iotaRecVckT_eq]
  simp only [StateT.run_bind, h1, except_ok_bind, liftFueled_run_some, ↓reduceIte, h2, h3, h4]
  rfl

theorem vckT_err_idx (a a1 a2 a3 a4 : AState) (tyC : EIdx)
    (h1 : (lvlsEq? usj cmpL).run a = .ok (some true, a1))
    (h2 : (iotaRecCmpT r fe depth rl lps us args rP margs).run a1 = .ok (true, a2))
    (h3 : (constTyAt cvj usj).run a2 = .ok (tyC, a3))
    (h4 : (iotaCertsFull r fe depth tyC margs).run a3 = .ok (true, a4)) (ce : CheckError)
    (h5 : (iotaIndexOk r fe depth mI rP rl.ctorParams tyC margs ((args.take mI).drop rP)).run a4 =
      .error ce) :
    (iotaRecVckT r fe depth mI rP lps us args usj cvj rl margs cmpL).run a = .error ce := by
  rw [iotaRecVckT_eq]
  simp only [StateT.run_bind, h1, except_ok_bind, liftFueled_run_some, ↓reduceIte, h2, h3, h4, h5]

end vckErr

section vck
variable (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p) (hw : WhnfCallees p)
  (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p)
  (hnv : closedNV p L.Checker.nvFns = true) (hCmp : IotaRecCmpE p) (hCF : IotaCertsFullE p)
  (hIx : IotaIndexOkE p)

include hp hc hw hEI hER hEK hnv hCmp hCF hIx in
/-- **`iota_rec_vck`'s verdicts**: the level comparison out of fuel declines; the parameters', the
telescope's and the indices' checks are their callees'. -/
theorem iotaRecVck_refinesE :
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
        (decI us) args.toList (decI usj) cvj rule margs.toList (decI cmpL)) s₀ a₀ := by
  intro n hk hkE F hnF hn62 s₀ a₀ dn vis fe MM eb mode d us recP so usj ctorP rl mo mn cmpL sn lps
    rule cvj args margs hS hm4 hebm hus husj hcmpL hlps hrule hcv hsa hsat hmI hsm hsmt hcpm
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (irVckE_spec p hp.vck n ⟨s₀.mem, Locals.init []⟩
    mode vis d us recP so usj ctorP rl mo mn cmpL) hc0 (Err.code_ne_of_cls hk0)
  simp only [irVckE] at hW
  have hspn := hS.spn
  have herec := hS.erec
  obtain ⟨-, -, -, hcpw, -, -, -, -, -⟩ := decRule_rd herec hrule
  obtain ⟨hnn, hname, hlpsj, -, hty, htype⟩ := decCV_rd1 herec hcv
  generalize hE0 : s₀.mem.arr64 EREC = E at *
  have hmsz : (mo + mn).toNat = mo.toNat + mn.toNat := by
    have := hsm.bound; rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  cases c1 : callE p n "lvls_eq_c" [usj, cmpL] s₀.mem with
  | error e1 =>
    rw [c1] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfIotaE_nv "lvls_eq_c" (by simp)) c1
  | ok q =>
  obtain ⟨rq, m1⟩ := q
  rw [c1] at hW
  simp only at hW
  have hn2 : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with h | h
    · have := lvlsEqC_small p hp.lvl.cs n h [usj, cmpL] s₀.mem
      rw [callW_of_callE c1] at this; cases this
    · exact h
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 2 := ⟨n - 2, by omega⟩
  obtain ⟨hrun1, ⟨M1, hS1, hK1, hSt1⟩, hr1⟩ := CoreSpec.run
    (lvlsEqC_refines p hp.lvl N ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb hS usj cmpL husj
      hcmpL) (callW_of_callE c1)
  have e1 : m1.arr64 EREC = E := by rw [hER _ _ _ _ _ _ (by simp) (callW_of_callE c1), hE0]
  by_cases q0 : rq.headD 0 = 0
  · rw [ite_eq_left q0] at hW; cases hW
    have hdo : decO (rq.headD 0) = none := by rw [q0]; rfl
    rw [hdo] at hrun1
    refine ErrClaim.of_run_eqW (vckT_fail_lvl _ _ _ _ _ _ _ _ _ _ _ _ _ a₀ _ hrun1) ?_
    exact ErrClaim.fail _ _ rfl
  rw [ite_eq_right q0] at hW
  by_cases q1 : rq.headD 0 = 1
  · rw [ite_eq_left q1] at hW; cases hW
  rw [ite_eq_right q1] at hW
  have hdo : decO (rq.headD 0) = some true := by unfold decO; rw [ite_eq_right q0, ite_eq_right q1]
  rw [hdo] at hrun1
  have hsa1 : SpineR m1 so sn args := hsa.keep hSt1.size hSt1.below hsat hspn
  have hsm1 : SpineR m1 mo mn margs := hsm.keep hSt1.size hSt1.below (by rw [← hsmt]; omega) hspn
  cases c2 : callE p (N + 2) "iota_rec_cmp" [mode, vis, d, us, recP, so, rl, mo] m1 with
  | error e2 =>
    rw [c2] at hW; cases hW
    have hcmp := hCmp (N + 1) (hk.mono (by omega)) (hkE.mono (by omega)) F (by omega)
      (by omega) ⟨m1, Locals.init []⟩ _ dn vis fe M1 eb mode d us recP so rl mo mn sn lps rule args
      margs hS1 hm4 hebm hus
    simp only [e1] at hcmp
    exact ErrClaim.of_run_err (fun ce h' => vckT_err_cmp _ _ _ _ _ _ _ _ _ _ _ _ _ a₀ _ hrun1 ce h')
      (CoreSpecE.of_callE (hcmp hlps hrule hsa1 (by rw [hSt1.1]; exact hsat) hmI hsm1
        (by rw [hSt1.1, ← hsmt]; omega) hcpm) c2)
  | ok q =>
  obtain ⟨rc, m2⟩ := q
  rw [c2] at hW
  simp only at hW
  have hcmp := iotaRecCmp_refines' p hp hc hw hEI hER (N + 1) (hk.mono (by omega)) F (by omega)
    (by omega) ⟨m1, Locals.init []⟩ _ dn vis fe M1 eb mode d us recP so rl mo mn sn lps rule args
    margs hS1 hm4 hebm hus
  simp only [e1] at hcmp
  obtain ⟨hrun2, ⟨M2, hS2, hK2, hSt2⟩, hr2⟩ := CoreSpec.run (hcmp hlps hrule hsa1
    (by rw [hSt1.1]; exact hsat) hmI hsm1 (by rw [hSt1.1, ← hsmt]; omega) hcpm) (callW_of_callE c2)
  have e2 : m2.arr64 EREC = E := by
    rw [callW_iotaRecCmp_erec p hp hER hEK _ _ _ _ _ rfl (callW_of_callE c2), e1]
  have hSt12 := hSt1.trans hSt2
  by_cases g0 : rc.headD 0 = 0
  · rw [ite_eq_left g0] at hW; cases hW
  rw [ite_eq_right g0] at hW
  have hb : decBool rc = true := by unfold decBool; exact bne_iff_ne.mpr g0
  rw [hb] at hrun2
  rw [e2] at hW
  cases c3 : callE p (N + 2) "const_ty_at" [rdW E (ctorP + 1), rdW E (ctorP + 2), rdW E (ctorP + 3),
      rdW E (ctorP + 4), usj] m2 with
  | error e3 =>
    rw [c3] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfIotaE_nv "const_ty_at" (by simp)) c3
  | ok q =>
  obtain ⟨rt, m3⟩ := q
  rw [c3] at hW
  simp only at hW
  obtain ⟨ok3, ⟨M3, hS3, hK3, hSt3⟩, res3, hr3⟩ := CoreSpec.of_callW
    (constTyAt_refines' p hp.toIotaProg' hw.instLP (N + 2) ⟨m2, Locals.init []⟩ _ dn vis fe M2 eb
      (rdW E (ctorP + 1)) (rdW E (ctorP + 2)) (rdW E (ctorP + 3)) (rdW E (ctorP + 4)) usj
      cvj.levelParams hS2 hnn hty husj (by rw [e2]; exact hlpsj)) (callW_of_callE c3)
  have hcvj : (⟨decI (rdW E (ctorP + 1)), cvj.levelParams, decE (rdW E (ctorP + 4))⟩ : IConstantVal) =
      cvj := by
    cases cvj; simp only at hname htype ⊢; rw [hname, htype]; rfl
  rw [hcvj] at ok3 res3 hS3
  have hrun3 := AM.run_of_ok _ _ ok3
  rw [res3] at hrun3
  have e3 : m3.arr64 EREC = E := by rw [hER _ _ _ _ _ _ (by simp) (callW_of_callE c3), e2]
  have hSt13 := hSt12.trans hSt3
  simp only [irVckTailE] at hW
  have hsm3 : SpineR m3 mo mn margs := hsm.keep hSt13.size hSt13.below (by rw [← hsmt]; omega) hspn
  cases c4 : callE p (N + 2) "iota_certs_full" [mode, vis, d, rt.headD 0, mo, mn] m3 with
  | error e4 =>
    rw [c4] at hW; cases hW
    exact ErrClaim.of_run_err (fun ce h' => vckT_err_cert _ _ _ _ _ _ _ _ _ _ _ _ _ a₀ _ _ _ _ hrun1
        hrun2 hrun3 ce h')
      (CoreSpecE.of_callE (hCF (N + 1) (hk.mono (by omega)) (hkE.mono (by omega)) F (by omega)
        (by omega) ⟨m3, Locals.init []⟩ _ dn vis fe M3 eb mode d (rt.headD 0) mo mn margs hS3 hm4 hebm
        hr3 hsm3 (by rw [hSt13.1]; exact hsmt)) c4)
  | ok q =>
  obtain ⟨rf, m4⟩ := q
  rw [c4] at hW
  simp only at hW
  obtain ⟨hrun4, ⟨M4, hS4, hK4, hSt4⟩, hr4⟩ := CoreSpec.run
    (iotaCertsFull_refines' p hp.toIotaProg4 hw.instList (N + 1) (hk.mono (by omega)) F (by omega)
      (by omega) ⟨m3, Locals.init []⟩ _ dn vis fe M3 eb mode d (rt.headD 0) mo mn margs hS3 hm4 hebm
      hr3 hsm3 (by rw [hSt13.1]; exact hsmt)) (callW_of_callE c4)
  have e4 : m4.arr64 EREC = E := by rw [hER _ _ _ _ _ _ (by simp) (callW_of_callE c4), e3]
  have hSt14 := hSt13.trans hSt4
  by_cases f0 : rf.headD 0 = 0
  · rw [ite_eq_left f0] at hW; cases hW
  rw [ite_eq_right f0] at hW
  rw [decBool_t_m2c f0] at hrun4
  rw [e4] at hW
  have hsa4 : SpineR m4 so sn args := hsa.keep hSt14.size hSt14.below hsat hspn
  have hsm4 : SpineR m4 mo mn margs := hsm.keep hSt14.size hSt14.below (by rw [← hsmt]; omega) hspn
  have hmIs : (rdW E (recP + 5)).toNat ≤ sn.toNat := by omega
  have hoff := ixOff_toNat (rdW E (recP + 5)) (rdW E (recP + 6))
  have hidx := SpineR.slice hsa4 (rdW E (recP + 6) - ixLen (rdW E (recP + 6)) (rdW E (recP + 5)))
    (rdW E (recP + 5)) (by rw [hoff]; omega) hmIs (by rw [hSt14.size]; exact hspn)
  have hl : UInt64.ofNat ((rdW E (recP + 5)).toNat -
      (rdW E (recP + 6) - ixLen (rdW E (recP + 6)) (rdW E (recP + 5))).toNat) =
      ixLen (rdW E (recP + 5)) (rdW E (recP + 6)) := by
    rw [hoff, ixLen_eq]; congr 1; omega
  rw [hl, hoff, take_drop_min_le] at hidx
  have hsat' := hsa.bound
  have hxo : (so + (rdW E (recP + 6) - ixLen (rdW E (recP + 6)) (rdW E (recP + 5)))).toNat +
      (ixLen (rdW E (recP + 5)) (rdW E (recP + 6))).toNat ≤ (spTop m4).toNat := by
    have htq : (spTop ({ mem := s₀.mem, loc := Locals.init [] } : St).mem).toNat =
        (spTop s₀.mem).toNat := rfl
    rw [hSt14.1, UInt64.toNat_add, hoff, Nat.mod_eq_of_lt (by omega), ixLen_eq, UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt (by omega)]
    omega
  have herr := err_of_k (k := fun (x : Except Err (List Word × Mem)) => match x with
      | .error e => (.error e : Except Err (Word × Mem))
      | .ok (ri, m5) => .ok (ri.headD 0, m5))
    (by intro q e; simp) (fun _ => rfl) hW
  have hix := hIx (N + 1) (hk.mono (by omega)) (hkE.mono (by omega)) F (by omega) (by omega)
      ⟨m4, Locals.init []⟩ _ dn vis fe M4 eb mode d (rdW E (recP + 5)) (rdW E (recP + 6))
      (rdW E (rl + 2)) (rt.headD 0) mo mn
      (so + (rdW E (recP + 6) - ixLen (rdW E (recP + 6)) (rdW E (recP + 5))))
      (ixLen (rdW E (recP + 5)) (rdW E (recP + 6))) margs _ hS4 hm4 hebm hr3 hsm4 hidx
      (by rw [hSt14.1, ← hsmt]; omega) hxo
  simp only [← hcpw] at hix
  exact ErrClaim.of_run_err (fun ce h' => vckT_err_idx _ _ _ _ _ _ _ _ _ _ _ _ _ a₀ _ _ _ _ _ hrun1
      hrun2 hrun3 hrun4 ce h') (CoreSpecE.of_callE hix herr)

end vck

/-! ## `iota_rec_fam`, `iota_rec_fire2`, `iota_rec_fire` -/

section famErr
variable (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth mI rP : Nat)
  (lps : List NIdx) (us : LsIdx) (args : List EIdx) (usj : LsIdx) (cvj : IConstantVal)
  (rl : IRecRule) (margs : List EIdx)

theorem famT_err_vck (a a1 a2 : AState) (cmpL : LsIdx) (h : mode.verifiedChecks = true)
    (h1 : (recFireLevels rl lps us cvj.levelParams).run a = .ok (cmpL, a1))
    (h2 : (iotaCase3 fe rl cvj cmpL).run a1 = .ok (true, a2)) (ce : CheckError)
    (h3 : (iotaRecVckT r fe depth mI rP lps us args usj cvj rl margs cmpL).run a2 = .error ce) :
    (iotaRecFamT mode r fe depth mI rP lps us args usj cvj rl margs).run a = .error ce := by
  simp only [iotaRecFamT, h, ↓reduceIte, StateT.run_bind, h1, except_ok_bind, h2, h3]

theorem fire2T_err_fam (c : NIdx) (a : AState) (h : margs.length = rl.ctorParams + rl.nfields)
    (ce : CheckError)
    (h1 : (iotaRecFamT mode r fe depth mI rP lps us args usj cvj rl margs).run a = .error ce) :
    (iotaRecFire2T mode r fe depth c mI rP lps us args usj cvj rl margs).run a = .error ce := by
  simp only [iotaRecFire2T, h, ↓reduceIte, StateT.run_bind, h1]; rfl

end famErr

theorem irFire2E_zero {p : Prog} {m : Mem} {mode vis d us recP so usj ctorP rl mo mn : Word}
    {er : Err} (h : callE p 0 "iota_rec_fam" [mode, vis, d, us, recP, so, usj, ctorP, rl, mo, mn] m =
      .error er) : er.cls = 0 := by
  obtain ⟨e', he', h0⟩ := callE_zero p "iota_rec_fam" [mode, vis, d, us, recP, so, usj, ctorP, rl, mo, mn] m
  rw [h] at he'; cases he'; exact h0

section fire
variable (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p) (hw : WhnfCallees p)
  (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p)
  (hnv : closedNV p L.Checker.nvFns = true) (hCmp : IotaRecCmpE p) (hCF : IotaCertsFullE p)
  (hIx : IotaIndexOkE p)

include hp hc hw hEI hER hEK hnv hCmp hCF hIx in
/-- **`iota_rec_fam`'s verdicts** are `iota_rec_vck`'s. -/
theorem iotaRecFam_refinesE :
    ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
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
    CoreSpecE p (n + 1) "iota_rec_fam" [mode, vis, d, us, recP, so, usj, ctorP, rl, mo, mn]
      (iotaRecFamT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat
        (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat (rdW (s₀.mem.arr64 EREC) (recP + 6)).toNat lps
        (decI us) args.toList (decI usj) cvj rule margs.toList) s₀ a₀ := by
  intro n hk hkE F hnF hn62 s₀ a₀ dn vis fe MM eb mode d us recP so usj ctorP rl mo mn sn lps rule cvj
    np nf args margs hS hm4 hebm hus husj hlps hrule hci hfe hsa hsat hmI hsm hsmt hcpm
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (irFamE_spec p hp.fam (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d us recP so usj ctorP rl mo mn) hc0 (Err.code_ne_of_cls hk0)
  simp only [irFamE] at hW
  have hspn := hS.spn
  have herec := hS.erec
  have hfc := fireCore_of hS hrule hci hfe
  have hld := lpsDen_of hS hfe
  obtain ⟨-, -, -, -, -, -, -, -, hkw⟩ := decRule_rd herec hrule
  have hcv := decCI_ctorInfo_cv hci
  have hmsz : (mo + mn).toNat = mo.toNat + mn.toNat := by
    have := hsm.bound; rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  generalize hE0 : s₀.mem.arr64 EREC = E at *
  by_cases hv : mode &&& 1 ≠ 0
  · rw [ite_eq_left hv] at hW; cases hW
  rw [ite_eq_right hv] at hW
  have hvc : (decMode mode).verifiedChecks = true := by
    rw [decMode_verified mode hm4]; simpa using hv
  cases c1 : callE p n "rec_fire_levels" [rdW E (rl + 3), rdW E (rl + 4), rdW E (rl + 5),
      rdW E (recP + 2), rdW E (recP + 3), us, rdW E (ctorP + 2), rdW E (ctorP + 3)] s₀.mem with
  | error e1 =>
    rw [c1, irFamE.k_rec_fire_levels.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfIotaE_nv "rec_fire_levels" (by simp)) c1
  | ok q =>
  obtain ⟨rv, m1⟩ := q
  rw [c1] at hW
  simp only [irFamE.k_rec_fire_levels] at hW
  obtain ⟨hrun1, ⟨M1, hS1, hK1, hSt1⟩, hr1⟩ := CoreSpec.run
    (hc.recFireLevels n ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb _ _ _ _ _ us _ _ rule lps
      cvj.levelParams hS hus (by show hslice? (s₀.mem.arr64 EREC) _ _ = _; rw [hE0]; exact hlps)
      hld hfc) (callW_of_callE c1)
  have e1 : m1.arr64 EREC = E := by rw [hER _ _ _ _ _ _ (by simp) (callW_of_callE c1), hE0]
  rw [e1] at hW
  cases c2 : callE p n "iota_case3" [rdW E (rl + 9), vis, ctorP, rv.headD 0] m1 with
  | error e2 =>
    rw [c2, irFamE.k_iota_case3.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfIotaE_nv "iota_case3" (by simp)) c2
  | ok q =>
  obtain ⟨r3, m2⟩ := q
  rw [c2] at hW
  simp only [irFamE.k_iota_case3] at hW
  obtain ⟨hrun2, ⟨M2, hS2, hK2, hSt2⟩, hr2⟩ := CoreSpec.run
    (iotaCase3_refines p hp.toIotaProg4 hc.capsNeverZero n ⟨m1, Locals.init []⟩ _ dn vis fe M1
      eb (rdW E (rl + 9)) ctorP (rv.headD 0) rule cvj np nf hS1 hr1 hkw (by rw [e1]; exact hci))
    (callW_of_callE c2)
  have e2 : m2.arr64 EREC = E := by rw [hER _ _ _ _ _ _ (by simp) (callW_of_callE c2), e1]
  have hSt12 := hSt1.trans hSt2
  by_cases g0 : r3.headD 0 = 0
  · rw [ite_eq_left g0] at hW; cases hW
  rw [ite_eq_right g0] at hW
  rw [decBool_t_m2c g0] at hrun2
  have hW' := err_of_k (by intro q e; simp [irFamE.k_iota_rec_vck]) (fun _ => rfl) hW
  cases n with
  | zero => exact ErrClaim.of_callE_zeroW hW'
  | succ N =>
  have hvk := iotaRecVck_refinesE p hp hc hw hEI hER hEK hnv hCmp hCF hIx N (hk.mono (by omega))
    (hkE.mono (by omega)) F (by omega) (by omega) ⟨m2, Locals.init []⟩ _ dn vis fe M2 eb mode d us
    recP so usj ctorP rl mo mn (rv.headD 0) sn lps rule cvj args margs hS2 hm4 hebm hus husj hr1
  simp only [e2] at hvk
  exact ErrClaim.of_run_err (fun ce h' => famT_err_vck _ _ _ _ _ _ _ _ _ _ _ _ _ a₀ _ _ _ hvc hrun1
      hrun2 ce h')
    (CoreSpecE.of_callE (hvk hlps hrule hcv (hsa.keep hSt12.size hSt12.below hsat hspn)
      (by rw [hSt12.1]; exact hsat) hmI
      (hsm.keep hSt12.size hSt12.below (by rw [← hsmt, hmsz]; exact Nat.le_refl _) hspn)
      (by rw [hSt12.1]; exact hsmt) hcpm) hW')

include hp hc hw hEI hER hEK hnv hCmp hCF hIx in
/-- **`iota_rec_fire2`'s verdicts** are `iota_rec_fam`'s. -/
theorem iotaRecFire2_refinesE :
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
        (decI us) args.toList (decI usj) cvj rule margs.toList) s₀ a₀ := by
  intro n hk hkE F hnF hn62 s₀ a₀ dn vis fe MM eb mode d c us recP so usj ctorP rl mo mn sn lps rule cvj
    np nf args margs hS hm4 hebm hcw hus husj hlps hrule hci hfe hsa hsat hmI hsm hsmt
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (irFire2E_spec p hp.fire2 n ⟨s₀.mem, Locals.init []⟩
    mode vis d c us recP so usj ctorP rl mo mn) hc0 (Err.code_ne_of_cls hk0)
  simp only [irFire2E] at hW
  have hspn := hS.spn
  have herec := hS.erec
  obtain ⟨hctw, hctor, hnfw, hcpw, -, -, hrhsw, hrhs, -⟩ := decRule_rd herec hrule
  generalize hE0 : s₀.mem.arr64 EREC = E at *
  have hmsz : (mo + mn).toNat = mo.toNat + mn.toNat := by
    have := hsm.bound; rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hmsize : margs.toList.length = mn.toNat := by simp [hsm.size]
  by_cases l1 : mn < rdW E (rl + 2)
  · rw [ite_eq_left l1] at hW; cases hW
  rw [ite_eq_right l1] at hW
  by_cases l2 : mn - rdW E (rl + 2) ≠ rdW E (rl + 1)
  · rw [ite_eq_left l2] at hW; cases hW
  rw [ite_eq_right l2] at hW
  have hlen : margs.toList.length = rule.ctorParams + rule.nfields := by
    rw [hmsize, hcpw, hnfw]
    have h1' : (rdW E (rl + 2)).toNat ≤ mn.toNat := by
      have := UInt64.not_lt.mp l1; exact UInt64.le_iff_toNat_le.mp this
    have := congrArg UInt64.toNat (Classical.not_not.mp l2)
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr h1')] at this; omega
  have hcpm : rule.ctorParams ≤ mn.toNat := by omega
  cases c1 : callE p n "iota_rec_fam" [mode, vis, d, us, recP, so, usj, ctorP, rl, mo, mn] s₀.mem with
  | error e1 =>
    rw [c1] at hW; cases hW
    cases n with
    | zero => exact absurd (irFire2E_zero c1) hk0
    | succ N =>
    have hfm := iotaRecFam_refinesE p hp hc hw hEI hER hEK hnv hCmp hCF hIx N (hk.mono (by omega))
      (hkE.mono (by omega)) F (by omega) (by omega) ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb mode d
      us recP so usj ctorP rl mo mn sn lps rule cvj np nf args margs hS hm4 hebm hus husj
    simp only [hE0] at hfm
    exact ErrClaim.of_run_err (fun ce h' => fire2T_err_fam _ _ _ _ _ _ _ _ _ _ _ _ _ _ a₀ hlen ce h')
      (CoreSpecE.of_callE (hfm hlps hrule hci hfe hsa hsat hmI hsm hsmt hcpm) c1)
  | ok q =>
  obtain ⟨rf, m1⟩ := q
  rw [c1] at hW
  simp only at hW
  split at hW
  · cases hW
  cases c2 : callE p n "rule_rhs_at" [c, rdW (m1.arr64 EREC) rl, rdW (m1.arr64 EREC) (recP + 2),
      rdW (m1.arr64 EREC) (recP + 3), rdW (m1.arr64 EREC) (rl + 8), us] m1 with
  | error e2 =>
    rw [c2] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfIotaE_nv "rule_rhs_at" (by simp)) c2
  | ok q =>
  obtain ⟨rr, m2⟩ := q
  rw [c2] at hW
  simp only at hW
  cases c3 : callE p n "mk_app_n" [rr.headD 0, so, rpLen (rdW E (recP + 5)) (rdW E (recP + 6))]
      m2 with
  | error e3 =>
    rw [c3] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfIotaE_nv "mk_app_n" (by simp)) c3
  | ok q =>
  obtain ⟨rx, m3⟩ := q
  rw [c3] at hW
  simp only at hW
  cases c4 : callE p n "mk_app_n_from" [rx.headD 0, mo, mn, rdW E (rl + 2)] m3 with
  | error e4 =>
    rw [c4] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfIotaE_nv "mk_app_n_from" (by simp)) c4
  | ok q => rw [c4] at hW; cases hW

include hp hc hw hEI hER hEK hnv hCmp hCF hIx in
/-- **`IotaRecFireE`**: `iota_rec_fire`'s verdicts are `iota_rec_fire2`'s. -/
theorem iotaRecFireE_of : IotaRecFireE p := by
  intro n hk hkE F hnF hn62 s₀ a₀ dn vis fe MM eb mode d c us recP so usj ctorP rl major sn lps rule cvj
    np nf args hS hm4 hebm hcw hus husj hmaj hlps hrule hci hfe hsa hsat hmI
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (irFireE_spec p hp.fire (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d c us recP so usj ctorP rl major) hc0 (Err.code_ne_of_cls hk0)
  simp only [irFireE] at hW
  have hspn := hS.spn
  cases c1 : callE p n "get_app_args" [major] s₀.mem with
  | error e1 =>
    rw [c1, irFireE.k_get_app_args.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfIotaE_nv "get_app_args" (by simp)) c1
  | ok q =>
  obtain ⟨ra, m1⟩ := q
  rw [c1] at hW
  simp only [irFireE.k_get_app_args] at hW
  have hW' := err_of_k (by intro q e; simp [irFireE.k_iota_rec_fire2]) (fun _ => rfl) hW
  obtain ⟨t1, ht1, -, fr1, gr1, hr0, htop1, xs, hrunA, hxs⟩ := triple_of_callE
    (getAppArgs_refines' p hp.spine.args hp.spine.cnt hp.spine.fill n ⟨s₀.mem, Locals.init []⟩ a₀
      hS.arena.1 major hmaj hspn) c1
  rw [ht1] at fr1 gr1 htop1 hxs
  have hS1 : CoreS dn m1 a₀ vis fe MM eb := hS.frame_stk fr1 (by simp) (by simp)
  have e1 : m1.arr64 EREC = s₀.mem.arr64 EREC := fr1.1 EREC (by simp [SPN, EREC]) (by decide)
  cases n with
  | zero => exact ErrClaim.of_callE_zeroW hW'
  | succ N =>
  have hf2 := iotaRecFire2_refinesE p hp hc hw hEI hER hEK hnv hCmp hCF hIx N (hk.mono (by omega))
    (hkE.mono (by omega)) F (by omega) (by omega) ⟨m1, Locals.init []⟩ a₀ dn vis fe MM eb mode d c us
    recP so usj ctorP rl (ra.headD 0) (ra.tail.headD 0) sn lps rule cvj np nf args xs.toArray hS1 hm4
    hebm hcw hus husj
  simp only [e1] at hf2
  have hEq : ∀ ce, (iotaRecFire2T (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI c)
      (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat (rdW (s₀.mem.arr64 EREC) (recP + 6)).toNat lps
      (decI us) args.toList (decI usj) cvj rule xs.toArray.toList).run a₀ = .error ce →
      (iotaRecFireT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI c)
      (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat (rdW (s₀.mem.arr64 EREC) (recP + 6)).toNat lps
      (decI us) args.toList (decE major) (decI usj) cvj rule).run a₀ = .error ce := by
    intro ce h'
    simp only [iotaRecFireT, StateT.run_bind, hrunA, except_ok_bind]
    simpa using h'
  exact ErrClaim.of_run_err hEq (CoreSpecE.of_callE (hf2 hlps hrule hci hfe
    (hsa.keep gr1.size gr1.below hsat hspn)
    (by
      show so.toNat + sn.toNat ≤ (spTop m1).toNat
      have := UInt64.le_iff_toNat_le.mp gr1.1
      have htq : (spTop ({ mem := s₀.mem, loc := Locals.init [] } : St).mem).toNat =
        (spTop s₀.mem).toNat := rfl
      omega)
    hmI hxs (by rw [htop1, hr0])) hW')

end fire

end L.Arena
