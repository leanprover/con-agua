import ConAgua.Arena.WhnfIotaRecRefine

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
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace L.Arena

/-- A constructor record's `ConstantVal`. -/
theorem decCI_ctorInfo_cv {b : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Nat}
    {cvj : IConstantVal} {np nf : Nat} (h : decCI b dn q = some (.ctorInfo cvj np nf)) :
    decCV b (q + 1) = some cvj := by
  cases hq : b[q]? with
  | none => simp [decCI, nat?, hq] at h
  | some w =>
  simp only [decCI, nat?, hq, Option.map_some, Option.bind_eq_bind, Option.bind_some] at h
  rcases hk : w.toNat with _ | _ | _ | _ | _ | _ | _ | k
  all_goals (rw [hk] at h; simp [Option.bind_eq_some_iff] at h)
  obtain ⟨cv, hcv, _, _, _, _, rfl, rfl, rfl⟩ := h
  exact hcv

/-! ## `iota_rec_fam(mode, vis, d, us, recP, so, usj, ctorP, rl, mo, mn)` -/

/-- Model of `iota_rec_fam`. -/
def irFamW (p : Prog) (n : Nat) (m : Mem) (mode vis d us recP so usj ctorP rl mo mn : Word) :
    Option (Word × Mem) :=
  if mode &&& 1 ≠ 0 then some (1, m) else
  match callW p n "rec_fire_levels" [rdW (m.arr64 EREC) (rl + 3), rdW (m.arr64 EREC) (rl + 4),
      rdW (m.arr64 EREC) (rl + 5), rdW (m.arr64 EREC) (recP + 2), rdW (m.arr64 EREC) (recP + 3), us,
      rdW (m.arr64 EREC) (ctorP + 2), rdW (m.arr64 EREC) (ctorP + 3)] m with
  | none => none
  | some (rv, m1) =>
  match callW p n "iota_case3" [rdW (m1.arr64 EREC) (rl + 9), vis, ctorP, rv.headD 0] m1 with
  | none => none
  | some (r3, m2) =>
  if r3.headD 0 = 0 then some (1, m2) else
  match callW p n "iota_rec_vck" [mode, vis, d, us, recP, so, usj, ctorP, rl, mo, mn, rv.headD 0]
      m2 with
  | none => none
  | some (rk, m3) => some (rk.headD 0, m3)

theorem iotaRecFam_spec (p : Prog) (hp : p.lookup "iota_rec_fam" = some iotaRecFamL) (n : Nat)
    (s₀ : St) (mode vis d us recP so usj ctorP rl mo mn : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "iota_rec_fam" [mode, vis, d, us, recP, so, usj, ctorP, rl, mo, mn]
    ⦃fun r s' => LocEq s' s₀ ∧
      irFamW p n s₀.mem mode vis d us recP so usj ctorP rl mo mn = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, iotaRecFamL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
    callW_spec p n "rec_fire_levels", callW_spec p n "iota_case3", callW_spec p n "iota_rec_vck"] <;>
  simp_all [-UInt64.toNat_add, irFamW, EREC, CTL, BinOp.eval, getElem_rdW', Cmp.eval, LocEq,
    St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero,
    Locals.init_cons_succ, Sig.retVal, Sig.retOr]

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

end famRun

/-- **`iota_rec_fam` refines the certificate family.** -/
theorem iotaRecFam_refines' (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p)
    (hden : LvlsEqDen p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d us recP so usj ctorP rl mo mn sn : Word) (lps : List NIdx)
    (rule : IRecRule) (cvj : IConstantVal) (np nf : Nat) (args margs : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW us → HW usj →
    hslice? (s₀.mem.arr64 EREC) (rdW (s₀.mem.arr64 EREC) (recP + 2)).toNat
      (rdW (s₀.mem.arr64 EREC) (recP + 3)).toNat = some lps →
    decRule (s₀.mem.arr64 EREC) rl.toNat = some rule →
    decCI (s₀.mem.arr64 EREC) dn ctorP.toNat = some (.ctorInfo cvj np nf) →
    SpineR s₀.mem so sn args → so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat + 1 = sn.toNat →
    (rdW (s₀.mem.arr64 EREC) (recP + 6)).toNat ≤ sn.toNat →
    (rule.fire = .plain → rule.ctorParams ≤ (rdW (s₀.mem.arr64 EREC) (recP + 6)).toNat) →
    SpineR s₀.mem mo mn margs → mo + mn = spTop s₀.mem → rule.ctorParams ≤ mn.toNat →
    CoreSpec p (n + 1) "iota_rec_fam" [mode, vis, d, us, recP, so, usj, ctorP, rl, mo, mn]
      (iotaRecFamT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat
        (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat (rdW (s₀.mem.arr64 EREC) (recP + 6)).toNat lps
        (decI us) args.toList (decI usj) cvj rule margs.toList) decBool s₀ a₀ dn vis fe MM eb := by
  intro n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d us recP so usj ctorP rl mo mn sn lps rule cvj
    np nf args margs hS hm4 hebm hus husj hlps hrule hci hsa hsat hmI hrP hplain hsm hsmt hcpm
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (iotaRecFam_spec p hp.fam n s₀ mode vis d us recP so usj ctorP rl mo mn)
  subst hs0
  refine ⟨hloc, ?_⟩
  simp only [irFamW] at hW
  have hspn := hS.spn
  have herec := hS.erec
  obtain ⟨-, -, -, -, -, -, -, -, hkw⟩ := decRule_rd herec hrule
  have hcv := decCI_ctorInfo_cv hci
  generalize hE0 : s.mem.arr64 EREC = E at *
  have hmsz : (mo + mn).toNat = mo.toNat + mn.toNat := by
    have := hsm.bound; rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  by_cases hv : mode &&& 1 ≠ 0
  · rw [if_pos hv] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    have hvc : (decMode mode).verifiedChecks = false := by
      rw [decMode_verified mode hm4]; simpa using hv
    obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _ (famT_run_trusted (decMode mode)
      (coreKnot (decMode mode) fe id F) fe d.toNat _ _ lps (decI us) args.toList (decI usj) cvj rule
      margs.toList a₀ hvc)
    refine ⟨hokF, ⟨MM, by rw [hstF, ← hm]; exact hS, KeptAll.refl _ _, by rw [← hm]; exact StackKept.refl _⟩, ?_, ?_⟩
    · rw [hresF]; unfold decBool; rw [← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  rw [if_neg hv] at hW
  have hvc : (decMode mode).verifiedChecks = true := by
    rw [decMode_verified mode hm4]; simpa using hv
  cases n with
  | zero => rw [callW_zero] at hW; cases hW
  | succ N =>
  -- the comparand levels
  cases c1 : callW p (N + 1) "rec_fire_levels" [rdW E (rl + 3), rdW E (rl + 4), rdW E (rl + 5),
      rdW E (recP + 2), rdW E (recP + 3), us, rdW E (ctorP + 2), rdW E (ctorP + 3)] s.mem with
  | none => rw [c1] at hW; cases hW
  | some q =>
  obtain ⟨rv, m1⟩ := q
  rw [c1] at hW
  simp only at hW
  obtain ⟨ok1, ⟨M1, hS1, hK1, hSt1⟩, res1, hr1⟩ := CoreSpec.of_callW
    (hc.recFireLevels (N + 1) ⟨s.mem, Locals.init []⟩ a₀ dn vis fe MM eb _ _ _ _ _ us _ _ rule lps
      cvj.levelParams hS) c1
  have hrun1 := AM.run_of_ok _ _ ok1
  rw [res1] at hrun1
  have e1 : m1.arr64 EREC = E := by rw [hER _ _ _ _ _ _ (by simp) c1, hE0]
  rw [e1] at hW
  -- case 3
  cases c2 : callW p (N + 1) "iota_case3" [rdW E (rl + 9), vis, ctorP, rv.headD 0] m1 with
  | none => rw [c2] at hW; cases hW
  | some q =>
  obtain ⟨r3, m2⟩ := q
  rw [c2] at hW
  simp only at hW
  obtain ⟨ok2, ⟨M2, hS2, hK2, hSt2⟩, res2, hr2⟩ := CoreSpec.of_callW
    (iotaCase3_refines p hp.toIotaProg4 hc.capsNeverZero (N + 1) ⟨m1, Locals.init []⟩ _ dn vis fe M1
      eb (rdW E (rl + 9)) ctorP (rv.headD 0) rule cvj np nf hS1 hr1 hkw (by rw [e1]; exact hci)) c2
  have hrun2 := AM.run_of_ok _ _ ok2
  rw [res2] at hrun2
  have e2 : m2.arr64 EREC = E := by rw [hER _ _ _ _ _ _ (by simp) c2, e1]
  have hSt12 := hSt1.trans hSt2
  by_cases g0 : r3.headD 0 = 0
  · rw [if_pos g0] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    have hb : decBool r3 = false := by unfold decBool; rw [g0]; rfl
    rw [hb] at hrun2
    obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _ (famT_run_nc3 (decMode mode)
      (coreKnot (decMode mode) fe id F) fe d.toNat _ _ lps (decI us) args.toList (decI usj) cvj rule
      margs.toList a₀ _ _ _ hvc hrun1 hrun2)
    refine ⟨hokF, ⟨M2, by rw [hstF, ← hm]; exact hS2, hK1.trans hK2, by rw [← hm]; exact hSt12⟩, ?_, ?_⟩
    · rw [hresF]; unfold decBool; rw [← hr]; rfl
    · unfold ResH HW; rw [← hr]; decide
  rw [if_neg g0] at hW
  have hb : decBool r3 = true := by unfold decBool; exact bne_iff_ne.mpr g0
  rw [hb] at hrun2
  -- the checks
  cases c3 : callW p (N + 1) "iota_rec_vck" [mode, vis, d, us, recP, so, usj, ctorP, rl, mo, mn,
      rv.headD 0] m2 with
  | none => rw [c3] at hW; cases hW
  | some q =>
  obtain ⟨rk, m3⟩ := q
  rw [c3] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  have hvk := iotaRecVck_refines' p hp hc hw hEI hER hEK hden N (hk.mono (by omega)) F
    (by omega) (by omega) ⟨m2, Locals.init []⟩ _ dn vis fe M2 eb mode d us recP so usj ctorP rl mo mn
    (rv.headD 0) sn lps rule cvj args margs hS2 hm4 hebm hus husj hr1
  simp only [e2] at hvk
  obtain ⟨ok3, ⟨M3, hS3, hK3, hSt3⟩, res3, hr3⟩ := CoreSpec.of_callW (hvk hlps hrule hcv
    (hsa.keep hSt12.2.1 hSt12.2.2 hsat hspn) (by rw [hSt12.1]; exact hsat) hmI hrP hplain
    (hsm.keep hSt12.2.1 hSt12.2.2 (by rw [← hsmt]; omega) hspn) (by rw [hSt12.1]; exact hsmt)
    hcpm) c3
  have hrun3 := AM.run_of_ok _ _ ok3
  rw [res3] at hrun3
  obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _ (famT_run_vck (decMode mode)
    (coreKnot (decMode mode) fe id F) fe d.toNat _ _ lps (decI us) args.toList (decI usj) cvj rule
    margs.toList a₀ _ _ _ _ _ hvc hrun1 hrun2 hrun3)
  refine ⟨hokF, ⟨M3, by rw [hstF, ← hm]; exact hS3, hK1.trans (hK2.trans hK3),
    by rw [← hm]; exact hSt12.trans hSt3⟩, ?_, ?_⟩
  · rw [hresF]; simp only [decBool, ← hr]
  · unfold ResH; rw [← hr]; exact hr3

end L.Arena
