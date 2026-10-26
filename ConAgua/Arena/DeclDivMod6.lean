import ConAgua.Arena.DeclDivMod5
import ConAgua.Arena.DeclCanonEq
import ConAgua.Arena.DeclRomStubs
import ConAgua.L.ModelGen

/-!
# The `Nat.div` family's pin gate, bottom up: the guards (lane `decls3`, `decls3-divmod`)

Part 6: `bool_ctor_typed`, `type_pin_stored`, `ground_guards`, `type_pin_guard`, `type_pins_guard`,
`div_mod_pin_guard`, `div_mod_certs_guard_go`, `div_mod_certs_guard`.
-/

noncomputable section

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open L.Rom (PinSetR)

namespace L.Ind

open L.Arena

structure DmProg6 (p : Prog) : Prop extends DmProg5 p where
  lBoolCtorTyped : p.lookup "bool_ctor_typed" = some boolCtorTypedL
  lDivModPinGuard : p.lookup "div_mod_pin_guard" = some divModPinGuardL
  lTypePinStored : p.lookup "type_pin_stored" = some typePinStoredL
  lGroundGuards : p.lookup "ground_guards" = some groundGuardsL
  lTypePinGuard : p.lookup "type_pin_guard" = some typePinGuardL
  lTypePinsGuard : p.lookup "type_pins_guard" = some typePinsGuardL
  lCertsGuardGo : p.lookup "div_mod_certs_guard_go" = some divModCertsGuardGoL
  lCertsGuard : p.lookup "div_mod_certs_guard" = some divModCertsGuardL

section guards
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

/-! ## `bool_ctor_typed` -/

/-- **`bool_ctor_typed` is its model `dmBctW`** (generated). -/
l_model bct_specW (p : Prog) (hp : p.lookup "bool_ctor_typed" = some boolCtorTypedL)
  fns [hp ↦ dmBctW list]
  specs [callW_spec p n "env_find", callW_spec p n "ci_to_cv", callW_spec p n "pin_at", callW_spec p n "const_e"]
  grind [arena_grind] finish [ntBW, rdW_eq] gen 30 heartbeats 1600000 bind ntBW instances 10000

theorem DmProg2.cvProg (hD : DmProg2 p) : NatCvProg p :=
  hD.toNatEqProg.toNatTyProg.toNatGuardProg.toNatLitProg.toNatCvProg

theorem bct_ref (hD : DmProg6 p) (nm : Word) :
    CallRef p "bool_ctor_typed" [vis, nm] (fun m a => StageR dn vis fe m a ∧ H nm)
      (boolCtorTyped fe (decI nm)) (KeepPost dn vis fe decW0B) := by
  refine CallRef.of_succ fun k m a r m' ⟨hS, hn⟩ hcall => ?_
  have hw := callW_model (M := fun mq => dmBctW p (k + 1) mq vis nm)
    (bct_specW p hD.lBoolCtorTyped (k + 1) · vis nm) hcall
  rw [dmBctW.arm1] at hw
  replace hw := ntBW_some hw; obtain ⟨rf, m1, h1, hw⟩ := hw
  obtain ⟨hm1, hfd⟩ := envFind_call hD.toDmProg5.toMasterProg nm hn hS.1.env h1
  subst hm1
  cases hf : fe.find? (decI nm) with
  | none =>
    rw [hf] at hfd
    have hz : rf.headD 0 = 0 := hfd
    rw [if_pos hz] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact ⟨false, a, by simp only [boolCtorTyped, hf]; rfl, hS, IWGrow.refl _, by simp [decW0B]⟩
  | some ci =>
    rw [hf] at hfd
    obtain ⟨hr1, hci⟩ := hfd
    rw [if_neg (by rw [hr1]; decide)] at hw
    obtain ⟨r2, m2, x2, a2, hrun2, ⟨hS2, hg2, hcv2⟩, hw⟩ :=
      (ciToCv_ref hD.toDmProg5.cvProg (rf.tail.headD 0) ci).bind_ ⟨hS, hci⟩ hw
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hrun2)
    obtain ⟨r3, m3, x3, a3, hrun3, ⟨hS3, hg3, hl3, rfl⟩, hw⟩ :=
      (pinSlot_ref p hD.toDmProg5.lPinAt 29 pinBool rfl).bind_ hS2 hw
    obtain ⟨r4, m4, x4, a4, hrun4, ⟨hS4, hg4, hl4, rfl⟩, hw⟩ :=
      (constE_ref hD.toDmProg5.toMasterProg (r3.headD 0)).bind_ ⟨hS3, hl3⟩ hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    obtain ⟨wt, -, hrd, hwt, hty, hst⟩ := cvWordsAt hS2.2.2.2.2.1 hcv2
    have hrd4 := (hst m4 (hg3.trans hg4)).2
    refine ⟨decide (wt = r4.headD 0), a4, ?_, hS4, hg2.trans (hg3.trans hg4), ?_⟩
    · have hb := decI_beq_word (κ := IdxKind.expr) hwt hl4
      simp only [boolCtorTyped, hf, StateT.run_bind, boolName, hrun3]
      have hrun4' : (constE (decI (r3.headD 0))).run a3 = .ok (decI (r4.headD 0), a4) := hrun4
      simp only [hrun4', exc_ok_bind', hty]
      simp only [bne_iff_ne, hb]
      try rfl
    · rw [hrd4]
      unfold decW0B
      simp only [List.headD_cons]
      generalize r4.headD 0 = z
      by_cases e : wt = z <;> simp [e]

@[refines ConRon.Arena.boolCtorTyped]
theorem boolCtorTyped_refines (hD : DmProg6 p) (nm : Word) :
    RefAM p "bool_ctor_typed" [vis, nm] (fun m a => StageR dn vis fe m a ∧ H nm)
      (boolCtorTyped fe (decI nm)) (KeepPost dn vis fe decW0B) :=
  (bct_ref hD nm).refAM

/-! ## `div_mod_pin_guard` -/

/-- **`type_pin_stored` is its model `dmTpsW`** (generated). -/
l_model tps_specW (p : Prog) (hp : p.lookup "type_pin_stored" = some typePinStoredL)
  fns [hp ↦ dmTpsW list]
  specs [callW_spec p n "env_find", callW_spec p n "pin_word", callW_spec p n "intern_sort",
    callW_spec p n "ci_to_cv"]
  grind [arena_grind] finish [ntBW, rdW_eq] gen 30 heartbeats 1600000 bind ntBW instances 10000

theorem internSort_ref (hM : MasterProg p) (u : Word) (hu : H u) :
    CallRef p "intern_sort" [u] (StageR dn vis fe) (internE (.sort (decI u)))
      (KeepPost dn vis fe decW0E) := by
  refine CallRef.of_triple fun n s₀ a₀ hS => ?_
  refine triple_post (internSort_spec p hM.lSortFind hM.lSortPush hM.lInternSort n s₀ u) ?_
  rintro r s' ⟨hl, hI⟩
  obtain ⟨a', hrun, hS', hg⟩ := internSort_stage hS u hu hI
  exact ⟨hl, decE (r.headD 0), a', hrun, hS', hg, consInternM_lt sortCS_wf hS.1.arena.1.sort hI, rfl⟩

theorem tps_ref (hD : DmProg6 p) (nm : Word) :
    CallRef p "type_pin_stored" [vis, nm] (fun m a => StageR dn vis fe m a ∧ H nm)
      (typePinStored fe (decI nm)) (KeepPost dn vis fe decW0E) := by
  refine CallRef.of_succ fun k m a r m' ⟨hS, hn⟩ hcall => ?_
  have hw := callW_model (M := fun mq => dmTpsW p (k + 1) mq vis nm)
    (tps_specW p hD.lTypePinStored (k + 1) · vis nm) hcall
  rw [dmTpsW.arm1] at hw
  replace hw := ntBW_some hw; obtain ⟨rf, m1, h1, hw⟩ := hw
  obtain ⟨hm1, hfd⟩ := envFind_call hD.toDmProg5.toMasterProg nm hn hS.1.env h1
  subst hm1
  cases hf : fe.find? (decI nm) with
  | none =>
    rw [hf] at hfd
    have hz : rf.headD 0 = 0 := hfd
    rw [if_pos hz] at hw
    obtain ⟨r2, m2, x2, a2, hrun2, ⟨hS2, hg2, hl2, rfl⟩, hw⟩ :=
      (pinWord53_ref (dn := dn) (vis := vis) (fe := fe) p hD.toDmProg5.toMasterProg.lPinWord).bind_ hS hw
    obtain ⟨r3, m3, x3, a3, hrun3, ⟨hS3, hg3, hl3, rfl⟩, hw⟩ :=
      (internSort_ref hD.toDmProg5.toMasterProg (r2.headD 0) hl2).bind_ hS2 hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    refine ⟨_, a3, ?_, hS3, hg2.trans hg3, hl3, rfl⟩
    simp only [typePinStored, hf, zeroLevel, StateT.run_bind, hrun2, exc_ok_bind']
    exact hrun3
  | some ci =>
    rw [hf] at hfd
    obtain ⟨hr1, hci⟩ := hfd
    rw [if_neg (by rw [hr1]; decide)] at hw
    obtain ⟨r2, m2, x2, a2, hrun2, ⟨hS2, hg2, hcv2⟩, hw⟩ :=
      (ciToCv_ref hD.toDmProg5.cvProg (rf.tail.headD 0) ci).bind_ ⟨hS, hci⟩ hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    obtain ⟨wt, -, hrd, hwt, hty, -⟩ := cvWordsAt hS2.2.2.2.2.1 hcv2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hrun2)
    refine ⟨ci.toConstantVal.type, a, ?_, hS2, hg2, ?_⟩
    · simp only [typePinStored, hf]; rfl
    · simp only [List.headD_cons, hrd, decW0E]
      exact ⟨hwt, hty.symm⟩

@[refines ConRon.Arena.typePinStored]
theorem typePinStored_refines (hD : DmProg6 p) (nm : Word) :
    RefAM p "type_pin_stored" [vis, nm] (fun m a => StageR dn vis fe m a ∧ H nm)
      (typePinStored fe (decI nm)) (KeepPost dn vis fe decW0E) :=
  (tps_ref hD nm).refAM

def dmGgW (p : Prog) (cl : CallM) (n : Nat) (m : Mem) (vs pe : Word) : Option (List Word × Mem) :=
  ntBW (lbbF m [4000000000, 0, pe]) fun r2 m2 =>
  if r2.headD 0 = 0 then some ([0], m2) else
  ntBW (hffF m2 [4000000000, pe]) fun r3 m3 =>
  if r3.headD 0 ≠ 0 then some ([0], m3) else
  ntBW (cl n "all_level_params_defined" [0, 0, pe] m3) fun r4 m4 =>
  if r4.headD 0 = 0 then some ([0], m4) else
  ntBW (cl n "consts_resolve_ffast" [vs, pe] m4) fun r5 m5 => some ([r5.headD 0], m5)

set_option maxHeartbeats 1600000 in
theorem gg_specW (p : Prog) (hb : BvbProg p) (hf : HfF p) (hp : p.lookup "ground_guards" = some groundGuardsL)
    (cl : CallM) (hcl : CallSpec p cl) (n : Nat) (s₀ : St) (vs pe : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "ground_guards" [vs, pe]
    ⦃fun r s' => LocEq s' s₀ ∧ dmGgW p cl n s₀.mem vs pe = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, groundGuardsL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, lbbF_spec p hb n,
      hffF_spec p hf n, hcl n "all_level_params_defined", hcl n "consts_resolve_ffast"] <;>
    finish (gen := 30) (instances := 10000) [dmGgW, ntBW]

def dmTpgW (p : Prog) (cl : CallM) (n : Nat) (m : Mem) (vs nm ty : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "env_find" [nm, vs] m) fun r1 m1 =>
  if r1.headD 0 = 0 then some ([0], m1) else
  ntBW (callW p n "type_pin_stored" [vs, nm] m1) fun r2 m2 =>
  ntBW (hffF m2 [4000000000, r2.headD 0]) fun r3 m3 =>
  if r3.headD 0 ≠ 0 then some ([0], m3) else
  ntBW (lbbF m3 [4000000000, 0, ty]) fun r4 m4 =>
  if r4.headD 0 = 0 then some ([0], m4) else
  ntBW (hffF m4 [4000000000, ty]) fun r5 m5 =>
  if r5.headD 0 ≠ 0 then some ([0], m5) else
  ntBW (cl n "consts_resolve_ffast" [vs, ty] m5) fun r6 m6 => some ([r6.headD 0], m6)

set_option maxHeartbeats 1600000 in
theorem tpg_specW (p : Prog) (hb : BvbProg p) (hf : HfF p) (hp : p.lookup "type_pin_guard" = some typePinGuardL)
    (cl : CallM) (hcl : CallSpec p cl) (n : Nat) (s₀ : St) (vs nm ty : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "type_pin_guard" [vs, nm, ty]
    ⦃fun r s' => LocEq s' s₀ ∧ dmTpgW p cl n s₀.mem vs nm ty = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, typePinGuardL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, callW_spec p n "env_find",
      callW_spec p n "type_pin_stored", lbbF_spec p hb n, hffF_spec p hf n,
      hcl n "consts_resolve_ffast"] <;>
    finish (gen := 30) (instances := 10000) [dmTpgW, ntBW]

/-- **`type_pins_guard` is its model `tpsgW`** (generated). -/
l_model tpsg_specW (p : Prog) (hp : p.lookup "type_pins_guard" = some typePinsGuardL)
  fns [hp ↦ tpsgW list]
  specs [callW_spec p n "type_pin_guard", callW_spec p n "type_pins_guard"]
  grind [arena_grind] finish [ntBW, rdW_eq] gen 30 heartbeats 1600000 bind ntBW instances 10000

/-- **`div_mod_pin_guard` is its model `dmPgW`** (generated). -/
l_model pg_specW (p : Prog) (hp : p.lookup "div_mod_pin_guard" = some divModPinGuardL)
  fns [hp ↦ dmPgW list]
  specs [callW_spec p n "div_mod_decl_pin", callW_spec p n "ground_guards",
    callW_spec p n "div_mod_type_pins", callW_spec p n "type_pins_guard"]
  grind [arena_grind] heartbeats 1600000 bind ntBW simp [ntBW]

/-! ## `div_mod_certs_guard_go` -/

theorem rdW_iw_of {m : Mem} {x : Word} {i : Nat} {w : Word} (h : (iwA m)[i]? = some w)
    (hx : x.toNat = i) : rdW (m.arr64 IW) x = w := by
  simp only [iwA] at h; simp [rdW, hx, h]

theorem word_add_two {w : Word} (h : w.toNat + 2 < 2 ^ 64) : (w + 2).toNat = w.toNat + 2 := by
  rw [UInt64.toNat_add]; simp; omega

theorem StmtL.cons {m : Mem} {so sl : Word} {s : List EIdx × EIdx} {ss : List (List EIdx × EIdx)}
    (hI : IWOK m) (h : StmtL m so.toNat sl.toNat (s :: ss)) :
    sl ≠ 0 ∧ ∃ q : Word, rdW (m.arr64 IW) so = q ∧ StmtAt m q s ∧
      StmtL m (so + 1).toNat (sl - 1).toNat ss := by
  obtain ⟨hb, hl, hj⟩ := h
  have hl0 : sl ≠ 0 := fun e => by rw [e] at hl; simp at hl
  have hlen : sl.toNat = ss.length + 1 := by simpa using hl
  have ho : (so + 1).toNat = so.toNat + 1 := by
    have h1 := hI.1; have h2 := hI.2.2.1
    rw [UInt64.toNat_add]; simp; omega
  have hl1 : (sl - 1).toNat = ss.length := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
  obtain ⟨q, hq, hs⟩ := hj 0 (by simp)
  refine ⟨hl0, q, rdW_iw_of (by simpa using hq) rfl, by simpa using hs, ?_⟩
  rw [ho, hl1]
  refine ⟨by omega, rfl, fun j hj' => ?_⟩
  obtain ⟨q2, hq2, hs2⟩ := hj (j + 1) (by simpa using hj')
  exact ⟨q2, by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hq2, by simpa using hs2⟩

/-- **`div_mod_certs_guard_go` is its model `cggoW`** (generated). -/
l_model cggo_specW (p : Prog) (hp : p.lookup "div_mod_certs_guard_go" = some divModCertsGuardGoL)
  fns [hp ↦ cggoW list]
  specs [callW_spec p n "div_mod_cert_guard", callW_spec p n "div_mod_certs_guard_go"]
  grind [arena_grind] finish [ntBW, rdW_eq] gen 30 heartbeats 1600000 bind ntBW instances 10000

/-! ## `div_mod_certs_guard` -/

/-- **`div_mod_certs_guard` is its model `cgsW`** (generated). -/
l_model cgs_specW (p : Prog) (hp : p.lookup "div_mod_certs_guard" = some divModCertsGuardL)
  fns [hp ↦ cgsW list]
  specs [callW_spec p n "div_mod_cert_stmts", callW_spec p n "div_mod_cert_proofs", callW_spec p n "div_mod_certs_guard_go"]
  grind [arena_grind] heartbeats 1600000 bind ntBW simp [ntBW]

end guards

end L.Ind
