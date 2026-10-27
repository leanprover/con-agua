import ConAgua.Verdict.DeclArmsE
import ConAgua.Arena.DeclAxQuotT
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# The verdict claim of the axiom arm `check_decl_axiom` (lane `verdicts-b`, helper `d`)
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF DeclAt CVAt dw)
open ConRon.Bridge (FoldOK PinsDenote)

local notation "V" => ConLeche.CheckMode.verified

l_model checkDeclAxiom_specE (p : Prog) (hf : p.lookup "check_decl_axiom" = some checkDeclAxiom)
  fns [hf ↦ checkDeclAxiomE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

section ax
variable (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)

/-- **`check_decl_axiom`'s error claim under `StageT`.** -/
theorem checkDeclAxiom_errT {p : Prog} (hX : AxProg p) (hq : KnotStageProg p) (hap : ApdF p)
    (hkp : CrKeep p) (hnv : closedNV p L.Checker.nvFns = true) (hcE : CoreStubsE p)
    (hUL : UceLookups p) (hdn : DnInj dn) (hQd : QuotDn dn) (cv : IConstantVal) :
    ArmSpecE pins dn ds p "check_decl_axiom" (.axiomDecl cv) := by
  unfold ArmSpecE
  intro n hn m a vis fe pend i hi hd hok hR hS hF hden _ hCr e hc
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (checkDeclAxiom_specE p hX.cda n ⟨m, Locals.init []⟩ i vis) hc
    (Err.code_ne_of_cls hk0)
  have hd' : ds[i.toNat] = .axiomDecl cv := by
    rw [Array.getElem?_eq_getElem hi] at hd; exact Option.some.inj hd
  obtain ⟨x, hx⟩ := hden
  simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hx
  obtain ⟨c, hcvd, -⟩ := hx
  have hdecl := hR.decls.recs i.toNat hi
  rw [hd'] at hdecl
  obtain ⟨-, hcvAt⟩ := hdecl
  cases n with
  | zero => rw [checkDeclAxiomE.eq_1] at hW; cases hW; exact absurd rfl hk0
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [checkDeclAxiomE.arm1] at hW
  unfold checkDecl
  simp only []
  -- `erec_ci`
  cases h1 : callE p n "erec_ci" [i, 0] m with
  | error e1 =>
    rw [h1, checkDeclAxiomE.k_erec_ci.none] at hW; cases hW
    exact nvl hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, checkDeclAxiomE.k_erec_ci.arm1] at hW
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callE (erecCi_specW p hX.val.rcp n ⟨m, Locals.init []⟩ i 0) h1
  subst hs1
  have hf1 := erecCiW_frame hW1
  have hCr1 := CrOK.frame hCr hf1 (by decide) (by decide)
  obtain ⟨hS1, hg1, hci1, hcv1, htop1⟩ := erecCiW_okA hW1 hS.stage hR.decls hi hcvAt
  have hT1 : StageT dn vis fe s1.mem a :=
    ⟨hS1, hS.twin.frame hf1 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
      ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
      ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩,
      by simp only [pinW, hf1.1 PINS (by decide) (by decide)]; exact hS.flag⟩
  generalize hq0 : r1.headD 0 = q at hW hci1 hcv1 htop1
  have hqb : q.toNat + 8 < 2 ^ 64 := by
    have := hS1.2.2.1; have := hS1.2.2.2.2.1; omega
  have hq1 : (q + 1).toNat = q.toNat + 1 := toNat_add_small q 1 (by omega)
  obtain ⟨wn, hwn, hwnl, hname0⟩ := decCI_name hci1
  have hname : cv.name = decI wn := hname0
  rw [rdW_of_get? hq1.symm (erecP_get hwn)] at hW
  have hpa := hX.quot.pa
  -- `Quot.sound`
  cases h2 : callE p n "pin_at" [4] s1.mem with
  | error e2 =>
    rw [h2, checkDeclAxiomE.k_pin_at.none] at hW; cases hW
    exact nvl hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2] at hW
  obtain ⟨s2, hs2, -, hW2⟩ := triple_of_callE (pinAt_specW p hpa n ⟨s1.mem, Locals.init []⟩ 4) h2
  obtain ⟨hm2, hr2, hl2, hrun2⟩ := pinAtW_ok hW2 hS1.1.pins
  have hm2' : m2 = s1.mem := hs2.symm.trans hm2
  subst hm2'
  have ep2 : r2.headD 0 = pinW s1.mem (1 + (4 : Word).toNat) := by rw [hr2]; rfl
  have hb2 := decI_beq (k := .name) wn _ hwnl hl2
  have hpq : pinQuotSound.run a = .ok (decI (pinW s1.mem (1 + (4 : Word).toNat)), a) := by
    simpa [pinQuotSound, show PIN_QUOT_SOUND = (4 : Word).toNat from rfl] using hrun2
  refine ErrClaim.bind_right hpq ?_
  rw [hname, hb2]
  by_cases eq2 : wn = r2.headD 0
  · rw [checkDeclAxiomE.k_pin_at.arm1 p _ _ _ _ _ _ eq2] at hW
    rw [ep2] at eq2
    simp only [eq2, decide_true, ite_true]
    have hN : L.Rom.NamesDn dn a L.Rom.quotNames := hQd.namesDn hS.twin.mem
    cases h3 : callE p n "rom_basis_decls" [4] s1.mem with
    | error e3 =>
      rw [h3, checkDeclAxiomE.k_rom_basis_decls.none] at hW; cases hW
      exact nvl hnv (by decide +kernel) h3
    | ok q3 =>
    obtain ⟨r3, m3⟩ := q3
    rw [h3] at hW
    obtain ⟨blk, a3, hrun3, hS3, hg3, hD3, -⟩ :=
      hX.quot.rom.quot dn vis fe n s1.mem a r3 m3 ⟨hS1, hok, hN⟩ (callW_of_callE h3)
    have hrun3' : (BasisKind.decls .quotK).run a = .ok (blk, a3) := hrun3
    have hok3 := (ConRon.Bridge.BasisKind.decls_run hok hrun3').1
    have hlen : blk.length = (r3.tail.headD 0).toNat := decPL_length (truncM m3) hD3
    refine ErrClaim.bind_right hrun3' ?_
    by_cases hl : r3.tail.headD 0 ≤ 4
    · rw [checkDeclAxiomE.k_rom_basis_decls.abort1 p _ _ _ _ _ hl] at hW; cases hW
      have hn4 : blk[4]? = none := by
        apply List.getElem?_eq_none; rw [hlen]
        have := UInt64.le_iff_toNat_le.mp hl; simpa using this
      rw [hn4]
      exact ErrClaim.fail _ _ rfl
    rw [checkDeclAxiomE.k_rom_basis_decls.arm1 p _ _ _ _ _ hl] at hW
    generalize r3.headD 0 = o3 at hW hD3
    generalize r3.tail.headD 0 = l3 at hD3 hlen hl
    have hlt : 4 < l3.toNat := by
      have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hl); simpa using this
    obtain ⟨v, ci, hv, hci, hget⟩ := decPL_get _ _ _ hD3 4 hlt
    have hvm : iwN m3 (o3.toNat + 4) = some v := (IWGrow.refl m3).truncExt.1.nat? hv
    obtain ⟨w, hw, rfl⟩ : ∃ w, (iwA m3)[o3.toNat + 4]? = some w ∧ w.toNat = v := by
      simp only [iwN, nat?, Option.map_eq_some_iff] at hvm; exact hvm
    have hob : o3.toNat + 4 < 2 ^ 64 := by
      have := (Array.getElem?_eq_some_iff.mp hw).1; have := hS3.2.2.2.1; simp only [iwA] at *; omega
    have ew : rdW (m3.arr64 IW) (o3 + 4) = w := by
      have : (o3 + 4).toNat = o3.toNat + 4 := by
        rw [UInt64.toNat_add]; simp; omega
      simp only [rdW, this]; simp only [iwA] at hw; simp [hw]
    rw [ew] at hW
    rw [hget]
    cases h4 : callE p n "ci_canon_eq" [q, w] m3 with
    | error e4 =>
      rw [h4, checkDeclAxiomE.k_ci_canon_eq.none] at hW; cases hW
      exact ErrClaim.bind_left (nvl hnv (by decide +kernel) h4)
    | ok q4 =>
    obtain ⟨r4, m4⟩ := q4
    rw [h4] at hW
    obtain ⟨s4, hs4, -, hok4, ⟨⟨hS4, hg4, hb4, -⟩, -⟩, -⟩ := triple_of_callE
      (ciCanonEq_refines p hX.quot.canon dn vis fe q w (.axiomInfo cv) ci n ⟨m3, Locals.init []⟩ a3
        ⟨hS3, ArrExt.decCI (IWGrow.erecPExt hg3) hci1, ArrExt.decCI (truncM_erecP m3) hci,
          poolSmall_of_stage hS3, fun x y l hx hy => hok3.view_inj hx hy⟩) h4
    have hrun4 := AM.run_of_ok _ _ hok4
    by_cases z4 : r4.headD 0 = 0
    · rw [checkDeclAxiomE.k_ci_canon_eq.abort1 p _ _ _ z4] at hW; cases hW
      have hb : AM.res ((IConstantInfo.axiomInfo cv).canonEq ci) a3 = false := by
        rw [← hb4, z4]; rfl
      rw [hb] at hrun4
      refine ErrClaim.bind_right hrun4 ?_
      exact ErrClaim.ite_neg (by decide) (ErrClaim.fail _ _ rfl)
    rw [checkDeclAxiomE.k_ci_canon_eq.arm1 p _ _ _ z4] at hW; cases hW
  · rw [checkDeclAxiomE.k_pin_at.arm2 p _ _ _ _ _ _ eq2] at hW
    rw [ep2] at eq2
    simp only [eq2, decide_false, Bool.false_eq_true, ite_false]
    have hcv1' : decCV (erecP s1.mem) (q + 1).toNat = some cv := by rw [hq1]; exact hcv1
    -- the constant check
    cases h3 : callE p n "check_constant_val" [vis, q + 1] s1.mem with
    | error e3 =>
      rw [h3, checkDeclAxiomE.k_check_constant_val.none] at hW; cases hW
      exact ErrClaim.bind_left (ccvE_okT hq hX.val hap hkp hnv hcE hUL hn' h3 hT1 hcv1' (by omega)
        (denoteCV_lps hcvd) hCr1)
    | ok q3 =>
    obtain ⟨r3, m3⟩ := q3
    rw [h3, checkDeclAxiomE.k_check_constant_val.arm1] at hW
    obtain ⟨s3, hs3, -, hok3, hS3, hg3, hCr3⟩ := triple_of_callE
      (checkConstantVal_refinesT p hX.val hq hap hkp n hn' ⟨s1.mem, Locals.init []⟩ a dn fe vis (q + 1)
        cv hT1 hcv1' (by omega) (denoteCV_lps hcvd) hCr1) h3
    subst hs3
    have hrun3 := AM.run_of_ok _ _ hok3
    obtain ⟨env, hFo⟩ := hF
    obtain ⟨hstep1, -, hpure1⟩ :=
      ConRon.Bridge.checkConstantVal_bridge_of_fold rfl (ConRon.Bridge.CoreSpec.of_core rfl) hFo hcvd hrun3
    have hok1 := hFo.ofCore hstep1
    have hcA := ConRon.Bridge.denoteCV_ext hcvd hstep1.ext
    have hnmA : denoteN a.store.ns (decI wn) = some c.name := by
      rw [← hname]; exact (ConRon.Bridge.denoteCV_inv hcvd).1
    have hext1 := hstep1.ext
    refine ErrClaim.bind_right hrun3 ?_
    generalize AM.st (checkConstantVal V fe cv) a = a3 at hrun3 hS3 hok1 hcA hext1
    have hP3 : ArrExt (erecP s1.mem) (erecP s3.mem) := IWGrow.erecPExt hg3
    -- the standard axioms
    cases h4 : callE p n "std_axiom_ok" [vis, q + 1] s3.mem with
    | error e4 =>
      rw [h4, checkDeclAxiomE.k_std_axiom_ok.none] at hW; cases hW
      exact ErrClaim.bind_left (nvl hnv (by decide +kernel) h4)
    | ok q4 =>
    obtain ⟨r4, m4⟩ := q4
    rw [h4] at hW
    obtain ⟨s4, hs4, -, hok4, hS4, hg4, hb4, -⟩ := triple_of_callE
      (stdAxiomOk_refines p hX.std dn hdn vis fe (q + 1) cv n ⟨s3.mem, Locals.init []⟩ a3
        ⟨hS3.stage, ArrExt.decCV hP3 hcv1'⟩) h4
    subst hs4
    have hrun4 := AM.run_of_ok _ _ hok4
    refine ErrClaim.bind_right hrun4 ?_
    generalize AM.res (stdAxiomOk fe cv) a3 = b4 at hrun4 hb4
    generalize AM.st (stdAxiomOk fe cv) a3 = a4 at hrun4 hS4
    by_cases z4 : r4.headD 0 ≠ 0
    · rw [checkDeclAxiomE.k_std_axiom_ok.arm1 p _ _ _ _ _ _ z4] at hW
      have hb : b4 = true := by rw [← hb4]; simpa using z4
      rw [hb]
      refine ErrClaim.ite_pos rfl ?_
      cases h5 : callE p n "env_push" [vis, q] s4.mem with
      | error e5 =>
        rw [h5, checkDeclAxiomE.k_env_push.none] at hW; cases hW
        exact ErrClaim.of_cls0 (callE_nv hnv (declNv_mem _ (by decide +kernel)) _ _ _ h5)
      | ok q5 =>
        obtain ⟨r5, m5⟩ := q5
        rw [h5, checkDeclAxiomE.k_env_push.arm1] at hW; cases hW
    have z4' : r4.headD 0 = 0 := by simpa using z4
    rw [checkDeclAxiomE.k_std_axiom_ok.arm2 p _ _ _ _ _ _ z4'] at hW
    have hb : b4 = false := by rw [← hb4, z4']; rfl
    rw [hb]
    refine ErrClaim.ite_neg (by decide) ?_
    have hP4 : ArrExt (erecP s1.mem) (erecP s4.mem) := IWGrow.erecPExt (hg3.trans hg4)
    have hCr4 := hCr3
    -- a pin read, generic over the memory `s4.mem`
    -- `Lean.trustCompiler`
    cases h5 : callE p n "pin_at" [42] s4.mem with
    | error e5 =>
      rw [h5, checkDeclAxiomE.k_pin_at_2.none] at hW; cases hW
      exact nvl hnv (by decide +kernel) h5
    | ok q5 =>
    obtain ⟨r5, m5⟩ := q5
    rw [h5] at hW
    obtain ⟨s5, hs5, -, hW5⟩ := triple_of_callE (pinAt_specW p hpa n ⟨s4.mem, Locals.init []⟩ 42) h5
    obtain ⟨hm5, hr5, hl5, hrun5⟩ := pinAtW_ok hW5 hS4.1.pins
    have hm5' : m5 = s4.mem := hs5.symm.trans hm5
    subst hm5'
    have ep5 : r5.headD 0 = pinW s4.mem (1 + (42 : Word).toNat) := by rw [hr5]; rfl
    have hb5 := decI_beq (k := .name) wn _ hwnl hl5
    have htn : trustCompilerName.run a4 = .ok (decI (pinW s4.mem (1 + (42 : Word).toNat)), a4) := by
      simpa [trustCompilerName, pinTrustCompiler, show PIN_TRUST_COMPILER = (42 : Word).toNat from rfl]
        using hrun5
    refine ErrClaim.bind_right htn ?_
    rw [hb5]
    by_cases eq5 : wn = r5.headD 0
    · rw [checkDeclAxiomE.k_pin_at_2.arm1 p _ _ _ _ _ _ eq5] at hW
      rw [ep5] at eq5
      simp only [eq5, decide_true, ite_true]
      cases h6 : callE p n "trust_compiler_ok" [vis, q + 1] s4.mem with
      | error e6 =>
        rw [h6, checkDeclAxiomE.k_trust_compiler_ok.none] at hW; cases hW
        exact ErrClaim.bind_left (nvl hnv (by decide +kernel) h6)
      | ok q6 =>
      obtain ⟨r6, m6⟩ := q6
      rw [h6] at hW
      obtain ⟨s6, hs6, -, hok6, hS6, hg6, hb6, -⟩ := triple_of_callE
        (trustCompilerOk_refines p hX.tco dn vis fe (q + 1) cv n ⟨s4.mem, Locals.init []⟩ a4
          ⟨hS4, ArrExt.decCV hP4 hcv1'⟩) h6
      have hrun6 := AM.run_of_ok _ _ hok6
      refine ErrClaim.bind_right hrun6 ?_
      by_cases z6 : r6.headD 0 = 0
      · rw [checkDeclAxiomE.k_trust_compiler_ok.abort1 p _ _ _ _ _ z6] at hW; cases hW
        have ht6 : AM.res (trustCompilerOk fe cv) a4 = false := by rw [← hb6, z6]; rfl
        rw [ht6]
        exact ErrClaim.ite_neg (by decide) (ErrClaim.fail _ _ rfl)
      rw [checkDeclAxiomE.k_trust_compiler_ok.arm1 p _ _ _ _ _ (by simpa using z6)] at hW
      have ht6 : AM.res (trustCompilerOk fe cv) a4 = true := by rw [← hb6]; simpa using z6
      rw [ht6]
      refine ErrClaim.ite_pos rfl ?_
      cases h7 : callE p n "env_push" [vis, q] m6 with
      | error e7 =>
        rw [h7, checkDeclAxiomE.k_env_push.none] at hW; cases hW
        exact ErrClaim.of_cls0 (callE_nv hnv (declNv_mem _ (by decide +kernel)) _ _ _ h7)
      | ok q7 =>
        obtain ⟨r7, m7⟩ := q7
        rw [h7, checkDeclAxiomE.k_env_push.arm1] at hW; cases hW
    rw [checkDeclAxiomE.k_pin_at_2.arm2 p _ _ _ _ _ _ eq5] at hW
    rw [ep5] at eq5
    simp only [eq5, decide_false, Bool.false_eq_true, ite_false]
    -- the `ofReduce*` pair
    cases h7 : callE p n "pin_at" [45] s4.mem with
    | error e7 =>
      rw [h7, checkDeclAxiomE.k_pin_at_3.none] at hW; cases hW
      exact nvl hnv (by decide +kernel) h7
    | ok q7 =>
    obtain ⟨r7, m7⟩ := q7
    rw [h7, checkDeclAxiomE.k_pin_at_3.arm1] at hW
    obtain ⟨s7, hs7, -, hW7⟩ := triple_of_callE (pinAt_specW p hpa n ⟨s4.mem, Locals.init []⟩ 45) h7
    obtain ⟨hm7, hr7, hl7, hrun7⟩ := pinAtW_ok hW7 hS4.1.pins
    have hm7' : m7 = s4.mem := hs7.symm.trans hm7
    subst hm7'
    have ep7 : r7.headD 0 = pinW s4.mem (1 + (45 : Word).toNat) := by rw [hr7]; rfl
    cases h8 : callE p n "pin_at" [46] s4.mem with
    | error e8 =>
      rw [h8, checkDeclAxiomE.k_pin_at_4.none] at hW; cases hW
      exact nvl hnv (by decide +kernel) h8
    | ok q8 =>
    obtain ⟨r8, m8⟩ := q8
    rw [h8] at hW
    obtain ⟨s8, hs8, -, hW8⟩ := triple_of_callE (pinAt_specW p hpa n ⟨s4.mem, Locals.init []⟩ 46) h8
    obtain ⟨hm8, hr8, hl8, hrun8⟩ := pinAtW_ok hW8 hS4.1.pins
    have hm8' : m8 = s4.mem := hs8.symm.trans hm8
    subst hm8'
    have ep8 : r8.headD 0 = pinW s4.mem (1 + (46 : Word).toNat) := by rw [hr8]; rfl
    have hb7 := decI_beq (k := .name) wn _ hwnl hl7
    have hb8 := decI_beq (k := .name) wn _ hwnl hl8
    have hon : ofReduceNatName.run a4 = .ok (decI (pinW s4.mem (1 + (45 : Word).toNat)), a4) := by
      simpa [ofReduceNatName, pinOfReduceNat, show PIN_OF_REDUCE_NAT = (45 : Word).toNat from rfl]
        using hrun7
    have hob : ofReduceBoolName.run a4 = .ok (decI (pinW s4.mem (1 + (46 : Word).toNat)), a4) := by
      simpa [ofReduceBoolName, pinOfReduceBool, show PIN_OF_REDUCE_BOOL = (46 : Word).toNat from rfl]
        using hrun8
    refine ErrClaim.bind_right hon (ErrClaim.bind_right hob ?_)
    by_cases eq8 : wn = r7.headD 0 ∨ wn = r8.headD 0
    · rw [checkDeclAxiomE.k_pin_at_4.arm1 p _ _ _ _ _ _ _ eq8] at hW
      rw [ep7, ep8] at eq8
      have hor : ((decI wn : NIdx) == decI (pinW s4.mem (1 + (45 : Word).toNat)) ||
          (decI wn : NIdx) == decI (pinW s4.mem (1 + (46 : Word).toNat))) = true := by
        rw [hb7, hb8]; rcases eq8 with e | e <;> simp [e]
      rw [hor]
      refine ErrClaim.ite_pos rfl ?_
      cases h9 : callE p n "of_reduce_ax_ok" [vis, q + 1] s4.mem with
      | error e9 =>
        rw [h9, checkDeclAxiomE.k_of_reduce_ax_ok.none] at hW; cases hW
        exact ErrClaim.bind_left (nvl hnv (by decide +kernel) h9)
      | ok q9 =>
      obtain ⟨r9, m9⟩ := q9
      rw [h9] at hW
      obtain ⟨s9, hs9, -, hok9, hS9, hg9, hb9, -⟩ := triple_of_callE
        (ofReduceAxOk_refines p hX.ora dn hdn vis fe (q + 1) cv n ⟨s4.mem, Locals.init []⟩ a4
          ⟨hS4, ArrExt.decCV hP4 hcv1'⟩) h9
      have hrun9 := AM.run_of_ok _ _ hok9
      refine ErrClaim.bind_right hrun9 ?_
      by_cases z9 : r9.headD 0 = 0
      · rw [checkDeclAxiomE.k_of_reduce_ax_ok.abort1 p _ _ _ _ _ z9] at hW; cases hW
        have ht9 : AM.res (ofReduceAxOk fe cv) a4 = false := by rw [← hb9, z9]; rfl
        rw [ht9]
        exact ErrClaim.ite_neg (by decide) (ErrClaim.fail _ _ rfl)
      rw [checkDeclAxiomE.k_of_reduce_ax_ok.arm1 p _ _ _ _ _ (by simpa using z9)] at hW
      have ht9 : AM.res (ofReduceAxOk fe cv) a4 = true := by rw [← hb9]; simpa using z9
      rw [ht9]
      refine ErrClaim.ite_pos rfl ?_
      cases h10 : callE p n "env_push" [vis, q] m9 with
      | error e10 =>
        rw [h10, checkDeclAxiomE.k_env_push.none] at hW; cases hW
        exact ErrClaim.of_cls0 (callE_nv hnv (declNv_mem _ (by decide +kernel)) _ _ _ h10)
      | ok q10 =>
        obtain ⟨r10, m10⟩ := q10
        rw [h10, checkDeclAxiomE.k_env_push.arm1] at hW; cases hW
    rw [checkDeclAxiomE.k_pin_at_4.arm2 p _ _ _ _ _ _ _ eq8] at hW
    rw [ep7, ep8] at eq8
    have hor : ((decI wn : NIdx) == decI (pinW s4.mem (1 + (45 : Word).toNat)) ||
        (decI wn : NIdx) == decI (pinW s4.mem (1 + (46 : Word).toNat))) = false := by
      rw [hb7, hb8]; simp only [not_or] at eq8
      simp only [decide_eq_false eq8.1, decide_eq_false eq8.2, Bool.or_false]
    rw [hor]
    refine ErrClaim.ite_neg (by decide) ?_
    -- `propext` / `choice` of another shape
    cases h9 : callE p n "pin_at" [32] s4.mem with
    | error e9 =>
      rw [h9, checkDeclAxiomE.k_pin_at_5.none] at hW; cases hW
      exact nvl hnv (by decide +kernel) h9
    | ok q9 =>
    obtain ⟨r9, m9⟩ := q9
    rw [h9, checkDeclAxiomE.k_pin_at_5.arm1] at hW
    obtain ⟨s9, hs9, -, hW9⟩ := triple_of_callE (pinAt_specW p hpa n ⟨s4.mem, Locals.init []⟩ 32) h9
    obtain ⟨hm9, hr9, hl9, hrun9⟩ := pinAtW_ok hW9 hS4.1.pins
    have hm9' : m9 = s4.mem := hs9.symm.trans hm9
    subst hm9'
    have ep9 : r9.headD 0 = pinW s4.mem (1 + (32 : Word).toNat) := by rw [hr9]; rfl
    cases h10 : callE p n "pin_at" [33] s4.mem with
    | error e10 =>
      rw [h10, checkDeclAxiomE.k_pin_at_6.none] at hW; cases hW
      exact nvl hnv (by decide +kernel) h10
    | ok q10 =>
    obtain ⟨r10, m10⟩ := q10
    rw [h10] at hW
    obtain ⟨s10, hs10, -, hW10⟩ := triple_of_callE (pinAt_specW p hpa n ⟨s4.mem, Locals.init []⟩ 33) h10
    obtain ⟨hm10, hr10, hl10, hrun10⟩ := pinAtW_ok hW10 hS4.1.pins
    have hm10' : m10 = s4.mem := hs10.symm.trans hm10
    subst hm10'
    have ep10 : r10.headD 0 = pinW s4.mem (1 + (33 : Word).toNat) := by rw [hr10]; rfl
    have hb9 := decI_beq (k := .name) wn _ hwnl hl9
    have hb10 := decI_beq (k := .name) wn _ hwnl hl10
    have hpn : propextName.run a4 = .ok (decI (pinW s4.mem (1 + (32 : Word).toNat)), a4) := by
      simpa [propextName, pinPropext, show PIN_PROPEXT = (32 : Word).toNat from rfl] using hrun9
    have hch : choiceName.run a4 = .ok (decI (pinW s4.mem (1 + (33 : Word).toNat)), a4) := by
      simpa [choiceName, pinChoice, show PIN_CHOICE = (33 : Word).toNat from rfl] using hrun10
    refine ErrClaim.bind_right hpn (ErrClaim.bind_right hch ?_)
    by_cases eq10 : wn = r9.headD 0 ∨ wn = r10.headD 0
    · rw [checkDeclAxiomE.k_pin_at_6.abort1 p _ _ _ _ _ _ eq10] at hW; cases hW
      rw [ep9, ep10] at eq10
      have hor2 : ((decI wn : NIdx) == decI (pinW s4.mem (1 + (32 : Word).toNat)) ||
          (decI wn : NIdx) == decI (pinW s4.mem (1 + (33 : Word).toNat))) = true := by
        rw [hb9, hb10]; rcases eq10 with e | e <;> simp [e]
      rw [hor2]
      exact ErrClaim.ite_pos rfl (ErrClaim.fail _ _ rfl)
    rw [checkDeclAxiomE.k_pin_at_6.eq_2 p _ _ _ _ _ _, ite_eq_right eq10] at hW
    rw [ep9, ep10] at eq10
    have hor2 : ((decI wn : NIdx) == decI (pinW s4.mem (1 + (32 : Word).toNat)) ||
        (decI wn : NIdx) == decI (pinW s4.mem (1 + (33 : Word).toNat))) = false := by
      rw [hb9, hb10]; simp only [not_or] at eq10
      simp only [decide_eq_false eq10.1, decide_eq_false eq10.2, Bool.or_false]
    rw [hor2]
    refine ErrClaim.ite_neg (by decide) ?_
    -- `sorryAx` is skipped
    cases h11 : callE p n "pin_at" [13] s4.mem with
    | error e11 =>
      rw [h11, checkDeclAxiomE.k_pin_at_7.none] at hW; cases hW
      exact nvl hnv (by decide +kernel) h11
    | ok q11 =>
    obtain ⟨r11, m11⟩ := q11
    rw [h11] at hW
    obtain ⟨s11, hs11, -, hW11⟩ := triple_of_callE (pinAt_specW p hpa n ⟨s4.mem, Locals.init []⟩ 13) h11
    obtain ⟨hm11, hr11, hl11, hrun11⟩ := pinAtW_ok hW11 hS4.1.pins
    have hm11' : m11 = s4.mem := hs11.symm.trans hm11
    subst hm11'
    have ep11 : r11.headD 0 = pinW s4.mem (1 + (13 : Word).toNat) := by rw [hr11]; rfl
    have hb11 := decI_beq (k := .name) wn _ hwnl hl11
    have hsa : pinSorryAx.run a4 = .ok (decI (pinW s4.mem (1 + (13 : Word).toNat)), a4) := by
      simpa [pinSorryAx, show PIN_SORRY_AX = (13 : Word).toNat from rfl] using hrun11
    refine ErrClaim.bind_right hsa ?_
    by_cases eq11 : wn = r11.headD 0
    · rw [checkDeclAxiomE.k_pin_at_7.arm1 p _ _ _ _ eq11] at hW; cases hW
    rw [checkDeclAxiomE.k_pin_at_7.abort1 p _ _ _ _ eq11] at hW; cases hW
    rw [ep11] at eq11
    rw [hb11, decide_eq_false eq11]
    refine ErrClaim.ite_neg (by decide) ?_
    -- the readback of the name
    obtain ⟨hst4, hext4, hcache4, -, -⟩ := ConRon.Bridge.stdAxiomOk_run hok1 hcA hrun4
    have hrn4 : ReadNCOK a4 := fun h x e =>
      ConRon.Bridge.denoteN_ext (hok1.check.caches.readN h x (by rw [← hcache4]; exact e)) hext4
    have hnm4 : denoteN a4.store.ns (decI wn) = some c.name :=
      ConRon.Bridge.denoteN_ext (ConRon.Bridge.denoteN_ext hnmA hext1) hext4
    obtain ⟨X, hrunN, -⟩ := readNameM_run' a4 (decI wn) c.name hnm4 hrn4
    exact ErrClaim.bind_right hrunN (ErrClaim.fail _ _ rfl)

end ax

end L.Arena
