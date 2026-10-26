import ConAgua.Verdict.DeclBasisE
import ConAgua.Arena.DeclAxQuotT

/-!
# The verdict claim of the quotient arm `check_decl_quot` (lane `verdicts-b`, helper `d`)
-/

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF DeclAt CVAt dw quotW)
open ConRon.Bridge (FoldOK PinsDenote)

local notation "V" => ConLeche.CheckMode.verified

l_model checkDeclQuot_specE (p : Prog) (hf : p.lookup "check_decl_quot" = some checkDeclQuot)
  fns [hf ↦ checkDeclQuotE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

theorem checkDecl_quot_shape (pins : List INatOpPinSet) (fe : IFEnv) (k : ConLeche.QuotKind)
    (cv : IConstantVal) :
    checkDecl V pins fe (.quotDecl k cv) =
      (quotPinHit k cv >>= fun b => if b = true then
        (match k with | .type => checkBasisDecl fe .quotK | _ => pure fe)
        else fail (.notImplemented (match k with
          | .sound => "quotient soundness axiom mismatch"
          | _ => "quotient declaration mismatch"))) := rfl

section quot
variable (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)

/-- **`check_decl_quot`'s error claim under `StageT`.** -/
theorem checkDeclQuot_errT {p : Prog} (hQ : QuotProg p) (hRp : RecProg p) (hdn : DnInj dn) (hQd : QuotDn dn)
    (hnv : closedNV p L.Checker.nvFns = true) (k : ConLeche.QuotKind) (cv : IConstantVal) :
    ArmSpecE pins dn ds p "check_decl_quot" (.quotDecl k cv) := by
  unfold ArmSpecE
  intro n hn m a vis fe pend i hi hd hok0 hR hS hF hden _ hCr e hc
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (checkDeclQuot_specE p hQ.cdq n ⟨m, Locals.init []⟩ i vis) hc
    (Err.code_ne_of_cls hk0)
  have hd' : ds[i.toNat] = .quotDecl k cv := by
    rw [Array.getElem?_eq_getElem hi] at hd; exact Option.some.inj hd
  have hcvD : ∃ c, Frontend.denoteCV a.store cv = some c := by
    obtain ⟨x, hx⟩ := hden
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hx
    obtain ⟨c, hc, -⟩ := hx
    exact ⟨c, hc⟩
  have hdecl := hR.decls.recs i.toNat hi
  rw [hd'] at hdecl
  obtain ⟨-, hcvAt, hk⟩ := hdecl
  have h1r := hR.decls.room
  have h2r := hR.decls.dsize
  have hkw : rdW (m.arr64 DECL) (7 + 8 * i) = dw (m.arr64 DECL) i.toNat 6 :=
    rdW_dw _ (by omega) (by decide) (by decide)
  rw [checkDecl_quot_shape]
  cases n with
  | zero => rw [checkDeclQuotE.eq_1] at hW; cases hW; exact absurd rfl hk0
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [checkDeclQuotE.eq_2, hkw] at hW
  have hsel : ∀ (kw : Word) (J : Word → Except Err (Word × Mem)),
      (if kw = 1 then J 0 else if kw = 2 then J 1 else if kw = 3 then J 2 else J 3) =
        J (slotOfW kw) := by
    intro kw J; unfold slotOfW
    by_cases h1 : kw = 1 <;> by_cases h2 : kw = 2 <;> by_cases h3 : kw = 3 <;> simp [h1, h2, h3]
  rw [hsel (dw (m.arr64 DECL) i.toNat 6) (fun ks => checkDeclQuotE.j1 p n i vis ks m),
    slotOfW_eq, hk] at hW
  rw [checkDeclQuotE.j1.arm1] at hW
  cases h1 : callE p n "erec_ci" [i, 0] m with
  | error e1 =>
    rw [h1, checkDeclQuotE.k_erec_ci.none] at hW; cases hW
    exact nvl hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, checkDeclQuotE.k_erec_ci.arm1] at hW
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callE (erecCi_specW p hRp n ⟨m, Locals.init []⟩ i 0) h1
  subst hs1
  obtain ⟨hS1, hg1, -, hcv1, htop1⟩ := erecCiW_okA hW1 hS.stage hR.decls hi hcvAt
  have hqb : (r1.headD 0).toNat + 8 < 2 ^ 64 := by
    have := hS1.2.2.1; have := hS1.2.2.2.2.1; omega
  have hq1 : (r1.headD 0 + 1).toNat = (r1.headD 0).toNat + 1 := toNat_add_small _ 1 (by omega)
  -- `quot_pin_hit`
  cases h2 : callE p n "quot_pin_hit" [UInt64.ofNat k.slot, r1.headD 0 + 1] s1.mem with
  | error e2 =>
    rw [h2, checkDeclQuotE.k_quot_pin_hit.none] at hW; cases hW
    exact nvl hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2] at hW
  obtain ⟨s2, hs2, -, hW2⟩ := triple_of_callE
    (qph_specW p hQ.qph n ⟨s1.mem, Locals.init []⟩ _ _) h2
  subst hs2
  obtain ⟨b, a2, hrun2, hS2, hg2, hd2⟩ :=
    qphW_ok hQ.canon hQ.rom hW2 hS1 (by rw [hq1]; exact hcv1) hok0 (hQd.namesDn hS.twin.mem)
  obtain ⟨c, hc⟩ := hcvD
  have hrun2' : quotPinHit k cv a = .ok (b, a2) := hrun2
  obtain ⟨hok2, hx2, -⟩ := ConRon.Bridge.quotPinHit_run hok0 hc hrun2'
  refine ErrClaim.bind_right hrun2 ?_
  by_cases z2 : r2.headD 0 = 0
  · rw [checkDeclQuotE.k_quot_pin_hit.abort1 p _ _ _ _ _ z2] at hW; cases hW
    have hb : b = false := by rw [← hd2.1]; simpa using z2
    rw [hb]
    exact ErrClaim.ite_neg (by decide) (ErrClaim.fail _ _ rfl)
  have hb : b = true := by rw [← hd2.1]; simpa using z2
  rw [hb]
  refine ErrClaim.ite_pos rfl ?_
  by_cases ht : UInt64.ofNat k.slot = 0
  · rw [checkDeclQuotE.k_quot_pin_hit.arm1 p _ _ _ _ _ z2 ht] at hW
    have hk0' : k = .type := by
      cases k <;> simp_all [ConLeche.QuotKind.slot] <;> exact absurd ht (by decide)
    subst hk0'
    cases h3 : callE p n "check_basis_decl" [vis, 4] s2.mem with
    | error e3 =>
      rw [h3, checkDeclQuotE.k_check_basis_decl.none] at hW; cases hW
      exact cbdE_okT hQ.basis hQ.canon hQ.rom hnv hQ.pa hQ.cbd hdn (by decide) hS2
        (fun _ => ⟨hok2, L.Rom.NamesDn.ext (hQd.namesDn hS.twin.mem) hx2⟩) h3
    | ok q3 =>
      obtain ⟨r3, m3⟩ := q3
      rw [h3, checkDeclQuotE.k_check_basis_decl.arm1] at hW; cases hW
  · rw [checkDeclQuotE.k_quot_pin_hit.arm2 p _ _ _ _ _ z2 ht] at hW; cases hW

end quot

end L.Arena
