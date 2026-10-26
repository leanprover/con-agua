import ConAgua.Verdict.DeclValsE
import ConAgua.Arena.CheckerT

/-!
# The verdict claims of the `check_decl` arms (lane `verdicts-b`, helper `d`)

`ArmSpecE`: the error half of `ArmSpecT` (`Arena/CheckerT.lean`), the arm's failing runs claim
the twin's `checkDecl` failure. Under the hypotheses of the ok refinements and the callees' error
claims (`CoreStubsE`, `IvgE`).
-/

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF)
open ConRon.Bridge (FoldOK PinsDenote)

local notation "V" => ConLeche.CheckMode.verified

l_model checkDeclThm_specE (p : Prog) (hf : p.lookup "check_decl_thm" = some checkDeclThm)
  fns [hf ↦ checkDeclThmE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

section arms
variable (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)

/-- **The shape of an arm's error spec** (`ArmSpecT`'s error half): a failing run of the arm on
record `d` claims the twin's `checkDecl` failure from the same state. -/
def ArmSpecE (p : Prog) (f : FnName) (d : IDeclaration) : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (m : Mem) (a₀ : AState) (vis : Word) (fe : IFEnv)
    (pend : Array PendingCheck) (i : Word), i.toNat < ds.size → ds[i.toNat]? = some d →
    ConRon.Bridge.StateOK a₀ → LoopR pins dn m a₀ vis fe pend ds →
    StageT dn vis fe m a₀ → (∃ env, FoldOK V env fe a₀) →
    (∃ x, Frontend.denoteDecl a₀.store d = some x) → (∃ pinsP, PinsDenote a₀.store pins pinsP) →
    L.Stubs.CrOK m → ∀ e, callE p n f [i, vis] m = .error e →
    ErrClaim (checkDecl V pins fe d) a₀ e

/-- **`check_decl_thm`'s error claim under `StageT`.** -/
theorem checkDeclThm_errT {p : Prog} (hV : ValProg p) (hq : KnotStageProg p) (hap : ApdF p)
    (hkp : CrKeep p) (hnv : closedNV p L.Checker.nvFns = true) (hcE : CoreStubsE p)
    (hivE : IvgE p) (hnvP : NVAt p "pin_word") (hnvL : NVAt p "lvl_eq_c")
    (hnvE : NVAt p "env_push")
    (hp : p.lookup "check_decl_thm" = some checkDeclThm) (cv : IConstantVal) (v : EIdx) :
    ArmSpecE pins dn ds p "check_decl_thm" (.thmDecl cv v) := by
  unfold ArmSpecE
  intro n hn m a vis fe pend i hi hd _ hR hS hF hden _ hCr e hc
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (checkDeclThm_specE p hp n ⟨m, Locals.init []⟩ i vis) hc
    (Err.code_ne_of_cls hk0)
  have hd' : ds[i.toNat] = .thmDecl cv v := by
    rw [Array.getElem?_eq_getElem hi] at hd; exact Option.some.inj hd
  obtain ⟨env, hF⟩ := hF
  obtain ⟨x, hx⟩ := hden
  simp only [Frontend.denoteDecl] at hx
  split at hx
  rotate_left
  · cases hx
  rename_i c e' hcd he
  show ErrClaim (do checkConstantVal V fe cv; checkThmVal V fe cv v) a e
  cases n with
  | zero => rw [checkDeclThmE.eq_1] at hW; cases hW; exact absurd rfl hk0
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  simp only [checkDeclThmE] at hW
  cases h1 : callE p n "erec_ci" [i, 2] m with
  | error e1 =>
    rw [h1, checkDeclThmE.k_erec_ci.none] at hW; cases hW
    exact nvl hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, checkDeclThmE.k_erec_ci.arm1] at hW
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callE (erecCi_specW p hV.rcp n ⟨m, Locals.init []⟩ i 2) h1
  subst hs1
  have hCr1 := CrOK.frame hCr (erecCiW_frame hW1) (by decide) (by decide)
  obtain ⟨hS1, hg1, hci1, hcv1, hval1, htop1⟩ :=
    erecCiW_okT (ci := .thmInfo cv) hW1 hS hR.decls hi (by rw [hd']; rfl)
  rw [hd'] at hcv1 hval1
  simp only [stepCV, stepVal] at hcv1 hval1
  generalize hq0 : r1.headD 0 = q at hW hci1 hcv1 hval1 htop1
  have hqb : q.toNat + 8 < 2 ^ 64 := by
    have := hS1.stage.2.2.1; have := hS1.stage.2.2.2.2.1; omega
  have hq1 : (q + 1).toNat = q.toNat + 1 := toNat_add_small q 1 (by omega)
  -- `check_constant_val(vis, q + 1)`
  cases h2 : callE p n "check_constant_val" [vis, q + 1] s1.mem with
  | error e2 =>
    rw [h2, checkDeclThmE.k_check_constant_val.none] at hW; cases hW
    exact ErrClaim.bind_left (ccvE_okT hq hV hap hkp hnv hcE hn' h2 hS1 (by rw [hq1]; exact hcv1)
      (by omega) (denoteCV_lps hcd) hCr1)
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, checkDeclThmE.k_check_constant_val.arm1] at hW
  obtain ⟨s2, hs2, -, hok2, hS2, hg2, hCr2⟩ := triple_of_callE
    (checkConstantVal_refinesT p hV hq hap hkp n hn' ⟨s1.mem, Locals.init []⟩ a dn fe vis (q + 1) cv
      hS1 (by rw [hq1]; exact hcv1) (by omega) (denoteCV_lps hcd) hCr1) h2
  subst hs2
  have hrun2 := AM.run_of_ok _ _ hok2
  obtain ⟨hstep1, _F1, hpure1⟩ :=
    ConRon.Bridge.checkConstantVal_bridge_of_fold rfl (ConRon.Bridge.CoreSpec.of_core rfl) hF hcd hrun2
  have hok1 := hF.ofCore hstep1
  have hcA := ConRon.Bridge.denoteCV_ext hcd hstep1.ext
  have hwsT : ConLeche.Expr.WScoped 0 c.type :=
    ConLeche.Expr.WScoped.of_not_hasFvar (ConRon.Bridge.checkConstantVal_typeWF hpure1).fvar
  refine ErrClaim.bind_right hrun2 ?_
  -- `check_thm_val(vis, q)`
  cases h3 : callE p n "check_thm_val" [vis, q] s2.mem with
  | error e3 =>
    rw [h3, checkDeclThmE.k_check_thm_val.none] at hW; cases hW
    have hx2 : ArrExt (erecP s1.mem) (erecP s2.mem) := IWGrow.erecPExt hg2
    exact tvE_okT hq hV hq.knot.lvc hap hkp hcE hivE hnvP hnvL hnvE hn' hS2
      (ArrExt.decCV hx2 hcv1) (ArrExt.hd? hx2 hval1) ⟨env, c, hok1.envWF, hok1.check, hcA, hwsT⟩
      hCr2 h3
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, checkDeclThmE.k_check_thm_val.arm1] at hW
  cases hW

end arms

end L.Arena
