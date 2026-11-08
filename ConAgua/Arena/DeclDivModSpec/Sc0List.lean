module

public import ConAgua.Arena.DeclDivModSpec.DmCgW
public import ConAgua.Arena.DeclDivModSpec.EqAt1
public import ConAgua.Arena.IndRealApdT
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.DeclNatGate
import ConAgua.Arena.IndInstallSpec.DomsW
import all ConAgua.Arena.DeclArmsNat

@[expose] public section

/-!
# Sc0List

`DmProg5`, `applied_ref`, `sc0List_specW`, `sc0ListW`, `sc0List_ref`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

structure DmProg5 (p : Prog) : Prop extends DmProg2 p where
  lSlCons : p.lookup "sl_cons" = some slCons
  lIwCopy : p.lookup "iw_copy" = some iwCopy
  lSubstConst0 : p.lookup "subst_const0" = some substConst0L
  lSubstConstAll : p.lookup "subst_const_all" = some substConstAllL
  lSubstConst0List : p.lookup "subst_const0_list" = some substConst0ListL
  lConstsResolveAll : p.lookup "consts_resolve_all" = some constsResolveAllL
  lDivModCertGuard : p.lookup "div_mod_cert_guard" = some divModCertGuardL
  bvb : BvbProg p
  hf : HfF p
  /-- `all_level_params_defined`'s program (the guards under `StageT`, `DeclDivGateT1.lean`). -/
  apd : ApdF p

section applied
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

set_option maxHeartbeats 1600000 in
theorem applied_ref (hD : DmProg5 p) (pr ho hl : Word) (hyps : List EIdx) :
    CallRef p "div_mod_cert_applied" [pr, ho, hl]
      (fun m s => StageR vis fe m s ∧ H pr ∧ decHL m ho.toNat hl.toNat = some hyps ∧
        ho.toNat + hl.toNat ≤ iwTop m)
      (divModCertApplied (decE pr) hyps) (KeepPost vis fe decW0E) := by
  sorry

/-! ## `subst_const0_list` -/

/-- **`subst_const0_list` is its model `sc0ListW`** (generated). -/
l_model sc0List_specW (p : Prog) (hp : p.lookup "subst_const0_list" = some substConst0ListL)
  fns [hp ↦ sc0ListW list]
  specs [callW_spec p n "subst_const0", callW_spec p n "subst_const0_list", callW_spec p n "sl_cons"]
  grind [arena_grind] finish [ntBW, rdW_eq] gen 30 heartbeats 1600000 bind ntBW instances 10000

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem sc0List_ref (hD : DmProg5 p) (hs0 : SubstC0 p dn vis fe) (nm r : Word) (hn : H nm) (hr : H r) :
    ∀ (hyps : List EIdx) (o l : Word) (k : Nat) (m : Mem) (a : AState) (res : List Word) (m' : Mem),
      StageR vis fe m a → decHL m o.toNat l.toNat = some hyps → o.toNat + l.toNat ≤ iwTop m →
      callW p k "subst_const0_list" [nm, r, o, l] m = some (res, m') →
      ∃ x a', (substConst0List (decI nm) (decE r) hyps).run a = .ok (x, a') ∧
        KeepPost vis fe (decRL (fun m => decHL m) 0) m m' a' res x := by
  sorry

-/

end applied

end L.Ind

end
