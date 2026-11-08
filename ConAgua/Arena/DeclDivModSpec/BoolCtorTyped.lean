module

public import ConAgua.Arena.DeclDivModSpec.Sc0List
public import ConAgua.Arena.DeclDivModSpec.Cons
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import all ConAgua.Arena.DeclArmsNat

@[expose] public section

/-!
# BoolCtorTyped: `ConRon.Arena.boolCtorTyped`, `ConRon.Arena.typePinStored`

The refinement theorems `boolCtorTyped_refines`, `typePinStored_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

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
    CallRef p "bool_ctor_typed" [vis, nm] (fun m a => StageR vis fe m a ∧ H nm)
      (boolCtorTyped fe (decI nm)) (KeepPost vis fe decW0B) := by
  sorry

@[refines ConRon.Arena.boolCtorTyped]
theorem boolCtorTyped_refines (hD : DmProg6 p) (nm : Word) :
    RefAM p "bool_ctor_typed" [vis, nm] (fun m a => StageR vis fe m a ∧ H nm)
      (boolCtorTyped fe (decI nm)) (KeepPost vis fe decW0B) :=
  (bct_ref hD nm).refAM

/-! ## `div_mod_pin_guard` -/

/-- **`type_pin_stored` is its model `dmTpsW`** (generated). -/
l_model tps_specW (p : Prog) (hp : p.lookup "type_pin_stored" = some typePinStoredL)
  fns [hp ↦ dmTpsW list]
  specs [callW_spec p n "env_find", callW_spec p n "pin_word", callW_spec p n "intern_sort",
    callW_spec p n "ci_to_cv"]
  grind [arena_grind] finish [ntBW, rdW_eq] gen 30 heartbeats 1600000 bind ntBW instances 10000

theorem internSort_ref (hM : MasterProg p) (u : Word) (hu : H u) :
    CallRef p "intern_sort" [u] (StageR vis fe) (internE (.sort (decI u)))
      (KeepPost vis fe decW0E) := by
  refine CallRef.of_triple fun n s₀ a₀ hS => ?_
  refine triple_post (internSort_spec p hM.lSortFind hM.lSortPush hM.lInternSort n s₀ u) ?_
  rintro r s' ⟨hl, hI⟩
  obtain ⟨a', hrun, hS', hg⟩ := internSort_stage hS u hu hI
  exact ⟨hl, decE (r.headD 0), a', hrun, hS', hg, consInternM_lt sortCS_wf hS.check.arena.base.sort hI, rfl⟩

theorem tps_ref (hD : DmProg6 p) (nm : Word) :
    CallRef p "type_pin_stored" [vis, nm] (fun m a => StageR vis fe m a ∧ H nm)
      (typePinStored fe (decI nm)) (KeepPost vis fe decW0E) := by
  sorry

@[refines ConRon.Arena.typePinStored]
theorem typePinStored_refines (hD : DmProg6 p) (nm : Word) :
    RefAM p "type_pin_stored" [vis, nm] (fun m a => StageR vis fe m a ∧ H nm)
      (typePinStored fe (decI nm)) (KeepPost vis fe decW0E) :=
  (tps_ref hD nm).refAM

set_option maxHeartbeats 1600000 in
theorem gg_specW (p : Prog) (hb : BvbProg p) (hf : HfF p) (hp : p.lookup "ground_guards" = some groundGuardsL)
    (cl : CallM) (hcl : CallSpec p cl) (n : Nat) (s₀ : St) (vs pe : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "ground_guards" [vs, pe]
    ⦃fun r s' => LocEq s' s₀ ∧ dmGgW p cl n s₀.mem vs pe = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, groundGuardsL]
  sym only [lang_grind, arena_grind] =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, lbbF_spec p hb n,
      hffF_spec p hf n, hcl n "all_level_params_defined", hcl n "consts_resolve_ffast"] <;>
    finish (gen := 30) (instances := 10000) [dmGgW, ntBW]

set_option maxHeartbeats 1600000 in
theorem tpg_specW (p : Prog) (hb : BvbProg p) (hf : HfF p) (hp : p.lookup "type_pin_guard" = some typePinGuardL)
    (cl : CallM) (hcl : CallSpec p cl) (n : Nat) (s₀ : St) (vs nm ty : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "type_pin_guard" [vs, nm, ty]
    ⦃fun r s' => LocEq s' s₀ ∧ dmTpgW p cl n s₀.mem vs nm ty = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, typePinGuardL]
  sym only [lang_grind, arena_grind] =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, callW_spec p n "env_find",
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
  grind [arena_grind] heartbeats 1600000 bind ntBW

theorem word_add_two {w : Word} (h : w.toNat + 2 < 2 ^ 64) : (w + 2).toNat = w.toNat + 2 := by
  rw [UInt64.toNat_add]; simp; omega

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
  grind [arena_grind] heartbeats 1600000 bind ntBW

end guards

end L.Ind

end
