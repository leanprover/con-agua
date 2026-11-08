module

import ConAgua.Arena.DeclBasisSpec2
public import ConAgua.Arena.DeclDivModSpec.BoolCtorTyped
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.DeclNatDeps
public import ConAgua.Arena.DeclCanonEq
public import ConAgua.Rom.CIReadSpec
import all ConAgua.Arena.DeclArmsNat

@[expose] public section

/-!
# DivModEnvGuard: `ConRon.Arena.divModEnvGuard`

The refinement theorems `divModEnvGuard_refines` and the lemmas only they use.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open L.Rom (PinSetR)

namespace L.Ind

open L.Arena

structure DmProg7 (p : Prog) : Prop extends DmProg6 p where
  lDivModEnvGuard : p.lookup "div_mod_env_guard" = some divModEnvGuardL
  lFindIs : p.lookup "find_is" = some findIs
  lNatOpGuard' : p.lookup "nat_op_guard" = some natOpGuardL
  lRom : L.Rom.RomRefs p

section envguard
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

/-- **`div_mod_env_guard` is its model `egW`** (generated). -/
l_model eg_specW (p : Prog) (hp : p.lookup "div_mod_env_guard" = some divModEnvGuardL)
  fns [hp ↦ egW list]
  specs [callW_spec p n "nat_op_guard", callW_spec p n "nat_op_deps", callW_spec p n "nat_op_stored_ok_all", callW_spec p n "pin_at", callW_spec p n "rom_ci", callW_spec p n "find_is", callW_spec p n "bool_ctor_typed"]
  grind [arena_grind] heartbeats 3200000 bind ntBW

theorem DmProg7.ty (hD : DmProg7 p) : NatTyProg p := hD.toDmProg6.toDmProg5.toDmProg2.toNatEqProg.toNatTyProg

@[refines ConRon.Arena.divModEnvGuard]
theorem divModEnvGuard_refines (hD : DmProg7 p) (hdn : DnInj dn) (c : Word) :
    RefAM p "div_mod_env_guard" [vis, c] (fun m s => StageR vis fe m s ∧ H c)
      (divModEnvGuard fe (decI c)) (KeepPost vis fe decW0B) :=
  (eg_ref hD hdn c).refAM

end envguard

end L.Ind
