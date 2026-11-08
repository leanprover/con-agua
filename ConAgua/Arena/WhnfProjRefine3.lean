module

import ConAgua.Arena.WhnfProjRefine2
public import ConAgua.Arena.DeclLvlStage
import ConAgua.Arena.InferProj
import ConAgua.Arena.WhnfIotaRefine4
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.Arena.WhnfCoreProj
import ConAgua.Arena.WhnfIotaRefine2
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.CoreDen
public import ConAgua.Arena.Knot
public import ConAgua.Arena.WhnfIotaRefine
public import ConAgua.Arena.WhnfProjRefine
import all ConAgua.Arena.WhnfProj

@[expose] public section

/-!
# `tower_slots_all` refines `towerSlotsAll` on the real `find_proj`

(The file's `fire_ok` refinement went with `IProjEntry.fireOk`, con-leche's task #480.)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

theorem except_ok_bind' {ε α β : Type} (x : α) (f : α → Except ε β) : (Except.ok x >>= f) = f x := rfl

theorem rdW_of_get {a : Array Word} {x : Word} {k : Nat} {w : Word} (hk : x.toNat = k)
    (h : a[k]? = some w) : rdW a x = w := by simp [rdW, hk, h]

theorem fo_toNat_add_small (x : Word) (c : Nat) (h : x.toNat + c < 2 ^ 64) :
    (x + UInt64.ofNat c).toNat = x.toNat + c := by
  rw [UInt64.toNat_add]
  have e : (UInt64.ofNat c).toNat = c := by simp; omega
  rw [e]; exact Nat.mod_eq_of_lt h

/-- **`tower_slots_all` refines `towerSlotsAll`**, on the real `find_proj`. -/
@[refines ConRon.Arena.towerSlotsAll]
theorem towerSlotsAll_refines (p : Prog) (hp : IotaProg' p) (hq : ProjProg p) :
    TowerSlotsAllOK p :=
  towerSlotsAll_refines' p hp (findProj_refines p hq) (projFound p hq)

end L.Arena
