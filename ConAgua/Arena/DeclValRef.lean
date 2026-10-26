import ConAgua.Arena.DeclValSpec

/-!
# `checkDecl`'s value checks: the relational lemmas (lane `decls3`)

A model run of `check_constant_val`/`check_defn_val`/`check_thm_val`/`check_opaque_val` from the
stage relation is a successful twin run (`ccvW_ok`, `dvW_ok`, `tvW_ok`), and the census theorems
(`checkConstantVal_refines`, …) assemble them with the `vcgen` specs of `DeclValSpec.lean`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

open L.Ind

local notation "V" => ConLeche.CheckMode.verified

/-- The value checks' common tail: the value's guards, its type against the declared one, the
push of `ci` (`msg` the twin's error text, never reached on a successful run). -/
def dvT (fe : IFEnv) (cv : IConstantVal) (v : EIdx) (ci : IConstantInfo) (msg : String) :
    AM IFEnv := do
  installValueGuards fe cv v
  let vtype ← inferTypeCore V fe checkFuel 0 v
  unless ← isDefEqCore V fe checkFuel 0 vtype cv.type do
    fail (.invalid msg)
  pure (fe.push ci)

theorem checkDefnVal_dvT (fe : IFEnv) (cv : IConstantVal) (v : EIdx)
    (h : ConLeche.ReducibilityHint) :
    checkDefnVal V fe cv v h = dvT fe cv v (.defnInfo cv v h) "type mismatch in definition" := rfl

theorem checkOpaqueVal_dvT (fe : IFEnv) (cv : IConstantVal) (v : EIdx) :
    checkOpaqueVal V fe cv v = dvT fe cv v (.axiomInfo cv) "type mismatch in opaque" := rfl

theorem checkThmVal_eq (fe : IFEnv) (cv : IConstantVal) (v : EIdx) :
    checkThmVal V fe cv v = (do
      let stype ← inferTypeCore V fe checkFuel 0 cv.type
      let u ← ensureSortCore V fe checkFuel 0 stype
      let z ← zeroLevel
      unless ← liftFueled "level comparison" (← lvlEq? u z) do
        fail (.invalid "type of theorem is not a proposition")
      dvT fe cv v (.thmInfo cv) "type mismatch in theorem") := by
  simp only [checkThmVal, dvT]

theorem toNat_add_small (c : Word) (k : Nat) (h : c.toNat + k < 2 ^ 64) :
    (c + UInt64.ofNat k).toNat = c.toNat + k := by
  rw [UInt64.toNat_add]; simp; omega

/-- A decoding in `erecP` is below the record pool's size, so offsets from it do not wrap. -/
theorem erecP_bound {m : Mem} {i : Nat} {w : Word} (h : (erecP m)[i]? = some w) (hS : IWOK m) :
    i < 2 ^ 64 := by
  have := (Array.getElem?_eq_some_iff.mp (erecP_get h)).1
  have := hS.2.2.2.1
  omega

/-! ## `check_constant_val` -/

/-! ## `check_defn_val`, `check_opaque_val` -/

end L.Arena

namespace L.Arena

open L.Ind

local notation "V" => ConLeche.CheckMode.verified

/-! ## `check_thm_val` -/

/-! ## The census theorems -/

theorem decls_decCI_defn {a : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Nat} {cv : IConstantVal}
    {v : EIdx} {hh : ConLeche.ReducibilityHint} (h : decCI a dn q = some (.defnInfo cv v hh)) :
    decCV a (q + 1) = some cv ∧ hd? a (q + 5) = some v := by
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, -, h⟩ := h
  split at h
  all_goals (try simp only [Option.bind_eq_some_iff, Option.some.injEq] at h)
  all_goals grind

theorem decCI_cvTA {a : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Nat}
    {ci : IConstantInfo} {cv : IConstantVal}
    (h : decCI a dn q = some ci) (hk : ci = .thmInfo cv ∨ ci = .axiomInfo cv) :
    decCV a (q + 1) = some cv := by
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, -, h⟩ := h
  rcases hk with rfl | rfl <;> split at h
  all_goals (try simp only [Option.bind_eq_some_iff, Option.some.injEq] at h)
  all_goals grind

end L.Arena
