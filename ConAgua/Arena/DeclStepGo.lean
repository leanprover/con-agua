module

public import ConAgua.Arena.DeclHeader
public import ConAgua.Arena.DeclRec
import ConAgua.Arena.DeclStepSpec
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
public import ConAgua.Arena.DeclBase
public import ConAgua.Arena.DeclCvg
import all ConAgua.Arena.DeclStep

@[expose] public section

noncomputable section

/-!
# Phase A's step body, `install_step_go`, refines `installStepGo` (lane `decls2`)

`install_step_go(i, vis)` reads the record's kind and name, asks `pin_in` whether a definition or
an opaque is pinned, and goes to `check_decl` (the pinned names and every other kind) or to
`install_value` (the guard-and-install arm). This file: `pin_in`'s model and meaning, the twin's
name lists under the pin table, the arm's twin (`ivT`). The unified model and the refinement, under
`StageT`, are `CheckerT.lean`'s `installStepGoE` and `istg_ref` (lane `loopt2`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF DeclAt CVAt dw)

/-! ## `pin_in(x, k, hi)` -/

/-- The model of `pin_in` (the memory is unchanged). -/
def pinInW : Nat → Mem → Word → Word → Word → Option Word
  | 0, _, _, _, _ => none
  | n + 1, m, x, k, hi =>
    if pinW m 0 = 0 then none
    else if hi ≤ k then some 0
    else if rdW (m.arr64 PINS) k = x then some 1
    else pinInW n m x (k + 1) hi

section arms
variable (n : Nat) (m : Mem) (x k hi : Word)
theorem pinInW_empty (h0 : pinW m 0 = 0) : pinInW (n + 1) m x k hi = none := by simp [pinInW, h0]
theorem pinInW_end (h0 : pinW m 0 ≠ 0) (h : hi ≤ k) : pinInW (n + 1) m x k hi = some 0 := by
  simp [pinInW, h0, h]
theorem pinInW_hit (h0 : pinW m 0 ≠ 0) (h : ¬ hi ≤ k) (h2 : rdW (m.arr64 PINS) k = x) :
    pinInW (n + 1) m x k hi = some 1 := by simp [pinInW, h0, h, h2]
theorem pinInW_next (h0 : pinW m 0 ≠ 0) (h : ¬ hi ≤ k) (h2 : rdW (m.arr64 PINS) k ≠ x) :
    pinInW (n + 1) m x k hi = pinInW n m x (k + 1) hi := by simp [pinInW, h0, h, h2]
end arms

grind_pattern [ind_grind] pinInW_empty => pinInW (n + 1) m x k hi
grind_pattern [ind_grind] pinInW_end => pinInW (n + 1) m x k hi
grind_pattern [ind_grind] pinInW_hit => pinInW (n + 1) m x k hi
grind_pattern [ind_grind] pinInW_next => pinInW (n + 1) m x k hi

/-- **What `pin_in` answers**: `x` is one of the words `PINS[k‥hi)`. -/
theorem pinInW_ok (n : Nat) : ∀ (m : Mem) (x k hi : Word) (c : Word),
    pinInW n m x k hi = some c → hi.toNat ≤ 71 →
    (c ≠ 0 ↔ ∃ j, k.toNat ≤ j ∧ j < hi.toNat ∧ rdW (m.arr64 PINS) (UInt64.ofNat j) = x) := by
  induction n with
  | zero => intro m x k hi c h; simp [pinInW] at h
  | succ n ih =>
    intro m x k hi c h hh
    by_cases h0 : pinW m 0 = 0
    · rw [pinInW_empty n m x k hi h0] at h; cases h
    by_cases h1 : hi ≤ k
    · rw [pinInW_end n m x k hi h0 h1] at h
      cases h
      have : hi.toNat ≤ k.toNat := UInt64.le_iff_toNat_le.mp h1
      simp only [ne_eq, not_true_eq_false, false_iff, not_exists, not_and]
      intro j hj hj2; omega
    · have hlt : k.toNat < hi.toNat := by
        have : ¬ hi.toNat ≤ k.toNat := fun h' => h1 (UInt64.le_iff_toNat_le.mpr h'); omega
      by_cases h2 : rdW (m.arr64 PINS) k = x
      · rw [pinInW_hit n m x k hi h0 h1 h2] at h
        cases h
        refine ⟨fun _ => ⟨k.toNat, Nat.le_refl _, hlt, by simpa using h2⟩, fun _ => by decide⟩
      · rw [pinInW_next n m x k hi h0 h1 h2] at h
        have hk1 : (k + 1).toNat = k.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
        rw [ih m x (k + 1) hi c h hh, hk1]
        constructor
        · rintro ⟨j, h3, h4, h5⟩; exact ⟨j, by omega, h4, h5⟩
        · rintro ⟨j, h3, h4, h5⟩
          refine ⟨j, ?_, h4, h5⟩
          rcases Nat.lt_or_ge k.toNat j with hj | hj
          · omega
          · have : j = k.toNat := by omega
            subst this
            exact absurd (by simpa using h5) h2

/-! ## The pinned names, under a filled pin table -/

theorem natOpNames_run {m : Mem} {a : AState} (h : PinsFull m a.pins) :
    natOpNames.run a = .ok ((List.range' 15 7).map (fun j => decI (pinW m j)), a) := by
  simp [natOpNames, natPredName, natAddName, natSubName, natMulName, natPowName, natBeqName,
    natBleName, pinNatPred, pinNatAdd, pinNatSub, pinNatMul, pinNatPow, pinNatBeq, pinNatBle,
    PIN_NAT_PRED, PIN_NAT_ADD, PIN_NAT_SUB, PIN_NAT_MUL, PIN_NAT_POW, PIN_NAT_BEQ, PIN_NAT_BLE,
    StateT.run_bind, pinAt_run h, exc_ok_bind', List.range']
  rfl

theorem natDivModNames_run {m : Mem} {a : AState} (h : PinsFull m a.pins) :
    natDivModNames.run a = .ok ((List.range' 22 8).map (fun j => decI (pinW m j)), a) := by
  simp [natDivModNames, natDivName, natModName, natGcdName, natLandName, natLorName, natXorName,
    natShiftLeftName, natShiftRightName, pinNatDiv, pinNatMod, pinNatGcd, pinNatLand, pinNatLor,
    pinNatXor, pinNatShiftLeft, pinNatShiftRight, PIN_NAT_DIV, PIN_NAT_MOD, PIN_NAT_GCD,
    PIN_NAT_LAND, PIN_NAT_LOR, PIN_NAT_XOR, PIN_NAT_SHIFT_LEFT, PIN_NAT_SHIFT_RIGHT,
    StateT.run_bind, pinAt_run h, exc_ok_bind', List.range']
  rfl

theorem reduceOpNames_run {m : Mem} {a : AState} (h : PinsFull m a.pins) :
    reduceOpNames.run a = .ok ((List.range' 44 2).map (fun j => decI (pinW m j)), a) := by
  simp [reduceOpNames, reduceNatName, reduceBoolName, pinReduceNat, pinReduceBool,
    PIN_REDUCE_NAT, PIN_REDUCE_BOOL, StateT.run_bind, pinAt_run h, exc_ok_bind', List.range']
  rfl

/-- A `pin_in` answer means a filled pin table. -/
theorem pinInW_flag {n : Nat} {m : Mem} {x k hi c : Word} (h : pinInW n m x k hi = some c) :
    pinW m 0 ≠ 0 := by
  cases n with
  | zero => simp [pinInW] at h
  | succ n => intro h0; rw [pinInW_empty n m x k hi h0] at h; cases h

/-- **A pinned name list's `contains`, as word equality** (the pinned names are handle words). -/
theorem contains_pins {m : Mem} {p : Pins} (hF : PinsFull m p) {x : Word} (hx : x.toNat < 2 ^ 32)
    (lo cnt : Nat) (h1 : 1 ≤ lo) (h2 : lo + cnt ≤ 52) :
    ((List.range' lo cnt).map fun j => (decI (pinW m j) : NIdx)).contains (decI x) = true ↔
      ∃ j, lo ≤ j ∧ j < lo + cnt ∧ pinW m j = x := by
  rw [List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨j, hj, he⟩
    rw [List.mem_range'] at hj
    obtain ⟨k, hk, rfl⟩ := hj
    have hlt : (pinW m (lo + 1 * k)).toNat < 2 ^ 32 := by
      have := hF.names_lt (lo + 1 * k - 1) (by omega)
      rwa [show 1 + (lo + 1 * k - 1) = lo + 1 * k by omega] at this
    exact ⟨lo + 1 * k, by omega, by omega, decI_inj hlt hx he⟩
  · rintro ⟨j, hj1, hj2, rfl⟩
    refine ⟨j, ?_, rfl⟩
    rw [List.mem_range']
    exact ⟨j - lo, by omega, by omega⟩

theorem rdW_pins (m : Mem) (j : Nat) (hj : j < 2 ^ 64) :
    rdW (m.arr64 PINS) (UInt64.ofNat j) = pinW m j := by
  have : (UInt64.ofNat j).toNat = j := UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; exact hj)
  simp [rdW, pinW, this]

/-- **`pin_in` against a twin name list**: a nonzero answer is the twin's `contains`. -/
theorem pinIn_contains {m : Mem} {p : Pins} (hF : PinsFull m p) {n : Nat} {x k hi c : Word}
    (h : pinInW n m x k hi = some c) (hx : x.toNat < 2 ^ 32) (h1 : 1 ≤ k.toNat) (hk : k ≤ hi)
    (h2 : hi.toNat ≤ 52) :
    (c ≠ 0) ↔ ((List.range' k.toNat (hi.toNat - k.toNat)).map
      fun j => (decI (pinW m j) : NIdx)).contains (decI x) = true := by
  have hk' : k.toNat ≤ hi.toNat := UInt64.le_iff_toNat_le.mp hk
  rw [pinInW_ok n m x k hi c h (by omega), contains_pins hF hx _ _ h1 (by omega)]
  constructor
  · rintro ⟨j, a, b, e⟩; exact ⟨j, a, by omega, by rw [← rdW_pins m j (by omega)]; exact e⟩
  · rintro ⟨j, a, b, e⟩; exact ⟨j, a, by omega, by rw [rdW_pins m j (by omega)]; exact e⟩

/-! ## The twin's two arms -/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`installStepGo`'s `checkDecl` arm.** -/
def cdT (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (fe : IFEnv) (d : IDeclaration) :
    AM (IFEnv × Option ValueGroup) := do
  pure (← checkDecl mode pins fe d, none)
-/

/-- The pinned definitions' names (`natOpNames ++ natDivModNames`) are the pin table's 15 to 29. -/
theorem pinnedDefn_contains (m : Mem) (x : NIdx) :
    (((List.range' 15 7).map fun j => (decI (pinW m j) : NIdx)).contains x ||
      ((List.range' 22 8).map fun j => (decI (pinW m j) : NIdx)).contains x) =
      ((List.range' 15 15).map fun j => (decI (pinW m j) : NIdx)).contains x := by
  rw [← List.contains_append, ← List.map_append]; rfl

/-- The lookups `install_step_go`'s body needs. -/
structure IstgProg (p : Prog) : Prop where
  reset : p.lookup "iw_reset" = some iwReset

/-! ## The loop's relation around the body -/

theorem stepC_200 : (200 : Word) ∈ stepC := by decide +kernel

/-- **`iw_reset` keeps the loop's relation.** -/
theorem LoopR.reset {pins : List INatOpPinSet} {m : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {ds : Array IDeclaration}
    (h : LoopR pins m a vis fe ds) : LoopR pins (m.set64 CTL 200 0) a vis fe ds := by
  have hf : MemFrame stepA stepC m (m.set64 CTL 200 0) :=
    (MemFrame.setCtl m 200 0).mono (by simp) (by simpa using stepC_200)
  refine h.of_step (iwReset_stage ⟨h.check, h.iw⟩).1 hf ?_
  rw [erecP_reset]; exact fun _ _ h => h

/-- The constant-record and value-group kinds of `install_value`'s call for a record. -/
def IvArgs (ck vk : Word) : IDeclaration → Prop
  | .defnDecl .. => ck = 1 ∧ vk = 0
  | .thmDecl .. => ck = 2 ∧ vk = 1
  | .opaqueDecl .. => ck = 0 ∧ vk = 2
  | _ => False

/-! ## `install_value`'s text -/

/-- `install_value`'s text: this lane's functions, lane `induct`'s library and stubs, the
environment. -/
def ivProg : Prog := declStepFns ++ L.Ind.libFns ++ L.Ind.stubFns ++ envProg

/-- The functions `install_value` reaches. -/
def ivFns : List FnName :=
  ["erec_ci", "erec_alloc", "dlp_copy", "env_find",
   "env_row_get", "env_ix", "reserved_contains", "reserved_from", "cv_lps",
   "er_to_iw", "iw_alloc", "er_copy", "sl_nodup", "sl_contains", "loose_bvars_bounded_fast",
   "has_fvar_fast", "all_level_params_defined", "consts_resolve_ffast", "env_push", "env_row_set"]

/-- A program with `install_value`'s text. -/
structure IvProg (p : Prog) : Prop extends TextProg p ivProg ivFns where
  bvb : BvbProg p
  hf : HfF p

section ivLookups
variable {p : Prog} (h : IvProg p)
include h
theorem IvProg.recP : RecProg p := by
  constructor <;> exact (h.agree _ (by decide) (by decide)).trans rfl
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem IvProg.ih : IhProg p := by
  sorry

-/
end ivLookups

end L.Arena
