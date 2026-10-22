import ConAgua.Arena.DeclHeader
import ConAgua.Arena.DeclStepSpec
import ConAgua.Arena.PinsNatOp
import ConAgua.Arena.WhnfBase

/-!
# Phase A's step body, `install_step_go`, refines `installStepGo` (lane `decls2`)

`install_step_go(i, vis)` reads the record's kind and name, asks `pin_in` whether a definition or
an opaque is pinned, and goes to `check_decl` (the pinned names and every other kind) or to
`install_value` (the guard-and-install arm). This file: `pin_in`'s model and meaning, the twin's
name lists under the pin table, the arm's twin (`ivT`), and the dispatch.
-/

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsR DeclAt CVAt dw)

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

theorem pinIn_specW (p : Prog) (hp : p.lookup "pin_in" = some pinIn) (n : Nat) :
    ∀ (s₀ : St) (x k hi : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pin_in" [x, k, hi]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ pinInW n s₀.mem x k hi = some (r.headD 0); ⊤⦄ := by
  induction n with
  | zero => intro s₀ x k hi; rw [invoke_eq _ hp]; simp only [callFn, pinIn]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ x k hi
    rw [invoke_eq _ hp]
    simp only [callFn, pinIn]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      finish (gen := 20) [rdW_eq, pinW_eq]

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

/-- **`installStepGo`'s guard-and-install arm** (what `install_value` refines). -/
def ivT (fe : IFEnv) : IDeclaration → AM (IFEnv × Option ValueGroup)
  | .defnDecl cv value hint => do
    installHeader fe cv
    installValueGuards fe cv value
    pure (fe.push (.defnInfo cv value hint), some ⟨.defn, cv, value⟩)
  | .thmDecl cv value => do
    installHeader fe cv
    pure (fe.push (.thmInfo cv), some ⟨.thm, cv, value⟩)
  | .opaqueDecl cv value => do
    installHeader fe cv
    installValueGuards fe cv value
    pure (fe.push (.axiomInfo cv), some ⟨.opaque, cv, value⟩)
  | _ => pure (fe, none)

/-- **`installStepGo`'s `checkDecl` arm.** -/
def cdT (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (fe : IFEnv) (d : IDeclaration) :
    AM (IFEnv × Option ValueGroup) := do
  pure (← checkDecl mode pins fe d, none)

/-- The pinned definitions' names (`natOpNames ++ natDivModNames`), as the pin table holds them. -/
def pinnedDefnL (m : Mem) : List NIdx :=
  (List.range' 15 7).map (fun j => decI (pinW m j)) ++ (List.range' 22 8).map (fun j => decI (pinW m j))

/-- The pinned opaques' names (`reduceOpNames`). -/
def pinnedOpaqueL (m : Mem) : List NIdx := (List.range' 44 2).map (fun j => decI (pinW m j))

theorem pinnedDefnL_eq (m : Mem) :
    pinnedDefnL m = (List.range' 15 15).map (fun j => decI (pinW m j)) := by
  simp [pinnedDefnL, List.range']

section twin
variable (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (fe : IFEnv) {m : Mem} {a : AState}

theorem installStepGo_defn (h : PinsFull m a.pins) (cv : IConstantVal) (v : EIdx)
    (hint : ConLeche.ReducibilityHint) :
    (installStepGo mode pins fe (.defnDecl cv v hint)).run a =
      if (pinnedDefnL m).contains cv.name then (cdT mode pins fe (.defnDecl cv v hint)).run a
      else (ivT fe (.defnDecl cv v hint)).run a := by
  simp only [installStepGo, StateT.run_bind, natOpNames_run h, exc_ok_bind',
    natDivModNames_run h, pinnedDefnL, List.contains_append]
  split <;> simp [cdT, ivT, StateT.run_bind]

theorem installStepGo_opaque (h : PinsFull m a.pins) (cv : IConstantVal) (v : EIdx) :
    (installStepGo mode pins fe (.opaqueDecl cv v)).run a =
      if (pinnedOpaqueL m).contains cv.name then (cdT mode pins fe (.opaqueDecl cv v)).run a
      else (ivT fe (.opaqueDecl cv v)).run a := by
  simp only [installStepGo, StateT.run_bind, reduceOpNames_run h, exc_ok_bind', pinnedOpaqueL]
  by_cases hc : ((List.range' 44 2).map (fun j => (decI (pinW m j) : NIdx))).contains cv.name = true
  · simp only [hc, if_true]; rfl
  · simp only [hc, if_false, Bool.false_eq_true]; rfl

theorem installStepGo_thm (cv : IConstantVal) (v : EIdx) :
    installStepGo mode pins fe (.thmDecl cv v) = ivT fe (.thmDecl cv v) := rfl

theorem installStepGo_axiom (cv : IConstantVal) :
    installStepGo mode pins fe (.axiomDecl cv) = cdT mode pins fe (.axiomDecl cv) := rfl

theorem installStepGo_quot (k : ConLeche.QuotKind) (cv : IConstantVal) :
    installStepGo mode pins fe (.quotDecl k cv) = cdT mode pins fe (.quotDecl k cv) := rfl

end twin

/-! ## The model of `install_step_go` (its two big callees through `callW`) -/

section model
variable (p : Prog)

/-- `check_decl`'s result as `install_step_go` returns it. -/
def istgCD : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, 0, 0], m)

/-- `install_value`'s result as `install_step_go` returns it. -/
def istgIV : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, 1, r.tail.headD 0], m)

/-- A pinnable kind: `pin_in`'s answer picks `check_decl` or `install_value(i, vis, ck, vk)`. -/
def istgPin (n : Nat) (i vis ck vk : Word) (m0 : Mem) : Option Word → Option (List Word × Mem)
  | none => none
  | some c =>
    if c ≠ 0 then istgCD (callW p n "check_decl" [i, vis] m0)
    else istgIV (callW p n "install_value" [i, vis, ck, vk] m0)

/-- After `iw_reset`: the record's kind and name. -/
def istgK0 (n : Nat) (i vis : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m0) =>
    if rdW (m0.arr64 DECL) (1 + 8 * i) = 2 then
      istgPin p n i vis 1 0 m0 (pinInW n m0 (rdW (m0.arr64 DECL) (2 + 8 * i) &&& 4294967295) 15 30)
    else if rdW (m0.arr64 DECL) (1 + 8 * i) = 3 then
      istgIV (callW p n "install_value" [i, vis, 2, 1] m0)
    else if rdW (m0.arr64 DECL) (1 + 8 * i) = 4 then
      istgPin p n i vis 0 2 m0 (pinInW n m0 (rdW (m0.arr64 DECL) (2 + 8 * i) &&& 4294967295) 44 46)
    else istgCD (callW p n "check_decl" [i, vis] m0)

/-- **The model of `install_step_go`.** -/
def istgW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, i, vis => istgK0 p n i vis (iwResetW m)

section arms
variable (n : Nat) (m m0 : Mem) (i vis ck vk c : Word) (r0 : List Word)
theorem istgW_step : istgW p (n + 1) m i vis = istgK0 p n i vis (iwResetW m) := rfl
theorem istgK0_some : istgK0 p n i vis (some (r0, m0)) =
    if rdW (m0.arr64 DECL) (1 + 8 * i) = 2 then
      istgPin p n i vis 1 0 m0 (pinInW n m0 (rdW (m0.arr64 DECL) (2 + 8 * i) &&& 4294967295) 15 30)
    else if rdW (m0.arr64 DECL) (1 + 8 * i) = 3 then
      istgIV (callW p n "install_value" [i, vis, 2, 1] m0)
    else if rdW (m0.arr64 DECL) (1 + 8 * i) = 4 then
      istgPin p n i vis 0 2 m0 (pinInW n m0 (rdW (m0.arr64 DECL) (2 + 8 * i) &&& 4294967295) 44 46)
    else istgCD (callW p n "check_decl" [i, vis] m0) := rfl
theorem istgPin_some : istgPin p n i vis ck vk m0 (some c) =
    if c ≠ 0 then istgCD (callW p n "check_decl" [i, vis] m0)
    else istgIV (callW p n "install_value" [i, vis, ck, vk] m0) := rfl
end arms

grind_pattern [ind_grind] istgW_step => istgW p (n + 1) m i vis
grind_pattern [ind_grind] istgK0_some => istgK0 p n i vis (some (r0, m0))
grind_pattern [ind_grind] istgPin_some => istgPin p n i vis ck vk m0 (some c)

/-- The lookups `install_step_go`'s body needs. -/
structure IstgProg (p : Prog) : Prop where
  go : p.lookup "install_step_go" = some installStepGoL
  reset : p.lookup "iw_reset" = some iwReset
  pin : p.lookup "pin_in" = some pinIn

set_option maxHeartbeats 1600000 in
theorem istg_specW (h : IstgProg p) (n : Nat) (s₀ : St) (i vis : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_step_go" [i, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ istgW p n s₀.mem i vis = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.go]
  simp only [callFn, installStepGoL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        iwReset_specW p h.reset n, pinIn_specW p h.pin n,
        callW_spec p n "check_decl", callW_spec p n "install_value"] <;>
      finish (gen := 20) [istgCD, istgIV, rdW_eq]

end model

end L.Arena
